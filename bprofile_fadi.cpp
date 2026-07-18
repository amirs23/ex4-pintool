/*########################################################################################################*/
// cd /nfs/iil/ptl/bt/ghaber1/pin/pin-2.10-45467-gcc.3.4.6-ia32_intel64-linux/source/tools/SimpleExamples
// make btranslate.test
//  ../../../pin -t obj-intel64/btranslate.so -- ~/workdir/tst
/*########################################################################################################*/
/*BEGIN_LEGAL
Intel Open Source License

Copyright (c) 2002-2011 Intel Corporation. All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.  Redistributions
in binary form must reproduce the above copyright notice, this list of
conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.  Neither the name of
the Intel Corporation nor the names of its contributors may be used to
endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE INTEL OR
ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
END_LEGAL */
/* ===================================================================== */

/* ===================================================================== */
/*! @file
 * This probe pintool generates translated code of all the routines, places them 
 * in an allocated Translation Cache (TC) along with instrumentation instructions that collect 
 * profiling for each BBL and for each indirect jump target.
 *
 * The profiling data is then printed on exit into the output file edge-profile.csv,
 * one line per BBL sorted from hottest (most executed) to coldest.
 */

#include "pin.H"
extern "C" {
#include "xed-interface.h"
}
#include <iostream>
#include <iomanip>
#include <fstream>
#include <sys/mman.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <malloc.h>
#include <errno.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <values.h>
#include <set>
#include <map>
#include <vector>
#include <algorithm>
#include <time.h>
#include <fstream>

using namespace std;

/* ============================================================= */
/* Routine filtering for probe-mode translation                  */
/* ============================================================= */
//
// The original loop in find_candidate_rtns_for_tc() / commit_translated_rtns_to_tc()
// added every routine returned by Pin as a translation candidate, with no check that
// the routine is actually safe to patch with RTN_ReplaceProbed(). Pin's own docs
// require calling RTN_IsSafeForProbedReplacement() before probing a routine (the
// original skeleton only does this for "_exit", not for the routines it translates).
// This is the same class of bug that made exercise 3's btranslate.cpp segfault; ported
// here with the same fix (see that exercise's README for how it was diagnosed).
static const set<string> g_known_bad_rtns = {
    "ggc_min_heapsize_heuristic",
    // Bisected (via -max_rtns) on cpugcc_r_base.Oz-m64: an ordinary compiler
    // routine (not crt/startup/.plt glue like the entries above), but produces
    // an Illegal Instruction crash post-translation, reproducing identically
    // with -no_prof. Almost certainly the same category as
    // ggc_min_heapsize_heuristic: some instruction in it doesn't survive the
    // XED decode-then-re-encode round trip faithfully. "alias_sets_conflict_p"
    // is the same GCC source file (alias.c) as alias_set_subset_of and was
    // bisected the same way -- likely both hit the same underlying encoding
    // edge case, possibly shared via inlining or a common code pattern in
    // that file.
    "alias_set_subset_of",
    "alias_sets_conflict_p"
};

// Bisection aid (same technique exercise 3's README describes): pass
// "-max_rtns N" on the pin command line to translate only the first N
// routines that would otherwise pass all the safety checks below. Halving N
// until the crash disappears/reappears isolates the exact bad routine
// without needing to recompile between guesses; its name gets printed to
// stderr (prefixed "candidate #") as it's accepted, so the last name printed
// before a bisection run crashes is the culprit to add to g_known_bad_rtns.
KNOB<UINT> KnobMaxRtns(KNOB_MODE_WRITEONCE, "pintool",
    "max_rtns", "0", "Translate at most N routines (0 = unlimited); for bisecting a bad routine");

// Debug aid: force every profiling stub to save/restore all of RAX/RBX/RCX,
// i.e. disable just the dead-register liveness optimization while leaving
// every other part of the profiling instrumentation active. Used to isolate
// whether a bug is in the liveness analysis specifically or elsewhere in
// add_profiling_instrs().
KNOB<BOOL> KnobForceLiveAll(KNOB_MODE_WRITEONCE, "pintool",
    "force_live_all", "0", "Debug: disable dead-register liveness optimization (always save/restore RAX/RBX/RCX)");

bool rtn_is_translatable(RTN rtn)
{
    if (rtn == RTN_Invalid())
        return false;

    string name = RTN_Name(rtn);

    // Pin usually groups an entire PLT-family section into one pseudo-routine
    // named ".plt", but there can be several such sections in one binary
    // (".plt", ".plt.got", ".plt.sec", ...) and some linkers instead expose
    // each lazy-binding trampoline as its own routine named "<symbol>@plt"
    // (bisected via -max_rtns down to ".plt.got" and "fileno@plt" separately
    // on cpugcc_r_base.Oz-m64). All of these are GOT-indirect "jmp [rip+disp]"
    // stubs: relocating one into the TC drifts the RIP-relative GOT offset
    // just enough to jump through the wrong slot, landing inside the dynamic
    // linker's lazy-binding resolver with garbage arguments. Never translate
    // any of them -- match by prefix/suffix rather than exact name so any
    // section naming variant is covered, not just the ones seen so far.
    if (name.compare(0, 4, ".plt") == 0 ||
        (name.size() > 4 && name.compare(name.size() - 4, 4, "@plt") == 0))
        return false;

    // The C runtime's own startup/teardown plumbing: tiny, ABI-mandated stubs
    // that run before main() or after it returns, generated directly by the
    // crt object files (crtbegin.o/crtend.o/glibc's csu) rather than compiled
    // from ordinary C. "_init", "_start", and "__do_global_dtors_aux" were each
    // individually bisected (via -max_rtns) on cpugcc_r_base.Oz-m64 to be exact
    // routines that produce an Illegal Instruction crash post-translation --
    // reproduces identically with -no_prof, so it's the raw decode/re-encode
    // round trip that doesn't survive here, not anything specific to profiling
    // instrumentation. The rest of this list is the same category of
    // special-purpose crt glue from the same source files (crtstuff.c) that
    // wasn't individually hit yet, listed preemptively -- none of it is ever
    // meaningfully "hot" for profiling anyway, so excluding it costs nothing.
    static const set<string> g_crt_startup_rtns = {
        "_init", "_start", "_fini",
        "register_tm_clones", "deregister_tm_clones", "frame_dummy",
        "__do_global_dtors_aux", "__do_global_ctors_aux", "call_weak_fn"
    };
    if (g_crt_startup_rtns.count(name))
        return false;

    // glibc / dynamic-linker internals: these can run while the loader or libc
    // itself is in the middle of bookkeeping, which makes redirecting them via a
    // probe jump unsafe regardless of what RTN_IsSafeForProbedReplacement() says.
    //
    // "__mpn_" is a separate case with a separate reason: glibc's internal
    // multi-precision-arithmetic primitives (distinct from GCC's own bundled,
    // unprefixed "mpn_"/"mpz_" GMP copy, which translates fine) are tight,
    // hand-tuned loops. Bisected on sgcc_base.mytest-m64: __mpn_sub_n uses a
    // "jrcxz" whose *original* target is a safe 85 bytes back (well within the
    // 8-bit relative-branch range), but our translation expands the
    // surrounding code (RIP-relative fixups, profiling stubs) enough to push
    // the *translated* copy's distance out of 8-bit range, which
    // fix_direct_jmp_or_call_displacement() correctly refuses to encode --
    // aborting translation for the ENTIRE binary rather than just this one
    // routine, since a single fix_instructions_displacements() failure
    // anywhere currently kills the whole commit. Given ~20 sibling __mpn_*
    // routines in this binary are almost certainly built the same tight way,
    // exclude the whole family rather than finding them one at a time.
    static const char* internal_prefixes[] = {"_dl_", "_IO_", "_Unwind_", "__libc_", "__GI_", "__mpn_"};
    for (const char* prefix : internal_prefixes) {
        if (name.compare(0, strlen(prefix), prefix) == 0)
            return false;
    }

    if (g_known_bad_rtns.count(name))
        return false;

    // Too small to safely hold the probe's replacement jump.
    if (RTN_Size(rtn) < 16)
        return false;

    if (!RTN_IsSafeForProbedReplacement(rtn))
        return false;

    // This function gets called once per routine from find_candidate_rtns_for_tc()
    // and again from commit_translated_rtns_to_tc(); track accepted routines by
    // address (not a plain counter) so a routine already accepted in the first
    // pass is never re-counted/re-capped/re-printed in the second.
    static set<ADDRINT> accepted;
    ADDRINT addr = RTN_Address(rtn);
    if (accepted.count(addr))
        return true;

    // Only print/count candidates when actually bisecting (-max_rtns set);
    // on a normal run (max_rtns == 0, unlimited) this would otherwise spam
    // stderr with one line per accepted routine -- thousands of lines for a
    // binary the size of cpugcc_r_base -- for no benefit.
    UINT32 max_rtns = KnobMaxRtns.Value();
    if (max_rtns != 0) {
        if (accepted.size() >= max_rtns)
            return false;
        cerr << "candidate #" << dec << accepted.size() << ": " << name << endl;
    }
    accepted.insert(addr);
    return true;
}

static inline bool fits_signed_bits(xed_int64_t value, unsigned bits)
{
    xed_int64_t min_val = -(1LL << (bits - 1));
    xed_int64_t max_val =  (1LL << (bits - 1)) - 1;
    return value >= min_val && value <= max_val;
}

static inline bool is_within_32bit_branch_range(ADDRINT addr, ADDRINT base)
{
    xed_int64_t diff = (xed_int64_t)addr - (xed_int64_t)base;
    return fits_signed_bits(diff, 32);
}

static inline bool is_region_within_32bit_branch_range(ADDRINT addr, size_t size, ADDRINT base)
{
    return is_within_32bit_branch_range(addr, base) &&
           is_within_32bit_branch_range(addr + size, base);
}

/*======================================================================*/
/* commandline switches                                                 */
/*======================================================================*/
KNOB<BOOL>   KnobVerbose(KNOB_MODE_WRITEONCE,    "pintool",
    "verbose", "0", "Verbose run");

KNOB<BOOL>   KnobDumpOrigCode(KNOB_MODE_WRITEONCE,    "pintool",
    "dump_orig_code", "0", "Dump Original non-translated Code");

KNOB<BOOL>   KnobDumpTranslatedCode(KNOB_MODE_WRITEONCE,    "pintool",
    "dump_tc", "0", "Dump Translated Code");

KNOB<BOOL>   KnobDoNotCommitTranslatedCode(KNOB_MODE_WRITEONCE,    "pintool",
    "no_tc_commit", "0", "Do not commit translated code");

KNOB<UINT> KnobNumSecsDuringProfile(KNOB_MODE_WRITEONCE,    "pintool",
    "prof_time", "2", "Number of seconds for collecting BBL counters");

KNOB<BOOL> KnobDumpProfile(KNOB_MODE_WRITEONCE,    "pintool",
    "dump_prof", "0", "Dump profiling information");

KNOB<BOOL> KnobNoProfile(KNOB_MODE_WRITEONCE,    "pintool",
    "no_prof", "0", "Do not collect profile information");


/* ===================================================================== */
/* Global Variables */
/* ===================================================================== */
std::ofstream* out = 0;

// For XED:
#if defined(TARGET_IA32E)
    xed_state_t dstate = {XED_MACHINE_MODE_LONG_64, XED_ADDRESS_WIDTH_64b};
#else
    xed_state_t dstate = { XED_MACHINE_MODE_LEGACY_32, XED_ADDRESS_WIDTH_32b};
#endif

//For XED: Pass in the proper length: 15 is the max. But if you do not want to
//cross pages, you can pass less than 15 bytes, of course, the
//instruction might not decode if not enough bytes are provided.
const unsigned max_inst_len = XED_MAX_INSTRUCTION_BYTES;

ADDRINT lowest_sec_addr = 0;
ADDRINT highest_sec_addr = 0;

// tc containing the new code:
char *tc = nullptr;
unsigned tc_size = 0;
unsigned max_tc_size = 0;


// Array of original target addresses that cannot be translated in the TC.
ADDRINT *jump_to_orig_addr_map = nullptr;
unsigned jump_to_orig_addr_num = 0;

// basic instruction types.
typedef enum {
    RegularIns = 0,
    RtnHeadIns,
    ProfilingIns,

} ins_enum_t;

// instructions map with an entry for each new instruction in the code.
typedef struct {
    ADDRINT orig_ins_addr;
    ADDRINT new_ins_addr;
    ADDRINT orig_targ_addr;
    ADDRINT orig_rip_addr;
    ins_enum_t ins_type;
    char encoded_ins[XED_MAX_INSTRUCTION_BYTES];
    unsigned size;
    int targ_map_entry;
    unsigned bbl_num;
    xed_category_enum_t xed_category;
} instr_map_t;


// Instrs map:
instr_map_t *instr_map = NULL;
unsigned num_of_instr_map_entries = 0;
unsigned max_ins_count = 0;

#define MAX_TARG_ADDRS 0x3

// Bbl map of all the bbl exec counters to be collected at runtime:
typedef struct {
  UINT64 counter;
  UINT64 fallthru_counter; // for BBLs that terminate with a cond branch.
  ADDRINT targ_addr[MAX_TARG_ADDRS+1];
  UINT64  targ_count[MAX_TARG_ADDRS+1];
  unsigned starting_ins_entry;
  unsigned terminating_ins_entry;
} bbl_map_t;

bbl_map_t *bbl_map;
unsigned bbl_num = 0;
std::map<ADDRINT, unsigned> entry_map;

unsigned max_rtn_count = 0;

struct timespec start_running_time;
struct timespec end_running_time;

/* ============================================================= */
/* Service instr routines                                        */
/* ============================================================= */
bool isUncondJump(INS ins)
{
    const xed_decoded_inst_t* xedd = INS_XedDec(ins);
    xed_category_enum_t category_enum = xed_decoded_inst_get_category(xedd);
    if (category_enum == XED_CATEGORY_UNCOND_BR)
      return true;
    return false;
}

bool isJumpOrRet(INS ins)
{
   if (!INS_IsCall(ins) &&
       (INS_IsIndirectControlFlow(ins) ||
        INS_IsDirectControlFlow(ins) ||
        INS_IsRet(ins)))
     return true;

   return false;
}

bool isBackwardJump(INS ins)
{
  return (!INS_IsCall(ins) && INS_IsDirectControlFlow(ins) &&
          INS_DirectControlFlowTargetAddress(ins) < INS_Address(ins));
}

int create_nop7_xedd_instr(xed_decoded_inst_t *xedd)
{
  xed_encoder_instruction_t enc_instr;
  xed_encoder_request_t enc_req;
  char encoded_ins[XED_MAX_INSTRUCTION_BYTES];
  unsigned int ilen = XED_MAX_INSTRUCTION_BYTES;
  unsigned int olen = 0;
  
  xed_inst0(&enc_instr, dstate, XED_ICLASS_NOP7, 64);
  
  xed_encoder_request_zero_set_mode(&enc_req, &dstate);
  xed_bool_t convert_ok = xed_convert_to_encoder_request(&enc_req, &enc_instr);
  if (!convert_ok) {
      cerr << "conversion to encode request failed" << endl;
      return -1;
  }
  xed_error_enum_t xed_error = xed_encode(&enc_req,
            reinterpret_cast<UINT8*>(encoded_ins), ilen, &olen);
  if (xed_error != XED_ERROR_NONE) {
      cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
    return -1;
  }
  xed_decoded_inst_zero_set_mode(xedd, &dstate);
  xed_error_enum_t xed_code = xed_decode(xedd, reinterpret_cast<UINT8*>(&encoded_ins), max_inst_len); // xed_decode(&xedd, nop7, max_inst_len);
  if (xed_code != XED_ERROR_NONE) {
      cerr << "DECODE ERROR: " << xed_error_enum_t2str(xed_code) << endl;
      return -1;;
  }
  return 0;
}


/* ============================================================= */
/* Service dump routines                                         */
/* ============================================================= */

/*********************/
/* dump_image_instrs */
/*********************/
void dump_image_instrs(IMG img)
{
    for (SEC sec = IMG_SecHead(img); SEC_Valid(sec); sec = SEC_Next(sec))
    {
        for (RTN rtn = SEC_RtnHead(sec); RTN_Valid(rtn); rtn = RTN_Next(rtn))
        {

            // Open the RTN.
            RTN_Open( rtn );

            cerr << RTN_Name(rtn) << ":" << endl;

            for( INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins) )
            {
                  cerr << "0x" << hex << INS_Address(ins) << ": " << INS_Disassemble(ins) << endl;
            }

            // Close the RTN.
            RTN_Close( rtn );

            cerr << endl;
        }
    }
}


/*************************/
/* dump_instr_from_xedd */
/*************************/
void dump_instr_from_xedd (xed_decoded_inst_t* xedd, ADDRINT address)
{
    // debug print decoded instr:
    char disasm_buf[2048];

    xed_uint64_t runtime_address = static_cast<UINT64>(address);  // set the runtime adddress for disassembly

    xed_format_context(XED_SYNTAX_INTEL, xedd, disasm_buf, sizeof(disasm_buf), static_cast<UINT64>(runtime_address), 0, 0);

    cerr << hex << address << ": " << disasm_buf <<  endl;
}


/************************/
/* dump_instr_from_mem */
/************************/
void dump_instr_from_mem (ADDRINT *address, ADDRINT new_addr)
{
  char disasm_buf[2048];
  xed_decoded_inst_t new_xedd;

  xed_decoded_inst_zero_set_mode(&new_xedd,&dstate);

  xed_error_enum_t xed_code = xed_decode(&new_xedd, reinterpret_cast<UINT8*>(address), max_inst_len);

  BOOL xed_ok = (xed_code == XED_ERROR_NONE);
  if (!xed_ok){
      cerr << "invalid opcode" << endl;
  }

  xed_format_context(XED_SYNTAX_INTEL, &new_xedd, disasm_buf, 2048, static_cast<UINT64>(new_addr), 0, 0);

  cerr << "0x" << hex << new_addr << ": " << disasm_buf <<  endl;

}


/****************************/
/*  dump_entire_instr_map() */
/****************************/
void dump_entire_instr_map()
{
    for (unsigned i=0; i < num_of_instr_map_entries; i++) {
      // Print the routine name if known.
      if (instr_map[i].ins_type == RtnHeadIns) {
        PIN_LockClient();
        RTN rtn = RTN_FindByAddress(instr_map[i].orig_ins_addr);
        if (rtn == RTN_Invalid()) {
            cerr << "Unknown"  << ":" << endl;
        } else {
            cerr << RTN_Name(rtn) << ":" << endl;
        }
        PIN_UnlockClient();
      }

      if (!instr_map[i].size)
        continue;


      dump_instr_from_mem ((ADDRINT *)instr_map[i].encoded_ins, instr_map[i].orig_ins_addr);
    }
}

/*************************/
/*  get_bbl_start_addr()  */
/*************************/
// Returns the address of the first REAL (non-profiling-stub) instruction of
// bbl b. bbl_map[b].starting_ins_entry cannot be used directly: when a BBL
// immediately follows a conditional branch, its starting_ins_entry actually
// points at the fallthrough-counter profiling stub, which is stamped with
// the PRECEDING BBL's terminating branch address (see add_profiling_instrs()
// call sites in find_candidate_rtns_for_tc()), not this BBL's own address.
ADDRINT get_bbl_start_addr(unsigned b)
{
    for (unsigned i = bbl_map[b].starting_ins_entry; i <= bbl_map[b].terminating_ins_entry; i++) {
        if (instr_map[i].ins_type != ProfilingIns)
            return instr_map[i].orig_ins_addr;
    }
    // Should not happen (every BBL has at least its own terminator instr),
    // but fall back safely rather than crash.
    return instr_map[bbl_map[b].starting_ins_entry].orig_ins_addr;
}

/****************************/
/*  write_edge_profile_csv() */
/****************************/
// Writes edge-profile.csv: one line per BBL, sorted hottest-to-coldest, in
// the format required by the exercise:
//   <bbl addr>, <exec count>, <taken count>, <fallthru count>,
//   <targ addr1, exec count1>, <targ addr2, exec count2>,
//   <targ addr3, exec count3>, <targ addr4, exec count4>
void write_edge_profile_csv()
{
    std::vector<unsigned> order;
    order.reserve(bbl_num);
    for (unsigned b = 0; b < bbl_num; b++)
        order.push_back(b);

    std::sort(order.begin(), order.end(), [](unsigned a, unsigned b) {
        if (bbl_map[a].counter != bbl_map[b].counter)
            return bbl_map[a].counter > bbl_map[b].counter; // hottest first.
        return get_bbl_start_addr(a) < get_bbl_start_addr(b); // deterministic tie-break.
    });

    for (unsigned k = 0; k < order.size(); k++) {
        unsigned b = order[k];
        UINT64 exec_count = bbl_map[b].counter;
        UINT64 fallthru_count = bbl_map[b].fallthru_counter;
        UINT64 taken_count = (exec_count > fallthru_count) ? (exec_count - fallthru_count) : 0;

        *out << "0x" << hex << get_bbl_start_addr(b) << dec
             << ", " << exec_count
             << ", " << taken_count
             << ", " << fallthru_count;

        for (unsigned j = 0; j <= MAX_TARG_ADDRS; j++) {
            *out << ", 0x" << hex << bbl_map[b].targ_addr[j] << dec
                 << ", " << bbl_map[b].targ_count[j];
        }
        *out << endl;
    }
}

/**************************/
/* dump_instr_map_entry() */
/**************************/
void dump_instr_map_entry(unsigned instr_map_entry)
{
    cerr << dec << instr_map_entry << ": ";
    cerr << " orig_ins_addr: 0x" << hex << instr_map[instr_map_entry].orig_ins_addr;
    cerr << " new_ins_addr: 0x" << hex << instr_map[instr_map_entry].new_ins_addr;

    if (instr_map[instr_map_entry].orig_targ_addr) {
      cerr << " orig_targ_addr: 0x" << hex << instr_map[instr_map_entry].orig_targ_addr;
      ADDRINT new_targ_addr;
      if (instr_map[instr_map_entry].targ_map_entry >= 0)
          new_targ_addr = instr_map[instr_map[instr_map_entry].targ_map_entry].new_ins_addr;
      else
          new_targ_addr = instr_map[instr_map_entry].orig_targ_addr;
      cerr << " new_targ_addr: 0x" << hex << new_targ_addr;
    }

    cerr << "    new instr:";
    dump_instr_from_mem((ADDRINT *)instr_map[instr_map_entry].encoded_ins,
                        instr_map[instr_map_entry].new_ins_addr);
}


/*************/
/* dump_tc() */
/*************/
void dump_tc(char *tc, unsigned size_tc)
{
  char disasm_buf[2048];
  xed_decoded_inst_t new_xedd;
  ADDRINT address = (ADDRINT)&tc[0];

  while (address < (ADDRINT)&tc[size_tc]) {

      xed_decoded_inst_zero_set_mode(&new_xedd,&dstate);
      xed_error_enum_t xed_code = xed_decode(&new_xedd, reinterpret_cast<UINT8*>(address), max_inst_len);

      BOOL xed_ok = (xed_code == XED_ERROR_NONE);
      if (!xed_ok){
          cerr << "invalid opcode" << endl;
          return;
      }

      xed_format_context(XED_SYNTAX_INTEL, &new_xedd, disasm_buf, 2048, static_cast<UINT64>(address), 0, 0);

      cerr << "0x" << hex << address << ": " << disasm_buf <<  endl;

      address += xed_decoded_inst_get_length (&new_xedd);
  }
}


/* ============================================================= */
/* Translation routines                                         */
/* ============================================================= */


/***************************/
/* disable_profiling_in_tc */
/***************************/
int disable_profiling_in_tc(instr_map_t * instr_map, unsigned num_of_instr_map_entries)
{
    for (unsigned i = 0; i < num_of_instr_map_entries; i++) {
        // Check for the case of a NOP instr at the head of a
        // pofiling code stub and replace it by a jump instr that skips it.
        if (instr_map[i].ins_type == ProfilingIns &&
            instr_map[i].xed_category == XED_CATEGORY_WIDENOP) {
            // Calculate the jump displacement.
            unsigned j = 1;
            xed_int64_t disp = 0;
            while (instr_map[i+j].ins_type == ProfilingIns) {
                disp += instr_map[i+j].size;
                j++;
            }

          xed_encoder_instruction_t enc_instr;
          xed_encoder_request_t enc_req;
          unsigned int ilen = XED_MAX_INSTRUCTION_BYTES;
          char encoded_jmp_ins[XED_MAX_INSTRUCTION_BYTES];
          unsigned int olen = 5; // skip jump instr is exactly 5 bytes long.
          
          disp += (instr_map[i].size - olen);
          xed_inst1(&enc_instr, dstate,  XED_ICLASS_JMP, 64, xed_relbr(disp, 32));
          
          xed_encoder_request_zero_set_mode(&enc_req, &dstate);
          xed_bool_t convert_ok = xed_convert_to_encoder_request(&enc_req, &enc_instr);
          if (!convert_ok) {
              cerr << "conversion to encode request failed" << endl;
              return -1;
          }           
          xed_error_enum_t xed_error = xed_encode(&enc_req,
                    reinterpret_cast<UINT8*>(encoded_jmp_ins), ilen, &olen);
          if (xed_error != XED_ERROR_NONE) {
              cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
            return -1;
          }

          if (olen > instr_map[i].size) {
             cerr << " unable to set a relative jump to skip the profiling code stub at: "
                  << hex << "0x" << instr_map[i].new_ins_addr << "\n";
             return -1;
          }

          // Write the bypassing jump instr on the NOP instr.
          memcpy((ADDRINT *)instr_map[i].new_ins_addr, encoded_jmp_ins, olen);
          i += (j - 1);
       }
    }
    return 0;
}    

/*************************/
/* add_new_instr_entry() */
/*************************/
int add_new_instr_entry(xed_decoded_inst_t *xedd, ADDRINT pc, ins_enum_t ins_type)
{
    // copy target addr to instr map:
    ADDRINT orig_targ_addr = 0x0;

    // Check if the instruction has a branch displacement:
    xed_uint_t disp_byts = xed_decoded_inst_get_branch_displacement_width(xedd);
    xed_int32_t disp;
    if (disp_byts > 0) { // there is a branch offset.
      disp = xed_decoded_inst_get_branch_displacement(xedd);
      orig_targ_addr = pc + xed_decoded_inst_get_length (xedd) + disp;
    }

    // copy rip-relative addr to instr map:
    ADDRINT orig_rip_addr = 0x0;

    // check for a rip-relative displacement:
    unsigned memops = xed_decoded_inst_number_of_memory_operands(xedd);
    if (memops) {
      xed_reg_enum_t base_reg = xed_decoded_inst_get_base_reg(xedd, 0);
      if (base_reg == XED_REG_RIP) {
         unsigned size = xed_decoded_inst_get_length (xedd);
         xed_int64_t disp = xed_decoded_inst_get_memory_displacement(xedd, 0);
         orig_rip_addr = (ADDRINT)(pc + disp + size);
      }
    }

    // Converts the decoder request to a valid encoder request:
    xed_encoder_request_init_from_decode (xedd);

    unsigned new_size = 0;

    xed_error_enum_t xed_error =
       xed_encode (xedd, reinterpret_cast<UINT8*>(instr_map[num_of_instr_map_entries].encoded_ins),
                   max_inst_len , &new_size);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        return -1;
    }

    // Add a new entry to instr_map:
    //
    instr_map[num_of_instr_map_entries].orig_ins_addr = pc;
    instr_map[num_of_instr_map_entries].new_ins_addr = 0x0;
    instr_map[num_of_instr_map_entries].orig_targ_addr = orig_targ_addr;
    instr_map[num_of_instr_map_entries].orig_rip_addr = orig_rip_addr;
    instr_map[num_of_instr_map_entries].targ_map_entry = -1;
    instr_map[num_of_instr_map_entries].size = new_size;
    instr_map[num_of_instr_map_entries].ins_type = ins_type;
    instr_map[num_of_instr_map_entries].bbl_num = bbl_num;
    instr_map[num_of_instr_map_entries].xed_category = xed_decoded_inst_get_category(xedd);

    num_of_instr_map_entries++;

    if (num_of_instr_map_entries >= max_ins_count) {
        cerr << "out of memory for map_instr" << endl;
        return -1;
    }

    // debug print new encoded instr:
    if (KnobVerbose) {
        cerr << "    new instr:";
        dump_instr_from_mem((ADDRINT *)instr_map[num_of_instr_map_entries-1].encoded_ins,
                            instr_map[num_of_instr_map_entries-1].new_ins_addr);
    }

    return new_size;
}

/***************************/
/* add_new_encoded_instr() */
/***************************/
int add_new_encoded_instr(ADDRINT ins_addr, xed_encoder_instruction_t *enc_instr, ins_enum_t ins_type) {
    char encoded_ins[XED_MAX_INSTRUCTION_BYTES];
    unsigned int ilen = XED_MAX_INSTRUCTION_BYTES;
    unsigned int olen = 0;
  
    // Convert the encoding instr to a valid encoder request.
    xed_encoder_request_t enc_req;    
    xed_encoder_request_zero_set_mode(&enc_req, &dstate);
    xed_bool_t convert_ok = xed_convert_to_encoder_request(&enc_req, enc_instr);
    if (!convert_ok) {
        cerr << "conversion to encode request failed" << endl;
        return -1;
    }
    
    // Encode instr.
    xed_error_enum_t xed_error = xed_encode(&enc_req,
              reinterpret_cast<UINT8*>(encoded_ins), ilen, &olen);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
      return -1;
    }
  
    // Decode instr.
    xed_decoded_inst_t xedd;
    xed_decoded_inst_zero_set_mode(&xedd,&dstate);
    xed_error_enum_t xed_code = xed_decode(&xedd, reinterpret_cast<UINT8*>(&encoded_ins), max_inst_len);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << ins_addr << endl;
        return -1;;
    }
    int rc = add_new_instr_entry(&xedd, ins_addr, ins_type);
    if (rc < 0) {
      cerr << "ERROR: failed during instructon translation." << endl;
      return -1;
    }
    return 0;
}

/* ============================================================= */
/* Liveness analysis for dead-register elimination in profiling  */
/* stubs (exercise requirement 2)                                */
/* ============================================================= */
//
// add_profiling_instrs() below must clobber RAX (and, for indirect jumps,
// RBX/RCX) as scratch registers. If the ORIGINAL program's value in one of
// those registers is never read again before it is overwritten -- i.e. it is
// "dead" at the point the stub is injected -- spilling/restoring it around
// the stub is pure overhead with no correctness benefit. This computes, for
// every instruction in a routine, which of {RAX,RBX,RCX} are live going INTO
// that instruction (LiveIn), via a standard backward dataflow fixpoint over
// the routine's local control-flow graph.
//
// Any control-flow edge we cannot resolve locally (indirect branch/call, ret,
// a direct branch/call whose target lands outside this routine, falling off
// the end of the routine) is conservatively treated as "all three registers
// live". That makes this analysis only ever miss an optimization opportunity,
// never unsafe -- it can't claim a register is dead when it might not be.
#define LIVE_RAX  0x1u
#define LIVE_RBX  0x2u
#define LIVE_RCX  0x4u
#define LIVE_NONE 0x0u
#define LIVE_ALL  (LIVE_RAX | LIVE_RBX | LIVE_RCX)

static unsigned reg_to_live_bit(REG reg)
{
    // Fully qualify LEVEL_BASE::REG_RAX/RBX/RCX: glibc's <sys/ucontext.h> also
    // defines unqualified REG_RAX/REG_RBX/REG_RCX (as mcontext gregset_t
    // indices), and pin.H pulls in signal.h, so the bare names are ambiguous
    // here even though they aren't anywhere else in this file.
    if (!REG_valid(reg))
        return LIVE_NONE;
    REG full = REG_FullRegName(reg);
    if (full == LEVEL_BASE::REG_RAX) return LIVE_RAX;
    if (full == LEVEL_BASE::REG_RBX) return LIVE_RBX;
    if (full == LEVEL_BASE::REG_RCX) return LIVE_RCX;
    return LIVE_NONE;
}

// Computes, for every instruction in rtn (which must already be RTN_Open()'d),
// the subset of {RAX,RBX,RCX} live just before that instruction executes, and
// stores it in live_in_at keyed by instruction address.
static void compute_rtn_liveness(RTN rtn, std::map<ADDRINT, unsigned> &live_in_at)
{
    std::vector<INS> ins_list;
    std::map<ADDRINT, unsigned> addr_to_idx;
    for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins)) {
        addr_to_idx[INS_Address(ins)] = (unsigned)ins_list.size();
        ins_list.push_back(ins);
    }

    unsigned n = (unsigned)ins_list.size();
    if (!n)
        return;

    std::vector<unsigned> use_set(n, LIVE_NONE), def_set(n, LIVE_NONE);
    std::vector< std::vector<unsigned> > successors(n);
    std::vector<bool> exits_conservatively(n, false);

    for (unsigned i = 0; i < n; i++) {
        INS ins = ins_list[i];

        for (UINT32 r = 0; r < INS_MaxNumRRegs(ins); r++)
            use_set[i] |= reg_to_live_bit(INS_RegR(ins, r));
        for (UINT32 w = 0; w < INS_MaxNumWRegs(ins); w++)
            def_set[i] |= reg_to_live_bit(INS_RegW(ins, w));

        // Conservatively treat a call as clobbering the caller-saved
        // registers we track (RAX, RCX): Pin's own INS_RegW for a CALL only
        // reports RSP/return-address effects, not the callee's ABI-implied
        // clobber of volatile registers. RBX is callee-saved, so it is NOT
        // added here -- a well-formed callee must preserve it.
        if (INS_IsCall(ins))
            def_set[i] |= (LIVE_RAX | LIVE_RCX);

        if (INS_IsIndirectControlFlow(ins) || INS_IsRet(ins)) {
            // Unknown target, or routine exit: assume the worst.
            exits_conservatively[i] = true;
        } else if (INS_IsDirectControlFlow(ins) && !INS_IsCall(ins)) {
            ADDRINT targ = INS_DirectControlFlowTargetAddress(ins);
            std::map<ADDRINT, unsigned>::iterator it = addr_to_idx.find(targ);
            if (it != addr_to_idx.end())
                successors[i].push_back(it->second);
            else
                exits_conservatively[i] = true; // branch target outside this routine.
        }
        // A direct call's callee is not part of this routine's local CFG; only
        // its fall-through return point (handled below) matters here.

        if (INS_HasFallThrough(ins)) {
            if (i + 1 < n)
                successors[i].push_back(i + 1);
            else
                exits_conservatively[i] = true; // falls off the end of the routine.
        }
    }

    std::vector<unsigned> live_in(n, LIVE_NONE), live_out(n, LIVE_NONE);
    bool changed = true;
    while (changed) {
        changed = false;
        for (unsigned k = 0; k < n; k++) {
            unsigned i = n - 1 - k; // walk roughly backward; only affects convergence speed, not correctness.
            unsigned new_out = exits_conservatively[i] ? LIVE_ALL : LIVE_NONE;
            for (unsigned s = 0; s < successors[i].size(); s++)
                new_out |= live_in[successors[i][s]];
            unsigned new_in = use_set[i] | (new_out & ~def_set[i]);
            if (new_out != live_out[i] || new_in != live_in[i]) {
                live_out[i] = new_out;
                live_in[i] = new_in;
                changed = true;
            }
        }
    }

    for (unsigned i = 0; i < n; i++)
        live_in_at[INS_Address(ins_list[i])] = live_in[i];
}

/**************************/
/* add_profiling_instrs() */
/**************************/
int add_profiling_instrs(INS ins, ADDRINT ins_addr,
                         UINT64 *counter_addr, unsigned bbl_num,
                         unsigned live_regs_mask)
{
  xed_encoder_instruction_t enc_instr;

  static uint64_t rax_mem = 0;

  // Add NOP instr (to be overwritten later on by a jmp that skips
  // the profiling, once profiling is done).
  xed_inst0(&enc_instr, dstate, XED_ICLASS_NOP4, 64);
  if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
    return -1;

  // Save RAX (skipped if RAX is dead at this point -- see compute_rtn_liveness()):
  // MOV RAX into rax_mem
  bool rax_is_live = (live_regs_mask & LIVE_RAX) != 0;
  if (rax_is_live) {
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)&rax_mem, 64), 64), // Destination op.
              xed_reg(XED_REG_RAX));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
  }

  // Create profiling for indirect jump targets.
  if (INS_IsIndirectControlFlow(ins) && !INS_IsRet(ins) && !INS_IsCall(ins)) {
    // Debug print.
    //cerr << " BBL terminates with indirect jump: "
    //     << " 0x" << hex << ins_addr << ": "
    //     << INS_Disassemble(ins) << "\n";

    static uint64_t rbx_mem = 0;
    static uint64_t rcx_mem = 0;

    // Retrieve the details about the mem operand.
    xed_decoded_inst_t *xedd = INS_XedDec(ins);
    xed_reg_enum_t base_reg = xed_decoded_inst_get_base_reg(xedd, 0);
    xed_reg_enum_t index_reg = xed_decoded_inst_get_index_reg(xedd, 0);
    xed_int64_t disp = xed_decoded_inst_get_memory_displacement(xedd, 0);
    xed_uint_t scale = xed_decoded_inst_get_scale(xedd, 0);
    xed_uint_t width = xed_decoded_inst_get_memory_displacement_width_bits(xedd, 0);
    unsigned mem_addr_width = xed_decoded_inst_get_memop_address_width(xedd, 0);
    
    xed_reg_enum_t targ_reg = XED_REG_INVALID;
    unsigned memops = xed_decoded_inst_number_of_memory_operands(xedd);
    if (!memops)
      targ_reg = xed_decoded_inst_get_reg(xedd, XED_OPERAND_REG0);

    // Debug print.
    //dump_instr_from_xedd(xedd, ins_addr);
    //cerr << " base reg: " << xed_reg_enum_t2str(base_reg)
    //     << " index reg " << xed_reg_enum_t2str(index_reg)
    //     << " scale: " << dec << scale
    //     << " disp: 0x" << hex << disp
    //     << " width: " << dec << width
    //     << " mem addr width: " << dec << mem_addr_width
    //     << " targ reg: " << targ_reg << xed_reg_enum_t2str(targ_reg)
    //     << "\n";
    
    // save RBX into rbx_mem in 2 steps via RAX
    // save RCX into rcx_mem in 2 steps via RAX
    // Convert jmp [base_reg + index_reg*scale] to: MOV RAX, [base_reg + index_reg*scale]
    //         Or convert jmp targ_reg to: MOV RAX, targ_reg ==> RAX holds jump targ addr
    // MOV RBX, RAX ==> Now RBX also holds targ addr
    // AND RAX, MAX_TARG_ADDR ==> RAX holds index i = 0..MAX_TARG_ADDRS
    // MOV RCX, xed_imm0((ADDRINT)&bbl_map_targ_addr[bbl_num][0])
    // MOV [RCX + 8*RAX], RBX
    // MOV RBX, xed_imm0((ADDRINT)&bbl_map_targ_count[bbl_num][0])
    // MOV RCX, [RBX + 8*RAX]
    // LEA RCX, [RCX + 1]
    // MOV [RBX + 8*RAX], RCX
    // restore RCX from rcx_mem in 2 steps via RAX
    // restore RBX from rbx_mem in 2 steps via RAX
    
    // Save RBX (skipped if dead at this point):
    bool rbx_is_live = (live_regs_mask & LIVE_RBX) != 0;
    if (rbx_is_live) {
      // Save RBX step 1 - MOV RBX into RAX
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RAX),  // Destination op.
                xed_reg(XED_REG_RBX));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;

      // Save RBX step 2 - MOV RAX into rbx_mem
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)&rbx_mem, 64), 64), // Destination op.
                xed_reg(XED_REG_RAX));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;
    }

    // Save RCX (skipped if dead at this point):
    bool rcx_is_live = (live_regs_mask & LIVE_RCX) != 0;
    if (rcx_is_live) {
      // Save RCX step 1 - MOV RCX into RAX
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RAX),   // Destination op.
                xed_reg(XED_REG_RCX));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;

      // Save RCX step 2 - MOV RAX into rcx_mem
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)&rcx_mem, 64), 64), // Destination op.
                xed_reg(XED_REG_RAX));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;
    }

    // Replace RIP reg by an absolute displacement.
    // Convert 'jmp [rax*8+0x657118]' or: 'jmp [rip+0x42513c]'
    // to: mov rax, [rax*8+0x657118] or: mov rax, [<absolute addr>]
    //
    // Check if we need to restore RAX in case  it is used as base reg or index reg,
    // e.g., jmp [RIP+8*RAX] or: jmp [RAX+8*RBX]
    
    // Check if we need to restore RAX from rax_mem.
    if (targ_reg == XED_REG_RAX || base_reg == XED_REG_RAX || index_reg == XED_REG_RAX) {
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RAX), // Destination reg op.
                xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)&rax_mem, 64), 64));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
       return -1;
    }
    // Check if we need to convert [RIP+disp+index*scale] to [absolute_disp + index*scale]
    if (base_reg == XED_REG_RIP) {
      unsigned int orig_size = xed_decoded_inst_get_length (xedd);
      // Absolute address the original RIP-relative jump-table/GOT operand pointed to.
      ADDRINT abs_target = (ADDRINT)(ins_addr + disp + orig_size);

      // Do NOT try to bake this into an absolute disp32 operand (as the
      // unpatched code did): PIE binaries (e.g. cpugcc_r_base, unlike the
      // fixed-address bzip2/tst) load at ASLR'd addresses far above the 2GB
      // mark, so a plain 32-bit displacement can never reach abs_target and
      // add_profiling_instrs() would always fail here. Instead keep this a
      // genuine RIP-relative operand with a placeholder displacement, and
      // let the existing fix_rip_displacement() pass compute the real
      // displacement later once this instruction's actual address inside the
      // TC is known -- exactly the mechanism already used for every other
      // relocated RIP-relative instruction (the TC is guaranteed to be
      // within 32-bit branch range of the original code; see
      // allocate_and_init_memory()).
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RAX),    // Destination reg op.
                xed_mem_bd(XED_REG_RIP, xed_disp(0, 32), mem_addr_width));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;
      instr_map[num_of_instr_map_entries - 1].orig_rip_addr = abs_target;
    } else if (targ_reg != XED_REG_RAX) { // avoid ceating the MOV RAX, RAX Nop.
        xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                 xed_reg(XED_REG_RAX),    // Destination reg op.
                 (targ_reg != XED_REG_INVALID ? xed_reg(targ_reg) :
                  xed_mem_bisd(base_reg, index_reg, scale, xed_disp(disp, width), mem_addr_width)));
        if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
          return -1;
    }
    // (If neither branch fired -- a bare `jmp/call reg` where reg is already
    // RAX -- the "restore RAX from rax_mem" step above already left RAX
    // holding the correct target address, so no extra MOV is needed here.)

    // MOV RBX, RAX
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_reg(XED_REG_RBX),    // Destination reg op.
              xed_reg(XED_REG_RAX));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // AND RAX, MAX_TARG_ADDRS. (NOTE: Modifies RFLAGS).
    xed_inst2(&enc_instr, dstate, XED_ICLASS_AND, 64,
              xed_reg(XED_REG_RAX),    // Destination reg op.
              xed_imm0(MAX_TARG_ADDRS, 8));  // keep only MAX_TARG_ADDRS+1 targets for profiling.
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // MOV RCX, xed_imm0((ADDRINT)&bbl_map[bbl_num].targ_addr[0])
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_reg(XED_REG_RCX), // Destination reg op.
              xed_imm0((ADDRINT)&(bbl_map[bbl_num].targ_addr[0]), 64));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // MOV [RCX + 8*RAX], RBX
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_mem_bisd(XED_REG_RCX, // base reg
                           XED_REG_RAX, //index reg
                           8, // scale
                           xed_disp(0, 32), // disp
                           64),  // Destination reg op.
              xed_reg(XED_REG_RBX));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // MOV RBX, xed_imm0((ADDRINT)&bbl_map[bbl_num].targ_count[0])
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_reg(XED_REG_RBX), // Destination reg op.
              xed_imm0((ADDRINT)&(bbl_map[bbl_num].targ_count[0]), 64));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // MOV RCX, [RBX + 8*RAX]
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_reg(XED_REG_RCX),   // Destination reg op.
              xed_mem_bisd(XED_REG_RBX, // base reg
                           XED_REG_RAX, //index reg
                           8, // scale
                           xed_disp(0, 32), // disp
                           64));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // LEA RCX, [RCX + 1]
    xed_inst2(&enc_instr, dstate, XED_ICLASS_LEA, 64,
              xed_reg(XED_REG_RCX), // Destination reg op.
              xed_mem_bd(XED_REG_RCX, // base reg
                         xed_disp(1, 8), // disp
                         64));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // MOV [RBX + 8*RAX], RCX
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_mem_bisd(XED_REG_RBX, // base reg
                           XED_REG_RAX, //index reg
                           8, // scale
                           xed_disp(0, 32), // disp
                           64),     // Destination op.
              xed_reg(XED_REG_RCX));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
    
    // Restore RCX (only if it was actually saved above):
    if (rcx_is_live) {
      // Restore RCX step 1- MOV from rcx_mem into RAX
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RAX), // Destination op.
                xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)&rcx_mem, 64), 64));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;

      // Restore RCX step 2 - MOV RAX into RCX
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RCX),  // Destination op.
                xed_reg(XED_REG_RAX));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;
    }

    // Restore RBX (only if it was actually saved above):
    if (rbx_is_live) {
      // Restore RBX step 1 - MOV from rbx_mem into RAX
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RAX), // Destination op.
                xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)&rbx_mem, 64), 64));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;

      // Restore RBX step 2 - MOV RAX into RBX
      xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
                xed_reg(XED_REG_RBX),  // Destination op.
                xed_reg(XED_REG_RAX));
      if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
        return -1;
    }

  } // end of: 'if bbl terminates with indirect jump'.
  
  // Create the profiling instrs for counting the BBL frequency.
  //

  // MOV from bbl_map into RAX
  xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
            xed_reg(XED_REG_RAX),  // Destination reg op.
            xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)counter_addr, 64), 64));
  if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
    return -1;

  // LEA RAX, [RAX+1]
  xed_inst2(&enc_instr, dstate, XED_ICLASS_LEA,  64,  // operand width
            xed_reg(XED_REG_RAX), // Destination reg op.
            xed_mem_bd(XED_REG_RAX, xed_disp(1, 8), 64));
  if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
    return -1;

  // MOV from RAX into bbl_map
  xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
            xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)counter_addr, 64), 64), // Destination op.
            xed_reg(XED_REG_RAX));
  if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
    return -1;

  // Restore RAX (only if it was actually saved above):
  // MOV from rax_mem into RAX
  if (rax_is_live) {
    xed_inst2(&enc_instr, dstate, XED_ICLASS_MOV, 64,
              xed_reg(XED_REG_RAX), // Destination reg op.
              xed_mem_bd(XED_REG_INVALID, xed_disp((ADDRINT)&rax_mem, 64), 64));
    if (add_new_encoded_instr(ins_addr, &enc_instr, ProfilingIns) < 0)
      return -1;
  }

  return 0;
}

/**************************************************/
/* chain_all_direct_jmp_and_call_target_entries() */
/**************************************************/
void chain_all_direct_jmp_and_call_target_entries(unsigned from_entry,
                                                 unsigned until_entry)
{
    entry_map.clear();

    for (unsigned i = from_entry; i < until_entry; i++) {
        instr_map[i].targ_map_entry = -1;
        ADDRINT orig_ins_addr = instr_map[i].orig_ins_addr;
        if (!orig_ins_addr)
          continue;
        // For instrs with same orig_addr, give precedence to the first one.
        entry_map.emplace(orig_ins_addr, i);
    }

    for (unsigned i = from_entry; i < until_entry; i++) {
        ADDRINT orig_targ_addr = instr_map[i].orig_targ_addr;
        if (orig_targ_addr == 0)
            continue;
        if (instr_map[i].targ_map_entry > 0)
            continue;
        if (!entry_map.count(orig_targ_addr))
            continue;
        if (!instr_map[i].size)
            continue;
        instr_map[i].targ_map_entry = entry_map[orig_targ_addr];
    }
}


/***********************************************/
/* set_initial_estimated_new_ins_addrs_in_tc() */
/***********************************************/
int set_initial_estimated_new_ins_addrs_in_tc(char *tc) {
  unsigned tc_cursor = 0;
  // Set initial estimated new addrs for each instruction in the tc.
  for (unsigned i=0; i < num_of_instr_map_entries; i++) {
    instr_map[i].new_ins_addr = (ADDRINT)&tc[tc_cursor];
    // update expected size of tc.
    tc_cursor += instr_map[i].size;
    // Check if we exceeded the TC size.
    if (tc_cursor >= max_tc_size)
      return -1;
  }
  return 0;
}


/**************************/
/* fix_rip_displacement() */
/**************************/
int fix_rip_displacement(unsigned instr_map_entry)
{
    // uncond jumps instructions with size=0
    // should remain with size=0 for beeing removed from tc
    if (!instr_map[instr_map_entry].size)
        return 0;

    // Check if it is a RIP-relative instr.
    if (!instr_map[instr_map_entry].orig_rip_addr)
      return 0;

    // Check if it is a direct jmp or call instruction.
    if (instr_map[instr_map_entry].orig_targ_addr != 0)
      return 0;

    xed_decoded_inst_t xedd;
    xed_decoded_inst_zero_set_mode(&xedd, &dstate);

    xed_error_enum_t xed_code =
       xed_decode(&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), max_inst_len);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: " << "0x"
             << hex << instr_map[instr_map_entry].new_ins_addr << endl;
        return -1;
    }

    //debug print:
    if (KnobVerbose) {
      cerr << " Before fixing rip offset\n";
      dump_instr_map_entry(instr_map_entry);
    }

    //xed_uint_t disp_byts = xed_decoded_inst_get_memory_displacement_width(xedd,i); // how many byts in disp ( disp length in byts - for example FFFFFFFF = 4
    xed_int64_t new_disp = 0;
    xed_uint_t new_disp_byts = 4;   // set maximal num of byts for now.

    // Modify rip displacement. use rip-relative direct addressing mode.
    new_disp = (xed_int64_t)(instr_map[instr_map_entry].orig_rip_addr - instr_map[instr_map_entry].new_ins_addr -
                               instr_map[instr_map_entry].size);
    // Code when using direct addressing mode.
    //xed_encoder_request_set_base0 (&xedd, XED_REG_INVALID);
    //new_disp = instr_map[instr_map_entry].orig_rip_addr;
    if (!fits_signed_bits(new_disp, 32)) {
        cerr << "Invalid rip displacement larger than 32 bits in fix_rip_displacement\n";
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    unsigned max_size = XED_MAX_INSTRUCTION_BYTES;
    unsigned new_size = 0;

    // Converts the decoder request to a valid encoder request. NOTE: this must
    // happen BEFORE setting the new memory displacement below — calling it after
    // rebuilds the encoder request from the original decode and silently discards
    // the displacement we just set, which left every rip-relative access in the
    // TC pointing at the original (now wrong) address and was the actual cause of
    // the segfault.
    xed_encoder_request_init_from_decode (&xedd);

    // Set the memory displacement using a bit length.
    xed_encoder_request_set_memory_displacement (&xedd, new_disp, new_disp_byts);

    xed_error_enum_t xed_error =
       xed_encode (&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins),
                   max_size , &new_size);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    //debug print:
    if (KnobVerbose) {
      cerr << " After fixing rip offset\n";
      dump_instr_map_entry(instr_map_entry);
    }

    return new_size;
}


/**************************************/
/* fix_direct_jmp_or_call_to_orig_addr */
/**************************************/
int fix_direct_jmp_or_call_to_orig_addr(unsigned instr_map_entry)
{
    // Ignore instructions of zero size.
    if (!instr_map[instr_map_entry].size)
      return 0;

    // Debug print.
    if (KnobVerbose) {
        cerr << "jump to orig addr: 0x" << hex << instr_map[instr_map_entry].orig_targ_addr << " : ";
        dump_instr_from_mem((ADDRINT *)instr_map[instr_map_entry].encoded_ins,
                            instr_map[instr_map_entry].orig_ins_addr);
    }

    // check for cases of direct jumps/calls back to the orginal target address:
    if (instr_map[instr_map_entry].targ_map_entry >= 0) {
        cerr << "ERROR: Invalid jump or call instruction" << endl;
        return -1;
    }

    xed_decoded_inst_t xedd;
    xed_decoded_inst_zero_set_mode(&xedd,&dstate);

    xed_error_enum_t xed_code =
        xed_decode(&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), max_inst_len);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: " << "0x"
             << hex << instr_map[instr_map_entry].new_ins_addr << endl;
        return -1;
    }

    xed_category_enum_t category_enum = xed_decoded_inst_get_category(&xedd);

    // Conditional branches have no memory-operand encoding, so they cannot be
    // redirected through jump_to_orig_addr_map like calls/unconditional jumps
    // below. Instead, just re-encode the branch to point directly at its
    // original target. Without this, any conditional branch whose target fell
    // outside the translated routine (e.g. into a routine we chose not to
    // translate) made the whole translation fail here.
    if (category_enum == XED_CATEGORY_COND_BR) {
        xed_int64_t cond_disp = (xed_int64_t)instr_map[instr_map_entry].orig_targ_addr -
                                 (xed_int64_t)instr_map[instr_map_entry].new_ins_addr -
                                 (xed_int64_t)instr_map[instr_map_entry].size;

        xed_uint_t cond_disp_byts = 4;
        xed_iclass_enum_t iclass_enum = xed_decoded_inst_get_iclass(&xedd);
        xed_iform_enum_t iform_enum = xed_decoded_inst_get_iform_enum(&xedd);
        if (iclass_enum == XED_ICLASS_LOOP || iclass_enum == XED_ICLASS_LOOPE ||
            iclass_enum == XED_ICLASS_LOOPNE || iform_enum == XED_IFORM_JRCXZ_RELBRb) {
            cond_disp_byts = 1;
        }

        if (!fits_signed_bits(cond_disp, 32) ||
            (cond_disp_byts == 1 && !fits_signed_bits(cond_disp, 8))) {
            cerr << "Invalid conditional branch displacement to original code\n";
            dump_instr_map_entry(instr_map_entry);
            return -1;
        }

        xed_encoder_request_init_from_decode(&xedd);
        xed_encoder_request_set_branch_displacement(&xedd, cond_disp, cond_disp_byts);

        unsigned cond_new_size = 0;
        xed_error_enum_t cond_xed_error =
            xed_encode(&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins),
                       XED_MAX_INSTRUCTION_BYTES, &cond_new_size);
        if (cond_xed_error != XED_ERROR_NONE) {
            cerr << "ENCODE ERROR: " << xed_error_enum_t2str(cond_xed_error) << endl;
            dump_instr_map_entry(instr_map_entry);
            return -1;
        }

        return cond_new_size;
    }

    if (category_enum != XED_CATEGORY_CALL && category_enum != XED_CATEGORY_UNCOND_BR) {
        cerr << "ERROR: Invalid direct jump from translated code to original code for:\n";
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    unsigned ilen = XED_MAX_INSTRUCTION_BYTES;
    unsigned olen = 0;

    xed_encoder_instruction_t  enc_instr;

    // Use the heap variable instr_map[instr_map_entry].orig_targ_addr as the
    // memory container that holds the target address for the jmp/call
    // and indirectly jmp/call via that memory location.

    // search for orig_targ_addr in jump_to_orig_addr_map.
    int jump_to_orig_addr_map_entry = -1;
    for (unsigned i = 0; i < jump_to_orig_addr_num; i++) {
      if (instr_map[instr_map_entry].orig_targ_addr == jump_to_orig_addr_map[i]) {
        jump_to_orig_addr_map_entry = i;
        break;
      }
    }
    if (jump_to_orig_addr_map_entry < 0) {
      // NOTE: must use the counter as the index BEFORE incrementing it, otherwise
      // slot 0 of jump_to_orig_addr_map is always skipped (off-by-one) and the
      // map can be written one entry past its allocated size.
      jump_to_orig_addr_map_entry = jump_to_orig_addr_num;
      if ((unsigned)jump_to_orig_addr_map_entry >= max_rtn_count) {
         cerr << "exceeded size of jump_to_orig_addr_map at fix_direct_jmp_or_call_to_orig_addr\n";
         return -1;
      }
      jump_to_orig_addr_map[jump_to_orig_addr_map_entry] = instr_map[instr_map_entry].orig_targ_addr;
      jump_to_orig_addr_num++;
    }

    // The new instruction we are about to encode is always a 6-byte indirect
    // "call/jmp qword ptr [rip+disp32]" (2-byte opcode/modrm + 4-byte disp32),
    // regardless of how long the original instruction was. RIP-relative
    // displacements are relative to the end of THIS new instruction, so using
    // the original instruction's length here (as the unpatched code did) skews
    // the displacement and makes the indirect jump/call land on garbage memory.
    const xed_uint_t new_instr_len = 6;

    xed_int64_t new_disp = (ADDRINT)&jump_to_orig_addr_map[jump_to_orig_addr_map_entry] -
                       instr_map[instr_map_entry].new_ins_addr -
                       new_instr_len;
    if (!fits_signed_bits(new_disp, 32)) {
        cerr << "Invalid rip displacement larger than 32 bits in fix_direct_jmp_or_call_to_orig_addr\n";
        cerr << "new displacement: " << dec << new_disp << "\n";
        return -1;
    }

    if (category_enum == XED_CATEGORY_CALL)
            xed_inst1(&enc_instr, dstate,
            XED_ICLASS_CALL_NEAR, 64,
            xed_mem_bd (XED_REG_RIP, xed_disp(new_disp, 32), 64));

    if (category_enum == XED_CATEGORY_UNCOND_BR)
            xed_inst1(&enc_instr, dstate,
            XED_ICLASS_JMP, 64,
            xed_mem_bd (XED_REG_RIP, xed_disp(new_disp, 32), 64));

    xed_encoder_request_t enc_req;

    xed_encoder_request_zero_set_mode(&enc_req, &dstate);
    xed_bool_t convert_ok = xed_convert_to_encoder_request(&enc_req, &enc_instr);
    if (!convert_ok) {
        cerr << "conversion to encode request failed" << endl;
        return -1;
    }

    xed_error_enum_t xed_error =
       xed_encode(&enc_req, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), ilen, &olen);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) << endl;
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    // NOTE: We cannot zero the orig_targ_addr field in instr_map as follows:
    //  instr_map[instr_map_entry].orig_targ_addr = 0x0;
    // This is because the RIP displacement may become too large to fit into 4 bytes long.

    // debug prints:
    if (KnobVerbose) {
        dump_instr_map_entry(instr_map_entry);
    }

    return olen;
}


/**************************************/
/* fix_direct_jmp_or_call_displacement */
/**************************************/
int fix_direct_jmp_or_call_displacement(unsigned instr_map_entry)
{
    //uncond jumps instructions with size=0 should remain with size=0
    // for beeing removed from tc
    if (!instr_map[instr_map_entry].size)
        return 0;

    // Check if it is indeed a direct branch or a direct call instr:
    if (instr_map[instr_map_entry].orig_targ_addr == 0)
      return 0;

    xed_decoded_inst_t xedd;
    xed_decoded_inst_zero_set_mode(&xedd,&dstate);

    xed_error_enum_t xed_code =
        xed_decode(&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), max_inst_len);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: "
             << "0x" << hex << instr_map[instr_map_entry].new_ins_addr << endl;
        return -1;
    }

    xed_int64_t  new_disp = 0;
    unsigned max_size = XED_MAX_INSTRUCTION_BYTES;
    unsigned new_size = 0;


    xed_category_enum_t category_enum = xed_decoded_inst_get_category(&xedd);

    if (category_enum != XED_CATEGORY_CALL &&
        category_enum != XED_CATEGORY_COND_BR &&
        category_enum != XED_CATEGORY_UNCOND_BR) {
        cerr << "ERROR: unrecognized branch displacement" << endl;
        return -1;
    }

    // fix direct branches/calls to original targ addresses or
    // indirect branches via a rip offset which had previously been
    // formed by previouis calls to fix_direct_jmp_or_call_to_orig_addr()
    // in order to relpace direct jumps to orig targ addrs.
    if (instr_map[instr_map_entry].targ_map_entry < 0) {
       int rc = fix_direct_jmp_or_call_to_orig_addr(instr_map_entry);
       return rc;
    }

    ADDRINT new_targ_addr;
    new_targ_addr = instr_map[instr_map[instr_map_entry].targ_map_entry].new_ins_addr;

    new_disp =
      (new_targ_addr - instr_map[instr_map_entry].new_ins_addr) - instr_map[instr_map_entry].size; // orig_size;
     if (!fits_signed_bits(new_disp, 32)) {
        cerr << "Invalid rip displacement larger than 32 bits in fix_direct_jmp_or_call_displacement\n";
        return -1;
    }

    xed_uint_t   new_disp_byts = 4; // num_of_bytes(new_disp);  ???

    // the max displacement size of loop instructions is 1 byte:
    xed_iclass_enum_t iclass_enum = xed_decoded_inst_get_iclass(&xedd);
    if (iclass_enum == XED_ICLASS_LOOP ||
        iclass_enum == XED_ICLASS_LOOPE ||
        iclass_enum == XED_ICLASS_LOOPNE) {
      new_disp_byts = 1;
    }

    // the max displacement size of jecxz instructions is ???:
    xed_iform_enum_t iform_enum = xed_decoded_inst_get_iform_enum (&xedd);
    if (iform_enum == XED_IFORM_JRCXZ_RELBRb){
      new_disp_byts = 1;
    }

    if (new_disp_byts == 1 && !fits_signed_bits(new_disp, 8)) {
        cerr << "Invalid 8-bit branch displacement in fix_direct_jmp_or_call_displacement\n";
        dump_instr_map_entry(instr_map_entry);
        return -1;
    }

    // Converts the decoder request to a valid encoder request:
    xed_encoder_request_init_from_decode (&xedd);

    //Set the branch displacement:
    xed_encoder_request_set_branch_displacement (&xedd, new_disp, new_disp_byts);

    //xed_uint8_t enc_buf[XED_MAX_INSTRUCTION_BYTES];
    //xed_error_enum_t xed_error = xed_encode (&xedd, enc_buf, max_size , &new_size);
    xed_error_enum_t xed_error =
        xed_encode (&xedd, reinterpret_cast<UINT8*>(instr_map[instr_map_entry].encoded_ins), max_size, &new_size);
    if (xed_error != XED_ERROR_NONE) {
        cerr << "ENCODE ERROR: " << xed_error_enum_t2str(xed_error) <<  endl;
        char buf[2048];
        xed_format_context(XED_SYNTAX_INTEL, &xedd, buf, 2048,
                           static_cast<UINT64>(instr_map[instr_map_entry].orig_ins_addr), 0, 0);
        cerr << " instr: " << "0x" << hex << instr_map[instr_map_entry].orig_ins_addr << " : " << buf <<  endl;
          return -1;
    }

    //debug print of new instruction in tc:
    if (KnobVerbose) {
        dump_instr_map_entry(instr_map_entry);
    }

    return new_size;
}

/************************************/
/* fix_instructions_displacements() */
/************************************/
int fix_instructions_displacements()
{
   // fix displacemnets of direct branch or call instructions:

    int size_diff = 0;
    bool is_diff = false;

    do {

        size_diff = 0;
        is_diff = false;

        if (KnobVerbose) {
            cerr << "starting a pass of fixing instructions displacements: " << endl;
        }

        for (unsigned i=0; i < num_of_instr_map_entries; i++) {

            instr_map[i].new_ins_addr += size_diff;

            // fix rip displacement:
            int new_size = fix_rip_displacement(i);
            if (new_size) {
              if (new_size < 0)
                  return -1;
              if (instr_map[i].size != (unsigned)new_size) { // this was a rip-based instruction which was fixed.
                  if (instr_map[i].size < (unsigned)new_size)
                     size_diff += (new_size - instr_map[i].size);
                  else
                     size_diff -= (instr_map[i].size - new_size);
                  instr_map[i].size = (unsigned)new_size;
                  is_diff = true;
                  continue;
              }
            }

            // fix instr displacement for direct jump or call:
            new_size = fix_direct_jmp_or_call_displacement(i);
            if (new_size) {
              if (new_size < 0)
                  return -1;
              if (instr_map[i].size != (unsigned)new_size) {
                if (instr_map[i].size < (unsigned)new_size)
                   size_diff += (new_size - instr_map[i].size);
                else
                   size_diff -= (instr_map[i].size - new_size);
                instr_map[i].size = (unsigned)new_size;
                is_diff = true;
                continue;
              }
            }

        }  // end int i=0; i ..

    } while (is_diff);

   return 0;
 }


/********************************/
/* find_candidate_rtns_for_tc() */
/********************************/
int find_candidate_rtns_for_tc(IMG img)
{
    int rc = 0;
    // go over routines and check if they are candidates for translation and mark them for translation:

    for (SEC sec = IMG_SecHead(img); SEC_Valid(sec); sec = SEC_Next(sec))
    {
        if (!SEC_IsExecutable(sec) || SEC_IsWriteable(sec) || !SEC_Address(sec))
            continue;

        for (RTN rtn = SEC_RtnHead(sec); RTN_Valid(rtn); rtn = RTN_Next(rtn))
        {
            // Skip routines that are not safe to relocate/probe (see rtn_is_translatable()).
            if (!rtn_is_translatable(rtn))
                continue;

            // Keep the entry num of the rtn head in case we need to
            // revert the insertin of the instruction in rtn into the instructions
            // map due to an invalid decoding.
            //unsigned rtn_entry = num_of_instr_map_entries;

            // Open the RTN.
            RTN_Open( rtn );

            // Map all instructions that are a target of some direct jump or call in the rtn.
            std::map<ADDRINT, bool>is_targ_map;
            is_targ_map.empty();
            for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins)) {
               if (INS_IsDirectControlFlow(ins)) {
                 ADDRINT targ_addr = INS_DirectControlFlowTargetAddress(ins);
                 is_targ_map[targ_addr] = true;
               }
            }

            // Liveness of {RAX,RBX,RCX} at each instruction, used below to skip
            // dead-register save/restore in the profiling stubs (see
            // compute_rtn_liveness() / add_profiling_instrs()).
            std::map<ADDRINT, unsigned> live_in_at;
            compute_rtn_liveness(rtn, live_in_at);

            for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins)) {

                //debug print of orig instruction:
                if (KnobVerbose) {
                    cerr << "old instr: ";
                    cerr << "0x" << hex << INS_Address(ins) << ": " << INS_Disassemble(ins) <<  endl;
                    //xed_print_hex_line(reinterpret_cast<UINT8*>(INS_Address (ins)), INS_Size(ins));
                }

                ADDRINT ins_addr = INS_Address(ins);

                // Default to conservative (all live) if the address is missing
                // from the map for any reason -- correctness over optimization.
                unsigned live_regs_mask = LIVE_ALL;
                if (!KnobForceLiveAll) {
                    std::map<ADDRINT, unsigned>::iterator live_it = live_in_at.find(ins_addr);
                    if (live_it != live_in_at.end())
                        live_regs_mask = live_it->second;
                }

                xed_decoded_inst_t xedd;
                xed_error_enum_t xed_code;

                // Add instr into instr map:
                bool isRtnHeadIns = (RTN_Address(rtn) == ins_addr);
                ins_enum_t ins_type = (isRtnHeadIns ? RtnHeadIns : RegularIns);

                // Insert a NOP7 instr at Rtn Head to be used in order
                // to restore orig target of a cond jumps to a routine.
                //
                if (!KnobNoProfile && isRtnHeadIns) {
                  rc = create_nop7_xedd_instr(&xedd);
                  if (rc < 0) {
                    cerr << "ERROR: failed to create a NOP7 instr during translation of instr at: "
                         << "0x" << hex << ins_addr << endl;
                    RTN_Close(rtn);
                    return -1;
                  }
                  rc = add_new_instr_entry(&xedd, ins_addr, ins_type);
                  if (rc < 0) {
                    cerr << "ERROR: failed during instructon translation." << endl;
                    RTN_Close(rtn);
                    return -1;
                  }
                  ins_type = RegularIns;
                }

                // Check if ins is a control transfer instr that terminates a BBL
                // or the next instr is a target of a direct branch or call.
                INS next_ins = INS_Next(ins);
                bool isNextInsJumpTarget = 
                    (!INS_Valid(next_ins) ? false : is_targ_map[INS_Address(next_ins)]);
                bool isInsTerminatesBBL = (isJumpOrRet(ins) || isNextInsJumpTarget);

                // Add profiling instructions to count each BBL exec at runtime:
                //
                if (!KnobNoProfile) {
                  if (isInsTerminatesBBL) {
                    rc = add_profiling_instrs(ins, ins_addr, &bbl_map[bbl_num].counter, bbl_num,
                                              live_regs_mask);
                    if (rc < 0) {
                      RTN_Close(rtn);
                      return -1;
                    }
                  }
                }

                // Add ins to instr_map:
                //
                xed_decoded_inst_zero_set_mode(&xedd,&dstate);
                xed_code = xed_decode(&xedd, reinterpret_cast<UINT8*>(ins_addr), max_inst_len);
                if (xed_code != XED_ERROR_NONE) {
                    cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << ins_addr << endl;
                    RTN_Close(rtn);
                    return -1;
                }

                // Add the instr into the instr_map table.
                rc = add_new_instr_entry(&xedd, INS_Address(ins), ins_type);
                if (rc < 0) {
                    cerr << "ERROR: failed during instructon translation." << endl;
                    RTN_Close(rtn);
                    return -1;
                }

                if (isInsTerminatesBBL) {
                  bbl_map[bbl_num].terminating_ins_entry = num_of_instr_map_entries - 1;
                  bbl_num++;
                  bbl_map[bbl_num].starting_ins_entry = num_of_instr_map_entries;
                }

                // Apply edge Profiling: For BBLs that end with a conditional branch,
                //     insert an increment of the fallthrough counter for this BBL,
                //     immediately after the cond branch which terminates the bbl.
                //     and before the next BBL.
                if (!KnobNoProfile && INS_Category(ins) == XED_CATEGORY_COND_BR) {
                  rc = add_profiling_instrs(ins, ins_addr,
                                            &bbl_map[bbl_num - 1].fallthru_counter, bbl_num-1,
                                            live_regs_mask);
                  if (rc < 0) {
                    RTN_Close(rtn);
                    return -1;
                  }
                }

            } // end for INS...

            // debug print of routine name:
            if (KnobVerbose) {
                cerr <<   "rtn name: " << RTN_Name(rtn) << endl;
            }

            // Close the RTN.
            RTN_Close( rtn );

            // Apply local chaining of direct calls and branches for this routine.
            //chain_all_direct_jmp_and_call_target_entries(rtn_entry, num_of_instr_map_entries);

         } // end for RTN..
    } // end for SEC...

    return 0;
}


/***************************/
/* int copy_instrs_to_tc() */
/***************************/
int copy_instrs_to_tc(char *tc)
{
    int cursor = 0;

    for (unsigned i=0; i < num_of_instr_map_entries; i++) {

      if ((ADDRINT)&tc[cursor] != instr_map[i].new_ins_addr) {
          cerr << "ERROR: Non-matching instruction addresses: "
               << hex << (ADDRINT)&tc[cursor]
               << " vs. " << instr_map[i].new_ins_addr << endl;
          return -1;
      }

      memcpy(&tc[cursor], (char *)instr_map[i].encoded_ins, instr_map[i].size);

      cursor += instr_map[i].size;
    }

    return cursor;
}


/***************************************/
/* void commit_translated_rtns_to_tc() */
/***************************************/
inline void commit_translated_rtns_to_tc()
{
    // Commit the translated routines:
    // Go over the routines and replace the original ones
    // by their new successfully translated ones:

    for (unsigned i=0; i < num_of_instr_map_entries; i++) {

        //replace routine by new routine in tc

        if (instr_map[i].ins_type != RtnHeadIns)
          continue;

        RTN rtn = RTN_FindByAddress(instr_map[i].orig_ins_addr);
        if (rtn == RTN_Invalid()) {
           cerr << "invalid rtN for commit for addr: 0x"
                << instr_map[i].orig_ins_addr << "\n";
           continue;
        }

        if (!rtn_is_translatable(rtn))
          continue;

        // Debug print.
        // cerr << "committing rtN: " << RTN_Name(rtn);
        // cerr << " from: 0x" << hex << RTN_Address(rtn)
        //      << " to: 0x" << hex << instr_map[i].new_ins_addr << endl;


        AFUNPTR origFptr = RTN_ReplaceProbed(rtn,  (AFUNPTR)instr_map[i].new_ins_addr);

        if (origFptr == NULL) {
            cerr << "RTN_ReplaceProbed failed.";
            cerr << " orig routine addr: 0x" << hex << RTN_Address(rtn)
                 << " translated routine addr: 0x" << hex
                 << instr_map[i].new_ins_addr << endl;
            dump_instr_from_mem ((ADDRINT *)RTN_Address(rtn), RTN_Address(rtn));
        }

        // debug print.
        //if (origFptr != NULL) {
        //  cerr << "RTN_ReplaceProbed succeeded. ";
        //  cerr << " orig routine addr: 0x" << hex << RTN_Address(rtn)
        //       << " translated routine addr: 0x" << hex
        //       << instr_map[i].new_ins_addr << endl;
        //  dump_instr_from_mem ((ADDRINT *)RTN_Address(rtn), RTN_Address(rtn));
        //}
    }
}

/**********************************************/
/* start_stop_profile_gathering_thread_func() */
/**********************************************/
void start_stop_profile_gathering_thread_func(void *v)
{
    // Wait prof_time seconds for the profiling to count
    // execution frequency for each BBL.
    cerr << " prof time: " << dec << KnobNumSecsDuringProfile << " sec\n";
    sleep(KnobNumSecsDuringProfile);

    cerr << "disabling profile gathering\n";

    // disable profiling.
    //  Add a jump at beginning of every profile stub to bypass the
	//  profiling counters in TC.
    //
    // NOTE: tried wrapping this in PIN_StopApplicationThreads()/
    // PIN_ResumeApplicationThreads() on the theory that this patches live,
    // currently-executing code and could race with an application thread
    // fetching those same bytes. That made an intermittent ~50% failure
    // rate on sgcc_base into a consistent 100% failure rate, so it was
    // actively wrong (either the race isn't the real cause, or that API
    // isn't safe to call this way from an internal Pin thread on this Pin
    // version) -- reverted. The intermittent crash on very large/hot
    // binaries remains open; see README.
    int rc = disable_profiling_in_tc(instr_map, num_of_instr_map_entries);
    if  (rc < 0)
      return;
}

/****************************/
/* allocate_and_init_memory */
/****************************/
int allocate_and_init_memory(IMG img)
{
    // Calculate size of executable sections and allocate required memory:
    //
    ADDRINT highest_addr = 0;
    for (SEC sec = IMG_SecHead(img); SEC_Valid(sec); sec = SEC_Next(sec))
    {
        if (!SEC_IsExecutable(sec) || SEC_IsWriteable(sec) || !SEC_Address(sec))
            continue;

        if (!lowest_sec_addr || lowest_sec_addr > SEC_Address(sec))
            lowest_sec_addr = SEC_Address(sec);

        if (highest_sec_addr < SEC_Address(sec) + SEC_Size(sec))
            highest_sec_addr = SEC_Address(sec) + SEC_Size(sec);

        // need to avouid using RTN_Open as it is expensive...
        for (RTN rtn = SEC_RtnHead(sec); RTN_Valid(rtn); rtn = RTN_Next(rtn))
        {
            if (highest_addr < RTN_Address(rtn) + RTN_Size(rtn))
                highest_addr = RTN_Address(rtn) + RTN_Size(rtn);
            max_rtn_count++;
            max_ins_count += RTN_NumIns  (rtn);
        }
    }

    max_ins_count *= 10; // estimating that the num of instrs for the profiling
                         // and for the inlined functions will not exceed
                         // the total nunmber of the entire code.


    // get a page size in the system:
    int pagesize = sysconf(_SC_PAGE_SIZE);
    if (pagesize == -1) {
      perror("sysconf");
      return -1;
    }

    ADDRINT text_size = (highest_sec_addr - lowest_sec_addr) * 2 + pagesize * 4;

    max_tc_size = 10 * text_size + pagesize * 4;   // FIXME: need a better estimate
    // Check thet max_tc_size is not larger than a 32 bit branch displacement
    if (max_tc_size >= 0x7FFFFFFF) {
      cerr << "size of TC is beyond the range of a branch displacement" << endl;
      return -1;
    }

    // Allocate the needed memory for tc and tc2 + jump orig addr map
    // with RW+EXEC permissions which is not
    // located in an address that is more than 32bits afar:
    const size_t mem_size =
              max_tc_size +                     // TC + TC2 size
              max_rtn_count * sizeof(ADDRINT);  // jump_to_orig_addr_map size
    char *addr = nullptr;
    ADDRINT max_distance = 0x7FFFFFFF;
    const size_t step = pagesize; // Try every page
    // Align target address to page boundary
    ADDRINT aligned_target = ((ADDRINT)highest_addr) & ~(pagesize - 1);
    // Try exact address first
    void* result = mmap((void*)aligned_target, mem_size,
                       PROT_READ | PROT_WRITE | PROT_EXEC,
                       MAP_PRIVATE | MAP_ANONYMOUS,
                       0, 0);
    // Check that the FAR end of the allocated region (not just its start) is
    // still within 32-bit branch range of aligned_target: mem_size can be tens
    // of MB (10x the text size), so a region whose start looked close enough
    // could still put code near its tail out of reach of a rel32 branch.
    if (result != MAP_FAILED &&
        is_region_within_32bit_branch_range((ADDRINT)result, mem_size, aligned_target)) {
        addr = (char *)result;
    } else if (result != MAP_FAILED) {
        munmap(result, mem_size);
    }

    if (!addr) {
        // Search in expanding rings around target
        for (size_t offset = step; offset <= max_distance; offset += step) {
            // Try above target address
            ADDRINT try_addr = aligned_target + offset;
            result = mmap((void*)try_addr, mem_size,
                         PROT_READ | PROT_WRITE | PROT_EXEC,
                         MAP_PRIVATE | MAP_ANONYMOUS,
                         0, 0);
            if (result != MAP_FAILED &&
                is_region_within_32bit_branch_range((ADDRINT)result, mem_size, aligned_target)) {
                addr = (char *)result;
                break;
            }
            if (result != MAP_FAILED) {
                munmap(result, mem_size);
            }

            // Try below target address (if not underflow)
            if (highest_addr >= offset) {
                try_addr = aligned_target - offset;
                result = mmap((void*)try_addr, mem_size,
                             PROT_READ | PROT_WRITE | PROT_EXEC,
                             MAP_PRIVATE | MAP_ANONYMOUS,
                             0, 0);
                if (result != MAP_FAILED &&
                    is_region_within_32bit_branch_range((ADDRINT)result, mem_size, aligned_target)) {
                    addr = (char *)result;
                    break;
                }
                if (result != MAP_FAILED) {
                    munmap(result, mem_size);
                }
            }
        }
    }

    if (!addr) {
        cerr << "failed to allocate memory within 32-bit range. " << endl;
        return -1;
    }

    // debug print.
    cerr << " allocated memory at: 0x" << hex << (ADDRINT)addr << "\n";

    // TC is allocated first.
    tc = (char *)addr;
    addr += max_tc_size;

    // Allocate memory to the jump map to orig addrs which cannot be relocated.
    jump_to_orig_addr_map = (ADDRINT *)addr;

    // Allocate memory for the instr_map table.
    instr_map = (instr_map_t *)calloc(max_ins_count, sizeof(instr_map_t));
    if (instr_map == NULL) {
        perror("calloc");
        return -1;
    }

    // Allocate memory for the bbl_map table.
    bbl_map = (bbl_map_t *)calloc(max_ins_count, sizeof(bbl_map_t));
    if (bbl_map == NULL) {
        perror("calloc");
        return -1;
    }

    return 0;
}



/* ============================================ */
/* Main translation routine                     */
/* ============================================ */
typedef VOID (*EXITFUNCPTR)(INT code);
EXITFUNCPTR origExit;

/********/
/* Fini */
/********/
VOID Fini(INT32 code, VOID* v)
{
    cerr << "Reached _exit." << endl;
    write_edge_profile_csv();

    clock_gettime(CLOCK_MONOTONIC, &end_running_time);
    double elapsed = (end_running_time.tv_sec - start_running_time.tv_sec) + 
                     (end_running_time.tv_nsec - start_running_time.tv_nsec) / 1e9;
	cerr << " Translated code run took: " << elapsed << " seconds\n";
}

/*******************/
/* ExitInProbeMode */
/*******************/
VOID ExitInProbeMode(INT code)
{
    Fini(code, 0);
    (*origExit)(code);
}

/*************/
/* create_tc */
/*************/
VOID create_tc(IMG img, VOID *v)
{
    // Insert a call to function Fini when raching the _exit routine.
    RTN exitRtn = RTN_FindByName(img, "_exit");
    if (RTN_Valid(exitRtn) && RTN_IsSafeForProbedReplacement(exitRtn)) {
      origExit = (EXITFUNCPTR)RTN_ReplaceProbed(exitRtn, AFUNPTR(ExitInProbeMode));
    }

    // Step 0: Check the image and the CPU:
    if (!IMG_IsMainExecutable(img))
      return;

    if (KnobDumpOrigCode)
      dump_image_instrs(img);

    int rc = 0;

    struct timespec start;
    clock_gettime(CLOCK_MONOTONIC, &start);
    // Set this here (not just after a successful commit at the bottom of this
    // function) so that if translation aborts early on any of the rc<0 paths
    // below, Fini()'s "Translated code run took" elapsed-time calculation
    // still measures from a real reference point instead of from whatever
    // start_running_time was zero-initialized to (which reads back as system
    // uptime, since CLOCK_MONOTONIC counts from boot -- misleadingly large).
    start_running_time = start;

    // step 1: Check size of executable sections and allocate required memory:
    rc = allocate_and_init_memory(img);
    if (rc < 0) {
        cerr << "failed to initialize memory for translation\n";
        return;
    }
    cerr << "after memory allocation" << endl;

    // Step 2: go over all routines and identify candidate routines and copy
    //         their code into the instr map IR:
    rc = find_candidate_rtns_for_tc(img);
    if (rc < 0) {
        cerr << "failed to find candidates for translation\n";
        return;
    }
    cerr << "after identifying candidate routines" << endl;

    // Step 3: Chaining - calculate direct branch and call instructions to point
    //         to corresponding target instr entries:
    chain_all_direct_jmp_and_call_target_entries(0, num_of_instr_map_entries);
    cerr << "after chaining all branch targets" << endl;

    // Step 4: Set initial estimated new addrs for each instruction in the tc.
    rc = set_initial_estimated_new_ins_addrs_in_tc(tc);
    if (rc < 0 ) {
        cerr << "failed to set initial estimated new ins addrs in the TC\n";
        return;
    }
    cerr << "after setting initial estimated new ins addrs in the TC" << endl;

    // Step 5: fix rip-based, direct branch and direct call displacements:
    rc = fix_instructions_displacements();
    if (rc < 0 ) {
        cerr << "failed to fix displacments of translated instructions\n";
        return;
    }
    cerr << "after fixing instructions displacements" << endl;

    // Step 6: write translated instructions to the tc:
    rc = copy_instrs_to_tc(tc);
    if (rc < 0 ) {
        cerr << "failed to copy the instructions to the translation cache\n";
        return;
    }
    tc_size = rc;
    cerr << "after write all new instructions to memory tc" << endl;

    if (KnobDumpTranslatedCode) {
       cerr << "Translation Cache dump:" << endl;
       dump_tc(tc, tc_size);  // dump the entire tc

       //cerr << endl << "instructions map dump:" << endl;
       //dump_profile();     // dump all translated instructions in map_instr
    }

    // Step 7: Commit the translated routines:
    //         Go over the candidate functions and replace the original ones
    //         by their new successfully translated ones:
    if (!KnobDoNotCommitTranslatedCode) {
      commit_translated_rtns_to_tc();
      cerr << "after commit of translated routines from orig code to TC" << endl;
    }

    struct timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    double elapsed = (end.tv_sec - start.tv_sec) +
	                 (end.tv_nsec - start.tv_nsec) / 1e9;
    cerr << " create_tc took: " << elapsed << " seconds\n";

	clock_gettime(CLOCK_MONOTONIC, &start_running_time);
}



/* ===================================================================== */
/* Print Help Message                                                    */
/* ===================================================================== */
INT32 Usage()
{
    cerr << "This tool translated routines of an Intel(R) 64 binary"
         << endl;
    cerr << KNOB_BASE::StringKnobSummary();
    cerr << endl;
    return -1;
}


/* ===================================================================== */
/* Main                                                                  */
/* ===================================================================== */

int main(int argc, char * argv[])
{
    // Open output profile file.
    out = new std::ofstream("edge-profile.csv");

    // Initialize pin & symbol manager
    if( PIN_Init(argc,argv) )
        return Usage();

    PIN_InitSymbols();

    // Register create_tc
    IMG_AddInstrumentFunction(create_tc, 0);

    // Create internal thread to start and stop profile gathering.
    THREADID tid = PIN_SpawnInternalThread(start_stop_profile_gathering_thread_func, NULL, 0, NULL);
    if (tid == INVALID_THREADID) {
        cerr << "failed to spawn a thread for commit" << endl;
    }

    // Start the program, never returns
    PIN_StartProgramProbed();

    return 0;
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
