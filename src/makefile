##############################################################
# Makefile for the ex4 bprofile pintool (Intel Pin 4.0)
#
# Usage:
#   make PIN_ROOT=/path/to/pin
#
# The compiled tool is placed at obj-intel64/bprofile.so
##############################################################

ifdef PIN_ROOT
CONFIG_ROOT := $(PIN_ROOT)/source/tools/Config
else
CONFIG_ROOT := ../Config
endif
include $(CONFIG_ROOT)/makefile.config
include makefile.rules
include $(TOOLS_ROOT)/Config/makefile.default.rules
