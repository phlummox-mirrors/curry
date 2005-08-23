# Specific rules for building with hbc
# $Id: hbc.mk 1744 2005-08-23 16:17:12Z wlux $
#
# Copyright (c) 2002-2004, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for hbc
HBCMAKE = hbcmake -f $(srcdir)/hbc.mk
HBC_HCFLAGS = -I hbc
HBCFLAGS = -H20m -noflags -s

# programs
mach: $(mach_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@
cycc: $(cycc_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@
cymk: $(cymk_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@
newer: $(newer_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@

# compute the dependencies
depend-dir:
	@: Do not delete this line
