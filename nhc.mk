# Specific rules for building with nhc
# $Id: nhc.mk 1744 2005-08-23 16:17:12Z wlux $
#
# Copyright (c) 2002-2004, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for nhc
HMAKE = hmake -nhc98
NHC_HCFLAGS = +CTS -H8M -CTS -Inhc

# programs
mach: $(mach_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@
cycc: $(cycc_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@
cymk: $(cymk_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@
newer: $(newer_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@

# compute the dependencies
depend-dir:
	@: Do not delete this line
