# Specific rules for building with ghc
# $Id: ghc.mk 1744 2005-08-23 16:17:12Z wlux $
#
# Copyright (c) 2002-2004, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for ghc
GHC_HCFLAGS = -H12m # -Rghc-timing

# additional suffix rules
.SUFFIXES: .hs .lhs .hi .o
.hs.o:
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) $($*_HCFLAGS) -c $< -o $@
.lhs.o:
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) $($*_HCFLAGS) -c $< -o $@
.o.hi:
	@test -f $@ || \
	(echo "$@ does not exist!"; \
	 echo "Remove $< and run make again."; exit 1)

# programs
mach: $(mach_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(mach_OBJS)
cycc: $(cycc_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(cycc_OBJS)
cymk: $(cymk_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(cymk_OBJS)
newer: $(newer_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(newer_OBJS)

# additional cleanup rules
mostlyclean-dir::
	-rm -f Main.hi

# compute the dependencies
# NB: ./ prefixes stripped from dependencies for proper operation with BSD make
depend-dir: $(mach_SRCS) $(cycc_SRCS) $(cymk_SRCS) $(newer_SRCS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -M -optdep-f -optdep.depend.ghc \
		$(mach_SRCS) $(cycc_SRCS) $(cymk_SRCS) $(newer_SRCS)
	sed 's,\./,,' .depend.ghc > .depend
	@rm -f -- .depend.ghc .depend.ghc.bak
