# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := Makefile.coq Makefile.icfp25.coq build-icfp25 \
				clean cleanall distclean
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile Make Make.icfp25

.DEFAULT_GOAL := invoke-coqmakefile

COQMAKEFILE       = $(COQBIN)coq_makefile
COQMAKE           = $(MAKE) --no-print-directory -f Makefile.coq
COQMAKE_ICFP25    = $(MAKE) --no-print-directory -f Makefile.icfp25.coq

Makefile.coq: Makefile Make
	$(COQMAKEFILE) -f Make -o Makefile.coq

Makefile.icfp25.coq: Makefile Make.icfp25
	$(COQMAKEFILE) -f Make.icfp25 -o Makefile.icfp25.coq

invoke-coqmakefile: Makefile.coq
	$(COQMAKE) $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

build-icfp25: Makefile.icfp25.coq invoke-coqmakefile
	$(COQMAKE_ICFP25)

theories/%.vo: Makefile.coq
	$(COQMAKE) $@

icfp25/%.vo: Makefile.icfp25.coq
	$(COQMAKE_ICFP25) $@

clean::
	@if [ -f Makefile.coq ]; then $(COQMAKE) clean; fi
	@if [ -f Makefile.icfp25.coq ]; then $(COQMAKE_ICFP25) clean; fi

cleanall::
	@if [ -f Makefile.coq ]; then $(COQMAKE) cleanall; fi
	@if [ -f Makefile.icfp25.coq ]; then $(COQMAKE_ICFP25) cleanall; fi

distclean:: cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f Makefile.icfp25.coq Makefile.icfp25.coq.conf

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
