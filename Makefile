# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := Makefile.coq Makefile.benchmark.coq build-benchmark \
				clean cleanall distclean
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile Make Make.benchmark

.DEFAULT_GOAL := invoke-coqmakefile

COQMAKEFILE       = $(COQBIN)coq_makefile
COQMAKE           = $(MAKE) --no-print-directory -f Makefile.coq
COQMAKE_BENCHMARK = $(MAKE) --no-print-directory -f Makefile.benchmark.coq

Makefile.coq: Makefile Make
	$(COQMAKEFILE) -f Make -o Makefile.coq

Makefile.benchmark.coq: Makefile Make.benchmark
	$(COQMAKEFILE) -f Make.benchmark -o Makefile.benchmark.coq

invoke-coqmakefile: Makefile.coq
	$(COQMAKE) $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

build-benchmark: Makefile.benchmark.coq invoke-coqmakefile
	$(COQMAKE_BENCHMARK)

clean::
	@if [ -f Makefile.coq ]; then $(COQMAKE) clean; fi
	@if [ -f Makefile.benchmark.coq ]; then $(COQMAKE_BENCHMARK) clean; fi

cleanall::
	@if [ -f Makefile.coq ]; then $(COQMAKE) cleanall; fi
	@if [ -f Makefile.benchmark.coq ]; then $(COQMAKE_BENCHMARK) cleanall; fi

distclean:: cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f Makefile.benchmark.coq Makefile.benchmark.coq.conf

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
