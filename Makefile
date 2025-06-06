# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := Makefile.coq Makefile.misc.coq build-misc \
				clean cleanall distclean
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile Make Make.misc

.DEFAULT_GOAL := invoke-coqmakefile

COQMAKEFILE       = $(COQBIN)coq_makefile
COQMAKE           = $(MAKE) --no-print-directory -f Makefile.coq
COQMAKE_MISC      = $(MAKE) --no-print-directory -f Makefile.misc.coq

Makefile.coq: Makefile Make
	$(COQMAKEFILE) -f Make -o Makefile.coq

Makefile.misc.coq: Makefile Make.misc
	$(COQMAKEFILE) -f Make.misc -o Makefile.misc.coq

invoke-coqmakefile: Makefile.coq
	$(COQMAKE) $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

build-misc: Makefile.misc.coq invoke-coqmakefile
	$(COQMAKE_MISC)

theories/%.vo: Makefile.coq
	$(COQMAKE) $@

misc/%.vo: Makefile.misc.coq
	$(COQMAKE_MISC) $@

clean::
	@if [ -f Makefile.coq ]; then $(COQMAKE) clean; fi
	@if [ -f Makefile.misc.coq ]; then $(COQMAKE_MISC) clean; fi

cleanall::
	@if [ -f Makefile.coq ]; then $(COQMAKE) cleanall; fi
	@if [ -f Makefile.misc.coq ]; then $(COQMAKE_MISC) cleanall; fi

distclean:: cleanall
	rm -f Makefile.coq Makefile.coq.conf
	rm -f Makefile.misc.coq Makefile.misc.coq.conf

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
