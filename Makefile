# Override to match your opam switch, or set to empty to skip opam env setup:
#   make OPAM_SWITCH= all
OPAM_SWITCH ?= 5.2.0+trunk

ifneq ($(OPAM_SWITCH),)
  OPAM_SETUP := eval $$(opam env --switch=$(OPAM_SWITCH)) &&
else
  OPAM_SETUP :=
endif

.PHONY: all test clean

all:
	$(OPAM_SETUP) $(MAKE) -C src

test: all
	$(OPAM_SETUP) bash scripts/run_tests.sh

clean:
	$(MAKE) -C src clean
