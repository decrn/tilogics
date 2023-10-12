# Always run with nproc jobs by default. Can be overridden by the user.
MAKEFLAGS := --jobs=$(shell nproc)

# Comment out the below line if you want to be quiet by default.
VERBOSE ?= 1
ifeq ($(V),1)
E=@true
Q=
else
E=@echo
Q=@
MAKEFLAGS += -s
endif

SRCS := $(shell egrep '^.*\.v$$' _CoqProject | grep -v '^#')
AUXS := $(join $(dir $(SRCS)), $(addprefix ., $(notdir $(SRCS:.v=.aux))))

.PHONY: coq clean summaxlen install uninstall pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed-diff

coq: Makefile.coq
	$(E) "MAKE Makefile.coq"
	$(Q)$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject Makefile $(SRCS)
	$(E) "COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*

install uninstall pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed-diff: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq $@
