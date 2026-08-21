.NOTPARALLEL:

all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

check: all
	python3 test_wigderson.py

rebuild:
	@+$(MAKE) clean
	@+$(MAKE) all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall

distclean: clean
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all check rebuild clean distclean force
