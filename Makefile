all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

admitted :
	@grep -nR --color=auto [aA]dmit theories/ || echo "No admitted proof found !"

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force
