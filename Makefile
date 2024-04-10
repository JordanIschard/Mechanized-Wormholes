# ============ Variables ============

SRC = src/
MAIN = test
EXEC = wormhole


# =============== Coq ===============

all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@


# ============== OCaml ==============

compile:
	@rm -f $(SRC)$(EXEC)
	ocamlbuild -Is $(SRC) $(SRC)$(MAIN).native
	@cp -L test.native $(SRC)$(EXEC)
	@rm $(MAIN).native

run: compile
	./$(SRC)$(EXEC)

# ============== Clean ===============

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf
	@rm -f $(SRC)*.o $(SRC)*.cm[iox] $(SRC)*.aux $(SRC)$(EXEC).opt

cleanall : clean
	@rm -f $(SRC)$(EXEC)

.PHONY: all clean force
