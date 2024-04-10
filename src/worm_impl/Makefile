SOURCES = utils.ml identifier.ml typ.ml term.ml evaluation.ml typing.ml functional.ml test.ml

EXEC = test


all:
	ocamlopt -o $(EXEC) $(SOURCES)

doc:
	ocamldoc -latex $(SOURCES) -o $(EXEC).tex

run: all
	./$(EXEC)

clean:
	rm -f *.o *.cm[iox] *.aux *.fdb_latexmk *.fls *.log *.synctex.gz *.toc *~ .*~ #*# 
	rm -f $(EXEC)
	rm -f $(EXEC).opt
