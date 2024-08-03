all: coq c

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

coq: Makefile.coq
	+make -f Makefile.coq all
	@[ -f ./glue.c ] && mv ./glue.c ./c/ || true
	@[ -f ./glue.h ] && mv ./glue.h ./c/ || true
	@[ -f ./program.c ] && mv ./program.c ./c/ || true
	@[ -f ./program.h ] && mv ./program.h ./c/ || true
	
clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f ./c/glue.{c,h} ./c/program.{c,h}
	rm -rf ./program ./program.dSYM

c:
	gcc -I ./certicoq/plugin/runtime -lncurses -w -g -o program ./c/main.c ./c/program.c ./c/glue.c ./c/foreign.c

.PHONY: all Makefile.coq coq clean c
