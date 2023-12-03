default: coq c

.PHONY: default clean coq c

clean:
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./*.*.o
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h
	rm -f ./glue.c
	rm -f ./glue.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob

coq:
	coqc prog.v

c:
	gcc -I ../VeriFFI/certicoq/plugin/runtime -lncurses -w -g -o prog main.c prog.c glue.c prims.c
