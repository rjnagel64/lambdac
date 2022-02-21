
demo: out.o rts.o
	clang out.o rts.o -o demo

out.o: out.c rts.h
	clang out.c -c -o out.o

fact: fact.o rts.o
	clang fact.o rts.o -o fact

rts.o: rts.c rts.h
	clang rts.c -c -o rts.o

fact.o: fact.c rts.h
	clang fact.c -c -o fact.o

.PHONY: clean
clean:
	rm -f rts.o
	rm -f fact.o
	rm -f out.o
	rm -f fact
	rm -f demo
