
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
	rm -f fact
