
RTSFLAGS = -O0

rts/librts.a: rts/alloc.o rts/prim.o rts/control.o rts/panic.o rts/main.o
	ar -crs rts/librts.a rts/alloc.o rts/prim.o rts/control.o rts/panic.o rts/main.o

rts/alloc.o: rts/alloc.c rts/alloc.h rts/panic.h
	clang $(RTSFLAGS) -c rts/alloc.c -o rts/alloc.o

rts/prim.o: rts/prim.c rts/prim.h rts/alloc.h
	clang $(RTSFLAGS) -c rts/prim.c -o rts/prim.o

rts/control.o: rts/control.c rts/control.h rts/alloc.h
	clang $(RTSFLAGS) -c rts/control.c -o rts/control.o

rts/panic.o: rts/panic.c rts/panic.h
	clang $(RTSFLAGS) -c rts/panic.c -o rts/panic.o

rts/main.o: rts/main.c rts/alloc.h rts/control.h rts/panic.h
	clang $(RTSFLAGS) -c rts/main.c -o rts/main.o

.PHONY: clean
clean:
	rm -f rts/*.o
	rm -f rts/librts.a
