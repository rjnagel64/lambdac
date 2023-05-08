
RTSFLAGS = -O2

# Hmm. Maybe I should provide two targets:
#   rts/librts-debug.a
# and
#   rts/librts-opt.a
# The compiler can then decide which one to link a user program against, which
# would be helpful for alternating between ASAN and optimized program runs.
# I'm not quite sure how to write concise 'make' rules for that, without lots of duplication.
rts/librts.a: rts/alloc.o rts/prim.o rts/control.o rts/panic.o rts/string_buf.o rts/simple_record.o rts/main.o
	ar -crs rts/librts.a rts/alloc.o rts/prim.o rts/control.o rts/panic.o rts/string_buf.o rts/main.o

rts/alloc.o: rts/alloc.c rts/alloc.h rts/panic.h rts/string_buf.h
	clang $(RTSFLAGS) -c rts/alloc.c -o rts/alloc.o

rts/prim.o: rts/prim.c rts/prim.h rts/alloc.h
	clang $(RTSFLAGS) -c rts/prim.c -o rts/prim.o

rts/control.o: rts/control.c rts/control.h rts/alloc.h
	clang $(RTSFLAGS) -c rts/control.c -o rts/control.o

rts/panic.o: rts/panic.c rts/panic.h
	clang $(RTSFLAGS) -c rts/panic.c -o rts/panic.o

rts/string_buf.o: rts/string_buf.c rts/string_buf.h
	clang $(RTSFLAGS) -c rts/string_buf.c -o rts/string_buf.o

rts/simple_record.o: rts/simple_record.c rts/simple_record.h rts/alloc.h rts/panic.h rts/prim.h
	clang $(RTSFLAGS) -c rts/simple_record.c -o rts/simple_record.o

rts/main.o: rts/main.c rts/alloc.h rts/control.h rts/panic.h rts/string_buf.h
	clang $(RTSFLAGS) -c rts/main.c -o rts/main.o

.PHONY: clean
clean:
	rm -f rts/*.o
	rm -f rts/librts.a
