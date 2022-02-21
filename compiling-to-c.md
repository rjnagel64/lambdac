
# Compiling a Functional Programming Language to C

## I - Continuation Passing Style

Parsing is boring. Type-checking is not relevant/required, because LISP exists.

Generate a tree of basic blocks (graph, with recursion).

## II - Closure Conversion

Annotate functions and continuations with free variables.

## III - Hoisting

Separate closure *declaration* from closure *allocation*. Denest definitions.

## IV - Code Generation and Runtime Support

Trampolined tail calls, GC, data layout, and primops.

## Appendix A: Parsing

## Appendix B: Type Checking

## Appendix C: Optimization

Optimizations on `TermK` (inlining, DCE, CSE, etc.). Optimizations in codegen
(calling conventions, etc.)

## Appendix D: References and Inspiration

inspire: Detail from this were used to implement this
reference: I implemented things using my ideas, and then found that my ideas are well-known

* Compiling with Continuations, Continued: inspire CPS, CC
* CHICKEN Internals: The Garbage Collector: reference C generation
* GHC RTS: reference thunk entry code
