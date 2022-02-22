
# A Miniature Lambda Calculus that Compiles to C

During my time programming, I've written a lot of type checkers. I've also
written maybe half that many frontends and interpreters. Yet, I've never quite
been able to figure out how functional languages get compiled.

So eventually, I buckled down and went through the nuts and bolts of
continuation passing style, closure conversion, and mark-sweep garbage
collection, and assembled them into this prototype.

Strictly-evaluated lambda calculus with primitive integers but not much else.
Code is compiled to C and linked with a rather small runtime.

# Hard parts

* Closure conversion for recursive bind groups: recursive bind groups have
  closures with cyclic references to each other.
* Tracing GC through closure environments: Eventually, I just added an extra
  function pointer to each closure that performs the appropriate tracing.
*

# Planned features and improvements

* Sums and products, projections and case analysis.
* A type-checker
* Smarter calling conventions: currently, all functions accept one boxed
  argument and pass one boxed argument to their continuation. Passing multiple
  arguments at once, unboxing arguments, typed value representations (e.g., a
  value of type `int32` cannot be `inl(v)`, etc.), and many more improvements
  are possible.
* Optimizations before code generation: inlining, dead code elimination,
  call-pattern specialization, and many others.

# The Compilation Process

* Input
* Parsing
* Type-Checking
* CPS
* CC
* Hoisting
* Generation

# References

* Compiling with Continuations, Continued
* That paper about PHOAS
* jozefg gist about closure conversion
* It turns out, my compilation scheme is quite similar to a simplified version
  of [CHICKEN Scheme](https://www.more-magic.net/posts/internals-gc.html)