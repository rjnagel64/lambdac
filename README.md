
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
* Hoisting: ultimately, the purpose of hoisting is to separate the
  *declaration* of closure types from the *allocation* of those closures.

# Planned features and improvements

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

* *Compiling with Continuations, Continued* by Andrew Kennedy
* After implementing closure conversion, I found that my implementation has
  much in common with [The Simple Essence of Closure Conversion](https://siek.blogspot.com/2012/07/essence-of-closure-conversion.html)
  by Jeremy Siek. I had actually read it before, but the notation (`δ` and `γ`
  functions) prevented me from understanding the connection.
* [This gist](https://gist.github.com/jozefg/652f1d7407b7f0266ae9) about closure conversion
* It turns out, my compilation scheme is quite similar to a simplified version
  of [CHICKEN Scheme](https://www.more-magic.net/posts/internals-gc.html)
* [Crafting Interpreters](https://www.craftinginterpreters.com), for details of
  the garbage collection algorithm
