
# Documentation and Design Notes

This subdirectory contains notes on the design and implementation of LambdaC.

## Table of Contents

* `notes.md`: wide-ranging design notes on the implementation of LambdaC,
  including runtime representation of values, the (hypothetical) IO subsystem,
  optimizations, and more.
* `monomorphise.txt`: a worked example of what monomorphisation might have
  looked like as an implementation strategy for polymorphism, had it not been
  insufficient to deal with rank-n polymorphism.
* `arity.txt`: some notes and examples about uncurrying, arity-raising, and
  eta-expansion for optimization.
* `hoist.txt`: An attempt at formalizing `Hoist`, the final IR stage of LamdaC.
  Probably the most legible document in this subdirectory.
