
Miscellaneous design notes that don't fit neatly in the code.

# Table of Contents

* Code Generation & Runtime Representations
  * data types
  * type info and GC
  * polymorphism
  * existential types
  * one big switch-case
  * bytecode vm
* Type and Effect and Module System
  * effects/delimited continuations, maybe
  * IO, primitives, and FFI
  * ML modules
* Optimizations
  * uncurrying/arity raising/eta-expansion
  * inlining/specialization
  * etc.
* Random Weird Ideas
  * Multiple return values as a source-level feature
  * Automatic differentiation
  * Codata


# Code Generation & Runtime Representation

## Data Types and Values

### Booleans

Conceptually speaking, are booleans small integers (1-bit), or are the sum types with no payload?

Is there a distinction in their runtime layout? How they are used?

Probably "small integers". Right now, all sum payloads are kept behind an
indirection. (And even if I add `ALLOC_CTOR` with n fields, those fields are
still boxed.)

Update: booleans are now sum types, that happen to have no fields.
Update again: booleans are effectively small integers, but the field is named
'discriminant' so that the code-generation for case analysis still works on it. 

### Function Values (and continuation values?)

```
struct value {
  alloc_header header;
  uintptr_t words[];
};
```

```
inl x
+--------+---+----+
| header | 0 | &x |
+--------+---+----+

true
+--------+---+
| header | 1 |
+--------+---+

let fun f x = x + y in f
+--------+------+-------+--------+
| header | &env | &code | &trace |
+--------+------+-------+--------+
```

Basically the problem I have now is that I want closures to be values, so I can
have things like (not, true): pair containing closure and boolean.
This means that I need to encode closures as an array of words.
I think I just need to adjust the entry code, then? (I.E., the part of the
driver loop that invokes the code pointer?)

I also need to adjust the patching of cyclic closure references. Not that
different, but somewhat more verbose.

### Generating type declarations

Right now, a pair value is a header and a pair of words. Soon, I hope to turn
that into a header and a pair of `struct alloc_header *`. This is basically the
representation of a polymorphic pair `(a, b)`. I think it may be desirable to
generate type declarations corresponding to other types, such as a monomorphic
`data Foo = Foo Int Bool` being

```
struct Foo_value {
  struct alloc_header header;
  struct int_value *_0;
  struct bool_value *_1;
};
```

However, this requires an unknown number of `enum allocation_type`, so I think
I would need to have "info tables" a la GHC, or at least store a tracing method
in the header of a value.

Update: I am slowly approaching the possibility of implementing this, by
carrying `type_info` values as the runtime representation of type arguments.


## Tail Calls, Trampolines, and Thunks

Apple Clang 13.0.0 does not recognize any form of the `musttail` attribute.
*Real* clang doesn't have this problem, ugh.

`llvm-hs` uses LLVM 9, which supports `tail call` and `musttail call`
instructions. This is viable, I think. (Need to screw around with LLVM homebrew
to get it working, though...)


Consequently, I have to deal with trampolines and thunks.

A thunk is a saturated function call, a closure and its arguments. The
top-level driver loop repeatedly takes the current thunk, unpacks its
arguments, and calls its code pointer. The thunk needs an "entry code" to
unpack the arguments and jump to the code pointer.

An important point is that the entry code picked when creating a thunk is
chosen from the actual closure, not the expected closure type. This ensures
that a closure is always opened with the matching entry code. Otherwise, UB
occurs when a monomorphic closure is opened using polymorphic entry code (the
function pointers get cast wrong).


## Reabstraction Thunks

Early on when trying to implement polymorphism, I was running into issues with
function pointer casts. One potential solution I considered was generating
"adapter" continuation-thingies in order to handle the ABI mismatch between a
polymorphic closure and a monomorphic closure.

I chose not to implement it, because I thought that it would create a lot of
code bloat and I also wasn't sure how to integrate it into the type system, but
I think there's still potential in the idea.

The Swift ABI actually makes use of this, which is interesting: [ref][1]

[1]: https://gankra.github.io/blah/swift-abi/#reabstraction

As for the actual implementation, I think it might look something like this:

```
// Wrap a '(int) -> 0' closure 'foo' as a '(T) -> 0' closure
// Does this need a closure environment? I guess it does, to reference 'foo'.
void reabs_code(void *env, struct alloc_header *x) {
  tailcall_V(env->foo, AS_INT64(x));
}

// It also works in the other direction: Treat a polymorphic closure as a
// monomorphic closure, by using 'AS_ALLOC' appropriately.
```

The implementation is almost entirely trivial, as it just casts the arguments.
This is rather disappointing from the perspective of performance (this is
logically a no-op, but potentially necessary to avoid UB(?)).

The real test of whether this works, I think, would be something like the
identity function, where you need to abstract the input, and also need the
continuation to concretize the result. And of course, representing
reabstraction thunks in the IR.


## Closure Representation

This is the current (20f917d) closure representation:

```
struct closure {
  alloc_header header;
  void *env;
  void (*trace)(void *env);
  void (*code)();
};
```

We also have thunks, representing a closure with all its arguments applied; a
tail call.

It works well for monomorphic code, but dies horribly with UB on polymorphic
code. Why? Because even in simple situtations like `id`, the closure is a
concrete type, but it gets opened using the entry code for a polymorphic
closure. This sort of function pointer casting is UB.


The solution is to add a field to the closure:

```
struct closure {
  alloc_header header;
  void *env;
  void (*trace)(void *env);
  void (*code)();
  void (*enter)(void);
};
```

Each closure knows how to open its corresponding thunk, and therefore a closure
will always be opened by the matching entry code and UB will not occur.

Done: closures now store entry code, suspend methods use that entry code.


## Closure Environment Representation

Currently, closures are an existential type, effectively `∃c. c * (c, a, b ->
0) -> 0`. One consequence of this is that the environment must be boxed.
Additionally, empty environments (functions that don't capture anything) still
need to allocate `()`, which is purely useless.

So therefore, the question is, is it possible to have a non-existential
closure? For example, if we know that a function `f` captures `x : int` and `y
: bool`, what's stopping us from generating a data type like the following?

```
struct f_env {
  int64_box x;
  bool_box y;
};
struct f_closure {
  struct f_env env; // Environment not even boxed?
  void (*code)(struct f_env env, arg1..., kont1...);
};
```

The `suspend`/`tailcall` operation for this still needs to unpack/pass the
environment, so this isn't quite the same as a tuple that contains a raw
function pointer. (The tuple+raw function version would work, but the tuple
projections needed are verbose and kind of redundant.)

Another thing is the existential-argument-to-polymorphic-function thing.
Basically a variant of splitting product arguments, so effectively another
instance of worker-wrapper.

```
let fun foo (x : ∃a. t[a]) (k : bool -> 0) = e; in e'
===>
let fun foo @a (y : t[a]) (k : bool -> 0) = let x = pack <a, y> in e; in e'
```


## Existential Types and Garbage Collection

A typical existential value looks like this:

```
pack <τ, e> as ∃a.F[a]
```

At runtime, it looks like this:

```
// Runtime representation of '∃a.F[a]'
struct this_package {
  type_info a_info; // type info for 'a'
  foo_value *e; // foo_value is runtime representation of 'F[a]', I think.
};
```

It's not entirely clear how to trace this. The problem is that the type info
stored is for `τ`, not `F[τ]`, so we can't just use that.

On the other hand, `F[_]` should be statically known, so I *should* be able to
generate it like I generate product types and other things.


A third complication is that tracing `e` somehow needs to have access to
`tau_info`. Existentials may also be nested, and therefore need access to
multiple packaged type infos. I think this follows a stack discipline, so
*hypothetically*, I could generate something like this:

```
// Push existentially-quantified info onto stack.
void push_existential_info(type_info info);

// Remove n items from the stack.
void pop_existential_info(size_t num_items);

// Retrieve the nth item from the top of the stack.
type_info get_existential_info(size_t index);

void trace_this_package(boxed self_) {
  this_package *self = self_;
  push_existential_info(self->a_info);
  mark_gray(self->e, trace_foo_value);
  pop_existential_info(1);
}

void trace_foo_value(boxed self_) {
  foo_value *self = self_;
  ...
  type_info tau_info = get_existential_info(0);
}
```

Effectively, the calls to `get_existential_info` use deBruijn indices.

## Nested/Polymorphic Recursion

Do I need to construct new `type_info` at runtime?
Does the trace method need a free variable?

Polymorphic recursion requires constructing new type class dictionaries at
runtime. Does that mean we need to create new `type_info` at runtime as well?

```
-- Example goes here: perfect trees, rose trees(?), finger trees, etc.

-- Example: FunList
data FunList a b t
  = Done t
  | More a (FunList a b (b -> t))

map :: forall t t' a b. (t -> t') -> FunList a b t -> FunList a b t'
map @t @t' @a @b f xs = case xs of {
  Done (x : t) -> Done @t' (f x)
  More (y : a) (ys : FunList a b (b -> t)) ->
    -- Polymorphic recursion: 'map' instantiated with 'b -> t' and 'b -> t''
    More @a @b @(b -> t) y (map @(b -> t) @(b -> t') @a @b (\g x -> f (g x)) ys
}
```

Another example is perfect binary trees, with `2^n` elements. Descending into
the tree changes the element type from `a` to `Two a`, so polymorphic recursion
is needed when operating on it.

```
record Two a = Two { fst : a; snd : a }
data Perfect a
  = Z a
  | S (Perfect (Two a))

tmap : forall a b. (a -> b) -> Two a -> Two b
tmap @a @b f (Two x y) = Two @b (f x) (f y)

pmap : forall a b. (a -> b) -> Perfect a -> Perfect b
pmap @a @b f (Z x) = Z @b (f x)
pmap @a @b f (S t) = S @b (pmap @(Two a) @(Two b) (tmap @a @b f) t)
-- For brevity, assume all arguments are uncurried and passed as a unit.
```

I think this works out. In the recursive call, we are given info for `a` and
`b`, and we need to construct info for `Two a` and `Two b`. Info for
parametrized data types is uniform, so this all works out:

```
struct Two {
  struct alloc_header header;
  type_info a_info;
  struct alloc_header *fst;
  struct alloc_header *snd;
};
void trace_Two(struct alloc_header *alloc) {
  struct Two *v = AS_Two(alloc);
  mark_gray(v->fst, v->a_info);
  mark_gray(v->snd, v->a_info);
}
type_info Two_info = { trace_Two };
```


## Sum Types

### Sum-of-Products C representation (tagged union) 

Consider the following data declaration:

```
data Foo
  = Bar int
  | Baz unit
```

We can represent this in C with a tagged union:

```
struct Foo {
  struct alloc_header header;
  uint32_t discriminant;
  union {
    struct {
      struct constant *arg0;
    } Bar;
    struct {
      struct product_P0 *arg0;
    } Baz;
  } data;
};
```

This sum-of-products thing is literally a sum of products. Each branch is
effectively a 'product' decl, and stores the needed type info and fields.

However, I'm not particularly fond of using this scheme right now. For one
thing, it's wasteful of space, as every value is the size of the largest
constructor. Since constructed values cannot change their discriminant, that
extra space is completely wasted.

### Sum-of-Products C representation (case classes) 

One possible alternative is to use struct subtyping in a different way, with a
subtype for each constructor:

```
struct Foo {
  uint32_t discriminant;
};

struct Foo_Bar {
  struct Foo header;
  struct constant *arg0;
};

struct Foo_Baz {
  struct Foo header;
  struct product_P0 *arg0;
};
```

To the limits of my understanding, this is basically what case classes are in Scala.

### Built-ins versus user-defined

I hope to eventually have general user-defined algebraic data types. However,
I'm not remotely ready to implement them yet.

`struct sum` implemented a generic sum-of-products representation, but that
representation is too generic to easily migrate to the type-info-based GC.

All I really need are binary sums (`T + S` for any types `T` and `S`), and
booleans.

I have now replaced `struct sum` with specialized runtime representations for
binary sums and booleans, as follows:

```
struct sum {
  struct alloc_header header;
  uint32_t discriminant;
  type_info info;
  struct alloc_header *payload;
};

struct bool_value {
  struct alloc_header header;
  uint8_t discriminant;
};
```

`struct bool_value` is effectively the same as `struct constant`, but the fields are
named differently so that I can do case analysis on booleans.


## Recursion

Currently, `let fun f (x : a) : b = e1; fun g (y : c) : d = e2; in e`. One parameter.
(Extras are curried.)

* What if polymorphic recursion: not a problem, probably. Explicit type applications.
  * I think I meant, "what if polymorphic function is recursive, like `sum`"
  New version of letrec requires RHS to have form `\x -> e'`. This can be
  extended to support polymorphic functions by loosening that restriction to
  permit `\@a -> e'` as well.
* What if many arguments (in source?)
  * What if partially applied (in source?)
  `let fun` treats the first argument differently, which is kind of annoying.
  `letrec` treats all arguments the same.
* What if recursive values, not recursive functions:
  This is probably reasonable to implement. Like OCaml, I probably need to
  restrict `letrec` bound-terms to be "statically constructive", i.e., there
  is an obvious outermost constructor so that I can patch fields to make
  cycles.

### Fixpoint combinators

I don't actually want these, I'd rather just implement `letrec` directly.

Mutual recursion can be obtained as the fixpoint of a tuple of functions.
However, this has an extra layer of indirection through the tuple.

Fixpoint combinators can be implemented by using (iso)recursive types.


## Polymorphism

Add a list of type parameters to each `fun` binding.
(But doesn't this restrict us to prenex polymorphism? At the very least, it
inhibits optimizations because you can't mix term and type arguments when
joining argument lists)

Do polymorphic values make sense? `forall a. a` versus `forall a. a -> a` versus `forall a. Int`

At/After CC, polymorphic types are erased to values of sort `Alloc`.

### CPS for type abstractions/applications

```
CPS[forall a. t] == forall a. (CPS[t] -> 0) -> 0
```

This is the "standard" CPS translation of a `forall`. Apparently, in ML-style
systems where instantiating a forall is not "signficant work", there is a more
efficient translation. (Something like `forall a+. CPS[t] -> 0`?) Apparently it
works when the body of a type abstraction is already a value.

Example:

```
\ @a -> 3 + 5
```

Must be translated as

```
letabs f0 @a (k0 : int -> 0) =
  let t0 = 3 in
  let t1 = 5 in
  let t2 = t0 + t1 in
  k0 t2
in
halt f0
```

Because the body is not a value.

After closure conversion, type abstractions become no-argument,
one-continuation functions. The 'contify' optimization can turn this into a
no-argument continuation. Arity-raising/uncurrying should still work here.

I theory, I could have a combined type-term abstraction `let f0 a+ x+ k+ = e`,
but I think that would rule out the more-efficient translation when the body is
a value. (Or would it?)

### Type arguments at runtime

I can't completely erase type arguments (I think), because I need to provide
type information to the GC. Historically, this info was handled with `enum
allocation_type`, and could theoretically be achieved by storing a pointer to
an info table in every object header.

I have decided to instead carry around `type_info` values, as literal "type
arguments". They are passed as part of instantiation, and stored in closure
environments.

## One Big Switch-Case

CPS and the IRs that follow it are basically a tree/graph of basic blocks. It
gets a bit muddled when I turn each closure into its own function, but an
alternate path could be to make each basic block literally a basic block, using
a big switch-case or GCC's "labels as values"/"computed goto" to transfer
control.

This wouldn't be a silver bullet, but it would avoid needing to allocate a
thunk/trampoline for every control transfer. Modularity becomes a bit more
complicated though, because you need to be able to hand off control to some
other module's big switch-case.


## Bytecode VM

Another path I want to explore is a bytecode VM. However, for that, I need to
do some research on what a viable IR looks like. It seems that most VMs of this
type are stack-based, so there's a starting point, at least.

That paper about the Categorial Abstract Machine is one starting point, Zinc,
and the Krivine Machine are other starting points. [Tao][tao] is a functional
language with a bytecode VM to examine, too.

[tao]: https://github.com/zesterer/tao


# Type, Effect, and Module System

## Effects

### Answer Types

CPS turns a function `a -> b` into `(a, b => R) => R` for some fixed answer type `R`.

Effectful operations are ones that return `R`. So I can have `R` be something
that encodes the set of possible operations?

Basically, a system call for the runtime to perform?

```
enum answer_type {
  // words[] contains the halting value (restrict to integer?)
  HALT,
  // words[0] is entry code, remainder are thunk arguments
  FORCE_THUNK,
  // words[] is continuation to invoke with input value
  READ_INT32,
  // words[0] is value to display, words[1] is continuation
  PRINT_INT32,
  ...
};

struct answer {
  enum answer_type operation;
  uintptr_t words[];
};

switch (answer.operation) {
case HALT:
  printf("done\n");
  break;
case FORCE_THUNK:
  answer *next = answer->words[0](answer);
  free(answer);
  answer = next;
  break;
case READ_INT32:
  {
  int32_t x;
  scanf("%d\n", &x);
  answer *next = answer->words[0](answer, x);
  free(answer);
  answer = next;
  }
  break;
case PRINT_INT32:
  printf("%d\n", answer->words[0]);
  answer *next = answer->words[1](answer);
  free(answer);
  answer = next;
  break;
}
```

In an extreme case, I think I could make allocation operations effect
operations, kind of like how CHICKEN passes a continuation to the allocation/GC
routine. 

### Continuation-Based IO

An alternative to having an IO monad. Fairly well-aligned with by existing use
of continuations for computation.

Also, [this post](http://blog.sigfpe.com/2009/11/programming-with-impossible-functions.html)

From the runtime's perspective, suspending/resuming with an IO-computed value
is perfectly reasonable. From the user's perspective, there are two problems, though:

1. How to express the continuation of the IO operation (lambdas are clumsy)
2. How to maintain overall purity (I think I still need something like an IO
   monad, or at least an IO answer type)

### OI

This [blog post](http://comonad.com/reader/2011/free-monads-for-less-3/) has an
`OI` type for representing IO that boils down to being a codata type.

```
type FFI o i -- send/emit 'o' to outside world, receive 'i' back
newtype IO a = IO (forall r. (a -> r) -> (forall o i. FFI o i -> o -> (i -> r) -> r) -> r)
```

This type is a CPS-ed free monad built out these piece:

```
type FFI o i
-- Base functor
data OI ans = forall o i. OI o (FFI o i) (i -> ans)
instance Functor OI

-- CPS-ed free monad
-- Negative sum type, I think.
newtype F f a = F { runF :: forall r. (a -> r) -> (f r -> r) -> r }
instance Functor (F f) where
  fmap f (F g) = F (\kp -> g (kp . f))
instance Monad (F f) where
  return a = F (\kp _ -> kp a)
  F m >>= f = F (\kp kf -> m (\a -> runF (f a) kp kf) kf)

type IO a = F OI a
-- Flattened:
-- IO a
-- = F OI a
-- = forall r. (a -> r) -> (OI r -> r) -> r
```

The essential features is that there's an opaque type `FFI o i` for sending `o`
to the outside world and receiving `i` back. `FFI` operations are not called
directly, but there's something like a function `ffi :: FFI o i -> (o -> IO i)`.
IO monad operations compose like usual, but `IO` has a different internal
implementation that's friendlier to my system.

```
read_int : FFI unit int;
put_int : FFI int unit;
let main : IO () =
  ffi read_int () >>= \x -> ffi read_int () >>= \y -> ffi put_int (x + y)
in
main
```

FFI operations seem like they might end up being just another type of
suspension, but the details of IO are more complicated.

### FFI

Because I target C, FFI is theoretically as easy as emitting prototypes for
foreign functions and then linking with their definitions.

However, should foreign functions be treated as primitive (inline calls, like
`prim_addint32`), or should they suspend/resume?

### Coroutining

Implementing coroutines with `call/cc` and a queue is a classic example of
continuations for control structures. Would it be worthwhile to implement such
a thing in the runtime? Maybe not. Extra complexity, both for the runtime and
for the overall language, even if we already have a nice concept of
suspending/resuming.

If I have a (pri)queue of suspended thunks instead of just one, coroutines are
trivial. However, proper mulithreading make gc hard. Also, every single jump
becomes a yield point, which is slow.

I can imagine a setup where each thread has a trampoline and there is a
yield/resume thunk that pushes the current computation onto a global queue. I'm
not clear what that would look like from a user perspective, though.

(Multicore OCaml: EIO library, capabilities, support for thread-switching?)

### Reference Cells

`ref : * -> *` is a classic feature of ML. However, mutability interacts poorly
with polymorphism, leading to the "value restriction". Figure out what this
really means.

CubiML has problems with refcells also (for different reason?) Their solution
is to give two type parameters: one contravariant for writing, one covariant
for reading. Would this be at all helpful for avoiding the value restriction?

### Delimited Continuations

Delimited continuations don't play all that nicely with CPS. The problem is
that a continuation only provides an 'apply' operation, but delcont require the
ability to inspect/slice/compose continuations.

Therefore, to implement delcont, you either need to CPS your CPS code
(producing inefficient results), or re-introduce the notion of a
stack/linked-list of "activation records" to scan for particular prompt tags.

I think I *might* be able to maintain a chain of thunks for the activation
record stack?

Reference: [A Monadic Framework for Delimited Continuations][1] (Dybvig, Peyton
Jones, and Sabry)

[1]: https://legacy.cs.indiana.edu/~sabry/papers/monadicDC.pdf


## Type Systems (Especially for the later stages)

At a minimum, I need types `fun`, `cont`, and `value`. I hope to do something
like System F, though.

After closure conversion, types are converted into `Sort`s. `Sort`s are
basically runtime representations of values.

Everything is boxed right now. CPS and later stages all require exact arity
matching, but in practice those arities are 1 parameter/1 argument. I hope to
optimize this later.

### Polymorphic Closure Conversion

According to *From System F to Typed Assembly Language*, you need to record the
free type variables of a closure in its type environment.

Apparently, the "type environment" captured this way is also sort of
complicated. Minamide et al (1985?, "Polymorphic Closure Conversion") represent
the type environment using something that basically turns out to be singleton
types, but apparently there's also a way based on type erasure, so that all
polymorphic instantiations end up using the same runtime code.

My implementation of `type_info` structs is effectively Minamide's singletons.

### Monomorphisation

If I can't figure out how to mix CPS with System-F polymorphism, I can always
resort to monomorphising out the polymorphism. (For this, every polymorphic
definition would need a name, I think.)

Unfortunately, this is not a complete solution. I hope to implement all of
System F, but monomorphisation only works for rank 1 (prenex) polymorphism.

### Recursive types and values

Idea: CPS translation for isorecursive types.
* roll and unroll constructs (that cast to/from `alloc_header`)
* recfun becomes roll?
* polymorphism is fine.
* ez data types (as fixed point of polynomial functor)

* Works for type-level recursion, but I still somehow need to have value-level
  recursion.
* (Apparently roll/unroll imply value-level recursion?)
  (Yes, recursive types enable fixpoint combinators)
  (So include a fixpoint term directly, to reduce inefficiency?)
  (==> justification for including letrec?)
  The essential aspect of a fixpoint operator is that it makes a value cyclic.
  (Generally, makes a set of values cyclic among each other.)

## Module System

I might as well go for ML-style modules.


Implicit top-level module?

```
signature FOO = sig val x : int; end
module Foo : FOO =
struct
  val x : int = 17;
end

signature BAR = sig val y : bool; val z : int -> int end
module Bar (X : FOO) : BAR =
struct
  val y : bool = X.x == 0;
  val z : int -> int = \ (n : int) -> n + X.x;
end

val main : int = let module Quux = Bar Foo; in (Quux.y, Quux.z 32)
```

Compiles and evaluates to `(false, 49)`.


Should I full-on defunctorize (like MLton)? Do I need to have a notion of a
module at runtime? (Modules are existentially quantified product types, so I
could if I needed to, but eliminating administrative computation is desirable)


# Optimization

## Unboxing arguments and continuations

Note: `(a + b) -> 0` is isomorphic to `(a -> 0, b -> 0)`. In other words, a
continuation for a sum type is basically the double-barrelled CPS transform for
exception handling.

I think that this can be fairly straightforward to optimize, using call-pattern
specialization/worker-wrapper.

(E.G., rewrite `f x k` to `let j1 z = k (Left z); j2 = k (Right z); in f x j1 j2`
and specialize `k` on patterns `z :- Left z` and `z :- Right z`.)

This rewrite is probably most beneficial if only one of the branches is
invoked. Or maybe it's beneficial overall, because it turns allocations and
case analysis into direct jumps.


For example, given `letfun f (p : A * B) (q : (C + D) -> 0) = e; in e'`, we can
rewrite it into:

```
letfun f_worker (x : A) (y : B) (j : C -> 0) (h : D -> 0) =
  let p : A * B = (x, y) in
  letcont q z = case z of { inl x -> j x; inr y -> h y } in
  e; -- call sites of f turned into f_worker manually, to avoid recursive inlining.
in
letfun f (p : A * B) (q : (C + D) -> 0) =
  letcont j1 x = q (inl x); in
  letcont j2 x = q (inr x); in
  f_worker (fst p) (snd p) j1 j2;
in
e'
```

`p` and `q` can be inlined in `e` to clean up the body. Call sites of `k` still
need to be rewritten into `k_worker`, though.

It's still basically worker-wrapper. Furthermore, once flattened like this,
unused arguments can be discarded.


In addition to flattening the either/except monad, CPS can also flatten the
state monad: `s -> (a, s)` CPS-transforms to `(s, (a, s) -> 0) -> 0`.

With arity analysis, `a -> (s -> (b, s))` can turn into `(a, s, (b, s) -> 0) -> 0`.


## Lifting Environment References into Parameters

Another idea is turning environment fields into parameters. (Specifically, the
closure for an if-branch has no parameters but does capture variables through
the environment. By turning captures into arguments -- lambda-lifting? -- there
can be less indirections) This may not always be possible, if the closure is
captured by something else? Consider the allocation of `k10` here.

```
k10 {closure k0, value n} (value x2) =
  let value z10 = prim_addint32(@.n, x2);
  @.k0 z10;
k200 {closure k0, value n, closure tri} (value z) =
  let value x10 = -1;
  let value z00 = prim_addint32(@.n, x10);
  let
    closure k10 = k10 {closure k0 = @.k0, value n = @.n}
  in
  @.tri z00 k10;
```

A common case is for an `if`-expression. There are two zero-argument closures,
and a case-terminator afterward. There shouldn't be anything capturing the
branch-continuations, hoisting should possibly be able to turn environment
fields into parameters when hoisting.

Actually, this seems viable. Environments are effectively product types/values,
so this would be an extension of flattening products into multiple arguments.

Yes, the environment parameter is a product type, so it makes sense to be able
to flatten it into multiple parameters. Furthermore, the closure itself can
have multiple environment fields in an analogous manner.


## N-ary and 0-ary products

```
data TypeK
  = ProdK [TypeK]
  | ...
```

This would make it easier to have many-argument functions, maybe. (no need to
worry about associativity)

Is `unit`/`()` just a 0-tuple? It might be.
`()` as a 0-tuple makes sense. However, I'm using `t * s` at the type level, so
I think I need to have `unit` still.

(And how does `t * s * r` flatten into `ProdK`? Left-assoc? Right-assoc?
cons/snoc/append?) Maybe source-level `t * s` is always binary, but later
stages may flatten? Hmm, not quite -- tuple literals are a thing.

Flattening can work for both products and sums:
`(a + b) + (c + d) ==> AnyOf [a, b, c, d]`
`(a * b) * (c * d) ==> AllOf [a, b, c, d]`


Another consideration is how products are exposed to the user. Currently, they
only exist as pair types `t * s` with values `(e1, e2)`. Multiplication of
types tends to be binary, so values tend to be pairs. Haskell-style tuples and
tuple types avoid the 2-ary bias, at cost of making ambiguity between
type-level tuples and tuple types. (I have no intentions to add type-level
values, but it's still worth considering)


Records are another example of n-ary products, this time with named fields.
Fixed-field records are perfectly reasonable (and desugar to tuples), but row
polymorphism and/or subtyping complicate the design space greatly. At minimum,
I should avoid Haskell's half-assed record types.


## Continuations are second-class

I haven't quite figured out what that means, though. At the end of compilation,
functions and continuations have been folded into a single notion of closures,
but there's probably structure to exploit for more efficient continuation
invocations.

One thing is that continuations are always fully applied (cf. GHC join points).
Another is that a continuation is never passed to another continuation (`JumpK
CoVar TmVar`, not `JumpK CoVar CoVar`)

However, continuations are still passed to functions, and do capture variables.
So I'm not really sure how to exploit this. (Other than by writing a native
code generator so I can tailcall directly without trampolining)

So therefore, I can split `ContK :: TypeK -> TypeK` into `FunK :: [TypeK] ->
[TypeK] -> TypeK` and `ContK :: [TypeK] -> TypeK`. I need to split them,
because functions have both term and continuation parameters, but continuations
only have term parameters.

```
data TypeK
  -- Represents (t1, t2, ..., s1 -> 0, s2 -> 0, ...) -> 0
  -- (basically, (NP ts, NS ss -> 0) -> 0)
  = FunK [TypeK] [TypeK]
  -- Represents (s1, s2, ...) -> 0
  | ContK [TypeK]

data FunDef = FunDef TmVar [(TmVar, TypeK)] [(CoVar, TypeK)] TermK
data ContDef = ContDef CoVar [(TmVar, TypeK)] TermK
```

When a function has no continuation arguments, it can turn into a continuation.
Contify removes coterm arguments, with a variant of call-pattern specialization
(SpecConstr mostly cares about what constructors are passed as arguments,
contify cares about which specific continuations are used)

In GHC `Note [Join points]`, it explains that join points/jumps can be compiled
as named blocks and jumps. The jumps do not need to allocate closures, and are
thus much more efficient.

Unfortunately, in my C codegen, I do not have the ability to do real
tailcalls/jumps, so I have to make continuation closure/thunk jumps.

If/When I do a native code generator, I might be able to exploit this more
thoroughly.


What if I don't closure-convert continuations? Hmm. Continuations are still
passed as arguments, though? For this I think I would need a real stack again.


## Beta-Reduction and Discarding Unused Bindings

```
let p = (x, y) in let z = fst p in e
==>
let p = (x, y) in e[z := x]

let z = inl x in case z k1 k2
==>
k1 x
```

After doing a "downward" pass to simplify things, you can count occurrences on
the way back up to annotate binders. (e.g., unused, one-shot, etc.)

However, I don't have a way of annotating binders, so I can simply discard
unused bindings and ignore other multiplicity information.

(I now have annotations on function/continuation definitions, so I can record
this information now, I think.)


## Applied Argument Analysis (AAA/call arity(?)/arity raising(?))

For each parameter of function/continuation type, count transitively the number
of arguments applied to that parameter.

```
letcont k x = halt x -- no arguments applied to x
letcont k f = f 1 k' -- k' applies n arguments; f 1 k' applies n+1 arguments
```

recursive case: iter to fixpoint. start wi noapp

once params annotated, inspect call sites to see how many applications are
always performed.

```
letfun f (x : 2 app) (k : 1 app);
letcont k (x : 3 app);
let x0 = ...
... f x0 ... k x0
-- f x0: 2 args applied
-- k x0: 3 args applied
-- => 2 args always applied
```

then rewite fn/app to use multiple parameters

Does AAA work through case branches? (no, probably)
Does AAA work through captured variables?
Does AAA work if a function has multiple continuations?

The paper *Tag-free garbage collection using explicit type parameters* mentions
that their compiler (modified from Caml Light) contains an uncurrying pass,
which is basically what I'm trying to do here. (Hmm. Can't really find the
implementation, though. And there's a decent chance they use direct-style IR,
not CPS, anyway.)

In addition to uncurrying value arguments, I can most likely uncurry type
arguments as well.


## Case-Commuting Conversion

Is this still necessary, or does the use of continuations (join points) obviate
it? I think it is unnecessary. CPS translation inherently unrolls nested cases
and uses join points.


## Inlining

* Compute definition size (easy)
* Count occurrences of definition (~easy)
* Expand occurrences of definition (~easy)
  * Peform renaming of parameters for arguments over inlined defn (since both are lists of variables)
  * Append renamed inlined defn to definition (Because definitions are basically straight-line code)

Curried functions do not inline well, because the outermost function is very
large, and also because inlining an argument requires inlining the function
definition, and then the continuation definition (2 steps).


## Specialization

Specializing polymorphic definitions: rather similar to inlining.

```
let abs dup0 @a (k0 : (a, (a * a) -> 0) -> 0) =
  let fun dup1 (x : a) (k1 : (a * a) -> 0) =
    let t0 = (x, x) in
    k1 t0
  in
  k0 dup1
in
let cont k0 (dup_bool : (bool, (bool * bool) -> 0) -> 0) =
  let cont k1 (z : bool * bool) =
    halt z
  in
  dup_bool true k1
in
dup0 @bool k0
```

Becomes

```
let cont k0 (dup_bool : (bool, (bool * bool) -> 0) -> 0) =
  let cont k1 (z : bool * bool) =
    halt z
  in
  dup_bool true k1
in
let fun dup1 (x : bool) (k1 : (bool * bool) -> 0) =
  let t0 = (x, x) in
  k1 t0
in
k0 dup1
```

Becomes

```
let fun dup1 (x : bool) (k1 : (bool * bool) -> 0) =
  let t0 = (x, x) in
  k1 t0
in
let cont k1 (z : bool * bool) =
  halt z
in
dup1 true k1
```


## Common Subexpression Elimination

If a tuple component is projected multiple times, the CPS IR contains multiple
statements projecting it. They should be deduplicated.

```
let p = (3, 4) in
fst p + fst p
~~~>
let p = (3, 4) in
let t1 = fst p in
let t2 = fst p in
let z = t1 + t2 in
z
~~~>
let p = (3, 4) in
let t1 = fst p in
let z = t1 + t1 in
z
~~~>
let p = (3, 4) in
let t1 = 3 in
let z = x + x in
z
~~~>
let z = 6 in
z
```

More generally, common expressions should be merged.


# Random Weird Ideas

Neat ideas for a PL, that require significant thought to work out their
implementation or implications

## Source-level multiple returns

CPS has a straightforward notion of multiple return values: when multiple
arguments are passed to the continuation. What that looks like at the source
level, however, is less clear.

For starters, almost all constructs are single-value. For example, if `f x`
returns 3 values, `inl (f x)` probably doesn't make much sense.

But what if it did? Maybe `inl e` applies the constructor `inl` to each value
returned from `e`.

Likewise, if `fn` returns two function values, and `arg` returns 3 argument
values, what does `fn arg` produce? `[fn1 arg1, fn1 arg2, fn1 arg3, fn2 arg1,
fn2 arg2, fn2 arg3]`, or `[fn1 arg1, fn2 arg1, fn1 arg2, fn2 arg2, fn1 arg3, fn2
arg3]`? Or maybe even 2-d returns, though that rapidly gets out of hand.

`let`-expressions allow binding multiple returns, and `case`-expressions allow
matching on multiple values at once.

```
let f : unit -> (int, bool); -- (t, s) for multiple values, (t * s) for product
let _, b = f ();
case f () of
  17, false -> "yay"
  _, true -> "nay"
```

Maybe instead of implicitly broadcasting, default to single-return and have a
lightweight operator (a la Julia's '.') to perform the broadcast.


## Automatic differentiation

Autodiff can work by transforming the program to include more variables and
operations to track derivative values.

example:

```
let x = y + z in
let w = t * x in
f w ret
```

becomes

```
let x = y + z in
let dx = dy + dz in
let w = t * x in
let t0 = dt * x in
let t1 = t * dx in
let dw = t0 + t1 in
f w dw ret
```

Which types are eligible for autodiff?
The transformed program can be optimized using standard techniques.


## Codata types and values

Codata are very much not a priority here, but they are interesting. The might
possibly be implemented analogous to function values, but with multiple code
pointers. There is still quite a bit of asymmetry in this scheme; I want to
think more about how/why codata/data are as they are.

```
codata Fun A B {
  .app : A |- B
}
==> CallK f xA kB
codata NProd A B {
  .fst : |- A
  .snd : |- B
}
==> NFstK p kA
==> NSndK p kB
codata NSum A B {
  .either : |- A, B
}
==> NEitherK s kA kB
```

Generally, codata types require the following constructors in `CPS`:

* `ObserveK :: TmVar -> Observation -> TermK`
* `data Observation = Observation CodataMethod [TmVar] [CoVar]`

There is asymmetry here, because the coterm is fused to the scrutinee (in `ObserveK`)

### Codata via CPS?

```
// It may be possible to translate codata types to C by doing something like CPS or BB?
// This is for the positive case, I think.
// If the polarity is negative, I would need to dualize all this (??)
// (And that's where the trouble with reify/compile when flipping polarity comes from)

data Mul a b where
  .Both : ( a, b |- )

data Add a b where
  .Inl : ( a |- )
  .Inr : ( b |- )

codata With a b where
  .fst : ( |- a )
  .snd : ( |- b )

codata Par a b where
  .either : ( |- a, b )

data Zero where

data One where
  .One : ( |- )

codata Bot where

codata Top where
  .top : ( |- )

data Negate a where
  .Foo : ( |- a )

codata Invert a where
  .foo : ( a |- )
```

Corresponds to these C declarations, potentially.

```
struct mul_value {
  struct value *fst;
  struct value *snd;
};

struct add_value {
  bool tag;
  struct value *payload; // no sum types in C, have to encode as (ptr + ptr) as (2 * ptr)
};

// Kind of like CPS-converting, or boehm-berarducci encoding
struct with_value {
  void *env; // probably.
  void (*fst)(struct closure_value *k);
  void (*snd)(struct closure_value *k);
};

struct par_value {
  void *env; // probably.
  void (*either)(struct closure_value *k1, struct closure_value *k2);
};

struct zero_value;

struct one_value {
};

struct bot_value {
  void *env;
};

struct top_value {
  void *env;
  void (*top)();
};

struct neg_value {
  // ?
  ;
};

struct inv_value {
  // ?
  ;
};
```

