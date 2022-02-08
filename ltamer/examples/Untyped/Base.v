Parameter base : Set.
Parameter encode : base -> nat.

Axiom encode_inj : forall x y, encode x = encode y -> x = y.

Parameter base_eq_dec : forall x y : base, {x = y} + {x <> y}.
