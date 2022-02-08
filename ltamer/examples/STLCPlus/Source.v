(* Copyright (c) 2008, Adam Chlipala
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

Require Import LambdaTamer.LambdaTamer.

Set Implicit Arguments.


Inductive type : Type :=
| TBool : type
| TArrow : type -> type -> type
| TUnit : type
| TProd : type -> type -> type
| TSum : type -> type -> type
| TNat : type
| TList : type -> type.

Notation "'Bool'" := TBool : source_scope.
Infix "-->" := TArrow (right associativity, at level 61) : source_scope.
Notation "'Unit'" := TUnit : source_scope.
Infix "**" := TProd (left associativity, at level 59) : source_scope.
Infix "++" := TSum (right associativity, at level 60) : source_scope.
Notation "'Nat'" := TNat : source_scope.
Notation "'List' t" := (TList t) (at level 58) : source_scope.

Bind Scope source_scope with type.
Delimit Scope source_scope with source.

Open Local Scope source_scope.

Section vars.
  Variable var : type -> Type.

  Inductive term : type -> Type :=
  | EVar : forall t,
    var t
    -> term t

  | ETrue : term TBool
  | EFalse : term TBool

  | EApp : forall t1 t2,
    term (t1 --> t2)
    -> term t1
    -> term t2
  | EAbs : forall t1 t2,
    (var t1 -> term t2)
    -> term (t1 --> t2)

  | EUnit : term Unit

  | EPair : forall t1 t2,
    term t1
    -> term t2
    -> term (t1 ** t2)
  | EFst : forall t1 t2,
    term (t1 ** t2)
    -> term t1
  | ESnd : forall t1 t2,
    term (t1 ** t2)
    -> term t2

  | EInl : forall t1 t2,
    term t1
    -> term (t1 ++ t2)
  | EInr : forall t1 t2,
    term t2
    -> term (t1 ++ t2)
  | ECase : forall t1 t2 t,
    term (t1 ++ t2)
    -> (var t1 -> term t)
    -> (var t2 -> term t)
    -> term t

  | EO : term Nat
  | ES : term Nat -> term Nat
  | ENatCase : forall t,
    term Nat
    -> term t
    -> (var Nat -> term t)
    -> term t

  | ENil : forall t,
    term (List t)
  | ECons : forall t,
    term t
    -> term (List t)
    -> term (List t)
  | EFold : forall tls tst,
    term ((tls --> tst --> tst) --> tst --> List tls --> tst).
End vars.

Implicit Arguments EVar [var t].

Implicit Arguments ETrue [var].
Implicit Arguments EFalse [var].

Implicit Arguments EApp [var t1 t2].
Implicit Arguments EAbs [var t1 t2].

Implicit Arguments EUnit [var].

Implicit Arguments EPair [var t1 t2].
Implicit Arguments EFst [var t1 t2].
Implicit Arguments ESnd [var t1 t2].

Implicit Arguments EInl [var t1 t2].
Implicit Arguments EInr [var t1 t2].
Implicit Arguments ECase [var t1 t2 t].

Implicit Arguments EO [var].
Implicit Arguments ES [var].
Implicit Arguments ENatCase [var t].

Implicit Arguments ENil [var t].
Implicit Arguments ECons [var t].
Implicit Arguments EFold [var tst tls].

Notation "# v" := (EVar v) (at level 70) : source_scope.

Notation "'Tru'" := ETrue : source_scope.
Notation "'Fals'" := EFalse : source_scope.

Infix "@" := EApp (left associativity, at level 77) : source_scope.
Notation "\ x , e" := (EAbs (fun x => e)) (at level 78) : source_scope.

Notation "()" := EUnit : source_scope.

Notation "[ x1 , x2 ]" := (EPair x1 x2) (at level 73) : source_scope.
Notation "#1 x" := (EFst x) (at level 72) : source_scope.
Notation "#2 x" := (ESnd x) (at level 72) : source_scope.

Notation "'Inl' e" := (EInl e) (at level 72) : source_scope.
Notation "'Inr' e" := (EInr e) (at level 72) : source_scope.
Notation "'Case' e 'of' x ==> e1 ||| y ==> e2" := (ECase e (fun x => e1) (fun y => e2))
  (at level 77) : source_scope.

Notation "'^O'" := EO : source_scope.
Notation "'^S' e" := (ES e) (at level 72) : source_scope.
Notation "'NatCase' e 'of' e1 ||| y ==> e2" := (ENatCase e e1 (fun y => e2))
  (at level 77) : source_scope.

Notation "'Nil'" := ENil : source_scope.
Infix ":::" := ECons (right associativity, at level 60) : source_scope.
Notation "'Fold'" := EFold : source_scope.

Bind Scope source_scope with term.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Bool => bool
    | t1 --> t2 => typeDenote t1 -> typeDenote t2
    | Unit => unit
    | t1 ** t2 => typeDenote t1 * typeDenote t2
    | t1 ++ t2 => typeDenote t1 + typeDenote t2
    | Nat => nat
    | List t => list (typeDenote t)
  end%type.

Fixpoint termDenote t (e : term typeDenote t) {struct e} : typeDenote t :=
  match e in (term _ t) return (typeDenote t) with
    | EVar _ v => v

    | ETrue => true
    | EFalse => false

    | EApp _ _ e1 e2 => (termDenote e1) (termDenote e2)
    | EAbs _ _ e' => fun x => termDenote (e' x)

    | EUnit => tt

    | EPair _ _ e1 e2 => (termDenote e1, termDenote e2)
    | EFst _ _ e' => fst (termDenote e')
    | ESnd _ _ e' => snd (termDenote e')

    | EInl _ _ e' => inl _ (termDenote e')
    | EInr _ _ e' => inr _ (termDenote e')
    | ECase _ _ _ e' e1 e2 =>
      match termDenote e' with
        | inl x => termDenote (e1 x)
        | inr y => termDenote (e2 y)
      end

    | EO => O
    | ES e' => S (termDenote e')
    | ENatCase _ e' e1 e2 =>
      match termDenote e' with
        | O => termDenote e1
        | S n => termDenote (e2 n)
      end

    | ENil _ => nil
    | ECons _ e1 e2 => termDenote e1 :: termDenote e2
    | EFold _ _ => fun f s l => fold_left (fun st el => f el st) l s
  end.

Definition Term t := forall var, term var t.
Definition TermDenote t (E : Term t) := termDenote (E _).


(** * Term equivalence *)

Section term_equiv.
  Variables var1 var2 : type -> Type.

  Inductive term_equiv : ctxt var1 var2 -> forall t, term var1 t -> term var2 t -> Prop :=
  | EqEVar : forall G t (v1 : var1 t) v2,
    In (vars (v1, v2)) G
    -> term_equiv G (#v1) (#v2)

  | EqETrue : forall G,
    term_equiv G Tru Tru
  | EqEFalse : forall G,
    term_equiv G Fals Fals

  | EqEApp : forall G t1 t2 (f1 : term _ (t1 --> t2)) (x1 : term _ t1) f2 x2,
    term_equiv G f1 f2
    -> term_equiv G x1 x2
    -> term_equiv G (f1 @ x1) (f2 @ x2)
  | EqEAbs : forall G t1 t2 (f1 : var1 t1 -> term var1 t2) f2,
    (forall v1 v2, term_equiv (vars (v1, v2) :: G) (f1 v1) (f2 v2))
    -> term_equiv G (EAbs f1) (EAbs f2)

  | EqEUnit : forall G,
    term_equiv G () ()

  | EqEPair : forall G t1 t2 (x1 : term _ t1) (y1 : term _ t2) x2 y2,
    term_equiv G x1 x2
    -> term_equiv G y1 y2
    -> term_equiv G ([x1, y1]) ([x2, y2])
  | EqEFst : forall G t1 t2 (e1 : term _ (t1 ** t2)) e2,
    term_equiv G e1 e2
    -> term_equiv G (#1 e1) (#1 e2)
  | EqESnd : forall G t1 t2 (e1 : term _ (t1 ** t2)) e2,
    term_equiv G e1 e2
    -> term_equiv G (#2 e1) (#2 e2)

  | EqEInl : forall G t1 t2 (e1 : term _ t1) e2,
    term_equiv G e1 e2
    -> term_equiv G (EInl (t2 := t2) e1) (Inl e2)
  | EqEInr : forall G t1 t2 (e1 : term _ t2) e2,
    term_equiv G e1 e2
    -> term_equiv G (EInr (t1 := t1) e1) (Inr e2)
  | EqECase : forall G t1 t2 t (e1 : term _ (t1 ++ t2)) (e11 : _ -> term _ t) e21 e2 e12 e22,
    term_equiv G e1 e2
    -> (forall v1 v2, term_equiv (vars (v1, v2) :: G) (e11 v1) (e12 v2))
    -> (forall v1 v2, term_equiv (vars (v1, v2) :: G) (e21 v1) (e22 v2))
    -> term_equiv G (ECase e1 e11 e21) (ECase e2 e12 e22)

  | EqEO : forall G, term_equiv G (^O) (^O)
  | EqES : forall G e1 e2,
    term_equiv G e1 e2
    -> term_equiv G (^S e1) (^S e2)
  | EqENatCase : forall G t e1 (e11 : term _ t) e21 e2 e12 e22,
    term_equiv G e1 e2
    -> term_equiv G e11 e12
    -> (forall v1 v2, term_equiv (vars (v1, v2) :: G) (e21 v1) (e22 v2))
    -> term_equiv G (ENatCase e1 e11 e21) (ENatCase e2 e12 e22)

  | EqENil : forall G t, term_equiv G (t := List t) Nil Nil
  | EqECons : forall G t (h1 : term _ t) t1 h2 t2,
    term_equiv G h1 h2
    -> term_equiv G t1 t2
    -> term_equiv G (h1 ::: t1) (h2 ::: t2)
  | EqEFold : forall G tst tls,
    term_equiv G (EFold (tst := tst) (tls := tls)) Fold.
End term_equiv.

Axiom Term_equiv : forall t (E : Term t) var1 var2,
  term_equiv nil (E var1) (E var2).
