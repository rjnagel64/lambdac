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
| TArrow : type -> type -> type.

Notation "'Bool'" := TBool : source_scope.
Infix "-->" := TArrow (right associativity, at level 60) : source_scope.

Bind Scope source_scope with type.
Delimit Scope source_scope with source.

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
    -> term (t1 --> t2).
End vars.

Implicit Arguments EVar [var t].
Implicit Arguments ETrue [var].
Implicit Arguments EFalse [var].
Implicit Arguments EApp [var t1 t2].
Implicit Arguments EAbs [var t1 t2].

Notation "# v" := (EVar v) (at level 70) : source_scope.

Notation "'Tru'" := ETrue : source_scope.
Notation "'Fals'" := EFalse : source_scope.

Infix "@" := EApp (left associativity, at level 77) : source_scope.
Notation "\ x , e" := (EAbs (fun x => e)) (at level 78) : source_scope.
Notation "\ ! , e" := (EAbs (fun _ => e)) (at level 78) : source_scope.

Bind Scope source_scope with term.

Open Local Scope source_scope.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Bool => bool
    | t1 --> t2 => typeDenote t1 -> typeDenote t2
  end.

Fixpoint termDenote t (e : term typeDenote t) {struct e} : typeDenote t :=
  match e in (term _ t) return (typeDenote t) with
    | EVar _ v => v

    | ETrue => true
    | EFalse => false

    | EApp _ _ e1 e2 => (termDenote e1) (termDenote e2)
    | EAbs _ _ e' => fun x => termDenote (e' x)
  end.

Definition Term t := forall var, term var t.
Definition TermDenote t (e : Term t) := termDenote (e _).


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
    -> term_equiv G (EAbs f1) (EAbs f2).
End term_equiv.

Axiom Term_equiv : forall t (E : Term t) var1 var2,
  term_equiv nil (E var1) (E var2).
