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

Require Import LambdaTamer.
Require Import Util.

Set Implicit Arguments.


Inductive type : Type :=
| TUnit : type
| TArrow : type -> type -> type
| TProd : type -> type -> type
| TSum : type -> type -> type.

Notation "'Unit'" := TUnit : source_scope.
Infix "-->" := TArrow (right associativity, at level 61) : source_scope.
Infix "++" := TSum (right associativity, at level 60) : source_scope.
Infix "**" := TProd (right associativity, at level 59) : source_scope.

Bind Scope source_scope with type.
Delimit Scope source_scope with source.

Inductive pat : type -> list type -> Type :=
| SPVar : forall t,
  pat t (t :: nil)
| SPPair : forall t1 t2 ts1 ts2,
  pat t1 ts1
  -> pat t2 ts2
  -> pat (t1 ** t2) (ts1 ++ ts2)
| SPInl : forall t1 t2 ts,
  pat t1 ts
  -> pat (t1 ++ t2) ts
| SPInr : forall t1 t2 ts,
  pat t2 ts
  -> pat (t1 ++ t2) ts.

Implicit Arguments SPVar [t].
Implicit Arguments SPInl [t1 t2 ts].
Implicit Arguments SPInr [t1 t2 ts].

Notation "##" := SPVar (at level 70) : pat_scope.
Notation "[< p1 , p2 >]" := (SPPair p1 p2) (at level 72) : pat_scope.
Notation "'Inl' p" := (SPInl p) (at level 71) : pat_scope.
Notation "'Inr' p" := (SPInr p) (at level 71) : pat_scope.

Bind Scope pat_scope with pat.
Delimit Scope pat_scope with pat.

Section vars.
  Variable var : type -> Type.

  Inductive term : type -> Type :=
  | SVar : forall t,
    var t
    -> term t

  | SUnit : term TUnit

  | SApp : forall t1 t2,
    term (t1 --> t2)
    -> term t1
    -> term t2
  | SAbs : forall t1 t2,
    (var t1 -> term t2)
    -> term (t1 --> t2)

  | SPair : forall t1 t2,
    term t1
    -> term t2
    -> term (t1 ** t2)

  | SInl : forall t1 t2,
    term t1
    -> term (t1 ++ t2)
  | SInr : forall t1 t2,
    term t2
    -> term (t1 ++ t2)

  | SCase : forall t1 t2,
    term t1
    -> list { ts : list type & pat t1 ts * (tuple var ts -> term t2)}%type
    -> term t2
    -> term t2.
End vars.

Implicit Arguments SVar [var t].
Implicit Arguments SUnit [var].
Implicit Arguments SApp [var t1 t2].
Implicit Arguments SAbs [var t1 t2].
Implicit Arguments SPair [var t1 t2].
Implicit Arguments SInl [var t1 t2].
Implicit Arguments SInr [var t1 t2].
Implicit Arguments SCase [var t1 t2].

Notation "# v" := (SVar v) (at level 70) : source_scope.

Notation "()" := SUnit.

Infix "@" := SApp (left associativity, at level 77) : source_scope.
Notation "\ x , e" := (SAbs (fun x => e)) (at level 78) : source_scope.

Notation "[ x , y ]" := (SPair x y) (at level 72) : source_scope.

Notation "'Inl' e" := (SInl e) (at level 71) : source_scope.
Notation "'Inr' e" := (SInr e) (at level 71) : source_scope.

Notation "'Case' e 'of' ps 'default' e'" := (SCase e ps e')
  (no associativity, at level 77, ps at next level) : source_scope.
Notation "p 'named' x ==> e" := (existT (fun ts => (pat _ ts * (tuple _ ts -> term _ _))%type) _ (p, fun x => e))
  (no associativity, at level 40).

Bind Scope source_scope with term.

Open Local Scope source_scope.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Unit => unit
    | t1 --> t2 => typeDenote t1 -> typeDenote t2
    | t1 ** t2 => (typeDenote t1 * typeDenote t2)%type
    | t1 ++ t2 => (typeDenote t1 + typeDenote t2)%type
  end.

Fixpoint patDenote t ts (p : pat t ts) {struct p} : typeDenote t -> option (tuple typeDenote ts) :=
  match p in (pat t ts) return (typeDenote t -> option (tuple typeDenote ts)) with
    | SPVar _ => fun v => Some (v, tt)
    | SPPair _ _ _ _ p1 p2 => fun v =>
      match patDenote p1 (fst v), patDenote p2 (snd v) with
        | Some tup1, Some tup2 => Some (concat tup1 tup2)
        | _, _ => None
      end
    | SPInl _ _ _ p' => fun v =>
      match v with
        | inl v' => patDenote p' v'
        | _ => None
      end
    | SPInr _ _ _ p' => fun v =>
      match v with
        | inr v' => patDenote p' v'
        | _ => None
      end
  end.

Fixpoint termDenote t (e : term typeDenote t) {struct e} : typeDenote t :=
  match e in (term _ t) return (typeDenote t) with
    | SVar _ v => v

    | SUnit => tt

    | SApp _ _ e1 e2 => (termDenote e1) (termDenote e2)
    | SAbs _ _ e' => fun x => termDenote (e' x)

    | SPair _ _ e1 e2 => (termDenote e1, termDenote e2)

    | SInl _ _ e' => inl _ (termDenote e')
    | SInr _ _ e' => inr _ (termDenote e')

    | SCase _ _ e ms def =>
      (fix matchesDenote (ms : list { ts : list type & pat _ ts * (tuple typeDenote ts -> term typeDenote _) }%type)
        : typeDenote _ :=
        match ms with
          | nil => termDenote def
          | existT ts (p, b) :: ms' =>
            match patDenote p (termDenote e) with
              | None => matchesDenote ms'
              | Some vs => termDenote (b vs)
            end
        end) ms
  end.

Definition Term t := forall var, term var t.
Definition TermDenote t (E : Term t) := termDenote (E _).
