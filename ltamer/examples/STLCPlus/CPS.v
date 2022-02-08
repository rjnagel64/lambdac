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


Inductive ptype : Type :=
| PBool : ptype
| PCont : ptype -> ptype
| PUnit : ptype
| PProd : ptype -> ptype -> ptype
| PSum : ptype -> ptype -> ptype
| PNat : ptype
| PList : ptype -> ptype.

Notation "'Bool'" := PBool : cps_scope.
Notation "t --->" := (PCont t) (at level 61) : cps_scope.
Notation "'Unit'" := PUnit : cps_scope.
Infix "**" := PProd (left associativity, at level 59) : cps_scope.
Infix "++" := PSum (right associativity, at level 60) : cps_scope.
Notation "'Nat'" := PNat : cps_scope.
Notation "'List' t" := (PList t) (at level 58) : cps_scope.

Bind Scope cps_scope with ptype.
Delimit Scope cps_scope with cps.

Open Local Scope cps_scope.

Section vars.
  Variable var : ptype -> Type.

  Variable result : ptype.

  Inductive pterm : Type :=
  | PHalt :
    var result
    -> pterm
  | PApp : forall t,
    var (t --->)
    -> var t
    -> pterm
  | PBind : forall t,
    pprimop t
    -> (var t -> pterm)
    -> pterm
  | PCase : forall t1 t2,
    var (t1 ++ t2)
    -> (var t1 -> pterm)
    -> (var t2 -> pterm)
    -> pterm
  | PNatCase :
    var Nat
    -> pterm
    -> (var Nat -> pterm)
    -> pterm

  with pprimop : ptype -> Type :=
  | PVar : forall t,
    var t
    -> pprimop t
    
  | PTrue : pprimop Bool
  | PFalse : pprimop Bool
    
  | PAbs : forall t,
    (var t -> pterm)
    -> pprimop (t --->)

  | PUnitIntro : pprimop Unit

  | PPair : forall t1 t2,
    var t1
    -> var t2
    -> pprimop (t1 ** t2)
  | PFst : forall t1 t2,
    var (t1 ** t2)
    -> pprimop t1
  | PSnd : forall t1 t2,
    var (t1 ** t2)
    -> pprimop t2

  | PInl : forall t1 t2,
    var t1
    -> pprimop (t1 ++ t2)
  | PInr : forall t1 t2,
    var t2
    -> pprimop (t1 ++ t2)

  | PO : pprimop Nat
  | PS : var Nat -> pprimop Nat

  | PNil : forall t,
    pprimop (List t)
  | PCons : forall t,
    var t
    -> var (List t)
    -> pprimop (List t)

  | PFold : forall tst tls,
    pprimop ((tls ** tst ** (tst --->) --->) ** tst ** List tls ** (tst --->) --->).
End vars.

Implicit Arguments PHalt [var result].
Implicit Arguments PApp [var result t].
Implicit Arguments PBind [var result t].
Implicit Arguments PCase [var result t1 t2].
Implicit Arguments PNatCase [var result].

Implicit Arguments PVar [var result t].
Implicit Arguments PTrue [var result].
Implicit Arguments PFalse [var result].
Implicit Arguments PAbs [var result t].
Implicit Arguments PUnitIntro [var result].
Implicit Arguments PPair [var result t1 t2].
Implicit Arguments PFst [var result t1 t2].
Implicit Arguments PSnd [var result t1 t2].
Implicit Arguments PInl [var result t1 t2].
Implicit Arguments PInr [var result t1 t2].
Implicit Arguments PO [var result].
Implicit Arguments PS [var result].
Implicit Arguments PNil [var result t].
Implicit Arguments PCons [var result t].
Implicit Arguments PFold [var result tst tls].

Notation "'Halt' x" := (PHalt x) (no associativity, at level 75) : cps_scope.
Infix "@@" := PApp (no associativity, at level 75) : cps_scope.
Notation "x <- p ; e" := (PBind p (fun x => e))
  (right associativity, at level 76, p at next level) : cps_scope.
Notation "'Case' e 'of' x ==> e1 ||| y ==> e2" := (PCase e (fun x => e1) (fun y => e2))
  (at level 77) : cps_scope.
Notation "'NatCase' e 'of' e1 ||| y ==> e2" := (PNatCase e e1 (fun y => e2))
  (at level 77) : cps_scope.

Notation "# v" := (PVar v) (at level 70) : cps_scope.

Notation "'Tru'" := PTrue : cps_scope.
Notation "'Fals'" := PFalse : cps_scope.

Notation "\ x , e" := (PAbs (fun x => e)) (at level 78) : cps_scope.

Notation "()" := PUnitIntro : cps_scope.

Notation "[ x1 , x2 ]" := (PPair x1 x2) (at level 73) : cps_scope.
Notation "#1 x" := (PFst x) (at level 72) : cps_scope.
Notation "#2 x" := (PSnd x) (at level 72) : cps_scope.

Notation "'Inl' x" := (PInl x) (at level 72) : cps_scope.
Notation "'Inr' x" := (PInr x) (at level 72) : cps_scope.

Notation "'^O'" := PO : cps_scope.
Notation "'^S' x" := (PS x) (at level 72) : cps_scope.
Notation "'Nil'" := PNil : cps_scope.
Infix ":::" := PCons (right associativity, at level 60) : cps_scope.
Notation "'Fold'" := PFold : cps_scope.

Bind Scope cps_scope with pterm pprimop.

Open Local Scope cps_scope.

Fixpoint ptypeDenote (t : ptype) : Set :=
  match t with
    | Bool => bool
    | t' ---> => ptypeDenote t' -> bool
    | Unit => unit
    | t1 ** t2 => (ptypeDenote t1 * ptypeDenote t2)%type
    | t1 ++ t2 => (ptypeDenote t1 + ptypeDenote t2)%type
    | Nat => nat
    | List t => list (ptypeDenote t)
  end.

Section kfold_left.
  Variables Tst Tls : Set.
  Variable f : Tls * Tst * (Tst -> bool) -> bool.

  Fixpoint kfold_left (s : Tst) (ls : list Tls) (k : Tst -> bool) : bool :=
    match ls with
      | nil => k s
      | h :: t => f (h, s, fun s' => kfold_left s' t k)
    end.
End kfold_left.

Fixpoint ptermDenote result (e : pterm ptypeDenote result) (k : ptypeDenote result -> bool)
  {struct e} : bool :=
  match e with
    | PHalt v => k v
    | PApp _ f x => f x
    | PBind _ p x => ptermDenote (x (pprimopDenote p k)) k
    | PCase _ _ x e1 e2 =>
      match x with
        | inl y1 => ptermDenote (e1 y1) k
        | inr y2 => ptermDenote (e2 y2) k
      end
    | PNatCase x e1 e2 =>
      match x with
        | O => ptermDenote e1 k
        | S n => ptermDenote (e2 n) k
      end
  end

with pprimopDenote result t (p : pprimop ptypeDenote result t) (k : ptypeDenote result -> bool)
  {struct p} : ptypeDenote t :=
  match p in (pprimop _ _ t) return (ptypeDenote t) with
    | PVar _ v => v

    | PTrue => true
    | PFalse => false

    | PAbs _ e => fun x => ptermDenote (e x) k

    | PUnitIntro => tt

    | PPair _ _ v1 v2 => (v1, v2)
    | PFst _ _ v => fst v
    | PSnd _ _ v => snd v

    | PInl _ _ v => inl _ v
    | PInr _ _ v => inr _ v

    | PO => 0
    | PS x => S x

    | PNil _ => nil
    | PCons _ h t => h :: t
    | PFold _ _ => fun arg =>
      match arg with
        (f, s, l, k) => kfold_left f s l k
      end
  end.

Definition Pterm result := forall var, pterm var result.
Definition Pprimop result t := forall var, pprimop var result t.
Definition PtermDenote result (e : Pterm result) := ptermDenote (e _).
Definition PprimopDenote result t (p : Pprimop result t) := pprimopDenote (p _).
