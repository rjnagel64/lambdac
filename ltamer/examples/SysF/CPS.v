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

Require Import Source.

Set Implicit Arguments.


Section vars.
  Variable tvar : Type.

  Inductive ptype : Type :=
  | PBool : ptype
  | PTVar : tvar -> ptype
  | PCont : ptype -> ptype
  | PProd : ptype -> ptype -> ptype
  | PAll : (tvar -> ptype) -> ptype.

  Notation "^ v" := (PTVar v) (at level 60).
  Notation "t --->" := (PCont t) (at level 61).
  Infix "**" := PProd (right associativity, at level 60).

  Inductive PSubst : (tvar -> ptype) -> ptype -> ptype -> Prop :=
  | PSBool : forall t, PSubst (fun _ => PBool) t PBool
  | PSVarEq : forall t, PSubst PTVar t t
  | PSVarNeq : forall (v : tvar) t, PSubst (fun _ => ^v) t (^v)
  | PSArrow : forall t1 t1' t,
    PSubst t1 t t1'
    -> PSubst (fun v => t1 v --->) t (t1' --->)
  | PSProd : forall t1 t2 t1' t2' t,
    PSubst t1 t t1'
    -> PSubst t2 t t2'
    -> PSubst (fun v => t1 v ** t2 v) t (t1' ** t2')
  | PSAll : forall t1 t1' t,
    (forall v', PSubst (fun v => t1 v v') t (t1' v'))
    -> PSubst (fun v => PAll (t1 v)) t (PAll t1').


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

  with pprimop : ptype -> Type :=
  | PVar : forall t,
    var t
    -> pprimop t

  | PTrue : pprimop PBool
  | PFalse : pprimop PBool
    
  | PAbs : forall t,
    (var t -> pterm)
    -> pprimop (t --->)

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

  | PTApp : forall t1,
    var (PAll t1)
    -> forall t2 t1',
      PSubst t1 t2 t1'
      -> pprimop t1'
  | PTAbs : forall t1,
    (forall v, pprimop (t1 v))
    -> pprimop (PAll t1).
End vars.

Hint Constructors PSubst.

Implicit Arguments PBool [tvar].

Implicit Arguments PHalt [tvar var result].
Implicit Arguments PApp [tvar var result t].
Implicit Arguments PBind [tvar var result t].

Implicit Arguments PVar [tvar var result t].
Implicit Arguments PTrue [tvar var result].
Implicit Arguments PFalse [tvar var result].
Implicit Arguments PAbs [tvar var result t].
Implicit Arguments PPair [tvar var result t1 t2].
Implicit Arguments PFst [tvar var result t1 t2].
Implicit Arguments PSnd [tvar var result t1 t2].
Implicit Arguments PTApp [tvar var result t1 t1'].
Implicit Arguments PTAbs [tvar var result t1].

Notation "'Bool'" := PBool : cps_scope.
Notation "^ v" := (PTVar v) (at level 60) : cps_scope.
Notation "t --->" := (PCont t) (at level 61) : cps_scope.
Infix "**" := PProd (right associativity, at level 60) : cps_scope.
Notation "'All' x , t" := (PAll (fun x => t)) (no associativity, at level 62) : cps_scope.
Notation "'All' ? , t" := (PAll (fun _ => t)) (no associativity, at level 62) : cps_scope.

Bind Scope cps_scope with ptype.
Delimit Scope cps_scope with cps.

Notation "'Halt' x" := (PHalt x) (no associativity, at level 75) : cps_scope.
Infix "@@@" := PApp (no associativity, at level 75) : cps_scope.
Notation "x <- p ; e" := (PBind p (fun x => e))
  (right associativity, at level 76, p at next level) : cps_scope.
Notation "? <- p ; e" := (PBind p (fun _ => e))
  (right associativity, at level 76, p at next level) : cps_scope.

Notation "# v" := (PVar v) (at level 62) : cps_scope.
Notation "'Tru'" := PTrue : cps_scope.
Notation "'Fals'" := PFalse : cps_scope.

Notation "\ x , e" := (PAbs (fun x => e)) (at level 78) : cps_scope.
Notation "\ ! , e" := (PAbs (fun _ => e)) (at level 78) : cps_scope.

Notation "[ x1 , x2 ]" := (PPair x1 x2) (at level 73) : cps_scope.
Notation "#1 x" := (PFst x) (left associativity, at level 72) : cps_scope.
Notation "#2 x" := (PSnd x) (left associativity, at level 72) : cps_scope.

Notation "e @@ t" := (PTApp e t _) (left associativity, at level 77) : cps_scope.
Notation "\\ T , e" := (PTAbs (fun T => e)) (at level 78) : cps_scope.
Notation "\\ ! , e" := (PTAbs (fun _ => e)) (at level 78) : cps_scope.

Bind Scope cps_scope with pterm pprimop.

Open Local Scope cps_scope.

Fixpoint ptypeDenote (t : ptype Set) {struct t} : Set :=
  match t with
    | PBool => bool
    | PTVar v => v
    | t1 ---> => ptypeDenote t1 -> bool
    | t1 ** t2 => ptypeDenote t1 * ptypeDenote t2
    | PAll t' => forall T, ptypeDenote (t' T)
  end%type.

Theorem PSubst_ptypeDenote : forall t1 t2 t1',
  PSubst t1 t2 t1'
  -> ptypeDenote (t1 (ptypeDenote t2)) = ptypeDenote t1'.
  induction 1; equation; apply ext_eq_forallS; auto.
Defined.

Fixpoint ptermDenote result (e : pterm ptypeDenote result) (k : ptypeDenote result -> bool)
  {struct e} : bool :=
  match e with
    | PHalt v => k v
    | PApp _ f x => f x
    | PBind _ p x => ptermDenote (x (pprimopDenote p k)) k
  end

with pprimopDenote result t (p : pprimop ptypeDenote result t) (k : ptypeDenote result -> bool)
  {struct p} : ptypeDenote t :=
  match p in (pprimop _ _ t) return (ptypeDenote t) with
    | PVar _ v => v

    | PTrue => true
    | PFalse => false

    | PAbs _ e => fun x => ptermDenote (e x) k

    | PPair _ _ v1 v2 => (v1, v2)
    | PFst _ _ v => fst v
    | PSnd _ _ v => snd v

    | PTApp _ v t _ Hsubst => v (ptypeDenote t) :? PSubst_ptypeDenote Hsubst
    | PTAbs _ p' => fun T => pprimopDenote (p' T) k
  end.

Definition Ptyp := forall tvar, ptype tvar.
Definition Pterm t := forall tvar (var : ptype tvar -> Type), pterm var (t tvar).

Definition PtypDenote (T : Ptyp) : Set := ptypeDenote (T _).
Definition PtermDenote T (E : Pterm T) (K : PtypDenote T -> bool) : bool
  := ptermDenote (E _ _) K.
