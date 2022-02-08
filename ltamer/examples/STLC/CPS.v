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
| PProd : ptype -> ptype -> ptype.

Notation "'Bool'" := PBool : cps_scope.
Notation "t --->" := (PCont t) (at level 61) : cps_scope.
Notation "'Unit'" := PUnit : cps_scope.
Infix "**" := PProd (right associativity, at level 60) : cps_scope.

Bind Scope cps_scope with ptype.
Delimit Scope cps_scope with cps.

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

  with pprimop : ptype -> Type :=
  | PVar : forall t,
    var t
    -> pprimop t
    
  | PTrue : pprimop Bool
  | PFalse : pprimop Bool
    
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
    -> pprimop t2.
End vars.

Implicit Arguments PHalt [var result].
Implicit Arguments PApp [var result t].
Implicit Arguments PBind [var result t].

Implicit Arguments PVar [var result t].
Implicit Arguments PTrue [var result].
Implicit Arguments PFalse [var result].
Implicit Arguments PAbs [var result t].
Implicit Arguments PPair [var result t1 t2].
Implicit Arguments PFst [var result t1 t2].
Implicit Arguments PSnd [var result t1 t2].

Notation "'Halt' x" := (PHalt x) (no associativity, at level 75) : cps_scope.
Infix "@@" := PApp (no associativity, at level 75) : cps_scope.
Notation "x <- p ; e" := (PBind p (fun x => e))
  (right associativity, at level 76, p at next level) : cps_scope.
Notation "! <- p ; e" := (PBind p (fun _ => e))
  (right associativity, at level 76, p at next level) : cps_scope.

Notation "# v" := (PVar v) (at level 70) : cps_scope.

Notation "'Tru'" := PTrue : cps_scope.
Notation "'Fals'" := PFalse : cps_scope.

Notation "\ x , e" := (PAbs (fun x => e)) (at level 78) : cps_scope.
Notation "\ ! , e" := (PAbs (fun _ => e)) (at level 78) : cps_scope.

Notation "[ x1 , x2 ]" := (PPair x1 x2) (at level 73) : cps_scope.
Notation "#1 x" := (PFst x) (at level 72) : cps_scope.
Notation "#2 x" := (PSnd x) (at level 72) : cps_scope.

Bind Scope cps_scope with pterm pprimop.

Open Local Scope cps_scope.

Fixpoint ptypeDenote (t : ptype) : Set :=
  match t with
    | Bool => bool
    | t' ---> => ptypeDenote t' -> bool
    | Unit => unit
    | t1 ** t2 => (ptypeDenote t1 * ptypeDenote t2)%type
  end.

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
  end.

Definition Pterm result := forall var, pterm var result.
Definition Pprimop result t := forall var, pprimop var result t.
Definition PtermDenote result (e : Pterm result) := ptermDenote (e _).
Definition PprimopDenote result t (p : Pprimop result t) := pprimopDenote (p _).


(** * Term equivalence *)

Section pterm_equiv.
  Variable result : ptype.
  Variables var1 var2 : ptype -> Type.

  Inductive pterm_equiv : ctxt var1 var2
    -> pterm var1 result -> pterm var2 result -> Prop :=
  | EqPHalt : forall G v1 v2,
    In (vars (v1, v2)) G
    -> pterm_equiv G (Halt v1) (Halt v2)
  | EqPApp : forall G t (f1 : var1 (t --->)) f2 x1 x2,
    In (vars (f1, f2)) G
    -> In (vars (x1, x2)) G
    -> pterm_equiv G (f1 @@ x1) (f2 @@ x2)
  | EqPBind : forall G t (p1 : pprimop var1 result t) p2 e1 e2,
    pprimop_equiv G p1 p2
    -> (forall v1 v2, pterm_equiv (vars (v1, v2) :: G) (e1 v1) (e2 v2))
    -> pterm_equiv G (PBind p1 e1) (PBind p2 e2)

  with pprimop_equiv : ctxt var1 var2
    -> forall t, pprimop var1 result t -> pprimop var2 result t -> Prop :=
  | EqPVar : forall G t (v1 : var1 t) v2,
    In (vars (v1, v2)) G
    -> pprimop_equiv G (#v1) (#v2)

  | EqPTrue : forall G,
    pprimop_equiv G Tru Tru
  | EqPFalse : forall G,
    pprimop_equiv G Fals Fals

  | EqPPair : forall G t1 t2 (x1 : var1 t1) x2 (y1 : var1 t2) y2,
    In (vars (x1, x2)) G
    -> In (vars (y1, y2)) G
    -> pprimop_equiv G ([x1, y1]) ([x2, y2])
  | EqPFst : forall G t1 t2 (x1 : var1 (t1 ** t2)) x2,
    In (vars (x1, x2)) G
    -> pprimop_equiv G (#1 x1) (#1 x2)
  | EqPSnd : forall G t1 t2 (x1 : var1 (t1 ** t2)) x2,
    In (vars (x1, x2)) G
    -> pprimop_equiv G (#2 x1) (#2 x2)

  | EqPAbs : forall G t (f1 : var1 t -> pterm var1 result) f2,
    (forall v1 v2, pterm_equiv (vars (v1, v2) :: G) (f1 v1) (f2 v2))
    -> pprimop_equiv G (PAbs f1) (PAbs f2).
End pterm_equiv.

Axiom Pterm_equiv : forall result (E : Pterm result) var1 var2,
  pterm_equiv nil (E var1) (E var2).
