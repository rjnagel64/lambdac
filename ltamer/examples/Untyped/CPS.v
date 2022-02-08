(* Copyright (c) 2009, Adam Chlipala
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

Require Import Base.

Set Implicit Arguments.

Section vars.
  Variable var : Type.

  Inductive exp : Type :=
  | EHalt : var -> exp
  | Call : var -> var -> exp
  | Bind : primop -> (var -> exp) -> exp
  | ECase : var -> (var -> exp) -> (var -> exp) -> exp
  | EUncaught : var -> exp

  with primop : Type :=
  | Abs : (var -> var -> exp) -> primop

  | Unit : primop

  | Pair : var -> var -> primop
  | EFst : var -> primop
  | ESnd : var -> primop
      
  | EInl : var -> primop
  | EInr : var -> primop

  | New : var -> primop
  | Read : var -> primop
  | Write : var -> var -> primop

  | Const : base -> primop
  | Eq : var -> var -> primop.
End vars.

Implicit Arguments EHalt [var].
Implicit Arguments EUncaught [var].
Implicit Arguments Unit [var].
Implicit Arguments Const [var].

Notation "'Halt'" := EHalt : cps_scope.
Notation "'Uncaught'" := EUncaught : cps_scope.
Infix "@@@" := Call (no associativity, at level 80) : cps_scope.
Notation "x <- p ; e" := (Bind p (fun x => e)) (right associativity, at level 80) : cps_scope.
Notation "'Case' e 'Of' x => e1 | y => e2" := (ECase e (fun x => e1) (fun y => e2))
  (no associativity, at level 80) : cps_scope.

Open Local Scope cps_scope.

Notation "\ x , e" := (Abs (fun _ x => e)) (at level 81) : cps_scope.
Notation "\\ F , x , e" := (Abs (fun F x => e)) (at level 81) : cps_scope.

Notation "()" := Unit : cps_scope.

Notation "[< e1 , e2 >]" := (Pair e1 e2) (at level 0) : cps_scope.
Notation "'Fst' e" := (EFst e) (at level 72) : cps_scope.
Notation "'Snd' e" := (ESnd e) (at level 72) : cps_scope.

Notation "'Inl' e" := (EInl e) (at level 72) : cps_scope.
Notation "'Inr' e" := (EInr e) (at level 72) : cps_scope.

Notation "'Ref' e" := (New e) (no associativity, at level 71) : cps_scope.
Notation "! e" := (Read e) (no associativity, at level 71) : cps_scope.
Infix "::=" := Write (no associativity, at level 71) : cps_scope.

Notation "^^ e" := (Const e) (no associativity, at level 71) : cps_scope.
Infix "==" := Eq (no associativity, at level 71) : cps_scope.

Definition Exp := forall var, exp var.
Definition Primop := forall var, primop var.

Bind Scope cps_scope with exp primop.
Delimit Scope cps_scope with cps.

Inductive val : Set :=
| VCont : label -> val
| VUnit : val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VRef : label -> val
| VBase : base -> val.

Definition expV := exp val.
Definition primopV := primop val.

Definition closure := val -> val -> expV.
Definition closures := list closure.

Definition heap := list val.

Inductive evalP : closures -> heap -> primopV -> closures -> heap -> val -> Prop :=
| EvalAbs : forall s h e1,
  evalP s h (Abs e1) (e1 :: s) h (VCont (length s))

| EvalUnit : forall s h,
  evalP s h () s h VUnit

| EvalPair : forall s h v1 v2,
  evalP s h [< v1, v2 >] s h (VPair v1 v2)
| EvalFst : forall s h v1 v2,
  evalP s h (Fst (VPair v1 v2)) s h v1
| EvalSnd : forall s h v1 v2,
  evalP s h (Snd (VPair v1 v2)) s h v2

| EvalInl : forall s h v,
  evalP s h (Inl v) s h (VInl v)
| EvalInr : forall s h v,
  evalP s h (Inr v) s h (VInr v)

| EvalNew : forall s h v,
  evalP s h (Ref v) s (v :: h) (VRef (length h))
| EvalRead : forall s h r v,
  h # r = Some v
  -> evalP s h (!(VRef r)) s h v
| EvalWrite : forall s h r v,
  evalP s h (VRef r ::= v) s (h ## r <~ v) VUnit

| EvalConst : forall s h b,
  evalP s h (Const b) s h (VBase b)
| EvalEqT : forall s h b,
  evalP s h (VBase b == VBase b) s h (VInr VUnit)
| EvalEqF : forall s h b1 b2,
  b1 <> b2
  -> evalP s h (VBase b1 == VBase b2) s h (VInl VUnit).

Inductive result : Type :=
| Ans : val -> result
| Ex : val -> result.

Inductive eval : closures -> heap -> expV -> result -> Prop :=
| EvalHalt : forall s h v,
  eval s h (Halt v) (Ans v)
| EvalApp : forall s1 h1 l v1 f v2,
  s1 # l = Some f
  -> eval s1 h1 (f (VCont l) v1) v2
  -> eval s1 h1 (VCont l @@@ v1) v2

| EvalBind : forall s1 h1 p e s2 h2 v1 v2,
  evalP s1 h1 p s2 h2 v1
  -> eval s2 h2 (e v1) v2
  -> eval s1 h1 (Bind p e) v2
| EvalCaseL : forall s1 h1 v e1 e2 r,
  eval s1 h1 (e1 v) r
  -> eval s1 h1 (ECase (VInl v) e1 e2) r
| EvalCaseR : forall s1 h1 v e1 e2 r,
  eval s1 h1 (e2 v) r
  -> eval s1 h1 (ECase (VInr v) e1 e2) r

| EvalUncaught : forall s h v,
  eval s h (Uncaught v) (Ex v).

Theorem evalP_monotone : forall s1 h1 p s2 h2 v,
  evalP s1 h1 p s2 h2 v
  -> s1 ~> s2.
  induction 1; eauto.
Qed.

Hint Immediate evalP_monotone.

Definition Eval (s : closures) (h : heap) (E : Exp) (r : result) :=
  eval s h (E _) r.
Definition EvalP (s1 : closures) (h1 : heap) (P : Primop) (s2 : closures) (h2 : heap) (v : val) :=
  evalP s1 h1 (P _) s2 h2 v.

Ltac evalOne := (econstructor; [ solve [ eauto ] | concretize; simpl ])
  || (econstructor; []).

Hint Extern 1 (eval _ _ _ _) =>
  evalOne; repeat evalOne : cps_eval.


Section exp_equiv.
  Variables var1 var2 : Type.

  Inductive primop_equiv : list (var1 * var2) -> primop var1 -> primop var2 -> Prop :=
  | EqAbs : forall G f1 f2,
    (forall F1 F2 v1 v2, exp_equiv ((F1, F2) :: (v1, v2) :: G) (f1 F1 v1) (f2 F2 v2))
    -> primop_equiv G (Abs f1) (Abs f2)

  | EqUnit : forall G,
    primop_equiv G () ()

  | EqPair : forall G x y x' y',
    In (x, x') G
    -> In (y, y') G
    -> primop_equiv G [< x, y >] [< x', y' >]
  | EqFst : forall G v v',
    In (v, v') G
    -> primop_equiv G (Fst v) (Fst v')
  | EqSnd : forall G v v',
    In (v, v') G
    -> primop_equiv G (Snd v) (Snd v')

  | EqInl : forall G v v',
    In (v, v') G
    -> primop_equiv G (Inl v) (Inl v')
  | EqInr : forall G v v',
    In (v, v') G
    -> primop_equiv G (Inr v) (Inr v')

  | EqNew : forall G v1 v2,
    In (v1, v2) G
    -> primop_equiv G (Ref v1) (Ref v2)
  | EqRead : forall G v1 v2,
    In (v1, v2) G
    -> primop_equiv G (!v1) (!v2)
  | EqWrite : forall G v1 v2 v1' v2',
    In (v1, v2) G
    -> In (v1', v2') G
    -> primop_equiv G (v1 ::= v1') (v2 ::= v2')

  | EqConst : forall G b,
    primop_equiv G (^^b) (^^b)
  | EqEq : forall G v1 v2 v1' v2',
    In (v1, v2) G
    -> In (v1', v2') G
    -> primop_equiv G (v1 == v1') (v2 == v2')

  with exp_equiv : list (var1 * var2) -> exp var1 -> exp var2 -> Prop :=
  | EqHalt : forall G v v',
    In (v, v') G
    -> exp_equiv G (Halt v) (Halt v')
  | EqUncaught : forall G v v',
    In (v, v') G
    -> exp_equiv G (Uncaught v) (Uncaught v')

  | EqBind : forall G p1 p2 e1 e2,
    primop_equiv G p1 p2
    -> (forall v1 v2, exp_equiv ((v1, v2) :: G) (e1 v1) (e2 v2))
    -> exp_equiv G (Bind p1 e1) (Bind p2 e2)

  | EqApp : forall G f1 x1 f2 x2,
    In (f1, f2) G
    -> In (x1, x2) G
    -> exp_equiv G (f1 @@@ x1) (f2 @@@ x2)

  | EqCase : forall G v v' e1 e1' e2 e2',
    In (v, v') G
    -> (forall v1 v2, exp_equiv ((v1, v2) :: G) (e1 v1) (e1' v2))
    -> (forall v1 v2, exp_equiv ((v1, v2) :: G) (e2 v1) (e2' v2))
    -> exp_equiv G (ECase v e1 e2) (ECase v' e1' e2').
End exp_equiv.

Definition Exp_wf (E : Exp) := forall var1 var2,
  exp_equiv nil (E var1) (E var2).


Section exp_valid.
  Variable var : Type.

  Inductive primop_valid : list var -> primop var -> Prop :=
  | VldAbs : forall G f,
    (forall F v, exp_valid (F :: v :: G) (f F v))
    -> primop_valid G (Abs f)

  | VldUnit : forall G,
    primop_valid G ()

  | VldPair : forall G x y,
    In x G
    -> In y G
    -> primop_valid G [< x, y >]
  | VldFst : forall G v,
    In v G
    -> primop_valid G (Fst v)
  | VldSnd : forall G v,
    In v G
    -> primop_valid G (Snd v)

  | VldInl : forall G v,
    In v G
    -> primop_valid G (Inl v)
  | VldInr : forall G v,
    In v G
    -> primop_valid G (Inr v)

  | VldNew : forall G v,
    In v G
    -> primop_valid G (Ref v)
  | VldRead : forall G v,
    In v G
    -> primop_valid G (!v)
  | VldWrite : forall G v1 v2,
    In v1 G
    -> In v2 G
    -> primop_valid G (v1 ::= v2)

  | VldConst : forall G b,
    primop_valid G (^^b)
  | VldEq : forall G v1 v2,
    In v1 G
    -> In v2 G
    -> primop_valid G (v1 == v2)

  with exp_valid : list var -> exp var -> Prop :=
  | VldHalt : forall G v,
    In v G
    -> exp_valid G (Halt v)
  | VldUncaught : forall G v,
    In v G
    -> exp_valid G (Uncaught v)

  | VldBind : forall G p e,
    primop_valid G p
    -> (forall v, exp_valid (v :: G) (e v))
    -> exp_valid G (Bind p e)

  | VldApp : forall G f x,
    In f G
    -> In x G
    -> exp_valid G (f @@@ x)

  | VldCase : forall G v e1 e2,
    In v G
    -> (forall v, exp_valid (v :: G) (e1 v))
    -> (forall v, exp_valid (v :: G) (e2 v))
    -> exp_valid G (ECase v e1 e2).
End exp_valid.

Scheme exp_equiv_mut := Minimality for exp_equiv Sort Prop
with primop_equiv_mut := Minimality for primop_equiv Sort Prop.

Hint Constructors exp_valid primop_valid.

Lemma var_valid : forall var x x' G,
  In (x, x') G
  -> In x (map (fst (A:=var) (B:=var)) G).
  induction G; simpler.
Qed.

Hint Resolve var_valid.

Lemma Exp_valid' : forall var G (e1 e2 : exp var),
  exp_equiv G e1 e2
  -> exp_valid (map (@fst _ _) G) e1.
  intro; apply (exp_equiv_mut
    (fun G (e1 e2 : exp var) =>
      exp_valid (map (@fst _ _) G) e1)
    (fun G (p1 p2 : primop var) =>
      primop_valid (map (@fst _ _) G) p1)); simpler; eauto.
Qed.

Theorem Exp_valid : forall (E : Exp) var,
  Exp_wf E
  -> exp_valid nil (E var).
  intros; change (@nil var) with (map (@fst var var) nil);
    eapply Exp_valid'; auto.
Qed.
