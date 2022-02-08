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

Require Import Result.

Set Implicit Arguments.

Section vars.
  Variable var : Type.

  Inductive exp : Type :=
  | EHalt : exp
  | Call : var -> var -> exp
  | Bind : primop -> (var -> exp) -> exp
  | ECase : var -> (var -> exp) -> (var -> exp) -> exp
  | EUncaught : exp

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
  | Write : var -> var -> primop.
End vars.

Implicit Arguments EHalt [var].
Implicit Arguments EUncaught [var].
Implicit Arguments Unit [var].


Notation "'Halt'" := EHalt : cps_scope.
Notation "'Uncaught'" := EUncaught : cps_scope.
Infix "@@@" := Call (no associativity, at level 80) : cps_scope.
Notation "x <- p ; e" := (Bind p (fun x => e)) (right associativity, at level 80) : cps_scope.
Notation "'Case' e 'Of' x => e1 | y => e2" := (ECase e (fun x => e1) (fun y => e2))
  (no associativity, at level 81) : cps_scope.

Open Local Scope cps_scope.

Notation "\ f , x , e" := (Abs (fun f x => e)) (at level 82) : cps_scope.
Notation "\_ , x , e" := (Abs (fun _ x => e)) (at level 82) : cps_scope.

Notation "()" := Unit : cps_scope.

Notation "[< e1 , e2 >]" := (Pair e1 e2) (at level 0) : cps_scope.
Notation "'Fst' e" := (EFst e) (at level 72) : cps_scope.
Notation "'Snd' e" := (ESnd e) (at level 72) : cps_scope.

Notation "'Inl' e" := (EInl e) (at level 72) : cps_scope.
Notation "'Inr' e" := (EInr e) (at level 72) : cps_scope.

Notation "'Ref' e" := (New e) (no associativity, at level 71) : cps_scope.
Notation "! e" := (Read e) (no associativity, at level 71) : cps_scope.
Infix "::=" := Write (no associativity, at level 71) : cps_scope.

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
| VRef : label -> val.

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
  evalP s h (VRef r ::= v) s (h ## r <~ v) VUnit.

Hint Constructors evalP.

Inductive eval : closures -> heap -> expV -> result -> Prop :=
| EvalHalt : forall s h,
  eval s h Halt Ans
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

| EvalUncaught : forall s h,
  eval s h Uncaught Ex.

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
