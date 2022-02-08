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
  | Var : var -> exp

  | App : exp -> exp -> exp
  | Abs : (var -> var -> exp) -> exp

  | ELet : exp -> (var -> exp) -> exp

  | Unit : exp
  | Pair : exp -> exp -> exp
  | EFst : exp -> exp
  | ESnd : exp -> exp
      
  | EInl : exp -> exp
  | EInr : exp -> exp
  | ECase : exp -> (var -> exp) -> (var -> exp) -> exp

  | New : exp -> exp
  | Read : exp -> exp
  | Write : exp -> exp -> exp

  | EThrow : exp -> exp
  | ECatch : exp -> (var -> exp) -> exp

  | Const : base -> exp
  | Eq : exp -> exp -> exp.
End vars.

Implicit Arguments Unit [var].
Implicit Arguments Const [var].

Notation "# v" := (Var v) (at level 70) : core_scope.

Open Local Scope core_scope.

Infix "@" := App (left associativity, at level 77) : core_scope.
Notation "\ x , e" := (Abs (fun _ x => e)) (at level 81) : core_scope.
Notation "\\ F , x , e" := (Abs (fun F x => e)) (at level 81) : core_scope.

Notation "'Let' x := e1 'in' e2" := (ELet e1 (fun x => e2)) (at level 81) : core_scope.

Notation "()" := Unit : core_scope.

Notation "[< e1 , e2 >]" := (Pair e1 e2) (at level 0) : core_scope.
Notation "'Fst' e" := (EFst e) (at level 72) : core_scope.
Notation "'Snd' e" := (ESnd e) (at level 72) : core_scope.

Notation "'Inl' e" := (EInl e) (at level 72) : core_scope.
Notation "'Inr' e" := (EInr e) (at level 72) : core_scope.
Notation "'Case' e 'Of' x => e1 | y => e2" := (ECase e (fun x => e1) (fun y => e2))
  (no associativity, at level 80) : core_scope.

Notation "'Ref' e" := (New e) (no associativity, at level 71) : core_scope.
Notation "! e" := (Read e) (no associativity, at level 71) : core_scope.
Infix "::=" := Write (no associativity, at level 71) : core_scope.

Notation "'Throw' e" := (EThrow e) (no associativity, at level 71) : core_scope.
Notation "e1 'Catch' x => e2" := (ECatch e1 (fun x => e2)) (no associativity, at level 80) : core_scope.

Notation "^^ e" := (Const e) (no associativity, at level 71) : core_scope.
Infix "==" := Eq (no associativity, at level 71) : core_scope.

Definition Exp := forall var, exp var.

Bind Scope core_scope with exp.

Inductive val : Set :=
| VFunc : label -> val
| VUnit : val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VRef : label -> val
| VBase : base -> val.

Definition expV := exp val.

Definition closure := val -> val -> expV.
Definition closures := list closure.

Definition heap := list val.

Inductive result : Type :=
| Ans : val -> result
| Ex : val -> result.

Inductive eval : closures -> heap -> expV -> closures -> heap -> result -> Prop :=
| EvalVar : forall s h v, eval s h (Var v) s h (Ans v)

| EvalApp : forall e1 e2 s1 h1 s2 h2 l f s3 h3 v1 s4 h4 v2,
  eval s1 h1 e1 s2 h2 (Ans (VFunc l))
  -> s2 # l = Some f
  -> eval s2 h2 e2 s3 h3 (Ans v1)
  -> eval s3 h3 (f (VFunc l) v1) s4 h4 v2
  -> eval s1 h1 (e1 @ e2) s4 h4 v2
| EvalAppEx1 : forall e1 e2 s1 h1 s2 h2 v,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> eval s1 h1 (e1 @ e2) s2 h2 (Ex v)
| EvalAppEx2 : forall e1 e2 s1 h1 s2 h2 l s3 h3 v,
  eval s1 h1 e1 s2 h2 (Ans (VFunc l))
  -> eval s2 h2 e2 s3 h3 (Ex v)
  -> eval s1 h1 (e1 @ e2) s3 h3 (Ex v)

| EvalAbs : forall s h e1,
  eval s h (Abs e1) (e1 :: s) h (Ans (VFunc (length s)))

| EvalLet : forall s1 h1 e1 s2 h2 v s3 h3 e2 r,
  eval s1 h1 e1 s2 h2 (Ans v)
  -> eval s2 h2 (e2 v) s3 h3 r
  -> eval s1 h1 (ELet e1 e2) s3 h3 r
| EvalLetEx : forall s1 h1 e1 s2 h2 v e2,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> eval s1 h1 (ELet e1 e2) s2 h2 (Ex v)

| EvalPair : forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
  eval s1 h1 e1 s2 h2 (Ans v1)
  -> eval s2 h2 e2 s3 h3 (Ans v2)
  -> eval s1 h1 [<e1, e2>] s3 h3 (Ans (VPair v1 v2))
| EvalPairEx1 : forall s1 h1 e1 s2 h2 v e2,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> eval s1 h1 [<e1, e2>] s2 h2 (Ex v)
| EvalPairEx2 : forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
  eval s1 h1 e1 s2 h2 (Ans v1)
  -> eval s2 h2 e2 s3 h3 (Ex v2)
  -> eval s1 h1 [<e1, e2>] s3 h3 (Ex v2)

| EvalUnit : forall s h,
  eval s h () s h (Ans VUnit)

| EvalFst : forall s1 h1 e s2 h2 v1 v2,
  eval s1 h1 e s2 h2 (Ans (VPair v1 v2))
  -> eval s1 h1 (Fst e) s2 h2 (Ans v1)
| EvalFstEx : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ex v)
  -> eval s1 h1 (Fst e) s2 h2 (Ex v)
| EvalSnd : forall s1 h1 e s2 h2 v1 v2,
  eval s1 h1 e s2 h2 (Ans (VPair v1 v2))
  -> eval s1 h1 (Snd e) s2 h2 (Ans v2)
| EvalSndEx : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ex v)
  -> eval s1 h1 (Snd e) s2 h2 (Ex v)

| EvalInl : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ans v)
  -> eval s1 h1 (Inl e) s2 h2 (Ans (VInl v))
| EvalInlEx : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ex v)
  -> eval s1 h1 (Inl e) s2 h2 (Ex v)
| EvalInr : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ans v)
  -> eval s1 h1 (Inr e) s2 h2 (Ans (VInr v))
| EvalInrEx : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ex v)
  -> eval s1 h1 (Inr e) s2 h2 (Ex v)

| EvalCaseL : forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
  eval s1 h1 e s2 h2 (Ans (VInl v))
  -> eval s2 h2 (e1 v) s3 h3 r
  -> eval s1 h1 (ECase e e1 e2) s3 h3 r
| EvalCaseR : forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
  eval s1 h1 e s2 h2 (Ans (VInr v))
  -> eval s2 h2 (e2 v) s3 h3 r
  -> eval s1 h1 (ECase e e1 e2) s3 h3 r
| EvalCaseEx : forall s1 h1 e e1 e2 s2 h2 v,
  eval s1 h1 e s2 h2 (Ex v)
  -> eval s1 h1 (ECase e e1 e2) s2 h2 (Ex v)

| EvalNew : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ans v)
  -> eval s1 h1 (Ref e) s2 (v :: h2) (Ans (VRef (length h2)))
| EvalNewEx : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ex v)
  -> eval s1 h1 (Ref e) s2 h2 (Ex v)

| EvalRead : forall s1 h1 e s2 h2 r v,
  eval s1 h1 e s2 h2 (Ans (VRef r))
  -> h2 # r = Some v
  -> eval s1 h1 (!e) s2 h2 (Ans v)
| EvalReadEx : forall s1 h1 e s2 h2 v,
  eval s1 h1 e s2 h2 (Ex v)
  -> eval s1 h1 (!e) s2 h2 (Ex v)

| EvalWrite : forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
  eval s1 h1 e1 s2 h2 (Ans (VRef r))
  -> eval s2 h2 e2 s3 h3 (Ans v)
  -> eval s1 h1 (e1 ::= e2) s3 (h3 ## r <~ v) (Ans VUnit)
| EvalWriteEx1 : forall s1 h1 e1 s2 h2 e2 v,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> eval s1 h1 (e1 ::= e2) s2 h2 (Ex v)
| EvalWriteEx2 : forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
  eval s1 h1 e1 s2 h2 (Ans (VRef r))
  -> eval s2 h2 e2 s3 h3 (Ex v)
  -> eval s1 h1 (e1 ::= e2) s3 h3 (Ex v)

| EvalThrow : forall s1 h1 e1 s2 h2 v,
  eval s1 h1 e1 s2 h2 (Ans v)
  -> eval s1 h1 (Throw e1) s2 h2 (Ex v)
| EvalThrowEx : forall s1 h1 e1 s2 h2 v,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> eval s1 h1 (Throw e1) s2 h2 (Ex v)

| EvalCatch : forall s1 h1 e1 s2 h2 v e2,
  eval s1 h1 e1 s2 h2 (Ans v)
  -> eval s1 h1 (ECatch e1 e2) s2 h2 (Ans v)
| EvalCatchEx : forall s1 h1 e1 s2 h2 v e2 s3 h3 r,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> eval s2 h2 (e2 v) s3 h3 r
  -> eval s1 h1 (ECatch e1 e2) s3 h3 r

| EvalConst : forall s h b,
  eval s h (^^b) s h (Ans (VBase b))

| EvalEqT : forall s1 h1 e1 s2 h2 e2 b s3 h3,
  eval s1 h1 e1 s2 h2 (Ans (VBase b))
  -> eval s2 h2 e2 s3 h3 (Ans (VBase b))
  -> eval s1 h1 (e1 == e2) s3 h3 (Ans (VInr VUnit))
| EvalEqF : forall s1 h1 e1 s2 h2 e2 b1 s3 h3 b2,
  eval s1 h1 e1 s2 h2 (Ans (VBase b1))
  -> eval s2 h2 e2 s3 h3 (Ans (VBase b2))
  -> b1 <> b2
  -> eval s1 h1 (e1 == e2) s3 h3 (Ans (VInl VUnit))
| EvalEqEx1 : forall s1 h1 e1 s2 h2 e2 v,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> eval s1 h1 (e1 == e2) s2 h2 (Ex v)
| EvalEqEx2 : forall s1 h1 e1 s2 h2 e2 b s3 h3 v,
  eval s1 h1 e1 s2 h2 (Ans (VBase b))
  -> eval s2 h2 e2 s3 h3 (Ex v)
  -> eval s1 h1 (e1 == e2) s3 h3 (Ex v).

Theorem eval_monotone : forall s1 h1 e s2 h2 r,
  eval s1 h1 e s2 h2 r
  -> s1 ~> s2.
  induction 1; eauto.
Qed.

Hint Immediate eval_monotone.

Definition Eval (s1 : closures) (h1 : heap) (E : Exp) (s2 : closures) (h2 : heap) (r : result) :=
  eval s1 h1 (E _) s2 h2 r.


(** * Exp equivalence *)

Section exp_equiv.
  Variables var1 var2 : Type.

  Inductive exp_equiv : list (var1 * var2) -> exp var1 -> exp var2 -> Prop :=
  | EqVar : forall G v1 v2,
    In (v1, v2) G
    -> exp_equiv G (#v1) (#v2)

  | EqApp : forall G f1 x1 f2 x2,
    exp_equiv G f1 f2
    -> exp_equiv G x1 x2
    -> exp_equiv G (f1 @ x1) (f2 @ x2)
  | EqAbs : forall G f1 f2,
    (forall F1 F2 v1 v2, exp_equiv ((F1, F2) :: (v1, v2) :: G) (f1 F1 v1) (f2 F2 v2))
    -> exp_equiv G (Abs f1) (Abs f2)

  | EqLet : forall G f1 x1 f2 x2,
    exp_equiv G f1 f2
    -> (forall v1 v2, exp_equiv ((v1, v2) :: G) (x1 v1) (x2 v2))
    -> exp_equiv G (ELet f1 x1) (ELet f2 x2)

  | EqUnit : forall G,
    exp_equiv G () ()

  | EqPair : forall G x1 y1 x2 y2,
    exp_equiv G x1 x2
    -> exp_equiv G y1 y2
    -> exp_equiv G [< x1, y1 >] [< x2, y2 >]
  | EqFst : forall G e1 e2,
    exp_equiv G e1 e2
    -> exp_equiv G (Fst e1) (Fst e2)
  | EqSnd : forall G e1 e2,
    exp_equiv G e1 e2
    -> exp_equiv G (Snd e1) (Snd e2)

  | EqInl : forall G e1 e2,
    exp_equiv G e1 e2
    -> exp_equiv G (Inl e1) (Inl e2)
  | EqInr : forall G e1 e2,
    exp_equiv G e1 e2
    -> exp_equiv G (Inr e1) (Inr e2)
  | EqCase : forall G e e' e1 e1' e2 e2',
    exp_equiv G e e'
    -> (forall v1 v2, exp_equiv ((v1, v2) :: G) (e1 v1) (e1' v2))
    -> (forall v1 v2, exp_equiv ((v1, v2) :: G) (e2 v1) (e2' v2))
    -> exp_equiv G (ECase e e1 e2) (ECase e' e1' e2')

  | EqNew : forall G e1 e2,
    exp_equiv G e1 e2
    -> exp_equiv G (Ref e1) (Ref e2)
  | EqRead : forall G e1 e2,
    exp_equiv G e1 e2
    -> exp_equiv G (!e1) (!e2)
  | EqWrite : forall G e1 e2 e1' e2',
    exp_equiv G e1 e2
    -> exp_equiv G e1' e2'
    -> exp_equiv G (e1 ::= e1') (e2 ::= e2')

  | EqThrow : forall G e1 e2,
    exp_equiv G e1 e2
    -> exp_equiv G (Throw e1) (Throw e2)
  | EqCatch : forall G e1 e2 e1' e2',
    exp_equiv G e1 e1'
    -> (forall v1 v2, exp_equiv ((v1, v2) :: G) (e2 v1) (e2' v2))
    -> exp_equiv G (ECatch e1 e2) (ECatch e1' e2')

  | EqConst : forall G b,
    exp_equiv G (^^b) (^^b)
  | EqEq : forall G e11 e12 e21 e22,
    exp_equiv G e11 e21
    -> exp_equiv G e12 e22
    -> exp_equiv G (e11 == e12) (e21 == e22).
End exp_equiv.

Definition Exp_wf (E : Exp) := forall var1 var2,
  exp_equiv nil (E var1) (E var2).
