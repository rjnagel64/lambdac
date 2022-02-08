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

  Inductive primop : Type :=
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

  Inductive exp : Type :=
  | EHalt : var -> exp
  | Call : var -> var -> exp
  | Bind : primop -> (var -> exp) -> exp
  | ECase : var -> (var -> exp) -> (var -> exp) -> exp
  | EUncaught : var -> exp.

  Inductive prog : Type :=
  | Abs : (var -> var -> exp) -> (var -> prog) -> prog
  | EBody : exp -> prog.
End vars.

Implicit Arguments Unit [var].
Implicit Arguments Const [var].
Implicit Arguments EHalt [var].
Implicit Arguments EUncaught [var].

Bind Scope closed_scope with exp primop prog.
Delimit Scope closed_scope with closed.
Open Local Scope closed_scope.

Notation "()" := Unit : closed_scope.

Notation "[< e1 , e2 >]" := (Pair e1 e2) (at level 0) : closed_scope.
Notation "'Fst' e" := (EFst e) (at level 72) : closed_scope.
Notation "'Snd' e" := (ESnd e) (at level 72) : closed_scope.

Notation "'Inl' e" := (EInl e) (at level 72) : closed_scope.
Notation "'Inr' e" := (EInr e) (at level 72) : closed_scope.

Notation "'Ref' e" := (New e) (no associativity, at level 71) : closed_scope.
Notation "! e" := (Read e) (no associativity, at level 71) : closed_scope.
Infix "::=" := Write (no associativity, at level 71) : closed_scope.

Notation "^^ e" := (Const e) (no associativity, at level 71) : closed_scope.
Infix "==" := Eq (no associativity, at level 71) : closed_scope.


Notation "'Halt'" := EHalt : closed_scope.
Notation "'Uncaught'" := EUncaught : closed_scope.
Infix "@@@" := Call (no associativity, at level 80) : closed_scope.
Notation "x <- p ; e" := (Bind p (fun x => e)) (right associativity, at level 80) : closed_scope.
Notation "'Case' e 'Of' x => e1 | y => e2" := (ECase e (fun x => e1) (fun y => e2))
  (no associativity, at level 80) : closed_scope.


Notation "f <== \ x , e ; fs" := (Abs (fun _ x => e) (fun f => fs)) (at level 81) : closed_scope.
Notation "f <== \\ F , x , e ; fs" := (Abs (fun F x => e) (fun f => fs)) (at level 81) : closed_scope.
Notation "'Body' x" := (EBody x) (at level 80) : closed_scope.


Definition Primop := forall var, primop var.
Definition Exp := forall var, exp var.
Definition Prog := forall var, prog var.


Inductive val : Set :=
| VCont : label -> val
| VUnit : val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VRef : label -> val
| VBase : base -> val.

Definition progV := prog val.
Definition expV := exp val.
Definition primopV := primop val.

Definition closure := val -> val -> expV.
Definition closures := list closure.

Definition heap := list val.

Inductive evalP : heap -> primopV -> heap -> val -> Prop :=
| EvalUnit : forall h,
  evalP h () h VUnit

| EvalTuple : forall h v1 v2,
  evalP h [< v1, v2 >] h (VPair v1 v2)
| EvalFst : forall h v1 v2,
  evalP h (Fst (VPair v1 v2)) h v1
| EvalSnd : forall h v1 v2,
  evalP h (Snd (VPair v1 v2)) h v2

| EvalInl : forall h v,
  evalP h (Inl v) h (VInl v)
| EvalInr : forall h v,
  evalP h (Inr v) h (VInr v)

| EvalNew : forall h v,
  evalP h (Ref v) (v :: h) (VRef (length h))
| EvalRead : forall h r v,
  h # r = Some v
  -> evalP h (!(VRef r)) h v
| EvalWrite : forall h r v,
  evalP h (VRef r ::= v) (h ## r <~ v) VUnit

| EvalConst : forall h b,
  evalP h (Const b) h (VBase b)
| EvalEqT : forall h b,
  evalP h (VBase b == VBase b) h (VInr VUnit)
| EvalEqF : forall h b1 b2,
  b1 <> b2
  -> evalP h (VBase b1 == VBase b2) h (VInl VUnit).

Inductive result : Type :=
| Ans : val -> result
| Ex : val -> result.

Section eval.
  Variable s : closures.

  Inductive eval : heap -> expV -> result -> Prop :=
  | EvalHalt : forall h v,
    eval h (Halt v) (Ans v)
  | EvalApp : forall h1 l v f r,
    s # l = Some f
    -> eval h1 (f (VCont l) v) r
    -> eval h1 (VCont l @@@ v) r

  | EvalBind : forall h1 p e h2 v1 v2,
    evalP h1 p h2 v1
    -> eval h2 (e v1) v2
    -> eval h1 (Bind p e) v2
  | EvalCaseL : forall h1 v e1 e2 r,
    eval h1 (e1 v) r
    -> eval h1 (ECase (VInl v) e1 e2) r
  | EvalCaseR : forall h1 v e1 e2 r,
    eval h1 (e2 v) r
    -> eval h1 (ECase (VInr v) e1 e2) r

  | EvalUncaught : forall h v,
    eval h (Uncaught v) (Ex v).
End eval.

Inductive evalPr : closures -> progV -> result -> Prop :=
| EvalBody : forall s e r,
  eval s nil e r
  -> evalPr s (Body e) r
| EvalAbs : forall s f pr r,
  evalPr (f :: s) (pr (VCont (length s))) r
  -> evalPr s (Abs f pr) r.

Definition Eval (s : closures) (h1 : heap) (E : Exp) (r : result) :=
  eval s h1 (E _) r.
Definition EvalP (h1 : heap) (P : Primop) (h2 : heap) (v : val) :=
  evalP h1 (P _) h2 v.
Definition EvalPr (s : closures) (P : Prog) (r : result) :=
  evalPr s (P _) r.

Ltac evalOne := (econstructor; [ solve [ eauto ] | concretize; simpl ])
  || (econstructor; [])
  || solve [ econstructor ].

Hint Extern 1 (eval _ _ _ _) =>
  evalOne; repeat evalOne : closed_eval.
Hint Extern 1 (evalPr _ _ _) =>
  evalOne; repeat evalOne : closed_eval.


Section exp_equiv.
  Variables var1 var2 : Type.

  Inductive primop_equiv : list (var1 * var2) -> primop var1 -> primop var2 -> Prop :=
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
    -> primop_equiv G (v1 == v1') (v2 == v2').

  Inductive exp_equiv : list (var1 * var2) -> exp var1 -> exp var2 -> Prop :=
  | EqHalt : forall G v1 v2,
    In (v1, v2) G
    -> exp_equiv G (Halt v1) (Halt v2)
  | EqUncaught : forall G v1 v2,
    In (v1, v2) G
    -> exp_equiv G (Uncaught v1) (Uncaught v2)

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

  Inductive prog_equiv : list (var1 * var2) -> prog var1 -> prog var2 -> Prop :=
  | EqBody : forall G e1 e2,
    exp_equiv G e1 e2
    -> prog_equiv G (Body e1) (Body e2)
  | EqAbs : forall G f1 f2 pr1 pr2,
    (forall F1 F2 v1 v2, exp_equiv ((F1, F2) :: (v1, v2) :: G) (f1 F1 v1) (f2 F2 v2))
    -> (forall v1 v2, prog_equiv ((v1, v2) :: G) (pr1 v1) (pr2 v2))
    -> prog_equiv G (Abs f1 pr1) (Abs f2 pr2).
End exp_equiv.

Definition Prog_wf (P : Prog) := forall var1 var2,
  prog_equiv nil (P var1) (P var2).


Section exp_valid.
  Variable var : Type.

  Inductive primop_valid : list var -> primop var -> Prop :=
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
    -> primop_valid G (v1 == v2).

  Inductive exp_valid : list var -> exp var -> Prop :=
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

  Inductive prog_valid : list var -> prog var -> Prop :=
  | VldBody : forall G e,
    exp_valid G e
    -> prog_valid G (Body e)
  | VldAbs : forall G f pr,
    (forall F v, exp_valid (F :: v :: G) (f F v))
    -> (forall v, prog_valid (v :: G) (pr v))
    -> prog_valid G (Abs f pr).
End exp_valid.

Hint Constructors exp_valid primop_valid prog_valid.

Lemma var_valid : forall var x x' G,
  In (x, x') G
  -> In x (map (fst (A:=var) (B:=var)) G).
  induction G; simpler.
Qed.

Hint Resolve var_valid.

Lemma Primop_valid : forall var G (p1 p2 : primop var),
  primop_equiv G p1 p2
  -> primop_valid (map (@fst _ _) G) p1.
  induction 1; simpler; eauto.
Qed.

Hint Resolve Primop_valid.

Lemma Exp_valid : forall var G (e1 e2 : exp var),
  exp_equiv G e1 e2
  -> exp_valid (map (@fst _ _) G) e1.
  induction 1; simpler; eauto.
Qed.

Hint Resolve Exp_valid.

Lemma Prog_valid' : forall var G (pr1 pr2 : prog var),
  prog_equiv G pr1 pr2
  -> prog_valid (map (@fst _ _) G) pr1.
  Hint Extern 1 (exp_valid (?v :: map ?F ?G) _) =>
    change (v :: map F G) with (map F ((v, v) :: G)).
  Hint Extern 1 (exp_valid (?f :: ?v :: map ?F ?G) _) =>
    change (f :: v :: map F G) with (map F ((f, f) :: (v, v) :: G)).

  induction 1; simpler; eauto.
Qed.

Theorem Prog_valid : forall (P : Prog) var,
  Prog_wf P
  -> prog_valid nil (P var).
  intros; change (@nil var) with (map (@fst var var) nil);
    eapply Prog_valid'; auto.
Qed.
