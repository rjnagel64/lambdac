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

Require Import Core.
Require Import CPS.

Require Import CPSify.

Set Implicit Arguments.


Section cr.
  Variable s1 : Core.closures.
  Variable s2 : CPS.closures.

  Import Core.

  Inductive cr : Core.val -> CPS.val -> Prop :=
  | EquivArrow : forall l1 l2 G
    (f1 : Core.val -> Core.val -> Core.exp Core.val)
    (f2 : CPS.val -> CPS.val -> Core.exp CPS.val),
    (forall F1 F2 x1 x2, exp_equiv ((F1, F2) :: (x1, x2) :: G) (f1 F1 x1) (f2 F2 x2))
    -> (forall x1 x2, In (x1, x2) G -> cr x1 x2)
    -> s1 # l1 = Some f1
    -> s2 # l2 = Some (cpsFunc f2)
    -> cr (Core.VFunc l1) (CPS.VCont l2)

  | EquivUnit : cr Core.VUnit CPS.VUnit

  | EquivPair : forall x1 x2 y1 y2,
    cr x1 x2
    -> cr y1 y2
    -> cr (Core.VPair x1 y1) (CPS.VPair x2 y2)

  | EquivInl : forall v1 v2,
    cr v1 v2
    -> cr (Core.VInl v1) (CPS.VInl v2)
  | EquivInr : forall v1 v2,
    cr v1 v2
    -> cr (Core.VInr v1) (CPS.VInr v2)

  | EquivRef : forall l,
    cr (Core.VRef l) (CPS.VRef l)

  | EquivBase : forall b,
    cr (Core.VBase b) (CPS.VBase b).

  Inductive crr : Core.result -> CPS.result -> Prop :=
  | EquivAns : forall v1 v2,
    cr v1 v2
    -> crr (Core.Ans v1) (CPS.Ans v2)
  | EquivEx : forall v1 v2,
    cr v1 v2
    -> crr (Core.Ex v1) (CPS.Ex v2).
End cr.

Notation "s1 & s2 |-- v1 ~~ v2" := (cr s1 s2 v1 v2) (no associativity, at level 70).
Notation "s1 & s2 |--- r1 ~~ r2" := (crr s1 s2 r1 r2) (no associativity, at level 70).

Hint Constructors cr crr.

Section cr_extend'.
  Variables s1 s1' : Core.closures.
  Variables s2 s2' : CPS.closures.
  Hypothesis H1 : s1 ~> s1'.
  Hypothesis H2 : s2 ~> s2'.

  Lemma cr_extend' : forall v1 v2,
    s1 & s2 |-- v1 ~~ v2
    -> s1' & s2' |-- v1 ~~ v2.
    induction 1; eauto.
  Qed.
End cr_extend'.

Theorem cr_extend : forall s1 s2 s1' s2' v1 v2,
  s1 & s2 |-- v1 ~~ v2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> s1' & s2' |-- v1 ~~ v2.
  intros; eapply cr_extend'; eauto.
Qed.

Hint Resolve cr_extend.

Theorem crr_extend : forall s1 s2 s1' s2' r1 r2,
  s1 & s2 |--- r1 ~~ r2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> s1' & s2' |--- r1 ~~ r2.
  destruct 1; eauto.
Qed.

Hint Resolve crr_extend.

Lemma cr_push : forall v1 v2 v1' v2' G s1 s2,
  In (v1, v2) ((v1', v2') :: G)
  -> s1 & s2 |-- v1' ~~ v2'
  -> (forall v3 v4, In (v3, v4) G -> s1 & s2 |-- v3 ~~ v4)
  -> s1 & s2 |-- v1 ~~ v2.
  simpler.
Qed.

Lemma cr_pushA' : forall v1 v2 F1 F2 v1' v2' G s1 s2,
  In (v1, v2) ((F1, F2) :: (v1', v2') :: G)
  -> s1 & s2 |-- v1' ~~ v2'
  -> s1 & s2 |-- F1 ~~ F2
  -> (forall v3 v4, In (v3, v4) G -> s1 & s2 |-- v3 ~~ v4)
  -> s1 & s2 |-- v1 ~~ v2.
  simpler.
Qed.

Lemma cr_pushA : forall s1 ke k s2 v1 v2 l1 l2 x1 x2 G,
  In (v1, v2) ((VFunc l1, VCont l2) :: (x1, x2) :: G)
  -> s1 & s2 |-- x1 ~~ x2
  -> s1 & s2 |-- VFunc l1 ~~ VCont l2
  -> (forall x1 x2, In (x1, x2) G -> s1 & s2 |-- x1 ~~ x2)
  -> s1 & ke :: k :: s2 |-- v1 ~~ v2.
  intros; eapply cr_pushA'; eauto.
Qed.

Hint Extern 1 (_ & _ |-- _ ~~ _) =>
  match goal with
    | [ |- _ & _ :: _ :: _ |-- _ ~~ _ ] => eapply cr_pushA || fail 1
    | _ => eapply cr_push
  end.

Notation "s1 & s2 |-- h1 ~~~ h2" := (sall (cr s1 s2) h1 h2) (no associativity, at level 70).

Definition answer (r : CPS.result) (P1 : val -> Prop) (P2 : val -> Prop) :=
   match r with
     | Ans v => P1 v
     | Ex v => P2 v
   end.

Lemma EquivRef' : forall s1 s2 h1 h2,
  s1 & s2 |-- h1 ~~~ h2
  -> s1 & s2 |-- Core.VRef (length h1) ~~ VRef (length h2).
  intros; match goal with
            | [ H : _ |- _ ] => rewrite <- (sall_length H)
          end; auto.
Qed.

Theorem answer_Ans : forall (P1 : _ -> Prop) P2 v,
  P1 v
  -> answer (Ans v) P1 P2.
  tauto.
Qed.

Theorem answer_Ex : forall P1 (P2 : _ -> Prop) v,
  P2 v
  -> answer (Ex v) P1 P2.
  tauto.
Qed.

Lemma cpsExp_correct : forall s1 h1 (e1 : Core.expV) s1' h1' r1,
  Core.eval s1 h1 e1 s1' h1' r1
  -> forall G (e2 : Core.exp CPS.val),
    Core.exp_equiv G e1 e2
    -> forall s2 h2,
      (forall v1 v2, In (v1, v2) G -> s1 & s2 |-- v1 ~~ v2)
      -> s1 & s2 |-- h1 ~~~ h2
      -> forall k ke, exists s2', exists h2', exists r2,
        (forall r,
          answer r2
          (fun v2 => CPS.eval s2' h2' (k v2) r
            -> CPS.eval s2 h2 (cpsExp e2 k ke) r)
          (fun v2 => CPS.eval s2' h2' (ke v2) r
            -> CPS.eval s2 h2 (cpsExp e2 k ke) r))
        /\ s1' & s2' |--- r1 ~~ r2
        /\ s2 ~> s2'
        /\ s1' & s2' |-- h1' ~~~ h2'.
  Hint Constructors CPS.evalP.
  Hint Resolve answer_Ans answer_Ex.
  Hint Resolve CPS.EvalCaseL CPS.EvalCaseR EquivRef'.

  Hint Extern 1 (CPS.eval _ _ (cpsFunc _ _ _) _) => unfold cpsFunc, cpsFunc'.

  induction 1; abstract (inversion 1; simpler;
    repeat (match goal with
              | [ H : _ & _ |-- _ ~~ _ |- _ ] => invert_1_2 H
              | [ H : _ & _ |--- _ ~~ _ |- _ ] => invert_1 H
              | [ H : forall G e2, Core.exp_equiv G ?E e2 -> _ |- _ ] =>
                match goal with
                  | [ _ : Core.eval ?S _ E _ _ _, _ : Core.eval _ _ ?E' ?S _ _,
                      _ : forall G e2, Core.exp_equiv G ?E' e2 -> _ |- _ ] => fail 1
                  | _ => match goal with
                           | [ k : val -> expV, ke : val -> exp val,
                               _ : _ & ?s |-- _ ~~ _, _ : context[VCont] |- _ ] =>
                             guessWith ((fun (_ : val) x => ke x) :: (fun (_ : val) x => k x) :: s) H
                           | _ => guess H
                         end
                end
            end; simpler);
    try (match goal with
           | [ H1 : _, H2 : _ |- _ ] => generalize (sall_grab H1 H2)
         end; simpler);
    splitter; eauto 9 with cps_eval; intros;
      try match goal with
            | [ H : _ & _ |--- _ ~~ ?r |- answer ?r _ _ ] =>
              inverter H; simpler; eauto 9 with cps_eval
          end).
Qed.

Inductive comp : Core.val -> CPS.val -> Prop :=
| CompArrow : forall l v,
  comp (Core.VFunc l) v

| CompUnit : comp Core.VUnit CPS.VUnit

| CompPair : forall x1 x2 y1 y2,
  comp x1 x2
  -> comp y1 y2
  -> comp (Core.VPair x1 y1) (CPS.VPair x2 y2)

| CompInl : forall v1 v2,
  comp v1 v2
  -> comp (Core.VInl v1) (CPS.VInl v2)
| CompInr : forall v1 v2,
  comp v1 v2
  -> comp (Core.VInr v1) (CPS.VInr v2)

| CompRef : forall l v,
  comp (Core.VRef l) v

| CompBase : forall b,
  comp (Core.VBase b) (CPS.VBase b).

Inductive compR : Core.result -> CPS.result -> Prop :=
| CompAns : forall v1 v2,
  comp v1 v2
  -> compR (Core.Ans v1) (CPS.Ans v2)
| CompEx : forall v1 v2,
  comp v1 v2
  -> compR (Core.Ex v1) (CPS.Ex v2).

Hint Constructors comp compR.

Lemma comp_in : forall s1 s2 v1 v2,
  s1 & s2 |-- v1 ~~ v2
  -> comp v1 v2.
  induction 1; eauto.
Qed.

Hint Resolve comp_in.

Lemma compR_in : forall s1 s2 r1 r2,
  s1 & s2 |--- r1 ~~ r2
  -> compR r1 r2.
  destruct 1; eauto.
Qed.

Hint Resolve compR_in.

Theorem CpsExp_correct : forall (E : Core.Exp) s h r1,
  Core.Eval nil nil E s h r1
  -> Core.Exp_wf E
  -> exists r2,
    CPS.Eval nil nil (CpsExp E) r2
    /\ compR r1 r2.
  Hint Constructors CPS.eval.

  unfold CpsExp, CPS.Eval; intros until r1; intros H1 H2;
    generalize (cpsExp_correct H1 (H2 _ _)
      (s2 := nil) (fun _ _ pf => match pf with end)
      (sall_nil _) (@EHalt _) (@EUncaught _)); simpler;
    match goal with
      | [ H : _ & _ |--- _ ~~ _ |- _ ] => destruct H
    end; simpler; eauto 6.
Qed.
