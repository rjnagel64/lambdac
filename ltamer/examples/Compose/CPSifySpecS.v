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
Require Import Result.

Require Import CPSifySpec.

Set Implicit Arguments.


Import Core.

Inductive support1 : closures -> heap -> expV -> closures -> heap -> expV -> Prop :=
| SupApp1 : forall e1 e2 s1 h1,
  support1 s1 h1 (e1 @ e2) s1 h1 e1
| SupApp2 : forall e1 e2 s1 h1 s2 h2 l,
  eval s1 h1 e1 s2 h2 (Ans (VFunc l))
  -> support1 s1 h1 (e1 @ e2) s2 h2 e2
| SupApp3 : forall e1 e2 s1 h1 s2 h2 l f s3 h3 v1,
  eval s1 h1 e1 s2 h2 (Ans (VFunc l))
  -> s2 # l = Some f
  -> eval s2 h2 e2 s3 h3 (Ans v1)
  -> support1 s1 h1 (e1 @ e2) s3 h3 (f (VFunc l) v1)

| SupLet1 : forall s1 h1 e1 e2,
  support1 s1 h1 (ELet e1 e2) s1 h1 e1
| SupLet2 : forall s1 h1 e1 e2 s2 h2 v,
  eval s1 h1 e1 s2 h2 (Ans v)
  -> support1 s1 h1 (ELet e1 e2) s2 h2 (e2 v)

| SupPair1 : forall s1 h1 e1 e2,
  support1 s1 h1 [<e1, e2>] s1 h1 e1
| SupPair2 : forall s1 h1 e1 s2 h2 v1 e2,
  eval s1 h1 e1 s2 h2 (Ans v1)
  -> support1 s1 h1 [<e1, e2>] s2 h2 e2

| SupFst : forall s1 h1 e,
  support1 s1 h1 (Fst e) s1 h1 e
| SupSnd : forall s1 h1 e,
  support1 s1 h1 (Snd e) s1 h1 e

| SupInl : forall s1 h1 e,
  support1 s1 h1 (Inl e) s1 h1 e
| SupInr : forall s1 h1 e,
  support1 s1 h1 (Inr e) s1 h1 e

| SupCase1 : forall s1 h1 e e1 e2,
  support1 s1 h1 (ECase e e1 e2) s1 h1 e
| SupCaseL : forall s1 h1 e e1 e2 s2 h2 v,
  eval s1 h1 e s2 h2 (Ans (VInl v))
  -> support1 s1 h1 (ECase e e1 e2) s2 h2 (e1 v)
| SupCaseR : forall s1 h1 e e1 e2 s2 h2 v,
  eval s1 h1 e s2 h2 (Ans (VInr v))
  -> support1 s1 h1 (ECase e e1 e2) s2 h2 (e2 v)

| SupNew : forall s1 h1 e,
  support1 s1 h1 (New e) s1 h1 e
| SupRead : forall s1 h1 e,
  support1 s1 h1 (Read e) s1 h1 e

| SupWrite1 : forall s1 h1 e1 e2,
  support1 s1 h1 (e1 ::= e2) s1 h1 e1
| SupWrite2 : forall s1 h1 e1 s2 h2 v1 e2,
  eval s1 h1 e1 s2 h2 (Ans v1)
  -> support1 s1 h1 (e1 ::= e2) s2 h2 e2

| SupThrow : forall s1 h1 e,
  support1 s1 h1 (Throw e) s1 h1 e

| SupCatch1 : forall s1 h1 e1 e2,
  support1 s1 h1 (ECatch e1 e2) s1 h1 e1
| SupCatch2 : forall s1 h1 e1 e2 s2 h2 v,
  eval s1 h1 e1 s2 h2 (Ex v)
  -> support1 s1 h1 (ECatch e1 e2) s2 h2 (e2 v).

Inductive support : closures -> heap -> expV -> closures -> heap -> expV -> Prop :=
| SupOne : forall s1 h1 e1 s2 h2 e2,
  support1 s1 h1 e1 s2 h2 e2
  -> support s1 h1 e1 s2 h2 e2
| SupTrans : forall s1 h1 e1 s2 h2 e2 s3 h3 e3,
  support1 s1 h1 e1 s2 h2 e2
  -> support s2 h2 e2 s3 h3 e3
  -> support s1 h1 e1 s3 h3 e3.

Hint Constructors support1 support.

Module Type COMPILATION.
  Parameter self : compilation.

  Axiom selfOk : compilationOk self.

  Axiom Cases : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s1' h1' r,
      eval s1 h1 e1 s1' h1' r
      -> (forall s1'' h1'' e1', support s1 h1 e1 s1'' h1'' e1'
        -> forall s1''' h1''' r',
          eval s1'' h1'' e1' s1''' h1''' r'
          -> spec full full s1'' h1'' e1' s1''' h1''' r')
      -> spec full self s1 h1 e1 s1' h1' r.
End COMPILATION.

Theorem eval_det : forall s1 h1 e s2 h2 r,
  eval s1 h1 e s2 h2 r
  -> forall s2' h2' r', eval s1 h1 e s2' h2' r'
    -> s2 = s2' /\ h2 = h2' /\ r = r'.
  induction 1; inversion 1; subst;
    repeat match goal with
             | _ => discriminate
             | [ H : Ans _ = Ans _ |- _ ] => injection H; clear H; intros; subst
             | [ H : Ex _ = Ex _ |- _ ] => injection H; clear H; intros; subst
             | [ H1 : ?E = Some _, H2 : ?E = Some _ |- _ ] =>
               rewrite H1 in H2; clear H1; injection H2; clear H2; intros; subst
             | [ H1 : forall s2' h2' r', _ -> _ /\ _ /\ ?r1 = r', H2 : eval _ _ _ _ _ ?r2 |- _ ] =>
               match r1 with
                 | r2 => fail 1
                 | _ => generalize (H1 _ _ _ H2); clear H1; intros [? [? ?]]; subst
               end
           end; tauto.
Qed.

Module Close (C : COMPILATION) : CLOSED with Definition comp := C.self.
  Definition comp := C.self.

  Lemma correct' : forall s1 h1 e1 s1' h1' r1,
    Core.eval s1 h1 e1 s1' h1' r1
    -> forall ss1 sh1 se1 ss1' sh1' sr1,
      (ss1 = s1 /\ sh1 = h1 /\ se1 = e1) \/ support s1 h1 e1 ss1 sh1 se1
      -> Core.eval ss1 sh1 se1 ss1' sh1' sr1
      -> forall G e2 k ke,
        compExp C.self G se1 k ke e2
        -> forall s2 h2,
          (forall v1 v2, In (v1, v2) G -> C.self &| ss1 & s2 |-- v1 ~~ v2)
          -> C.self &| ss1 & s2 |-- sh1 ~~~ h2
          -> exists s2', exists h2', exists r2,
            (forall r,
              answer r2
              (fun v2 => CPS.eval s2' h2' (k v2) r
                -> CPS.eval s2 h2 e2 r)
              (fun v2 => CPS.eval s2' h2' (ke v2) r
                -> CPS.eval s2 h2 e2 r))
            /\ C.self &| ss1' & s2' |--- sr1 ~~ r2
            /\ s2 ~> s2'
            /\ C.self &| ss1' & s2' |-- sh1' ~~~ h2'.
    Hint Constructors Core.eval.

    induction 1; abstract (simpler;
      repeat (match goal with
                | [ H : Ans _ = Ans _ |- _ ] => injection H; clear H; intros; subst
                | [ H : Ex _ = Ex _ |- _ ] => injection H; clear H; intros; subst
                | [ H1 : eval ?S ?H ?E _ _ _, H2 : eval ?S ?H ?E _ _ _ |- _ ] =>
                  generalize (eval_det H1 H2); clear H2; simpler
                | [ H : support1 _ _ _ _ _ _ |- _ ] => inverter H; subst
                | [ H : support _ _ _ _ _ _ |- _ ] => inverter H; subst
                | [ _ : compExp _ _ ?e _ _ _, _ : forall v1 v2, _ -> _ &| ?s & _ |-- _ ~~ _,
                    _ : _ &| _ & _ |-- ?h ~~~ _ |- _ ] =>
                  generalize C.Cases; intro HC; unfold spec in HC;
                    eapply (HC _ (includes_refl _) C.selfOk s h e); intros; eauto
              end; eauto)).
  Qed.

  Theorem correctOpen : forall e1 s1 h1 s1' h1' r e2 G s2 h2,
    Core.eval s1 h1 e1 s1' h1' r
    -> compExp comp G e1 (fun _ => Halt)%cps (fun _ => Uncaught)%cps e2
    -> (forall v1 v2, In (v1, v2) G -> comp &| s1 & s2 |-- v1 ~~ v2)
    -> comp &| s1 & s2 |-- h1 ~~~ h2
    -> CPS.eval s2 h2 e2 (cpsResult r).
    Hint Constructors CPS.eval.

    unfold comp; intros until h2; intros H1 H2 H3 H4;
      generalize (correct' H1 (or_introl _ (conj (refl_equal _) (conj (refl_equal _) (refl_equal _))))
        H1 _ _ _ _ H2 H3 H4); simpler;
      match goal with
        | [ H : _ &| _ & _ |--- _ ~~ _ |- _ ] => destruct H
      end; simpler.
  Qed.

  Theorem correctClosed : forall e1 s h r e2,
    Core.eval nil nil e1 s h r
    -> compExp comp nil e1 (fun _ => Halt)%cps (fun _ => Uncaught)%cps e2
    -> CPS.eval nil nil e2 (cpsResult r).
    Hint Constructors CPS.eval.

    unfold comp; intros until e2; intros H1 H2;
      generalize (correct' H1 (or_introl _ (conj (refl_equal _) (conj (refl_equal _) (refl_equal _))))
        H1 _ _ _ _ H2
        (s2 := nil) (fun _ _ pf => match pf with end)
        (sall_nil _)); simpler;
      match goal with
        | [ H : _ &| _ & _ |--- _ ~~ _ |- _ ] => destruct H
      end; simpler.
  Qed.
End Close.

Module Join (C1 : COMPILATION) (C2 : COMPILATION)
  : COMPILATION with Definition self := join C1.self C2.self.
  Definition self := join C1.self C2.self.

  Theorem selfOk : compilationOk self.
    red; unfold self; simpler;
      match goal with
        | [ F1 : Core.val, F2 : CPS.val, v1 : Core.val, v2 : CPS.val, k : CPS.val, ke : CPS.val,
            H : compFunc _ _ _ _ |- _ ] =>
          solve [ generalize (C1.selfOk _ _ _ H F1 F2 v1 v2 k ke); firstorder
            | generalize (C2.selfOk _ _ _ H F1 F2 v1 v2 k ke); firstorder ]
      end.
  Qed.

  Theorem Cases : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s1' h1' r,
      eval s1 h1 e1 s1' h1' r
      -> (forall s1'' h1'' e1', support s1 h1 e1 s1'' h1'' e1'
        -> forall s1''' h1''' r',
          eval s1'' h1'' e1' s1''' h1''' r'
          -> spec full full s1'' h1'' e1' s1''' h1''' r')
      -> spec full self s1 h1 e1 s1' h1' r.
    unfold spec, self; intros;
      match goal with
        | [ H : compExp (_ |_| _) _ _ _ _ _ |- _ ] => destruct H
      end;
      [generalize C1.Cases | generalize C2.Cases];
      intro Hc; unfold spec in Hc; eapply Hc; eauto.
  Qed.
End Join.

Module Simple (C : CPSifySpec.COMPILATION)
  : COMPILATION with Definition self := C.self.
  Definition self := C.self.

  Definition selfOk := C.selfOk.

  Hint Unfold spec.

  Theorem Cases : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s1' h1' r,
      eval s1 h1 e1 s1' h1' r
      -> (forall s1'' h1'' e1', support s1 h1 e1 s1'' h1'' e1'
        -> forall s1''' h1''' r',
          eval s1'' h1'' e1' s1''' h1''' r'
          -> spec full full s1'' h1'' e1' s1''' h1''' r')
      -> spec full self s1 h1 e1 s1' h1' r.
    Ltac t c := generalize c; intro Hc; red in Hc; eapply Hc; eauto;
      red; intros; match goal with
                     | [ H : forall s'' : closures, _ |- _ ] => eapply H
                       end;
      try match goal with
            | [ |- eval _ _ _ _ _ _ ] => eauto
          end; eauto.

    unfold spec, self; destruct 3; intros; [
      t C.VarCase
      | t C.AppCase
      | t C.AppEx1Case
      | t C.AppEx2Case
      | t C.AbsCase
      | t C.LetCase
      | t C.LetExCase
      | t C.PairCase
      | t C.PairEx1Case
      | t C.PairEx2Case
      | t C.UnitCase
      | t C.FstCase
      | t C.FstExCase
      | t C.SndCase
      | t C.SndExCase
      | t C.InlCase
      | t C.InlExCase
      | t C.InrCase
      | t C.InrExCase
      | t C.CaseLCase
      | t C.CaseRCase
      | t C.CaseExCase
      | t C.NewCase
      | t C.NewExCase
      | t C.ReadCase
      | t C.ReadExCase
      | t C.WriteCase
      | t C.WriteEx1Case
      | t C.WriteEx2Case
      | t C.ThrowCase
      | t C.ThrowExCase
      | t C.CatchCase
      | t C.CatchExCase ].
  Qed.
End Simple.
