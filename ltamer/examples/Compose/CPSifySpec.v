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

Set Implicit Arguments.


Inductive result' : Type :=
| Ans' : val -> result'
| Ex' : val -> result'.

Record compilation : Type := Compilation {
  compExp : list (Core.val * CPS.val)
    -> Core.exp Core.val
    -> (CPS.val -> CPS.exp CPS.val)
    -> (CPS.val -> CPS.exp CPS.val)
    -> CPS.exp CPS.val
    -> Prop;
  compFunc : list (Core.val * CPS.val)
    -> (Core.val -> Core.val -> Core.exp Core.val)
    -> (CPS.val -> CPS.val -> CPS.exp CPS.val)
    -> Prop
}.

Definition includes (c1 c2 : compilation) :=
  (forall G e1 k ke e2, compExp c1 G e1 k ke e2 -> compExp c2 G e1 k ke e2)
  /\ (forall G f1 f2, compFunc c1 G f1 f2 -> compFunc c2 G f1 f2).

Infix "[=" := includes (no associativity, at level 70).

Theorem includes_refl : forall c,
  c [= c.
  unfold includes; tauto.
Qed.

Hint Resolve includes_refl.

Definition join (c1 c2 : compilation) :=
  Compilation (fun G e1 k ke e2 => compExp c1 G e1 k ke e2 \/ compExp c2 G e1 k ke e2)
  (fun G f1 f2 => compFunc c1 G f1 f2 \/ compFunc c2 G f1 f2).

Infix "|_|" := join (left associativity, at level 69).

Ltac includes_join := unfold includes, join; simpl in *; firstorder.

Theorem includes_join1 : forall c1 c2,
  c1 [= c1 |_| c2.
  includes_join.
Qed.

Theorem includes_join2 : forall c1 c2,
  c2 [= c1 |_| c2.
  includes_join.
Qed.

Theorem uninclude_join1 : forall c1 c2 c,
  c1 |_| c2 [= c
  -> c1 [= c.
  includes_join.
Qed.

Theorem uninclude_join2 : forall c1 c2 c,
  c1 |_| c2 [= c
  -> c2 [= c.
  includes_join.
Qed.

Hint Resolve includes_join1 includes_join2 uninclude_join1 uninclude_join2.

Theorem compExp_join1 : forall c1 c2 G e1 k ke e2,
  compExp c1 G e1 k ke e2
  -> compExp (c1 |_| c2) G e1 k ke e2.
  includes_join.
Qed.

Theorem compExp_join2 : forall c1 c2 G e1 k ke e2,
  compExp c2 G e1 k ke e2
  -> compExp (c1 |_| c2) G e1 k ke e2.
  includes_join.
Qed.

Hint Resolve compExp_join1 compExp_join2.

Lemma compFunc_include : forall c full G f1 f2,
  c [= full
    -> compFunc c G f1 f2
    -> compFunc full G f1 f2.
  unfold compFunc, includes; firstorder.
Qed.

Hint Resolve compFunc_include.

Section cr.
  Variable R : compilation.

  Variable s1 : Core.closures.
  Variable s2 : CPS.closures.

  Import Core.

  Inductive cr : Core.val -> CPS.val -> Prop :=
  | EquivArrow : forall l1 l2 G
    (f1 : Core.val -> Core.val -> Core.exp Core.val)
    (f2 : CPS.val -> CPS.val -> CPS.exp CPS.val),
    s1 # l1 = Some f1
    -> s2 # l2 = Some f2
    -> (forall x1 x2, In (x1, x2) G -> cr x1 x2)
    -> compFunc R G f1 f2
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
    cr (Core.VRef l) (CPS.VRef l).

  Inductive crr : Core.result -> result' -> Prop :=
  | EquivAns : forall v1 v2,
    cr v1 v2
    -> crr (Core.Ans v1) (Ans' v2)
  | EquivEx : forall v1 v2,
    cr v1 v2
    -> crr (Core.Ex v1) (Ex' v2).
End cr.

Notation "R &| s1 & s2 |-- v1 ~~ v2" := (cr R s1 s2 v1 v2) (no associativity, at level 70).
Notation "R &| s1 & s2 |--- r1 ~~ r2" := (crr R s1 s2 r1 r2) (no associativity, at level 70).

Hint Constructors cr crr.

Section cr_extend'.
  Variable R : compilation.

  Variables s1 s1' : Core.closures.
  Variables s2 s2' : CPS.closures.
  Hypothesis H1 : s1 ~> s1'.
  Hypothesis H2 : s2 ~> s2'.

  Lemma cr_extend' : forall v1 v2,
    R &| s1 & s2 |-- v1 ~~ v2
    -> R &| s1' & s2' |-- v1 ~~ v2.
    induction 1; eauto.
  Qed.
End cr_extend'.

Theorem cr_extend : forall R s1 s2 s1' s2' v1 v2,
  R &| s1 & s2 |-- v1 ~~ v2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> R &| s1' & s2' |-- v1 ~~ v2.
  intros; eapply cr_extend'; eauto.
Qed.

Hint Resolve cr_extend.

Hint Extern 1 (_ &| _ & _ :: _ :: _ |-- _ ~~ _) => eapply cr_extend; eauto.

Theorem crr_extend : forall R s1 s2 s1' s2' r1 r2,
  R &| s1 & s2 |--- r1 ~~ r2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> R &| s1' & s2' |--- r1 ~~ r2.
  destruct 1; eauto.
Qed.

Hint Resolve crr_extend.

Lemma cr_push : forall R v1 v2 v1' v2' G s1 s2,
  In (v1, v2) ((v1', v2') :: G)
  -> R &| s1 & s2 |-- v1' ~~ v2'
  -> (forall v3 v4, In (v3, v4) G -> R &| s1 & s2 |-- v3 ~~ v4)
  -> R &| s1 & s2 |-- v1 ~~ v2.
  simpler.
Qed.

Lemma cr_push_rec : forall R v1 v2 v1' v2' G s1 s2 G' l1 l2 f1 f2,
  In (v1, v2) ((v1', v2') :: (VFunc l1, VCont l2) :: G)
  -> R &| s1 & s2 |-- v1' ~~ v2'
    -> s1 # l1 = Some f1
    -> s2 # l2 = Some f2
    -> (forall x1 x2, In (x1, x2) G' -> R &| s1 & s2 |-- x1 ~~ x2)
    -> compFunc R G' f1 f2
    -> (forall v3 v4, In (v3, v4) G -> R &| s1 & s2 |-- v3 ~~ v4)
    -> R &| s1 & s2 |-- v1 ~~ v2.
  simpler; eauto.
Qed.

Hint Resolve cr_push cr_push_rec.

Notation "R &| s1 & s2 |-- h1 ~~~ h2" := (sall (cr R s1 s2) h1 h2) (no associativity, at level 70).

Definition answer (r : result') (P1 : val -> Prop) (P2 : val -> Prop) :=
  match r with
    | Ans' v => P1 v
    | Ex' v => P2 v
  end.

Lemma EquivRef' : forall R s1 s2 h1 h2,
  R &| s1 & s2 |-- h1 ~~~ h2
  -> R &| s1 & s2 |-- Core.VRef (length h1) ~~ VRef (length h2).
  intros; match goal with
            | [ H : _ |- _ ] => rewrite <- (sall_length H)
          end; auto.
Qed.

Theorem answer_Ans : forall (P1 : _ -> Prop) P2 v,
  P1 v
  -> answer (Ans' v) P1 P2.
  tauto.
Qed.

Theorem answer_Ex : forall P1 (P2 : _ -> Prop) v,
  P2 v
  -> answer (Ex' v) P1 P2.
  tauto.
Qed.

Definition compilationOk comp := forall G f1 f2,
  compFunc comp G f1 f2
  -> forall F1 F2 v1 v2 k ke, exists f2',
    compExp comp ((v1, v2) :: (F1, F2) :: G) (f1 F1 v1) (fun x => k @@@ x)%cps (fun x => ke @@@ x)%cps f2'
    /\ (forall s h r,
      CPS.eval s h f2' r
      -> CPS.eval s h (f2 F2 (VPair v2 (VPair k ke))) r).

Definition spec (full self : compilation) s1 h1 (e1 : Core.exp Core.val) s1' h1' r1 :=
  forall G (e2 : CPS.exp CPS.val) k ke,
    compExp self G e1 k ke e2
    -> forall s2 h2,
      (forall v1 v2, In (v1, v2) G -> full &| s1 & s2 |-- v1 ~~ v2)
      -> full &| s1 & s2 |-- h1 ~~~ h2
      -> exists s2', exists h2', exists r2,
        (forall r,
          answer r2
          (fun v2 => CPS.eval s2' h2' (k v2) r
            -> CPS.eval s2 h2 e2 r)
          (fun v2 => CPS.eval s2' h2' (ke v2) r
            -> CPS.eval s2 h2 e2 r))
        /\ full &| s1' & s2' |--- r1 ~~ r2
        /\ s2 ~> s2'
        /\ full &| s1' & s2' |-- h1' ~~~ h2'.

Module Type COMPILATION.
  Parameter self : compilation.

  Axiom selfOk : compilationOk self.

  Axiom VarCase : forall full, self [= full
    -> compilationOk full
    -> forall s h v, spec full self s h (#v) s h (Core.Ans v).

  Axiom AppCase : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 l f0 s3 h3 v1 s4 h4 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> s2 # l = Some f0
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v1)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v1)
      -> Core.eval s3 h3 (f0 (VFunc l) v1) s4 h4 v2
      -> spec full full s3 h3 (f0 (VFunc l) v1) s4 h4 v2
      -> spec full self s1 h1 (e1 @ e2) s4 h4 v2.

  Axiom AppEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (e1 @ e2) s2 h2 (Core.Ex v).

  Axiom AppEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 l s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full self s1 h1 (e1 @ e2) s3 h3 (Core.Ex v).

  Axiom AbsCase : forall full, self [= full
    -> compilationOk full
    -> forall s h e1,
      spec full self s h (Core.Abs e1) (e1 :: s) h (Core.Ans (VFunc (length s))).

  Axiom LetCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v s3 h3 e2 r,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (ELet e1 e2) s3 h3 r.

  Axiom LetExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (ELet e1 e2) s2 h2 (Core.Ex v).

  Axiom PairCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v1)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v1)
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v2)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v2)
      -> spec full self s1 h1 [<e1, e2>] s3 h3 (Core.Ans (Core.VPair v1 v2)).

  Axiom PairEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 [<e1, e2>] s2 h2 (Core.Ex v).

  Axiom PairEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v1)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v1)
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v2)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v2)
      -> spec full self s1 h1 [<e1, e2>] s3 h3 (Core.Ex v2).

  Axiom UnitCase : forall full, self [= full
    -> compilationOk full
    -> forall s h,
      spec full self s h () s h (Core.Ans Core.VUnit).

  Axiom FstCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v1 v2,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full self s1 h1 (Fst e) s2 h2 (Core.Ans v1).

  Axiom FstExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Fst e) s2 h2 (Core.Ex v).

  Axiom SndCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v1 v2,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full self s1 h1 (Snd e) s2 h2 (Core.Ans v2).

  Axiom SndExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Snd e) s2 h2 (Core.Ex v).

  Axiom InlCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Inl e) s2 h2 (Core.Ans (Core.VInl v)).

  Axiom InlExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Inl e) s2 h2 (Core.Ex v).

  Axiom InrCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Inr e) s2 h2 (Core.Ans (Core.VInr v)).

  Axiom InrExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Inr e) s2 h2 (Core.Ex v).

  Axiom CaseLCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VInl v))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VInl v))
      -> Core.eval s2 h2 (e1 v) s3 h3 r
      -> spec full full s2 h2 (e1 v) s3 h3 r
      -> spec full self s1 h1 (Core.ECase e e1 e2) s3 h3 r.

  Axiom CaseRCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VInr v))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VInr v))
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (Core.ECase e e1 e2) s3 h3 r.

  Axiom CaseExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Core.ECase e e1 e2) s2 h2 (Core.Ex v).

  Axiom NewCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Ref e) s2 (v :: h2) (Core.Ans (Core.VRef (length h2))).

  Axiom NewExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Ref e) s2 h2 (Core.Ex v).

  Axiom ReadCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 r v,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VRef r))
      -> h2 # r = Some v
      -> spec full self s1 h1 (!e) s2 h2 (Core.Ans v).

  Axiom ReadExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (!e) s2 h2 (Core.Ex v).

  Axiom WriteCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v)
      -> spec full self s1 h1 (e1 ::= e2) s3 h3 ## r <~ v (Core.Ans Core.VUnit).

  Axiom WriteEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (e1 ::= e2) s2 h2 (Core.Ex v).

  Axiom WriteEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full self s1 h1 (e1 ::= e2) s3 h3 (Core.Ex v).

  Axiom ThrowCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Throw e1) s2 h2 (Core.Ex v).

  Axiom ThrowExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Throw e1) s2 h2 (Core.Ex v).

  Axiom CatchCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (ECatch e1 e2) s2 h2 (Core.Ans v).

  Axiom CatchExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2 s3 h3 r,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (ECatch e1 e2) s3 h3 r.
End COMPILATION.

Definition cpsResult (r : Core.result) :=
  match r with
    | Core.Ans _ => Ans
    | Core.Ex _ => Ex
  end.

Module Type CLOSED.
  Parameter comp : compilation.

  Axiom correctOpen : forall e1 s1 h1 s1' h1' r e2 G s2 h2,
    Core.eval s1 h1 e1 s1' h1' r
    -> compExp comp G e1 (fun _ => Halt)%cps (fun _ => Uncaught)%cps e2
    -> (forall v1 v2, In (v1, v2) G -> comp &| s1 & s2 |-- v1 ~~ v2)
    -> comp &| s1 & s2 |-- h1 ~~~ h2
    -> CPS.eval s2 h2 e2 (cpsResult r).

  Axiom correctClosed : forall e1 s h r e2,
    Core.eval nil nil e1 s h r
    -> compExp comp nil e1 (fun _ => Halt)%cps (fun _ => Uncaught)%cps e2
    -> CPS.eval nil nil e2 (cpsResult r).
End CLOSED.

Module Close (C : COMPILATION) : CLOSED with Definition comp := C.self.
  Definition comp := C.self.

  Lemma correct' : forall s1 h1 e1 s1' h1' r1,
    Core.eval s1 h1 e1 s1' h1' r1
    -> forall G e2 k ke,
      compExp C.self G e1 k ke e2
      -> forall s2 h2,
        (forall v1 v2, In (v1, v2) G -> C.self &| s1 & s2 |-- v1 ~~ v2)
        -> C.self &| s1 & s2 |-- h1 ~~~ h2
        -> exists s2', exists h2', exists r2,
          (forall r,
            answer r2
            (fun v2 => CPS.eval s2' h2' (k v2) r
              -> CPS.eval s2 h2 e2 r)
            (fun v2 => CPS.eval s2' h2' (ke v2) r
              -> CPS.eval s2 h2 e2 r))
          /\ C.self &| s1' & s2' |--- r1 ~~ r2
          /\ s2 ~> s2'
          /\ C.self &| s1' & s2' |-- h1' ~~~ h2'.
    Hint Constructors Core.eval.

    Ltac t H := let H' := fresh "H'" in
      intros; generalize H; intro H'; unfold spec in H'; eapply H';
        try apply includes_refl; try apply C.selfOk; eassumption.

    induction 1; [
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

  Theorem correctOpen : forall e1 s1 h1 s1' h1' r e2 G s2 h2,
    Core.eval s1 h1 e1 s1' h1' r
    -> compExp comp G e1 (fun _ => Halt)%cps (fun _ => Uncaught)%cps e2
    -> (forall v1 v2, In (v1, v2) G -> comp &| s1 & s2 |-- v1 ~~ v2)
    -> comp &| s1 & s2 |-- h1 ~~~ h2
    -> CPS.eval s2 h2 e2 (cpsResult r).
    Hint Constructors CPS.eval.

    unfold comp; intros until h2; intros H1 H2 H3 H4;
      generalize (correct' H1 _ _ _ _ H2 H3 H4); simpler;
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
      generalize (correct' H1 _ _ _ _ H2
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
        | [ F1 : Core.val, F2 : val, v1 : Core.val, v2 : val, k : val, ke : val, H : compFunc _ _ _ _ |- _ ] =>
          solve [ generalize (C1.selfOk _ _ _ H F1 F2 v1 v2 k ke); firstorder
            | generalize (C2.selfOk _ _ _ H F1 F2 v1 v2 k ke); firstorder ]
      end.
  Qed.

  Ltac t ca1 ca2 :=
    unfold spec, self; intros;
      match goal with
        | [ H : compExp (_ |_| _) _ _ _ _ _ |- _ ] => destruct H
      end;
      [generalize ca1 | generalize ca2];
      intro Hc; unfold spec in Hc; eapply Hc; eauto.

  Theorem VarCase : forall full, self [= full
    -> compilationOk full
    -> forall s h v, spec full self s h (#v) s h (Core.Ans v).
    t C1.VarCase C2.VarCase.
  Qed.

  Theorem AppCase : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 l f0 s3 h3 v1 s4 h4 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> s2 # l = Some f0
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v1)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v1)
      -> Core.eval s3 h3 (f0 (VFunc l) v1) s4 h4 v2
      -> spec full full s3 h3 (f0 (VFunc l) v1) s4 h4 v2
      -> spec full self s1 h1 (e1 @ e2) s4 h4 v2.
    t C1.AppCase C2.AppCase.
  Qed.

  Theorem AppEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (e1 @ e2) s2 h2 (Core.Ex v).
    t C1.AppEx1Case C2.AppEx1Case.
  Qed.

  Theorem AppEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 l s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full self s1 h1 (e1 @ e2) s3 h3 (Core.Ex v).
    t C1.AppEx2Case C2.AppEx2Case.
  Qed.

  Theorem AbsCase : forall full, self [= full
    -> compilationOk full
    -> forall s h e1,
      spec full self s h (Core.Abs e1) (e1 :: s) h (Core.Ans (VFunc (length s))).
    t C1.AbsCase C2.AbsCase.
  Qed.

  Theorem LetCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v s3 h3 e2 r,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (ELet e1 e2) s3 h3 r.
    t C1.LetCase C2.LetCase.
  Qed.

  Theorem LetExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (ELet e1 e2) s2 h2 (Core.Ex v).
    t C1.LetExCase C2.LetExCase.
  Qed.

  Theorem PairCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v1)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v1)
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v2)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v2)
      -> spec full self s1 h1 [<e1, e2>] s3 h3 (Core.Ans (Core.VPair v1 v2)).
    t C1.PairCase C2.PairCase.
  Qed.

  Theorem PairEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 [<e1, e2>] s2 h2 (Core.Ex v).
    t C1.PairEx1Case C2.PairEx1Case.
  Qed.

  Theorem PairEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v1)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v1)
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v2)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v2)
      -> spec full self s1 h1 [<e1, e2>] s3 h3 (Core.Ex v2).
    t C1.PairEx2Case C2.PairEx2Case.
  Qed.

  Theorem UnitCase : forall full, self [= full
    -> compilationOk full
    -> forall s h,
      spec full self s h () s h (Core.Ans Core.VUnit).
    t C1.UnitCase C2.UnitCase.
  Qed.

  Theorem FstCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v1 v2,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full self s1 h1 (Fst e) s2 h2 (Core.Ans v1).
    t C1.FstCase C2.FstCase.
  Qed.

  Theorem FstExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Fst e) s2 h2 (Core.Ex v).
    t C1.FstExCase C2.FstExCase.
  Qed.

  Theorem SndCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v1 v2,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full self s1 h1 (Snd e) s2 h2 (Core.Ans v2).
    t C1.SndCase C2.SndCase.
  Qed.

  Theorem SndExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Snd e) s2 h2 (Core.Ex v).
    t C1.SndExCase C2.SndExCase.
  Qed.

  Theorem InlCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Inl e) s2 h2 (Core.Ans (Core.VInl v)).
    t C1.InlCase C2.InlCase.
  Qed.

  Theorem InlExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Inl e) s2 h2 (Core.Ex v).
    t C1.InlExCase C2.InlExCase.
  Qed.

  Theorem InrCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Inr e) s2 h2 (Core.Ans (Core.VInr v)).
    t C1.InrCase C2.InrCase.
  Qed.

  Theorem InrExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Inr e) s2 h2 (Core.Ex v).
    t C1.InrExCase C2.InrExCase.
  Qed.

  Theorem CaseLCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VInl v))
      -> spec full full  s1 h1 e s2 h2 (Core.Ans (Core.VInl v))
      -> Core.eval s2 h2 (e1 v) s3 h3 r
      -> spec full full s2 h2 (e1 v) s3 h3 r
      -> spec full self s1 h1 (Core.ECase e e1 e2) s3 h3 r.
    t C1.CaseLCase C2.CaseLCase.
  Qed.

  Theorem CaseRCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VInr v))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VInr v))
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (Core.ECase e e1 e2) s3 h3 r.
    t C1.CaseRCase C2.CaseRCase.
  Qed.

  Theorem CaseExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Core.ECase e e1 e2) s2 h2 (Core.Ex v).
    t C1.CaseExCase C2.CaseExCase.
  Qed.

  Theorem NewCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Ref e) s2 (v :: h2) (Core.Ans (Core.VRef (length h2))).
    t C1.NewCase C2.NewCase.
  Qed.

  Theorem NewExCase : forall full, self [= full  
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Ref e) s2 h2 (Core.Ex v).
    t C1.NewExCase C2.NewExCase.
  Qed.

  Theorem ReadCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 r v,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VRef r))
      -> h2 # r = Some v
      -> spec full self s1 h1 (!e) s2 h2 (Core.Ans v).
    t C1.ReadCase C2.ReadCase.
  Qed.

  Theorem ReadExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (!e) s2 h2 (Core.Ex v).
    t C1.ReadExCase C2.ReadExCase.
  Qed.

  Theorem WriteCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v)
      -> spec full self s1 h1 (e1 ::= e2) s3 h3 ## r <~ v (Core.Ans Core.VUnit).
    t C1.WriteCase C2.WriteCase.
  Qed.

  Theorem WriteEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (e1 ::= e2) s2 h2 (Core.Ex v).
    t C1.WriteEx1Case C2.WriteEx1Case.
  Qed.

  Theorem WriteEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full self s1 h1 (e1 ::= e2) s3 h3 (Core.Ex v).
    t C1.WriteEx2Case C2.WriteEx2Case.
  Qed.

  Theorem ThrowCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Throw e1) s2 h2 (Core.Ex v).
    t C1.ThrowCase C2.ThrowCase.
  Qed.

  Theorem ThrowExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Throw e1) s2 h2 (Core.Ex v).
    t C1.ThrowExCase C2.ThrowExCase.
  Qed.

  Theorem CatchCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (ECatch e1 e2) s2 h2 (Core.Ans v).
    t C1.CatchCase C2.CatchCase.
  Qed.

  Theorem CatchExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2 s3 h3 r,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (ECatch e1 e2) s3 h3 r.
    t C1.CatchExCase C2.CatchExCase.
  Qed.
End Join.
