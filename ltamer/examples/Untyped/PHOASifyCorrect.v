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

Require Import Arith.

Require Import LambdaTamer.LambdaTamer.

Require Import Core.
Require Import Source.

Require Import PHOASify.

Set Implicit Arguments.


Fixpoint isSource n (e : Source.exp n) {struct e} : Prop :=
  match e with
    | Var _ _ => True

    | App _ e1 e2 => isSource e1 /\ isSource e2
    | Abs _ e1 => isSource e1

    | ELet _ e1 e2 => isSource e1 /\ isSource e2

    | Unit _ => True

    | Pair _ e1 e2 => isSource e1 /\ isSource e2
    | EFst _ e1 => isSource e1
    | ESnd _ e1 => isSource e1

    | EInl _ e1 => isSource e1
    | EInr _ e1 => isSource e1
    | ECase _ e1 e2 e3 => isSource e1 /\ isSource e2 /\ isSource e3

    | New _ e1 => isSource e1
    | Read _ e1 => isSource e1
    | Write _ e1 e2 => isSource e1 /\ isSource e2

    | EThrow _ e1 => isSource e1
    | ECatch _ e1 e2 => isSource e1 /\ isSource e2

    | Const _ _ => True
    | Eq _ e1 e2 => isSource e1 /\ isSource e2

    | Value _ _ => False
  end.

Fixpoint same (s : Core.closures) n (e1 : Source.exp n) (e2 : Core.exp Core.val) {struct e1} : ilist Core.val n -> Prop :=
  match e1 in Source.exp n, e2 return ilist Core.val n -> Prop with
    | Var _ f, #v => fun il => iget il f = v

    | App _ e1 e2, e1' @ e2' => fun il => same s e1 e1' il /\ same s e2 e2' il
    | Abs _ e1, Core.Abs e1' => fun il => forall F x, same s e1 (e1' F x) (F ::: x ::: il)

    | ELet _ e1 e2, Core.ELet e1' e2' => fun il => same s e1 e1' il /\ forall x, same s e2 (e2' x) (x ::: il)

    | Unit _, () => fun _ => True

    | Pair _ e1 e2, [<e1', e2'>] => fun il => same s e1 e1' il /\ same s e2 e2' il
    | EFst _ e1, Fst e1' => fun il => same s e1 e1' il
    | ESnd _ e1, Snd e1' => fun il => same s e1 e1' il

    | EInl _ e1, Inl e1' => fun il => same s e1 e1' il
    | EInr _ e1, Inr e1' => fun il => same s e1 e1' il
    | ECase _ e1 e2 e3, Core.ECase e1' e2' e3' => fun il => same s e1 e1' il
      /\ (forall x, same s e2 (e2' x) (x ::: il))
      /\ (forall x, same s e3 (e3' x) (x ::: il))

    | New _ e1, Ref e1' => fun il => same s e1 e1' il
    | Read _ e1, !e1' => fun il => same s e1 e1' il
    | Write _ e1 e2, e1' ::= e2' => fun il => same s e1 e1' il /\ same s e2 e2' il

    | EThrow _ e1, Throw e1' => fun il => same s e1 e1' il
    | ECatch _ e1 e2, Core.ECatch e1' e2' => fun il => same s e1 e1' il
      /\ (forall x, same s e2 (e2' x) (x ::: il))

    | Value _ v1, #v2 => fun il => cr s v1 v2

    | Const _ b1, ^^b2 => fun _ => b1 = b2
    | Eq _ e1 e2, e1' == e2' => fun il => same s e1 e1' il /\ same s e2 e2' il

    | _, _ => fun _ => False
  end

with cr (s : Core.closures) (v1 : Source.val) (v2 : Core.val) {struct v1} : Prop :=
  match v1, v2 with
    | Source.VFunc e1, Core.VFunc l =>
      match s # l with
        | None => False
        | Some e2 => forall F x s', s ~> s' -> same s' e1 (e2 F x) (F ::: x ::: INil)
      end

    | Source.VUnit, Core.VUnit => True
    | Source.VPair v1 v2, Core.VPair v1' v2' => cr s v1 v1' /\ cr s v2 v2'
    | Source.VInl v1, Core.VInl v1' => cr s v1 v1'
    | Source.VInr v1, Core.VInr v1' => cr s v1 v1'
    | Source.VRef l, Core.VRef l' => l = l'
    | Source.VBase b, Core.VBase b' => b = b'

    | _, _ => False
  end.

Theorem cr_monotone : forall s s',
  s ~> s'
  -> forall v1 v2, cr s v1 v2
    -> cr s' v1 v2.
  induction v1; destruct v2; simpler;
    match goal with
      | [ l : label, H : _ ~> _ |- _ ] =>
        case_eq (s # l); [ intros ? Heq | intros Heq ]; rewrite Heq in *; simpler;
          rewrite (grab_extends l H Heq); eauto
    end.
Qed.

Hint Resolve cr_monotone.

Theorem same_monotone : forall s s',
  s ~> s'
  -> forall n (e1 : Source.exp n) e2 il, same s e1 e2 il
    -> same s' e1 e2 il.
  induction e1; intro e0; destruct e0; simpler; eauto.
Qed.

Hint Resolve same_monotone.

Definition crR s r1 r2 :=
  match r1, r2 with
    | Source.Ans v1, Core.Ans v2 => cr s v1 v2
    | Source.Ex v1, Core.Ex v2 => cr s v1 v2
    | _, _ => False
  end.

Lemma phoasify_same : forall n (e : Source.exp n) il,
  isSource e
  -> same nil e (phoasify e il) il.
  induction e; simpler.
Qed.

Definition refOk s h1 h2 rf :=
  forall v1, h1 # rf = Some v1
    -> exists v2, h2 # rf = Some v2
      /\ cr s v1 v2.

Definition cut_not_zero A n (f : fin n) : ilist A (S (pred n)) -> ilist A n :=
  match f in fin n return ilist A (S (pred n)) -> ilist A n with
    | FO _ => fun e => e
    | FS _ _ => fun e => e
  end.

Fixpoint cut A n (f : fin n) {struct f} : ilist A n -> ilist A (pred n) :=
  match f in fin n return ilist A n -> ilist A (pred n) with
    | FO _ => fun il => itail il
    | FS _ f' => fun il => cut_not_zero f' (ihead il ::: cut f' (itail il))
  end.

Lemma recutO : forall n s (e1 : exp (S (S n))) v1 e2 il x,
  same s (subst' e1 v1 (FS FO)) e2 (cut (FS FO) (x ::: il))
  -> same s (subst' e1 v1 (FS FO)) e2 (x ::: itail il).
  simpler.
Qed.

Lemma recutOA : forall n s (e1 : exp (S (S (S n)))) v1 e2 il F x,
  same s (subst' e1 v1 (FS (FS FO))) e2 (cut (FS (FS FO)) (F ::: x ::: il))
  -> same s (subst' e1 v1 (FS (FS FO))) e2 (F ::: x ::: itail il).
  simpler.
Qed.

Lemma recutS : forall n s (e1 : exp (S (S n))) v1 e2 il x f,
  same s (subst' e1 v1 (FS (FS f))) e2 (cut (FS (FS f)) (x ::: il))
  -> same s (subst' e1 v1 (FS (FS f))) e2 (x ::: cut_not_zero f (ihead il ::: cut f (itail il))).
  simpler.
Qed.

Lemma recutSA : forall n s (e1 : exp (S (S (S n)))) v1 e2 il F x f,
  same s (subst' e1 v1 (FS (FS (FS f)))) e2 (cut (FS (FS (FS f))) (F ::: x ::: il))
  -> same s (subst' e1 v1 (FS (FS (FS f)))) e2 (F ::: x ::: cut_not_zero f (ihead il ::: cut f (itail il))).
  simpler.
Qed.

Hint Extern 1 (same _ (subst' (n := S (S ?n)) _ _ _) _ _) => apply (@recutO n) || apply (@recutS n).
Hint Extern 1 (same _ (subst' (n := S (S (S ?n))) _ _ _) _ _) => apply (@recutOA n) || apply (@recutSA n).

Ltac destructer :=
  intros; repeat match goal with
                   | [ f : fin (S _) |- _ ] => dep_destruct f
                   | [ il : ilist _ (S _) |- _ ] => dep_destruct il
                  end; simpler.

Lemma iget_ihead : forall n (il : ilist Core.val (S (S n))),
  ihead il = iget il FO.
  destructer.
Qed.

Lemma iget_itail : forall n (v : fin n) (il : ilist Core.val _),
  iget (itail il) v = iget il (FS v).
  destructer.
Qed.

Lemma iget_itail_itail : forall n (v : fin n) (il : ilist Core.val _),
  iget (itail (itail il)) v = iget il (FS (FS v)).
  destructer.
Qed.

Hint Immediate iget_ihead iget_itail iget_itail_itail.

Lemma substVar_self : forall n (f : fin n),
  substVar f f = None.
  induction f; equation.
Qed.

Hint Rewrite substVar_self : ltamer.

Lemma substVar_correct : forall n (f0 f : fin n),
  (f0 = f /\ substVar f0 f = None)
  \/ exists f', substVar f0 f = Some f'
    /\ forall il : ilist Core.val _, iget (cut f0 il) f' = iget il f.
  induction f0; destructer; eauto;
    match goal with
      | [ IHf : forall f : fin ?n, (?f0 = f /\ _) \/ _, f : fin ?n |- _ ] =>
        match f with
          | f0 => fail 1
          | _ => destruct (IHf f); clear IHf; simpler; right;
            match goal with
              | [ f' : fin _ |- _ ] => exists (not_zero' f (FS x)); equation
            end
        end
      | _ => right; splitter; eauto
    end;
  try match goal with
        | [ |- context[match ?v with FO _ => _ | FS _ _ => _ end] ] => destruct v; simpler
      end;
  intros; repeat (match goal with
                    | [ f : fin (S _) |- _ ] => dep_destruct f
                    | [ il : ilist _ (S _) |- _ ] => dep_destruct il
                    | [ |- context[cut_not_zero ?f _] ] => destruct f; simpler
                  end; simpler).
Qed.

Lemma same_subst' : forall s v1 n (e1 : exp n) f il e2,
  same s e1 e2 il
  -> cr s v1 (iget il f)
  -> same s (subst' e1 v1 f) e2 (cut f il).
  induction e1; intros ? ? e0; destruct e0; simpler;
    match goal with
      | [ |- context[not_zero ?f _] ] => destruct f; simpler
      | [ |- context[not_zeroA ?f _] ] => destruct f; simpler
      | [ |- context[substVar ?f1 ?f2] ] => destruct (substVar_correct f1 f2); equation
    end.
Qed.

Lemma same_subst : forall s e1 e2 v1 v2,
  same s e1 e2 (v2 ::: INil)
  -> cr s v1 v2
  -> same s (subst e1 v1) e2 INil.
  unfold subst; intros.
    replace (@INil Core.val) with (cut FO (v2 ::: INil)); auto;
      apply (@same_subst' s v1 1); auto.
Qed.

Lemma same_substA : forall s e1 e2 F1 F2 v1 v2,
  same s e1 e2 (F2 ::: v2 ::: INil)
  -> cr s F1 F2
  -> cr s v1 v2
  -> same s (subst (subst e1 F1) v1) e2 INil.
  unfold subst; intros.
    replace (@INil Core.val) with (cut FO (cut FO (F2 ::: v2 ::: INil))); auto;
      apply (@same_subst' s v1 1); auto; apply (@same_subst' s F1 2); auto.
Qed.

Hint Resolve same_subst.

Theorem refOk_monotone : forall s s' h1 h2 rf,
  refOk s h1 h2 rf
  -> s ~> s'
  -> refOk s' h1 h2 rf.
  unfold refOk; intros until rf; intros H1 ? ? H2;
    rewrite H2 in H1; destruct (H1 _ (refl_equal _)) as [? [? ?]]; eauto.
Qed.

Hint Resolve refOk_monotone.

Lemma same_Abs : forall s (e1 : exp 1) e2 x il,
  same s e1 e2 (x ::: il)
  -> same s e1 e2 (x ::: INil).
  intros; dep_destruct il; trivial.
Qed.

Lemma same_AbsA : forall s (e1 : exp 2) e2 F x il,
  same s e1 e2 (F ::: x ::: il)
  -> same s e1 e2 (F ::: x ::: INil).
  intros; dep_destruct il; trivial.
Qed.

Hint Resolve same_Abs same_AbsA.

Lemma refOk_push : forall s h1 h2 v1 v2,
  (forall rf, refOk s h1 h2 rf)
  -> cr s v1 v2
  -> length h1 = length h2
  -> (forall rf, refOk s (v1 :: h1) (v2 :: h2) rf).
  unfold refOk; simpler_expensive; eauto.
Qed.

Lemma length_write : forall (h : list val) l rf v v',
  (h ## l <~ v) # rf = Some v'
  -> rf < length h.
  intros; replace (length h) with (length (h ## l <~ v)); eauto; simpler.
Qed.

Hint Immediate length_write.

Lemma refOk_write : forall s h1 h2 v1 v2 l,
  (forall rf, refOk s h1 h2 rf)
  -> cr s v1 v2
  -> length h1 = length h2
  -> (forall rf, refOk s (h1 ## l <~ v1) (h2 ## l <~ v2) rf).
  unfold refOk; simpler_expensive.
    match goal with
      | [ H : (?h ## ?l <~ ?v) # ?rf = Some _ |- _ ] =>
        let H' := fresh "H'" in
          assert (H' : rf < length h); [ eauto
            | destruct (upd_choices l v H'); simpler; eauto ]
    end.
Qed.

Hint Immediate refOk_push refOk_write.

Lemma length_eq_write : forall A B (h1 : list A) (h2 : list B) l v,
  length h1 = length h2
  -> length h1 = length (h2 ## l <~ v).
  simpler.
Qed.

Hint Immediate length_eq_write.

Lemma cr_VFunc : forall s e1 l e2,
  s # l = Some e2
  -> (forall F x s', s ~> s' -> same s' e1 (e2 F x) (F ::: x ::: INil))
  -> cr s (Source.VFunc e1) (Core.VFunc l).
  equation.
Qed.

Hint Resolve cr_VFunc.

Theorem phoasify_follow : forall h1 e1 h1' v,
  Source.eval h1 e1 h1' v
  -> forall s e2 h2 il,
    same s e1 e2 il
    -> (forall rf, refOk s h1 h2 rf)
    -> length h1 = length h2
    -> exists s', exists h2', exists v',
      Core.eval s h2 e2 s' h2' v'
      /\ s ~> s'
      /\ crR s' v v'
      /\ (forall rf, refOk s' h1' h2' rf)
      /\ length h1' = length h2'.
  Hint Constructors Core.eval.

  Hint Extern 1 (Core.eval ?s ?h (Ref ?e) _ ?h' _) =>
    match goal with
      | [ _ : Core.eval s h e _ ?h'' _, _ : cr _ _ ?v |- _ ] =>
        equate h' (v :: h'')
    end.

  Hint Extern 1 (Core.eval _ _ (_ ::= ?e) _ ?h' _) =>
    match goal with
      | [ _ : Core.eval _ _ _ _ _ (Core.Ans (Core.VRef ?l)),
        H : Core.eval _ _ ?e _ ?h (Core.Ans ?v) |- _ ] =>
      equate h' (h ## l <~ v)
    end.

  Hint Extern 0 (same _ (subst (subst _ _) _) _ _) => eapply same_substA; eauto.

  induction 1; abstract (intros s e0; destruct e0; abstract (simpler;
    repeat (match goal with
              | [ _ : match ?x with Core.Ans _ => _ | Core.Ex _ => _ end |- _ ] => destruct x
              | [ _ : match ?x with
                        | Core.VFunc _ => _
                        | Core.VUnit => _
                        | Core.VPair _ _ => _
                        | Core.VInl _ => _
                        | Core.VInr _ => _
                        | Core.VRef _ => _
                        | Core.VBase _ => _
                      end |- _ ] => destruct x
              | [ H : match ?x # ?l with Some _ => _ | None => _ end |- _ ] =>
                let Heq := fresh "Heq" in
                  case_eq (x # l); [ intros ? Heq | intros Heq ]; rewrite Heq in H
              | [ H1 : forall rf : label, refOk _ _ _ rf, H2 : _ # _ = Some _ |- _ ] =>
                destruct (H1 _ _ H2) as [? [? ?]]; clear H2
              | [ s : closures, H : eval ?h2 ?e _ _, IHeval : forall (s : closures) e2 h3 il, same _ ?e _ _ -> _ |- _ ] =>
                match goal with
                  | [ _ : eval _ _ h2 _ |- _ ] => fail 1
                  | _ =>
                    let rec chaseClosures s :=
                      match goal with
                        | [ _ : s ~> ?s' |- _ ] => chaseClosures s'
                        | _ => s
                      end in
                      let s' := chaseClosures s in
                        guessWith s' IHeval; clear H
                end
            end; simpler); splitter;
    (concretize; simpl;
      try match goal with
            | [ |- context[eq_nat_dec ?X ?X] ] => destruct (eq_nat_dec X X); intuition
          end; eauto))).
Qed.

Theorem refOk_nil : forall rf : label, refOk nil nil nil rf.
  red; simpler.
Qed.

Hint Resolve refOk_nil.

Theorem phoasify_correct : forall e h1' r,
  Source.eval nil e h1' r
  -> isSource e
  -> exists s', exists h2', exists r',
      Core.eval nil nil (phoasify e INil) s' h2' r'
      /\ crR s' r r'.
  Hint Resolve phoasify_same.

  intros; guessKeep phoasify_follow; simpler; eauto.
Qed.

Inductive comp : Source.val -> Core.val -> Prop :=
| CompArrow : forall l v,
  comp (Source.VFunc l) v

| CompUnit : comp Source.VUnit Core.VUnit

| CompPair : forall x1 x2 y1 y2,
  comp x1 x2
  -> comp y1 y2
  -> comp (Source.VPair x1 y1) (Core.VPair x2 y2)

| CompInl : forall v1 v2,
  comp v1 v2
  -> comp (Source.VInl v1) (Core.VInl v2)
| CompInr : forall v1 v2,
  comp v1 v2
  -> comp (Source.VInr v1) (Core.VInr v2)

| CompRef : forall l v,
  comp (Source.VRef l) v

| CompBase : forall b,
  comp (Source.VBase b) (Core.VBase b).

Inductive compR : Source.result -> Core.result -> Prop :=
| CompAns : forall v1 v2,
  comp v1 v2
  -> compR (Source.Ans v1) (Core.Ans v2)
| CompEx : forall v1 v2,
  comp v1 v2
  -> compR (Source.Ex v1) (Core.Ex v2).

Hint Constructors comp compR.

Lemma comp_in : forall s v1 v2,
  cr s v1 v2
  -> comp v1 v2.
  induction v1; destruct v2; simpler; eauto.
Qed.

Hint Resolve comp_in.

Lemma compR_in : forall s r1 r2,
  crR s r1 r2
  -> compR r1 r2.
  destruct r1; destruct r2; simpler; eauto.
Qed.

Hint Resolve compR_in.

Theorem Phoasify_correct : forall e h1' r,
  Source.eval nil e h1' r
  -> isSource e
  -> exists s', exists h2', exists r',
      Core.Eval nil nil (Phoasify e) s' h2' r'
      /\ compR r r'.
  unfold Core.Eval, Phoasify; intros; guessKeep phoasify_correct; simpler; eauto 6.
Qed.
