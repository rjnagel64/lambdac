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
Require Import CPS.
Require Import Result.

Require Import CPSify.
Require Import Link.

Require Import CPSifySpec.
Require Import CPSifySpecS.

Require Import SwapPre.

Set Implicit Arguments.

Module Self : COMPILATION with Definition self := comp.
  Definition self := comp.

  Lemma selfOk : compilationOk self.
    red; simpler; eauto 13 with cps_eval.
  Qed.

  Import Core.

  Hint Extern 1 (CPS.eval _ _ (SwapAppPair'Body _ _) _) => unfold SwapAppPair'Body.

  Lemma push1 : forall full G s1 s2 x6 x5 x1 f1 l2 f2 v1 v2 F1 F2 F,
    In (v1, v2) ((x6, x1) :: (VFunc x5, VCont l2) :: G)
    -> (forall (x1 : val) (x2 : CPS.val),
      In (x1, x2) G -> full &| s1 & s2 |-- x1 ~~ x2)
    -> full &| s1 & s2 |-- x6 ~~ x1
      -> s1 # x5 = Some f1
      -> s2 # l2 = Some f2
      -> compFunc full G f1 f2
      -> full &| F1 :: F2 :: s1 & F :: s2 |-- v1 ~~ v2.
    intros; eapply SwapPre.push; eauto.
  Qed.

  Lemma push2 : forall full G s1 s2 x6 x5 x1 f1 l2 f2 s1' s2' v1 v2 F1 F2 h e h' r F,
    In (v1, v2) ((x6, x1) :: (VFunc x5, VCont l2) :: G)
    -> (forall (x1 : val) (x2 : CPS.val),
      In (x1, x2) G -> full &| s1 & s2 |-- x1 ~~ x2)
    -> full &| s1 & s2 |-- x6 ~~ x1
      -> s1 # x5 = Some f1
      -> s2 # l2 = Some f2
      -> compFunc full G f1 f2
      -> eval (F1 :: F2 :: s1) h e s1' h' r
      -> F :: s2 ~> s2'
      -> full &| s1' & s2' |-- v1 ~~ v2.
    intros; eapply push; eauto.
  Qed.

  Hint Immediate push1.
  Hint Extern 1 (_ &| _ & _ |-- _ ~~ _) => eapply push2; eassumption.

  Theorem Cases : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s1' h1' r,
      Core.eval s1 h1 e1 s1' h1' r
      -> (forall s1'' h1'' e1', support s1 h1 e1 s1'' h1'' e1'
        -> forall s1''' h1''' r',
          Core.eval s1'' h1'' e1' s1''' h1''' r'
          -> spec full full s1'' h1'' e1' s1''' h1''' r')
      -> spec full self s1 h1 e1 s1' h1' r.
    unfold self, spec; intros until r; intro Hev; simpler;
      generalize (eval_SwapAppPairBody Hev); simpler;
        repeat (match goal with
                  | [ _ : match ?E with Ans _ => _ | Ex _ => _ end |- _ ] => destruct E
                end; simpler).

    abstract (match goal with
                | [ H : _ |- _ ] => generalize (H _ _ (or_introl _ (refl_equal _))); intro
              end;
    repeat match goal with
             | [ H : _ &| _ & _ |-- _ ~~ _ |- _ ] => invert_1 H; subst
           end;
    match goal with
      | [ H1 : _, H2 : _ |- _ ] => rewrite (func_eq H1 H2) in *; clear H1
    end;
    match goal with
      | [ H : compilationOk _, H' : _ |- _ ] => guessKeep (H _ _ _ H'); simpler
    end;
    match goal with
      | [ IH : forall s1'' h1'' e1', support _ _ _ _ _ _ -> _, H : support _ _ _ (_ :: _ :: _) _ _ |- _ ] =>
        generalize (IH _ _ _ H); clear H; intro Hf
    end;
    match goal with
      | [ _ : _ &| _ & ?s2 |-- _ ~~~ ?h2 |- _ ] =>
        evar (F : CPS.val -> CPS.val -> CPS.exp CPS.val);
        guessWith (F :: s2, h2) Hf;
        unfold F in *; clear F; simpler
    end;
    match goal with
      | [ H : _ &| _ & _ |--- _ ~~ _ |- _ ] => invert_1 H; subst; simpl in *
    end;
    match goal with
      | [ H : compilationOk _, H' : _ |- _ ] => guessKeep (H _ _ _ H'); clear H; simpler
    end;
    match goal with
      | [ IH : forall s1'' h1'' e1', support _ _ _ _ _ _ -> _, x : _ |- _ ] =>
        match goal with
          | [ H : support _ _ _ x _ _ |- _ ] =>
            generalize (IH _ _ _ H); clear IH H; intro Hf1
        end
    end;
    match goal with
      | [ _ : _ &| _ & ?s |-- _ ~~~ ?h, _ : _ ~> ?s |- _ ] =>
        evar (F : CPS.val -> CPS.val -> CPS.exp CPS.val);
        guessWith (F :: s, h) Hf1;
        unfold F in *; clear F;
          destruct Hf1 as [? [? [? [? [? [? ?]]]]]]
    end;
    match goal with
      | [ H : _ &| _ & _ |--- _ ~~ _ |- _ ] => invert_1 H; subst; simpl in *
    end;
    splitter; eauto 10 with cps_eval).

    Focus 2.

    abstract (match goal with
                | [ H : _ |- _ ] => generalize (H _ _ (or_introl _ (refl_equal _))); intro
              end;
    repeat match goal with
             | [ H : _ &| _ & _ |-- _ ~~ _ |- _ ] => invert_1 H; subst
           end;
    match goal with
      | [ H1 : _, H2 : _ |- _ ] => rewrite (func_eq H1 H2) in *; clear H1
    end;
    match goal with
      | [ H : compilationOk _, H' : _ |- _ ] => guessKeep (H _ _ _ H'); simpler
    end;
    match goal with
      | [ IH : forall s1'' h1'' e1', support _ _ _ _ _ _ -> _, H : support _ _ _ (_ :: _ :: _) _ _ |- _ ] =>
        generalize (IH _ _ _ H); clear H; intro Hf
    end;
    match goal with
      | [ _ : _ &| _ & ?s2 |-- _ ~~~ ?h2 |- _ ] =>
        evar (F : CPS.val -> CPS.val -> CPS.exp CPS.val);
        guessWith (F :: s2, h2) Hf;
        unfold F in *; clear F; simpler
    end;
    match goal with
      | [ H : _ &| _ & _ |--- _ ~~ _ |- _ ] => invert_1 H; subst; simpl in *
    end;
    splitter; eauto 10 with cps_eval).

    abstract (match goal with
                | [ H : _ |- _ ] => generalize (H _ _ (or_introl _ (refl_equal _))); intro
              end;
    repeat match goal with
             | [ H : _ &| _ & _ |-- _ ~~ _ |- _ ] => invert_1 H; subst
           end;
    match goal with
      | [ H1 : _, H2 : _ |- _ ] => rewrite (func_eq H1 H2) in *; clear H1
    end;
    match goal with
      | [ H : compilationOk _, H' : _ |- _ ] => guessKeep (H _ _ _ H'); simpler
    end;
    match goal with
      | [ IH : forall s1'' h1'' e1', support _ _ _ _ _ _ -> _, H : support _ _ _ (_ :: _ :: _) _ _ |- _ ] =>
        generalize (IH _ _ _ H); clear H; intro Hf
    end;
    match goal with
      | [ _ : _ &| _ & ?s2 |-- _ ~~~ ?h2 |- _ ] =>
        evar (F : CPS.val -> CPS.val -> CPS.exp CPS.val);
        guessWith (F :: s2, h2) Hf;
        unfold F in *; clear F; simpler
    end;
    match goal with
      | [ H : _ &| _ & _ |--- _ ~~ _ |- _ ] => invert_1 H; subst; simpl in *
    end;
    match goal with
      | [ H : compilationOk _, H' : _ |- _ ] => guessKeep (H _ _ _ H'); clear H; simpler
    end;
    match goal with
      | [ IH : forall s1'' h1'' e1', support _ _ _ _ _ _ -> _, x : _ |- _ ] =>
        match goal with
          | [ H : support _ _ _ x _ _ |- _ ] =>
            generalize (IH _ _ _ H); clear IH H; intro Hf1
        end
    end;
    match goal with
      | [ _ : _ &| _ & ?s |-- _ ~~~ ?h, _ : _ ~> ?s |- _ ] =>
        evar (F : CPS.val -> CPS.val -> CPS.exp CPS.val);
        guessWith (F :: s, h) Hf1;
        unfold F in *; clear F;
          destruct Hf1 as [? [? [? [? [? [? ?]]]]]]
    end;
    match goal with
      | [ H : _ &| _ & _ |--- _ ~~ _ |- _ ] => invert_1 H; subst; simpl in *
    end;
    splitter; eauto 10 with cps_eval).
  Qed.
End Self.
