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

Set Implicit Arguments.

Section Core.
  Import Core.
  Open Local Scope core_scope.

  Definition Swap : Exp := fun _ =>
    \_,p, [< Snd #p, Fst #p >].

  Definition AppPair : Exp := fun _ =>
    \_,p, [< Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p) >].

  Definition SwapAppPairBody : Exp2 := fun _ _ p =>
    Swap _ @ (AppPair _ @ #p).

  Definition SwapAppPair : Exp := fun _ => Abs (@SwapAppPairBody _).
End Core.

Section CPS.
  Import CPS.
  Open Local Scope cps_scope.

  Definition CExp2 := forall var, var -> var -> exp var.

  Definition SwapAppPair'Body : CExp2 := fun _ F p =>
    p' <- Fst p;
    f <- Fst p';
    d <- Snd p';
    p'' <- Snd p;
    k <- Fst p'';
    ke <- Snd p'';

    k1 <- (\_,r1,
      k2 <- (\_,r2,
        pr <- [< r2, r1 >];
        k @@@ pr);
      pi <- [< k2, ke >];
      d2 <- Snd d;
      pi <- [< d2, pi >];
      f @@@ pi);
    pi <- [< k1, ke >];
    d1 <- Fst d;
    pi <- [< d1, pi >];
    f @@@ pi.

  Definition SwapAppPair' : Primop := fun _ => Abs (@SwapAppPair'Body _).
End CPS.



Definition comp := Compilation
  (fun G e1 k ke e2 =>
    exists F1, exists F2, exists x1, exists x2, exists kx, exists kex,
      G = (x1, x2) :: (F1, F2) :: nil
      /\ e1 = SwapAppPairBody F1 x1
      /\ e2 = SwapAppPair'Body F2 (VPair x2 (VPair kx kex))
      /\ k = (fun x => kx @@@ x)%cps
      /\ ke = (fun x => kex @@@ x)%cps)
  (fun G f1 f2 =>
    G = nil
    /\ f1 = @SwapAppPairBody _
    /\ f2 = @SwapAppPair'Body _)%cps.

Hint Resolve answer_Ans answer_Ex.

Import Core.

Lemma eq_nat_dec_same : forall n, eq_nat_dec n n = left _ (refl_equal _).
  intros; destruct (eq_nat_dec n n); simpler.
Qed.

Hint Rewrite eq_nat_dec_same : ltamer.

Ltac inv tac := match goal with
                  | _ => tac
                  | [ H : eval _ _ ?E _ _ _ |- _ ] =>
                    match eval hnf in E with
                      | (#_)%core => idtac
                      | (_ @ _)%core => idtac
                      | Abs _ => idtac
                      | [< _, _ >]%core => idtac
                      | (Fst _)%core => idtac
                      | (Snd _)%core => idtac
                      | _ => fail 1
                    end; inverter H
                end; simpler.

Lemma func_same : forall s3 l0 f f0 s v0 h4 v1 h0,
  s3 # l0 = Some f
  -> eval ((fun _ p => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
    :: s) h0 (f0 (VFunc l0) v1) s3 h4 (Ans v0)
  -> (if eq_nat_dec l0 (length s)
    then
      Some
      (fun _ p : val => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
    else s # l0) = Some f0
  -> Some f0 = Some f.
  intros until h0; intros H1 H2 H3;
    rewrite <- H1; rewrite <- H3;
      destruct (eq_nat_dec l0 (length s)); simpler; [
        repeat inv fail | rewrite H3 ]; symmetry; eauto.
Qed.

Hint Constructors eval.

Hint Extern 1 (eval _ _ (AppPair _) _ _ _) => unfold AppPair.

Lemma support1_AppPair : forall s h l0 v1 v6,
  support1 s h (AppPair val @ #VPair (VFunc l0) (VPair v1 v6))
  ((fun _ p : val => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>]) :: s)
  h ((fun _ p : val => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>]) (VFunc (length s))
    (VPair (VFunc l0) (VPair v1 v6))).
  eauto.
Qed.

Hint Resolve support1_AppPair.

Hint Extern 1 (support1 _ _ _ _ _ _) => eapply SupPair2; eauto.

Lemma eval_AppPair : forall s h p s' h' r,
  eval s h (AppPair _ @ #p) s' h' r
  -> exists l, exists v1, exists v2, exists f,
    p = VPair (VFunc l) (VPair v1 v2)
    /\ ((fun _ p => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
      :: s) # l = Some f
    /\ exists s1, exists h1, exists r1,
      eval ((fun _ p => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
        :: s) h (f (VFunc l) v1) s1 h1 r1
      /\ support s h (AppPair _ @ #p)
      ((fun _ p => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
        :: s) h (f (VFunc l) v1)
      /\ match r1 with
           | Ex r1 => r = Ex r1 /\ s1 = s' /\ h1 = h'
           | Ans r1 =>
             exists r2,
               eval s1 h1 (f (VFunc l) v2) s' h' r2
               /\ support s h (AppPair _ @ #p) s1 h1 (f (VFunc l) v2)
               /\ match r2 with
                    | Ex r2 => r = Ex r2
                    | Ans r2 => r = Ans (VPair r1 r2)
                  end
         end.
  intros; do 4 inv fail;
    abstract (repeat inv fail;
      try match goal with
            | [ f0 : _, f : _ |- _ ] =>
              assert (Some f0 = Some f); [ eapply func_same; eassumption | simpler ]
          end;
      splitter; eauto 8; simpl; splitter; eauto 8; simpl; trivial).
Qed.

Lemma eval_Swap : forall s h p s' h' r,
  eval s h (Swap _ @ #p) s' h' r
  -> exists v1, exists v2,
    p = VPair v1 v2
    /\ r = Ans (VPair v2 v1).
  intros; repeat inv fail; eauto.
Qed.

Ltac invLemmas := idtac;
  match goal with
    | [ H : eval _ _ (Swap _ @ #_) _ _ _ |- _ ] => generalize (eval_Swap H); clear H
    | [ H : eval _ _ (AppPair _ @ #_) _ _ _ |- _ ] => generalize (eval_AppPair H); clear H
  end.

Hint Extern 1 (eval _ _ (Swap _) _ _ _) => unfold Swap.
Hint Extern 1 (support _ _ (SwapAppPairBody _ _) _ _ _) => unfold SwapAppPairBody.

Lemma eval_SwapAppPairBody : forall s h F p s' h' r,
  eval s h (SwapAppPairBody F p) s' h' r
  -> exists l, exists v1, exists v2, exists f,
    p = VPair (VFunc l) (VPair v1 v2)
    /\ ((fun _ p => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
      :: (fun _ p => [<Snd #p, Fst #p>]) :: s) # l = Some f
    /\ exists s1, exists h1, exists r1,
      eval ((fun _ p => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
        :: (fun _ p => [<Snd #p, Fst #p>]) :: s) h (f (VFunc l) v1) s1 h1 r1
      /\ support s h (SwapAppPairBody F p)
      ((fun _ p => [<Fst #p @ Fst (Snd #p), Fst #p @ Snd (Snd #p)>])
        :: (fun _ p => [<Snd #p, Fst #p>])
        :: s) h (f (VFunc l) v1)
      /\ match r1 with
           | Ex r1 => r = Ex r1 /\ s1 = s' /\ h1 = h'
           | Ans r1 =>
             exists r2,
               eval s1 h1 (f (VFunc l) v2) s' h' r2
               /\ support s h (SwapAppPairBody F p) s1 h1 (f (VFunc l) v2)
               /\ match r2 with
                    | Ex r2 => r = Ex r2
                    | Ans r2 => r = Ans (VPair r2 r1)
                  end
         end.
  intros; inv invLemmas;
    abstract (repeat inv invLemmas;
      repeat (match goal with
                | [ _ : match ?E with Ans _ => _ | Ex _ => _ end |- _ ] => destruct E
              end; simpler);
      splitter; eauto; simpl; splitter; eauto; simpl;
        match goal with
          | [ H : Ans _ = Ans _ |- _ ] => injection H; intros; subst
        end; trivial).
Qed.

Lemma func_eq : forall x5 s1 o1 o2 (x8 f1 : val -> val -> exp val),
  (if eq_nat_dec x5 (S (length s1))
    then
      o1
    else
      if eq_nat_dec x5 (length s1)
        then o2
        else s1 # x5) = Some x8
  -> s1 # x5 = Some f1
  -> x8 = f1.
  intros until f1; intros H1 H2;
    generalize (grab_oob' _ _ H2).
  intro.
  repeat (match goal with
            | [ _ : context[eq_nat_dec ?A ?B] |- _ ] =>
              destruct (eq_nat_dec A B)
          end; simpler).
Qed.

Implicit Arguments func_eq [x5 s1 o1 o2 x8 f1].

Lemma push : forall full G s1 s2 x6 x5 x1 f1 l2 f2 s1' s2' v1 v2,
  In (v1, v2) ((x6, x1) :: (VFunc x5, VCont l2) :: G)
  -> (forall (x1 : val) (x2 : CPS.val),
    In (x1, x2) G -> full &| s1 & s2 |-- x1 ~~ x2)
  -> full &| s1 & s2 |-- x6 ~~ x1
  -> s1 # x5 = Some f1
  -> s2 # l2 = Some f2
  -> compFunc full G f1 f2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> full &| s1' & s2' |-- v1 ~~ v2.
  simpler; eauto.
Qed.
