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

Require Import CPSify.
Require Import CPSifyTail.
Require Import CPSifySpec.

Require Import CPSifyCorrect.
Require Import CPSifyTailCorrect.

Require Import Ident.

Open Local Scope cps_scope.

Set Implicit Arguments.


Module Both := Join(CPSifyCorrect.Self)(CPSifyTailCorrect.Self).
Module C := Close(Both).


Definition Exp1 := forall var, var -> Core.exp var.
Definition Exp2 := forall var, var -> var -> Core.exp var.

Definition Exp1_wf (E : Exp1) := forall var1 var2 (x1 : var1) (x2 : var2),
  Core.exp_equiv ((x1, x2) :: nil) (E _ x1) (E _ x2).
Definition Exp2_wf (E : Exp2) := forall var1 var2 (F1 : var1) (F2 : var2) (x1 : var1) (x2 : var2),
  Core.exp_equiv ((x1, x2) :: (F1, F2) :: nil) (E _ F1 x1) (E _ F2 x2).

Lemma easy_env : forall comp s1 s2 x1 x2,
  In (x1, x2) nil
  -> comp &| s1 & s2 |-- x1 ~~ x2.
  simpler.
Qed.

Hint Resolve easy_env.

Hint Extern 1 (_ = Some _) => progress simpl.

Hint Extern 1 (compExp _ _ _ _ _ _) => progress simpl.
Hint Extern 1 (compFunc _ _ _ _) => progress simpl.

Hint Extern 1 (_ &| _ & _ |-- VFunc _ ~~ VCont _) => econstructor; eauto.

Ltac linker sym :=
  unfold Core.Eval, CPS.Eval, Exp1_wf; intros; repeat evalOne;
    repeat match goal with
             | [ H : Core.eval _ _ _ _ _ _ |- _ ] =>
               invert_1_2 H; subst; try match goal with
                                          | [ H : _ |- _ ] => solve [ inversion H ]
                                        end; []
           end;
    eapply sym; intros;
      (simpl in *; intuition;
        match goal with
          | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst
        end; econstructor; eauto) || eauto 9.

Theorem linkOneFunc : forall (F : Exp2) (E : Exp1) s h r,
  Core.Eval nil nil (fun _ => ELet (Core.Abs (F _)) (E _)) s h r
  -> Exp2_wf F
  -> Exp1_wf E
  -> CPS.Eval nil nil (fun _ =>
    f <- Abs (CPSify.cpsFunc (F _));
    CPSifyTail.cpsExp (E _ f) (CFunc (fun _ => Halt)) (CFunc (fun _ => Uncaught)))
  (cpsResult r).
  linker C.correctOpen.
Qed.


Module Ffi := Join(CPSifyCorrect.Self)(Ident.Self).
Module CFfi := Close(Ffi).

Theorem linkFfiIdent : forall (E : Exp1) s h r,
  Core.Eval nil nil (fun _ => ELet (\F, x, #x)%core (E _)) s h r
  -> Exp1_wf E
  -> CPS.Eval nil nil (fun _ =>
    f <- (\F, p, x <- Fst p; p' <- Snd p; k <- Fst p'; k @@@ x);
    CPSify.cpsExp (E _ f) (fun _ => Halt) (fun _ => Uncaught))
  (cpsResult r).
  linker CFfi.correctOpen.
Qed.
