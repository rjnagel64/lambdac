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
Require Import CPSifySpec.
Require Import CPSifySpecS.

Require Import SwapPre.
Require Import Swap.

Require Import Link.

Open Local Scope cps_scope.

Set Implicit Arguments.


Module Comp := Simple(CPSifyCorrect.Self).
Module Both := Join(Comp)(Swap.Self).
Module C := Close(Both).


Theorem linkFfiSwap : forall (E : Exp1) s h r,
  Core.Eval nil nil (fun _ => ELet (SwapAppPair _) (E _)) s h r
  -> Exp1_wf E
  -> CPS.Eval nil nil (fun _ =>
    f <- SwapAppPair' _;
    CPSify.cpsExp (E _ f) (fun _ => Halt) (fun _ => Uncaught))
  (cpsResult r).
  unfold Core.Eval, CPS.Eval, Exp1_wf, SwapAppPair'; intros; repeat evalOne;
    repeat match goal with
             | [ H : Core.eval _ _ _ _ _ _ |- _ ] =>
               invert_1_2 H; subst; try match goal with
                                          | [ H : _ |- _ ] => solve [ inversion H ]
                                        end; []
           end;
    eapply C.correctOpen; intros;
      (simpl in *; intuition;
        match goal with
          | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst
        end; econstructor; eauto) || eauto 9.
Qed.
