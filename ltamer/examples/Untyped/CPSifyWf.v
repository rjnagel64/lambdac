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


Hint Constructors CPS.exp_equiv.

Section vars.
  Variables var1 var2 : Type.

  Lemma cpsExp_wf : forall G (e1 : Core.exp var1) (e2 : Core.exp var2),
    Core.exp_equiv G e1 e2
    -> forall k1 k2 ke1 ke2 G',
      (forall p, In p G -> In p G')
      -> (forall G'' x1 x2,
        (forall p, In p G' -> In p G'')
        -> In (x1, x2) G''
        -> CPS.exp_equiv G'' (k1 x1) (k2 x2))
      -> (forall G'' x1 x2,
        (forall p, In p G' -> In p G'')
        -> In (x1, x2) G''
        -> CPS.exp_equiv G'' (ke1 x1) (ke2 x2))
      -> CPS.exp_equiv G' (cpsExp e1 k1 ke1) (cpsExp e2 k2 ke2).
    induction 1; simpler; unfold cpsFunc';
      repeat match goal with
               | _ => solve [ eauto 6 ]
               | [ H : forall G'' x1 x2, _ -> _ -> exp_equiv _ (?k1 _) (?k2 _)
                   |- context[exp_equiv _ (?k1 _) (?k2 _)] ] =>
                 apply H; simpl; intros
               | [ |- In _ _ ] => simpl in *; intuition eauto; subst; tauto
               | [ H : _ |- _ ] => eapply H; eauto; intros
               | _ => constructor; intros
             end.
  Qed.
End vars.

Theorem CpsExp_wf : forall E,
  Core.Exp_wf E
  -> CPS.Exp_wf (CpsExp E).
  Hint Resolve cpsExp_wf.

  unfold Core.Exp_wf, CPS.Exp_wf, CpsExp; eauto.
Qed.
