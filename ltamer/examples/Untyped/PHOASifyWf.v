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


Section vars.
  Variables var1 var2 : Type.

  Fixpoint zip n (il1 : ilist var1 n) {struct il1} : ilist var2 n -> list (var1 * var2) :=
    match il1 in ilist _ n return ilist _ n -> _ with
      | INil => fun _ => nil
      | ICons _ x1 il1' => fun il2 => (x1, ihead il2) :: zip il1' (itail il2)
    end.

  Theorem var_wf : forall n (f : fin n) (il1 : ilist var1 n) (il2 : ilist var2 n),
    In (iget il1 f, iget il2 f) (zip il1 il2).
    induction f; simpler; dep_destruct il1; dep_destruct il2; simpler.
  Qed.

  Hint Resolve var_wf.

  Theorem phoasify_wf : forall n (e : Source.exp n) (il1 : ilist var1 n) (il2 : ilist var2 n),
    Core.exp_equiv (zip il1 il2) (phoasify e il1) (phoasify e il2).
    Hint Constructors exp_equiv.

    Hint Extern 1 (exp_equiv ((?v1, ?v2) :: zip ?il1 ?il2) _ _) =>
      match goal with
        | [ IH : forall il1 il2, _ |- _ ] => apply (IH (v1 ::: il1) (v2 ::: il2))
      end.

    Hint Extern 1 (exp_equiv ((?F1, ?F2) :: (?v1, ?v2) :: zip ?il1 ?il2) _ _) =>
      match goal with
        | [ IH : forall il1 il2, _ |- _ ] => apply (IH (F1 ::: v1 ::: il1) (F2 ::: v2 ::: il2))
      end.

    induction e; simpler.
  Qed.
End vars.

Theorem Phoasify_wf : forall e,
  Core.Exp_wf (Phoasify e).
  unfold Exp_wf, Phoasify; intros;
    match goal with
      [ |- context[@nil (?var1 * ?var2)] ] =>
      change (@nil (var1 * var2)) with (zip (var1 := var1) (var2 := var2) INil INil); apply phoasify_wf
    end.
Qed.
