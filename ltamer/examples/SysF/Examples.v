(* Copyright (c) 2008, Adam Chlipala
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

Require Import Source.
Require Import CPS.

Require Import CPSify.

Set Implicit Arguments.


(** * Source *)

Section source.
  Open Local Scope source_scope.

  Definition eok T (E : Term T) := forall tvar1 tvar2 tvar3
    (var1 : type tvar1 -> Type) (var2 : type tvar2 -> Type) (var3 : type tvar3 -> Type),
    term_equiv nil nil (E _ var1) (E _ var2) (E _ var3).
  Ltac eok := red; repeat (intuition; constructor).

  Definition ident : Term (fun _ => All T, ^T --> ^T) := fun _ _ =>
    \\T, \x, #x.
  Eval simpl in termDenote (ident _).
  Theorem ident_eok : eok ident.
    unfold ident; eok.
  Qed.

  Definition ident_again : Term (fun _ => All T, ^T --> ^T).
    do 2 intro;
      refine (\\T, ident _ @@ ^T);
        auto.
  Defined.
  Eval simpl in termDenote (ident_again _).
  Theorem ident_again_eok : eok ident_again.
    unfold ident_again, ident; eok.
  Qed.

  Definition ident_self : Term (fun _ => All T, ^T --> ^T).
    do 2 intro;
      refine (ident _ @@ (All T, ^T --> ^T) @ ident _);
        auto.
  Defined.
  Eval simpl in termDenote (ident_self _).
  Theorem ident_self_eok : eok ident_self.
    unfold ident_self, ident; eok.
  Qed.

  Definition Nat : Typ := fun _ => All T, ^T --> (^T --> ^T) --> ^T.

  Definition zero : Term Nat := fun _ _ =>
    \\T, \z, \o, #z.
  Eval simpl in termDenote (zero _).
  Theorem zero_eok : eok zero.
    unfold Nat, zero; eok.
  Qed.

  Definition succ : Term (fun _ => Nat _ --> Nat _).
    do 2 intro;
      refine (\n, \\T, \z, \o, (#o @ (#n @@ ^T @ #z @ #o)));
        auto.
  Defined.
  Eval simpl in termDenote (succ _).
  Theorem succ_eok : eok succ.
    unfold succ; eok.
  Qed.

  Fixpoint nat_to_Nat (n : nat) : Term Nat :=
    match n with
      | O => zero
      | S n' => (fun _ _ => succ _ @ nat_to_Nat n' _)
    end.
  Definition Nat_to_nat (N : Term Nat) : nat :=
    termDenote (N _ _) nat O S.

  Eval compute in Nat_to_nat (nat_to_Nat 0).
  Eval compute in Nat_to_nat (nat_to_Nat 1).
  Eval compute in Nat_to_nat (nat_to_Nat 2).
  Eval compute in Nat_to_nat (nat_to_Nat 3).
  Eval compute in Nat_to_nat (nat_to_Nat 4).

  Eval compute in termDenote (nat_to_Nat (Nat_to_nat zero) _).
  Eval compute in termDenote (nat_to_Nat (Nat_to_nat (fun _ _ => succ _ @ zero _)) _).
  Eval compute in termDenote (nat_to_Nat (Nat_to_nat (fun _ _ => succ _ @ (succ _ @ zero _))) _).

End source.


(** * CPS *)

Theorem ident_subst : forall tvar (t : type tvar),
  Subst (fun T : tvar => ^T --> ^T)%source t (t --> t)%source.
  auto.
Qed.

Definition ident_correct (E : Term (fun _ => All T, ^T --> ^T)%source) :=
  PtermDenote (CpsTerm (fun _ _ => ETApp (E _ _) _ (ident_subst _) @ Tru)%source) (fun x => x) = true
  /\ PtermDenote (CpsTerm (fun _ _ => ETApp (E _ _) _ (ident_subst _) @ Fals)%source) (fun x => x) = false.

Eval compute in CpsTerm ident.
Theorem ident_cps_correct : ident_correct ident.
  compute_UIP; tauto.
Qed.

Eval compute in CpsTerm ident_again.
Theorem ident_again_cps_correct : ident_correct ident_again.
  compute_UIP; tauto.
Qed.

Eval compute in CpsTerm ident_self.
Theorem ident_self_cps_correct : ident_correct ident_self.
  compute_UIP; tauto.
Qed.

Theorem nat_subst : forall tvar (t : type tvar),
  Subst (fun T : tvar => ^T --> (^T --> ^T) --> ^T)%source t (t --> (t --> t) --> t)%source.
  auto.
Qed.

Eval compute in CpsTerm zero.
Theorem zero_cps_correct :
  PtermDenote (CpsTerm (fun _ _ => ETApp (zero _) _ (nat_subst _) @ Tru @ (\!, Fals))%source) (fun x => x)
  = true.
  compute_UIP; tauto.
Qed.

Eval compute in CpsTerm succ.
Theorem succ_cps_correct :
  PtermDenote (CpsTerm (fun _ _ => ETApp (succ _ @ zero _) _ (nat_subst _) @ Tru @ (\!, Fals))%source) (fun x => x)
  = false.
  compute_UIP; tauto.
Qed.
Theorem succ_cps_correct' :
  PtermDenote (CpsTerm (fun _ _ => ETApp (succ _ @ zero _) _ (nat_subst _) @ Tru @ (\x, #x))%source) (fun x => x)
  = true.
  compute_UIP; tauto.
Qed.
