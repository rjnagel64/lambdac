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
Require Import CC.

Require Import CPSify.
Require Import CCify.


(** * Source *)

Section source.
  Open Local Scope source_scope.

  Definition fals : Term Bool := fun _ => Fals.
  Eval compute in TermDenote fals.

  Definition tru : Term Bool := fun _ => Tru.
  Eval compute in TermDenote tru.

  Definition ident : Term (Bool --> Bool) := fun _ => \x, #x.
  Eval compute in TermDenote ident.

  Definition fals_again : Term Bool := fun _ => ident _ @ fals _.
  Eval compute in TermDenote fals_again.

  Definition first : Term (Bool --> Bool --> Bool) := fun _ => \x, \y, #x.
  Eval compute in TermDenote first.

  Definition second : Term (Bool --> Bool --> Bool) := fun _ => \x, \y, #y.
  Eval compute in TermDenote second.

  Definition test_first : Term Bool := fun _ => first _ @ fals _ @ tru _.
  Eval compute in TermDenote test_first.

  Definition test_second : Term Bool := fun _ => second _ @ fals _ @ tru _.
  Eval compute in TermDenote test_second.

  Definition app : Term ((Bool --> Bool) --> Bool --> Bool) :=
    fun _ => \f, \x, #f @ #x.
  Eval compute in TermDenote app.

  Definition fals_again2 : Term Bool := fun _ => app _ @ ident _ @ fals _.
  Eval compute in TermDenote fals_again2.
End source.


(** * CPS *)

Definition cps_fals := CpsTerm fals.
Eval compute in cps_fals.
Eval compute in PtermDenote cps_fals.

Definition cps_tru := CpsTerm tru.
Eval compute in cps_tru.
Eval compute in PtermDenote cps_tru.

Definition cps_ident := CpsTerm ident.
Eval compute in cps_ident.
Eval compute in PtermDenote cps_ident.

Definition cps_fals_again := CpsTerm fals_again.
Eval compute in cps_fals_again.
Eval compute in PtermDenote cps_fals_again.

Definition cps_first := CpsTerm first.
Eval compute in cps_first.
Eval compute in PtermDenote cps_first.

Definition cps_second := CpsTerm second.
Eval compute in cps_second.
Eval compute in PtermDenote cps_second.

Definition cps_test_first := CpsTerm test_first.
Eval compute in cps_test_first.
Eval compute in PtermDenote cps_test_first.

Definition cps_test_second := CpsTerm test_second.
Eval compute in cps_test_second.
Eval compute in PtermDenote cps_test_second.

Definition cps_app := CpsTerm app.
Eval compute in cps_app.
Eval compute in PtermDenote cps_app.

Definition cps_fals_again2 := CpsTerm fals_again2.
Eval compute in cps_fals_again2.
Eval compute in PtermDenote cps_fals_again2.


(** * CC *)

Notation wfT := (wfTerm (envT := nil) tt).

Definition cps_fals_wf : wfT (cps_fals _).
  simpl; tauto.
Defined.
Definition cc_fals := CcTerm' cps_fals cps_fals_wf.
Eval compute in cc_fals.
Eval compute in CprogDenote cc_fals.

Definition cps_tru_wf : wfT (cps_tru _).
  simpl; tauto.
Defined.
Definition cc_tru := CcTerm' cps_tru cps_tru_wf.
Eval compute in cc_tru.
Eval compute in CprogDenote cc_tru.

Definition cps_ident_wf : wfT (cps_ident _).
  simpl; tauto.
Defined.
Definition cc_ident := CcTerm' cps_ident cps_ident_wf.
Eval compute in cc_ident.
Eval compute in CprogDenote cc_ident.

Definition cps_fals_again_wf : wfT (cps_fals_again _).
  simpl; tauto.
Defined.
Definition cc_fals_again := CcTerm' cps_fals_again cps_fals_again_wf.
Eval compute in cc_fals_again.
Eval compute in CprogDenote cc_fals_again.

Definition cps_first_wf : wfT (cps_first _).
  simpl; tauto.
Defined.
Definition cc_first := CcTerm' cps_first cps_first_wf.
Eval compute in cc_first.
Eval compute in CprogDenote cc_first.

Definition cps_second_wf : wfT (cps_second _).
  simpl; tauto.
Defined.
Definition cc_second := CcTerm' cps_second cps_second_wf.
Eval compute in cc_second.
Eval compute in CprogDenote cc_second.

Definition cps_test_first_wf : wfT (cps_test_first _).
  simpl; tauto.
Defined.
Definition cc_test_first := CcTerm' cps_test_first cps_test_first_wf.
Eval compute in cc_test_first.
Eval compute in CprogDenote cc_test_first.

Definition cps_test_second_wf : wfT (cps_test_second _).
  simpl; tauto.
Defined.
Definition cc_test_second := CcTerm' cps_test_second cps_test_second_wf.
Eval compute in cc_test_second.
Eval compute in CprogDenote cc_test_second.

Definition cps_app_wf : wfT (cps_app _).
  simpl; tauto.
Defined.
Definition cc_app := CcTerm' cps_app cps_app_wf.
Eval compute in cc_app.
Eval compute in CprogDenote cc_app.

Definition cps_fals_again2_wf : wfT (cps_fals_again2 _).
  simpl; tauto.
Defined.
Definition cc_fals_again2 := CcTerm' cps_fals_again2 cps_fals_again2_wf.
Eval compute in cc_fals_again2.
Eval compute in CprogDenote cc_fals_again2.
