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
Require Import Elab.

Require Import Elabify.


(** * Source *)

Section source.
  Open Local Scope source_scope.

  Definition unit_ : Term Unit := fun _ => ().
  Eval compute in TermDenote unit_.

  Definition unit__unit_ : Term (Unit ** Unit) := fun _ => [ (), () ].
  Eval compute in TermDenote unit__unit_.

  Definition unit__left : Term (Unit ++ Unit) := fun _ => Inl ().
  Eval compute in TermDenote unit__left.

  Definition unit__right : Term (Unit ++ Unit) := fun _ => Inr ().
  Eval compute in TermDenote unit__right.

  Definition bool := Unit ++ Unit.

  Definition false : Term bool := fun _ => Inl ().
  Definition true : Term bool := fun _ => Inr ().

  Definition not : Term (bool --> bool) := fun _ =>
    \x, Case #x of (
      (((Inl ##)%pat named tup ==> Inr ())
        :: ((Inr ##)%pat named tup ==> Inl ())
        :: nil))
    default (false _).

  Eval compute in TermDenote not.

  Definition not_false : Term bool := fun _ => not _ @ false _.
  Eval compute in TermDenote not_false.

  Definition not_true : Term bool := fun _ => not _ @ true _.
  Eval compute in TermDenote not_true.

  Definition bubba : Term ((bool ** bool) ++ (bool ** bool) --> bool) := fun _ =>
    \x, Case #x of (
      ((Inl [< ##, ## >])%pat named tup ==> #(fst tup))
      :: ((Inr [< ##, ## >])%pat named tup ==> #(fst (snd tup)))
      :: nil)
    default (false _).
  Eval compute in TermDenote bubba.

  Definition bubba_test1 : Term bool := fun _ => bubba _ @ Inl [ true _, false _ ].
  Eval compute in TermDenote bubba_test1.

  Definition bubba_test2 : Term bool := fun _ => bubba _ @ Inl [ false _, true _ ].
  Eval compute in TermDenote bubba_test2.

  Definition bubba_test3 : Term bool := fun _ => bubba _ @ Inr [ false _, true _ ].
  Eval compute in TermDenote bubba_test3.
End source.


(** * Elabify *)

Definition eunit_ := Elabify unit_.
Eval compute in eunit_.
Eval compute in EtermDenote eunit_.

Definition eunit__unit_ := Elabify unit__unit_.
Eval compute in eunit__unit_.
Eval compute in EtermDenote eunit__unit_.

Definition eunit__left := Elabify unit__left.
Eval compute in eunit__left.
Eval compute in EtermDenote eunit__left.

Definition eunit__right := Elabify unit__right.
Eval compute in eunit__right.
Eval compute in EtermDenote eunit__right.

Definition etrue := Elabify true.
Eval compute in etrue.
Eval compute in EtermDenote etrue.

Definition efalse := Elabify false.
Eval compute in efalse.
Eval compute in EtermDenote efalse.

Definition enot := Elabify not.
Eval compute in enot.
Eval compute in EtermDenote enot.

Definition enot_false := Elabify not_false.
Eval compute in enot_false.
Eval compute in EtermDenote enot_false.

Definition enot_true := Elabify not_true.
Eval compute in enot_true.
Eval compute in EtermDenote enot_true.

Definition ebubba := Elabify bubba.
Eval compute in ebubba.
Eval compute in EtermDenote ebubba.

Definition ebubba_test1 := Elabify bubba_test1.
Eval compute in ebubba_test1.
Eval compute in EtermDenote ebubba_test1.

Definition ebubba_test2 := Elabify bubba_test2.
Eval compute in ebubba_test2.
Eval compute in EtermDenote ebubba_test2.

Definition ebubba_test3 := Elabify bubba_test3.
Eval compute in ebubba_test3.
Eval compute in EtermDenote ebubba_test3.
