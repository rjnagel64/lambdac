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

Require Import Coq.FSets.FMapList Coq.FSets.OrderedTypeEx.

Require Import LambdaTamer.LambdaTamer.

Set Implicit Arguments.


Module NM := Coq.FSets.FMapList.Make(Coq.FSets.OrderedTypeEx.Nat_as_OT).

Section operations.
  Variable A : Set.
  Variable default : A.

  Definition sel (h : NM.t A) (a : nat) :=
    match NM.find a h with
      | Some v => v
      | None => default
    end.
  Definition upd (h : NM.t A) (a : nat) (v : A) := NM.add a v h.

  Theorem sel_upd_eq : forall h a v a',
    a' = a
    -> sel (upd h a v) a' = v.
    unfold sel, upd; simpler;
      replace (NM.find a (NM.add a v h)) with (Some v); trivial;
        symmetry; apply NM.find_1; apply NM.add_1; auto.
  Qed.

  Lemma sel_upd_ne' : forall (h : NM.t A) a a' v,
    a' <> a
    -> NM.find a' (NM.add a v h) = NM.find a' h.
    Hint Resolve NM.find_1 NM.find_2 NM.add_2 NM.add_3.

    intros; case_eq (NM.find a' h); simpler;
      case_eq (NM.find a' (NM.add a v h)); simpler.
    generalize (NM.find_2 H1).
    intros.
    assert (a <> a'); [ auto | ].
    generalize (NM.add_3 H3 H2).
    intros.
    generalize (NM.find_1 H4).
    intros.
    congruence.
  Qed.

  Hint Rewrite sel_upd_ne' : ltamer.

  Theorem sel_upd_ne : forall h a a' v,
    a' <> a
    -> sel (upd h a v) a' = sel h a'.
    unfold sel, upd; simpler.
  Qed.

  Hint Resolve sel_upd_eq sel_upd_ne.

  Hint Resolve NM.find_1 NM.find_2 NM.add_1 NM.add_2 NM.add_3.

  Lemma find_upd_eq : forall m a (v : A),
    NM.find a (upd m a v) = Some v.
    unfold upd; auto.
  Qed.

  Lemma find_upd_ne : forall m a a' (v : A),
    a <> a'
    -> NM.find a' (upd m a v) = NM.find a' m.
    unfold upd; intros;
      case_eq (NM.find a' m); equation;
      case_eq (NM.find a' (NM.add a v m)); equation;
      match goal with
        | [ _ : NM.find _ _ = Some ?a0 |- _ ] =>
          assert (NM.find a' m = Some a0); eauto
      end.
  Qed.
End operations.

Ltac solver := solve [ auto | omega ].

Hint Rewrite sel_upd_eq sel_upd_ne find_upd_eq find_upd_ne using solver : ltamer.
