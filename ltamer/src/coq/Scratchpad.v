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

Require Import Arith List.

Require Import LambdaTamer.DepList.
Require Import LambdaTamer.Tactics.

Set Implicit Arguments.


Definition label := nat.

Reserved Notation "ls # l" (left associativity, at level 1).

Fixpoint grab (A : Type) (s : list A) (l : label) {struct s} : option A :=
  match s with
    | nil => None
    | x :: s' =>
      if eq_nat_dec l (length s')
        then Some x
        else s'#l
  end

where "ls # l" := (grab ls l).

Section grab.
  Variable A : Type.

  Theorem grab_length : forall x (s : list A),
    grab (x :: s) (length s) = Some x.
    simpl; intros.
    destruct (eq_nat_dec (length s) (length s)); tauto.
  Qed.

  Theorem grab_S_length : forall x y (s : list A),
    grab (x :: y :: s) (S (length s)) = Some x.
    simpl; intros.
    destruct (eq_nat_dec (length s) (length s)); simpl; tauto.
  Qed.

  Theorem grab_S_S_length : forall x y z (s : list A),
    grab (x :: y :: z :: s) (S (S (length s))) = Some x.
    simpl; intros.
    destruct (eq_nat_dec (length s) (length s)); simpl; tauto.
  Qed.

  Theorem grab_length_contra' : forall n (s : list A),
    n >= length s
    -> grab s n = None.
    induction s; simpler_expensive; elimtype False; omega.
  Qed.

  Theorem grab_length_contra : forall (s : list A),
    grab s (length s) = None.
    intros; apply grab_length_contra'; auto.
  Qed.

  Theorem grab_nil_contra : forall n v,
    grab (@nil A) n = Some v -> False.
    simpler.
  Qed.

  Theorem grab_middle : forall x (s2 : list A) s1,
    (s1 ++ x :: s2) # (length s2) = Some x.
    Hint Rewrite app_length : ltamer.

    induction s1; equation_expensive.
    elimtype False; omega.
  Qed.

  Theorem grab_middle_unused : forall y x n (s2 : list A),
    n <> length s2
    -> forall s1, (s1 ++ x :: s2) # n = (s1 ++ y :: s2) # n.
    Hint Rewrite app_length : ltamer.

    induction s1; equation_expensive.
  Qed.

  Theorem grab_middle_after : forall x n (s2 : list A),
    n < length s2
    -> forall s1, (s1 ++ x :: s2) # n = s2 # n.
    induction s1; equation_expensive;
      elimtype False; equation.
  Qed.

  Lemma grab_app : forall (v : A) a s2,
    s2 # a = Some v
    -> forall s1, (s1 ++ s2) # a = Some v.
    induction s1; simpler_expensive.
    rewrite grab_length_contra' in IHs1; simpler.
  Qed.

  Lemma grab_same_length : forall B (s1 : list A) (s2 : list B) v,
    length s1 = length s2
    -> (v :: s2) # (length s1) = Some v.
    simpler_expensive.
  Qed.

  Theorem lall_grab : forall P a (v : A) ls,
    lall P ls
    -> ls # a = Some v
    -> P v.
    induction ls; simpler_expensive.
  Qed.

  Theorem grab_middle_nil : forall x (s1 : list A),
    (s1 ++ x :: nil) # O = Some x.
    intros; change O with (length (@nil A)); apply grab_middle.
  Qed.

  Theorem grab_before_nil : forall x n (s1 : list A),
    (s1 ++ x :: nil) # (S n) = s1 # n.
    Hint Rewrite app_length plus_1 : ltamer.

    induction s1; simpler_expensive.
  Qed.

  Lemma plus_1 : forall n, n + 1 = S n.
    intro; omega.
  Qed.

  Theorem grab_last : forall x (s : list A),
    (s ++ x :: nil) # O = Some x.
    Hint Rewrite app_length plus_1 : ltamer.
    
    induction s; equation_expensive.
  Qed.

  Theorem grab_not_last : forall (x : A) n,
    n <> O
    -> forall s, (s ++ x :: nil) # n = s # (n-1).
    induction s; equation_expensive; comega.
  Qed.
End grab.

Hint Resolve grab_app.

Hint Rewrite grab_S_S_length grab_S_length grab_length grab_length_contra grab_middle : ltamer.
Hint Rewrite grab_middle_nil grab_before_nil : ltamer.
Hint Rewrite grab_same_length using assumption : ltamer.
Hint Rewrite grab_length_contra' grab_middle_unused grab_middle_after using solve [ auto ] : ltamer.

Implicit Arguments lall_grab [A P a v ls].
Hint Resolve lall_nil lall_cons.

Section extends.
  Variable A : Type.

  Definition extends (x y : list A) :=
    exists z, y = z ++ x.

  Theorem extends_refl : forall x, extends x x.
    exists (@nil A); reflexivity.
  Qed.

  Theorem extends_trans : forall x y,
    extends x y
    -> forall z, extends y z
      -> extends x z.
    induction 1; unfold extends in *; simpler.
    exists (x1 ++ x0); rewrite app_ass; reflexivity.
  Qed.

  Theorem extends_cons : forall x y,
    extends x (y :: x).
    intros; exists (y :: nil); reflexivity.
  Qed.
End extends.

Infix "~>" := extends (no associativity, at level 70).

Hint Resolve extends_refl extends_trans extends_cons.

Theorem grab_oob : forall A l (v : A) s,
  grab s l = Some v
  -> l >= length s
  -> False.
  induction s; simpler.
Qed.

Theorem grab_oob' : forall A l s (v : A),
  grab s l = Some v
  -> l < length s.
  intros.
  generalize (grab_oob _ H); omega.
Qed.

Theorem grab_extends : forall A l (v : A) s s',
  s ~> s'
  -> grab s l = Some v
  -> grab s' l = Some v.
  unfold extends; simpler.
Qed.

Hint Resolve grab_oob' grab_extends grab_length grab_S_length grab_S_S_length.

Reserved Notation "ls ## l <~ v" (left associativity, at level 2).

Fixpoint upd (A : Type) (s : list A) (l : label) (v : A) {struct s} : list A :=
  match s with
    | nil => nil
    | x :: s' =>
      if eq_nat_dec l (length s')
        then v :: s'
        else x :: (s' ## l <~ v)
  end

where "ls ## l <~ v" := (upd ls l v).

Theorem upd_length : forall A (s : list A) l v,
  length (s ## l <~ v) = length s.
  induction s; simpler_expensive.
Qed.

Hint Rewrite upd_length : ltamer.

Theorem upd_choices : forall A l l' v (s : list A),
  l' < length s
  -> (l = l' /\ (s ## l <~ v) # l' = Some v)
  \/ (l <> l' /\ (s ## l <~ v) # l' = s # l').
  induction s; simpler_expensive.
Qed.

Lemma sel_upd_eq : forall A l v (s : list A),
  l < length s
  -> (s ## l <~ v) # l = Some v.
  induction s; simpler_expensive; comega.
Qed.

Lemma sel_upd_ne : forall A l l' v (s : list A),
  l <> l'
  -> (s ## l <~ v) # l' = s # l'.
  induction s; simpler_expensive.
Qed.

Hint Rewrite sel_upd_eq sel_upd_ne using omega : ltamer.

Section sall.
  Variables A1 A2 : Type.
  Variable P : A1 -> A2 -> Prop.

  Definition sall (s1 : list A1) (s2 : list A2) :=
    length s1 = length s2
    /\ forall l : label, l < length s1
      -> match s1 # l, s2 # l with
           | None, None => True
           | Some v1, Some v2 => P v1 v2
           | _, _ => False
         end.

  Theorem sall_length : forall s1 s2, sall s1 s2 -> length s1 = length s2.
    unfold sall; tauto.
  Qed.

  Theorem sall_nil : sall nil nil.
    red; simpler.
  Qed.

  Theorem sall_cons : forall s1 s2, sall s1 s2
    -> forall v1 v2, P v1 v2
      -> sall (v1 :: s1) (v2 :: s2).
    unfold sall; simpler_expensive.
    apply H1.
    omega.
  Qed.

  Theorem sall_upd : forall s1 s2, sall s1 s2
    -> forall l v1 v2, P v1 v2
      -> sall (s1 ## l <~ v1) (s2 ## l <~ v2).
    unfold sall; simpler.
    generalize (upd_choices l v1 s1 H2).
    assert (l0 < length s2); [ simpler | ].
    generalize (upd_choices l v2 s2 H3).
    equation.
    apply H1; auto.
  Qed.

  Theorem sall_grab : forall s1 s2 l v1,
    sall s1 s2
    -> s1 # l = Some v1
    -> exists v2, s2 # l = Some v2 /\ P v1 v2.
    unfold sall; simpler.
    generalize (H2 l); clear H2; intros.
    rewrite H0 in H.
    destruct (s2 # l); intuition eauto.
    elimtype False; eauto.
  Qed.
End sall.

Hint Resolve sall_nil sall_cons sall_upd.

Implicit Arguments sall_grab [A1 A2 P s1 s2 l v1].

Section sall2.
  Variables A1 A2 : Type.
  Variable P P' : A1 -> A2 -> Prop.

  Hypothesis P_imp : forall v1 v2,
    P v1 v2 -> P' v1 v2.

  Theorem sall_weaken : forall s1 s2,
    sall P s1 s2
    -> sall P' s1 s2.
    unfold sall; intuition.
    generalize (H1 l); simpler.
    repeat (match goal with
              | [ |- match ?E with None => _ | Some _ => _ end ] => destruct E
            end; simpler).
  Qed.
End sall2.

Hint Resolve sall_weaken.

Implicit Arguments upd_choices [A l' s].
