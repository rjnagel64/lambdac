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

Require Import Arith Eqdep List Omega TheoryList.

Set Implicit Arguments.

(** * Transparent versions of some definitions from the standard library, to facilitate reduction *)

Section conj.
  Variables A B : Prop.

  Definition proj1 (c : A /\ B) : A :=
    match c with
      | conj x _ => x
    end.

  Definition proj2 (c : A /\ B) : B :=
    match c with
      | conj _ y => y
    end.
End conj.

Section list.
  Variables A B : Type.
  Variable f : A -> B.

  Theorem map_length : forall ls,
    length (map f ls) = length ls.
    induction ls; simpl; intuition.
  Defined.

  Theorem length_S_eq : forall A B (x1 : A) (x2 : B) ls1 ls2,
    length ls1 = length ls2
    -> length (x1 :: ls1) = length (x2 :: ls2).
    simpl; auto.
  Qed.
End list.

Hint Resolve length_S_eq.


(** * Casts *)

Notation "e :? pf" := (eq_rect _ (fun X : Set => X) e _ pf)
  (no associativity, at level 90).

Theorem cast_coalesce : forall (T1 T2 T3 : Set) (e : T1) (pf1 : T1 = T2) (pf2 : T2 = T3),
  ((e :? pf1) :? pf2) = (e :? trans_eq pf1 pf2).
  intros.
  generalize pf1 pf2.
  subst.
  intros.
  rewrite (UIP_refl _ _ pf1).
  rewrite (UIP_refl _ _ pf2).
  reflexivity.
Qed.

Lemma trans_cast : forall (T1 T2 : Set) H (x z : T1) (y : T2),
  x = (y :? H)
  -> (y :? H) = z
  -> x = z.
  intros; congruence.
Qed.

Notation "e ::? pf" := (eq_rect _ (fun X : Type => X) e _ pf)
  (no associativity, at level 90).

Theorem castT_coalesce : forall T1 T2 T3 (e : T1) (pf1 : T1 = T2) (pf2 : T2 = T3),
  ((e ::? pf1) ::? pf2) = (e ::? trans_eq pf1 pf2).
  intros.
  generalize pf1 pf2.
  subst.
  intros.
  rewrite (UIP_refl _ _ pf1).
  rewrite (UIP_refl _ _ pf2).
  reflexivity.
Qed.


(** * Variable-length tuples *)

Section repeat.
  Variable T : Type.

  Fixpoint repeat (n : nat) : Type :=
    match n with
      | O => unit
      | S n' => T * repeat n'
    end%type.

  Fixpoint index (n : nat) : Type :=
    match n with
      | O => Empty_set
      | S n' => option (index n')
    end.

  Definition first (n : nat) : index (S n) := None.
  Definition next (n : nat) (idx : index n) : index (S n) := Some idx.

  Fixpoint last (n : nat) : index (S n) :=
    match n return index (S n) with
      | O => None
      | S n' => Some (last n')
    end.

  Fixpoint lift (n : nat) : index n -> index (S n) :=
    match n return index n -> index (S n) with
      | O => fun idx => match idx with end
      | S n' => fun idx =>
        match idx with
          | None => None
          | Some idx' => Some (lift _ idx')
        end
    end.

  Fixpoint select (n : nat) : repeat n -> index n -> T :=
    match n return (repeat n -> index n -> T) with
      | O => fun _ idx => match idx with end
      | S n' => fun rep idx =>
        match idx with
          | None => fst rep
          | Some idx' => select n' (snd rep) idx'
        end
    end.

  Fixpoint eta_index (n : nat) : (index n -> T) -> (index n -> T) :=
    match n return (index n -> T) -> (index n -> T) with
      | O => fun _ idx => match idx with end
      | S n' => fun f idx =>
        match idx with
          | None => f None
          | Some idx' => eta_index n' (fun idx'' => f (Some idx'')) idx'
        end
    end.
End repeat.

Implicit Arguments first [n].
Implicit Arguments next [n].
Implicit Arguments last [n].
Implicit Arguments lift [n].
Implicit Arguments select [T n].
Implicit Arguments eta_index [T n].

(** * Hetereogeneous lists *)

Section tuple.
  Variable T : Type.

  Fixpoint nth0 (ls : list T) (n : nat) {struct ls} : option T :=
    match ls with
      | nil => None
      | h :: t =>
        match n with
          | O => Some h
          | S n' => nth0 t n'
        end
    end.

  Theorem nth0_concat_through : forall ls2 ls1 n,
    length ls1 <= n
    -> nth0 (ls1 ++ ls2) n = nth0 ls2 (n - length ls1).
    induction ls1; simpl; intuition.

    destruct n.

    elimtype False.
    omega.

    replace (S n - S (length ls1)) with (n - length ls1); [idtac | omega].
    auto with arith.
  Qed.

  Theorem nth0_concat_within : forall ls2 ls1 n,
    n < length ls1
    -> nth0 (ls1 ++ ls2) n = nth0 ls1 n.
    induction ls1; simpl; intuition.

    elimtype False; omega.

    destruct n; auto with arith.
  Qed.

  Fixpoint nth (ls : list T) (n : nat) {struct ls} : option T :=
    match ls with
      | nil => None
      | h :: t =>
        if eq_nat_dec n (length t)
          then Some h
          else nth t n
    end.

  Theorem nth_contra : forall v n ls,
    nth ls n = Some v
    -> n >= length ls
    -> False.
    induction ls; simpl; intuition.
    discriminate.
    destruct (eq_nat_dec n (length ls)).
    omega.
    auto with arith.
  Qed.

  Theorem nth_lt : forall v n ls,
    nth ls n = Some v
    -> n < length ls.
    intros.
    generalize (nth_contra _ H).
    omega.
  Qed.

  Theorem nth_weaken : forall v n ls ls',
    nth ls n = Some v
    -> nth (ls' ++ ls) n = Some v.
    induction ls'; simpl; intuition.

    destruct (eq_nat_dec n (length (ls' ++ ls))); intuition.
    elimtype False; eapply nth_contra; eauto; omega.
  Qed.

  Variable f : T -> Type.

  Fixpoint tuple (ls : list T) : Type :=
    match ls with
      | nil => unit
      | h :: t => (f h * tuple t)%type
    end.

  Fixpoint concat (ls1 ls2 : list T) {struct ls1} : tuple ls1 -> tuple ls2 -> tuple (ls1 ++ ls2) :=
    match ls1 return (tuple ls1 -> _ -> tuple (ls1 ++ ls2)) with
      | nil => fun _ tup2 => tup2
      | _ :: _ => fun tup1 tup2 => (fst tup1, concat _ _ (snd tup1) tup2)
    end.

  Implicit Arguments concat [ls1 ls2].

  Fixpoint take (ls1 ls2 : list T) {struct ls1} : tuple (ls1 ++ ls2) -> tuple ls1 :=
    match ls1 return (tuple (ls1 ++ ls2) -> tuple ls1) with
      | nil => fun _ => tt
      | _ :: _ => fun tup => (fst tup, take _ _ (snd tup))
    end.

  Fixpoint drop (ls1 ls2 : list T) {struct ls1} : tuple (ls1 ++ ls2) -> tuple ls2 :=
    match ls1 return (tuple (ls1 ++ ls2) -> tuple ls2) with
      | nil => fun tup => tup
      | _ :: _ => fun tup => drop _ _ (snd tup)
    end.

  Fixpoint toHetero (ls : list T) : tuple ls -> list (sigT f) :=
    match ls return (tuple ls -> _) with
      | nil => fun _ => nil
      | _ :: _ => fun tup => existT _ _ (fst tup) :: toHetero _ (snd tup)
    end.

  Definition lookup_result (v : option T) :=
    match v with
      | None => unit
      | Some x => f x
    end.

  Definition lookup (ls : list T) : forall n, tuple ls -> lookup_result (nth ls n).
    induction ls; intros.

    exact tt.

    simpl.
    destruct (eq_nat_dec n (length ls)).

    exact (fst X).

    apply IHls.
    exact (snd X).
  Defined.

  Fixpoint member (x : T) (ls : list T) {struct ls} : Type :=
    match ls with
      | nil => Empty_set
      | h :: t => (h = x) + member x t
    end%type.

  Fixpoint get x ls {struct ls} : tuple ls -> member x ls -> f x :=
    match ls return (tuple ls -> member x ls -> f x) with
      | nil => fun _ m => Empty_set_rect (fun _ => _) m
      | _ :: _ => fun tup m =>
        match m with
          | inl Heq => fst tup ::? (f_equal _ Heq)
          | inr m' => get _ _ (snd tup) m'
        end
    end.

  Implicit Arguments get [x ls].

  Fixpoint entuple ls : (forall x, member x ls -> f x) -> tuple ls :=
    match ls return ((forall x, member x ls -> f x) -> tuple ls) with
      | nil => fun _ => tt
      | _ :: _ => fun f => (f _ (inl _ (refl_equal _)), entuple _ (fun _ m => f _ (inr _ m)))
    end.

  Implicit Arguments entuple [ls].

  Fixpoint member_weaken (x : T) (ls1 ls2 : list T) (y : T) {struct ls1}
    : member x (ls1 ++ ls2) -> member x (ls1 ++ y :: ls2) :=
    match ls1 return (member x (ls1 ++ ls2) -> member x (ls1 ++ y :: ls2)) with
      | nil => fun m => inr _ m
      | _ :: _ => fun m =>
        match m with
          | inl Heq => inl _ Heq
          | inr m' => inr _ (member_weaken _ _ _ _ m')
        end
    end.

  Implicit Arguments member_weaken [x ls1 ls2].

  Theorem get_weaken : forall x ls2 (tup2 : tuple ls2)
    (t : T) (v : f t)
    ls1 (tup1 : tuple ls1) 
    (m : member x (ls1 ++ ls2)),
    get (concat (ls2 := t :: ls2) tup1 (v, tup2)) (member_weaken t m)
    = get (concat tup1 tup2) m.
    induction ls1; simpl; intuition.
  Qed.

  Fixpoint member_front (x : T) (ls1 ls2 : list T) (m : member x ls2) {struct ls1}
    : member x (ls1 ++ ls2) :=
    match ls1 return (member x (ls1 ++ ls2)) with
      | nil => m
      | _ :: _ => inr _ (member_front _ _ _ m)
    end.

  Implicit Arguments member_front [x ls2].

  Theorem get_front : forall x ls2 (tup2 : tuple ls2)
    (t : T) (v : f t)
    ls1 (tup1 : tuple ls1) 
    (m : member x ls2),
    get (concat tup1 tup2) (member_front _ m)
    = get tup2 m.
    induction ls1; simpl; intuition.
  Qed.

  Variable g : forall x, f x -> Type.

  Fixpoint tuple2 (ls : list T) : tuple ls -> Type :=
    match ls return (tuple ls -> Type) with
      | nil => fun _ => unit
      | _ :: _ => fun tup => (g (fst tup) * tuple2 _ (snd tup))%type
    end.
End tuple.

Implicit Arguments concat [T f ls1 ls2].
Implicit Arguments take [T f ls1 ls2].
Implicit Arguments drop [T f ls1 ls2].
Implicit Arguments toHetero [T f ls].
Implicit Arguments lookup [T f ls].
Implicit Arguments get [T f x ls].
Implicit Arguments entuple [T f ls].
Implicit Arguments tuple2 [T f ls].
Implicit Arguments member_weaken [T x ls1 ls2].
Implicit Arguments member_front [T x ls2].

Hint Rewrite nth0_concat_through nth0_concat_within using omega : ltamer.

Section tuple_map.
  Variable T : Type.
  Variables f1 f2 : T -> Type.
  Variable g : forall x, f1 x -> f2 x.

  Fixpoint tuple_map ls : tuple f1 ls -> tuple f2 ls :=
    match ls return (tuple f1 ls -> tuple f2 ls) with
      | nil => fun _ => tt
      | _ :: _ => fun tup => (g (fst tup), tuple_map _ (snd tup))
    end.

  Implicit Arguments tuple_map [ls].

  Theorem tuple_map_concat : forall ls1 (tup1 : tuple f1 ls1)
    ls2 (tup2 : tuple f1 ls2),
    tuple_map (concat tup1 tup2) = concat (tuple_map tup1) (tuple_map tup2).
    induction ls1; simpl; intuition; simpl.
    rewrite IHls1; auto.
  Qed.
End tuple_map.

Implicit Arguments tuple_map [T f1 f2 ls].

Section list2.
  Variables A B : Type.
  Variable f : A -> B.

  Theorem nth_map_some : forall ls n x,
    nth ls n = Some x
    -> nth (map f ls) n = Some (f x).
    induction ls; simpl; intros.

    discriminate.

    rewrite map_length.

    destruct (eq_nat_dec n (length ls)); subst.

    congruence.

    auto.
  Defined.
End list2.

Hint Resolve nth_map_some.


Section All2.
  Variables A B : Type.
  Variable P : A -> B -> Prop.

  Fixpoint All2 (ls1 : list A) (ls2 : list B) {struct ls1} : Prop :=
    match ls1, ls2 with
      | nil, nil => True
      | h1 :: t1, h2 :: t2 => P h1 h2 /\ All2 t1 t2
      | _, _ => False
    end.
End All2.


(** * Theorems meant to aid proofs that substitution relations are functions *)

Theorem eq_args : forall T1 T2 (f1 f2 : T1 -> T2) x,
  f1 = f2
  -> f1 x = f2 x.
  intros; congruence.
Defined.

Theorem eq_all_Sets : Empty_set = unit -> False.
  intros Heq; assert (H : exists x : Empty_set, True); [
    rewrite Heq; exists tt; auto
    | destruct H; tauto
  ].
Qed.
