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

Set Implicit Arguments.


Section vars.
  Variable tvar : Type.

  Inductive ty : Type :=
  | TVar : tvar -> ty
  | TTop : ty
  | TArrow : ty -> ty -> ty
  | TAll : ty -> (tvar -> ty) -> ty.

  Notation "# v" := (TVar v) (at level 70).
  Notation "'Top'" := TTop.
  Infix "-->" := TArrow (at level 71).
  Notation "'All' X <: t1 , t2" := (TAll t1 (fun X => t2)) (at level 72, X at level 0).

  Definition tctx := list (tvar * ty).

  Reserved Notation "G |-- t1 <: t2" (at level 80, t1 at next level).

  Inductive subty : tctx -> ty -> ty -> Prop :=
  | SA_Top : forall G S,
    G |-- S <: Top

  | SA_Refl_TVar : forall G X,
    G |-- #X <: #X

  | SA_Trans_TVar : forall G X U T,
    In (X, U) G
    -> G |-- U <: T
    -> G |-- #X <: T

  | SA_Arrow : forall G T1 S1 S2 T2,
    G |-- T1 <: S1
    -> G |-- S2 <: T2
    -> G |-- S1 --> S2 <: T1 --> T2

  | SA_All : forall G T1 S1 S2 T2,
    G |-- T1 <: S1
    -> (forall X, (X, T1) :: G |-- S2 X <: T2 X)
    -> G |-- TAll S1 S2 <: TAll T1 T2

  where "G |-- t1 <: t2" := (subty G t1 t2).

  Hint Constructors subty.
  
  Lemma Reflexivity : forall T G, G |-- T <: T.
    induction T; auto.
  Qed.

  Lemma Monotone_push : forall T (p p' : T) G D,
    (forall p, In p G -> In p D)
    -> In p (p' :: G)
    -> In p (p' :: D).
    simpler.
  Qed.

  Hint Resolve Monotone_push.

  Lemma Monotone : forall G S T,
    G |-- S <: T
    -> forall D, (forall p, In p G -> In p D)
      -> D |-- S <: T.
    induction 1; eauto.
  Qed.

  Lemma Narrowing_In1 : forall T (p1 p2 : T) D G,
    In p1 (G ++ p2 :: D)
    -> p1 = p2 \/ In p1 G \/ In p1 D.
    induction G; simpler.
  Qed.

  Implicit Arguments Narrowing_In1 [T p1 p2 D G].

  Lemma Narrowing_In2 : forall T (p1 p2 : T) D G,
    In p1 G
    -> In p1 (G ++ p2 :: D).
    induction G; simpler.
  Qed.

  Lemma Narrowing_In3 : forall T (p : T) D G,
    In p (G ++ p :: D).
    induction G; simpler.
  Qed.

  Lemma Narrowing_In4 : forall T (p1 p2 : T) D G,
    In p1 D
    -> In p1 (G ++ p2 :: D).
    induction G; simpler.
  Qed.

  Hint Resolve Narrowing_In2 Narrowing_In3 Narrowing_In4.

  Lemma Narrowing_Monotone : forall G S T,
    G |-- S <: T
    -> forall p D, G ++ p :: D |-- S <: T.
    intros; eapply Monotone; eauto.
  Qed.

  Lemma Monotone1 : forall G S T,
    G |-- S <: T
    -> forall p, p :: G |-- S <: T.
    intros; eapply Monotone; eauto; simpler.
  Qed.

  Hint Resolve Narrowing_Monotone Monotone1.

  Lemma subty_comm_cons : forall p G D S T,
    (p :: G) ++ D |-- S <: T
    -> p :: G ++ D |-- S <: T.
    trivial.
  Qed.

  Hint Resolve subty_comm_cons.

  Lemma swap_All : forall p G S T,
    G ++ p :: nil |-- S <: T
    -> p :: G |-- S <: T.
    intros; eapply Monotone; eauto; simpler;
      match goal with
        | [ H : In _ (_ ++ _ :: _) |- _ ] =>
          generalize (Narrowing_In1 H); simpler
      end.
  Qed.

  Lemma swap_All' : forall p G S T,
    p :: G |-- S <: T
    -> G ++ p :: nil |-- S <: T.
    intros; eapply Monotone; eauto; simpler.
  Qed.

  Hint Resolve swap_All swap_All'.

  Lemma Transitivity_and_Narrowing : forall Q,
    (forall G S T, G |-- S <: Q
      -> G |-- Q <: T
      -> G |-- S <: T)
    /\ ((forall G S T, G |-- S <: Q
      -> G |-- Q <: T
      -> G |-- S <: T)
    -> (forall G X D M N P, G ++ (X, Q) :: D |-- M <: N
      -> G |-- P <: Q
      -> G ++ (X, P) :: D |-- M <: N)).
    induction Q; simpler;
      match goal with
        | [ H : ?G ++ ?p :: ?D |-- _ <: _ |- _ ] =>
          remember (G ++ p :: D) as G'; generalize dependent G; induction H; simpler; eauto;
            match goal with
              | [ H : In _ (_ ++ _ :: _) |- _ ] =>
                generalize (Narrowing_In1 H); simpler; eauto
            end
        | [ H1 : _ |-- _ <: ?Q', H2 : _ |-- ?Q' <: _ |- _ ] =>
          remember Q' as Q; induction H1; simpler; eauto; inverter H2; simpler
      end;
      match goal with
        | [ H : (_ --> _) = (_ --> _) |- _ ] => injection H
        | [ H : TAll _ _ = TAll _ _ |- _ ] => injection H
      end; simpler;
      match goal with
        | [ |- _ |-- TAll _ _ <: TAll _ _ ] =>
          constructor; intros; auto; match goal with
                                       | [ X : tvar, H : forall X : tvar, _ /\ _ |- _ ] =>
                                         generalize (H X); intuition
                                     end
      end.
  Qed.

  Lemma Transitivity : forall G S Q T,
    G |-- S <: Q
    -> G |-- Q <: T
    -> G |-- S <: T.
    generalize Transitivity_and_Narrowing; firstorder.
  Qed.
End vars.

Implicit Arguments TTop [tvar].

Notation "# v" := (TVar v) (at level 70).
Notation "'Top'" := TTop.
Infix "-->" := TArrow (at level 71).
Notation "'All' X <: t1 , t2" := (TAll t1 (fun X => t2)) (at level 72, X at level 0).

Notation "G |-- t1 <: t2" := (subty G t1 t2) (at level 80, t1 at next level).
