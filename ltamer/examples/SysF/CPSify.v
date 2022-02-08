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

Require Import LambdaTamer.
Require Import Util.

Require Import Source.
Require Import CPS.

Set Implicit Arguments.


(** * CPS translation *)

(** ** Translating types *)

Fixpoint cpsType tvar (t : type tvar) : ptype tvar :=
  match t with
    | Bool => Bool%cps
    | ^x => (^x)%cps
    | t1 --> t2 => (cpsType t1 ** (cpsType t2 --->) --->)%cps
    | TAll t' => (All T, cpsType (t' T) ---> --->)%cps
  end%source.

Ltac my_changer :=
  match goal with
    | [ |- context[(fun x : ?T => PTVar x)] ] =>
      rewrite (eta_eq (@PTVar T))
  end.

Ltac my_simpler := repeat progress (equation; fold ptypeDenote in *;
  fold cpsType in *; try my_changer).

Section subst.
  Open Local Scope cps_scope.

  Theorem cpsSubst : forall tvar (t1 : tvar -> type tvar) (t2 t1' : type tvar),
    Subst t1 t2 t1'
    -> PSubst (fun x => cpsType (t1 x)) (cpsType t2) (cpsType t1').
    induction 1; my_simpler.
  Defined.

  Theorem cpsSubst_double_cont : forall tvar (t1 : tvar -> type tvar) (t2 t1' : type tvar),
    Subst t1 t2 t1'
    -> PSubst (fun x => cpsType (t1 x) ---> --->) (cpsType t2) (cpsType t1' ---> --->).
    Hint Resolve cpsSubst.
    auto.
  Defined.
End subst.

(** ** Translating terms *)

Section splice.
  Open Local Scope cps_scope.

  Fixpoint splice tvar (var : ptype tvar -> Type) (result1 result2 : ptype tvar)
    (e1 : pterm var result1) (e2 : var result1 -> pterm var result2) {struct e1} : pterm var result2 :=
    match e1 with
      | PHalt v => e2 v
      | PApp _ f x => f @@@ x
      | PBind _ p e' => x <- splicePrim p e2; splice (e' x) e2
    end

  with splicePrim tvar (var : ptype tvar -> Type) (result1 result2 : ptype tvar)
    t (p : pprimop var result1 t) (e2 : var result1 -> pterm var result2) {struct p} : pprimop var result2 t :=
    match p in (pprimop _ _ t) return (pprimop var result2 t) with
      | PVar _ v => #v

      | PTrue => Tru
      | PFalse => Fals

      | PAbs _ e => \x, splice (e x) e2

      | PPair _ _ v1 v2 => [v1, v2]

      | PFst _ _ v => #1 v
      | PSnd _ _ v => #2 v

      | PTApp _ v _ _ Hsub => PTApp v _ Hsub
      | PTAbs _ p' => \\T, splicePrim (p' T) e2
    end.
End splice.

Notation "x <-- e1 ; e2" := (splice e1 (fun x => e2))
  (right associativity, at level 76, e1 at next level) : cps_scope.
Notation "! <-- e1 ; e2" := (splice e1 (fun _ => e2))
  (right associativity, at level 76, e1 at next level) : cps_scope.

Section cpsTerm.
  Variable tvar : Type.
  Variable var : ptype tvar -> Type.

  Notation var' := (fun t => var (cpsType t)).

  Open Local Scope cps_scope.

  Fixpoint cpsTerm t (e : term var' t) {struct e} : pterm var (cpsType t) :=
    match e in (term _ t) return (pterm var (cpsType t)) with
      | EVar _ v => PHalt (var := var) v

      | ETrue =>
        x <- Tru;
        Halt x
      | EFalse =>
        x <- Fals;
        Halt x

      | EApp _ _ e1 e2 =>
        f <-- cpsTerm e1;
        x <-- cpsTerm e2;
        k <- \r, PHalt (var := var) r;
        p <- [x, k];
        f @@@ p
      | EAbs _ _ e' =>
        f <- PAbs (var := var) (fun p =>
          x <- #1 p;
          k <- #2 p;
          r <-- cpsTerm (e' x);
          k @@@ r);
        Halt f

      | ETApp _ e' t' _ Hsub =>
        f <-- cpsTerm e';
        fi <- PTApp f _ (cpsSubst_double_cont Hsub);
        k <- \r, Halt r;
        fi @@@ k
      | ETAbs _ e' =>
        r <- \\T, \k,
          v <-- cpsTerm (e' T);
          k @@@ v;
        Halt r
    end.
End cpsTerm.

Implicit Arguments cpsTerm [tvar var t].
Definition CpsTerm t (E : Term t) : Pterm (fun _ => cpsType (t _)) :=
  fun _ _ => cpsTerm (E _ _).


(** * Correctness *)

Scheme pterm_mut := Induction for pterm Sort Prop
with pprimop_mut := Induction for pprimop Sort Prop.

Section splice_correct.
  Variables result1 result2 : ptype Set.

  Variable e2 : ptypeDenote result1 -> pterm ptypeDenote result2.

  Theorem splice_correct : forall e1 k,
    ptermDenote (splice e1 e2) k
    = ptermDenote e1 (fun r => ptermDenote (e2 r) k).
    apply (pterm_mut
      (fun e1 => forall k,
        ptermDenote (splice e1 e2) k
        = ptermDenote e1 (fun r => ptermDenote (e2 r) k))
      (fun t p => forall k,
        pprimopDenote (splicePrim p e2) k
        = pprimopDenote p (fun r => ptermDenote (e2 r) k)));
    equation.
  Qed.
End splice_correct.

Record tvars : Type := {
  source : Set;
  cps : Set;
  rel : source -> cps -> Prop
}.

Fixpoint lr (t : type tvars) (t1 t2 : type Set) {struct t} : typeDenote t1 -> ptypeDenote (cpsType t2) -> Prop :=
  match t, t1, t2 return (typeDenote t1 -> ptypeDenote (cpsType t2) -> Prop) with
    | Bool, Bool, Bool => fun b1 b2 => b1 = b2

    | ^R, ^_, ^_ => fun v1 v2 => exists Heq1, exists Heq2, rel R (v1 :? Heq1) (v2 :? Heq2)

    | domR --> ranR, dom1 --> ran1, dom2 --> ran2 => fun f1 f2 =>
      forall x1 x2, lr domR _ _ x1 x2
        -> forall k, exists r,
          f2 (x2, k) = k r
          /\ lr ranR _ _ (f1 x1) r

    | TAll ranR, TAll ran1, TAll ran2 => fun f1 f2 =>
      forall (T1 T2 : Set) (R : T1 -> T2 -> Prop) k, exists r,
        f2 T2 k = k r
        /\ lr (ranR (Build_tvars R)) _ _ (f1 T1) r

    | _, _, _ => fun _ _ => False
  end%source.

Section equiv.
  Variables tvar1 tvar2 tvar3 : Type.

  Lemma type_equiv_permute' : forall (D : list (tvar1 * tvar2 * tvar3)) t1 t2 t3,
    type_equiv D t1 t2 t3
    -> forall D', (forall p, In p D -> In p D')
      -> type_equiv D' t1 t2 t3.
    Hint Constructors type_equiv.

    induction 1; simpler.

    constructor; simpler.
    apply H0; simpler.
  Qed.

  Lemma type_equiv_permute : forall p1 p2 (D : list (tvar1 * tvar2 * tvar3)) t1 t2 t3,
    type_equiv (p1 :: p2 :: D) t1 t2 t3
    -> type_equiv (p2 :: p1 :: D) t1 t2 t3.
    intros; eapply type_equiv_permute'; eauto; simpler.
  Qed.
End equiv.

Lemma Subst3_typeDenote2 : forall f1 f2 f3 a1 a2 a3 r1 r2 r3,
  Subst3 (tvar1 := tvars) (tvar3 := Set) f1 f2 f3 a1 a2 a3 r1 r2 r3
  -> typeDenote (f2 (typeDenote a2)) = typeDenote r2.
  induction 1; equation.
  apply ext_eq_forallS; intro; apply H; [exact (Build_tvars (fun _ _ : Empty_set => False)) | exact Empty_set].
Defined.

Lemma Subst3_typeDenote3 : forall f1 f2 f3 a1 a2 a3 r1 r2 r3,
  Subst3 (tvar1 := tvars) (tvar2 := Set) f1 f2 f3 a1 a2 a3 r1 r2 r3
  -> typeDenote (f3 (typeDenote a3)) = typeDenote r3.
  induction 1; equation.
  apply ext_eq_forallS; intro; apply H; [exact (Build_tvars (fun _ _ : Empty_set => False)) | exact Empty_set].
Defined.

Lemma cpsSubst3_2 : forall f1 f2 f3 a1 a2 a3 r1 r2 r3,
  Subst3 (tvar1 := tvars) (tvar2 := Set) (tvar3 := Set) f1 f2 f3 a1 a2 a3 r1 r2 r3
  -> PSubst (fun x => cpsType (f2 x)) (cpsType a2) (cpsType r2).
  induction 1; my_simpler.
  repeat constructor; apply H; [exact (Build_tvars (fun _ _ : Empty_set => False)) | exact Empty_set].
Defined.

Lemma cpsSubst3_3 : forall f1 f2 f3 a1 a2 a3 r1 r2 r3,
  Subst3 (tvar1 := tvars) (tvar2 := Set) (tvar3 := Set) f1 f2 f3 a1 a2 a3 r1 r2 r3
  -> PSubst (fun x => cpsType (f3 x)) (cpsType a3) (cpsType r3).
  induction 1; my_simpler.
  repeat constructor; apply H; [exact (Build_tvars (fun _ _ : Empty_set => False)) | exact Empty_set].
Defined.

Lemma lr_subst' : forall (tf1 : tvars -> type tvars) (targ1 tres1 : type tvars)
  (tf2 : Set -> type Set) (targ2 tres2 : type Set)
  (tf3 : Set -> type Set) (targ3 tres3 : type Set),
  Subst3 tf1 tf2 tf3 targ1 targ2 targ3 tres1 tres2 tres3
  -> forall D, (forall T1 T2 T3, type_equiv ((T1, T2, T3) :: D) (tf1 T1) (tf2 T2) (tf3 T3))
    -> forall v1 v2 Heq1 Heq2,
      (lr (tf1 (Build_tvars (lr targ1 targ2 targ3))) 
        (tf2 (typeDenote targ2)) (tf3 (ptypeDenote (cpsType targ3)))
        v1 v2
        <-> lr tres1 tres2 tres3 (v1 :? Heq1) (v2 :? Heq2)).
  Hint Extern 1 False =>
    match goal with
      | [ H : forall (T1 : tvars) (T2 T3 : Set),
        type_equiv ((T1, T2, T3) :: _) _ _ _ |- _ ] =>
      generalize (H (Build_tvars (fun (_ _ : bool) => False)) unit unit);
        clear H; intro H; inversion H; fail
    end.

  induction 1; my_simpler.

  (* Var *)

  exists (refl_equal (typeDenote t2)).
  exists (refl_equal (ptypeDenote (cpsType t3))).
  simpler.

  (* Arrow, -> *)

  generalize (IHX1 D); clear IHX1; intro IHX1.
  match type of IHX1 with
    | ?P -> _ => assert P
  end; simpler.
  generalize (H T1 T2 T3); inversion 1; assumption.

  generalize (H3 (x1 :? sym_eq (Subst3_typeDenote2 X1))
    (x2 :? sym_eq (PSubst_ptypeDenote (cpsSubst3_3 X1)))
    (Subst3_typeDenote2 X1)
    (PSubst_ptypeDenote (cpsSubst3_3 X1))).
  simpler.
  repeat match goal with
           | [ H : context[_ :? ?PF] |- _ ] => rewrite (UIP_refl _ _ PF) in H; simpler
         end.

  generalize (H0 _ _ H4 (fun v => k (v :? PSubst_ptypeDenote (cpsSubst3_3 X2))));
    clear H0; intro Hlr.
  simpler.
  exists (x :? PSubst_ptypeDenote (cpsSubst3_3 X2)); simpler.
  generalize H5; clear_all.
  generalize v2 x2 k x.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq2.
  rewrite (PSubst_ptypeDenote (cpsSubst3_3 X1)).
  rewrite (PSubst_ptypeDenote (cpsSubst3_3 X2)).
  simpler; rewrite (eta_eq k0) in H5; assumption.
  
  generalize (IHX2 D); clear IHX2; intro IHX2.
  match type of IHX2 with
    | ?P -> _ => assert P
  end; simpler.
  generalize (H T1 T2 T3); inversion 1; assumption.

  generalize (H8 ((v1 :? Heq1) x1 :? sym_eq (Subst3_typeDenote2 X2))
    x
    (Subst3_typeDenote2 X2)
    (PSubst_ptypeDenote (cpsSubst3_3 X2))); simpler.
  repeat match goal with
           | [ H : context[_ :? ?PF] |- _ ] => rewrite (UIP_refl _ _ PF) in H; simpler
         end.
  apply H10.
  generalize H7; clear_all.
  replace (v1 (x1 :? sym_eq (Subst3_typeDenote2 X1)))
    with ((v1 :? Heq1) x1 :? sym_eq (Subst3_typeDenote2 X2)); simpler.
  generalize v1 x1.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq1.
  rewrite (Subst3_typeDenote2 X1).
  rewrite (Subst3_typeDenote2 X2).
  simpler.

  (* Arrow, <- *)

  generalize (IHX1 D); clear IHX1; intro IHX1.
  match type of IHX1 with
    | ?P -> _ => assert P
  end; simpler.
  generalize (H T1 T2 T3); inversion 1; assumption.

  generalize (H3 x1 x2
    (Subst3_typeDenote2 X1)
    (PSubst_ptypeDenote (cpsSubst3_3 X1))).
  simpler.

  generalize (H0 _ _ H4 (fun v => k (v :? sym_eq (PSubst_ptypeDenote (cpsSubst3_3 X2)))));
    clear H0; intro Hlr.
  simpler.
  exists (x :? sym_eq (PSubst_ptypeDenote (cpsSubst3_3 X2))); simpler.
  generalize H6; clear_all.
  generalize v2 x2 k x.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq2.
  rewrite (PSubst_ptypeDenote (cpsSubst3_3 X1)).
  rewrite (PSubst_ptypeDenote (cpsSubst3_3 X2)).
  simpler; rewrite (eta_eq k0) in H6; assumption.
  
  generalize (IHX2 D); clear IHX2; intro IHX2.
  match type of IHX2 with
    | ?P -> _ => assert P
  end; simpler.
  generalize (H T1 T2 T3); inversion 1; assumption.

  generalize (H8 (v1 x1) (x :? sym_eq (PSubst_ptypeDenote (cpsSubst3_3 X2)))
    (Subst3_typeDenote2 X2)
    (PSubst_ptypeDenote (cpsSubst3_3 X2))).
  simpler.
  apply H11.
  generalize H7; clear_all.
  match goal with
    | [ |- context[_ :? ?PF] ] => rewrite (UIP_refl _ _ PF)
  end; simpl.
  replace ((v1 :? Heq1) (x1 :? Subst3_typeDenote2 X1))
    with (v1 x1 :? Subst3_typeDenote2 X2); simpler.
  generalize v1 x1.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq1.
  rewrite (Subst3_typeDenote2 X1).
  rewrite (Subst3_typeDenote2 X2).
  simpler.

  (* All, -> *)

  generalize (H1 _ _ R (fun v => k (v :? PSubst_ptypeDenote (cpsSubst3_3
    (s (Build_tvars R) T1 T2))))).
  simpler.
  exists (x :? PSubst_ptypeDenote (cpsSubst3_3 (s (Build_tvars R) T1 T2))); simpler.

  generalize H3; clear_all.
  generalize v2 k x.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq2.
  change ((forall T : Set,
    (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T)) ->
      bool) -> bool) =
  (forall T : Set,
    (ptypeDenote (cpsType (ran3' T)) -> bool) -> bool))
    with ((forall T : Set,
      ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T ->
        bool) -> bool) =
    (forall T : Set,
      ((fun T => ptypeDenote (cpsType (ran3' T))) T -> bool) -> bool)).
  change (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T2)) =
    ptypeDenote (cpsType (ran3' T2)))
    with ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T2 =
      (fun T => ptypeDenote (cpsType (ran3' T))) T2).
  change (forall T : Set,
    (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T)) ->
      bool) -> bool)
    with (forall T : Set,
    ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T ->
      bool) -> bool).
  change (ptypeDenote (cpsType (ran3' T2)))
    with ((fun T => ptypeDenote (cpsType (ran3' T))) T2).
  change (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T2)))
    with ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T2).
  replace (fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T)))
    with (fun T => ptypeDenote (cpsType (ran3' T))).
  simpler; rewrite (eta_eq k0) in H3; assumption.
  symmetry; ext_eq; exact (PSubst_ptypeDenote (cpsSubst3_3
    (s (Build_tvars (fun _ _ : Empty_set => False)) Empty_set _))).

  generalize (H (Build_tvars R) T1 T2 ((Build_tvars R, T1, T2) :: D)); clear H; intro H.
  match type of H with
    | ?P -> _ => assert P
  end; simpler.
  generalize (H0 T0 T3 T4); inversion 1; subst.
  apply type_equiv_permute; auto.

  generalize (H5 (((v1 :? Heq1) T1) :? sym_eq (Subst3_typeDenote2
    (s (Build_tvars R) T1 T2)))
    x
    (Subst3_typeDenote2 (s (Build_tvars R) T1 T2))
    (PSubst_ptypeDenote (cpsSubst3_3 (s (Build_tvars R) T1 T2)))).
  simpler.
  repeat match goal with
           | [ H : context[_ :? ?PF] |- _ ] => rewrite (UIP_refl _ _ PF) in H; simpler
         end.
  apply H6.
  generalize H4; clear_all.
  replace (v1 T1) with ((v1 :? Heq1) T1 :? sym_eq (Subst3_typeDenote2 (s (Build_tvars R) T1 T2))); simpler.
  generalize v1.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq1.
  change (forall T, typeDenote (ran2 (typeDenote arg2) T))
    with (forall T, (fun T => typeDenote (ran2 (typeDenote arg2) T)) T).
  change (forall T, typeDenote (ran2' T))
    with (forall T, (fun T => typeDenote (ran2' T)) T).
  change (typeDenote (ran2' T1))
    with ((fun T => typeDenote (ran2' T)) T1).
  change (typeDenote (ran2 (typeDenote arg2) T1))
    with ((fun T => typeDenote (ran2 (typeDenote arg2) T)) T1).
  replace (fun T => typeDenote (ran2 (typeDenote arg2) T))
    with (fun T => typeDenote (ran2' T)).
  simpler.
  symmetry; ext_eq; exact (Subst3_typeDenote2 (s (Build_tvars R) x0 T2)).

  (* All, <- *)

  generalize (H1 _ _ R (fun v => k (v :? sym_eq (PSubst_ptypeDenote (cpsSubst3_3
    (s (Build_tvars R) T1 T2)))))).
  simpler.
  exists (x :? sym_eq (PSubst_ptypeDenote (cpsSubst3_3 (s (Build_tvars R) T1 T2)))); simpler.

  generalize H3; clear_all.
  generalize v2 k x.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq2.
  change ((forall T : Set,
    (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T)) ->
      bool) -> bool) =
  (forall T : Set,
    (ptypeDenote (cpsType (ran3' T)) -> bool) -> bool))
    with ((forall T : Set,
      ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T ->
        bool) -> bool) =
    (forall T : Set,
      ((fun T => ptypeDenote (cpsType (ran3' T))) T -> bool) -> bool)).
  change (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T2)) =
    ptypeDenote (cpsType (ran3' T2)))
    with ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T2 =
      (fun T => ptypeDenote (cpsType (ran3' T))) T2).
  change (forall T : Set,
    (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T)) ->
      bool) -> bool)
    with (forall T : Set,
    ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T ->
      bool) -> bool).
  change (ptypeDenote (cpsType (ran3' T2)))
    with ((fun T => ptypeDenote (cpsType (ran3' T))) T2).
  change (ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T2)))
    with ((fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T))) T2).
  replace (fun T => ptypeDenote (cpsType (ran3 (ptypeDenote (cpsType arg3)) T)))
    with (fun T => ptypeDenote (cpsType (ran3' T))).
  simpler; rewrite (eta_eq k0) in H3; assumption.
  symmetry; ext_eq; exact (PSubst_ptypeDenote (cpsSubst3_3 (s (Build_tvars R) T1 x0))).

  generalize (H (Build_tvars R) T1 T2 ((Build_tvars R, T1, T2) :: D)); clear H; intro H.
  match type of H with
    | ?P -> _ => assert P
  end; simpler.
  generalize (H0 T0 T3 T4); inversion 1; subst.
  apply type_equiv_permute; auto.

  generalize (H5 (((v1 :? Heq1) T1) :? sym_eq (Subst3_typeDenote2 (s (Build_tvars R) T1 T2)))
    (x :? sym_eq (PSubst_ptypeDenote (cpsSubst3_3 (s (Build_tvars R) T1 T2))))
    (Subst3_typeDenote2 (s (Build_tvars R) T1 T2))
    (PSubst_ptypeDenote (cpsSubst3_3 (s (Build_tvars R) T1 T2)))).
  simpler.
  repeat match goal with
           | [ H : context[_ :? ?PF] |- _ ] => rewrite (UIP_refl _ _ PF) in H; simpler
         end.
  generalize H; clear_all.
  replace (v1 T1) with ((v1 :? Heq1) T1 :? sym_eq (Subst3_typeDenote2 (s (Build_tvars R) T1 T2))); simpler.
  generalize v1.
  repeat match goal with
           | [ |- context[_ :? ?PF] ] => generalize PF
         end.
  generalize Heq1.
  change (forall T, typeDenote (ran2 (typeDenote arg2) T))
    with (forall T, (fun T => typeDenote (ran2 (typeDenote arg2) T)) T).
  change (forall T, typeDenote (ran2' T))
    with (forall T, (fun T => typeDenote (ran2' T)) T).
  change (typeDenote (ran2' T1))
    with ((fun T => typeDenote (ran2' T)) T1).
  change (typeDenote (ran2 (typeDenote arg2) T1))
    with ((fun T => typeDenote (ran2 (typeDenote arg2) T)) T1).
  replace (fun T => typeDenote (ran2 (typeDenote arg2) T))
    with (fun T => typeDenote (ran2' T)).
  simpler.
  symmetry; ext_eq; exact (Subst3_typeDenote2 (s (Build_tvars R) x0 T2)). 
Qed.

Lemma lr_subst : forall (tf1 : tvars -> type tvars) (targ1 tres1 : type tvars)
  (tf2 : Set -> type Set) (targ2 tres2 : type Set)
  (tf3 : Set -> type Set) (targ3 tres3 : type Set),
  Subst3 tf1 tf2 tf3 targ1 targ2 targ3 tres1 tres2 tres3
  -> forall D,
    (forall T1 T2 T3, type_equiv ((T1, T2, T3) :: D) (tf1 T1) (tf2 T2) (tf3 T3))
    -> forall v1 v2 Heq1 Heq2,
      lr (tf1 (Build_tvars (lr targ1 targ2 targ3))) 
      (tf2 (typeDenote targ2)) (tf3 (ptypeDenote (cpsType targ3)))
      v1 v2
      -> lr tres1 tres2 tres3 (v1 :? Heq1) (v2 :? Heq2).
  intros.
  generalize (lr_subst' X H v1 v2 Heq1 Heq2); tauto.
Qed.

Opaque Subst_typeDenote PSubst_ptypeDenote.

Lemma cpsTerm_correct : forall (D : list (tvars * Set * Set)) G tR t1 t2
  (eR : term (fun _ => unit) tR)
  (e1 : term typeDenote t1)
  (e2 : term (fun t => ptypeDenote (cpsType t)) t2),
  term_equiv D G eR e1 e2
  -> (forall tR t1 t2 (vR : (fun _ => unit) tR) v1 v2, In (vars3 vR v1 v2) G -> lr tR t1 t2 v1 v2)
  -> forall k, exists r,
    ptermDenote (cpsTerm e2) k = k r
    /\ lr tR t1 t2 (termDenote e1) r.
  Hint Resolve lr_subst.

  Hint Rewrite splice_correct : ltamer.

  Hint Extern 1 (lr _ _ _) => push_vars.

  Ltac my_equation := repeat progress (equation; fold ptypeDenote in *;
    fold cpsType in *; fold typeDenote in *; try my_changer).

  Ltac my_chooser T k :=
    match T with
      | type _ => fail 1
      | ctxt _ _ => fail 1
      | bool => fail 1

      | Set => fail 1

      | _ => default_chooser T k
    end.

  Ltac my_matching := matching my_equation my_chooser.

  induction 1.

  my_matching; eauto.

  my_matching; eauto.
  my_matching; eauto.

  my_matching.

  my_matching.

  rewrite (eta_eq k0).
  apply H2 with tt; simpler.
  eauto.

  my_matching.

  generalize (H5 _ _ (lr targ1 targ2 targ3) (fun v => k (v :? PSubst_ptypeDenote (cpsSubst Hsub3))));
    clear H5; intro IH.
  firstorder.
  exists (x0 :? PSubst_ptypeDenote (cpsSubst Hsub3)).
  simpler.

  rewrite <- H3.
  generalize (x (ptypeDenote (cpsType targ3))).
  generalize (PSubst_ptypeDenote (cpsSubst_double_cont Hsub3)).
  generalize (PSubst_ptypeDenote (cpsSubst Hsub3)).
  simpl.
  rewrite (PSubst_ptypeDenote (cpsSubst Hsub3)).
  simpler.
  eauto.

  my_matching.
  rewrite (eta_eq k0).
  my_matching.
Qed.

Theorem CpsTerm_correct : forall (E : Term (fun _ => TBool)) k,
  PtermDenote (CpsTerm E) k = k (TermDenote E).
  intros.
  generalize (cpsTerm_correct (D := nil) (G := nil) (tR := Bool) (t1 := Bool) (t2 := Bool)
    (eR := E _ _) (e1 := E _ _) (e2 := E _ _) (Term_equiv E _ _ _)
    (fun _ _ _ _ _ _ Hin => False_ind _ Hin) k).
  simpler.
Qed.
