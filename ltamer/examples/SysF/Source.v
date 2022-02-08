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

Set Implicit Arguments.


Section vars.
  Variable tvar : Type.

  Inductive type : Type :=
  | TBool : type
  | TVar : tvar -> type
  | TArrow : type -> type -> type
  | TAll : (tvar -> type) -> type.

  Notation "^ v" := (TVar v) (at level 60).
  Infix "-->" := TArrow (right associativity, at level 61).

  Inductive Subst : (tvar -> type) -> type -> type -> Type :=
  | SBool : forall t, Subst (fun _ => TBool) t TBool
  | SVarEq : forall t, Subst TVar t t
  | SVarNeq : forall (v : tvar) t, Subst (fun _ => ^v) t (^v)
  | SArrow : forall t1 t2 t1' t2' t,
    Subst t1 t t1'
    -> Subst t2 t t2'
    -> Subst (fun v => t1 v --> t2 v) t (t1' --> t2')
  | SAll : forall t1 t1' t,
    (forall v', Subst (fun v => t1 v v') t (t1' v'))
    -> Subst (fun v => TAll (t1 v)) t (TAll t1').

  Lemma SVarEq' : forall t, Subst (fun T => TVar T) t t.
    intros; rewrite (eta_eq TVar); apply SVarEq.
  Qed.

  Variable var : type -> Type.

  Inductive term : type -> Type :=
  | EVar : forall t,
    var t
    -> term t

  | ETrue : term TBool
  | EFalse : term TBool

  | EApp : forall t1 t2,
    term (t1 --> t2)
    -> term t1
    -> term t2
  | EAbs : forall t1 t2,
    (var t1 -> term t2)
    -> term (t1 --> t2)

  | ETApp : forall t1,
    term (TAll t1)
    -> forall t2 t1',
      Subst t1 t2 t1'
      -> term t1'
  | ETAbs : forall t1,
    (forall v, term (t1 v))
    -> term (TAll t1).
End vars.

Hint Constructors Subst.
Hint Resolve SVarEq'.

Implicit Arguments TBool [tvar].

Notation "^ v" := (TVar v) (at level 60) : source_scope.
Notation "'Bool'" := TBool : source_scope.
Infix "-->" := TArrow (right associativity, at level 61) : source_scope.
Notation "'All' x , t" := (TAll (fun x => t)) (no associativity, at level 62) : source_scope.
Notation "'All' ! , t" := (TAll (fun _ => t)) (no associativity, at level 62) : source_scope.

Bind Scope source_scope with type.
Delimit Scope source_scope with source.

Implicit Arguments EVar [tvar var t].
Implicit Arguments ETrue [tvar var].
Implicit Arguments EFalse [tvar var].
Implicit Arguments EApp [tvar var t1 t2].
Implicit Arguments EAbs [tvar var t1 t2].
Implicit Arguments ETApp [tvar var t1 t1'].
Implicit Arguments ETAbs [tvar var t1].

Notation "# v" := (EVar v) (at level 62) : source_scope.
Notation "'Tru'" := ETrue : source_scope.
Notation "'Fals'" := EFalse : source_scope.
Infix "@" := EApp (left associativity, at level 77) : source_scope.
Notation "\ x , e" := (EAbs (fun x => e)) (at level 78) : source_scope.
Notation "\ ! , e" := (EAbs (fun _ => e)) (at level 78) : source_scope.
Notation "e @@ t" := (ETApp e t _) (left associativity, at level 77) : source_scope.
Notation "\\ T , e" := (ETAbs (fun T => e)) (at level 78) : source_scope.
Notation "\\ ! , e" := (ETAbs (fun _ => e)) (at level 78) : source_scope.

Open Local Scope source_scope.


Fixpoint typeDenote (t : type Set) {struct t} : Set :=
  match t with
    | Bool => bool
    | TVar v => v
    | t1 --> t2 => typeDenote t1 -> typeDenote t2
    | TAll t' => forall T, typeDenote (t' T)
  end.

Theorem ext_eq_forallS : forall T (f1 f2 : T -> Set),
  (forall x, f1 x = f2 x)
  -> (forall T, f1 T) = (forall T, f2 T).
  intros; rewrite (ext_eq _ _ H); trivial.
Defined.

Theorem Subst_typeDenote : forall t1 t2 t1',
  Subst t1 t2 t1'
  -> typeDenote (t1 (typeDenote t2)) = typeDenote t1'.
  induction 1; equation; apply ext_eq_forallS; auto.
Defined.

Fixpoint termDenote t (e : term typeDenote t) {struct e} : typeDenote t :=
  match e in (term _ t) return (typeDenote t) with
    | EVar _ v => v

    | ETrue => true
    | EFalse => false

    | EApp _ _ e1 e2 => (termDenote e1) (termDenote e2)
    | EAbs _ _ e' => fun x => termDenote (e' x)

    | ETApp _ e' t _ Hsubst => (termDenote e') (typeDenote t) :? Subst_typeDenote Hsubst
    | ETAbs _ e' => fun T => termDenote (e' T)
  end.

Definition Typ := forall tvar, type tvar.
Definition Term t := forall tvar (var : type tvar -> Type), term var (t tvar).

Definition TypDenote (T : Typ) := typeDenote (T _).
Definition TermDenote T (E : Term T) := termDenote (E _ _).


(** * Type and term equivalence *)

Section equiv.
  Variables tvar1 tvar2 tvar3 : Type.

  Inductive type_equiv : list (tvar1 * tvar2 * tvar3) -> type tvar1 -> type tvar2 -> type tvar3 -> Prop :=
  | EqBool : forall D, type_equiv D Bool Bool Bool
  | EqVar : forall D T1 T2 T3, In (T1, T2, T3) D -> type_equiv D (^T1) (^T2) (^T3)
  | EqArrow : forall D dom1 ran1 dom2 ran2 dom3 ran3,
    type_equiv D dom1 dom2 dom3
    -> type_equiv D ran1 ran2 ran3
    -> type_equiv D (dom1 --> ran1) (dom2 --> ran2) (dom3 --> ran3)
  | EqAll : forall D ran1 ran2 ran3,
    (forall T1 T2 T3, type_equiv ((T1, T2, T3) :: D) (ran1 T1) (ran2 T2) (ran3 T3))
    -> type_equiv D (TAll ran1) (TAll ran2) (TAll ran3).

  Inductive Subst3 : (tvar1 -> type tvar1) -> (tvar2 -> type tvar2) -> (tvar3 -> type tvar3)
    -> type tvar1 -> type tvar2 -> type tvar3
    -> type tvar1 -> type tvar2 -> type tvar3 -> Type :=
  | S3Bool : forall t1 t2 t3, Subst3 (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) t1 t2 t3 Bool Bool Bool
  | S3VarEq : forall t1 t2 t3, Subst3 (@TVar _) (@TVar _) (@TVar _) t1 t2 t3 t1 t2 t3
  | S3VarNeq : forall (v1 : tvar1) (v2 : tvar2) (v3 : tvar3) t1 t2 t3,
    Subst3 (fun _ => ^v1) (fun _ => ^v2) (fun _ => ^v3) t1 t2 t3 (^v1) (^v2) (^v3)
  | S3Arrow : forall dom1 dom2 dom3 ran1 ran2 ran3 arg1 arg2 arg3 dom1' dom2' dom3' ran1' ran2' ran3',
    Subst3 dom1 dom2 dom3 arg1 arg2 arg3 dom1' dom2' dom3'
    -> Subst3 ran1 ran2 ran3 arg1 arg2 arg3 ran1' ran2' ran3'
    -> Subst3 (fun v => dom1 v --> ran1 v) (fun v => dom2 v --> ran2 v) (fun v => dom3 v --> ran3 v)
    arg1 arg2 arg3 (dom1' --> ran1') (dom2' --> ran2') (dom3' --> ran3')
  | S3All : forall ran1 ran2 ran3 arg1 arg2 arg3 ran1' ran2' ran3',
    (forall v1 v2 v3, Subst3 (fun v => ran1 v v1) (fun v => ran2 v v2) (fun v => ran3 v v3)
      arg1 arg2 arg3 (ran1' v1) (ran2' v2) (ran3' v3))
    -> Subst3 (fun v => TAll (ran1 v)) (fun v => TAll (ran2 v)) (fun v => TAll (ran3 v))
    arg1 arg2 arg3 (TAll ran1') (TAll ran2') (TAll ran3').

  Variable var1 : type tvar1 -> Type.
  Variable var2 : type tvar2 -> Type.
  Variable var3 : type tvar3 -> Type.

  Inductive term_equiv : forall D : list (tvar1 * tvar2 * tvar3), ctxt3 var1 var2 var3
    -> forall t1 t2 t3, term var1 t1 -> term var2 t2 -> term var3 t3 -> Prop :=
  | EqEVar : forall D G t1 t2 t3 (v1 : var1 t1) (v2 : var2 t2) (v3 : var3 t3),
    type_equiv D t1 t2 t3
    -> In (vars3 v1 v2 v3) G
    -> term_equiv (D := D) G (#v1) (#v2) (#v3)

  | EqETrue : forall D G, term_equiv (D := D) G Tru Tru Tru
  | EqEFalse : forall D G, term_equiv (D := D) G Fals Fals Fals

  | EqEApp : forall D G dom1 ran1 dom2 ran2 dom3 ran3
    (f1 : term _ (dom1 --> ran1)) (x1 : term _ dom1)
    (f2 : term _ (dom2 --> ran2)) (x2 : term _ dom2)
    (f3 : term _ (dom3 --> ran3)) (x3 : term _ dom3),
    type_equiv D dom1 dom2 dom3
    -> type_equiv D ran1 ran2 ran3
    -> term_equiv (D := D) G f1 f2 f3
    -> term_equiv (D := D) G x1 x2 x3
    -> term_equiv (D := D) G (f1 @ x1) (f2 @ x2) (f3 @ x3)
  | EqEAbs : forall D G dom1 ran1 dom2 ran2 dom3 ran3
    (f1 : var1 dom1 -> term var1 ran1)
    (f2 : var2 dom2 -> term var2 ran2)
    (f3 : var3 dom3 -> term var3 ran3),
    type_equiv D dom1 dom2 dom3
    -> type_equiv D ran1 ran2 ran3
    -> (forall v1 v2 v3, term_equiv (D := D) (vars3 v1 v2 v3 :: G) (f1 v1) (f2 v2) (f3 v3))
    -> term_equiv (D := D) G (EAbs f1) (EAbs f2) (EAbs f3)

  | EqETApp : forall D G tf1 targ1 tres1 tf2 targ2 tres2 tf3 targ3 tres3
    (e1 : term var1 (TAll tf1)) (e2 : term var2 (TAll tf2)) (e3 : term var3 (TAll tf3))
    (Hsub1 : Subst tf1 targ1 tres1) (Hsub2 : Subst tf2 targ2 tres2) (Hsub3 : Subst tf3 targ3 tres3),
    (forall T1 T2 T3, type_equiv ((T1, T2, T3) :: D) (tf1 T1) (tf2 T2) (tf3 T3))
    -> term_equiv (D := D) G e1 e2 e3
    -> type_equiv D targ1 targ2 targ3
    -> Subst3 tf1 tf2 tf3 targ1 targ2 targ3 tres1 tres2 tres3
    -> term_equiv (D := D) G (ETApp e1 targ1 Hsub1) (ETApp e2 targ2 Hsub2) (ETApp e3 targ3 Hsub3)
  | EqETAbs : forall D G ran1 ran2 ran3
    (f1 : forall T, term var1 (ran1 T))
    (f2 : forall T, term var2 (ran2 T))
    (f3 : forall T, term var3 (ran3 T)),
    (forall T1 T2 T3, type_equiv ((T1, T2, T3) :: D) (ran1 T1) (ran2 T2) (ran3 T3))
    -> (forall T1 T2 T3, term_equiv (D := (T1, T2, T3) :: D) G (f1 T1) (f2 T2) (f3 T3))
    -> term_equiv (D := D) G (ETAbs f1) (ETAbs f2) (ETAbs f3).
End equiv.

Axiom Typ_equiv : forall (T : Typ) tvar1 tvar2 tvar3,
  type_equiv nil (T tvar1) (T tvar2) (T tvar3).
Axiom Term_equiv : forall T (E : Term T) tvar1 tvar2 tvar3
  (var1 : type tvar1 -> Type) (var2 : type tvar2 -> Type) (var3 : type tvar3 -> Type),
  term_equiv nil nil (E _ var1) (E _ var2) (E _ var3).
