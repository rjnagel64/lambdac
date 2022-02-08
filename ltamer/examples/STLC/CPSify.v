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

Set Implicit Arguments.


(** * CPS translation *)

(** ** Translating types *)

Fixpoint cpsType (t : type) : ptype :=
  match t with
    | Bool => Bool%cps
    | t1 --> t2 => (cpsType t1 ** (cpsType t2 --->) --->)%cps
  end%source.

(** ** Translating terms *)

Section splice.
  Open Local Scope cps_scope.

  Fixpoint splice (var : ptype -> Type) (result1 result2 : ptype) (e1 : pterm var result1) (e2 : var result1 -> pterm var result2) {struct e1} : pterm var result2 :=
    match e1 with
      | PHalt v => e2 v
      | PApp _ f x => f @@ x
      | PBind _ p e' => x <- splicePrim p e2; splice (e' x) e2
    end

  with splicePrim (var : ptype -> Type) (result1 result2 : ptype) t (p : pprimop var result1 t) (e2 : var result1 -> pterm var result2) {struct p} : pprimop var result2 t :=
    match p in (pprimop _ _ t) return (pprimop var result2 t) with
      | PVar _ v => #v

      | PTrue => Tru
      | PFalse => Fals

      | PAbs _ e => \x, splice (e x) e2

      | PPair _ _ v1 v2 => [v1, v2]

      | PFst _ _ v => #1 v
      | PSnd _ _ v => #2 v
    end.
End splice.

Notation "x <-- e1 ; e2" := (splice e1 (fun x => e2))
  (right associativity, at level 76, e1 at next level) : cps_scope.
Notation "! <-- e1 ; e2" := (splice e1 (fun _ => e2))
  (right associativity, at level 76, e1 at next level) : cps_scope.

Section cpsTerm.
  Variable var : ptype -> Type.

  Notation var' := (fun t => var (cpsType t)).

  Open Local Scope cps_scope.

  Fixpoint cpsTerm t (e : term var' t) {struct e} : pterm var (cpsType t) :=
    match e in (term _ t) return (pterm var (cpsType t)) with
      | EVar _ v => PHalt (var := var) v

      | ETrue => x <- Tru; Halt x
      | EFalse => x <- Fals; Halt x

      | EApp _ _ e1 e2 =>
        f <-- cpsTerm e1;
        x <-- cpsTerm e2;
        k <- \r, PHalt (var := var) r;
        p <- [x, k];
        f @@ p
      | EAbs _ _ e' =>
        f <- PAbs (var := var) (fun p =>
          x <- #1 p;
          k <- #2 p;
          r <-- cpsTerm (e' x);
          k @@ r);
        Halt f
    end.
End cpsTerm.

Implicit Arguments cpsTerm [var t].
Definition CpsTerm t (E : Term t) : Pterm (cpsType t) := fun _ => cpsTerm (E _).


(** * Correctness *)

Scheme pterm_mut := Induction for pterm Sort Prop
with pprimop_mut := Induction for pprimop Sort Prop.

Section splice_correct.
  Variables result1 result2 : ptype.

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

Fixpoint lr (t : type) : typeDenote t -> ptypeDenote (cpsType t) -> Prop :=
  match t return (typeDenote t -> ptypeDenote (cpsType t) -> Prop) with
    | TBool => fun n1 n2 => n1 = n2
    | TArrow t1 t2 => fun f1 f2 =>
      forall x1 x2, lr _ x1 x2
        -> forall k, exists r,
          f2 (x2, k) = k r
          /\ lr _ (f1 x1) r
  end.

Lemma cpsTerm_correct : forall G t (e1 : term _ t) (e2 : term _ t),
  term_equiv G e1 e2
  -> (forall t v1 v2, In (vars (v1, v2)) G -> lr t v1 v2)
  -> forall k, exists r,
    ptermDenote (cpsTerm e2) k = k r
    /\ lr t (termDenote e1) r.
  Hint Rewrite splice_correct : ltamer.

  Ltac my_changer :=
    match goal with
      [ H : (forall (t : _) (v1 : _) (v2 : _), vars _ = vars _ \/ In _ _ -> _) -> _ |- _ ] =>
      match typeof H with
        | ?P -> _ =>
          assert P; [intros; push_vars; intuition; fail 2
            | idtac]
      end
    end.

  Ltac my_simpler := repeat progress (equation; fold ptypeDenote in *;
    fold cpsType in *; try my_changer).

  Ltac my_chooser T k :=
    match T with
      | bool => fail 1
      | type => fail 1
      | ctxt _ _ => fail 1
      | _ => default_chooser T k
    end.

  induction 1; matching my_simpler my_chooser; eauto.
Qed.

Theorem CpsTerm_correct : forall t (E : Term t),
  forall k, exists r,
    PtermDenote (CpsTerm E) k = k r
    /\ lr t (TermDenote E) r.
  unfold PtermDenote, TermDenote, CpsTerm; simpl; intros.
  eapply (cpsTerm_correct (G := nil)); simpl; intuition.
  apply Term_equiv.
Qed.

Theorem CpsTerm_correct_bool : forall (E : Term TBool),
  forall k, PtermDenote (CpsTerm E) k = k (TermDenote E).
  intros.
  generalize (CpsTerm_correct E k); firstorder congruence.
Qed.
