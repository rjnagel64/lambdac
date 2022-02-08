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
    | Unit => Unit%cps
    | t1 ** t2 => (cpsType t1 ** cpsType t2)%cps
    | t1 ++ t2 => (cpsType t1 ++ cpsType t2)%cps
    | Nat => Nat%cps
    | List t => (List (cpsType t))%cps
  end%source.

(** ** Translating terms *)

Section splice.
  Open Local Scope cps_scope.

  Fixpoint splice (var : ptype -> Type) (result1 result2 : ptype) (e1 : pterm var result1)
    (e2 : var result1 -> pterm var result2) {struct e1} : pterm var result2 :=
    match e1 with
      | PHalt v => e2 v
      | PApp _ f x => f @@ x
      | PBind _ p e' => x <- splicePrim p e2; splice (e' x) e2
      | PCase _ _ x a1 a2 => Case x of y1 ==> splice (a1 y1) e2 ||| y2 ==> splice (a2 y2) e2
      | PNatCase x a1 a2 => NatCase x of splice a1 e2 ||| y2 ==> splice (a2 y2) e2
    end

  with splicePrim (var : ptype -> Type) (result1 result2 : ptype) t (p : pprimop var result1 t)
    (e2 : var result1 -> pterm var result2) {struct p} : pprimop var result2 t :=
    match p in (pprimop _ _ t) return (pprimop var result2 t) with
      | PVar _ v => #v

      | PTrue => Tru
      | PFalse => Fals

      | PAbs _ e => \x, splice (e x) e2

      | PUnitIntro => ()

      | PPair _ _ v1 v2 => [v1, v2]
      | PFst _ _ v => #1 v
      | PSnd _ _ v => #2 v

      | PInl _ _ v => Inl v
      | PInr _ _ v => Inr v

      | PO => ^O
      | PS v => ^S v

      | PNil _ => Nil
      | PCons _ x1 x2 => x1 ::: x2
      | PFold _ _ => Fold
    end.
End splice.

Notation "x <-- e1 ; e2" := (splice e1 (fun x => e2))
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

      | EUnit =>
        x <- ();
        Halt x

      | EPair _ _ e1 e2 =>
        x1 <-- cpsTerm e1;
        x2 <-- cpsTerm e2;
        p <- [x1, x2];
        Halt p
      | EFst _ _ e' =>
        x <-- cpsTerm e';
        x1 <- #1 x;
        Halt x1
      | ESnd _ _ e' =>
        x <-- cpsTerm e';
        x2 <- #2 x;
        Halt x2

      | EInl _ _ e' =>
        x <-- cpsTerm e';
        s <- Inl x;
        Halt s
      | EInr _ _ e' =>
        x <-- cpsTerm e';
        s <- Inr x;
        Halt s
      | ECase _ _ _ e' e1 e2 =>
        x <-- cpsTerm e';
        Case x of
            y1 ==> cpsTerm (e1 y1)
        ||| y2 ==> cpsTerm (e2 y2)

      | EO =>
        x <- ^O;
        Halt x
      | ES e =>
        x <-- cpsTerm e;
        x' <- ^S x;
        Halt x'
      | ENatCase _ e' e1 e2 =>
        x <-- cpsTerm e';
        NatCase x of
                   cpsTerm e1
        ||| y2 ==> cpsTerm (e2 y2)

      | ENil _ =>
        x <- Nil;
        Halt x
      | ECons _ e1 e2 =>
        h <-- cpsTerm e1;
        t <-- cpsTerm e2;
        x <- h ::: t;
        Halt x
      | EFold _ _ =>
        fold <- \p1,
          f <- #1 p1;
          k1 <- #2 p1;

          f' <- \fp1,
            ak <- #2 fp1;
            fp2 <- #1 fp1;
            ast <- #2 fp2;
            al <- #1 fp2;

            fa1 <- \ak1,
              p <- [ast, ak];
              ak1 @@ p;

            p <- [al, fa1];
            f @@ p;
          
          a1 <- \p2,
            s <- #1 p2;
            k2 <- #2 p2;

            a2 <- \p3,
              l <- #1 p3;
              k3 <- #2 p3;

              xfold <- Fold;

              fa1 <- [f', s];
              fa2 <- [fa1, l];
              fa3 <- [fa2, k3];

              xfold @@ fa3;

            k2 @@ a2;

          k1 @@ a1;

        Halt fold
    end.
End cpsTerm.

Implicit Arguments cpsTerm [var t].
Definition CpsTerm t (E : Term t) : Pterm (cpsType t) := fun _ => cpsTerm (E _).


(** * Correctness *)

Ltac my_changer :=
  match goal with
    [ H : (forall (t : _) (v1 : _) (v2 : _), vars _ = vars _ \/ In _ _ -> _) -> _ |- _ ] =>
      match typeof H with
        | ?P -> _ =>
          assert P; [intros; push_vars; simpler; fail 2
            | idtac]
      end

    | [ |- context[match ?E with inl _ => _ | inr _ => _ end] ] => destruct E
    | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E

    | [ H : context[match ?E with nil => _ | _ :: _ => _ end] |- _ ] => destruct E
  end.

Ltac my_simpler := repeat progress (equation; fold typeDenote in *; fold ptypeDenote in *;
  fold cpsType in *; try my_changer).

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
    my_simpler.
  Qed.
End splice_correct.

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

Fixpoint lr (t : type) : typeDenote t -> ptypeDenote (cpsType t) -> Prop :=
  match t return (typeDenote t -> ptypeDenote (cpsType t) -> Prop) with
    | Bool => fun b1 b2 => b1 = b2
    | t1 --> t2 => fun f1 f2 =>
      forall x1 x2, lr _ x1 x2
        -> forall k, exists r,
          f2 (x2, k) = k r
          /\ lr _ (f1 x1) r
    | Unit => fun _ _ => True
    | t1 ** t2 => fun p1 p2 =>
      lr t1 (fst p1) (fst p2)
      /\ lr t2 (snd p1) (snd p2)
    | t1 ++ t2 => fun s1 s2 =>
      match s1, s2 with
        | inl x1, inl x2 => lr t1 x1 x2
        | inr x1, inr x2 => lr t2 x1 x2
        | _, _ => False
      end
    | Nat => fun n1 n2 => n1 = n2
    | List t' => All2 (lr t')
  end%source.

Section cpsFold_correct.
  Variables Tst Tls Tcst Tcls : Set.

  Variable f : Tst -> Tls -> Tst.
  Variable cf : Tcls * Tcst * (Tcst -> bool) -> bool.

  Variable Rst : Tst -> Tcst -> Prop.
  Variable Rls : Tls -> Tcls -> Prop.

  Hypothesis fR : forall st el cst cel ck,
    Rls el cel
    -> Rst st cst
    -> exists r, cf (cel, cst, ck) = ck r
      /\ Rst (f st el) r.

  Lemma cpsFold_correct : forall ls st cls cst ck,
    All2 Rls ls cls
    -> Rst st cst
    -> exists r : Tcst,
      kfold_left cf cst cls ck = ck r
      /\ Rst (fold_left f ls st) r.
    induction ls; my_simpler; [
      eauto
      | match goal with
          | [ HRls : Rls _ _, HRst : Rst _ _ |- context[?F] ] =>
            generalize (fR F HRls HRst)
        end; my_simpler
    ].
  Qed.
End cpsFold_correct.

Lemma cpsTerm_correct : forall G t (e1 : term _ t) (e2 : term _ t),
  term_equiv G e1 e2
  -> (forall t v1 v2, In (vars (v1, v2)) G -> lr t v1 v2)
  -> forall k, exists r,
    ptermDenote (cpsTerm e2) k = k r
    /\ lr t (termDenote e1) r.
  Hint Rewrite splice_correct : ltamer.

  Ltac my_chooser T k :=
    match T with
      | bool => fail 1
      | type => fail 1
      | ctxt _ _ => fail 1

      | list _ -> bool =>
        match goal with
          | [ |- context[_ :: _] ] =>
            match goal with
              | [ k' : _, x : _ |- _ ] =>
                k (fun r => k' (x :: r))
            end
        end
      | list _ -> bool => fail 1

      | _ =>
        match goal with
          | [ |- exists r, kfold_left _ _ _ _ = _ _ /\ lr _ _ _ ] => fail 2
          | _ => default_chooser T k
        end
    end.

  Ltac my_matching := matching my_simpler my_chooser; eauto.

  Hint Extern 1 (exists r, kfold_left _ _ _ _ = _ _ /\ lr _ _ _) =>
    eapply cpsFold_correct; eauto; my_matching.

  induction 1; my_matching.
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
