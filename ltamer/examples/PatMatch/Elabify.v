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
Require Import Elab.

Set Implicit Arguments.


(** * Term translation *)

Notation "x <- e1 ; e2" := ((\x, e2) @ e1)%source (right associativity, at level 76, e1 at next level) : source_scope.
Notation "x <- e1 ; e2" := ((\x, e2) @ e1)%elab (right associativity, at level 76, e1 at next level) : elab_scope.

Section choice_tree.
  Open Local Scope source_scope.

  Fixpoint choice_tree var (t : type) (result : Type) : Type :=
    match t with
      | t1 ** t2 =>
        choice_tree var t1
        (choice_tree var t2
          result)
      | t1 ++ t2 =>
        choice_tree var t1 result
        * choice_tree var t2 result
      | t => eterm var t -> result
    end%type.

  Fixpoint merge var t result {struct t}
    : (result -> result -> result)
    -> choice_tree var t result -> choice_tree var t result -> choice_tree var t result :=
    match t return ((result -> result -> result)
      -> choice_tree var t result -> choice_tree var t result -> choice_tree var t result) with
      | _ ** _ => fun mr ct1 ct2 =>
        merge _ _
        (merge _ _ mr)
        ct1 ct2

      | _ ++ _ => fun mr ct1 ct2 =>
        (merge var _ mr (fst ct1) (fst ct2),
          merge var _ mr (snd ct1) (snd ct2))

      | _ => fun mr ct1 ct2 e => mr (ct1 e) (ct2 e)
    end.

  Fixpoint everywhere var t result {struct t}
    : (eterm var t -> result) -> choice_tree var t result :=
    match t return ((eterm var t -> result) -> choice_tree var t result) with
      | t1 ** t2 => fun r =>
        everywhere (t := t1) (fun e1 =>
          everywhere (t := t2) (fun e2 =>
            r ([e1, e2])%elab))

      | _ ++ _ => fun r =>
        (everywhere (fun e => r (Inl e)%elab),
          everywhere (fun e => r (Inr e)%elab))

      | _ => fun r => r
    end.
End choice_tree.

Implicit Arguments merge [var t result].


Section term_ind.
  Open Local Scope source_scope.

  Variable var : type -> Type.

  Variable P : forall t, term var t -> Prop.

  Variable PVar : forall t (v : var t),
    P (#v).

  Variable PUnit : P ().

  Variable PApp : forall t1 t2
    (e1 : term var (t1 --> t2))
    (e2 : term var t1),
    P e1
    -> P e2
    -> P (e1 @ e2).
  Variable PAbs : forall t1 t2
    (e' : var t1 -> term var t2),
    (forall x, P (e' x))
    -> P (SAbs e').

  Variable PPair : forall t1 t2
    (e1 : term var t1)
    (e2 : term var t2),
    P e1
    -> P e2
    -> P ([e1, e2]).

  Variable PInl : forall t1 t2
    (e' : term var t1),
    P e'
    -> P (SInl (t2 := t2) e').
  Variable PInr : forall t1 t2
    (e' : term var t2),
    P e'
    -> P (SInr (t1 := t1) e').

  Variable PCase : forall t1 t2
    (e : term var t1)
    (ms : list { ts : list type & pat t1 ts * (tuple var ts -> term var t2)}%type)
    (def : term var t2),
    P e
    -> (AllS (fun p => forall tup, P (snd (projT2 p) tup)) ms)
    -> P def
    -> P (SCase e ms def).

  Fixpoint term_ind t (e : term var t) {struct e} : P e :=
    match e return (P e) with
      | SVar _ v => PVar v

      | SUnit => PUnit

      | SApp _ _ e1 e2 => PApp (term_ind e1) (term_ind e2)
      | SAbs _ _ e' => PAbs _ (fun x => term_ind (e' x))

      | SPair _ _ e1 e2 => PPair (term_ind e1) (term_ind e2)

      | SInl _ _ e' => PInl _ (term_ind e')
      | SInr _ _ e' => PInr _ (term_ind e')

      | SCase t1 t2 e' ms def => PCase (term_ind e')
        ((fix matches_ind (ms : list { ts : list type & pat t1 ts * (tuple var ts -> term var t2)}%type)
          : AllS (fun p => forall tup, P (snd (projT2 p) tup)) ms :=
          match ms return (AllS (fun p => forall tup, P (snd (projT2 p) tup)) ms) with
            | nil => allS_nil _
            | p :: tl =>
              allS_cons (P := fun p => forall tup, P (snd (projT2 p) tup))
              p (fun tup => term_ind (snd (projT2 p) tup)) (matches_ind tl)
          end) ms)
        (term_ind def)
    end.
End term_ind.

Section elabify.
  Open Local Scope elab_scope.

  Fixpoint elabifyPat var t1 ts result (p : pat t1 ts) {struct p} :
    (tuple (eterm var) ts -> result) -> result -> choice_tree var t1 result :=
    match p in (pat t1 ts) return ((tuple (eterm var) ts -> result)
      -> result -> choice_tree var t1 result) with
      | SPVar _ => fun succ fail =>
        everywhere (fun disc => succ (disc, tt))

      | SPPair _ _ _ _ p1 p2 => fun succ fail =>
        elabifyPat _ p1
        (fun tup1 =>
          elabifyPat _ p2
          (fun tup2 =>
            succ (concat tup1 tup2))
          fail)
        (everywhere (fun _ => fail))

      | SPInl _ _ _ p' => fun succ fail =>
        (elabifyPat _ p' succ fail,
          everywhere (fun _ => fail))
      | SPInr _ _ _ p' => fun succ fail =>
        (everywhere (fun _ => fail),
          elabifyPat _ p' succ fail)
    end.

  Implicit Arguments elabifyPat [var t1 ts result].

  Fixpoint letify var t ts {struct ts} : (tuple var ts -> eterm var t)
    -> tuple (eterm var) ts -> eterm var t :=
    match ts return ((tuple var ts -> eterm var t)
      -> tuple (eterm var) ts -> eterm var t) with
      | nil => fun f _ => f tt
      | _ :: _ => fun f tup => letify _ (fun tup' => x <- fst tup; f (x, tup')) (snd tup)
    end.

  Implicit Arguments letify [var t ts].

  Fixpoint expand var result t1 t2
    (out : result -> eterm var t2) {struct t1}
    : forall ct : choice_tree var t1 result,
      eterm var t1
      -> eterm var t2 :=
      match t1 return (forall ct : choice_tree var t1 result, eterm var t1
        -> eterm var t2) with
        | (_ ** _)%source => fun ct disc =>
          expand
          (fun ct' => expand out ct' (#2 disc)%source)
          ct
          (#1 disc)
          
        | (_ ++ _)%source => fun ct disc =>
          Cases disc of
            ||| x => expand out (fst ct) (#x)
            ||| y => expand out (snd ct) (#y)
                
        | _ => fun ct disc =>
          x <- disc; out (ct (#x))
      end.

  Definition mergeOpt A (o1 o2 : option A) :=
    match o1 with
      | None => o2
      | _ => o1
    end.

  Fixpoint elabify var t (e : term var t) {struct e} : eterm var t :=
    match e in (term _ t) return (eterm var t) with
      | SVar _ v => #v

      | SUnit => ()

      | SApp _ _ e1 e2 => elabify e1 @ elabify e2
      | SAbs _ _ e' => \x, elabify (e' x) 

      | SPair _ _ e1 e2 => [elabify e1, elabify e2]
      | SInl _ _ e' => Inl (elabify e')
      | SInr _ _ e' => Inr (elabify e')

      | SCase t1 t2 e' ms def =>
        expand
        (fun eo => match eo with
                     | None => elabify def
                     | Some e => e
                   end)
        ((fix elabifyPats
          (ms : list { ts : list type & pat t1 ts * (tuple var ts -> term var t2)}%type)
          {struct ms}
          : choice_tree var t1 (option (eterm var t2)) :=
          match ms with
            | nil => everywhere (fun _ => None)
            | existT _ (p, b) :: rest =>
              merge (@mergeOpt _)
              (elabifyPat p
                (fun ts => Some (letify
                  (fun ts' => elabify (b ts'))
                  ts))
                None)
              (elabifyPats rest)
          end) ms)
        (elabify e')
    end.
End elabify.

Definition Elabify t (E : Term t) : Eterm t :=
  fun _ => elabify (E _).


(** * Correctness *)

Fixpoint grab t result : choice_tree typeDenote t result -> typeDenote t -> result :=
  match t return (choice_tree typeDenote t result -> typeDenote t -> result) with
    | t1 ** t2 => fun ct v =>
      grab t2 _ (grab t1 _ ct (fst v)) (snd v)
    | t1 ++ t2 => fun ct v =>
      match v with
        | inl v' => grab t1 _ (fst ct) v'
        | inr v' => grab t2 _ (snd ct) v'
      end
    | t => fun ct v => ct (#v)%elab
  end%source%type.

Implicit Arguments grab [t result].

Ltac my_changer := repeat progress
  match goal with
    | [ |- context[match ?E with inl _ => _ | inr _ => _ end] ] => destruct E
    | [ H : forall (result : Type) (succ : _ -> result), _
      |- context[everywhere ?succ] ] =>
      generalize (H _ succ); clear H; intro H

    | [ H : forall (result : Type) (succ : _ -> result) (fail : _) (v : _) (tup : _), _ ->
      exists tup', grab (elabifyPat _ ?p _ _) _ = _ /\ _
      |- context[elabifyPat _ ?p ?succ _] ] =>
      generalize (H _ succ); clear H; intro H
    | [ H : forall (fail : _) (v : _) (tup : _), _ ->
      exists tup', grab (elabifyPat _ ?p _ _) _ = _ /\ _
        |- context[elabifyPat _ ?p _ ?fail] ] =>
    generalize  (H fail); clear H; intro H

    | [ H : forall (result : Type) (succ : _ -> result) (fail : _) (v : _), _ ->
      grab (elabifyPat _ ?p _ _) _ = _
      |- context[elabifyPat _ ?p ?succ _] ] =>
      generalize (H _ succ); clear H; intro H
    | [ H : forall (fail : _) (v : _), _ ->
      grab (elabifyPat _ ?p _ _) _ = _
        |- context[elabifyPat _ ?p _ ?fail] ] =>
    generalize  (H fail); clear H; intro H

    | [ H1 : forall tup : tuple _ _, ?E = Some tup -> _,
      H2 : context[match ?E with None => _ | Some _ => _ end] |- _ ] =>
    destruct E; try discriminate;
      destruct (H1 _ (refl_equal _)); clear H1

    | [ H1 : ?E = None -> _,
      H2 : context[match ?E with None => _ | Some _ => _ end] |- _ ] =>
    destruct E

    | [ x : sigT _ |- _ ] => destruct x
  end.

Ltac my_chooser T k :=
  match T with
    | Type => fail 1

    | eterm _ (_ ** _)%source =>
      match goal with
        | [ e1 : eterm _ _, e2 : eterm _ _ |- _ ] => k ([e1, e2])%elab
      end
    | eterm _ _ =>
      match goal with
        | [ e : eterm _ (_ ** _)%source |- _ ] => k (#1 e)%elab || k (#2 e)%elab
        | [ v : typeDenote _ |- _ ] => k (#v)%elab
      end

    | _ => default_chooser T k
  end.

Ltac base_simpler := fold choice_tree in *; fold typeDenote in *.
Ltac my_simpler := simpler; base_simpler; repeat progress (my_changer; simpler; base_simpler).
Ltac my_equation := equation; base_simpler; repeat progress (my_changer; equation; base_simpler).
Ltac my_matching := matching my_equation my_chooser.

Lemma expand_grab : forall t2 t1 result
  (out : result -> eterm typeDenote t2)
  (ct : choice_tree typeDenote t1 result)
  (disc : eterm typeDenote t1),
  etermDenote (expand out ct disc) = etermDenote (out (grab ct (etermDenote disc))).
  induction t1; my_equation.
Qed.

Lemma recreate_pair : forall T1 T2 (p : T1 * T2),
  (fst p, snd p) = p.
  destruct p; trivial.
Qed.

Lemma everywhere_correct : forall t1 result
  (succ : eterm typeDenote t1 -> result) disc,
  exists disc', grab (everywhere succ) (etermDenote disc) = succ disc'
    /\ etermDenote disc' = etermDenote disc.
  Hint Resolve recreate_pair.

  induction t1; my_matching.
Qed.

Lemma merge_correct : forall t result
  (ct1 ct2 : choice_tree typeDenote t result)
  (mr : result -> result -> result) v,
  grab (merge mr ct1 ct2) v = mr (grab ct1 v) (grab ct2 v).
  induction t; equation.
Qed.

Lemma everywhere_fail : forall t result
  (fail : result) v,
  grab (everywhere (fun _ : eterm typeDenote t => fail)) v = fail.
  induction t; equation.
Qed.

Lemma elabifyPat_correct : forall t1 ts (p : pat t1 ts)
  result (succ : tuple (eterm typeDenote) ts -> result)
  (fail : result) v tup,
  patDenote p v = Some tup
  -> exists tup', grab (elabifyPat typeDenote p succ fail) v = succ tup'
    /\ tup = tuple_map etermDenote tup'.
  Hint Resolve tuple_map_concat.

  induction p; my_matching;
    try match goal with
          | [ |- context[grab (everywhere ?succ) ?v] ] =>
            generalize (everywhere_correct succ (#v)%elab); equation; eauto
        end.
Qed.

Lemma elabifyPat_fails : forall t1 ts (p : pat t1 ts)
  result (succ : tuple (eterm typeDenote) ts -> result)
  (fail : result) v,
  patDenote p v = None
  -> grab (elabifyPat typeDenote p succ fail) v = fail.
  Hint Resolve everywhere_fail.

  induction p; my_simpler;
    match goal with
      | [ |- context[grab (elabifyPat _ ?p ?succ ?fail) ?v] ] =>
        generalize (elabifyPat_correct p succ fail v)
    end; my_matching.
Qed.

Implicit Arguments letify [var t ts].

Lemma letify_correct : forall t ts (f : tuple typeDenote ts -> eterm typeDenote t)
  (tup : tuple (eterm typeDenote) ts),
  etermDenote (letify f tup)
  = etermDenote (f (tuple_map etermDenote tup)).
  induction ts; equation.
Qed.

Theorem elabify_correct : forall t (e : term typeDenote t),
  etermDenote (elabify e) = termDenote e.
  Hint Rewrite expand_grab merge_correct letify_correct : ltamer.
  Hint Rewrite everywhere_fail elabifyPat_fails using assumption : ltamer.

  induction e using term_ind; equation;
    match goal with
      | [ H : AllS _ _ |- _ ] =>
        induction H; my_equation
    end;
    match goal with
      | [ |- context[grab (elabifyPat typeDenote ?p ?succ ?fail) ?v] ] =>
        case_eq (patDenote p v); [intros tup Heq; simpler;
          destruct (elabifyPat_correct p succ fail _ Heq); equation
          | simpler]
    end.
Qed.
