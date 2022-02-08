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

Require Import Bool List.

Require Import Arith Omega.
Require Import LambdaTamer.Util.
Require Import LambdaTamer.Binding.
Require Import LambdaTamer.Tactics.

Require Import CPS.
Require Import CC.

Set Implicit Arguments.


(** * Closure conversion *)

Section cprimops.
  Variable var : ctype -> Set.

  Variables t : ptype.

  Inductive cprimops : Type :=
  | CReturn :
    var ([< t >])
    -> cprimops
  | CLet : forall t',
    cprimop var t'
    -> (var t' -> cprimops)
    -> cprimops.
End cprimops.

Implicit Arguments CReturn [var t].
Implicit Arguments CLet [var t t'].

Notation "'Return' x" := (CReturn x) (at level 75) : cc_scope.
Notation "x <~ p ; ps" := (CLet p (fun x => ps))
  (right associativity, at level 76, p at next level) : cc_scope.

Bind Scope cc_scope with cprimops.

Fixpoint cprimopsDenote t (p : cprimops ctypeDenote t) {struct p} : ptypeDenote t :=
  match p return (ptypeDenote t) with
    | CReturn v => v
    | CLet _ p ps' => cprimopsDenote (ps' (cprimopDenote p))
  end.

Section splice.
  Open Local Scope cc_scope.

  Fixpoint splicePrim var t (ps : cprimops var t)
    t' (ps' : var (CData t) -> cprimops var t') {struct ps} : cprimops var t' :=
    match ps with
      | CReturn v => ps' v
      | CLet _ p ps'' => x <~ p; splicePrim (ps'' x) ps'
    end.

  Fixpoint spliceTerm var result t (ps : cprimops var t)
    (e : var (CData t) -> cterm var result) {struct ps} : cterm var result :=
    match ps with
      | CReturn v => e v
      | CLet _ p ps' => x <- p; spliceTerm (ps' x) e
    end.

  Fixpoint spliceFuncs' var result T1 (fs : cfuncs var result T1)
    T2 (f : T1 -> T2) {struct fs} : cfuncs var result T2 :=
    match fs with
      | CMain v => Main (f v)
      | CAbs _ _ e fs' => CAbs e (fun x => spliceFuncs' (fs' x) f)
    end.

  Fixpoint spliceFuncs var result T1 (fs1 : cfuncs var result T1)
    T2 (fs2 : cfuncs var result T2)
    T3 (f : T1 -> T2 -> T3) {struct fs1} : cfuncs var result T3 :=
    match fs1 with
      | CMain v => spliceFuncs' fs2 (f v)
      | CAbs _ _ e fs1' => CAbs e (fun x => spliceFuncs (fs1' x) fs2 f)
    end.

  Fixpoint inside var result T1 (fs1 : cfuncs var result T1)
    T2 (fs2 : T1 -> cfuncs var result T2) {struct fs1} : cfuncs var result T2 :=
    match fs1 with
      | CMain v => fs2 v
      | CAbs _ _ e fs1' => CAbs e (fun x => inside (fs1' x) fs2)
    end.
End splice.

Notation "x <~~ ps ; ps'" := (splicePrim ps (fun x => ps'))
  (right associativity, at level 76, ps at next level) : cc_scope.
Notation "x <-- ps ; e" := (spliceTerm ps (fun x => e))
  (right associativity, at level 76, ps at next level) : cc_scope.

Definition natvar (_ : ptype) := nat.

Definition isfree := tuple (fun (_ : ptype) => bool).

Ltac my_changer :=
  match goal with
    | [ x : bool |- _ ] => destruct x
  end.

Ltac my_simpler := simpler_expensive; repeat progress (my_changer; simpler_expensive).
Ltac my_equation := equation_expensive; repeat progress (my_changer; equation_expensive).

Section isfree.
  Open Local Scope cps_scope.

  Hint Extern 3 False => omega.

  Fixpoint lookup_type (envT : list ptype) (n : nat) {struct envT}
    : isfree envT -> option ptype :=
    match envT return (isfree envT -> _) with
      | nil => fun _ => None
      | first :: rest => fun fvs =>
        if eq_nat_dec n (length rest)
          then match fvs with
                 | (true, _) => Some first
                 | (false, _) => None
               end
          else lookup_type rest n (snd fvs)
    end.
  
  Implicit Arguments lookup_type [envT].

  Notation ok := (fun (envT : list ptype) (fvs : isfree envT) (n : nat) (t : ptype)
    => lookup_type n fvs = Some t).

  Fixpoint wfTerm result (envT : list ptype) (fvs : isfree envT) (e : pterm natvar result) {struct e} : Prop :=
    match e with
      | PHalt n => ok envT fvs n result
      | PApp t n1 n2 => ok envT fvs n1 (t --->) /\ ok envT fvs n2 t
      | PBind t p e => wfPrimop _ fvs p /\ wfTerm (t :: envT) (true, fvs) (e (length envT))
    end

  with wfPrimop result (envT : list ptype) (fvs : isfree envT) t (p : pprimop natvar result t) {struct p} : Prop :=
    match p with
      | PVar t n => ok envT fvs n t
      | PTrue => True
      | PFalse => True
      | PAbs t e => wfTerm (t :: envT) (true, fvs) (e (length envT))
      | PPair t1 t2 n1 n2 => ok envT fvs n1 t1 /\ ok envT fvs n2 t2
      | PFst t1 t2 n => ok envT fvs n (t1 ** t2)
      | PSnd t1 t2 n => ok envT fvs n (t1 ** t2)
    end.

  Implicit Arguments wfTerm [result envT].
  Implicit Arguments wfPrimop [result envT t].

  Scheme pterm_mut := Induction for pterm Sort Prop
  with pprimop_mut := Induction for pprimop Sort Prop.

  Theorem wfTerm_weaken : forall result (e : pterm natvar result) envT (fvs fvs' : isfree envT),
    wfTerm fvs e
    -> (forall n t, ok _ fvs n t -> ok _ fvs' n t)
    -> wfTerm fvs' e.
    Hint Extern 1 (wfTerm _ _) =>
      match goal with
        | [ H: _ , _ : forall n t, lookup_type _ ?fvs = _ -> _ |- _ ] =>
        apply H with (true, fvs); simpler_expensive
      end.

    intro.
    apply (pterm_mut
      (fun (e : pterm natvar result) =>
        forall (envT : list ptype) (fvs fvs' : isfree envT),
          wfTerm fvs e ->
          (forall (n : nat) (t : ptype), ok envT fvs n t -> ok envT fvs' n t) ->
          wfTerm fvs' e)
      (fun t (p : pprimop natvar result t) =>
        forall (envT : list ptype) (fvs fvs' : isfree envT),
          wfPrimop fvs p ->
          (forall (n : nat) (t : ptype), ok envT fvs n t -> ok envT fvs' n t) ->
          wfPrimop fvs' p)); my_simpler; eauto.
  Defined.

  Fixpoint isfree_none (envT : list ptype) : isfree envT :=
    match envT return (isfree envT) with
      | nil => tt
      | _ :: _ => (false, isfree_none _)
    end.

  Implicit Arguments isfree_none [envT].

  Fixpoint isfree_one (envT : list ptype) (n : nat) {struct envT} : isfree envT :=
    match envT return (isfree envT) with
      | nil => tt
      | _ :: rest =>
        if eq_nat_dec n (length rest)
          then (true, isfree_none)
          else (false, isfree_one _ n)
    end.

  Implicit Arguments isfree_one [envT].

  Fixpoint isfree_merge (envT : list ptype) : isfree envT -> isfree envT -> isfree envT :=
    match envT return (isfree envT -> isfree envT -> isfree envT) with
      | nil => fun _ _ => tt
      | _ :: _ => fun fv1 fv2 => (fst fv1 || fst fv2, isfree_merge _ (snd fv1) (snd fv2))
    end.

  Implicit Arguments isfree_merge [envT].

  Fixpoint fvsPrimop result t (p : pprimop natvar result t)
    (envT : list ptype) {struct p} : isfree envT :=
    match p with
      | PVar _ n => isfree_one n

      | PTrue => isfree_none
      | PFalse => isfree_none

      | PAbs t f => snd (fvsTerm (f (length envT)) (t :: envT))

      | PPair _ _ n1 n2 => isfree_merge (isfree_one n1) (isfree_one n2)
      | PFst _ _ n => isfree_one n
      | PSnd _ _ n => isfree_one n
    end

  with fvsTerm result (e : pterm natvar result)
    (envT : list ptype) {struct e} : isfree envT :=
    match e with
      | PHalt n => isfree_one n
      | PApp _ n1 n2 => isfree_merge (isfree_one n1) (isfree_one n2)
      | PBind t p e => isfree_merge (fvsPrimop p envT) (snd (fvsTerm (e (length envT)) (t :: envT)))
    end.

  Lemma isfree_one_correct : forall t (v : natvar t) envT fvs,
    ok envT fvs v t
    -> ok envT (isfree_one (envT:=envT) v) v t.
    induction envT; my_equation; eauto.
  Defined.

  Lemma isfree_merge_correct1 : forall t (v : natvar t) envT fvs1 fvs2,
    ok envT fvs1 v t
    -> ok envT (isfree_merge (envT:=envT) fvs1 fvs2) v t.
    induction envT; my_equation; eauto.
  Defined.

  Lemma isfree_merge_correct2 : forall t (v : natvar t) envT fvs1 fvs2,
    ok envT fvs2 v t
    -> ok envT (isfree_merge (envT:=envT) fvs1 fvs2) v t.
    induction envT; my_equation; eauto.
  Defined.

  Hint Resolve isfree_one_correct isfree_merge_correct1 isfree_merge_correct2.
  
  Lemma fvsTerm_correct : forall result (e : pterm natvar result)
    envT (fvs : isfree envT), wfTerm fvs e
    -> forall (fvs' : isfree envT),
      (forall v t, ok envT (fvsTerm e envT) v t -> ok envT fvs' v t)
      -> wfTerm fvs' e.
    Hint Extern 1 (_ = _) =>
      match goal with
        | [ H : lookup_type _ (fvsTerm ?X ?Y) = _ |- _ ] =>
          destruct (fvsTerm X Y); my_equation
      end.

    intro.
    apply (pterm_mut
      (fun (e : pterm natvar result) =>
        forall envT (fvs : isfree envT), wfTerm fvs e
          -> forall (fvs' : isfree envT),
            (forall v t, ok envT (fvsTerm e envT) v t -> ok envT fvs' v t)
            -> wfTerm fvs' e)
      (fun t (p : pprimop natvar result t) =>
        forall envT (fvs : isfree envT), wfPrimop fvs p
          -> forall (fvs' : isfree envT),
            (forall v t, ok envT (fvsPrimop p envT) v t -> ok envT fvs' v t)
            -> wfPrimop fvs' p)); my_simpler; eauto.
  Defined.

  Lemma lookup_type_unique : forall v t1 t2 envT (fvs1 fvs2 : isfree envT),
    lookup_type v fvs1 = Some t1
    -> lookup_type v fvs2 = Some t2
    -> t1 = t2.
    induction envT; my_equation; eauto.
  Defined.

  Implicit Arguments lookup_type_unique [v t1 t2 envT fvs1 fvs2].

  Hint Extern 2 (lookup_type _ _ = Some _) =>
    match goal with
      | [ H1 : lookup_type ?v _ = Some _,
        H2 : lookup_type ?v _ = Some _ |- _ ] =>
      (generalize (lookup_type_unique H1 H2); intro; subst)
      || rewrite <- (lookup_type_unique H1 H2)
    end.

  Lemma lookup_none : forall v t envT,
    lookup_type (envT:=envT) v (isfree_none (envT:=envT)) = Some t
    -> False.
    induction envT; simpler_expensive.
  Defined.

  Hint Extern 2 (_ = _) => contradictory; eapply lookup_none; eassumption.

  Lemma lookup_one : forall v' v t envT,
    lookup_type (envT:=envT) v' (isfree_one (envT:=envT) v) = Some t
    -> v' = v.
    induction envT; simpler_expensive.
  Defined.

  Implicit Arguments lookup_one [v' v t envT].

  Hint Extern 2 (lookup_type _ _ = Some _) =>
    match goal with
      | [ H : lookup_type _ _ = Some _ |- _ ] =>
        generalize (lookup_one H); intro; subst
    end.

  Lemma lookup_merge : forall v t envT (fvs1 fvs2 : isfree envT),
    lookup_type v (isfree_merge fvs1 fvs2) = Some t
    -> lookup_type v fvs1 = Some t
    \/ lookup_type v fvs2 = Some t.
    induction envT; my_equation.
  Defined.

  Implicit Arguments lookup_merge [v t envT fvs1 fvs2].

  Lemma lookup_bound : forall v t envT (fvs : isfree envT),
    lookup_type v fvs = Some t
    -> v < length envT.
    Hint Resolve lt_S.
    induction envT; equation_expensive; eauto.
  Defined.

  Hint Resolve lookup_bound.

  Lemma lookup_bound_contra : forall t envT (fvs : isfree envT),
    lookup_type (length envT) fvs = Some t
    -> False.
    intros; assert (length envT < length envT); eauto.
  Defined.

  Hint Resolve lookup_bound_contra.

  Hint Extern 3 (_ = _) => contradictory; omega.

  Lemma lookup_push_drop : forall v t t' envT fvs,
    v < length envT
    -> lookup_type (envT := t :: envT) v (true, fvs) = Some t'
    -> lookup_type (envT := envT) v fvs = Some t'.
    equation_expensive.
  Defined.

  Lemma lookup_push_add : forall v t t' envT fvs,
    lookup_type (envT := envT) v (snd fvs) = Some t'
    -> lookup_type (envT := t :: envT) v fvs = Some t'.
    equation_expensive; contradictory; eauto.
  Defined.

  Hint Resolve lookup_bound lookup_push_drop lookup_push_add.

  Theorem fvsTerm_minimal : forall result (e : pterm natvar result)
    envT (fvs : isfree envT), wfTerm fvs e
    -> (forall v t, ok envT (fvsTerm e envT) v t -> ok envT fvs v t).
    Hint Extern 1 (_ = _) =>
      match goal with
        | [ H : lookup_type _ (isfree_merge _ _) = Some _ |- _ ] =>
          destruct (lookup_merge H); clear H; eauto
      end.

    intro.
    apply (pterm_mut
      (fun (e : pterm natvar result) =>
        forall envT (fvs : isfree envT), wfTerm fvs e
          -> (forall v t, ok envT (fvsTerm e envT) v t -> ok envT fvs v t))
      (fun t (p : pprimop natvar result t) =>
        forall envT (fvs : isfree envT), wfPrimop fvs p
          -> (forall v t, ok envT (fvsPrimop p envT) v t -> ok envT fvs v t)));
    simpler; eauto.
  Defined.

  Fixpoint envType (envT : list ptype) : isfree envT -> ptype :=
    match envT return (isfree envT -> _) with
      | nil => fun _ => Unit
      | t :: _ => fun tup =>
        if fst tup
          then (t ** envType _ (snd tup))%cps
          else envType _ (snd tup)
    end.

  Implicit Arguments envType [envT].

  Fixpoint envOf (var : ctype -> Set) (envT : list ptype) {struct envT}
    : isfree envT -> Set :=
    match envT return (isfree envT -> _) with
      | nil => fun _ => unit
      | first :: rest => fun fvs =>
        match fvs with
          | (true, fvs') => (var (CData first) * envOf var rest fvs')%type
          | (false, fvs') => envOf var rest fvs'
        end
    end.

  Implicit Arguments envOf [envT].

  Notation "var <| to" := (match to with
                             | None => unit
                             | Some t => var ([< t >])%cc
                           end) (no associativity, at level 70).

  Fixpoint lookup (var : ctype -> Set) (envT : list ptype) :
    forall (n : nat) (fvs : isfree envT), envOf var fvs -> var <| lookup_type n fvs :=
      match envT return (forall (n : nat) (fvs : isfree envT), envOf var fvs
        -> var <| lookup_type n fvs) with
        | nil => fun _ _ _ => tt
        | first :: rest => fun n fvs =>
          match (eq_nat_dec n (length rest)) as Heq return
            (envOf var (envT := first :: rest) fvs
              -> var <| (if Heq
                then match fvs with
                       | (true, _) => Some first
                       | (false, _) => None
                     end
                else lookup_type n (snd fvs))) with
            | left _ =>
              match fvs return (envOf var (envT := first :: rest) fvs
                -> var <| (match fvs with
                             | (true, _) => Some first
                             | (false, _) => None
                           end)) with
                | (true, _) => fun env => fst env
                | (false, _) => fun _ => tt
              end
            | right _ =>
              match fvs return (envOf var (envT := first :: rest) fvs
                -> var <| (lookup_type n (snd fvs))) with
                | (true, fvs') => fun env => lookup var rest n fvs' (snd env)
                | (false, fvs') => fun env => lookup var rest n fvs' env
              end
          end
      end.

  Theorem lok : forall var n t envT (fvs : isfree envT),
    lookup_type n fvs = Some t
    -> var <| lookup_type n fvs = var ([< t >])%cc.
    equation.
  Defined.
End isfree.

Implicit Arguments lookup_type [envT].
Implicit Arguments lookup [envT fvs].
Implicit Arguments wfTerm [result envT].
Implicit Arguments wfPrimop [result envT t].
Implicit Arguments envType [envT].
Implicit Arguments envOf [envT].
Implicit Arguments lok [var n t envT fvs].

Section lookup_hints.
  Hint Resolve lookup_bound_contra.

  Ltac my_chooser T k :=
    match T with
      | ptype =>
        match goal with
          | [ H : lookup _ _ = Some ?t |- _ ] => k t
        end
      | _ => default_chooser T k
    end.

  Ltac my_matching := matching equation_expensive my_chooser.

  Lemma lookup_type_push : forall t' envT (fvs1 fvs2 : isfree envT) b1 b2,
    (forall (n : nat) (t : ptype),
      lookup_type (envT := t' :: envT) n (b1, fvs1) = Some t ->
      lookup_type (envT := t' :: envT) n (b2, fvs2) = Some t)
    -> (forall (n : nat) (t : ptype),
      lookup_type n fvs1 = Some t ->
      lookup_type n fvs2 = Some t).
    Hint Extern 3 (_ = _) => apply False_ind.

    my_matching; eauto.
  Defined.

  Lemma lookup_type_push_contra : forall t' envT (fvs1 fvs2 : isfree envT),
    (forall (n : nat) (t : ptype),
      lookup_type (envT := t' :: envT) n (true, fvs1) = Some t ->
      lookup_type (envT := t' :: envT) n (false, fvs2) = Some t)
    -> False.
    my_matching.
  Defined.
End lookup_hints.

Section packing.
  Open Local Scope cc_scope.

  Hint Resolve lookup_type_push lookup_type_push_contra.

  Definition packTerm (var : ctype -> Set) (envT : list ptype)
    (fvs1 fvs2 : isfree envT)
    : (forall n t, lookup_type n fvs1 = Some t -> lookup_type n fvs2 = Some t)
    -> envOf var fvs2 -> cprimops var (envType fvs1).
    refine (fix packTerm (var : ctype -> Set) (envT : list ptype) {struct envT}
      : forall fvs1 fvs2 : isfree envT,
        (forall n t, lookup_type n fvs1 = Some t -> lookup_type n fvs2 = Some t)
        -> envOf var fvs2 -> cprimops var (envType fvs1) :=
        match envT return (forall fvs1 fvs2 : isfree envT,
          (forall n t, lookup_type n fvs1 = Some t -> lookup_type n fvs2 = Some t)
          -> envOf var fvs2
          -> cprimops var (envType fvs1)) with
          | nil => fun _ _ _ _ => u <~ (); Return u
          | first :: rest => fun fvs1 =>
            match fvs1 return (forall fvs2 : isfree (first :: rest),
              (forall n t, lookup_type (envT := first :: rest) n fvs1 = Some t
                -> lookup_type n fvs2 = Some t)
              -> envOf var fvs2
              -> cprimops var (envType (envT := first :: rest) fvs1)) with
              | (false, fvs1') => fun fvs2 =>
                match fvs2 return ((forall n t, lookup_type (envT := first :: rest) n (false, fvs1') = Some t
                  -> lookup_type (envT := first :: rest) n fvs2 = Some t)
                -> envOf (envT := first :: rest) var fvs2
                -> cprimops var (envType (envT := first :: rest) (false, fvs1'))) with
                  | (false, fvs2') => fun Hmin env =>
                    packTerm var _  fvs1' fvs2' _ env
                  | (true, fvs2') => fun Hmin env =>
                    packTerm var _  fvs1' fvs2' _ (snd env)
                end
              | (true, fvs1') => fun fvs2 =>
                match fvs2 return ((forall n t, lookup_type (envT := first :: rest) n (true, fvs1') = Some t
                  -> lookup_type (envT := first :: rest) n fvs2 = Some t)
                -> envOf (envT := first :: rest) var fvs2
                -> cprimops var (envType (envT := first :: rest) (true, fvs1'))) with
                  | (false, fvs2') => fun Hmin env =>
                    False_rect _ _
                  | (true, fvs2') => fun Hmin env =>
                    p <~~ packTerm var _ fvs1' fvs2' _ (snd env);
                    p' <~ [fst env, p]; Return p'
                end
            end
        end); eauto.
  Defined.

  Hint Resolve fvsTerm_correct fvsTerm_minimal.
  Hint Resolve lookup_push_drop lookup_bound lookup_push_add.

  Implicit Arguments packTerm [var envT].

  Fixpoint unpackTerm (var : ctype -> Set) result (envT : list ptype) {struct envT}
    : forall fvs : isfree envT,
      cprimops var (envType fvs)
      -> (envOf var fvs -> cterm var result) -> cterm var result :=
      match envT return (forall fvs : isfree envT,
        cprimops var (envType fvs)
        -> (envOf var fvs -> cterm var result) -> cterm var result) with
        | nil => fun _ _ f => f tt
        | first :: rest => fun fvs =>
          match fvs return (cprimops var (envType (envT := first :: rest) fvs)
            -> (envOf var (envT := first :: rest) fvs -> cterm var result)
            -> cterm var result) with
            | (false, fvs') => fun p f =>
              unpackTerm rest fvs' p f
            | (true, fvs') => fun p f =>
              unpackTerm rest fvs'
              (px <~~ p; ps <~ #2 px; Return ps)
              (fun env => px <-- p; pf <- #1 px; f (pf, env))
          end
      end.
  
  Implicit Arguments unpackTerm [var result envT fvs].

  Theorem wfTerm_lax : forall result t envT (fvs : isfree envT) (e : pterm natvar result),
    wfTerm (envT := t :: envT) (true, fvs) e
    -> wfTerm (envT := t :: envT) (true, snd (fvsTerm e (t :: envT))) e.
    Hint Extern 1 (_ = _) =>
      match goal with
        | [ H : lookup_type _ (fvsTerm ?X ?Y) = _ |- _ ] =>
          destruct (fvsTerm X Y); my_equation
      end.
    eauto.
  Defined.

  Implicit Arguments wfTerm_lax [result t envT fvs e].

  Lemma inclusion : forall result t' envT fvs (e : pterm natvar result),
    wfTerm (envT := t' :: envT) (true, fvs) e
    -> (forall n t, lookup_type n (snd (fvsTerm e (t' :: envT))) = Some t
      -> lookup_type n fvs = Some t).
    eauto.
  Defined.

  Implicit Arguments inclusion [result t' envT fvs e].

  Definition env_prog var result envT (fvs : isfree envT) :=
    cfuncs var result (envOf var fvs -> cterm var result).
  Definition env_primops var result envT (fvs : isfree envT) t :=
    cfuncs var result (envOf var fvs -> cprimops var t).

  Implicit Arguments env_prog [envT].
  Implicit Arguments env_primops [envT].

  Fixpoint ccTerm var result (e : pterm natvar result)
    (envT : list ptype) (fvs : isfree envT)
    {struct e} : wfTerm fvs e -> env_prog var result fvs :=
    match e return (wfTerm fvs e -> env_prog var result fvs) with
      | PHalt n => fun Hwf =>
        Main (fun env =>
          CHalt (var := var) (lookup var n env :? lok Hwf))
      | PApp t n1 n2 => fun Hwf => CMain (fun env =>
        CApp (var := var) (t := t)
        (lookup var n1 env :? lok (proj1 Hwf))
        (lookup var n2 env :? lok (proj2 Hwf)))

      | PBind t p e => fun Hwf =>
        spliceFuncs
        (ccPrimop var p envT fvs (proj1 Hwf))
        (ccTerm var (e (length envT)) (t :: envT) (true, fvs) (proj2 Hwf))
        (fun p e env =>
          x <-- p env; e (x, env))
    end

  with ccPrimop var result t (p : pprimop natvar result t)
    (envT : list ptype) (fvs : isfree envT)
    {struct p} : wfPrimop fvs p -> env_primops var result fvs t :=
    match p in (pprimop _ _ t) return (wfPrimop fvs p -> env_primops var result fvs t) with
      | PVar t n => fun Hwf =>
        Main (fun env =>
          x <~ #(lookup var n env :? lok Hwf);
          Return x)

      | PTrue => fun Hwf =>
        Main (fun env =>
          x <~ Tru;
          Return x)
      | PFalse => fun Hwf =>
        Main (fun env =>
          x <~ Fals;
          Return x)

      | PAbs t body => fun Hwf =>
        inside (ccTerm var (body (length envT)) (t :: envT) (true, _) (wfTerm_lax Hwf))
        (fun body' =>
          CAbs (env := envType (snd (fvsTerm (body (length envT)) (t :: envT))))
          (fun envx arg =>
            unpackTerm (CReturn envx) (fun env => body' (arg, env)))
          (fun code =>
            Main (fun env =>
              envx <~~ packTerm
              (snd (fvsTerm (body (length envT)) (t :: envT)))
              fvs (inclusion Hwf) env;
              closure <~ code ## envx;
              Return closure)))

      | PPair t1 t2 n1 n2 => fun Hwf =>
        Main (fun env =>
          x <~ [lookup var n1 env :? lok (proj1 Hwf),
            lookup var n2 env :? lok (proj2 Hwf)];
          Return x)
      | PFst t1 t2 n => fun Hwf =>
        Main (fun env =>
          x <~ #1 (lookup var n env :? lok Hwf);
          Return x)
      | PSnd t1 t2 n => fun Hwf =>
        Main (fun env =>
          x <~ #2 (lookup var n env :? lok Hwf);
          Return x)
    end.
End packing.

Implicit Arguments packTerm [var envT].
Implicit Arguments unpackTerm [var result envT fvs].

Implicit Arguments ccTerm [var result envT].
Implicit Arguments ccPrimop [var result t envT].

Fixpoint map_funcs var result T1 T2 (f : T1 -> T2) (fs : cfuncs var result T1) {struct fs}
  : cfuncs var result T2 :=
  match fs with
    | CMain v => CMain (f v)
    | CAbs _ _ e fs' => CAbs e (fun x => map_funcs f (fs' x))
  end.

Definition CcTerm' result (E : Pterm result) (Hwf : wfTerm (envT := nil) tt (E _)) : Cprog result :=
  fun _ => map_funcs (fun f => f tt) (ccTerm (E _) (envT := nil) tt Hwf).


(** * Correctness *)

Scheme pterm_equiv_mut := Minimality for pterm_equiv Sort Prop
with pprimop_equiv_mut := Minimality for pprimop_equiv Sort Prop.

Section splicePrim_correct.
  Variables result t t' : ptype.
  Variable ps' : ctypeDenote ([< t >]) -> cprimops ctypeDenote t'.

  Theorem splicePrim_correct : forall (ps : cprimops ctypeDenote t),
    cprimopsDenote (splicePrim ps ps')
    = cprimopsDenote (ps' (cprimopsDenote ps)).
    induction ps; equation.
  Qed.
End splicePrim_correct.

Section spliceTerm_correct.
  Variables result t : ptype.
  Variable e : ctypeDenote ([< t >]) -> cterm ctypeDenote result.
  Variable k : ptypeDenote result -> bool.

  Theorem spliceTerm_correct : forall (ps : cprimops ctypeDenote t),
    ctermDenote (spliceTerm ps e) k
    = ctermDenote (e (cprimopsDenote ps)) k.
    induction ps; equation.
  Qed.
End spliceTerm_correct.

Section spliceFuncs'_correct.
  Variable result : ptype.
  Variables T1 T2 : Type.
  Variable f : T1 -> T2.
  Variable k : ptypeDenote result -> bool.

  Theorem spliceFuncs'_correct : forall fs,
    cfuncsDenote (spliceFuncs' fs f) k
    = f (cfuncsDenote fs k).
    induction fs; equation.
  Qed.
End spliceFuncs'_correct.

Section spliceFuncs_correct.
  Variable result : ptype.
  Variables T1 T2 T3 : Type.
  Variable fs2 : cfuncs ctypeDenote result T2.
  Variable f : T1 -> T2 -> T3.
  Variable k : ptypeDenote result -> bool.

  Hint Rewrite spliceFuncs'_correct : ltamer.

  Theorem spliceFuncs_correct : forall fs1,
    cfuncsDenote (spliceFuncs fs1 fs2 f) k
    = f (cfuncsDenote fs1 k) (cfuncsDenote fs2 k).
    induction fs1; equation.
  Qed.
End spliceFuncs_correct.

Section inside_correct.
  Variable result : ptype.
  Variables T1 T2 : Type.
  Variable fs2 : T1 -> cfuncs ctypeDenote result T2.
  Variable k : ptypeDenote result -> bool.

  Theorem inside_correct : forall fs1,
    cfuncsDenote (inside fs1 fs2) k
    = cfuncsDenote (fs2 (cfuncsDenote fs1 k)) k.
    induction fs1; equation.
  Qed.
End inside_correct.


Notation "var <| to" := (match to with
                           | None => unit
                           | Some t => var ([< t >])%cc
                         end) (no associativity, at level 70).

Section packing_correct.
  Variable result : ptype.

  Hint Rewrite splicePrim_correct spliceTerm_correct : ltamer.

  Ltac my_matching := matching my_equation default_chooser.

  Fixpoint makeEnv (envT : list ptype) : forall (fvs : isfree envT),
    ptypeDenote (envType fvs)
    -> envOf ctypeDenote fvs :=
    match envT return (forall (fvs : isfree envT),
      ptypeDenote (envType fvs)
      -> envOf ctypeDenote fvs) with
      | nil => fun _ _ => tt
      | first :: rest => fun fvs =>
        match fvs return (ptypeDenote (envType (envT := first :: rest) fvs)
          -> envOf (envT := first :: rest) ctypeDenote fvs) with
          | (false, fvs') => fun env => makeEnv rest fvs' env
          | (true, fvs') => fun env => (fst env, makeEnv rest fvs' (snd env))
        end
    end.

  Theorem unpackTerm_correct : forall (envT : list ptype) (fvs : isfree envT)
    (ps : cprimops ctypeDenote (envType fvs))
    (e : envOf ctypeDenote fvs -> cterm ctypeDenote result) k,
    ctermDenote (unpackTerm ps e) k
    = ctermDenote (e (makeEnv _ _ (cprimopsDenote ps))) k.
    induction envT; my_matching.
  Qed.

  Lemma lookup_type_more : forall v2 envT (fvs : isfree envT) t b v,
    (v2 = length envT -> False)
    -> lookup_type v2 (envT := t :: envT) (b, fvs) = v
    -> lookup_type v2 fvs = v.
    equation_expensive.
  Qed.

  Lemma lookup_type_less : forall v2 t envT (fvs : isfree (t :: envT)) v,
    (v2 = length envT -> False)
    -> lookup_type v2 (snd fvs) = v
    -> lookup_type v2 (envT := t :: envT) fvs = v.
    equation_expensive.
  Qed.

  Lemma lookup_bound_contra_eq : forall t envT (fvs : isfree envT) v,
    lookup_type v fvs = Some t
    -> v = length envT
    -> False.
    simpler; eapply lookup_bound_contra; eauto.
  Defined.

  Lemma lookup_type_inner : forall result t envT v t' (fvs : isfree envT) e,
    wfTerm (envT := t :: envT) (true, fvs) e
    -> lookup_type v (snd (fvsTerm (result := result) e (t :: envT))) = Some t'
    -> lookup_type v fvs = Some t'.
    Hint Resolve lookup_bound_contra_eq fvsTerm_minimal
      lookup_type_more lookup_type_less.
    Hint Extern 2 (Some _ = Some _) => contradictory.

    eauto 6.
  Qed.

  Lemma cast_irrel : forall T1 T2 x (H1 H2 : T1 = T2),
    (x :? H1) = (x :? H2).
    equation_expensive.
  Qed.

  Hint Immediate cast_irrel.

  Lemma cast_irrel_unit : forall T1 T2 x y (H1 : T1 = T2) (H2 : unit = T2),
    (x :? H1) = (y :? H2).
    intros; generalize H1;
      rewrite <- H2 in H1;
        equation_expensive.
    generalize H0 H2; simpler.
  Qed.

  Hint Immediate cast_irrel_unit.

  Hint Extern 3 (_ = _) =>
    match goal with
      | [ |- context[False_rect _ ?H] ] =>
        apply False_rect; exact H
    end.

  Theorem packTerm_correct : forall v2 t envT (fvs1 fvs2 : isfree envT)
    Heq1 (Heq2 : ctypeDenote <| lookup_type v2 fvs2 = ptypeDenote t)
    Hincl env,
    (lookup ctypeDenote v2 env :? Heq2)
    = (lookup ctypeDenote v2
      (makeEnv envT fvs1
        (cprimopsDenote
          (packTerm fvs1 fvs2 Hincl env))) :? Heq1).
    induction envT; my_equation.
  Qed.
End packing_correct.

Lemma look : forall envT n (fvs : isfree envT) t,
  lookup_type n fvs = Some t
  -> ctypeDenote <| lookup_type n fvs = ptypeDenote t.
  equation.
Qed.

Implicit Arguments look [envT n fvs t].


Theorem ccTerm_correct : forall result G
  (e1 : pterm ptypeDenote result)
  (e2 : pterm natvar result),
  pterm_equiv G e1 e2
  -> forall (envT : list ptype) (fvs : isfree envT)
    (env : envOf ctypeDenote fvs) (Hwf : wfTerm fvs e2) k,
    (forall t (v1 : ptypeDenote t) (v2 : natvar t),
      In (vars (x := t) (v1, v2)) G
      -> v2 < length envT)
    -> (forall t (v1 : ptypeDenote t) (v2 : natvar t),
      In (vars (x := t) (v1, v2)) G
      -> lookup_type v2 fvs = Some t
      -> forall Heq, (lookup ctypeDenote v2 env :? Heq) = v1)
    -> ptermDenote e1 k
    = ctermDenote (cfuncsDenote (ccTerm e2 fvs Hwf) k env) k.

  Hint Rewrite splicePrim_correct spliceTerm_correct
    spliceFuncs_correct inside_correct : ltamer.

  Hint Rewrite unpackTerm_correct : ltamer.
  Hint Resolve packTerm_correct lookup_type_inner.

  Hint Extern 1 (_ = _) => push_vars.

  Hint Extern 1 (_ = _) =>
    match goal with
      | [ Hvars : forall t v1 v2, _,
        Hin : In _ _ |- _ ] =>
      rewrite (Hvars _ _ _ Hin)
    end.

  Hint Extern 1 (wfPrimop _ _) => tauto.

  Hint Extern 1 (_ < _) =>
    match goal with
      | [ Hvars : forall t v1 v2, _,
        Hin : In _ _ |- _ ] =>
      exact (Hvars _ _ _ Hin)
    end.

  Hint Extern 1 (lookup_type _ _ = _) => tauto.

  Hint Extern 1 (_ = _) =>
    match goal with
      | [ Hvars : forall t v1 v2, _,
        Hin : In (vars (_, length ?envT)) _ |- _ ] =>
      contradictory; assert (length envT < length envT); [auto | omega]
    end.

  Hint Extern 5 (_ = _) => symmetry.

  Hint Extern 1 (_ = _) =>
    match goal with
      | [ H : lookup_type ?v _ = Some ?t, fvs : isfree _ |- (lookup _ _ _ :? _) = _ ] =>
        let Hty := fresh "Hty" in
          (assert (Hty : lookup_type v fvs = Some t);
            [eauto
              | eapply (trans_cast (look Hty))])
    end.

  Hint Extern 3 (ptermDenote _ _ = ctermDenote _ _) =>
    match goal with
      | [ H : _ |- ptermDenote (_ ?v1) _
        = ctermDenote (cfuncsDenote (ccTerm (_ ?v2) (envT := ?envT) ?fvs _) _ _) _ ] =>
      apply (H v1 v2 envT fvs); my_simpler
    end.

  intro.
  apply (pterm_equiv_mut
    (fun G (e1 : pterm ptypeDenote result) (e2 : pterm natvar result) =>
      forall (envT : list ptype) (fvs : isfree envT)
        (env : envOf ctypeDenote fvs) (Hwf : wfTerm fvs e2) k,
         (forall t (v1 : ptypeDenote t) (v2 : natvar t),
           In (vars (x := t) (v1, v2)) G
           -> v2 < length envT)
         -> (forall t (v1 : ptypeDenote t) (v2 : natvar t),
           In (vars (x := t) (v1, v2)) G
           -> lookup_type v2 fvs = Some t
           -> forall Heq, (lookup ctypeDenote v2 env :? Heq) = v1)
         -> ptermDenote e1 k
         = ctermDenote (cfuncsDenote (ccTerm e2 fvs Hwf) k env) k)
    (fun G t (p1 : pprimop ptypeDenote result t) (p2 : pprimop natvar result t) =>
      forall (envT : list ptype) (fvs : isfree envT)
        (env : envOf ctypeDenote fvs) (Hwf : wfPrimop fvs p2) Hwf k,
        (forall t (v1 : ptypeDenote t) (v2 : natvar t),
          In (vars (x := t) (v1, v2)) G
          -> v2 < length envT)
        -> (forall t (v1 : ptypeDenote t) (v2 : natvar t),
          In (vars (x := t) (v1, v2)) G
          -> lookup_type v2 fvs = Some t
          -> forall Heq, (lookup ctypeDenote v2 env :? Heq) = v1)
        -> pprimopDenote p1 k
        = cprimopsDenote (cfuncsDenote (ccPrimop p2 fvs Hwf) k env)));
  my_simpler; eauto.
Qed.


(** * Parametric version *)

Section wf.
  Variable result : ptype.

  Lemma Pterm_wf' : forall G (e1 e2 : pterm natvar result),
    pterm_equiv G e1 e2
    -> forall envT (fvs : isfree envT),
      (forall t (v1 v2 : natvar t), In (vars (v1, v2)) G
        -> lookup_type v1 fvs = Some t)
      -> wfTerm fvs e1.
    Hint Extern 3 (Some _ = Some _) => contradictory; eapply lookup_bound_contra; eauto.

    apply (pterm_equiv_mut
      (fun G (e1 e2 : pterm natvar result) =>
        forall envT (fvs : isfree envT),
          (forall t (v1 v2 : natvar t), In (vars (v1, v2)) G
            -> lookup_type v1 fvs = Some t)
          -> wfTerm (envT:=envT) fvs e1)
      (fun G t (p1 p2 : pprimop natvar result t) =>
        forall envT (fvs : isfree envT),
          (forall t (v1 v2 : natvar t), In (vars (v1, v2)) G
            -> lookup_type v1 fvs = Some t)
          -> wfPrimop (envT:=envT) fvs p1));
    simpler_expensive;
    match goal with
      | [ envT : list ptype, H : _ |- _ ] =>
        apply (H (length envT) (length envT)); simpler
    end;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; simpler
    end.
  Qed.

  Theorem Pterm_wf : forall (E : Pterm result),
    wfTerm (envT := nil) tt (E _).
    intros; eapply Pterm_wf';
      [apply Pterm_equiv
        | simpler].
  Qed.
End wf.

Definition CcTerm result (E : Pterm result) : Cprog result :=
  CcTerm' E (Pterm_wf E).

Lemma map_funcs_correct : forall result T1 T2 (f : T1 -> T2) (fs : cfuncs ctypeDenote result T1) k,
  cfuncsDenote (map_funcs f fs) k = f (cfuncsDenote fs k).
  induction fs; equation.
Qed.

Theorem CcTerm_correct : forall result (E : Pterm result) k,
  PtermDenote E k
  = CprogDenote (CcTerm E) k.
  Hint Rewrite map_funcs_correct : ltamer.

  unfold PtermDenote, CprogDenote, CcTerm, CcTerm', cprogDenote;
    simpler;
    apply (ccTerm_correct (result := result)
      (G := nil)
      (e1 := E _)
      (e2 := E _)
      (Pterm_equiv _ _ _)
      nil
      tt
      tt);
    simpler.
Qed.
