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

Require Import Arith Bool.

Require Import LambdaTamer.LambdaTamer.

Require Import CPS.
Require Import Closed.

Set Implicit Arguments.


Section cc.
  Variable var : Type.

  Import CPS.
  Open Scope closed_scope.

  Section wf.
    Open Scope cps_scope.

    Fixpoint wfE (G : nat) (e : CPS.exp nat) {struct e} : Prop :=
      match e with
        | EHalt x => x < G
        | Call x1 x2 => x1 < G /\ x2 < G
        | Bind p e' => wfP G p /\ wfE (S G) (e' G)
        | ECase x e1 e2 => x < G /\ wfE (S G) (e1 G) /\ wfE (S G) (e2 G)
        | EUncaught x => x < G
      end

    with wfP (G : nat) (p : CPS.primop nat) {struct p} : Prop :=
      match p with
        | Abs e => wfE (S (S G)) (e (S G) G)

        | Unit => True

        | Pair x1 x2 => x1 < G /\ x2 < G
        | Fst x => x < G
        | Snd x => x < G

        | Inl x => x < G
        | Inr x => x < G

        | New x => x < G
        | Read x => x < G
        | Write x1 x2 => x1 < G /\ x2 < G

        | Const _ => True
        | Eq x1 x2 => x1 < G /\ x2 < G
      end.
  End wf.

  (** ** Translating expressions *)

  Definition fvs := ilist bool.

  Definition eenvF (b : bool) :=
    if b then var else unit.
  Definition eenv := ihlist eenvF.

  Fixpoint none (G : nat) : fvs G :=
    match G return fvs G with
      | O => INil
      | S G' => false ::: none G'
    end.

  Implicit Arguments none [G].

  Fixpoint one (x : nat) (G : nat) {struct G} : fvs G :=
    match G return fvs G with
      | O => INil
      | S G' => (if eq_nat_dec x G' then true else false) ::: one x G'
    end.

  Definition merge G : fvs G -> fvs G -> fvs G :=
    imap2 orb (n := G).

  Fixpoint usedP G (p : primop nat) {struct p} : fvs G :=
    match p with
      | Abs e => itail (itail (usedE (S (S G)) (e (S G) G)))

      | Unit => none

      | Pair x1 x2 => merge (one x1 G) (one x2 G)
      | EFst x => one x G
      | ESnd x => one x G

      | EInl x => one x G
      | EInr x => one x G

      | New x => one x G
      | Read x => one x G
      | Write x1 x2 => merge (one x1 G) (one x2 G)

      | Const _ => none
      | Eq x1 x2 => merge (one x1 G) (one x2 G)
    end

  with usedE G (e : exp nat) {struct e} : fvs G :=
    match e with
      | EHalt x => one x G
      | EUncaught x => one x G
      | Call f x => merge (one f G) (one x G)
      | Bind p e' => merge (usedP G p) (itail (usedE (S G) (e' G)))
      | ECase x e1 e2 => merge (one x G) (merge (itail (usedE (S G) (e1 G))) (itail (usedE (S G) (e2 G))))
    end.

  Lemma oneE_step : forall x G,
    x <> G
    -> x < S G
    -> x < G.
    simpler.
  Qed.

  Implicit Arguments oneE_step [x G].

  Lemma lt_contra : forall n,
    n < 0 -> False.
    simpler.
  Qed.

  Fixpoint oneE (x : nat) (G : nat) {struct G}
    : eenv (one x G) -> x < G -> var :=
    match G return eenv (one x G) -> x < G -> var with
      | O => fun _ Hget => match lt_contra Hget with end
      | S G' =>
        match eq_nat_dec x G' as b return
          eenv (n := S G') ((if b then true else false) ::: one _ _)
          -> x < S G' -> var with
          | left Heq => fun eE Hget => ihhead eE
          | right Hne => fun (eE : eenv (_ ::: one _ _)) Hget => oneE (ihtail eE) (oneE_step Hne Hget)
        end
    end.

  Fixpoint unmerge1 G (ue1 : fvs G) {struct ue1}
    : forall ue2, eenv (merge ue1 ue2) -> eenv ue1 :=
    match ue1 return forall ue2, eenv (merge ue1 ue2) -> eenv ue1 with
      | INil => fun _ _ =>
        IHNil
      | ICons _ b1 ue1' => fun ue2 =>
        if b1 return eenv (merge (b1 ::: ue1') ue2) -> eenv (b1 ::: ue1')
          then fun eE => ihhead eE :::* unmerge1 _ _ (ihtail eE)
          else fun eE => (tt : eenvF false)
            :::* unmerge1 _ _ (ihtail eE)
    end.

  Implicit Arguments unmerge1 [G ue1 ue2].

  Fixpoint unmerge2 G (ue1 : fvs G) {struct ue1}
    : forall ue2, eenv (merge ue1 ue2) -> eenv ue2 :=
    match ue1 return forall ue2, eenv (merge ue1 ue2) -> eenv ue2 with
      | INil => fun _ _ => IHNil' _
      | ICons _ b1 ue1' => fun ue2 =>
        match ue2 in ilist _ G return forall (ue1' : ilist _ (pred G))
          (self : forall ue2, eenv (merge ue1' ue2) -> eenv ue2),
          match G return ilist _ (pred G) -> ilist _ G -> Type with
            | O => fun _ _ => unit
            | S _ => fun ue1' ue2 => eenv (merge (b1 ::: ue1') ue2) -> eenv ue2
          end ue1' ue2 with
          | INil => fun _ _ => tt
          | ICons _ b2 ue2' => fun ue1' self =>
            if b1 return eenv (merge (b1 ::: ue1') (b2 ::: ue2')) -> eenv (b2 ::: ue2')
              then if b2 return eenv (merge (true ::: ue1') (b2 ::: ue2')) -> eenv (b2 ::: ue2')
                then fun eE => ihhead eE :::* self _ (ihtail eE)
                else fun eE => (tt : eenvF false) :::* self _ (ihtail eE)
              else if b2 return eenv (merge (false ::: ue1') (b2 ::: ue2')) -> eenv (b2 ::: ue2')
                then fun eE => ihhead eE :::* self _ (ihtail eE)
                else fun eE => (tt : eenvF false) :::* self _ (ihtail eE)
        end ue1' (unmerge2 _)
    end.

  Implicit Arguments unmerge2 [G ue1 ue2].

  Definition push' (x : var) G b
    (ue : fvs G) (eE : eenv ue) : eenv (b ::: ue) :=
    (if b return (if b then _ else _)
      then x
      else tt) :::* eE.

  Implicit Arguments push' [G b ue].

  Definition push (x : var) G (ue : fvs (S G))
    : eenv (itail ue) -> eenv ue :=
    match ue in ilist _ n return match n return ilist _ n -> Type with
                                   | O => fun _ => unit
                                   | S _ => fun ue => var -> eenv (itail ue) -> eenv ue
                                 end ue with
      | INil => tt
      | ICons _ b ue' => fun x uE => push' x uE
    end x.

  Implicit Arguments push [G ue].
  Infix "+!" := push (right associativity, at level 35).

  Fixpoint envProd G (ue : fvs G) {struct ue} : nat :=
    match ue with
      | INil => O
      | ICons _ true ue' => S (envProd ue')
      | ICons _ false ue' => envProd ue'
    end.

  Fixpoint makeEnv G (ue : fvs G) {struct ue} : eenv ue -> (var -> Closed.exp var) -> Closed.exp var :=
    match ue return eenv ue -> _ with
      | INil => fun _ k =>
        p <- ();
        k p
      | ICons _ b ue' =>
        if b return eenv (b ::: ue') -> _
          then fun eE k => makeEnv (ihtail eE) (fun p' => p <- [< (ihhead eE : var), p' >]; k p)
          else fun eE k => makeEnv (ihtail eE) k
    end.

  Fixpoint supplyEnv G (ue : fvs G) (p : var) {struct ue}
    : (eenv ue -> Closed.exp var) -> Closed.exp var :=
    match ue return (eenv ue -> Closed.exp var) -> _ with
      | INil => fun k => k IHNil
      | ICons _ b ue' =>
        if b return (eenv (b ::: ue') -> _) -> _
          then fun k =>
            x <- Fst p;
            p' <- Snd p;
            supplyEnv p' (fun eE => k ((x : eenvF true) :::* eE))
          else fun k =>
            supplyEnv (ue := ue') p (fun eE => k ((tt : eenvF false)
              :::* eE))
    end.

  Fixpoint ccPrimop G (p : primop nat) {struct p}
    : wfP G p
    -> (((eenv (usedP G p)
      -> (var -> Closed.exp var)
      -> Closed.exp var)
    -> Closed.prog var)
    -> Closed.prog var) :=
    match p return wfP G p -> (((eenv (usedP G p)
      -> (var -> Closed.exp var)
      -> Closed.exp var)
    -> Closed.prog var)
    -> Closed.prog var) with
      | Abs e => fun wf k =>
        ccExp (e (S G) G) wf (fun ke =>
          f <== \\F, p,
            veE <- Fst p;
            arg <- Snd p;
            F' <- [< veE, F >];
            supplyEnv veE
            (fun eE => ke (F' +! arg +! eE));
          k (fun (eE : eenv (itail (itail (usedE (S (S G)) (e (S G) G))))) k' =>
            makeEnv eE (fun veE =>
              cl <- [< veE, f >];
              k' cl)))

      | Unit => fun _ k =>
        k (fun _ => Closed.Bind ())

      | Pair x1 x2 => fun wf k =>
        k (fun eE => Closed.Bind
          [< oneE (unmerge1 eE) (proj1 wf), oneE (unmerge2 eE) (proj2 wf) >])
      | EFst x => fun wf k =>
        k (fun eE => Closed.Bind
          (Fst (oneE eE wf)))
      | ESnd x => fun wf k =>
        k (fun eE => Closed.Bind
          (Snd (oneE eE wf)))

      | EInl x => fun wf k =>
        k (fun eE => Closed.Bind
          (Inl (oneE eE wf)))
      | EInr x => fun wf k =>
        k (fun eE => Closed.Bind
          (Inr (oneE eE wf)))

      | New x => fun wf k =>
        k (fun eE => Closed.Bind
          (Ref (oneE eE wf)))
      | Read x => fun wf k =>
        k (fun eE => Closed.Bind
          (!(oneE eE wf)))
      | Write x1 x2 => fun wf k =>
        k (fun eE => Closed.Bind
          (oneE (unmerge1 eE) (proj1 wf)
            ::= oneE (unmerge2 eE) (proj2 wf)))

      | Const b => fun _ k =>
        k (fun _ => Closed.Bind (^^b))
      | Eq x1 x2 => fun wf k =>
        k (fun eE => Closed.Bind
          (oneE (unmerge1 eE) (proj1 wf)
            == oneE (unmerge2 eE) (proj2 wf)))
    end

  with ccExp G (e : exp nat) {struct e}
    : wfE G e
    -> (((eenv (usedE G e) -> Closed.exp var) -> Closed.prog var)
      -> Closed.prog var) :=
    match e return wfE G e -> (((eenv (usedE G e) -> Closed.exp var) -> Closed.prog var)
      -> Closed.prog var) with
      | EHalt v => fun wf k =>
        k (fun eE => Halt (oneE eE wf))
      | EUncaught v => fun wf k =>
        k (fun eE => Uncaught (oneE eE wf))
    
      | Call f x => fun wf k =>
        k (fun eE =>
          env <- Fst (oneE (unmerge1 eE) (proj1 wf));
          f' <- Snd (oneE (unmerge1 eE) (proj1 wf));
          p <- [< env, oneE (unmerge2 eE) (proj2 wf) >];
          f' @@@ p)

      | Bind p e' => fun wf k =>
        ccPrimop p (proj1 wf)
        (fun kP => ccExp (e' G) (proj2 wf)
          (fun kE => k (fun eE =>
            kP (unmerge1 eE) (fun x =>
              kE (x +! unmerge2 eE)))))

      | ECase x e1 e2 => fun wf k =>
        ccExp (e1 G) (proj1 (proj2 wf)) (fun kE1 =>
          ccExp (e2 G) (proj2 (proj2 wf)) (fun kE2 =>
            k (fun eE =>
              Case (oneE (unmerge1 eE) (proj1 wf)) Of
              y => kE1 (y +! unmerge1 (unmerge2 eE))
              | z => kE2 (z +! unmerge2 (unmerge2 eE)))))
    end.
End cc.

Definition ccProg var (e : CPS.exp nat) (wf : wfE O e) : prog var :=
  ccExp e wf (fun k => EBody (k (IHNil' _))).

Import CPS.

Scheme exp_valid_mut := Minimality for exp_valid Sort Prop
with primop_valid_mut := Minimality for primop_valid Sort Prop.

Lemma Wf_var : forall G,
  (forall n, In n G -> n < length G)
  -> (forall n, length G = n \/ In n G -> n < S (length G)).
  intuition.
Qed.

Hint Resolve Wf_var.

Lemma WfE' : forall G e,
  exp_valid G e
  -> (forall n, In n G -> n < length G)
  -> wfE (length G) e.
  apply (exp_valid_mut
    (fun G e => (forall n, In n G -> n < length G)
      -> wfE (length G) e)
    (fun G p => (forall n, In n G -> n < length G)
      -> wfP (length G) p)); simpler; app; simpler.
Qed.

Theorem WfE : forall E : CPS.Exp, Exp_wf E -> wfE O (E _).
  Hint Resolve Exp_valid.

  intros; change O with (length (@nil nat)); apply WfE'; simpler.
Qed.

Definition CcProg (E : CPS.Exp) (H : Exp_wf E) : Prog := fun _ => ccProg _ (E _) (WfE H).


Implicit Arguments none [G].

Implicit Arguments push [var G ue].
Implicit Arguments push' [var G b ue].

Implicit Arguments unmerge1 [var G ue1 ue2].
Implicit Arguments unmerge2 [var G ue1 ue2].

Infix "+!" := push (right associativity, at level 35).

Implicit Arguments ccPrimop [var].
Implicit Arguments ccExp [var].
