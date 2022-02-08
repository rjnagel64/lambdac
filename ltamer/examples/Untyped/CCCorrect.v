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

Require Import Arith.

Require Import LambdaTamer.LambdaTamer.

Require Import CPS.
Require Import Closed.

Require Import CC.

Set Implicit Arguments.


(** * Define an alternate closure conversion that uses first-order binding for code. *)

Section firstOrderishCc.
  Record pcl' (G : nat) (usedP' : fvs G) : Type := Pcl' {
    sP : closures;
    payloadP' : eenv val usedP' -> (val -> expV) -> expV
  }.

  Record ecl' (G : nat) (usedE' : fvs G) : Type := Ecl' {
    sE : closures;
    payloadE' : eenv val usedE' -> expV
  }.

  Import CPS.
  Open Scope closed_scope.

  Fixpoint ccPrimop' G (p : primop nat) (s : Closed.closures) {struct p}
    : wfP G p -> pcl' (usedP G p) :=
    match p return wfP G p -> pcl' (usedP G p) with
      | Abs e => fun wf =>
        let er := ccExp' (S (S G)) (e (S G) G) s wf in
          Pcl' ((fun F p =>
            veE <- Fst p;
            arg <- Snd p;
            F' <- [< veE, F >];
            supplyEnv veE
            (fun eE => payloadE' er (F' +! arg +! eE))) :: sE er)
          (fun eE k =>
            makeEnv eE (fun veE =>
              cl <- [< veE, Closed.VCont (length (sE er)) >];
              k cl))

      | Unit => fun wf =>
        Pcl' s (fun eE => Closed.Bind ())

      | Pair x1 x2 => fun wf =>
        Pcl' s (fun eE => Closed.Bind [< oneE (unmerge1 eE) (proj1 wf), oneE (unmerge2 eE) (proj2 wf) >])
      | EFst x => fun wf =>
        Pcl' s (fun eE => Closed.Bind (Fst (oneE eE wf)))
      | ESnd x => fun wf =>
        Pcl' s (fun eE => Closed.Bind (Snd (oneE eE wf)))

      | EInl x => fun wf =>
        Pcl' s (fun eE => Closed.Bind (Inl (oneE eE wf)))
      | EInr x => fun wf =>
        Pcl' s (fun eE => Closed.Bind (Inr (oneE eE wf)))

      | New x => fun wf =>
        Pcl' s (fun eE => Closed.Bind (Ref (oneE eE wf)))
      | Read x => fun wf =>
        Pcl' s (fun eE => Closed.Bind (!(oneE eE wf)))
      | Write x1 x2 => fun wf =>
        Pcl' s (fun eE => Closed.Bind
          (oneE (unmerge1 eE) (proj1 wf)
            ::= oneE (unmerge2 eE) (proj2 wf)))

      | Const b => fun wf =>
        Pcl' s (fun eE => Closed.Bind (^^b))
      | Eq x1 x2 => fun wf =>
        Pcl' s (fun eE => Closed.Bind
          (oneE (unmerge1 eE) (proj1 wf)
            == oneE (unmerge2 eE) (proj2 wf)))
    end

  with ccExp' G (e : exp nat) (s : Closed.closures) {struct e}
    : wfE G e -> ecl' (usedE G e) :=
    match e return wfE G e -> ecl' (usedE G e) with
      | EHalt x => fun wf =>
        Ecl' s (fun eE => Halt (oneE eE wf))
      | EUncaught x => fun wf =>
        Ecl' s (fun eE => Uncaught (oneE eE wf))
    
      | Call f x => fun wf =>
        Ecl' s (fun eE =>
          env <- Fst (oneE (unmerge1 eE) (proj1 wf));
          f' <- Snd (oneE (unmerge1 eE) (proj1 wf));
          p <- [< env, oneE (unmerge2 eE) (proj2 wf) >];
          f' @@@ p)

      | Bind p e' => fun wf =>
        let pr := ccPrimop' G p s (proj1 wf) in
        let er := ccExp' (S G) (e' G) (sP pr) (proj2 wf) in
          Ecl' (sE er) (fun eE =>
            payloadP' pr (unmerge1 eE) (fun x =>
              payloadE' er (x +! unmerge2 eE)))

      | ECase x e1 e2 => fun wf =>
        let er1 := ccExp' (S G) (e1 G) s (proj1 (proj2 wf)) in
        let er2 := ccExp' (S G) (e2 G) (sE er1) (proj2 (proj2 wf)) in
          Ecl' (sE er2) (fun eE =>
            Case (oneE (unmerge1 eE) (proj1 wf)) Of
              y => payloadE' er1 (y +! unmerge1 (unmerge2 eE))
            | z => payloadE' er2 (z +! unmerge2 (unmerge2 eE)))
    end.
End firstOrderishCc.


(** * Correctness relations between source and target programs *)

Fixpoint envTuple G (ue : fvs G) {struct ue} : eenv Closed.val ue -> Closed.val :=
  match ue return eenv _ ue -> _ with
    | INil => fun _ => VUnit
    | ICons _ b _ =>
      if b return eenv _ (b ::: _) -> _
        then fun eE => VPair (ihhead eE) (envTuple (ihtail eE))
        else fun eE => envTuple (ihtail eE)
  end.

Section cr.
  Variable s1 : CPS.closures.

  Open Scope closed_scope.

  Inductive cr (s2 : Closed.closures) : CPS.val -> Closed.val -> Prop :=
  | EquivCont : forall l1 l2 G
    (f1 : CPS.val -> CPS.val -> CPS.exp CPS.val)
    (f2 : nat -> nat -> CPS.exp nat)
    s2' s2'' wf (eE : eenv _ (itail (itail (usedE (S (S (length G))) (f2 (S (length G)) (length G)))) : fvs _)),
    sE (ccExp' (S (S (length G))) (f2 (S (length G)) (length G)) s2' wf) ~> s2''
    -> s2'' ~> s2
    -> (forall F1 F2 x1 x2, CPS.exp_equiv ((F1, F2) :: (x1, x2) :: G) (f1 F1 x1) (f2 F2 x2))
    -> (forall x1 x2, In (x1, x2) G -> (ihlistOut eE) # x2 = None -> False)
    -> (forall x1 x2 v2, In (x1, x2) G -> (ihlistOut eE) # x2 = Some (existT _ true v2) -> cr s2'' x1 v2)
    -> (forall x1 x2, In (x1, x2) G -> x2 < length G)
    -> s1 # l1 = Some f1
    -> s2 # l2 = Some (fun F p =>
      veE <- Fst p;
      arg <- Snd p;
      F' <- [< veE, F >];
      supplyEnv veE
      (fun eE => payloadE' (ccExp' (S (S (length G))) (f2 (S (length G)) (length G)) s2' wf)
        (F' +! arg +! eE)))
    -> cr s2 (CPS.VCont l1) (Closed.VPair (envTuple eE) (Closed.VCont l2))

  | EquivUnit : cr s2 CPS.VUnit Closed.VUnit

  | EquivPair : forall x y x' y',
    cr s2 x x'
    -> cr s2 y y'
    -> cr s2 (CPS.VPair x y) (Closed.VPair x' y')

  | EquivInl : forall v1 v2,
    cr s2 v1 v2
    -> cr s2 (CPS.VInl v1) (Closed.VInl v2)
  | EquivInr : forall v1 v2,
    cr s2 v1 v2
    -> cr s2 (CPS.VInr v1) (Closed.VInr v2)

  | EquivRef : forall l,
    cr s2 (CPS.VRef l) (Closed.VRef l)

  | EquivBase : forall b,
    cr s2 (CPS.VBase b) (Closed.VBase b).

  Inductive crr (s2 : Closed.closures) : CPS.result -> Closed.result -> Prop :=
  | EquivAns : forall v1 v2,
    cr s2 v1 v2
    -> crr s2 (CPS.Ans v1) (Closed.Ans v2)
  | EquivEx : forall v1 v2,
    cr s2 v1 v2
    -> crr s2 (CPS.Ex v1) (Closed.Ex v2).
End cr.

Notation "s1 & s2 |-- v1 ~~ v2" := (cr s1 s2 v1 v2) (no associativity, at level 70).
Notation "s1 & s2 |--- r1 ~~ r2" := (crr s1 s2 r1 r2) (no associativity, at level 70).

Hint Constructors cr crr.

Section cr_extend'.
  Variables s1 s1' : CPS.closures.
  Hypothesis H1 : s1 ~> s1'.

  Lemma cr_extend' : forall s2 v1 v2,
    s1 & s2 |-- v1 ~~ v2
      -> forall s2', s2 ~> s2'
        -> s1' & s2' |-- v1 ~~ v2.
    induction 1; eauto 6.
  Qed.
End cr_extend'.

Theorem cr_extend : forall s1 s2 s1' s2' v1 v2,
  s1 & s2 |-- v1 ~~ v2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> s1' & s2' |-- v1 ~~ v2.
  intros; eapply cr_extend'; eauto.
Qed.

Hint Resolve cr_extend.

Theorem crr_extend : forall s1 s2 s1' s2' r1 r2,
  s1 & s2 |--- r1 ~~ r2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> s1' & s2' |--- r1 ~~ r2.
  destruct 1; eauto.
Qed.

Hint Resolve crr_extend.

Notation "s1 & s2 |-- h1 ~~~ h2" := (sall (cr s1 s2) h1 h2) (no associativity, at level 70).

Lemma EquivRef' : forall s1 s2 h1 h2,
  s1 & s2 |-- h1 ~~~ h2
  -> s1 & s2 |-- CPS.VRef (length h1) ~~ Closed.VRef (length h2).
  intros; match goal with
            | [ H : _ |- _ ] => rewrite <- (sall_length H)
          end; auto.
Qed.


(** * Correctness of [fvs] operations *)

Lemma one_correct : forall n G,
  n < G
  -> (ilistOut (one n G)) # n = Some true.
  induction G; simpler_expensive; elimtype False; omega.
Qed.

Ltac merge := intro x; dep_destruct x; simpler_expensive.

Lemma merge_correct1 : forall n G (ue1 ue2 : fvs G),
  (ilistOut ue1) # n = Some true
  -> (ilistOut (merge ue1 ue2)) # n = Some true.
  induction ue1; merge.
Qed.

Lemma merge_correct2 : forall n G (ue1 ue2 : fvs G),
  (ilistOut ue2) # n = Some true
  -> (ilistOut (merge ue1 ue2)) # n = Some true.
  Hint Rewrite orb_true_r : ltamer.

  induction ue1; merge.
Qed.

Hint Resolve one_correct merge_correct1 merge_correct2.
Hint Rewrite one_correct merge_correct1 merge_correct2 using solve [ auto ] : ltamer.


(** * Correctness of [eenv] operations *)

Ltac eenv := simpler_expensive;
  repeat match goal with
           | [ |- context[if ?b then _ else _] ] => destruct b
         end;
  simpler;
  (elimtype False; omega)
  || match goal with
       | [ eE : _ |- _ ] => 
         match goal with
           | [ H : (ihlistOut _) # _ = _ |- _ ] => rewrite (ihlist_cons eE) in H; simpler_expensive
         end
     end.

Lemma oneE_correct : forall v n G wf (eE : eenv _ (one n G)),
  (ihlistOut eE) # n = Some (existT (eenvF val) true v)
  -> oneE eE wf = v.
  induction G; eenv.
Qed.

Implicit Arguments oneE_correct [n G wf eE].

Ltac unmerge := intro x; dep_destruct x; eenv.

Lemma unmerge1_correct : forall (v : sigT (eenvF val)) n G (ue1 ue2 : fvs G) (eE : eenv _ (merge ue1 ue2)),
  (ihlistOut eE) # n = Some v
  -> (ilistOut ue1) # n = Some true
  -> (ihlistOut (unmerge1 eE)) # n = Some v.
  induction ue1; unmerge.
Qed.

Lemma unmerge2_correct : forall (v : sigT (eenvF val)) n G (ue1 ue2 : fvs G) (eE : eenv _ (merge ue1 ue2)),
  (ihlistOut eE) # n = Some v
  -> (ilistOut ue2) # n = Some true
  -> (ihlistOut (unmerge2 eE)) # n = Some v.
  induction ue1; unmerge.
Qed.

Implicit Arguments unmerge1_correct [n G ue1 ue2 eE].
Implicit Arguments unmerge2_correct [n G ue1 ue2 eE].

Hint Resolve unmerge1_correct unmerge2_correct.


(** * Reading from environments *)

Ltac solver := solve [ repeat (solve [ auto ]
  || apply unmerge1_correct || apply unmerge2_correct || apply one_correct
    || match goal with
         | [ H : _ /\ _ |- _ ] => generalize H; tauto
       end) ].

Ltac env_rewriter :=
  match goal with
    | [ H : _ # _ = Some (existT _ _ ?v) |- _ ] =>
      rewrite (oneE_correct v); [ | solver ]
    | [ H : _ # _ = Some ?v |- _ ] =>
      (rewrite (unmerge1_correct v) || rewrite (unmerge2_correct v));
      [ | solver | solver ]
    | [ H : _ & _ |-- _ ~~~ _ |- _ ] => rewrite <- (sall_length H)
  end.

Ltac vars := simpler;
  repeat (match goal with
            | [ s : sigT _ |- _ ] => destruct s
            | [ b : bool |- _ ] => destruct b
              
            | [ H : forall (v1 : CPS.val) (n : nat), In _ _
                  -> match (ihlistOut ?eE) # n with | Some _ => _ | None => _ end,
                H' : In (_, ?n) _ |- _ ] => generalize (H _ _ H'); clear H';
              case_eq ((ihlistOut eE) # n); intros; subst

            | [ H : forall i : fin (S _), _ |- _ ] =>
              generalize (H FO); generalize (fun i => H (FS i)); clear H
            | [ H : forall i : fin ?n, match (ihlistOut ?eE) # (iget ?vs i) with Some _ => _ | None => _ end
                |- match _ # (iget ?vs ?i) with Some _ => _ | None => _ end ] =>
              generalize (H i); case_eq ((ihlistOut eE) # (iget vs i)); clear H

            | [ H : match (ihlistOut ?eE) # ?n with Some _ => _ | None => _ end |- _ ] =>
              generalize dependent H; case_eq ((ihlistOut eE) # n)

            | _ => env_rewriter
          end; simpler).

Ltac envcontra := simpler;
  match goal with
    | [ eE : eenv _ _ |- _ ] => rewrite (ihlist_nil eE) in * || rewrite (ihlist_cons eE) in *
  end; simpler_expensive; eauto.

Lemma ihlistOut_one_contra : forall v G (eE : eenv _ (one v G)),
  (ihlistOut eE) # v = Some (existT (eenvF val) false tt)
  -> False.
  induction G; envcontra.
Qed.

Ltac mcontra := intro x; dep_destruct x; envcontra.

Lemma ihlistOut_merge_contra1 : forall v G (ue1 ue2 : fvs G) (eE : eenv _ (merge ue1 ue2)),
  (ihlistOut eE) # v = Some (existT (eenvF val) false tt)
  -> (ilistOut ue1) # v = Some true
  -> False.
  induction ue1; mcontra.
Qed.

Lemma ihlistOut_merge_contra2 : forall v G (ue1 ue2 : fvs G) (eE : eenv _ (merge ue1 ue2)),
  (ihlistOut eE) # v = Some (existT (eenvF val) false tt)
  -> (ilistOut ue1) # v = Some true
  -> False.
  induction ue1; mcontra.
Qed.

Hint Resolve ihlistOut_one_contra ihlistOut_merge_contra1 ihlistOut_merge_contra2.


(** * Compatibility of source and target environments *)

Definition varOk G (ue : fvs G) (eE : eenv Closed.val ue) s1 s2 v1 v2 :=
  match (ihlistOut eE) # v2 with
    | Some (existT b v2) =>
      (if b return (eenvF Closed.val b -> Prop)
        then fun v2 => s1 & s2 |-- v1 ~~ v2
        else fun _ => True) v2
    | None => False
  end.

Lemma grab_varOk' : forall e v G (ue : CC.fvs G) (eE : CC.eenv _ ue),
  (ihlistOut eE) # v = Some (existT (CC.eenvF Closed.val) false e)
  -> (ilistOut ue) # v = Some true
  -> False.
  induction eE; simpler_expensive.
Qed.

Lemma grab_varOk'' : forall e v G (ue : CC.fvs G) (eE : CC.eenv _ ue),
  (ihlistOut eE) # v = Some (existT (CC.eenvF Closed.val) false e)
  -> (ilistOut ue) # v = Some false.
  induction eE; simpler_expensive.
Qed.

Lemma grab_varOk : forall G (ue : CC.fvs G) (eE : CC.eenv _ ue) s1 s2 v1 v2,
  varOk eE s1 s2 v1 v2
  -> (ilistOut ue) # v2 = Some true
  -> exists x, (ihlistOut eE) # v2 = Some (existT _ true x) /\ s1 & s2 |-- v1 ~~ x.
  Hint Resolve grab_varOk'.
  Hint Rewrite grab_varOk'' : ltamer.

  unfold varOk; vars; eauto; elimtype False; eauto.
Qed.

Ltac simplr := simpler;
  repeat match goal with
           | [ s : sigT _ |- _ ] => destruct s
           | [ b : bool |- _ ] => destruct b

           | [ H : _ & _ |-- _ ~~ _ |- _ ] => invert_1 H; intros; subst

           | [ H : forall (v1 : CPS.val) n, In _ _
               -> varOk ?eE _ _ _ n,
               H' : In (_, ?n) _ |- _ ] => generalize (H _ _ H'); clear H'; intro H'

           | [ H : varOk ?eE ?s1 ?s2 ?v1 ?v2 |- _ ] =>
             match type of eE with
               | CC.eenv _ ?ue =>
                 let H' := fresh "H'" in
                   assert (H' : (ilistOut ue) # v2 = Some true); [
                     solve [ eauto ]
                     | destruct (grab_varOk _ _ _ _ _ H H') as [? [? ?]]; clear H H'
                   ]
             end

           | [ H : _ & _ |-- ?h ~~~ _, H' : ?h # _ = Some _ |- _ ] =>
             destruct (sall_grab H H'); clear H'

           | _ => env_rewriter
         end; simpler.

Lemma push'_varOk : forall v1' v2' G (ue : fvs (length G)) b (eE : eenv _ ue) s1 s2,
  s1 & s2 |-- v1' ~~ v2'
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) G -> varOk eE s1 s2 v1 v2)
  -> (forall v1 v2, In (v1, v2) G -> v2 < length G)
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) ((v1', length G) :: G) -> varOk (push' (b := b) v2' eE) s1 s2 v1 v2).
  unfold varOk; destruct b; simpler_expensive; try (app; auto);
    elimtype False;
    match goal with
      | [ H : forall v1 v2, In _ _ -> _, H' : In _ _ |- _ ] => generalize (H _ _ H'); omega
    end.
Qed.

Lemma push_varOk : forall v1' v2' G (ue : fvs (S (length G))) (eE : eenv _ (itail ue)) s1 s2,
  s1 & s2 |-- v1' ~~ v2'
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) G -> varOk eE s1 s2 v1 v2)
  -> (forall v1 v2, In (v1, v2) G -> v2 < length G)
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) ((v1', length G) :: G) -> varOk (G := S (length G)) (v2' +! eE) s1 s2 v1 v2).
  Hint Resolve push'_varOk.

  unfold push; intros; dep_destruct ue; eauto.
Qed.

Implicit Arguments push_varOk [G ue s1 s2].

Lemma pushA'_varOk : forall F1 F2 v1' v2' G (ue : fvs (length G)) bF b (eE : eenv _ ue) s1 s2,
  s1 & s2 |-- F1 ~~ F2
  -> s1 & s2 |-- v1' ~~ v2'
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) G -> varOk eE s1 s2 v1 v2)
  -> (forall v1 v2, In (v1, v2) G -> v2 < length G)
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) ((F1, S (length G)) :: (v1', length G) :: G)
    -> varOk (push' (b := bF) F2 (push' (b := b) v2' eE)) s1 s2 v1 v2).
  unfold varOk; destruct bF; destruct b; simpler_expensive; try (app; auto);
    elimtype False; try omega;
      match goal with
        | [ H : forall v1 v2, In _ _ -> _, H' : In _ _ |- _ ] => generalize (H _ _ H'); omega
      end.
Qed.

Lemma pushA_varOk : forall F1 F2 v1' v2' G (ue : fvs (S (S (length G)))) (eE : eenv _ (itail (itail ue))) s1 s2,
  s1 & s2 |-- F1 ~~ F2
  -> s1 & s2 |-- v1' ~~ v2'
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) G -> varOk eE s1 s2 v1 v2)
  -> (forall v1 v2, In (v1, v2) G -> v2 < length G)
  -> (forall (v1 : CPS.val) (v2 : nat),
    In (v1, v2) ((F1, S (length G)) :: (v1', length G) :: G)
    -> varOk (G := S (S (length G))) (F2 +! v2' +! eE) s1 s2 v1 v2).
  Hint Resolve pushA'_varOk.

  unfold push, fvs; intros; repeat match goal with
                                     | [ x : ilist _ (S _) |- _ ] => dep_destruct x
                                   end; eauto.
Qed.

Implicit Arguments pushA_varOk [G ue s1 s2].

Ltac unmerge_varOk :=
  unfold varOk in *; intro x; dep_destruct x; try discriminate;
    match goal with
      | [ H : match (ihlistOut ?eE) # _ with Some _ => _ | None => _ end |- _ ] =>
        rewrite (ihlist_nil eE) in H || rewrite (ihlist_cons eE) in H
    end; simpler;
    repeat match goal with
             | [ |- context[if ?a then _ else _] ] => destruct a
           end; simpler_expensive; app; auto.

Lemma unmerge1_varOk : forall s1 s2 v1 v2 G (ue1 ue2 : fvs G) (eE : eenv _ (merge ue1 ue2)),
  varOk eE s1 s2 v1 v2
  -> varOk (unmerge1 eE) s1 s2 v1 v2.
  induction ue1; unmerge_varOk.
Qed.

Lemma unmerge2_varOk : forall s1 s2 v1 v2 G (ue1 ue2 : fvs G) (eE : eenv _ (merge ue1 ue2)),
  varOk eE s1 s2 v1 v2
  -> varOk (unmerge2 eE) s1 s2 v1 v2.
  induction ue1; unmerge_varOk.
Qed.

Lemma varOk_extend : forall G (ue : fvs G) (eE : eenv _ ue) s1 s2 v1 v2 s1' s2',
  varOk eE s1 s2 v1 v2
  -> s1 ~> s1'
  -> s2 ~> s2'
  -> varOk eE s1' s2' v1 v2.
  unfold varOk; vars; eauto.
Qed.

Implicit Arguments varOk_extend [G ue eE s1 s2 v1 v2].

Ltac closure := unfold varOk; intros;
  match goal with
    | [ H1 : _, H2 : _ |- _ ] => solve [ rewrite H1 in H2; assumption ]
  end.

Lemma varOk_closure : forall s1 s2 v1 n v2
  G (ue : fvs G) (eE : eenv val ue),
  varOk eE s1 s2 v1 n
  -> (ihlistOut eE) # n = Some (existT _ true v2)
  -> s1 & s2 |-- v1 ~~ v2.
  closure.
Qed.

Lemma varOk_closure_contra : forall s1 s2 v1 n
  G (ue : fvs G) (eE : eenv val ue),
  varOk eE s1 s2 v1 n
  -> (ihlistOut eE) # n = None
  -> False.
  closure.
Qed.

Lemma varOk_alt : forall s1 s2' G0 s2'' n (il : ilist _ n)
  (eE0 : eenv val il),
  (forall (x1 : CPS.val) (x2 : nat),
    In (x1, x2) G0 -> (ihlistOut eE0) # x2 = None -> False)
  -> (forall (x1 : CPS.val) (x2 : nat) (v2 : val),
    In (x1, x2) G0
    -> (ihlistOut eE0) # x2 = Some (existT (eenvF val) true v2)
    -> s1 & s2'' |-- x1 ~~ v2)
  -> s2'' ~> s2'
  -> forall (v1 : CPS.val) (v2 : nat), In (v1, v2) G0
    -> varOk eE0 s1 s2' v1 v2.
  intros; red; case_eq ((ihlistOut eE0) # v2); simplr; eauto.
Qed.


(** * Proving that variable numbers are in bounds *)

Lemma push_bound : forall v1 (G0 : list (CPS.val * nat)),
  (forall v3 n, In (v3, n) G0 -> n < length G0)
  -> (forall v3 n, In (v3, n) ((v1, length G0) :: G0)
    -> n < S (length G0)).
  simpler; firstorder.
Qed.

Lemma pushA_bound : forall F1 v1 (G0 : list (CPS.val * nat)),
  (forall v3 n, In (v3, n) G0 -> n < length G0)
  -> (forall v3 n, In (v3, n) ((F1, S (length G0)) :: (v1, length G0) :: G0)
    -> n < S (S (length G0))).
  simpler; firstorder.
Qed.


(** * Monotonicity of the alternate translations *)

Scheme exp_mut := Induction for CPS.exp Sort Prop
with primop_mut := Induction for CPS.primop Sort Prop.

Ltac cc_monotone ind :=
  apply (ind _
    (fun e => forall G s wf,
      s ~> sE (ccExp' G e s wf))
    (fun p => forall G s wf,
      s ~> sP (ccPrimop' G p s wf))); abstract (simpler; eauto).

Theorem ccExp'_monotone : forall e G s wf,
  s ~> sE (ccExp' G e s wf).
  cc_monotone exp_mut.
Qed.

Theorem ccPrimop'_monotone : forall p G s wf,
  s ~> sP (ccPrimop' G p s wf).
  cc_monotone primop_mut.
Qed.

Theorem ccExp'_monotone_trans : forall G e wf s1 s2,
  sE (ccExp' G e s1 wf) ~> s2
  -> s1 ~> s2.
  intros; eapply extends_trans; [ apply ccExp'_monotone | eassumption ].
Qed.


(** * Correctness of primop translation *)

Hint Constructors evalP eval.

Theorem makeEnv_correct : forall s h r G (ue : fvs G) (eE : eenv Closed.val ue) k,
  Closed.eval s h (k (envTuple eE)) r
  -> Closed.eval s h (makeEnv eE k) r.
  induction eE; simplr; eauto.
Qed.

Hint Resolve makeEnv_correct.

Theorem ccPrimop'_correct : forall s1 h1 p1 s1' h1' v1,
  CPS.evalP s1 h1 p1 s1' h1' v1
  -> forall G p2 wf s2 s2' h2 eE,
    CPS.primop_equiv G p1 p2
    -> (forall v1 n, In (v1, n) G -> varOk eE s1 s2' v1 n)
    -> (forall v1 n, In (v1, n) G -> n < length G)
    -> s1 & s2' |-- h1 ~~~ h2
    -> sP (ccPrimop' (length G) p2 s2 wf) ~> s2'
    -> exists h2', exists v2,
      (forall k r, Closed.eval s2' h2' (k v2) r
        -> Closed.eval s2' h2 (payloadP' (ccPrimop' (length G) p2 s2 wf) eE k) r)
      /\ s1' & s2' |-- v1 ~~ v2
      /\ s1' & s2' |-- h1' ~~~ h2'.
  Hint Resolve EquivRef' varOk_closure varOk_closure_contra.
  Hint Resolve ccExp'_monotone.

  induction 1; abstract (inversion 1; simplr;
    try match goal with
          | [ wf : _ /\ _ |- _ ] => generalize (one_correct (proj1 wf));
            generalize (one_correct (proj2 wf)); simplr
        end; splitter; eauto;
    econstructor; try (eapply extends_trans; [ eapply extends_cons | eassumption ]); eauto).
Qed.


(** * The main theorem about [ccExp'] *)

Theorem supplyEnv_correct : forall s h r G (ue : fvs G) (eE : eenv Closed.val ue) (k : eenv Closed.val ue -> Closed.expV),
  Closed.eval s h (k eE) r
  -> Closed.eval s h (supplyEnv (envTuple eE) k) r.
  induction eE; simplr.
Qed.

Inductive comp : CPS.val -> Closed.val -> Prop :=
| CompCont : forall l v,
  comp (CPS.VCont l) v

| CompUnit : comp CPS.VUnit Closed.VUnit

| CompPair : forall x y x' y',
  comp x x'
  -> comp y y'
  -> comp (CPS.VPair x y) (Closed.VPair x' y')

| CompInl : forall v1 v2,
  comp v1 v2
  -> comp (CPS.VInl v1) (Closed.VInl v2)
| CompInr : forall v1 v2,
  comp v1 v2
  -> comp (CPS.VInr v1) (Closed.VInr v2)

| CompRef : forall l v,
  comp (CPS.VRef l) v

| CompBase : forall b,
  comp (CPS.VBase b) (Closed.VBase b).

Inductive compR : CPS.result -> Closed.result -> Prop :=
| CompAns : forall v1 v2,
  comp v1 v2
  -> compR (CPS.Ans v1) (Closed.Ans v2)
| CompEx : forall v1 v2,
  comp v1 v2
  -> compR (CPS.Ex v1) (Closed.Ex v2).

Hint Constructors comp compR.

Lemma comp_in : forall s1 s2 v1 v2,
  s1 & s2 |-- v1 ~~ v2
  -> comp v1 v2.
  induction 1; eauto.
Qed.

Hint Resolve comp_in.

Lemma compR_in : forall s1 s2 r1 r2,
  s1 & s2 |--- r1 ~~ r2
  -> compR r1 r2.
  destruct 1; eauto.
Qed.

Hint Resolve compR_in.

Theorem ccExp'_correct : forall s1 h1 e1 r1,
  CPS.eval s1 h1 e1 r1
  -> forall G e2 wf s2 s2' h2 eE,
    CPS.exp_equiv G e1 e2
    -> (forall v1 n, In (v1, n) G -> varOk eE s1 s2' v1 n)
    -> (forall v1 n, In (v1, n) G -> n < length G)
    -> sE (ccExp' (length G) e2 s2 wf) ~> s2'
    -> s1 & s2' |-- h1 ~~~ h2
    -> exists r2,
      Closed.eval s2' h2 (payloadE' (ccExp' (length G) e2 s2 wf) eE) r2
      /\ compR r1 r2.
  Hint Constructors evalPr eval.

  Hint Resolve supplyEnv_correct varOk_alt push_bound pushA_bound.
  Hint Resolve unmerge1_varOk unmerge2_varOk.
  Hint Resolve ccPrimop'_monotone ccExp'_monotone.
  Hint Immediate ccExp'_monotone_trans.

  Hint Extern 1 (_ < _) =>
    match goal with
      | [ H : _ /\ _ |- _ ] => generalize H; tauto
    end.

  Hint Extern 1 (eval _ _ _ _) => env_rewriter; repeat env_rewriter.

  Hint Extern 1 (varOk _ _ _ ?x1 ?x2) =>
    match goal with
      | [ H : In (x1, x2) ?G, H' : forall x1 x2, In (x1, x2) ?G -> varOk _ _ _ _ _ |- _ ] =>
        generalize (H' _ _ H); intro Hmm; clear H';
          eapply varOk_extend
    end.

  Hint Extern 1 (varOk ?E _ _ _ _) =>
    match E with
      | _ +! _ +! _ => (eapply pushA_varOk; [ econstructor; eassumption | eassumption | | | ]) || fail 1
      | _ => eapply push_varOk; [ eassumption | | | ]
    end.

  induction 1; abstract (inversion 1; simplr;
    try match goal with
          | [ H : CPS.evalP _ _ _ _ _ _, eE : eenv _ _, _ : _ & ?s2' |-- _ ~~~ ?h0,
              H' : CPS.primop_equiv _ _ _ |- context[ccPrimop' _ _ ?s0 ?wf] ] =>
            guessKeep (ccPrimop'_correct H wf s0 (unmerge1 eE) (h2 := h0) (s2' := s2') H'); simpler
        end;
    try match goal with
          | [ _ : forall F1 F2 x1 x2, CPS.exp_equiv ((F1, F2) :: (x1, x2) :: ?G0) (?f1 F1 x1) (?f0 F2 x2),
              _ : ?s1 & ?s2 |-- ?v1 ~~ ?v2, eE : eenv _ _,
              _ : ?s1 # ?l1 = Some _, _ : ?s2 # ?l2 = Some _,
              wf0 : wfE (S _) _,
              H : forall (G : list _) e2 wf s2 s2' h2 eE, CPS.exp_equiv G (?f1 _ _) _ -> _ |- _ ] =>
            guessOne ((CPS.VCont l1, S (length G0)) :: (v1, length G0) :: G0) H; simpl length in H;
              guessWith (f0 (S (length G0)) (length G0), wf0,
                Closed.VPair (envTuple eE) (Closed.VCont l2) +! v2 +! eE) H 
          | [ _ : forall x1 x2, CPS.exp_equiv ((x1, x2) :: ?G0) (?f1 x1) (?f0 x2),
              _ : _ & _ |-- ?v1 ~~ ?v2, eE : eenv _ _,
              H : forall (G : list _) e2 wf s2 s2' h2 eE, CPS.exp_equiv G (?f1 _) _ -> _ |- _ ] =>
            let doGuess wf0 eE :=
              guessOne ((v1, length G0) :: G0) H; simpl length in H;
                guessWith (f0 (length G0), wf0, v2 +! eE) H in
            match goal with
              | [ wf0 : wfE (S _) _ |- _ ] => doGuess wf0 eE
              | [ wf0 : _ /\ wfE (S _) _ |- _ ] => doGuess (proj2 wf0) (unmerge2 eE)
              | [ wf0 : _ /\ wfE (S _) _ /\ wfE (S _) _ |- _ ] =>
                (doGuess (proj1 (proj2 wf0)) (unmerge1 (unmerge2 eE));
                  match type of H with
                    | ex _ => idtac
                    | _ => fail 1
                  end)
                || doGuess (proj2 (proj2 wf0)) (unmerge2 (unmerge2 eE))
            end
        end;
    simpler; eauto 7 with closed_eval).
Qed.


(** * Connecting the two kinds of translation *)

Theorem ccExp'_lift : forall e s G wf k r,
  Closed.evalPr (sE (ccExp' G e s wf)) (k (payloadE' (ccExp' G e s wf))) r
  -> Closed.evalPr s (ccExp G e wf k) r.
  Hint Constructors evalPr.

  apply (exp_mut
    (fun e => forall s G wf k r,
      Closed.evalPr (sE (ccExp' G e s wf)) (k (payloadE' (ccExp' G e s wf))) r
      -> Closed.evalPr s (ccExp G e wf k) r)
    (fun p => forall s G wf k r,
      Closed.evalPr (sP (ccPrimop' G p s wf)) (k (payloadP' (ccPrimop' G p s wf))) r
      -> Closed.evalPr s (ccPrimop G p wf k) r)); simpler.
Qed.


(** * The final semantic preservation theorem *)

Lemma ccProg_correct : forall e1 e2 wf r1,
  CPS.exp_equiv nil e1 e2
  -> CPS.eval nil nil e1 r1
  -> exists r2,
    Closed.evalPr nil (ccProg val e2 wf) r2
    /\ compR r1 r2.
  Hint Resolve ccExp'_lift.

  Hint Extern 1 (varOk _ _ _ _ _) => tauto.
  Hint Extern 1 (_ < _) => tauto.
  Hint Extern 0 (_ ~> _) => apply extends_refl.

  unfold ccProg; intros;
    match goal with
      | [ H : CPS.eval _ _ _ _ |- _ ] => generalize (ccExp'_correct H (G := nil)); clear H; simpl; intro H;
        guessWith (e2, wf) H
    end; simpler; eauto.
Qed.

Theorem CcProg_correct : forall E (wf : CPS.Exp_wf E) r1,
  CPS.Eval nil nil E r1
  -> exists r2, Closed.EvalPr nil (CcProg wf) r2
    /\ compR r1 r2.
  Hint Resolve ccProg_correct.

  unfold CPS.Eval, Closed.EvalPr, CcProg; eauto.
Qed.
