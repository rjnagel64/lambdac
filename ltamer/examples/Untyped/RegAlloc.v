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

Require Import Arith Max.

Require Import LambdaTamer.LambdaTamer.

Require Import NatMap.

Require Import Flat.

Set Implicit Arguments.


Require Import Coq.FSets.FSetList Coq.FSets.OrderedTypeEx.

Module NS := Coq.FSets.FSetList.Make(Coq.FSets.OrderedTypeEx.Nat_as_OT).

Module NPK.
  Definition t := (nat * nat)%type.

  Definition canon (x : t) : t :=
    if le_lt_dec (fst x) (snd x)
      then x
      else (snd x, fst x).

  Definition eq (x y : t) : Prop := canon x = canon y.

  Definition lt (x y : t) : Prop := fst (canon x) < fst (canon y)
    \/ (fst (canon x) = fst (canon y) /\ snd (canon x) < snd (canon y)).

  Theorem eq_refl : forall x : t, eq x x.
    unfold eq; trivial.
  Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
    unfold eq; intuition.
  Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    unfold eq; intuition; eapply trans_eq; eauto.
  Qed.

  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    unfold lt; intuition.
  Qed.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    unfold eq, lt; intuition;
      match goal with
        | [ H : canon _ = canon _ |- _ ] => rewrite H in *; omega
      end.
  Qed.

  Definition compare (x y : t) : Compare lt eq x y.
    intros; refine (let x' := canon x in
      let y' := canon y in
        if eq_nat_dec (fst x') (fst y')
          then if eq_nat_dec (snd x') (snd y')
            then EQ _ _
            else if le_lt_dec (snd x') (snd y')
              then LT _ _
              else GT _ _
          else if le_lt_dec (fst x') (fst y')
            then LT _ _
            else GT _ _);
    unfold eq, lt, t, canon in *;
      repeat match goal with
               | [ x : _ |- _ ] => unfold x in *; clear x
               | [ x : (_ * _)%type |- _ ] => destruct x; simpler
               | [ |- context[if ?E then _ else _] ] => destruct E; simpler
             end.
  Defined.
End NPK.

Module NPK' := MOT_to_OT(NPK).
Module NPS := Coq.FSets.FSetList.Make(NPK').


Fixpoint liveV (v : var) : NS.t :=
  match v with
    | Slot n => NS.singleton n
    | FuncVar _ => NS.empty
  end.

Definition liveP (p : primop) : NS.t :=
  match p with
    | Unit => NS.empty
    | Pair x y => NS.union (liveV x) (liveV y)
    | EFst x => liveV x
    | ESnd x => liveV x
    | EInl x => liveV x
    | EInr x => liveV x
    | New x => liveV x
    | Read x => liveV x
    | Write x y => NS.union (liveV x) (liveV y)
    | Const _ => NS.empty
    | Eq x y => NS.union (liveV x) (liveV y)
  end.

Record result : Type := Res {
  live : NS.t;
  interf : NPS.t;
  build : NM.t nat -> exp
}.

Definition allocSlot (ra : NM.t nat) (sl : nat) : nat := sel 0 ra sl.

Definition allocVar (ra : NM.t nat) (v : var) : var :=
  match v with
    | Slot n => Slot (allocSlot ra n)
    | FuncVar n => FuncVar n
  end.

Definition allocPrimop (ra : NM.t nat) (p : primop) : primop :=
  match p with
    | Unit => Unit
    | Pair x y => Pair (allocVar ra x) (allocVar ra y)
    | EFst x => EFst (allocVar ra x)
    | ESnd x => ESnd (allocVar ra x)
    | EInl x => EInl (allocVar ra x)
    | EInr x => EInr (allocVar ra x)
    | New x => New (allocVar ra x)
    | Read x => Read (allocVar ra x)
    | Write x y => Write (allocVar ra x) (allocVar ra y)
    | Const b => Const b
    | Eq x y => Eq (allocVar ra x) (allocVar ra y)
  end.

Definition pure (p : primop) : bool :=
  match p with
    | New _ => false
    | Write _ _ => false
    | _ => true
  end.

Definition all (sl : nat) (s : NS.t) : NPS.t :=
  NS.fold (fun sl' int => NPS.add (sl, sl') int) s NPS.empty.

Fixpoint allocExp (e : exp) : result :=
  match e with
    | EHalt x => Res (liveV x) NPS.empty (fun ra => EHalt (allocVar ra x))
    | EUncaught x => Res (liveV x) NPS.empty (fun ra => EUncaught (allocVar ra x))

    | Call f x => Res (NS.union (liveV f) (liveV x)) NPS.empty
      (fun ra => Call (allocVar ra f) (allocVar ra x))

    | Assign sl p e' =>
      let er := allocExp e' in
      let erase := pure p && negb (NS.mem sl (live er)) in
        Res (NS.union (if erase then NS.empty else liveP p) (NS.remove sl (live er)))
        (NPS.union (all sl (NS.remove sl (live er))) (interf er))
        (if erase
          then build er
          else (fun ra => Assign (allocSlot ra sl) (allocPrimop ra p) (build er ra)))

    | ECase x sl1 e1 sl2 e2 =>
      let er1 := allocExp e1 in
      let er2 := allocExp e2 in
        Res (NS.union (liveV x) (NS.union (NS.remove sl1 (live er1)) (NS.remove sl2 (live er2))))
        (NPS.union (all sl1 (NS.remove sl1 (live er1)))
          (NPS.union (all sl2 (NS.remove sl2 (live er2)))
            (NPS.union (interf er1) (interf er2))))
        (fun ra => ECase (allocVar ra x) (allocSlot ra sl1) (build er1 ra) (allocSlot ra sl2) (build er2 ra))
  end.

Record cofinite : Type := Cofinite {
  pool : NS.t;
  bound : nat;
  no_overlap : NS.For_all (gt bound) pool
}.
Implicit Arguments Cofinite [].
Definition coIn (n : nat) (cf : cofinite) := NS.In n (pool cf) \/ n >= bound cf.

Definition full : cofinite.
  refine (Cofinite NS.empty O _);
    red; intros; match goal with
                   | [ H : NS.In _ NS.empty |- _ ] => destruct (NS.empty_1 H)
                 end.
Defined.

Fixpoint fill (base n : nat) {struct n} : NS.t :=
  match n with
    | O => NS.empty
    | S n' => NS.add (base + n') (fill base n')
  end.

Hint Resolve NS.add_3.

Theorem In_upper : forall x bound n,
  NS.In x (fill bound n)
  -> x < bound + n.
  induction n; simpler;
    match goal with
      | [ H : NS.In _ NS.empty |- _ ] => destruct (NS.empty_1 H)
      | [ H : NS.In ?x (NS.add ?n _) |- _ ] => destruct (eq_nat_dec n x); simpler; eauto
    end; match goal with
           | [ IHn : _, n0 : _, H : _ |- _ ] => solve [ generalize (IHn (NS.add_3 n0 H)); omega ]
         end.
Qed.

Implicit Arguments In_upper [x bound n].

Hint Resolve NS.remove_3.

Definition remove (n : nat) (cf : cofinite) : cofinite.
  intros; refine (if eq_nat_dec n (bound cf)
    then Cofinite (pool cf) (S (bound cf)) _
    else if le_lt_dec (bound cf) n
      then Cofinite (NS.union (pool cf) (fill (bound cf) (n - bound cf))) (S n) _
      else Cofinite (NS.remove n (pool cf)) (bound cf) _); abstract (destruct cf; unfold NS.For_all in *; simpler; eauto;
        repeat match goal with
                 | [ H : _, H' : _ |- _ ] => generalize (H _ H'); omega
                 | [ H : NS.In _ (NS.union _ _) |- _ ] => destruct (NS.union_1 H); clear H
                 | [ H : NS.In _ (fill _ _) |- _ ] => generalize (In_upper H); omega
               end).
Defined.

Definition choose (cf : cofinite) : nat :=
  match NS.choose (pool cf) with
    | None => bound cf
    | Some n => n
  end.

Definition chooseReg (int : NPS.t) (ra : NM.t nat) (sl : nat) : nat :=
  choose (NM.fold (fun sl' r acc => if NPS.mem (sl, sl') int then remove r acc else acc) ra full).

Fixpoint chooseRegs (max : nat) (int : NPS.t) (ra : NM.t nat) (n : nat) {struct n} : NM.t nat :=
  match n with
    | O => ra
    | S n' =>
      let sl := max - n in
        chooseRegs max int (upd ra sl (chooseReg int ra sl)) n'
  end.

Definition raMax (ra : NM.t nat) : nat :=
  S (NM.fold (fun _ => max) ra O).

Definition allocFunc (f : func) : func :=
  let er := allocExp (f_body f) in
  let ra := upd (upd (NM.empty _) 0 0) 1 1 in
  let ra := chooseRegs (f_nslots f) (interf er) ra (pred (pred (f_nslots f))) in
    Func (raMax ra) (build er ra).

Definition allocProg (pr : prog) : prog :=
  let fs := map allocFunc (p_funcs pr) in
  let er := allocExp (p_body pr) in
  let ra := chooseRegs (p_nslots pr) (interf er) (NM.empty _) (p_nslots pr) in
    Prog fs (raMax ra) (build er ra).
