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

Require Import Arith Max Coq.FSets.OrderedType.

Require Import LambdaTamer.LambdaTamer.

Require Import NatMap.

Require Import Flat.

Require Import RegAlloc.

Set Implicit Arguments.


Hint Resolve NS.singleton_2 NS.union_2 NS.union_3 NS.remove_2 NS.remove_3 NS.elements_1 NS.add_3
  NS.choose_1.
Hint Resolve NPS.add_1 NPS.add_2 NPS.add_3 NPS.union_2 NPS.union_3.
Hint Resolve NM.elements_1.

Lemma allocVar_correct : forall sls1 sls2 x v ra,
  (forall sl, NS.In sl (liveV x)
    -> forall v, sls1 # sl = Some (Some v)
      -> sls2 # (allocSlot ra sl) = Some (Some v))
  -> get sls1 x = Some v
  -> get sls2 (allocVar ra x) = Some v.
  destruct x; simpler;
    match goal with
      | [ H : forall sl, NS.In sl (NS.singleton ?n) -> _ |- _ ] =>
        generalize (H _ (NS.singleton_2 (refl_equal _)));
          destruct (sls1 # n); simpler
    end;
    match goal with
      | [ H : forall v0, Some (Some _) = Some (Some _) -> _ |- _ ] =>
        rewrite (H _ (refl_equal _)); trivial
    end.
Qed.

Hint Resolve allocVar_correct.

Hint Constructors evalP eval.

Lemma allocPrimop_correct : forall sls1 sls2 h1 p h2 v ra,
  evalP sls1 h1 p h2 v
  -> (forall sl, NS.In sl (liveP p)
    -> forall v, sls1 # sl = Some (Some v)
      -> sls2 # (allocSlot ra sl) = Some (Some v))
  -> evalP sls2 h1 (allocPrimop ra p) h2 v.
  destruct 1; simpler; eauto 9.
Qed.

Hint Resolve allocPrimop_correct.

Hint Resolve NM.find_1 NM.find_2 NM.add_1 NM.add_2 NM.add_3.

Lemma In_all'' : forall sl p ls acc,
  NPS.In p acc
  -> NPS.In p (fold_left (fun a0 e => NPS.add (sl, e) a0) ls acc).
  induction ls; simpler; eauto.
Qed.

Lemma In_all' : forall sl sl' ls acc,
  SetoidList.InA NS.E.eq sl' ls
  -> NPS.In (sl, sl') (fold_left (fun a e => NPS.add (sl, e) a) ls acc).
  Hint Resolve In_all''.

  induction ls; simpler;
    match goal with
      | [ H : SetoidList.InA _ _ _ |- _ ] => inversion H; clear H
    end; unfold NS.E.eq, OrderedTypeEx.Nat_as_OT.eq in *; simpler.
Qed.

Theorem In_all : forall sl sl' s,
  NS.In sl' s
  -> NPS.In (sl, sl') (all sl s).
  Hint Resolve In_all'.

  unfold all; intros; rewrite NS.fold_1; auto.
Qed.

Hint Resolve In_all.

Lemma bound_write : forall A sls a (v' : A) v,
  v < length sls
  -> v < length (sls ## a <~ v').
  simpler.
Qed.

Hint Resolve bound_write.

Lemma evalP_pure : forall sls h1 p h2 v,
  evalP sls h1 p h2 v
  -> pure p = true
  -> h1 = h2.
  destruct 1; simpler.
Qed.

Lemma same_contra : forall sl s A sls a (v : A),
  NS.In sl s
  -> NS.mem sl s = false
  -> sls # a = Some v.
  intros until v; intro H; generalize (NS.mem_1 H); congruence.
Qed.

Hint Immediate same_contra.

Lemma sel_upd_ne' : forall A sls sl (v : A) sl0 v0,
  (sls ## sl <~ v) # sl0 = Some v0
  -> sl <> sl0
  -> sls # sl0 = Some v0.
  intros; rewrite Scratchpad.sel_upd_ne in *; auto.
Qed.

Hint Immediate sel_upd_ne'.

Theorem map_allocFunc : forall fn fc fs,
  fs # fn = Some fc
  -> (map allocFunc fs) # fn = Some (allocFunc fc).
  Hint Rewrite map_length : ltamer.

  induction fs; simpler_expensive.
Qed.

Hint Resolve map_allocFunc.

Hint Resolve NatMap.sel_upd_ne.
Hint Extern 1 (_ <> _) => omega.
Hint Extern 1 (_ < _) => omega.

Hint Extern 1 (allocSlot _ _ = allocSlot _ _) => unfold allocSlot.

Lemma chooseRegs_untouched : forall ns int sl ns' ra,
  ns' < ns
  -> sl < ns - ns'
  -> allocSlot (chooseRegs ns int ra ns') sl = allocSlot ra sl.
  induction ns'; simpler;
    match goal with
      | [ IH : _ |- _ ] => rewrite IH; auto
    end.
Qed.

Hint Rewrite chooseRegs_untouched using omega : ltamer.

Lemma filler_None : forall a v n,
  (filler n) # a = Some (Some v)
  -> False.
  induction n; simpler_expensive.
Qed.

Hint Immediate filler_None.

Theorem grab_2nd_last : forall A x y (s : list A),
  (s ++ x :: y :: nil) # 1 = Some x.
  Hint Rewrite app_length plus_1 : ltamer.
    
  induction s; equation_expensive.
Qed.

Theorem grab_not_2nd_last : forall A x y (s : list A) l,
  (s ++ x :: y :: nil) # (S (S l)) = s # l.
  Hint Rewrite app_length plus_1 : ltamer.
    
  induction s; equation_expensive;
    replace (length s + 2) with (S (S (length s))); simpler_expensive.
Qed.

Hint Rewrite grab_2nd_last grab_not_2nd_last : ltamer.

Lemma same_call' : forall ns1 ns2 F xv sl v ns3 int,
  (filler ns1 ++ Some F :: Some xv :: nil) # sl = Some (Some v)
  -> (filler ns2 ++ Some F :: Some xv :: nil)
  # (allocSlot (chooseRegs ns3 int (NM.add 1 1 (NM.add 0 0 (NM.empty nat))) (pred (pred ns3))) sl)
  = Some (Some v).
  destruct sl; simpler; [ | destruct sl; simpler ]; repeat (destruct ns3; simpler; try solve [ contradictory; eauto ]).
Qed.

Lemma same_call : forall ns1 ns2 F xv sl v ns3 int,
  (filler ns1 ++ Some F :: Some xv :: nil) # sl = Some (Some v)
  -> (filler ns2 ++ Some F :: Some xv :: nil)
  # (allocSlot (chooseRegs (S (S ns3)) int (upd (upd (NM.empty nat) 0 0) 1 1) ns3) sl)
  = Some (Some v).
  simpler; unfold upd;
    match goal with
      | [ |- context[chooseRegs ?a ?b ?c ?d] ] => change (chooseRegs a b c d)
      with (chooseRegs a b c (pred (pred (S (S d)))))
    end; eapply same_call'; eauto.
Qed.

Hint Resolve same_call.

Lemma NPS_In_sym' : forall p m,
  NPS.In p m
  -> NPS.In (snd p, fst p) m.
  unfold NPS.In, NPS.E.eq, NPK.eq;
    induction 1; simpler; unfold NPS.elt, NPS.E.t in *;
      repeat match goal with
               | [ x : NPK.t |- _ ] => destruct x
             end; unfold NPK.canon in *; simpler;
      repeat (match goal with
                | [ _ : context[if ?E then _ else _ ] |- _ ] => destruct E
                | [ |- context[if ?E then _ else _ ] ] => destruct E
                | _ => constructor
              end; simpler).
Qed.

Lemma NPS_In_sym : forall n1 n2 m,
  NPS.In (n1, n2) m
  -> NPS.In (n2, n1) m.
  intros ? ? ? H; generalize (NPS_In_sym' H); simpler.
Qed.

Hint Immediate NPS_In_sym.

Section int.
  Variable int : NPS.t.
  Hypothesis int_not_crazy : forall sl, ~NPS.In (sl, sl) int.

  Lemma In_fill : forall r base n,
    NS.In r (fill base n)
    -> r >= base.
    induction n; simpler; eauto;
      match goal with
        | [ H : NS.In _ NS.empty |- _ ] => destruct (NS.empty_1 H)
        | [ H : NS.In ?r (NS.add ?n _) |- _ ] => destruct (eq_nat_dec r n); simpler; eauto
      end.
  Qed.

  Hint Resolve In_fill.

  Lemma coIn_remove1_contra : forall bound pool,
    NS.For_all (gt bound) pool
    -> NS.In bound pool
    -> False.
    intros ? ? H1 H2; generalize (H1 _ H2); omega.
  Qed.

  Lemma coIn_remove1_contra' : forall bound pool r,
    NS.For_all (gt bound) pool
    -> bound <= r
    -> NS.In r pool
    -> False.
    intros ? ? ? H1 H2 H3; generalize (H1 _ H3); omega.
  Qed.

  Hint Immediate coIn_remove1_contra coIn_remove1_contra'.

  Lemma coIn_remove1 : forall r acc,
    coIn r (remove r acc) -> False.
    unfold coIn, remove; destruct acc; simpler_expensive;
      repeat match goal with
               | [ H : NS.In _ (NS.union _ _) |- _ ] => destruct (NS.union_1 H); clear H
               | [ H : NS.In ?x (NS.remove ?x _) |- _ ] => destruct (NS.remove_1 (refl_equal _) H); clear H
               | [ H : NS.In _ (fill _ _) |- _ ] => generalize (In_upper H); omega
             end; simpler; eauto.
  Qed.

  Lemma coIn_remove2 : forall r b acc,
    coIn r (remove b acc) -> coIn r acc.
    unfold coIn, remove; simpler_expensive;
    try match goal with
          | [ H : NS.In _ (NS.union _ _) |- _ ] => destruct (NS.union_1 H)
        end; simpler; eauto.
  Qed.

  Hint Resolve coIn_remove1 coIn_remove2.

  Lemma chooseReg_correct''' : forall sl r ls acc,
    coIn r (fold_left (fun a p => if NPS.mem (sl, fst p) int then remove (snd p) a else a) ls acc)
    -> coIn r acc.
    induction ls; simpler; eauto;
      match goal with
        | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; eauto
      end.
  Qed.

  Hint Resolve chooseReg_correct'''.
  
  Lemma chooseReg_correct'' : forall sl sl' r ls acc,
    NPS.In (sl, sl') int
    -> In (sl', r) ls
    -> coIn r (fold_left (fun a p => if NPS.mem (sl, fst p) int then remove (snd p) a else a) ls acc)
    -> False.
    induction ls; simpler; eauto;
      match goal with
        | [ H : _ |- _ ] => rewrite (NPS.mem_1 H) in *; eauto
      end.
  Qed.

  Lemma from_InA : forall sl r ls,
    SetoidList.InA (NM.eq_key_elt (elt:=nat)) (sl, r) ls
    -> In (sl, r) ls.
    induction 1; unfold NM.eq_key_elt, NM.Raw.PX.eqke in *; simpler.
  Qed.

  Hint Resolve from_InA.

  Lemma chooseReg_correct' : forall sl sl' r ra acc,
    NPS.In (sl, sl') int
    -> NM.find sl' ra = Some r
    -> coIn r (NM.fold (fun sl' r acc => if NPS.mem (sl, sl') int then remove r acc else acc) ra acc)
    -> False.
    Hint Resolve chooseReg_correct''.
    
    intros; rewrite NM.fold_1 in *; eauto.
  Qed.

  Lemma choose_coIn : forall cf,
    coIn (choose cf) cf.
    unfold coIn, choose; destruct cf; simpler;
      match goal with
        | [ |- context[NS.choose ?p] ] => case_eq (NS.choose p); simpler
      end.
  Qed.

  Hint Resolve choose_coIn.
    
  Lemma chooseReg_correct : forall sl sl' r ra,
    NPS.In (sl, sl') int
    -> NM.find sl' ra = Some r
    -> chooseReg int ra sl = r
    -> False.
    Hint Resolve chooseReg_correct'.

    unfold chooseReg; simpler; eauto.
  Qed.

  Hint Resolve chooseReg_correct.

  Variable max : nat.

  Lemma crazy_neq : forall sl sl',
    NPS.In (sl, sl') int
    -> sl <> sl'.
    simpler; eauto.
  Qed.

  Lemma chooseRegs_sound : forall sl sl',
    NPS.In (sl, sl') int
    -> forall n ra,
      match NM.find sl ra, NM.find sl' ra with
        | Some r1, Some r2 => r1 <> r2
        | _, _ => True
      end
      -> match NM.find sl (chooseRegs max int ra n),
           NM.find sl' (chooseRegs max int ra n) with
           | Some r1, Some r2 => r1 <> r2
           | _, _ => True
         end.
    induction n; simpler; app;
      match goal with
        | [ H : _ |- _ ] => generalize (crazy_neq H)
      end;
    repeat match goal with
             | [ |- context[NM.find ?sl (upd _ ?sl' _)] ] =>
               match sl with
                 | sl' => fail 1
                 | _ => match goal with
                          | [ _ : sl = sl' -> False |- _ ] => fail 1
                          | _ => destruct (eq_nat_dec sl sl'); simpler
                        end
               end
           end;
    match goal with
      | [ |- context[match ?E with Some _ => _ | None => _ end] ] =>
        case_eq E; intuition;
          match goal with
            | [ H1 : _, H2 : _ |- _ ] => rewrite H1 in H2
          end
    end; [ eauto
      | subst; eapply chooseReg_correct; try apply NPS_In_sym; eauto ].
  Qed.

  Lemma chooseRegs_untouched' : forall ns int sl ns' ra,
    ns' < ns
    -> sl < ns - ns'
    -> NM.find sl (chooseRegs ns int ra ns') = NM.find sl ra.
    induction ns'; simpler;
      match goal with
        | [ IH : _ |- _ ] => rewrite IH; auto
      end;
      apply find_upd_ne; auto.
  Qed.

  Hint Rewrite chooseRegs_untouched' using omega : ltamer.

  Lemma chooseRegs_complete : forall sl n ra,
    n <= max
    -> max - n <= sl < max
    -> match NM.find sl (chooseRegs max int ra n) with
         | Some _ => True
         | None => False
       end.
    induction n; simpler; try comega;
      destruct (eq_nat_dec sl (max - S n)); simpler; app; omega.
  Qed.
End int.

Definition NPK_eq_dec : forall (p1 p2 : NPK.t), {NPK.eq p1 p2} + {~NPK.eq p1 p2}.
  intros; refine (match NPK.compare p1 p2 with
                    | EQ _ => left _ _
                    | _ => right _ _
                  end); auto; unfold NPK.lt, NPK.eq in *; intro H; rewrite H in *; omega.
Qed.

Lemma lift_eq : forall sl sl' a,
  sl' <> a
  -> ~NPK.eq (sl, a) (sl, sl').
  unfold NPK.eq, NPK.canon; simpler;
    repeat match goal with
             | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
           end; simpler.
Qed.

Hint Resolve lift_eq.

Lemma neq_sym : forall p1 p2,
  ~ NPK.eq p1 p2
  -> ~ NPS.E.eq p2 p1.
  Hint Immediate NPK.eq_sym.

  unfold NPS.E.eq; red; auto.
Qed.

Hint Immediate neq_sym.

Lemma In_all_rev' : forall sl sl1 sl2 ls acc,
  NPS.In (sl1, sl2) (fold_left (fun a e => NPS.add (sl, e) a) ls acc)
  -> (exists sl2',
    SetoidList.InA NS.E.eq sl2' ls /\ NPK.eq (sl1, sl2) (sl, sl2')) \/ NPS.In (sl1, sl2) acc.
  induction ls; simpler;
    repeat (match goal with
              | [ IH : _, H : _ |- _ ] => destruct (IH _ H); clear IH H; simpler
              | [ _ : NPS.In ?p1 (NPS.add ?p2 _) |- _ ] => destruct (NPK_eq_dec p1 p2)
            end; eauto 6).
Qed.

Theorem In_all_rev : forall sl sl1 sl2 s,
  NPS.In (sl1, sl2) (all sl s)
  -> (NS.In sl1 s /\ sl2 = sl) \/ (sl1 = sl /\ NS.In sl2 s).
  unfold all; intros ? ? ? ? H; rewrite NS.fold_1 in H; apply In_all_rev' in H; simpler;
    repeat match goal with
             | [ H : NPS.In _ NPS.empty |- _ ] => destruct (NPS.empty_1 H)
             | [ H : InA _ _ (NS.elements _) |- _ ] => generalize (NS.elements_2 H); clear H;
               unfold NPK.eq, NPK.canon in *; simpl in *
             | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; simpler
           end.
Qed.

Implicit Arguments In_all_rev [sl sl1 sl2 s].

Lemma remove_contra : forall n s,
  NS.In n (NS.remove n s)
  -> False.
  intros ? ? H; apply (NS.remove_1 (refl_equal _) H).
Qed.

Hint Immediate remove_contra.

Lemma interf_not_crazy : forall sl e,
  NPS.In (sl, sl) (interf (allocExp e))
  -> False.
  induction e; simpler;
    repeat match goal with
             | [ H : NPS.In _ NPS.empty |- _ ] => destruct (NPS.empty_1 H)
             | [ H : NPS.In _ (NPS.union _ _) |- _ ] => destruct (NPS.union_1 H); clear H
             | [ H : _ |- _ ] => destruct (In_all_rev H); simpler; eauto
           end; tauto.
Qed.

Hint Immediate interf_not_crazy.

Lemma interf_not_crazy' : forall sl1 sl2 int,
  (forall sl, NPS.In (sl, sl) int -> False)
  -> NPS.In (sl1, sl2) int
  -> sl1 <> sl2.
  intros; destruct (eq_nat_dec sl1 sl2); simpler; eauto.
Qed.

Hint Immediate interf_not_crazy'.

Hint Extern 1 (_ <= _ < _) => omega.

Lemma length_filler : forall n,
  length (filler n) = n.
  induction n; simpler.
Qed.

Hint Rewrite app_length length_filler : ltamer.

Lemma allocSlot_bound'' : forall r ls acc,
  r <= acc
  -> r <= fold_left (fun (a : nat) (p : NM.key * nat) => max (snd p) a) ls acc.
  induction ls; simpler; eauto with arith.
Qed.

Lemma max_lift : forall b x y,
  x <= y
  -> max b x <= max b y.
  induction b; simpler;
    repeat match goal with
             | [ |- context[match ?E with S _ => _ | O => _ end] ] => destruct E; simpler
           end.
Qed.

Hint Resolve max_lift.

Lemma allocSlot_bound''' : forall ls acc acc',
  acc <= acc'
  -> fold_left (fun (a : nat) (p : NM.key * nat) => max (snd p) a) ls acc
  <= fold_left (fun (a : nat) (p : NM.key * nat) => max (snd p) a) ls acc'.
  induction ls; simpler.
Qed.

Lemma allocSlot_bound' : forall sl r ls,
  SetoidList.InA (NM.eq_key_elt (elt := _)) (sl, r) ls
  -> forall acc, r <= fold_left (fun (a : nat) (p : NM.key * nat) => max (snd p) a) ls acc.
  induction 1; simpler;
    match goal with
      | [ H : NM.eq_key_elt _ _ |- _ ] => do 2 red in H; simpler
    end;
    match goal with
      | [ l : list _, n : nat |- _ ] =>
        solve [ apply le_trans with (fold_left (fun (a : nat) (p : NM.key * nat) => max (snd p) a) l n); [
          eapply allocSlot_bound''; auto
          | eapply allocSlot_bound'''; auto with arith ] ]
    end.
Qed.

Lemma allocSlot_bound : forall sl ra,
  allocSlot ra sl < S (NM.fold (fun _ : NM.key => max) ra 0).
  unfold allocSlot, sel; intros; rewrite NM.fold_1;
    case_eq (NM.find sl ra); simpler;
    match goal with
      | [ H : NM.find _ _ = Some _ |- _ ] => generalize (allocSlot_bound' (NM.find_2 H)); eauto with arith
    end.
Qed.

Hint Resolve allocSlot_bound.

Lemma grab_filler : forall n v1 v2 l v,
  (filler n ++ Some v1 :: Some v2 :: nil) # l = Some (Some v)
  -> (l = 0 /\ v = v2) \/ (l = 1 /\ v = v1).
  do 2 (destruct l; simpler); contradictory; eauto.
Qed.

Implicit Arguments grab_filler [n v1 v2 l v].

Lemma same_call_real : forall ns F xv sl nf int v,
  (filler (pred (pred ns)) ++ Some F :: Some xv :: nil) # sl = Some (Some v)
  -> (filler nf ++ Some F :: Some xv :: nil) # (allocSlot
    (chooseRegs ns int (upd (upd (NM.empty nat) 0 0) 1 1) (pred (pred ns)))
    sl) = Some (Some v).
  intros until v; intro H; destruct (grab_filler H); simpler; do 2 (destruct ns; simpler_expensive).
Qed.

Hint Resolve same_call_real.

Hint Rewrite chooseRegs_untouched' using omega : ltamer.

Lemma chooseRegs_untouched0 : forall int r ns,
  allocSlot (chooseRegs ns int r (pred (pred ns))) 0 = sel 0 r 0.
  destruct ns; simpler.
Qed.

Lemma chooseRegs_untouched1 : forall int r ns,
  allocSlot (chooseRegs ns int r (pred (pred ns))) 1 = sel 0 r 1.
  do 2 (destruct ns; simpler).
Qed.

Hint Rewrite chooseRegs_untouched0 chooseRegs_untouched1 : ltamer.

Theorem nm_sel_empty : forall (A : Set) n,
  NM.find n (NM.empty A) = None.
  eauto.
Qed.

Theorem nm_sel_upd_eq : forall (A : Set) h (v : A) a,
  NM.find a (NM.add a v h) = Some v.
  simpler;
  replace (NM.find a (NM.add a v h)) with (Some v); trivial;
          symmetry; apply NM.find_1; apply NM.add_1; auto.
Qed.

Hint Rewrite nm_sel_empty nm_sel_upd_eq NatMap.sel_upd_ne' using omega : ltamer.

Lemma find_two : forall sl n,
  NM.find sl (upd (upd (NM.empty nat) 0 0) 1 1) = Some n
  -> (sl = 0 /\ n = 0) \/ (sl = 1 /\ n = 1).
  unfold upd; do 2 (destruct sl; simpler).
Qed.

Implicit Arguments find_two [sl n].

Lemma completeo : forall sl ns int,
  sl < S (S ns)
  -> NM.find sl (chooseRegs (S (S ns)) int (upd (upd (NM.empty nat) 0 0) 1 1) ns) <> None.
  do 2 (destruct sl; simpler);
    generalize (@chooseRegs_complete int (S (S ns)) (S (S sl)) ns (upd (upd (NM.empty nat) 0 0) 1 1));
      intro Hsl; do 2 (forward Hsl; [ solve [ auto ] | ]);
        match goal with
          | [ H : _ |- _ ] => rewrite H in Hsl; tauto
        end.
Qed.

Lemma slots_disjoint_call : forall ns int sl sl',
  (forall sl1, NPS.In (sl1, sl1) int -> False)
  -> NPS.In (sl, sl') int
  -> sl < S (S (pred (pred ns)))
  -> sl' < S (S (pred (pred ns)))
  -> allocSlot (chooseRegs ns int (upd (upd (NM.empty nat) 0 0) 1 1) (pred (pred ns))) sl
  = allocSlot (chooseRegs ns int (upd (upd (NM.empty nat) 0 0) 1 1) (pred (pred ns))) sl'
  -> False.
  do 2 (destruct ns; simpler; [
    repeat (match goal with
              | [ H : _ = _ |- _ ] => compute in H; discriminate
              | [ n : nat |- _ ] => destruct n
            end; simpler; eauto)
    | ]);
  match goal with
    | [ H : _, H0 : _, _ : context[chooseRegs ?max _ ?ra ?ns] |- _ ] =>
      let Hs := fresh "Hs" in
        generalize (chooseRegs_sound H max H0 ns ra); intro Hs; forward Hs; [
          repeat (match goal with
                    | [ |- context[NM.find (S ?N) _] ] => destruct N
                    | [ |- context[NM.find ?N _] ] => destruct N
                  end; simpler; eauto)
          | ]
  end;
  repeat match goal with
           | [ int : NPS.t, H : _ < _ |- _ ] => generalize (completeo int H); clear H
         end; unfold allocSlot, sel in *;
  repeat match goal with
           | [ _ : context[match ?E with Some _ => _ | None => _ end] |- _ ] => destruct E
         end; eauto.
Qed.

Hint Resolve slots_disjoint_call.

Hint Rewrite plus_1 : ltamer.

Lemma alloc_fold : forall ra sl,
  allocSlot ra sl < pred (NM.fold (fun _ : NM.key => max) ra 0) + 2.
  intros; generalize (allocSlot_bound sl ra); omega.
Qed.

Hint Resolve alloc_fold.

Lemma filler_bound : forall ns int F xv sl,
  sl < S (S (pred (pred ns)))
  -> allocSlot (chooseRegs ns int (upd (upd (NM.empty nat) 0 0) 1 1) (pred (pred ns))) sl
  < length (filler
    (pred (NM.fold (fun _ : NM.key => max)
      (chooseRegs ns int (upd (upd (NM.empty nat) 0 0) 1 1) (pred (pred ns))) 0)) ++ Some F :: Some xv :: nil).
  unfold allocSlot; destruct ns; simpler; destruct sl; simpler.
Qed.

Hint Resolve filler_bound.

Lemma extra_disjoint : forall ra s1 s2 live2 sl sl2 (sls : list (option val)) v0,
  (forall sl1' sl2',
    NPS.In (sl1', sl2')
    (NPS.union s1 (NPS.union (all sl2 (NS.remove sl2 live2)) s2))
    -> sl1' < length sls
    -> sl2' < length sls
    -> allocSlot ra sl1' = allocSlot ra sl2'
    -> False)
  -> sls # sl = Some (Some v0)
  -> sl2 < length sls
  -> NS.In sl live2
  -> (sl2 = sl -> False)
  -> allocSlot ra sl2 <> allocSlot ra sl.
  intros; red; app; eauto; apply NPS_In_sym; auto.
Qed.

Hint Immediate extra_disjoint.

Lemma plus_2 : forall n,
  n + 2 = S (S n).
  simpler.
Qed.

Hint Rewrite plus_2 : ltamer.

Theorem allocExp_correct : forall fs h sls1 e r,
  eval fs h sls1 e r
  -> forall sls2 ra,
    (forall sl, NS.In sl (live (allocExp e))
      -> forall v, sls1 # sl = Some (Some v)
        -> sls2 # (allocSlot ra sl) = Some (Some v))
    -> (forall sl sl', NPS.In (sl, sl') (interf (allocExp e))
      -> sl < length sls1
      -> sl' < length sls1
      -> allocSlot ra sl <> allocSlot ra sl')
    -> (forall sl, sl < length sls1
      -> allocSlot ra sl < length sls2)
    -> eval (map allocFunc fs) h sls2 (build (allocExp e) ra) r.
  Hint Extern 1 (allocSlot _ _ <> allocSlot _ _) => red; app.

  induction 1; abstract (simpler;
    try match goal with
          | [ |- context[if ?b1 && negb ?b2 then _ else _ ] ] =>
            let Heq := fresh "Heq" in let Heq' := fresh "Heq'" in
              case_eq b1; intro Heq; rewrite Heq in *; simpler; [
                case_eq b2; intro Heq'; rewrite Heq' in *; simpler
                | ]
        end;
    repeat (match goal with
              | [ IHeval : forall (sls2 : list _) (ra : NM.t _), _ |- _ ] =>
                simpl; eapply IHeval; intros;
                  try match goal with
                        | [ |- context[(_ ## allocSlot ?ra ?sl <~ _) # (allocSlot ?ra ?sl')] ] =>
                          destruct (eq_nat_dec sl sl'); simpler;
                            [ rewrite Scratchpad.sel_upd_eq | rewrite Scratchpad.sel_upd_ne ]
                        | [ _ : context[(_ ## ?sl <~ _) # ?sl'] |- _ ] =>
                          destruct (eq_nat_dec sl sl'); subst
                      end
              | [ _ : _ = Some (VInr _) |- _ ] => eapply EvalCaseR
              | _ => econstructor
              | [ H1 : evalP _ _ _ _ _, H2 : pure _ = true |- _ ] => rewrite (evalP_pure H1 H2)
            end; (eapply slots_disjoint_call; try eassumption; [ eauto ]) || eauto 6)).
Qed.

Lemma filler_contra : forall A (x y : A) n sl v,
  (filler n) # sl = Some (Some v)
  -> x = y.
  intros until v; intro H; case_eq ((filler n) # sl); simpler; destruct (filler_None _ _ H).
Qed.

Hint Immediate filler_contra.

Lemma final_disjoint : forall ns int sl sl',
  (forall sl1, NPS.In (sl1, sl1) int -> False)
  -> NPS.In (sl, sl') int
  -> sl < length (filler ns)
  -> sl' < length (filler ns)
  -> allocSlot (chooseRegs ns int (NM.empty nat) ns) sl
  <> allocSlot (chooseRegs ns int (NM.empty nat) ns) sl'.
  simpler;
  repeat match goal with
           | [ _ : context[allocSlot (chooseRegs ?max ?int ?ra ?n) ?sl] |- _ ] =>
             match goal with
               | [ _ : match NM.find sl _ with Some _ => True | None => False end |- _ ] => fail 1
               | _ =>
                 let Hsl := fresh "Hsl" in
                   generalize (@chooseRegs_complete int max sl n ra); intro Hsl;
                     do 2 (forward Hsl; [ solve [ auto ] | ])
             end
         end;
  match goal with
    [ H : allocSlot _ ?sl1 = allocSlot _ ?sl2 |- _ ] =>
    unfold allocSlot, sel in H; simpler;
      match goal with
        | [ H : NPS.In _ ?int, H' : _, _ : context[chooseRegs ?max ?int ?ra ?n] |- _ ] =>
          generalize (@chooseRegs_sound int H' max _ _ H n ra)
      end; simpler;
      repeat match goal with
               | [ _ : match ?E with Some _ => True | None => False end |- _ ] => destruct E; simpler
             end
  end.
Qed.

Hint Resolve final_disjoint.

Lemma final_length : forall ra sl,
  allocSlot ra sl < length (filler (raMax ra)).
  unfold raMax; simpler.
Qed.

Hint Resolve final_length.

Theorem allocProg_correct : forall pr r,
  evalPr pr r
  -> evalPr (allocProg pr) r.
  Hint Resolve allocExp_correct.

  unfold allocProg, evalPr; simpl p_funcs; simpl p_nslots; simpl p_body; eauto.
Qed.
