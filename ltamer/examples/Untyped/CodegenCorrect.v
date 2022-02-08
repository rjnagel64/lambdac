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

Require Import Arith List Max.

Require Import LambdaTamer.LambdaTamer.

Require Import Base.

Require Import NatMap.

Require Import Flat.
Require Import Asm.

Require Import Codegen.

Set Implicit Arguments.


(** * Correctness relations between source and target programs *)

Section n_regs.
  Variable n_regs : nat.

  Section fs.
    Variable fs : list Flat.func.
    Variable scratch : nat.

    Section cr.
      Variable top : nat.
      Variable refs : list nat.

      Definition immutable (a : nat) := scratch <= a < top /\ lall (fun a' => a' >= scratch /\ a' <> a) refs.

      Lemma immutable_top : forall a,
        immutable a -> scratch <= a < top.
        unfold immutable; tauto.
      Qed.

      Variable h2 : heap.

      Inductive cr : Flat.val -> nat -> Prop :=
      | EquivProc : forall l,
        cr (Flat.VProc l) (genLabel fs l)

      | EquivUnit : forall n,
        cr Flat.VUnit n

      | EquivPair : forall x y a,
        cr x (sel h2 a)
        -> cr y (sel h2 (S a))
        -> immutable a
        -> immutable (S a)
        -> cr (Flat.VPair x y) a

      | EquivInl : forall v a,
        sel h2 a = 0
        -> cr v (sel h2 (S a))
        -> immutable a
        -> immutable (S a)
        -> cr (Flat.VInl v) a
      | EquivInr : forall v a,
        sel h2 a = 1
        -> cr v (sel h2 (S a))
        -> immutable a
        -> immutable (S a)
        -> cr (Flat.VInr v) a

      | EquivRef : forall l a,
        refs # l = Some a
        -> cr (Flat.VRef l) a

      | EquivBase : forall b,
        cr (Flat.VBase b) (encode b).
    End cr.

    Hint Constructors cr.
    Hint Resolve immutable_top.

    Lemma immutable_monotone : forall top top' refs refs' a,
      immutable top refs a
      -> top >= scratch
      -> top' >= top
      -> lall (fun a' => a' >= top) refs'
      -> immutable top' (refs' ++ refs) a.
      unfold immutable; simpler;
        apply lall_app; simpler;
          eapply lall_weaken; [ eassumption | simpler ].
    Qed.

    Hint Resolve immutable_monotone.

    Theorem cr_monotone' : forall top refs h2 top' refs' h2',
      top >= scratch
      -> top' >= top
      -> lall (fun a' => a' >= top) refs'
      -> (forall a, scratch <= a < top -> sel h2' a = sel h2 a
        \/ exists rf, refs # rf = Some a)
      -> forall v1 v2, cr top refs h2 v1 v2
        -> cr top' (refs' ++ refs) h2' v1 v2.
      induction 5; simpler;
        try match goal with
          | [ H : forall a, _ <= a < _ -> _ |- _ ] =>
            constructor; eauto;
              match goal with
                | [ Himm : immutable _ _ ?a |- context[sel _ ?a] ] =>
                  let H' := fresh "H'" in let H'' := fresh "H''" in
                    destruct (H a) as [? | [? H']]; eauto; [
                      equation
                      | destruct Himm as [? H'']; generalize (lall_grab H'' H'); tauto
                    ]
              end
        end.
    Qed.

    Theorem cr_monotone : forall top refs h2 v1 v2,
      cr top refs h2 v1 v2
      -> forall top' refs' h2', top >= scratch
        -> top' >= top
        -> lall (fun a' => a' >= top) refs'
        -> (forall a, scratch <= a < top -> sel h2' a = sel h2 a)
        -> cr top' (refs' ++ refs) h2' v1 v2.
      intros; eapply cr_monotone'; intros;
        match goal with
          | [ H1 : _, H2 : _ |- _ \/ _ ] => generalize (H1 _ H2); eauto
          | _ => eauto
        end.
    Qed.

    Theorem cr_monotone0 : forall top refs h2 v1 v2,
      cr top refs h2 v1 v2
      -> forall top' h2', top >= scratch
        -> top' >= top
        -> (forall a, scratch <= a < top -> sel h2' a = sel h2 a)
        -> cr top' refs h2' v1 v2.
      intros; change refs with (nil ++ refs); eapply cr_monotone; eauto.
    Qed.

    Hint Extern 6 (cr _ ?refs _ _ _) =>
      match goal with
        | [ H : cr _ refs _ _ _ |- _ ] => eapply (cr_monotone0 H)
      end.

    Theorem cr_monotone0' : forall top refs h2 v1 v2,
      cr top refs h2 v1 v2
      -> forall top' h2', top >= scratch
        -> top' >= top
        -> (forall a, scratch <= a < top -> sel h2' a = sel h2 a
          \/ exists rf, refs # rf = Some a)
        -> cr top' refs h2' v1 v2.
      intros; change refs with (nil ++ refs); eapply cr_monotone'; eauto.
    Qed.

    Implicit Arguments cr_monotone0' [top refs h2 v1 v2].

    Hint Extern 6 (cr _ ?refs _ _ _) =>
      match goal with
        | [ H : cr _ refs _ _ _ |- _ ] => eapply (cr_monotone0' H)
      end.

    Theorem cr_monotone1 : forall top refs h2 v1 v2,
      cr top refs h2 v1 v2
      -> forall top' h2', top >= scratch
        -> top' >= top
        -> (forall a, scratch <= a < top -> sel h2' a = sel h2 a)
        -> cr top' (top :: refs) h2' v1 v2.
      intros; change (top :: refs) with ((top :: nil) ++ refs); eapply cr_monotone; eauto.
    Qed.

    Hint Extern 6 (cr _ (_ :: _) _ _ _) =>
      match goal with
        | [ H : cr _ _ _ _ _ |- _ ] => eapply (cr_monotone1 H)
      end.

    Definition slotOk (rs : regs n_regs) h2 refs sls sl :=
      match sls # sl with
        | Some (Some v1) => cr (iget rs FO) refs h2 v1 (get rs h2 (genSlotR sl))
        | _ => True
      end.

    Definition refOk h1 (rs : regs n_regs) h2 refs rf :=
      match h1 # rf with
        | Some v1 =>
          match refs # rf with
            | Some a => scratch <= a < iget rs FO /\ cr (iget rs FO) refs h2 v1 (sel h2 a)
            | _ => False
          end
        | None => refs # rf = None
      end.

    Theorem sel_upd_eq : forall h a v a',
      a' = a
      -> sel (upd h a v) a' = v.
      unfold sel, upd; simpler.
    Qed.

    Theorem sel_upd_ne : forall h a a' v,
      a' <> a
      -> sel (upd h a v) a' = sel h a'.
      unfold sel, upd; simpler.
    Qed.

    Ltac solver := solve [ auto| omega ].

    Hint Rewrite sel_upd_eq sel_upd_ne using solver : ltamer.

    Hint Extern 1 (_ = _) => omega.
    Hint Extern 1 (_ <> _) => omega.
    Hint Extern 1 (_ < _) => omega.
    Hint Extern 1 (_ <= _) => omega.
    Hint Extern 1 (_ > _) => omega.
    Hint Extern 1 (_ >= _) => omega.

    Theorem get_heap_irrel : forall (rs : regs n_regs) h2 a v sl,
      a > sl
      -> get rs (upd h2 a v) (genSlotR sl) = get rs h2 (genSlotR sl).
      unfold get, genSlotR; intros; destruct (genSlot' n_regs sl); simpler.
    Qed.

    Hint Rewrite get_heap_irrel using solver : ltamer.

    Theorem iget_iupd_eq : forall A v n f (il : ilist A n),
      iget (iupd f v il) f = v.
      induction f; simpler.
    Qed.

    Theorem iget_iupd_ne : forall A v n f f' (il : ilist A n),
      f' <> f
      -> iget (iupd f v il) f' = iget il f'.
      induction f; intros; dep_destruct f'; dep_destruct il; simpler; app; simpler.
    Qed.

    Hint Rewrite iget_iupd_eq iget_iupd_ne using solver : ltamer.

    Theorem slotOk_monotone : forall rs h2 refs sls sl,
      slotOk rs h2 refs sls sl
      -> forall rs' h2' refs', iget rs FO >= scratch
        -> iget rs' FO >= iget rs FO
        -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a)
        -> lall (fun a' => a' >= iget rs FO) refs'
        -> (sl >= length sls \/ get rs' h2' (genSlotR sl) = get rs h2 (genSlotR sl))
        -> slotOk rs' h2' (refs' ++ refs) sls sl.
      unfold slotOk; intuition; [
        case_eq (sls # sl); equation
        | repeat match goal with
                   | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E
                 end; equation; eauto; eapply cr_monotone; eauto ].
    Qed.

    Theorem slotOk_monotone0 : forall rs h2 refs sls sl,
      slotOk rs h2 refs sls sl
      -> forall rs' h2', iget rs FO >= scratch
        -> iget rs' FO >= iget rs FO
        -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a)
        -> (sl >= length sls \/ get rs' h2' (genSlotR sl) = get rs h2 (genSlotR sl))
        -> slotOk rs' h2' refs sls sl.
      intros; change refs with (nil ++ refs); eapply slotOk_monotone; eauto.
    Qed.

    Implicit Arguments slotOk_monotone0 [rs h2 refs sls sl].

    Hint Extern 20 (slotOk _ _ ?refs _ ?sl) =>
      match goal with
        | [ H : forall sl, slotOk _ _ refs _ sl |- _ ] => eapply (slotOk_monotone0 (H sl))
      end.

    Theorem slotOk_monotone' : forall rs h2 refs sls sl,
      slotOk rs h2 refs sls sl
      -> forall rs' h2' refs', iget rs FO >= scratch
        -> iget rs' FO >= iget rs FO
        -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a
          \/ exists rf, refs # rf = Some a)
        -> lall (fun a' => a' >= iget rs FO) refs'
        -> (sl >= length sls \/ get rs' h2' (genSlotR sl) = get rs h2 (genSlotR sl))
        -> slotOk rs' h2' (refs' ++ refs) sls sl.
      unfold slotOk; intuition; [
        case_eq (sls # sl); equation
        | repeat match goal with
                   | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E
                 end; equation; eauto; eapply cr_monotone'; eauto ].
    Qed.

    Theorem slotOk_monotone0' : forall rs h2 refs sls sl,
      slotOk rs h2 refs sls sl
      -> forall rs' h2', iget rs FO >= scratch
        -> iget rs' FO >= iget rs FO
        -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a
          \/ exists rf, refs # rf = Some a)
        -> (sl >= length sls \/ get rs' h2' (genSlotR sl) = get rs h2 (genSlotR sl))
        -> slotOk rs' h2' refs sls sl.
      intros; change refs with (nil ++ refs); eapply slotOk_monotone'; eauto.
    Qed.

    Implicit Arguments slotOk_monotone0' [rs h2 refs sls sl].

    Hint Extern 20 (slotOk _ _ ?refs _ ?sl) =>
      match goal with
        | [ H : forall sl, slotOk _ _ refs _ sl |- _ ] => eapply (slotOk_monotone0' (H sl))
      end.

    Theorem slotOk_monotone1 : forall rs h2 refs sls sl,
      slotOk rs h2 refs sls sl
      -> forall rs' n h2', iget rs FO >= scratch
        -> iget rs' FO >= iget rs FO
        -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a)
        -> n >= iget rs FO
        -> (sl >= length sls \/ get rs' h2' (genSlotR sl) = get rs h2 (genSlotR sl))
        -> slotOk rs' h2' (n :: refs) sls sl.
      intros; change (n :: refs) with ((n :: nil) ++ refs); eapply slotOk_monotone; eauto.
    Qed.

    Implicit Arguments slotOk_monotone1 [rs h2 refs sls sl].

    Hint Extern 19 (slotOk _ _ (_ :: ?refs) _ ?sl) =>
      match goal with
        | [ H : forall sl, slotOk _ _ refs _ sl |- _ ] => eapply (slotOk_monotone1 (H sl))
      end.

    Theorem refOk_monotone0 : forall h1 rs h2 refs rf,
      refOk h1 rs h2 refs rf
      -> forall rs' h2', iget rs FO >= scratch
        -> iget rs' FO >= iget rs FO
        -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a)
        -> lall (fun a' => scratch <= a' < iget rs FO) refs
        -> refOk h1 rs' h2' refs rf.
      unfold refOk; intros;
        repeat match goal with
                 | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; simpler
                 | [ H : forall a, _ |- _ ] => rewrite H; eauto
               end.
    Qed.

    Implicit Arguments refOk_monotone0 [h1 rs h2 refs rf].

    Hint Extern 20 (refOk _ _ _ ?refs ?rf) =>
      match goal with
        | [ H : forall rf, refOk _ _ _ refs rf |- _ ] =>
          match rf with
            | rf => eapply (refOk_monotone0 (H rf))
          end
      end.

    Theorem refOk_monotone1 : forall h1 rs h2 refs rf,
      refOk h1 rs h2 refs rf
      -> forall rs' v1 v2 h2', iget rs FO >= scratch
        -> iget rs' FO > iget rs FO
        -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a)
        -> lall (fun a' => scratch <= a' < iget rs FO) refs
        -> cr (iget rs FO) refs h2 v1 v2
        -> sel h2' (iget rs FO) = v2
        -> length h1 = length refs
        -> refOk (v1 :: h1) rs' h2' (iget rs FO :: refs) rf.
      unfold refOk; equation_expensive;
        repeat match goal with
                 | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; simpler
               end;
        match goal with
          | [ H : _ |- _ ] => rewrite H; eauto
        end.
    Qed.

    Hint Resolve refOk_monotone1.

    Theorem iget_ihead : forall rs : regs n_regs,
      ihead rs = iget rs FO.
      unfold regs; intros; dep_destruct rs; auto.
    Qed.

    Hint Rewrite iget_ihead : ltamer.

    Lemma genSlot'_inj : forall n_regs sl1 sl2 f1 f2,
      genSlot' n_regs sl1 = Some f1
      -> genSlot' n_regs sl2 = Some f2
      -> sl1 <> sl2
      -> f1 <> f2.
      induction n_regs0; destruct sl1; destruct sl2; simpler;
        try match goal with
              | [ _ : S ?sl1 = S ?sl2 -> False, IH : forall (sl1 sl2 : nat), _ |- _ ] =>
                generalize (IH sl1 sl2)
            end;
        repeat match goal with
                 | [ H : match ?E with Some _ => _ | None => _ end = _ |- _ ] => destruct E; simpler
               end; eauto;
        match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H
        end.
    Qed.

    Hint Resolve genSlot'_inj.

    Lemma iget_itail_itail : forall A n (il : ilist A (S (S n))) (f : fin n),
      iget (itail (itail il)) f = iget il (FS (FS f)).
      intros; dep_destruct il; match goal with
                                 | [ v : ilist _ _ |- _ ] => dep_destruct v; trivial
                               end.
    Qed.

    Hint Resolve iget_itail_itail.

    Definition setR (rs : regs n_regs) (h : heap) (lv : lval n_regs) (v : nat) : regs n_regs :=
      match lv with
        | LReg r => iupd r v rs
        | LMemReg r n => rs
        | LMemImm n => rs
      end.

    Definition setH (rs : regs n_regs) (h : heap) (lv : lval n_regs) (v : nat) : heap :=
      match lv with
        | LReg r => h
        | LMemReg r n => upd h (iget rs r + n) v
        | LMemImm n => upd h n v
      end.

    Theorem set_decomp : forall rs h lv v,
      set rs h lv v = (setR rs h lv v, setH rs h lv v).
      destruct lv; auto.
    Qed.

    Hint Rewrite set_decomp : ltamer.

    Lemma genSlot'_None : forall n_regs sl,
      genSlot' n_regs sl = None
      -> sl >= n_regs.
      induction n_regs0; simpler_expensive; destruct sl; simpler;
        generalize (IHn_regs0 sl);
          match goal with
            | [ H : context[match ?E with Some _ => _ | None => _ end] |- _ ] => destruct E
          end; simpler.
    Qed.

    Ltac get_set :=
      unfold genSlotL, genSlotR;
        intros; repeat match goal with
                         | [ |- context[match ?E with Some _ => _ | None => _ end] ] => case_eq E
                       end; simpler;
        unfold regs in *; simpl in *;
          repeat match goal with
                   | [ il : ilist _ (S _) |- _ ] => dep_destruct il
                 end;
          simpler; eauto;
            try (rewrite sel_upd_ne; auto;
              repeat match goal with
                       | [ H : genSlot' _ _ = None |- _ ] => generalize (genSlot'_None _ H); clear H
                     end; omega).

    Lemma iget_setR_hptr : forall rs h sl v,
      iget (setR rs h (genSlotL sl) v) (hptr n_regs) = iget rs (hptr n_regs).
      get_set.
    Qed.

    Lemma iget_setH_high : forall rs h sl v a,
      a >= scratch
      -> sl < scratch
      -> sel (setH rs h (genSlotL sl) v) a = sel h a.
      get_set.
    Qed.

    Hint Rewrite iget_setR_hptr iget_setH_high using solver : ltamer.

    Lemma get_set : forall rs h sl v,
      sl < scratch
      -> get (setR rs h (genSlotL sl) v) (setH rs h (genSlotL sl) v) (genSlotR sl) = v.
      get_set.
    Qed.

    Lemma get_set_1 : forall r1 rs h sl v,
      sl < scratch
      -> get (r1 ::: itail (setR rs h (genSlotL sl) v)) (setH rs h (genSlotL sl) v) (genSlotR sl) = v.
      get_set.
    Qed.

    Hint Resolve iget_iupd_ne.

    Lemma get_set_ne : forall rs h sl sl' v,
      sl < scratch
      -> sl' <> sl
      -> get (setR rs h (genSlotL sl) v) (setH rs h (genSlotL sl) v) (genSlotR sl') = get rs h (genSlotR sl').
      get_set.
    Qed.

    Lemma get_set_ne_1 : forall r1 rs h sl sl' v,
      sl < scratch
      -> sl' <> sl
      -> get (r1 ::: itail (setR rs h (genSlotL sl) v)) (setH rs h (genSlotL sl) v) (genSlotR sl')
      = get rs h (genSlotR sl').
      get_set.
    Qed.

    Hint Rewrite get_set get_set_1 get_set_ne get_set_ne_1 using solver : ltamer.

    Lemma prove_immutable : forall rs refs n a,
      iget rs FO >= scratch
      -> a >= iget rs FO
      -> lall (fun a => scratch <= a < iget rs FO) refs
      -> a < iget rs (hptr n_regs) + S n
      -> immutable (iget rs (hptr n_regs) + S n) refs a.
      red; unfold hptr; simpler;
        eapply lall_weaken; [ eassumption | simpler ].
    Qed.

    Hint Resolve prove_immutable.

    Lemma cr_input : forall x v1 rs h refs sls,
      iget rs FO >= scratch
      -> Flat.get sls x = Some v1
      -> (forall sl, slotOk rs h refs sls sl)
      -> cr (iget rs FO) refs h v1 (get rs h (genVar n_regs fs x)).
      intros;
        let n := fresh "n" in
          destruct x as [n | ?]; [ simpl in * | simpler ];
            match goal with
              | [ H : forall sl, slotOk _ _ _ ?sls sl |- _ ] =>
                generalize (H n); clear H; intro H; red in H;
                  destruct (sls # n); subst; autorewrite with ltamer; simpl in *;
                    try discriminate; eauto
            end.
    Qed.

    Lemma get_slot_high2 : forall r1 r2 (rs : regs n_regs) h sl,
      get (r1 ::: r2 ::: itail (itail rs)) h (genSlotR sl) = get rs h (genSlotR sl).
      get_set.
    Qed.

    Lemma get_slot_high3 : forall r1 r2 r3 (rs : regs n_regs) h sl,
      get (r1 ::: r2 ::: r3 ::: itail (itail (itail rs))) h (genSlotR sl) = get rs h (genSlotR sl).
      get_set.
    Qed.

    Hint Rewrite get_slot_high2 get_slot_high3 : ltamer.

    Theorem read_result : forall rs h dst (src : rval n_regs) n,
      dst < scratch
      -> exists rs', exists h',
        evalIs rs h (read (genSlotL dst) src n) = (rs', h', None)
        /\ get rs' h' (genSlotR dst) = sel h (n + get rs h src)
        /\ iget rs' FO >= iget rs FO
        /\ (forall a, scratch <= a < iget rs FO -> sel h' a = sel h a)
        /\ (forall sl', sl' <> dst -> get rs' h' (genSlotR sl') = get rs h (genSlotR sl')).
      destruct src; simpler; splitter; eauto; simpler.
    Qed.

    Lemma write_result : forall (rs : regs n_regs) h dst src n,
      get rs h dst >= scratch
      -> iget rs FO >= scratch
      -> exists rs', exists h',
        evalIs rs h (write dst n (genVar n_regs fs src)) = (rs', h', None)
        /\ sel h' (n + get rs h dst) = get rs h (genVar n_regs fs src)
        /\ iget rs' FO >= iget rs FO
        /\ (forall a, scratch <= a < iget rs FO -> a <> n + get rs h dst -> sel h' a = sel h a)
        /\ (forall sl, sl < scratch -> get rs' h' (genSlotR sl) = get rs h (genSlotR sl)).
      destruct dst; simpler; splitter; eauto; simpler; destruct src; simpler.
    Qed.

    Ltac read_cr := equation; match goal with
                                | [ H : forall a : nat, _ |- _ ] => rewrite <- H; eauto
                              end.

    Theorem read_cr0 : forall h' sl h (rs rs' : regs n_regs) x v refs,
      get rs' h' (genSlotR sl) = sel h (get rs h (genVar n_regs fs x))
      -> (forall a, scratch <= a < iget rs FO -> sel h' a = sel h a)
      -> cr (iget rs FO) refs h v (sel h (get rs h (genVar n_regs fs x)))
      -> iget rs FO >= scratch
      -> iget rs' FO >= iget rs FO
      -> immutable (iget rs FO) refs (get rs h (genVar n_regs fs x))
      -> cr (iget rs' FO) refs h' v (get rs' h' (genSlotR sl)).
      read_cr.
    Qed.

    Theorem read_cr1 : forall h' sl h (rs rs' : regs n_regs) x v refs,
      get rs' h' (genSlotR sl) = sel h (S (get rs h (genVar n_regs fs x)))
      -> (forall a, scratch <= a < iget rs FO -> sel h' a = sel h a)
      -> cr (iget rs FO) refs h v (sel h (S (get rs h (genVar n_regs fs x))))
      -> iget rs FO >= scratch
      -> iget rs' FO >= iget rs FO
      -> immutable (iget rs FO) refs (S (get rs h (genVar n_regs fs x)))
      -> cr (iget rs' FO) refs h' v (get rs' h' (genSlotR sl)).
      read_cr.
    Qed.

    Hint Resolve read_cr0 read_cr1.

    Lemma get_scratch : forall a x0 n x1,
      a >= scratch
      -> match x0 # n with
           | Some o => o
           | None => None (A := val)
         end = Some x1
      -> length x0 <= scratch
      -> a > n.
      intros until x1;
        generalize (grab_oob' n x0); intro Hlem;
          destruct (x0 # n); simpler; generalize (Hlem _ (refl_equal _)); omega.
    Qed.

    Hint Immediate get_scratch.

    Theorem get_heap_irrel_var : forall (rs : regs n_regs) h2 a v x,
      a >= scratch
      -> (exists sls, exists v',
        Flat.get sls x = Some v' /\ length sls <= scratch)
      -> get rs (upd h2 a v) (genVar n_regs fs x) = get rs h2 (genVar n_regs fs x).
      get_set; destruct x; simpler; rewrite get_heap_irrel; eauto.
    Qed.

    Hint Rewrite get_heap_irrel_var using (solver || (do 3 econstructor; eassumption)) : ltamer.

    Theorem lall_new : forall rs n (rs' : ilist _ n) refs,
      lall (fun a => scratch <= a < iget rs FO) refs
      -> lall (fun a => a < iget (iget rs (hptr n_regs) + 1 ::: rs') FO) (iget rs FO :: refs).
      unfold hptr; simpler; eapply lall_weaken; eauto.
    Qed.

    Hint Immediate lall_new.

    Lemma use_refOk : forall h1 rs h2 refs rf v1 v2 v2' top h2',
      refOk h1 rs h2 refs rf
      -> h1 # rf = Some v1
      -> v2 = sel h2 v2'
      -> refs # rf = Some v2'
      -> top >= iget rs FO
      -> (forall a, scratch <= a < iget rs FO -> sel h2' a = sel h2 a)
      -> cr top refs h2' v1 v2.
      unfold refOk; simpler;
        repeat match goal with
                 | [ H1 : _, H2 : _ |- _ ] => rewrite H1 in H2
               end; simpler; eauto.
    Qed.

    Hint Immediate use_refOk.

    Lemma ref_bound : forall refs rf v,
      refs # rf = Some v
      -> forall h rs h2,
        refOk h rs h2 refs rf
        -> v >= scratch.
      unfold refOk; simpler;
        repeat match goal with
                 | [ H1 : _, H2 : _ |- _ ] => rewrite H1 in H2
                 | [ _ : match ?E with Some _ => _ | None => _ end |- _ ] => destruct E
               end; simpler.
    Qed.

    Implicit Arguments ref_bound [refs rf v].

    Hint Extern 10 (?v >= scratch) =>
      match goal with
        | [ H : _ # _ = Some v |- _ ] => eapply (ref_bound H)
      end.

    Definition refsDisjoint (refs : list nat) :=
      forall rf1 rf2 l, refs # rf1 = Some l -> refs # rf2 = Some l -> rf1 = rf2.

    Lemma refOk_write' : forall (rs : regs n_regs) h2' h2 l2 a refs rf,
      (forall a, scratch <= a < iget rs FO -> a <> l2 -> sel h2' a = sel h2 a)
      -> refs # rf = Some l2
      -> scratch <= a < iget rs FO
      -> sel h2' a = sel h2 a \/
      (exists rf0, refs # rf0 = Some a).
      intros; destruct (eq_nat_dec a l2); subst; eauto.
    Qed.

    Hint Resolve refOk_write'.

    Lemma refOk_write : forall h1 rs h2 refs,
      (forall rf, refOk h1 rs h2 refs rf)
      -> forall rs' h2' l1 l2 v1 v2,
        cr (iget rs FO) refs h2 v1 v2
        -> refs # l1 = Some l2
        -> refsDisjoint refs
        -> sel h2' l2 = v2
        -> length h1 = length refs
        -> iget rs FO >= scratch
        -> iget rs' FO >= iget rs FO
        -> scratch <= l2 < iget rs' FO
        -> (forall a, scratch <= a < iget rs FO -> a <> l2 -> sel h2' a = sel h2 a)
        -> (forall rf, refOk (h1 ## l1 <~ v1) rs' h2' refs rf).
      red; simpler;
        match goal with
          | [ Hok : forall rf : Scratchpad.label, _, Hdisj : refsDisjoint ?refs, H2 : ?refs # _ = Some _ |- _ ] =>
            generalize (Hok rf); generalize (Hdisj _ rf _ H2); unfold refOk; intros
        end;
        destruct (le_lt_dec (length h1) rf); [
          repeat (rewrite grab_length_contra'; [ | solve [ simpler ] ]); auto
          | match goal with
              | [ H : _ < length ?h |- context[?h ## ?l1 <~ ?v1] ] =>
                destruct (upd_choices l1 v1 H); equation
            end; repeat match goal with
                          | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; simpler
                        end;
            try match goal with
                  | [ _ : ?n < iget _ _, _ : ?m < iget _ _, H : forall a : nat, _ |- _ ] =>
                    destruct (eq_nat_dec n m); simpler; rewrite H
                end; eauto ].
    Qed.

    Implicit Arguments refOk_write [h1 rs h2 refs].

    Hint Extern 10 (refOk (_ ## _ <~ _) _ _ ?refs _) =>
      match goal with
        | [ H : forall rf, refOk _ _ _ refs rf |- _ ] => eapply (refOk_write H)
      end.

    Theorem refsDisjoint_new : forall h rs h2 refs,
      (forall rf, refOk h rs h2 refs rf)
      -> refsDisjoint refs
      -> refsDisjoint (iget rs FO :: refs).
      red; simpler_expensive; eauto;
        match goal with
          | [ Hok : forall rf : Scratchpad.label, _, H : _ # ?rf = Some _ |- _ ] =>
            generalize (Hok rf); unfold refOk; destruct (h # rf); simpler; rewrite H in *; simpler
        end.
    Qed.

    Hint Resolve refsDisjoint_new.

    Definition used (P : Prop) (H : P) := True.

    Ltac use_hyps :=
      repeat match goal with
               | [ H1 : _ >= scratch, H2 : Flat.get ?sls ?x = Some ?v,
                 H3 : forall sl, slotOk ?rs ?h2 ?refs _ _ |- _ ] =>
                 match goal with
                   | [ _ : used H2 |- _ ] => fail 1
                   | _ => generalize (cr_input x rs h2 refs sls H1 H2 H3); generalize (I : used H2); simpler
                 end
               | [ H : cr _ _ _ _ _ |- _ ] => invert_1 H; subst
             end.

    Lemma write_bound : forall h rs h2 refs (x : regs n_regs) l v,
      (forall rf, refOk h rs h2 refs rf)
      -> refs # l = Some (get rs h2 v)
      -> iget x FO >= iget rs FO
      -> scratch <= get rs h2 v < iget x FO.
      intros until v; intro H; generalize (H l); unfold refOk; destruct (h # l); simpler;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] => rewrite H1 in H2
        end; simpler.
    Qed.

    Hint Immediate write_bound.

    Lemma write_or : forall refs l (rs x : regs n_regs) h2 x0 v,
      refs # l = Some v
      -> iget x FO >= iget rs FO
      -> (forall a, scratch <= a < iget rs FO -> a <> v -> sel x0 a = sel h2 a)
      -> (forall a, scratch <= a < iget rs FO
        -> sel x0 a = sel h2 a \/ (exists rf : Scratchpad.label, refs # rf = Some a)).
      intros; destruct (eq_nat_dec a v); simpler; eauto.
    Qed.

    Hint Immediate write_or.

    Lemma encode_disj : forall b1 b2,
      (b1 = b2 -> False)
      -> encode b1 = encode b2
      -> 1 = 0.
      generalize encode_inj; firstorder.
    Qed.

    Hint Immediate encode_disj.

    Theorem genPrimop_correct : forall sls h1 p h1' v1,
      Flat.evalP sls h1 p h1' v1
      -> forall h2 rs refs sl,
        sl < scratch
        -> (forall sl, slotOk rs h2 refs sls sl)
        -> lall (fun a => scratch <= a < iget rs FO) refs
        -> length h1 = length refs
        -> refsDisjoint refs
        -> (forall rf, refOk h1 rs h2 refs rf)
        -> iget rs FO >= scratch
        -> length sls <= scratch
        -> exists refs', exists rs', exists h2',
          Asm.evalIs rs h2 (genPrimop fs (genSlotL sl) p) = (rs', h2', None)
          /\ iget rs' FO >= iget rs FO
          /\ lall (fun a => scratch <= a < iget rs' FO) refs'
          /\ length h1' = length (refs' ++ refs)
          /\ refsDisjoint (refs' ++ refs)
          /\ (forall rf, refOk h1' rs' h2' (refs' ++ refs) rf)
          /\ cr (iget rs' FO) (refs' ++ refs) h2' v1 (get rs' h2' (genSlotR sl))
          /\ (forall sl', sl' <> sl -> slotOk rs' h2' (refs' ++ refs) sls sl').
      Ltac simplr' := unfold hptr; simpl in *; autorewrite with ltamer.
      Ltac simplr := unfold hptr; simpler.

      Hint Extern 1 (iget _ _ >= _) => simplr'.
      Hint Extern 1 (iget _ _ > _) => simplr'.
      Hint Extern 1 (iget _ _ + _ >= _) => simplr'.
      Hint Extern 1 (iget _ _ + _ > _) => simplr'.
      Hint Extern 1 (sel _ _ = _) => simplr'.

      Hint Extern 1 (?N >= ?M \/ _) => destruct (le_lt_dec M N); [ tauto | right; autorewrite with ltamer ].

      Hint Extern 1 ((if eq_nat_dec ?X ?Y then _ else _) = _) => destruct (eq_nat_dec X Y); try tauto.

      destruct 1; abstract (intros; match goal with
                                      | [ rs : regs _ |- context[New _] ] => exists (iget rs FO :: nil)
                                      | _ => idtac
                                    end;
      simplr; try match goal with
                    | [ rs : regs _, H1 : _ < scratch, h : _ |- context[read _ ?RV ?N] ] =>
                      generalize (read_result rs h RV N H1); simplr
                  end; use_hyps;
      try match goal with
            | [ rs : regs _, H2 : _ >= scratch, h : _ |- context[write ?DST ?N (genVar _ _ ?SRC)] ] =>
              let H1 := fresh "H1" in
                assert (H1 : get rs h DST >= scratch); [ solve [ eauto ]
                  | generalize (write_result rs h DST SRC N H1 H2); simplr ]
          end;
      splitter; try match goal with
                      | [ |- lall _ _ ] => eapply lall_nil
                    end;
      match goal with
        | [ |- forall x, _ ] => idtac
        | [ |- cr _ _ _ _ _ ] => simplr; constructor
        | _ => eauto
      end; simplr; eauto).
    Qed.

    Theorem get_regs_irrel_var : forall r1 r2 r3 rs h2 x,
      get (r1 ::: r2 ::: r3 ::: itail (itail (itail rs))) h2 (genVar n_regs fs x) = get rs h2 (genVar n_regs fs x).
      destruct x; simpler.
    Qed.

    Theorem evalB_cons : forall bls (rs : regs n_regs) h2 i is j r rs' h2' h2'',
      evalI rs h2 i = inl _ (rs', h2')
      -> evalB bls rs' h2' (is, j) h2'' r
      -> evalB bls rs h2 (i :: is, j) h2'' r.
      inversion 2; simpler; econstructor; simpl;
        try match goal with
              | [ H : _ |- _ ] => rewrite H
            end; eauto.
    Qed.

    Theorem evalB_app : forall bls is j r is' (rs : regs n_regs) h2 rs' h2' h2'',
      evalIs rs h2 is' = (rs', h2', None)
      -> evalB bls rs' h2' (is, j) h2'' r
      -> evalB bls rs h2 (is' ++ is, j) h2'' r.
      Hint Resolve evalB_cons.

      induction is'; simpler;
        match goal with
          | [ H : context[match ?E with inl _ => _ | inr _ => _ end] |- _ ] => case_eq E; intros
        end;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] => rewrite H1 in H2
        end; simpler; eauto.
    Qed.

    Hint Rewrite pair_uneta : ltamer.

    Lemma slotOk_call' : forall F v sl v' fillBy,
      (filler fillBy ++ Some F :: Some v :: nil) # sl = Some (Some v')
      -> (sl = 0 /\ v' = v) \/ (sl = 1 /\ v' = F).
      induction fillBy; simpler_expensive.
    Qed.

    Implicit Arguments slotOk_call' [F v sl v' fillBy].

    Lemma slotOk_call : forall rs F2 v2 h2 refs fillBy F1 v1 sl,
      1 < scratch
      -> iget rs FO >= scratch
      -> cr (iget rs FO) refs h2 v1 v2
      -> cr (iget rs FO) refs h2 F1 F2
      -> slotOk (setR
        (setR (iget rs FO ::: v2 ::: F2 ::: itail (itail (itail rs))) h2 (genSlotL O) v2)
        (setH (iget rs FO ::: v2 ::: F2 ::: itail (itail (itail rs))) h2 (genSlotL O) v2)
        (genSlotL 1) F2)
      (setH (setR (iget rs FO ::: v2 ::: F2 ::: itail (itail (itail rs))) h2 (genSlotL O) v2)
        (setH (iget rs FO ::: v2 ::: F2 ::: itail (itail (itail rs))) h2 (genSlotL O) v2)
        (genSlotL 1) F2)
      refs (filler fillBy ++ Some F1 :: Some v1 :: nil) sl.
      red; intros;
        repeat match goal with
                 | [ |- match ?E with Some _ => _ | None => _ end ] => case_eq E; simpler
               end;
        match goal with
          | [ H : _ |- _ ] => generalize (slotOk_call' H); equation
        end.
    Qed.

    Theorem length_filler : forall n,
      length (filler n) = n.
      induction n; simpler.
    Qed.

    Hint Rewrite length_filler app_length : ltamer.

    Variable bls : list (block n_regs).

    Hypothesis Hbls1 : forall l f,
      fs # l = Some f
      -> nth_error bls (genLabel fs l)
      = @Some (block _) (Assgn (genSlotL O) (RReg (FS FO))
        :: Assgn (genSlotL 1) (RReg (FS (FS FO)))
        :: fst (fst (genExp n_regs fs (S (genLabel fs l)) (f_body f))),
        snd (fst (genExp n_regs fs (S (genLabel fs l)) (f_body f)))).

    Hypothesis Hbls2 : forall l f l' bl,
      fs # l = Some f
      -> nth_error (snd (genExp n_regs fs (S (genLabel fs l)) (f_body f))) l' = Some bl
      -> nth_error bls (l' + S (genLabel fs l)) = Some bl.

    Hypothesis Hbls_nslots : forall l f,
      fs # l = Some f
      -> f_nslots f <= scratch.

    Lemma nslots_le : forall fn fc,
      fs # fn = Some fc
      -> 1 < scratch
      -> pred (pred (f_nslots fc)) + 2 <= scratch.
      intros fn fc H; generalize (Hbls_nslots _ H); omega.
    Qed.

    Hint Resolve nslots_le.

    Lemma nth_error_call : forall fn fc r1 r2 r3 rs h2 f,
      fs # fn = Some fc
      -> genLabel fs fn = get rs h2 (genVar n_regs fs f)
      -> nth_error bls (get (r1 ::: r2 ::: r3 ::: itail (itail (itail rs))) h2 (genVar n_regs fs f))
      = @Some (block _) (Assgn (genSlotL O) (RReg (FS FO))
        :: Assgn (genSlotL 1) (RReg (FS (FS FO)))
        :: fst (fst (genExp n_regs fs (S (genLabel fs fn)) (f_body fc))),
        snd (fst (genExp n_regs fs (S (genLabel fs fn)) (f_body fc)))).
      intros; rewrite get_regs_irrel_var;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] => rewrite <- H1; rewrite (Hbls1 _ H2); reflexivity
        end.
    Qed.

    Hint Resolve nth_error_call.

    Lemma Assgn_slotOk : forall rs refs h v sl sls,
      cr (iget rs FO) refs h v (get rs h (genSlotR sl))
      -> (forall sl', sl' <> sl -> slotOk rs h refs sls sl')
      -> (forall sl', slotOk rs h refs (sls ## sl <~ (Some v)) sl').
      red; intros; destruct (le_lt_dec (length sls) sl');
        try solve [ rewrite grab_length_contra'; simpler ];
          match goal with
            | [ H : _ < length ?sls |- context[?sls ## ?sl <~ ?v] ] =>
              destruct (upd_choices sl v H); equation
          end;
          match goal with
            | [ H : forall sl' : nat, _ |- context[_ # ?sl'] ] =>
              generalize (H sl'); unfold slotOk; intuition
          end.
    Qed.

    Hint Resolve Assgn_slotOk.

    Lemma Assgn_lall : forall refs refs' (rs rs' : regs n_regs),
      lall (fun a => scratch <= a < iget rs FO) refs
      -> lall (fun a : nat => scratch <= a < iget rs' FO) refs'
      -> iget rs' FO >= iget rs FO
      -> lall (fun a => scratch <= a < iget rs' FO) (refs' ++ refs).
      intros; apply lall_app; [ eapply lall_weaken; [ eassumption | simpler] | assumption ].
    Qed.

    Hint Immediate Assgn_lall.

    Lemma app_length_eq : forall A B (ls : list A) (ls1 ls2 : list B),
      length ls = length ls1 + length ls2
      -> length ls = length (ls1 ++ ls2).
      simpler.
    Qed.

    Hint Immediate app_length_eq.

    Lemma Case_slotOk : forall rs r2 h2 refs sls v a sl,
      (forall sl, slotOk rs h2 refs sls sl)
      -> cr (iget rs FO) refs h2 v (sel h2 (S a))
      -> iget rs FO >= scratch
      -> sl < scratch
      -> (forall sl', slotOk (setR (iget rs FO ::: r2 ::: itail (itail rs)) h2 (genSlotL sl) (sel h2 (a + 1)))
        (setH (iget rs FO ::: r2 ::: itail (itail rs)) h2 (genSlotL sl) (sel h2 (a + 1))) refs
        (sls ## sl <~ (Some v)) sl').
      red; intros; rewrite plus_1; destruct (le_lt_dec (length sls) sl');
        try solve [ rewrite grab_length_contra'; simpler ];
          match goal with
            | [ H : _ < length ?sls |- context[?sls ## ?sl <~ ?v] ] =>
              destruct (upd_choices sl v H); equation
          end;
          match goal with
            | [ H : forall sl' : Scratchpad.label, _ |- context[_ # ?sl'] ] =>
              generalize (H sl'); unfold slotOk; intros
          end;
          repeat match goal with
                   | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; simpler
                 end.
    Qed.

    Hint Resolve Case_slotOk.

    Lemma f_nslots_bound : forall fn fc,
      fs # fn = Some fc
      -> 0 < scratch
      -> S (pred (f_nslots fc)) <= scratch.
      intros fn fc H; generalize (Hbls_nslots _ H); simpler.
    Qed.

    Hint Resolve f_nslots_bound.

    Lemma nth_error_swap : forall l' n l bl,
      nth_error bls ((l' + S n) + l) = Some bl
      -> nth_error bls (l' + S (n + l)) = Some bl.
      intros; replace (l' + S (n + l)) with ((l' + S n) + l); simpler.
    Qed.
    
    Hint Resolve nth_error_swap.

    Section comp.
      Variable h2 : heap.

      Inductive comp : Flat.val -> nat -> Prop :=
      | CompProc : forall l v,
        comp (Flat.VProc l) v

      | CompUnit : forall n,
        comp Flat.VUnit n

      | CompPair : forall x y a,
        comp x (sel h2 a)
        -> comp y (sel h2 (S a))
        -> comp (Flat.VPair x y) a

      | CompInl : forall v a,
        sel h2 a = 0
        -> comp v (sel h2 (S a))
        -> comp (Flat.VInl v) a
      | CompInr : forall v a,
        sel h2 a = 1
        -> comp v (sel h2 (S a))
        -> comp (Flat.VInr v) a

      | CompRef : forall l v,
        comp (Flat.VRef l) v

      | CompBase : forall b,
        comp (Flat.VBase b) (encode b).

      Inductive compR : Flat.result -> Asm.result -> Prop :=
      | CompAns : forall v1 v2,
        comp v1 v2
        -> compR (Flat.Ans v1) (Asm.Ans v2)
      | CompEx : forall v1 v2,
        comp v1 v2
        -> compR (Flat.Ex v1) (Asm.Ex v2).

      Hint Constructors comp compR.

      Lemma comp_in : forall top refs v1 v2,
        cr top refs h2 v1 v2
        -> comp v1 v2.
        induction 1; eauto.
      Qed.
    End comp.

    Hint Resolve comp_in.

    Theorem iget_3 : forall r1 r2 r3 h rs sl v,
      iget (setR (r1 ::: r2 ::: r3 ::: rs) h (genSlotL sl) v) (FS (FS FO)) = r3.
      get_set.
    Qed.

    Hint Rewrite iget_3 get_regs_irrel_var : ltamer.

    Theorem genExp_correct : forall h1 sls e r1,
      Flat.eval fs h1 sls e r1
      -> forall h2 rs refs l,
        (forall sl, slotOk rs h2 refs sls sl)
        -> lall (fun a => scratch <= a < iget rs FO) refs
        -> length h1 = length refs
        -> refsDisjoint refs
        -> (forall rf, refOk h1 rs h2 refs rf)
        -> iget rs FO >= scratch
        -> length sls <= scratch
        -> 1 < scratch
        -> (forall l' bl, nth_error (snd (genExp n_regs fs l e)) l' = Some bl -> nth_error bls (l' + l) = Some bl)
        -> exists h2', exists r2, Asm.evalB bls rs h2 (fst (genExp n_regs fs l e)) h2' r2
          /\ compR h2' r1 r2.
      Hint Constructors evalB.

      Ltac esimp := progress (simpl; try rewrite set_decomp; try rewrite plus_0_r;
        try match goal with
              | [ H : sel _ _ = _ |- _ ] => rewrite H
            end).

      Hint Extern 1 (evalI _ _ _ = _) => esimp.
      Hint Extern 1 (evalIs _ _ _ = _) => esimp.
      Hint Extern 1 (lall _ _) => progress simplr'.

      Hint Extern 1 (nth_error _ _ = Some _) =>
        match goal with
          | [ _ : _ # ?fn = Some ?fc |- _ ] => apply (@nth_error_call fn fc)
        end.

      Hint Extern 1 (slotOk _ _ _ _ _) =>
        match goal with
          | [ rs : regs n_regs |- _ ] => apply (@slotOk_call rs)
        end.

      Hint Extern 1 (slotOk _ _ _ _ _) =>
        match goal with
          | [ rs : regs n_regs, _ : sel _ ?E = _ |- _ ] =>
            apply (@Case_slotOk rs E)
        end.

      induction 1; abstract (simpler; use_hyps;
        try match goal with
              [ |- context[genPrimop _ (genSlotL ?sl) _] ] => guessWithKeep sl genPrimop_correct; simpler
            end;
        try match goal with
              | [ IHeval : forall h2 : heap, _ |- _ ] => guess IHeval; simpler
            end;
        splitter;
        try match goal with
              | [ _ : evalB _ _ _ _ ?h1 ?r1 |- evalB _ _ _ _ ?h2 ?r2 ] =>
                equate h1 h2; equate r1 r2
            end;
        repeat match goal with
                 | _ => eapply evalB_cons; [ solve [ eauto ] | simpler ]
                 | _ => eapply evalB_app; [ solve [ eauto ] | simpler ]
                 | _ => eapply EvalJnz; [ solve [ eauto] | solve [ eauto ] | simpler]
                 | _ => econstructor; eauto
               end; eauto).
    Qed.
  End fs.

  Lemma Hbls1_final'' : forall (f : nat -> Flat.exp -> block n_regs * list (block n_regs)) i i' fs bls,
    exists bls',
      fold_left (fun bls f0 => let (bl, bls') := f (S (length bls)) (f_body f0) in
        bls ++ (i :: i' :: fst bl, snd bl) :: bls') fs bls
      = bls ++ bls'.
    Hint Resolve app_nil_end.

    intro f; induction fs; simpler; eauto;
      match goal with
        | [ |- context[f ?a ?b] ] => rewrite <- (pair_uneta (f a b))
      end;
      match goal with
        | [ IH : forall bls : list _, _ |- context[fold_left _ _ ?x] ] => guessWith x IH
      end; simpler;
      match goal with
        | [ H : _ |- _ ] => rewrite H
      end; econstructor; simpler.
  Qed.

  Hint Rewrite app_length : ltamer.

  Lemma internalLabels_genExp : forall fs e l,
    length (snd (genExp n_regs fs l e)) = internalLabels e.
    induction e; equation.
  Qed.

  Hint Rewrite internalLabels_genExp : ltamer.

  Hint Rewrite app_ass plus_0_r nth_error_middle plus_1 : ltamer.
  Hint Rewrite <- app_comm_cons minus_n_n : ltamer.

  Hint Extern 1 (_ = _) => omega.

  Lemma Hbls1_final' : forall fsG l f i i' e fs blsOut,
    fs # l = Some f
    -> nth_error (fold_left
      (fun bls f0 => let (bl, bls') := genExp n_regs fsG (S (length bls)) (f_body f0) in
        bls ++ (i :: i' :: fst bl, snd bl) :: bls')
      fs blsOut
      ++ snd (genExp n_regs fsG (length (fold_left
        (fun bls f0 => let (bl, bls') := genExp n_regs fsG (S (length bls)) (f_body f0) in
          bls ++ (i :: i' :: fst bl, snd bl) :: bls') fs blsOut)) e))
    (length blsOut + genLabel fs l)
    = Some (i :: i' :: fst (fst (genExp n_regs fsG (length blsOut + S (genLabel fs l)) (f_body f))),
      snd (fst (genExp n_regs fsG (length blsOut + S (genLabel fs l)) (f_body f)))).
    induction fs; simpler;
      match goal with
        | [ |- context[genExp ?a ?b ?c ?d] ] => rewrite <- (pair_uneta (genExp a b c d)) in *
      end;
      match goal with
        | [ |- context[fold_left _ _ ?acc] ] => generalize (IHfs acc)
      end; simpler_expensive; [
        match goal with
          | [ |- context[fold_left _ _ ?bls] ] => destruct (Hbls1_final'' (genExp n_regs fsG) i i' fs bls) as [bls' Hbls']
        end; rewrite Hbls'; autorewrite with ltamer; eauto
        | match goal with
            | [ H : _ = Some ?X |- _ = Some ?Y ] => replace Y with X
          end; [
            match goal with
              | [ H : _ = ?X |- _ = ?X ] => rewrite <- H; f_equal; omega
            end
            | repeat match goal with
                       | [ |- genExp _ _ ?x _ = genExp _ _ ?y _ ] => replace y with x; auto
                       | _ => f_equal
                     end ] ].
  Qed.

  Lemma Hbls1_final : forall l f i i' e fs,
    fs # l = Some f
    -> nth_error (fold_left
      (fun bls f0 => let (bl, bls') := genExp n_regs fs (S (length bls)) (f_body f0) in
        bls ++ (i :: i' :: fst bl, snd bl) :: bls')
      fs nil
      ++ snd (genExp n_regs fs (length (fold_left
        (fun bls f0 => let (bl, bls') := genExp n_regs fs (S (length bls)) (f_body f0) in
          bls ++ (i :: i' :: fst bl, snd bl) :: bls') fs nil)) e))
    (genLabel fs l)
    = Some (i :: i' :: fst (fst (genExp n_regs fs (S (genLabel fs l)) (f_body f))),
      snd (fst (genExp n_regs fs (S (genLabel fs l)) (f_body f)))).
    intros; generalize (@Hbls1_final' fs l f i i' e fs nil); tauto.
  Qed.

  Hint Resolve Hbls1_final.

  Opaque nth_error.

  Lemma Hbls2_final' : forall fsG i i' e l f l' bl fs blsOut,
   fs # l = Some f
   -> nth_error (snd (genExp n_regs fsG (length blsOut + S (genLabel fs l)) (f_body f))) l' = Some bl
   -> nth_error (fold_left (fun bls f0 =>
     let (bl0, bls') :=
       genExp n_regs fsG (S (length bls)) (f_body f0) in
       bls ++ (i :: i' :: fst bl0, snd bl0) :: bls') fs blsOut
   ++ snd (genExp n_regs fsG (length
     (fold_left (fun bls f0 =>
       let (bl0, bls') :=
         genExp n_regs fsG (S (length bls)) (f_body f0) in
         bls ++ (i :: i' :: fst bl0, snd bl0) :: bls') fs blsOut))
   e)) (length blsOut + l' + S (genLabel fs l))
   = Some bl.
    induction fs; simpler;
      match goal with
        | [ |- context[genExp ?a ?b ?c ?d] ] => rewrite <- (pair_uneta (genExp a b c d)) in *
      end;
      match goal with
        | [ |- context[fold_left _ _ ?acc] ] => generalize (IHfs acc)
      end; simpler_expensive; [
        match goal with
          | [ |- context[fold_left _ _ ?bls] ] => destruct (Hbls1_final'' (genExp n_regs fsG) i i' fs bls) as [bls' Hbls']
        end; rewrite Hbls'; autorewrite with ltamer; eauto
        | match goal with
            | [ H : _ -> _ = ?X |- _ = ?X ] => rewrite <- H; [
              f_equal; omega
              | match goal with
                  | [ _ : context[genExp _ _ ?N _] |- context[genExp _ _ ?M _ ] ] => replace M with N; solve [ auto ]
                end
            ]
          end ].
  Qed.

  Lemma Hbls2_final : forall i i' e l f l' bl fs,
    fs # l = Some f
    -> nth_error (snd (genExp n_regs fs (S (genLabel fs l)) (f_body f))) l' = Some bl
    -> nth_error (fold_left (fun bls f0 =>
      let (bl0, bls') :=
        genExp n_regs fs (S (length bls)) (f_body f0) in
        bls ++ (i :: i' :: fst bl0, snd bl0) :: bls') fs nil
    ++ snd (genExp n_regs fs (length
      (fold_left (fun bls f0 =>
        let (bl0, bls') :=
          genExp n_regs fs (S (length bls)) (f_body f0) in
          bls ++ (i :: i' :: fst bl0, snd bl0) :: bls') fs nil))
    e)) (l' + S (genLabel fs l))
    = Some bl.
    intros; generalize (@Hbls2_final' fs i i' e l f l' bl fs nil); tauto.
  Qed.

  Hint Resolve Hbls2_final.

  Lemma le_max : forall n m o,
    n <= m
    -> n <= max m o.
    intros; destruct (le_lt_dec m o) as [Hl | Hr]; [
      generalize (max_r _ _ Hl)
      | assert (Ho : o <= m); [ | generalize (max_l _ _ Ho) ] ];
    omega.
  Qed.

  Lemma Hbls_nslots' : forall n fs m,
    n <= m
    -> n <= fold_left (fun n f0 => max n (f_nslots f0)) fs m.
    induction fs; simpler; app; apply le_max; auto.
  Qed.

  Lemma Hbls_nslots : forall l f fs n_slots,
   fs # l = Some f
   -> f_nslots f <= fold_left (fun n f => max n (f_nslots f)) fs n_slots.
    induction fs; simpler_expensive; apply Hbls_nslots'; apply le_max_r.
  Qed.

  Hint Resolve Hbls_nslots.

  Lemma grab_filler : forall n m,
    (filler m) # n = None \/ (filler m) # n = Some None.
    induction m; simpler_expensive.
  Qed.

  Theorem slotOk_filler : forall fs scratch rs h2 refs sl n,
    slotOk fs scratch rs h2 refs (filler n) sl.
    red; intros; destruct (grab_filler sl n); equation.
  Qed.

  Hint Resolve slotOk_filler.

  Hint Resolve lall_nil.

  Lemma refsDisjoint_nil : refsDisjoint nil.
    red; simpler.
  Qed.

  Hint Resolve refsDisjoint_nil.

  Theorem refOk_nil : forall fs scratch rs h2 rf,
    refOk fs scratch nil rs h2 nil rf.
    red; simpler.
  Qed.

  Hint Resolve refOk_nil.

  Lemma max_pos : forall fs n,
    1 < n
    -> 1 < fold_left (fun n f => max n (f_nslots f)) fs n.
    induction fs; simpler; app;
      match goal with
        | [ |- context[max ?a ?b] ] => generalize (le_max_l a b); omega
      end.
  Qed.

  Hint Resolve max_pos.

  Hint Extern 1 (_ < _) => omega.

  Hint Resolve nth_error_middle nth_error_after'.
  Hint Rewrite plus_0_r : ltamer.

  Transparent nth_error.

  Lemma nth_error_after''' : forall A v (ls2 : list A) n ls1,
    nth_error ls2 n = Some v
    -> nth_error (ls1 ++ ls2) (n + length ls1) = Some v.
    induction n; destruct ls1; destruct ls2; simpl; unfold error, value in *; intuition; try discriminate;
      try rewrite plus_0_r; auto; match goal with
                                    | [ H : Some _ = Some _ |- _ ] => injection H
                                  end; intros; subst; eauto.
  Qed.

  Hint Resolve nth_error_after''' Hbls_nslots'.

  Hint Extern 1 (length (filler _) <= _) => rewrite length_filler.
  Hint Extern 0 (f_nslots _ <= _) => eapply Hbls_nslots.
  Hint Extern 1 (iget (_ ::: _) _ >= _) => simpl.

  Lemma iget_first : forall v,
    iget (v ::: zeroRegs (S (S n_regs))) FO >= v.
    simpler.
  Qed.

  Hint Resolve iget_first.

  Lemma le_nslots : forall pr fs,
    p_nslots pr <= fold_left (fun n f => max n (f_nslots f)) fs (S (S (p_nslots pr))).
    intros; apply Hbls_nslots'; omega.
  Qed.

  Hint Resolve le_nslots.

  Theorem genProg_correct : forall pr r1,
    Flat.evalPr pr r1
    -> exists h2, exists r2, Asm.evalPr (genProg n_regs pr) h2 r2
      /\ compR h2 r1 r2.
    unfold Flat.evalPr, Asm.evalPr, genProg; simpler;
      guessWithKeep (p_funcs pr,
        fold_left (fun n f => max n (f_nslots f)) (p_funcs pr) (S (p_nslots pr)) ::: zeroRegs (S n_regs),
        NM.empty nat) genExp_correct; simpler;
      splitter; [match goal with
                   | [ |- context[genExp ?a ?b ?c ?d] ] => rewrite <- (pair_uneta (genExp a b c d))
                 end; simpl; eapply evalB_cons; simpl; eauto; rewrite pair_uneta; eauto
        | eauto ].
  Qed.

End n_regs.
