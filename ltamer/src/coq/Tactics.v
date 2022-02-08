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

Require Import Arith Eqdep List.
Require Import LambdaTamer.Axioms.
Require Import LambdaTamer.Util.
Require Import LambdaTamer.Binding.

Set Implicit Arguments.

Ltac concretize := cbv zeta.

Ltac typeof e :=
  let t := type of e in
    t.

Ltac app := match goal with
              | [ H : _ |- _ ] => apply H
            end.

Ltac contradictory := assert False; [idtac | tauto].

Ltac selfer Heq :=
  generalize Heq; subst;
    let Heq := fresh "Heq" in
      (intro Heq; rewrite (UIP_refl _ _ Heq) in *; clear Heq).

Ltac ext_eq := apply ext_eq_dep; intro.
Ltac ext_eq_forall := apply ext_eq_forallT; intro.

Lemma eta_eq : forall T1 T2 (f : T1 -> T2),
  (fun x => f x) = f.
  intros; ext_eq; trivial.
Qed.

Section injection_existT.
  Variable A : Type.
  Variable f : A -> Type.

  Lemma injection_existT : forall f x1 x2 y1 y2,
    existT (A := A) f x1 y1 = existT f x2 y2
    -> x1 = x2.
    inversion 1; reflexivity.
  Qed.
End injection_existT.

Ltac push_var H :=
  generalize (injection_existT H); intro; subst;
    repeat match goal with
             | [ Heq : _ |- _ ] =>
               let H := fresh "H" in
                 (generalize (inj_pairT2 _ _ _ _ _ Heq); clear Heq;
                   intro H; injection H; clear H)
           end;
    intros; subst.

Ltac invert_helper :=
  subst; repeat (match goal with
                    | [ H : context[existT _ _ _ = existT _ _ _] |- _ ] => push_var H
                 end; subst).

Ltac invert H := inversion H; invert_helper.

Definition Injected T (v : T) := True.

Ltac injector H :=
  match goal with
    | [ _ : Injected H |- _ ] => fail 1
    | _ =>
      injection H; intros; try subst;
        (clear H || (assert (Injected H); [ constructor | ]))
  end.

Ltac simpler_goal :=
  match goal with
    | [ Heq : _ = _ |- _ ] =>
      (rewrite (UIP_refl _ _ Heq) in *; clear Heq)
      || (generalize (inj_pairT2 _ _ _ _ _ Heq); clear Heq)

    | [ H : _ :: _ = _ :: _ |- _ ] => injector H
    | [ H : value _ = value _ |- _ ] => injector H
    | [ H : Some _ = Some _ |- _ ] => injector H
    | [ H : S _ = S _ |- _ ] => injector H
    | [ H : (_, _) = (_, _) |- _ ] => injector H

    | [ H : unit |- _ ] => destruct H
    | [ H : ex _ |- _ ] => destruct H
    | [ H : (_ * _)%type |- _ ] => destruct H
    | [ H : vars _ = vars _ |- _ ] => (injection H; clear H) || unfold vars in H
    | [ H : var1 _ = var1 _ |- _ ] => (injection H; clear H) || unfold var1 in H
    | [ H : vars2 _ _ = vars2 _ _ |- _ ] => (injection H; clear H) || unfold vars2 in H
    | [ H : vars3 _ _ _ = vars3 _ _ _ |- _ ] => (injection H; clear H) || unfold vars3 in H

    | [ H1 : ?X = _, H2 : ?X = _ |- _ ] =>
      rewrite H1 in H2; injection H2; clear H2

    | [ H : Injected (refl_equal _) |- _ ] => clear H
  end.

Ltac simpler_goal_expensive :=
  match goal with
    | [ |- context[False_rect _ ?pf] ] => contradictory; exact pf
    | [ |- context[False_ind _ ?pf] ] => contradictory; exact pf
    | [ |- context[False_rec _ ?pf] ] => contradictory; exact pf

    | [ Heq : _ = _ |- _ ] =>
      match goal with
        | [ |- context[Heq] ] => selfer Heq
        | [ _ : context[Heq] |- _ ] => selfer Heq
      end

    | [ |- context[?E] ] => rewrite (eta_eq E)

    | [ |- context[eq_nat_dec ?X ?Y] ] => destruct (eq_nat_dec X Y)
    | [ H : context[eq_nat_dec ?X ?Y] |- _ ] => destruct (eq_nat_dec X Y)
    | [ |- context[le_lt_dec ?X ?Y] ] => destruct (le_lt_dec X Y)
    | [ H : context[le_lt_dec ?X ?Y] |- _ ] => destruct (le_lt_dec X Y)

    | [ |- context[match ?PF with refl_equal => _ end] ] =>
      rewrite (UIP_refl _ _ PF) || (generalize PF; rewrite PF)

    | [ H : context[existT _ _ _ = existT _ _ _] |- _ ] => push_var H
  end.

Ltac compute_UIP := compute; repeat progress (
  match goal with
    | [ |- context[match ?PF with refl_equal => _ end] ] =>
      rewrite (UIP_refl _ _ PF)
  end; compute).

Ltac compute_UIP_ext := compute_UIP; repeat (ext_eq; compute_UIP); trivial.

Ltac push_vars :=
  match goal with
    | [ H : vars _ = vars _ \/ _ |- _ ] =>
      destruct H as [H | H]; [push_var H | idtac]
  end.

Ltac simpler :=
  intuition;
    repeat progress
      (autorewrite with ltamer in *;
        repeat progress (simpl in *; try subst;
          unfold eq_rect_r, eq_rec_r in * );
        try simpler_goal; try ext_eq; try ext_eq_forall; try congruence; intuition).

Ltac simpler_expensive := simpler; repeat (simpler_goal_expensive; simpler).

Ltac refler :=
  repeat match goal with
           | [ |- context[match ?PF with refl_equal => _ end] ] =>
             generalize PF; rewrite PF
         end;
  simpler.

Ltac simplerN n :=
  match n with
    | O => simpler
    | S ?n' =>
      simpler;
      try match goal with
            | [ H : _ |- _ ] => apply H; simplerN n'
          end
  end.

Ltac clear_all :=
  repeat match goal with
           | [ H : _ |- _ ] => clear H
         end.

Ltac equation := simpler; repeat (
  match goal with
    | [ H : _ |- _ ] => rewrite H; [idtac]
  end;
  simpler).

Ltac equation_expensive := equation; repeat (simpler_goal_expensive; equation).

Ltac matcher chooser :=
  match goal with
    | [ H : forall x : ?T, _ |- _ ] =>
      chooser T ltac:(fun e => generalize (H e); clear H; intro H)
    | [ |- ex (A := ?T) _ ] =>
      chooser T ltac:(fun e => exists e)
  end.

Ltac default_chooser T k :=
  match goal with
    | [ |- context[?E] ] => k E
    | [ H : context[?E] |- _ ] => k E
  end.

Ltac matching simpler chooser := simpler; repeat (matcher chooser; simpler).

Hint Rewrite cast_coalesce : ltamer.


(** * Proving that a substitution relation is a function *)

Ltac srel_feq X Y :=
  assert (X = Y); [
    apply ext_eq; intro x;
      match goal with
        | [ H : _ = _ |- _ ] =>
          generalize (eq_args x H); congruence
      end
    | subst
  ].

Ltac srel_discriminate :=
  match goal with
    | [ H : ?X = ?Y |- _ ] =>
      generalize (eq_args unit H); intuition; discriminate
  end.

Ltac srel_all_Set :=
  match goal with
    | [ H : ?X = ?Y |- _ ] =>
      contradictory; apply eq_all_Sets;
        generalize (eq_args unit H);
          generalize (eq_args Empty_set H);
            congruence
  end.

Ltac srel_simpler :=
  simpler;
  try srel_discriminate;
    try srel_all_Set;
      repeat match goal with
               | [ t1 : _ -> _, t2 : _ -> _ |- _ ] => srel_feq t1 t2
             end;
      f_equal; simpler.

Ltac srel_func :=
  induction 1; inversion 1; srel_simpler.

Ltac equate e1 e2 := let H := fresh in assert (H : e1 = e2); [reflexivity | clear H].
Ltac equateNew e1 e2 :=
  match e1 with
    | e2 => fail 1
    | _ => equate e1 e2
  end.

Ltac mini_simpler :=
  repeat progress (simpl in *; intros; subst;
    repeat match goal with
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ :: _ = _ :: _ |- _ ] => injector H
             | [ H : value _ = value _ |- _ ] => injector H
             | [ H : Some _ = Some _ |- _ ] => injector H
             | [ H : S _ = S _ |- _ ] => injector H
             | [ H : (_, _) = (_, _) |- _ ] => injector H
           end; try congruence).

Ltac tryAll f opts :=
  f opts
  || match opts with
       | (?hd, ?tl) => f tl || tryAll f hd
     end.

Ltac guessOne opts H :=
  match type of H with
    | forall x : ?T, _ =>
      tryAll ltac:(fun v => generalize (H v); clear H; intro H) opts
      || match type of T with
           | Prop =>
             (let H' := fresh "H'" in
               assert (H' : T); [
                 solve [ eauto 7 ]
                 | generalize (H H'); clear H H'; intro H
               ]) || fail 1
           | _ =>
             let x := fresh "x" in
               evar (x : T);
               let y := eval cbv delta [x] in x in
                 clear x; generalize (H y); clear H; intro H
         end
  end.

Ltac guessWith opts H := repeat guessOne opts H.

Ltac guessWithKeep opts H :=
  let H' := fresh "H'" in
    generalize H; intro H'; hnf in H'; simpl in H'; guessWith opts H'.

Ltac guess := guessWith tt.
Ltac guessKeep := guessWithKeep tt.

Ltac splitter := repeat match goal with
                          | [ |- _ /\ _ ] => split
                          | [ |- ex _ ] => econstructor
                        end.

Theorem dep_destruct : forall (T : Type) (T' : T -> Type) x (v : T' x) (P : T' x -> Prop),
  (forall x' (v' : T' x') (Heq : x' = x), P (match Heq in (_ = x) return (T' x) with
                                               | refl_equal => v'
                                             end))
  -> P v.
  intros.
  generalize (H _ v (refl_equal _)); trivial.
Qed.

Theorem dep_destructT : forall (T : Type) (T' : T -> Type) x (v : T' x) (P : T' x -> Type),
  (forall x' (v' : T' x') (Heq : x' = x), P (match Heq in (_ = x) return (T' x) with
                                               | refl_equal => v'
                                             end))
  -> P v.
  intros.
  generalize (X _ v (refl_equal _)); trivial.
Qed.

Ltac dep_destruct E :=
  clear E ||
  let doit A :=
    let T := type of A in
      generalize dependent E;
        let e := fresh "e" in
          intro e; pattern e;
            (apply (@dep_destruct T) || apply (@dep_destructT T));
              let x := fresh "x" with v := fresh "v"  in
                intros x v; destruct v; try clear e; mini_simpler;
                  let bestEffort Heq E tac :=
                    repeat match goal with
                             | [ H : context[E] |- _ ] =>
                               match H with
                                 | Heq => fail 1
                                 | _ => generalize dependent H
                               end
                           end;
                    generalize Heq; tac Heq; clear Heq; intro Heq;
                      rewrite (UIP_refl _ _ Heq); intros in
                  repeat match goal with
                           | [ Heq : ?X = ?X |- _ ] =>
                             generalize (UIP_refl _ _ Heq); intro; subst; clear Heq
                           | [ Heq : ?E = _ |- _ ] => bestEffort Heq E ltac:(fun E => rewrite E)
                           | [ Heq : _ = ?E |- _ ] => bestEffort Heq E ltac:(fun E => rewrite <- E)
                         end;
                  try clear e
                  in match type of E with
                       | _ ?A => doit A
                       | _ _ ?A => doit A
                       | _ _ _ ?A => doit A
                     end; simpl in *.

Ltac forward H :=
  match type of H with
    | ?P -> _ => let H' := fresh "H'" in
      assert (H' : P); [ | generalize (H H'); clear H H'; intro H ]
  end.

Ltac hypEq H :=
  match goal with
    | [ |- ?P ] =>
      let P' := type of H in
        replace P with P'; [ assumption | clear H ]
  end.

Ltac inverter H := inversion H; clear H.
Ltac invert_1 H := inversion H; []; clear H.
Ltac invert_1_2 H := ((inversion H; []) || (inversion H; [|])); clear H.

Ltac comega := contradictory; omega.
