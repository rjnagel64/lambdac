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

Require Import LambdaTamer.LambdaTamer.

Require Import Closed.

Require Import CSE.

Set Implicit Arguments.


Hint Constructors exp_equiv primop_equiv prog_equiv.

Section vars.
  Variables var1 var2 : Type.

  Lemma In_sval : forall x1 sv1 x2 sv2 G,
    In ((x1, sv1), (x2, sv2)) G
    -> (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      In ((x1, sv1), (x2, sv2)) G -> sv1 = sv2)
    -> sv1 = sv2.
    induction G; simpler; eauto.
  Qed.

  Implicit Arguments In_sval [x1 sv1 x2 sv2 G].

  Lemma csePrimop_wf1 : forall G (p1 : primop (var1 * sval)) (p2 : primop (var2 * sval)),
    primop_equiv G p1 p2
    -> forall G', (forall x1 sv1 x2 sv2, In ((x1, sv1), (x2, sv2)) G -> In (x1, x2) G')
    -> primop_equiv G' (fst (csePrimop p1)) (fst (csePrimop p2)).
    destruct 1; simpler; eauto.
  Qed.

  Lemma csePrimop_wf2 : forall G (p1 : primop (var1 * sval)) (p2 : primop (var2 * sval)),
    primop_equiv G p1 p2
    -> (forall x1 sv1 x2 sv2, In ((x1, sv1), (x2, sv2)) G -> sv1 = sv2)
    -> snd (csePrimop p1) = snd (csePrimop p2).
    destruct 1; simpler;
      repeat match goal with
               | [ H : In _ _ |- _ ] => rewrite (In_sval H)
             end; eauto.
  Qed.

  Definition mkG := map (fun p : sval * (var1 * var2) => (fst (snd p), snd (snd p))).
  Definition mkXs1 := map (fun p : sval * (var1 * var2) => (fst (snd p), fst p)).
  Definition mkXs2 := map (fun p : sval * (var1 * var2) => (snd (snd p), fst p)).

  Lemma lookup_wf : forall sv xs,
    (lookup sv (mkXs1 xs) = None /\ lookup sv (mkXs2 xs) = None)
    \/ exists x1, exists x2, lookup sv (mkXs1 xs) = Some x1
      /\ lookup sv (mkXs2 xs) = Some x2
      /\ In (sv, (x1, x2)) xs.
    induction xs; simpler;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; simpler; eauto 7.
  Qed.

  Lemma In_mkG : forall sv x1 x2 xs,
    In (sv, (x1, x2)) xs
    -> In (x1, x2) (mkG xs).
    induction xs; simpler.
  Qed.

  Hint Resolve In_mkG.

  Lemma length_mkXs2 : forall xs,
    length (mkXs2 xs) = length (mkXs1 xs).
    induction xs; simpler.
  Qed.

  Hint Rewrite length_mkXs2 : ltamer.

  Lemma eq_or : forall v1 v2 s G,
    (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      In (x1, sv1, (x2, sv2)) G
      -> sv1 = sv2)
    -> (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      (v1, s, (v2, s)) = (x1, sv1, (x2, sv2)) \/ In (x1, sv1, (x2, sv2)) G
      -> sv1 = sv2).
    simpler; eauto.
  Qed.

  Lemma eq_orA : forall F1 F2 v1 v2 sF s G,
    (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      In (x1, sv1, (x2, sv2)) G
      -> sv1 = sv2)
    -> (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      (F1, sF, (F2, sF)) = (x1, sv1, (x2, sv2)) \/ (v1, s, (v2, s)) = (x1, sv1, (x2, sv2)) \/ In (x1, sv1, (x2, sv2)) G
      -> sv1 = sv2).
    simpler; eauto.
  Qed.

  Lemma xs_or : forall v1 v2 s xs G,
    (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      In (x1, sv1, (x2, sv2)) G -> In (sv1, (x1, x2)) xs)
   -> (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
     (v1, s, (v2, s)) = (x1, sv1, (x2, sv2)) \/ In (x1, sv1, (x2, sv2)) G
     -> In (sv1, (x1, x2)) ((s, (v1, v2)) :: xs)).
    simpler; eauto.
  Qed.

  Lemma xs_known : forall v1 v2 s xs G,
    (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      In (x1, sv1, (x2, sv2)) G -> In (sv1, (x1, x2)) xs)
    -> In (s, (v1, v2)) xs
    -> (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      (v1, s, (v2, s)) = (x1, sv1, (x2, sv2)) \/ In (x1, sv1, (x2, sv2)) G
      -> In (sv1, (x1, x2)) xs).
    simpler; eauto.
  Qed.

  Hint Resolve eq_or eq_orA xs_or xs_known.

  Lemma cseExp_wf : forall G (e1 : exp (var1 * sval)) (e2 : exp (var2 * sval)),
    exp_equiv G e1 e2
    -> forall xs,
      (forall x1 sv1 x2 sv2, In ((x1, sv1), (x2, sv2)) G -> sv1 = sv2)
      -> (forall x1 sv1 x2 sv2, In ((x1, sv1), (x2, sv2)) G
        -> In (sv1, (x1, x2)) xs)
      -> exp_equiv (mkG xs) (cseExp e1 (mkXs1 xs)) (cseExp e2 (mkXs2 xs)).
    Hint Extern 1 (exp_equiv ((?v1, ?v2) :: mkG ?xs)
      (cseExp (_ (?v1, ?s)) ((?v1, ?s) :: mkXs1 ?xs))
      (cseExp (_ (?v2, ?s)) ((?v2, ?s) :: mkXs2 ?xs))) =>
    match goal with
      | [ H : _ |- _ ] => apply (H (v1, s) (v2, s) ((s, (v1, v2)) :: xs))
    end.

    induction 1; simpler;
      repeat match goal with
               | [ H : primop_equiv _ _ _ |- _ ] =>
                 generalize (csePrimop_wf1 H); guessKeep csePrimop_wf2; clear H;
                   destruct (csePrimop p1); destruct (csePrimop p2); simpler
               | [ H : In ((_, ?s1), (_, ?s2)) ?G,
                   H' : forall x1 sv1 x2 sv2, In ((x1, sv1), (x2, sv2)) ?G -> sv1 = sv2 |- _ ] =>
                 match s1 with
                   | s2 => fail 1
                   | _ => generalize (H' _ _ _ _ H); intro; subst
                 end
               | [ |- context[match ?E with SVar _ => _ | SUnit => _
                                | SPair _ _ => _ | SInl _ => _ | SInr _ => _ | SBase _ => _ end] ] =>
                 destruct E
               | [ |- context[match lookup ?s (mkXs1 ?xs) with Some _ => _ | None => _ end] ] =>
                 destruct (lookup_wf s xs); equation
               | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E; simpler
             end; eauto 10.
  Qed.

  Lemma xs_init : forall v1 v2 sv1 x1 sv2 x2 xs G,
    (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      In (x1, sv1, (x2, sv2)) G -> In (sv1, (x1, x2)) xs)
    -> (v1, SVar (length (mkXs1 xs)), (v2, SVar (length (mkXs1 xs)))) = (x1, sv1, (x2, sv2))
    \/ In (x1, sv1, (x2, sv2)) G
    -> (SVar (length (mkXs1 xs)), (v1, v2)) = (sv1, (x1, x2)) \/
    In (sv1, (x1, x2)) xs.
    simpler; eauto.
  Qed.

  Lemma xs_initA : forall F1 F2 v1 v2 sv1 x1 sv2 x2 xs G,
    (forall (x1 : var1) (sv1 : sval) (x2 : var2) (sv2 : sval),
      In (x1, sv1, (x2, sv2)) G -> In (sv1, (x1, x2)) xs)
    -> (F1, SVar (S (length (mkXs1 xs))), (F2, SVar (S (length (mkXs1 xs))))) = (x1, sv1, (x2, sv2))
    \/ (v1, SVar (length (mkXs1 xs)), (v2, SVar (length (mkXs1 xs)))) = (x1, sv1, (x2, sv2))
    \/ In (x1, sv1, (x2, sv2)) G
    -> (SVar (S (length (mkXs1 xs))), (F1, F2)) = (sv1, (x1, x2)) \/
    (SVar (length (mkXs1 xs)), (v1, v2)) = (sv1, (x1, x2)) \/
    In (sv1, (x1, x2)) xs.
    simpler; eauto.
  Qed.

  Hint Resolve xs_init xs_initA.

  Lemma cseProg_wf : forall G (pr1 : prog (var1 * sval)) (pr2 : prog (var2 * sval)),
    prog_equiv G pr1 pr2
    -> forall xs,
      (forall x1 sv1 x2 sv2, In ((x1, sv1), (x2, sv2)) G -> sv1 = sv2)
      -> (forall x1 sv1 x2 sv2, In ((x1, sv1), (x2, sv2)) G
        -> In (sv1, (x1, x2)) xs)
      -> prog_equiv (mkG xs) (cseProg pr1 (mkXs1 xs)) (cseProg pr2 (mkXs2 xs)).
    Hint Resolve cseExp_wf.

    Hint Extern 1 (exp_equiv ((?v1, ?v2) :: mkG ?xs)
      (cseExp (_ (?v1, ?s)) ((?v1, ?s) :: mkXs1 ?xs))
      (cseExp (_ (?v2, ?s)) ((?v2, ?s) :: mkXs2 ?xs))) =>
    match goal with
      | [ H : _ |- _ ] => apply (cseExp_wf (H (v1, s) (v2, s)) ((s, (v1, v2)) :: xs)); simpl
    end.

    Hint Extern 1 (exp_equiv ((?F1, ?F2) :: (?v1, ?v2) :: mkG ?xs)
      (cseExp (_ (?F1, ?sF) (?v1, ?s)) ((?F1, ?sF) :: (?v1, ?s) :: mkXs1 ?xs))
      (cseExp (_ (?F2, ?sF) (?v2, ?s)) ((?F2, ?sF) :: (?v2, ?s) :: mkXs2 ?xs))) =>
    match goal with
      | [ H : _ |- _ ] => apply (cseExp_wf (H (F1, sF) (F2, sF) (v1, s) (v2, s))
        ((sF, (F1, F2)) :: (s, (v1, v2)) :: xs)); simpl
    end.

    Hint Extern 1 (prog_equiv ((?v1, ?v2) :: mkG ?xs)
      (cseProg (_ (?v1, ?s)) ((?v1, ?s) :: mkXs1 ?xs))
      (cseProg (_ (?v2, ?s)) ((?v2, ?s) :: mkXs2 ?xs))) =>
    match goal with
      | [ H : _ |- _ ] => apply (H (v1, s) (v2, s) ((s, (v1, v2)) :: xs)); simpl
    end.

    induction 1; simpler; eauto 8.
  Qed.
End vars.

Theorem CseProg_wf : forall Pr, Prog_wf Pr -> Prog_wf (CseProg Pr).
  unfold Prog_wf, CseProg; intros ? H var1 var2; intros;
    apply (cseProg_wf (var1 := var1) (var2 := var2) (H _ _) nil); simpler.
Qed.
