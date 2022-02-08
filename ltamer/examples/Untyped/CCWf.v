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


Hint Constructors Closed.exp_equiv Closed.primop_equiv Closed.prog_equiv.

Section vars.
  Variables var1 var2 : Type.

  Definition eenvF2 b := (eenvF var1 b * eenvF var2 b)%type.
  Definition eenv2 := ihlist eenvF2.

  Fixpoint split1 G (ue : fvs G) (EE : eenv2 ue) {struct EE} : eenv var1 ue :=
    match EE in ihlist _ ue return eenv var1 ue with
      | IHNil => IHNil
      | IHCons _ _ _ (x1, _) EE' => x1 :::* split1 EE'
    end.

  Fixpoint split2 G (ue : fvs G) (EE : eenv2 ue) {struct EE} : eenv var2 ue :=
    match EE in ihlist _ ue return eenv var2 ue with
      | IHNil => IHNil
      | IHCons _ _ _ (_, x2) EE' => x2 :::* split2 EE'
    end.

  Fixpoint eout G (ue : fvs G) (EE : eenv2 ue) {struct EE} : list (var1 * var2) :=
    match EE with
      | IHNil => nil
      | IHCons false _ _ _ EE' => eout EE'
      | IHCons true _ _ vs EE' => vs :: eout EE'
    end.

  Lemma oneE_wf : forall x G EE (wf : x < G),
    In (oneE (split1 EE) wf, oneE (split2 EE) wf) (eout EE).
    induction G; intros; try comega;
      simpl in *; generalize dependent EE; destruct (eq_nat_dec x G); simpler;
        rewrite (ihlist_cons EE); simpl; destruct (ihhead EE); simpl; eauto.
  Qed.

  Hint Resolve oneE_wf.

  Fixpoint unmergeE1 G (ue1 : fvs G) {struct ue1} : forall ue2, eenv2 (merge ue1 ue2) -> eenv2 ue1 :=
    match ue1 return forall ue2, eenv2 (merge ue1 ue2) -> eenv2 ue1 with
      | INil => fun _ _ => IHNil
      | ICons _ true ue1' => fun ue2 EE => ihhead EE :::* unmergeE1 ue1' (itail ue2) (ihtail EE)
      | ICons _ false ue1' => fun ue2 EE => ((tt, tt) : eenvF2 false) :::* unmergeE1 ue1' (itail ue2) (ihtail EE)
    end.

  Fixpoint unmergeE2 G (ue1 : fvs G) {struct ue1} : forall ue2, eenv2 (merge ue1 ue2) -> eenv2 ue2 :=
    match ue1 return forall ue2, eenv2 (merge ue1 ue2) -> eenv2 ue2 with
      | INil => fun _ _ => IHNil' _
      | ICons _ true ue1' => fun ue2 =>
        match ue2 in ilist _ G' return match G' return ilist _ G' -> Type with
                                         | O => fun _ => unit
                                         | S G'' => fun ue2 => forall (ue1' : fvs G'')
                                           (self : forall ue2', eenv2 (merge ue1' ue2') -> eenv2 ue2'),
                                           eenv2 (true ::: merge ue1' (itail ue2))
                                           -> eenv2 ue2
                                       end ue2 with
          | INil => tt
          | ICons _ true ue2' => fun _ self EE => ihhead EE :::* self ue2' (ihtail EE)
          | ICons _ false ue2' => fun _ self EE => ((tt, tt) : eenvF2 false) :::* self ue2' (ihtail EE)
        end ue1' (unmergeE2 ue1')
      | ICons _ false ue1' => fun ue2 =>
        match ue2 in ilist _ G' return match G' return ilist _ G' -> Type with
                                         | O => fun _ => unit
                                         | S G'' => fun ue2 => forall (ue1' : fvs G'')
                                           (self : forall ue2', eenv2 (merge ue1' ue2') -> eenv2 ue2'),
                                           eenv2 (ihead ue2 ::: merge ue1' (itail ue2))
                                           -> eenv2 ue2
                                       end ue2 with
          | INil => tt
          | ICons _ true ue2' => fun _ self EE => ihhead EE :::* self ue2' (ihtail EE)
          | ICons _ false ue2' => fun _ self EE => ((tt, tt) : eenvF2 false) :::* self ue2' (ihtail EE)
        end ue1' (unmergeE2 ue1')
    end.

  Implicit Arguments unmergeE1 [G ue1 ue2].
  Implicit Arguments unmergeE2 [G ue1 ue2].

  Ltac unmerge :=
    intro ue2; dep_destruct ue2; simpler;
      match goal with
        | [ EE : eenv2 _ |- _ ] =>
          match goal with
            | [ v : ilist bool _, IH : forall ue2 EE, _ ?ue1 _ _ _ _ = _ |- _ ] =>
              match v with
                | ue1 => fail 1
                | _ => generalize (IH v); clear IH; intro IH
              end
          end;
          repeat match goal with
                   | [ |- context[if ?b then _ else _] ] => destruct b
                 end;
          rewrite (ihlist_cons EE); destruct (ihhead EE); equation
    end.

  Lemma unmerge1_split1 : forall G (ue1 ue2 : fvs G) (EE : eenv2 (merge ue1 ue2)),
    unmerge1 (split1 EE) = split1 (unmergeE1 EE).
    induction ue1; unmerge.
  Qed.

  Lemma unmerge1_split2 : forall G (ue1 ue2 : fvs G) (EE : eenv2 (merge ue1 ue2)),
    unmerge1 (split2 EE) = split2 (unmergeE1 EE).
    induction ue1; unmerge.
  Qed.

  Lemma unmerge2_split1 : forall G (ue1 ue2 : fvs G) (EE : eenv2 (merge ue1 ue2)),
    unmerge2 (split1 EE) = split1 (unmergeE2 EE).
    induction ue1; unmerge.
  Qed.

  Lemma unmerge2_split2 : forall G (ue1 ue2 : fvs G) (EE : eenv2 (merge ue1 ue2)),
    unmerge2 (split2 EE) = split2 (unmergeE2 EE).
    induction ue1; unmerge.
  Qed.

  Hint Rewrite unmerge1_split1 unmerge1_split2 unmerge2_split1 unmerge2_split2 : ltamer.

  Ltac In_unmerge :=
    intro ue2; dep_destruct ue2; simpler;
      match goal with
        | [ EE : eenv2 _ |- _ ] =>
          rewrite (ihlist_cons EE) in *; simpler;
            repeat match goal with
                     | [ _ : context[if ?b then _ else _] |- _ ] => destruct b; simpler
                     | [ |- context[if ?b then _ else _] ] => destruct b; simpler
                   end
      end.
  
  Lemma In_unmergeE1 : forall p G (ue1 ue2 : fvs G) (EE : eenv2 (merge ue1 ue2)),
    In p (eout (unmergeE1 EE))
    -> In p (eout EE).
    induction ue1; In_unmerge.
  Qed.

  Lemma In_unmergeE2 : forall p G (ue1 ue2 : fvs G) (EE : eenv2 (merge ue1 ue2)),
    In p (eout (unmergeE2 EE))
    -> In p (eout EE).
    induction ue1; In_unmerge.
  Qed.

  Hint Resolve In_unmergeE1 In_unmergeE2.

  Scheme primop_mut := Induction for CPS.primop Sort Prop
    with exp_mut := Induction for CPS.exp Sort Prop.

  Lemma ilist_cons : forall A n (il : ilist A (S n)),
    il = ihead il ::: itail il.
    intros; dep_destruct il; reflexivity.
  Qed.

  Definition pushE (x1 : var1) (x2 : var2) G (ue : fvs (S G)) : eenv2 (itail ue) -> eenv2 ue :=
    match ue in ilist _ G' return match G' return fvs G' -> Type with
                                    | O => fun _ => unit
                                    | S G'' => fun ue => eenv2 (itail ue) -> eenv2 ue
                                  end ue with
      | INil => tt
      | ICons _ false ue' => fun EE => ((tt, tt) : eenvF2 false) :::* EE
      | ICons _ true ue' => fun EE => ((x1, x2) : eenvF2 true) :::* EE
    end.

  Implicit Arguments pushE [G ue].

  Ltac split_push := 
    intros; match goal with
              | [ ue : fvs _ |- _ ] => dep_destruct ue; unfold push';
                match goal with
                  | [ |- context[if ?b then _ else _] ] => destruct b; simpler
                end; reflexivity
            end.

  Lemma split1_push : forall (x2 : var2) G (x1 : var1) (ue : fvs (S G)) (EE : eenv2 (itail ue)),
    x1 +! split1 EE
    = split1 (pushE x1 x2 EE).
    split_push.
  Qed.

  Lemma split2_push : forall (x1 : var1) G (x2 : var2) (ue : fvs (S G)) (EE : eenv2 (itail ue)),
    x2 +! split2 EE
    = split2 (pushE x1 x2 EE).
    split_push.
  Qed.

  Theorem In_pushE : forall x1 x2 G (ue : fvs (S G)) (EE : eenv2 (itail ue)) p,
    In p (eout (pushE x1 x2 EE))
    -> p = (x1, x2) \/ In p (eout EE).
    intros; dep_destruct ue; dep_destruct EE; simpler;
      match goal with
        | [ Heq : _ = _ |- _ ] =>
          match goal with
            [ H : context[Heq] |- _ ] => generalize dependent H
          end; generalize Heq; simpler;
          match goal with
            | [ _ : context[if ?b then _ else _] |- _ ] => destruct b; simpler
          end
      end.
  Qed.

  Implicit Arguments In_pushE [x1 x2 G ue EE p].

  Lemma supplyEnv_wf : forall nG (ue : fvs nG) k1 k2 G x1 x2,
    In (x1, x2) G
    -> (forall (EE : eenv2 ue) (G' : list (var1 * var2)),
      (forall p, In p G -> In p G')
      -> (forall p, In p (eout EE) -> In p G')
      -> exp_equiv G' (k1 (split1 EE)) (k2 (split2 EE)))
    -> exp_equiv G (supplyEnv x1 k1) (supplyEnv x2 k2).
    induction ue; simpler;
      repeat (match goal with
                | [ |- context[if ?b then _ else _] ] => destruct b
                | _ => constructor || app
              end; simpler);
      try match goal with
            | [ H : _ |- _ ] => apply (H IHNil)
            | [ H : _, EE : eenv2 _ |- _ ] => apply (H (((tt, tt) : eenvF2 false) :::* EE))
            | [ H : _, EE : eenv2 _, v1 : var1, v2 : var2 |- _ ] => apply (H (((v1, v2) : eenvF2 true) :::* EE))
          end; simpler.
  Qed.

  Lemma makeEnv_wf : forall nG (ue : fvs nG) (EE : eenv2 ue) G k1 k2,
    (forall (G' : list (var1 * var2)) (x1 : var1) (x2 : var2),
      (forall p, In p G -> In p G')
      -> In (x1, x2) G'
      -> exp_equiv G' (k1 x1) (k2 x2))
    -> (forall p, In p (eout EE) -> In p G)
    -> exp_equiv G (makeEnv (split1 EE) k1) (makeEnv (split2 EE) k2).
    induction ue; simpler; rewrite (ihlist_cons EE) in *; destruct (ihhead EE);
      repeat (match goal with
                | [ |- context[if ?b then _ else _] ] => destruct b
                | _ => app || constructor
              end; simpler).
  Qed.

  Lemma ccExp_wf : forall e Gf nG wf k1 k2,
    (forall Gf' k1' k2',
      (forall p, In p Gf -> In p Gf')
      -> (forall EE G',
        (forall p, In p Gf' -> In p G')
        -> (forall p, In p (eout EE) -> In p G')
        -> Closed.exp_equiv G' (k1' (split1 EE)) (k2' (split2 EE)))
      -> Closed.prog_equiv Gf' (k1 k1') (k2 k2'))
    -> Closed.prog_equiv Gf (ccExp (var := var1) nG e wf k1)
    (ccExp (var := var2) nG e wf k2).
    apply (exp_mut
      (fun p => forall Gf nG wf k1 k2,
        (forall Gf' k1' k2',
          (forall p, In p Gf -> In p Gf')
          -> (forall EE G' k1'' k2'',
            (forall p, In p Gf' -> In p G')
            -> (forall p, In p (eout EE) -> In p G')
            -> (forall G'' x1 x2,
              (forall p, In p G' -> In p G'')
              -> In (x1, x2) G''
              -> Closed.exp_equiv G'' (k1'' x1) (k2'' x2))
            -> Closed.exp_equiv G' (k1' (split1 EE) k1'') (k2' (split2 EE) k2''))
          -> Closed.prog_equiv Gf' (k1 k1') (k2 k2'))
        -> Closed.prog_equiv Gf (ccPrimop (var := var1) nG p wf k1)
        (ccPrimop (var := var2) nG p wf k2))
      (fun e => forall Gf nG wf k1 k2,
        (forall Gf' k1' k2',
          (forall p, In p Gf -> In p Gf')
          -> (forall EE G',
            (forall p, In p Gf' -> In p G')
            -> (forall p, In p (eout EE) -> In p G')
            -> Closed.exp_equiv G' (k1' (split1 EE)) (k2' (split2 EE)))
          -> Closed.prog_equiv Gf' (k1 k1') (k2 k2'))
        -> Closed.prog_equiv Gf (ccExp (var := var1) nG e wf k1)
        (ccExp (var := var2) nG e wf k2))); simpler;
    repeat match goal with
             | [ H : In _ (eout (pushE _ _ _)) |- _ ] => destruct (In_pushE H); clear H
             | [ |- In _ _ ] => solve [ simpler; eauto 7 ]
             | [ |- context[?x1 +! split1 _] ] =>
               match goal with
                 | [ |- context[?x2 +! split2 _] ] =>
                   rewrite (split1_push x2); rewrite (split2_push x1)
               end
             | _ => (apply supplyEnv_wf || apply makeEnv_wf || app || constructor); intros
             | _ => progress autorewrite with ltamer
           end.
  Qed.

End vars.

Theorem CcProg_wf : forall E (wf : CPS.Exp_wf E),
  CPS.Exp_wf E
  -> Closed.Prog_wf (CcProg wf).
  unfold CPS.Exp_wf, Closed.Prog_wf, CcProg, ccProg;
    intros; apply ccExp_wf; constructor;
      match goal with
        | [ H : _ |- _ ] => generalize (H (IHNil' _)); simpler
      end;
      generalize dependent (usedE O (E nat)); intro f; dep_destruct f; simpler.
Qed.
