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


Hint Constructors evalP eval evalPr.

Lemma csePrimop_correct1 : forall h p1 h' v,
  evalP h p1 h' v
  -> forall G p2,
    primop_equiv G p1 p2
    -> (forall x1 sv x2, In (x1, (x2, sv)) G -> x1 = x2)
    -> evalP h (fst (csePrimop p2)) h' v.
  destruct 1; inversion 1; simpler;
    repeat match goal with
             | [ H : In _ _, H' : forall x1 sv x2, In _ _ -> _ = _ |- _ ] =>
               generalize (H' _ _ _ H); clear H; simpler
           end.
Qed.

Fixpoint seval (vs : list val) (sv : sval) {struct sv} : option val :=
  match sv with
    | SVar n => vs # n
    | SUnit => Some VUnit
    | SPair sv1 sv2 => match seval vs sv1, seval vs sv2 with
                         | Some v1, Some v2 => Some (VPair v1 v2)
                         | _, _ => None
                       end
    | SInl sv1 => match seval vs sv1 with
                    | Some v1 => Some (VInl v1)
                    | _ => None
                  end
    | SInr sv2 => match seval vs sv2 with
                    | Some v2 => Some (VInr v2)
                    | _ => None
                  end
    | SBase b => Some (VBase b)
  end.

Lemma csePrimop_correct2 : forall h p1 h' v,
  evalP h p1 h' v
  -> forall G p2 vs,
    primop_equiv G p1 p2
    -> (forall x1 sv x2, In (x1, (x2, sv)) G -> x1 = x2)
    -> (forall x1 sv x2, In (x1, (x2, sv)) G -> seval vs sv = Some x1)
    -> match snd (csePrimop p2) with
         | Some sv => seval vs sv = Some v /\ h' = h
         | None => True
       end.
  destruct 1; inversion 1; simpler;
    repeat (match goal with
              | [ H : In _ _, H' : forall x1 sv x2, In _ _ -> _, H'' : forall x1 sv x2, In _ _ -> _ |- _ ] =>
               generalize (H' _ _ _ H); generalize (H'' _ _ _ H); clear H
              | [ |- context[match ?E with SVar _ => _ | SUnit => _ | SPair _ _ => _
                               | SInl _ => _ | SInr _ => _ | SBase _ => _ end] ] =>
                destruct E
              | [ _ : context[match ?E with Some _ => _ | None => _ end] |- _ ] =>
                destruct E
            end; equation).
Qed.

Lemma lookup_correct : forall sv vs G xs,
  (forall x1 sv x2, In (x1, (x2, sv)) G -> x1 = x2)
  -> (forall (x1 : val) (sv : sval) (x2 : val),
    In (x1, (x2, sv)) G -> seval vs sv = Some x1)
  -> (forall x sv, In (x, sv) xs -> In (x, (x, sv)) G)
  -> match lookup sv xs with
       | Some x' => seval vs sv = Some x' /\ In (x', (x', sv)) G
       | None => True
     end.
  induction xs; simpler;
    match goal with
      [ |- context[if ?E then _ else _] ] => destruct E
    end; simpler;
  match goal with
    | [ H : forall x y, _ \/ _ -> _ |- _ ] =>
      generalize (H _ _ (or_introl _ (refl_equal _))); simpler; eauto
  end;
  match goal with
    | [ IH : _ -> match ?E with Some _ => _ | None => _ end |- _ ] => guess IH; destruct E; simpler
  end.
Qed.

Lemma seval_push : forall x xs,
  seval (x :: map (@fst _ sval) xs) (SVar (length xs)) = Some x.
  Hint Rewrite map_length : ltamer.

  simpler_expensive.
Qed.

Lemma seval_push2 : forall x y xs,
  seval (x :: y :: map (@fst _ sval) xs) (SVar (S (length xs))) = Some x.
  Hint Rewrite map_length : ltamer.
    
  simpler_expensive.
Qed.
  
Hint Resolve seval_push seval_push2.

Lemma seval_monotone : forall vs vs',
  vs ~> vs'
  -> forall sv v, seval vs sv = Some v
    -> seval vs' sv = Some v.
  induction sv; simpler; eauto;
    repeat (match goal with
              | [ _ : context[match ?E with Some _ => _ | None => _ end] |- _ ] => destruct E
              | [ H : _ |- _ ] => rewrite (H _ (refl_equal _))
            end; simpler).
Qed.

Hint Resolve seval_monotone.

Lemma eq_push : forall v0 len x0,
  (forall (x1 : val) (sv : sval) (x2 : val),
    In (x1, (x2, sv)) x0 -> x1 = x2)
  -> (forall (x2 : val) (sv : sval) (x3 : val),
    In (x2, (x3, sv)) ((v0, (v0, len)) :: x0) -> x2 = x3).
  simpler; eauto.
Qed.

Lemma seval_push' : forall s v0 x1 x0,
  seval (map (fst (A:=val) (B:=sval)) ((v0, s) :: x1)) s = Some v0
  -> (forall (x2 : val) (sv : sval) (x3 : val),
    In (x2, (x3, sv)) x0
    -> seval (map (fst (A:=val) (B:=sval)) x1) sv = Some x2)
  -> forall (x2 : val) (sv : sval) (x3 : val),
    In (x2, (x3, sv)) ((v0, (v0, s)) :: x0) ->
    seval (map (fst (A:=val) (B:=sval)) ((v0, s) :: x1)) sv =
    Some x2.
  simpler; eauto.
Qed.

Lemma inc_push : forall v0 len x0 x1,
  (forall (x : val) (sv : sval), In (x, sv) x1 -> In (x, (x, sv)) x0)
  -> (forall (x2 : val) (sv : sval),
    In (x2, sv) ((v0, len) :: x1)
    -> In (x2, (x2, sv)) ((v0, (v0, len)) :: x0)).
  simpler.
Qed.

Lemma seval_push'' : forall G xs s v,
  (forall (x1 : val) (sv : sval) (x2 : val),
    In (x1, (x2, sv)) G
    -> seval (map (fst (A:=val) (B:=sval)) xs) sv = Some x1)
  -> seval (map (fst (A:=val) (B:=sval)) xs) s = Some v
  -> (forall (x1 : val) (sv : sval) (x2 : val),
    In (x1, (x2, sv)) ((v, (v, s)) :: G)
    -> seval (map (fst (A:=val) (B:=sval)) xs) sv = Some x1).
  simpler; eauto.
Qed.

Lemma sevalA_push : forall G xs s v sF F,
  (forall (x1 : val) (sv : sval) (x2 : val),
    In (x1, (x2, sv)) G
    -> seval (map (fst (A:=val) (B:=sval)) xs) sv = Some x1)
  -> seval (map (fst (A:=val) (B:=sval)) xs) s = Some v
  -> seval (map (fst (A:=val) (B:=sval)) xs) sF = Some F
  -> (forall (x1 : val) (sv : sval) (x2 : val),
    In (x1, (x2, sv)) ((F, (F, sF)) :: (v, (v, s)) :: G)
    -> seval (map (fst (A:=val) (B:=sval)) xs) sv = Some x1).
  simpler; eauto.
Qed.

Lemma inc_push' : forall v s G xs,
  (forall (x : val) (sv : sval), In (x, sv) xs -> In (x, (x, sv)) G)
  -> (forall (x : val) (sv : sval),
    In (x, sv) xs -> In (x, (x, sv)) ((v, (v, s)) :: G)).
  simpler.
Qed.

Hint Resolve eq_push seval_push' inc_push seval_push'' sevalA_push inc_push'.

Lemma cseExp_correct : forall s1 h e1 r,
  eval s1 h e1 r
  -> forall G e2 s2 (xs : list (val * sval)),
    exp_equiv G e1 e2
    -> (forall x1 sv x2, In (x1, (x2, sv)) G -> x1 = x2)
    -> (forall x1 sv x2, In (x1, (x2, sv)) G -> seval (map (@fst _ _) xs) sv = Some x1)
    -> (forall x sv, In (x, sv) xs -> In (x, (x, sv)) G)
    -> (forall l f1, s1 # l = Some f1
      -> exists f2, exists G', exists xs',
        (forall F1 F2 x1 x2, exp_equiv ((F1, F2) :: (x1, x2) :: G') (f1 F1 x1) (f2 F2 x2))
        /\ s2 # l = Some (fun F x => cseExp (f2 (F, SVar (S (length xs'))) (x, SVar (length xs')))
          ((F, SVar (S (length xs'))) :: (x, SVar (length xs')) :: xs'))
        /\ (forall x1 sv x2, In (x1, (x2, sv)) G' -> x1 = x2)
        /\ (forall x1 sv x2, In (x1, (x2, sv)) G' -> seval (map (@fst _ _) xs') sv = Some x1)
        /\ (forall x sv, In (x, sv) xs' -> In (x, (x, sv)) G'))
    -> length s2 = length s1
    -> eval s2 h (cseExp e2 xs) r.
  Hint Extern 1 (eval _ _ ((fun F x => _) _ _) _) =>
    match goal with
      | [ H : forall x, _ |- _ ] => simpl; eapply H; eauto
    end.
  Hint Extern 1 (seval (map _ (_ :: _)) _ = _) => simpl map.

  induction 1; inversion 1; simpler;
    repeat (match goal with
              | [ H : In _ _, H' : forall x1 sv x2, In _ _ -> _,
                  H'' : forall x1 sv x2, In _ _ -> _ |- _ ] =>
                generalize (H' _ _ _ H); generalize (H'' _ _ _ H); clear H
            end; simpler);
    try match goal with
          | [ H : _ # _ = Some _, H' : _ |- _ ] => generalize (H' _ _ H); simpler
          | [ H : evalP _ ?p1 _ _ , _ : primop_equiv _ ?p1 ?p2 |- _ ] =>
            guessKeep (csePrimop_correct1 H); guessWithKeep (p1, p2) csePrimop_correct2;
            destruct (csePrimop p2); simpler
        end;
    repeat match goal with
             | [ G : list (val * (val * sval)) |- context[match lookup ?s ?xs with Some _ => _ | None => _ end] ] =>
               generalize (lookup_correct s (map (@fst _ _) xs) G xs); destruct (lookup s xs); simpler
             | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E; simpler
             | [ H : ?E = Some _, H' : context[match ?E with Some _ => _ | None => _ end] |- _ ] =>
               rewrite H in H'; simpler
             | [ |- context[match ?E with SVar _ => _ | SUnit => _ | SPair _ _ => _
                              | SInl _ => _ | SInr _ => _ | SBase _ => _ end] ] =>
             destruct E
           end; try econstructor; (concretize; eauto 7).
Qed.

Hint Constructors evalPr.

Lemma cseProg_correct : forall s1 pr1 r,
  evalPr s1 pr1 r
  -> forall G pr2 s2 (xs : list (val * sval)),
    prog_equiv G pr1 pr2
    -> (forall x1 sv x2, In (x1, (x2, sv)) G -> x1 = x2)
    -> (forall x1 sv x2, In (x1, (x2, sv)) G -> seval (map (@fst _ _) xs) sv = Some x1)
    -> (forall x sv, In (x, sv) xs -> In (x, (x, sv)) G)
    -> (forall l f1, s1 # l = Some f1
      -> exists f2, exists G', exists xs',
        (forall F1 F2 x1 x2, exp_equiv ((F1, F2) :: (x1, x2) :: G') (f1 F1 x1) (f2 F2 x2))
        /\ s2 # l = Some (fun F x => cseExp (f2 (F, SVar (S (length xs'))) (x, SVar (length xs')))
          ((F, SVar (S (length xs'))) :: (x, SVar (length xs')) :: xs'))
        /\ (forall x1 sv x2, In (x1, (x2, sv)) G' -> x1 = x2)
        /\ (forall x1 sv x2, In (x1, (x2, sv)) G' -> seval (map (@fst _ _) xs') sv = Some x1)
        /\ (forall x sv, In (x, sv) xs' -> In (x, (x, sv)) G'))
    -> length s1 = length s2
    -> evalPr s2 (cseProg pr2 xs) r.
  Hint Resolve cseExp_correct.

  induction 1; inversion 1; simpler; eauto;
    constructor; match goal with
                   | [ IH : _ |- _ ] =>
                     eapply IH; eauto; equation_expensive; eauto 8
                 end.
Qed.

Lemma CseProg_correct : forall Pr r,
  EvalPr nil Pr r
  -> Prog_wf Pr
  -> EvalPr nil (CseProg Pr) r.
  unfold EvalPr, CseProg, Prog_wf; intros; eapply cseProg_correct; eauto; simpler.
Qed.
