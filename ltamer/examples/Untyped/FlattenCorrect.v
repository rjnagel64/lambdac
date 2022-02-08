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

Require Import Closed.
Require Import Flat.

Require Import Flatten.

Set Implicit Arguments.


(** * Correctness relations between source and target programs *)

Inductive cr : Closed.val -> Flat.val -> Prop :=
| EquivCont : forall l,
  cr (Closed.VCont l) (Flat.VProc l)

| EquivUnit : cr Closed.VUnit Flat.VUnit

| EquivPair : forall x y x' y',
  cr x x'
  -> cr y y'
  -> cr (Closed.VPair x y) (Flat.VPair x' y')

| EquivInl : forall v1 v2,
  cr v1 v2
  -> cr (Closed.VInl v1) (Flat.VInl v2)
| EquivInr : forall v1 v2,
  cr v1 v2
  -> cr (Closed.VInr v1) (Flat.VInr v2)

| EquivRef : forall l,
  cr (Closed.VRef l) (Flat.VRef l)

| EquivBase : forall b,
  cr (Closed.VBase b) (Flat.VBase b).

Infix "~~" := cr (no associativity, at level 70).

Hint Constructors cr.

Notation "h1 ~~~ h2" := (sall cr h1 h2) (no associativity, at level 70).

Lemma EquivRef' : forall h1 h2,
  h1 ~~~ h2
  -> Closed.VRef (length h1) ~~ Flat.VRef (length h2).
  intros; match goal with
            | [ H : _ |- _ ] => rewrite <- (sall_length H)
          end; auto.
Qed.

Hint Resolve EquivRef'.

Definition varOk (sls : list (option val)) (env : list var) v1 n :=
  match get sls (lookup env n) with
    | Some v2 => v1 ~~ v2
    | _ => False
  end.

Hint Constructors Flat.evalP.

Lemma use_varOk : forall sls env v1 n,
  varOk sls env v1 n
  -> exists v2, get sls (lookup env n) = Some v2 /\ v1 ~~ v2.
  unfold varOk; intros; destruct (get sls (lookup env n)); eauto; tauto.
Qed.

Implicit Arguments use_varOk [sls env v1 n].

Ltac simplr := simpler;
  repeat match goal with
           | [ H1 : In (_, ?n) ?G, H2 : forall v n, In _ ?G -> varOk _ _ _ _ |- _ ] =>
             destruct (use_varOk (H2 _ _ H1)) as [? [? ?]]; clear H1
           | [ H : _ ~~ _ |- _ ] => invert_1_2 H; simpler
           | [ H1 : sall _ _ _, H2 : _ = Some _ |- _ ] => destruct (sall_grab H1 H2) as [? [? ?]]; clear H2
         end.
  
Theorem flattenP_correct : forall h1 p1 h1' v1,
  Closed.evalP h1 p1 h1' v1
  -> forall G p2,
    Closed.primop_equiv G p1 p2
    -> forall env h2 sls, h1 ~~~ h2
      -> (forall v n, In (v, n) G -> varOk sls env v n)
      -> exists h2', exists v2,
        Flat.evalP sls h2 (flattenP p2 env) h2' v2
        /\ h1' ~~~ h2'
        /\ v1 ~~ v2.
  destruct 1; inversion 1; simplr; eauto 8.
Qed.

Ltac useIn :=
  repeat match goal with
           | [ H1 : forall v n, In (v, n) ?G -> _, H2 : In _ ?G |- _ ] =>
             generalize (H1 _ _ H2); clear H1
         end.

Ltac destructs := repeat match goal with
                           | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E
                           | [ _ : context[match ?E with Slot _ => _ | FuncVar _ => _ end] |- _ ] => destruct E
                         end.

Lemma get_eq : forall sls n v n' env,
  n < length env
  -> match env # n with
       | None => False
       | Some (Slot sl) => sl < n'
       | _ => True
     end
  -> get (sls ## n' <~ v) (lookup (Slot n' :: env) n) = get sls (lookup env n).
  unfold lookup; simpler_expensive; useIn; destructs; simpler.
Qed.

Lemma lookup_first : forall v env,
  lookup (v :: env) (length env) = v.
  unfold lookup; simpler.
Qed.

Lemma lookup_rest : forall v n env,
  n < length env
  -> lookup (v :: env) n = lookup env n.
  unfold lookup; simpler_expensive; comega.
Qed.

Lemma lookupA_second : forall F v env,
  lookup (F :: v :: env) (length env) = v.
  unfold lookup; simpler_expensive; comega.
Qed.

Lemma lookupA_first : forall F v env,
  lookup (F :: v :: env) (S (length env)) = F.
  unfold lookup; simpler.
Qed.

Lemma lookupA_rest : forall F v n env,
  n < length env
  -> lookup (F :: v :: env) n = lookup env n.
  unfold lookup; simpler_expensive; comega.
Qed.

Hint Rewrite lookup_first lookup_rest
  lookupA_first lookupA_second lookupA_rest using solve [ eauto ] : ltamer.

Definition slotOk Gbase env n :=
  match lookup env n with
    | Slot sl => sl < Gbase
    | _ => True
  end.

Lemma varOk_push : forall v1 v2 G sls env n',
  v1 ~~ v2
  -> (forall v n, In (v, n) G
    -> varOk sls env v n)
  -> (forall v n, In (v, n) G
    -> n < length env)
  -> (forall v n, In (v, n) G
    -> slotOk n' env n)
  -> n' < length sls
  -> (forall v n, In (v, n) ((v1, length env) :: G)
    -> varOk (sls ## n' <~ (Some v2)) (Slot n' :: env) v n).
  unfold varOk, slotOk; simpler; useIn; destruct (lookup env n); simpler.
Qed.

Lemma trans_ge : forall n m i,
  n >= m
  -> m >= i
  -> n >= i.
  intros; omega.
Qed.

Lemma S_ge : forall n m,
  n >= m
  -> S n >= m.
  intros; omega.
Qed.

Theorem flattenE_monotone : forall e Gbase env,
  f_nslots (flattenE Gbase e env) >= Gbase.
  induction e; simpler; eauto 6 using trans_ge, S_ge.
Qed.

Hint Resolve flattenE_monotone.

Lemma trans_lt : forall n m i,
  i >= m
  -> n < m
  -> n < i.
  intros; omega.
Qed.

Lemma up_lt : forall n m m',
  m' >= m
  -> n < m
  -> n < m'.
  intros; omega.
Qed.

Lemma bound_push : forall G env v1 (v' : var),
  (forall (v : Closed.val) (n : nat),
    In (v, n) G -> n < length env)
  -> (forall (v : Closed.val) (n : nat),
    In (v, n) ((v1, length env) :: G)
    -> n < length (v' :: env)).
  simpler; firstorder.
Qed.

Ltac slotOk_push := unfold slotOk, lookup; simpler_expensive; useIn; simpler; destructs; simpler.

Lemma slotOk_push : forall G env Gbase v1,
  (forall (v : Closed.val) (n : nat),
    In (v, n) G -> slotOk Gbase env n)
  -> (forall (v : Closed.val) (n : nat),
    In (v, n) ((v1, length env) :: G) -> slotOk (S Gbase) (Slot Gbase :: env) n).
  slotOk_push.
Qed.

Lemma slotOk_monotone : forall Gbase env n,
  slotOk Gbase env n
  -> forall Gbase', Gbase' >= Gbase
    -> slotOk Gbase' env n.
  unfold slotOk; simpler; destructs; auto; omega.
Qed.

Fixpoint prog_length (Gf : nat) (pr2 : Closed.prog nat) {struct pr2} : nat :=
  match pr2 with
    | EBody _ => O
    | Abs _ pr2' => S (prog_length (S Gf) (pr2' Gf))
  end.

Fixpoint extendG (n : nat) (G : list (Closed.val * nat)) {struct n} : list (Closed.val * nat) :=
  match n with
    | O => G
    | S n' => extendG n' ((VCont (length G), length G) :: G)
  end.

Fixpoint funcs_equiv (Gf : nat) (s : Closed.closures) (pr2 : Closed.prog nat) {struct pr2} : Prop :=
  match pr2 with
    | EBody _ => True
    | Abs e2 pr2' =>
      match s # Gf with
        | None => True
        | Some e1 => (forall F1 F2 v1 v2, Closed.exp_equiv ((F1, F2) :: (v1, v2) :: extendG Gf nil) (e1 F1 v1) (e2 F2 v2))
      end
      /\ funcs_equiv (S Gf) s (pr2' Gf)
  end.

Lemma plus_1 : forall n, n + 1 = S n.
  intro; omega.
Qed.

Theorem minus_minus_1 : forall n m,
  n - m - 1 = n - S m.
  intros; omega.
Qed.

Hint Rewrite grab_last grab_not_last minus_minus_1 using omega : ltamer.
Hint Rewrite <- minus_n_n minus_n_O : ltamer.

Hint Extern 1 (_ < _) => omega.
Hint Extern 1 (_ <= _) => omega.
Hint Extern 1 (_ > _) => omega.
Hint Extern 1 (_ >= _) => omega.

Lemma match_func' : forall s l e1 pr2 Gf,
  funcs_equiv Gf s pr2
  -> Gf <= l < Gf + prog_length Gf pr2
  -> s # l = Some e1
  -> exists e2,
    (p_funcs (flattenPr Gf pr2)) # (l - Gf) = Some (flattenE 2 (e2 (S l) l) (Slot 1 :: Slot O :: funcEnv l))
    /\ (forall F1 F2 v1 v2, Closed.exp_equiv ((F1, F2) :: (v1, v2) :: extendG l nil) (e1 F1 v1) (e2 F2 v2)).
  induction pr2; simpler;
    destruct (eq_nat_dec l Gf); simpler; eauto;
      match goal with
        | [ H1 : ?X = Some _, H2 : match ?X with Some _ => _ | None => _ end |- _ ] => rewrite H1 in H2
      end; eauto.
Qed.

Theorem match_func : forall s l e1 pr2,
  funcs_equiv O s pr2
  -> s # l = Some e1
  -> l < prog_length O pr2
  -> exists e2,
    (p_funcs (flattenPr O pr2)) # l = Some (flattenE 2 (e2 (S l) l) (Slot 1 :: Slot O :: funcEnv l))
    /\ (forall F1 F2 v1 v2, Closed.exp_equiv ((F1, F2) :: (v1, v2) :: extendG l nil) (e1 F1 v1) (e2 F2 v2)).
  intros; guessKeep (@match_func' s l e1 pr2 O); simpler; eauto.
Qed.

Lemma length_filler : forall n,
  length (filler n) = n.
  induction n; simpler.
Qed.

Hint Rewrite length_filler app_length : ltamer.

Lemma length_funcEnv : forall n,
  length (funcEnv n) = n.
  induction n; simpler.
Qed.

Hint Rewrite length_funcEnv : ltamer.

Lemma lookup_funcEnv : forall F v n,
  lookup (F :: v :: funcEnv n) n = v.
  unfold lookup; simpler_expensive; comega.
Qed.

Lemma lookup_funcEnv2 : forall F v n,
  lookup (F :: v :: funcEnv n) (S n) = F.
  unfold lookup; simpler_expensive; comega.
Qed.

Hint Rewrite lookup_funcEnv lookup_funcEnv2 : ltamer.

Lemma In_extendG : forall v0 n0 Gf G,
  In (v0, n0) (extendG Gf G)
  -> (v0 = VCont n0 /\ n0 < Gf + length G) \/ In (v0, n0) G.
  induction Gf; simpler;
    match goal with
      | [ H1 : _, H2 : _ |- _ ] => generalize (H1 _ H2)
    end; simpler.
Qed.

Implicit Arguments In_extendG [v0 n0 Gf G].

Lemma grab_funcEnv : forall Gf n,
  n < Gf
  -> (funcEnv Gf) # n = Some (FuncVar n).
  induction Gf; simpler_expensive; comega.
Qed.

Hint Rewrite grab_funcEnv using omega : ltamer.

Ltac call := simpler_expensive; try comega;
  match goal with
    | [ H : In _ (extendG _ _) |- _ ] => destruct (In_extendG H); simpler_expensive; try comega
  end.

Theorem grab_2nd_last : forall A x y (s : list A),
  (s ++ x :: y :: nil) # 1 = Some x.
  Hint Rewrite app_length plus_1 : ltamer.
    
  induction s; equation_expensive.
Qed.

Hint Rewrite grab_2nd_last : ltamer.

Lemma varOk_call : forall F1 F2 v1 v2 Gf nslots v0 n,
  In (v0, n) ((F1, S Gf) :: (v1, Gf) :: extendG Gf nil)
  -> F1 ~~ F2
  -> v1 ~~ v2
  -> varOk (filler nslots ++ Some F2 :: Some v2 :: nil) (Slot 1 :: Slot 0 :: funcEnv Gf) v0 n.
  unfold varOk, lookup; call.
Qed.

Lemma bound_call : forall F v Gf,
  forall (v0 : Closed.val) (n : nat),
    In (v0, n) ((F, S Gf) :: (v, Gf) :: extendG Gf nil)
    -> n < length (Slot 1 :: Slot 0 :: funcEnv Gf).
  call.
Qed.

Lemma lookup_funcEnv_cons : forall F v n Gf,
  n < Gf
  -> lookup (F :: v :: funcEnv Gf) n = FuncVar n.
  unfold lookup; simpler_expensive; comega.
Qed.

Hint Rewrite lookup_funcEnv_cons using omega : ltamer.

Lemma slotOk_call : forall F v Gf,
  forall (v0 : Closed.val) (n : nat),
    In (v0, n) ((F, S Gf) :: (v, Gf) :: extendG Gf nil)
    -> slotOk 2 (Slot 1 :: Slot 0 :: funcEnv Gf) n.
  unfold slotOk; call.
Qed.

Lemma In_head : forall A (x : A) ls,
  In x (x :: ls).
  simpler.
Qed.

Hint Resolve In_head.

Lemma nslots_call : forall n_slots F x,
  length (filler (pred (pred n_slots)) ++ F :: x :: nil) >= n_slots.
  simpler.
Qed.

Hint Resolve nslots_call.

Hint Constructors Flat.eval.

Inductive comp : Closed.val -> Flat.val -> Prop :=
| CompCont : forall l v,
  comp (Closed.VCont l) v

| CompUnit : comp Closed.VUnit Flat.VUnit

| CompPair : forall x y x' y',
  comp x x'
  -> comp y y'
  -> comp (Closed.VPair x y) (Flat.VPair x' y')

| CompInl : forall v1 v2,
  comp v1 v2
  -> comp (Closed.VInl v1) (Flat.VInl v2)
| CompInr : forall v1 v2,
  comp v1 v2
  -> comp (Closed.VInr v1) (Flat.VInr v2)

| CompRef : forall l v,
  comp (Closed.VRef l) v

| CompBase : forall b,
  comp (Closed.VBase b) (Flat.VBase b).

Inductive compR : Closed.result -> Flat.result -> Prop :=
| CompAns : forall v1 v2,
  comp v1 v2
  -> compR (Closed.Ans v1) (Flat.Ans v2)
| CompEx : forall v1 v2,
  comp v1 v2
  -> compR (Closed.Ex v1) (Flat.Ex v2).

Hint Constructors comp compR.

Lemma comp_in : forall v1 v2,
  cr v1 v2
  -> comp v1 v2.
  induction 1; eauto.
Qed.

Hint Resolve comp_in.

Section prog.
  Variable pr2 : Closed.prog nat.

  Theorem flattenE_correct : forall s h1 e1 r1,
    Closed.eval s h1 e1 r1
    -> forall G e2 Gbase env h2 sls,
      Closed.exp_equiv G e1 e2
      -> funcs_equiv O s pr2
      -> (forall l e, s # l = Some e -> l < prog_length O pr2)
      -> h1 ~~~ h2
      -> length sls >= f_nslots (flattenE Gbase e2 env)
      -> (forall v n, In (v, n) G -> varOk sls env v n)
      -> (forall v n, In (v, n) G -> n < length env)
      -> (forall v n, In (v, n) G -> slotOk Gbase env n)
      -> exists r2, Flat.eval (p_funcs (flattenPr 0 pr2))
        h2 sls (f_body (flattenE Gbase e2 env)) r2
        /\ compR r1 r2.
    Hint Resolve bound_push slotOk_push slotOk_monotone.
    Hint Resolve varOk_call bound_call slotOk_call.
    Hint Resolve trans_ge S_ge trans_lt up_lt flattenE_monotone.

    Hint Extern 1 (_ >= _) => match goal with
                                | [ |- context[?s ## ?l <~ ?v] ] => rewrite (upd_length s l v)
                              end.

    Hint Extern 5 (varOk _ _ _ _) => eapply varOk_push; eauto 6.

    Hint Extern 1 (varOk _ _ _ _) =>
      match goal with
        | [ H : _ = Some _ |- _ ] => rewrite H
      end.

    induction 1; abstract (inversion 1; simplr; eauto 6;
      try match goal with
            | [ H : Closed.evalP _ _ _ _ |- _ ] => guessKeep (flattenP_correct H); simpler
          end;
      match goal with
        | [ IHeval : forall G : list _, _ |- _ ] =>
          match goal with
            | [ sls : list (option val), Gbase : nat, _ : _ ~~ ?v2 |- _ ] =>
              let sl := match goal with
                          | [ |- context[Assign ?sl _ _] ] => sl
                          | [ _ : _ = Some (VInl _) |- context[ECase _ ?sl _ _ _] ] => sl
                          | [ _ : _ = Some (VInr _) |- context[ECase _ _ _ ?sl _] ] => sl
                        end in
              guessWith (sls ## sl <~ (Some v2)) IHeval
            | _ => guessKeep match_func; simpler; guess IHeval
          end
      end; simpler; eauto 8).
  Qed.
End prog.

Fixpoint getBody2 (Gf : nat) (pr : Closed.prog nat) {struct pr} : Closed.exp nat :=
  match pr with
    | EBody e => e
    | Abs _ pr' => getBody2 (S Gf) (pr' Gf)
  end.

Lemma flattenPr_body : forall pr Gf,
  p_body (flattenPr Gf pr) = f_body (flattenE O (getBody2 Gf pr) (funcEnv (prog_length Gf pr + Gf))).
  Hint Rewrite <- plus_n_Sm : ltamer.

  induction pr; equation.
Qed.

Fixpoint getBody1 (Gf : nat) (pr : Closed.progV) {struct pr} : Closed.expV :=
  match pr with
    | EBody e => e
    | Abs _ pr' => getBody1 (S Gf) (pr' (VCont Gf))
  end.

Fixpoint makeClosures (pr : Closed.prog Closed.val) (s : Closed.closures) {struct pr} : Closed.closures :=
  match pr with
    | EBody _ => s
    | Abs e pr' => makeClosures (pr' (VCont (length s))) (e :: s)
  end.

Lemma makeClosures_correct : forall s pr r,
  Closed.evalPr s pr r
  -> Closed.eval (makeClosures pr s) nil (getBody1 (length s) pr) r.
  induction 1; simpler.
Qed.

Lemma getBody_equiv' : forall G pr1 pr2,
  prog_equiv G pr1 pr2
  -> exp_equiv (extendG (prog_length (length G) pr2) G)
  (getBody1 (length G) pr1) (getBody2 (length G) pr2).
  induction 1; simpler.
Qed.

Lemma getBody_equiv : forall pr1 pr2,
  prog_equiv nil pr1 pr2
  -> exp_equiv (extendG (prog_length O pr2) nil)
  (getBody1 (length (@nil closure)) pr1) (getBody2 O pr2).
  intros pr1 pr2 H; apply (getBody_equiv' H).
Qed.

Lemma makeClosures_extends : forall pr s,
  s ~> makeClosures pr s.
  induction pr; simpler; eauto.
Qed.

Lemma extendG_flip_rewr : forall Gf s,
  S (Gf + length s) = Gf + length ((VCont (length s), length s) :: s).
  simpler.
Qed.

Lemma extendG_flip' : forall Gf s,
  (VCont (Gf + length s), Gf + length s) :: extendG Gf s
  = extendG Gf ((VCont (length s), length s) :: s).
  induction Gf; simpler;
    rewrite extendG_flip_rewr; match goal with
                                 | [ H : _ |- _ ] => rewrite H
                               end; simpler.
Qed.

Hint Rewrite plus_0_r : ltamer.

Lemma extendG_flip : forall Gf,
  extendG Gf ((VCont O, O) :: nil)
  = (VCont Gf, Gf) :: extendG Gf nil.
  intros; generalize (extendG_flip' Gf nil); simpler.
Qed.

Lemma make_funcs_equiv_rewr : forall f1 pr s (G : list (Closed.val * nat)),
  length s = length G
  -> (makeClosures pr (f1 :: s)) # (length G) = Some f1.
  Hint Resolve grab_extends makeClosures_extends.

  intros; match goal with [ H : _ |- _ ] => rewrite <- H end; eauto.
Qed.

Lemma make_funcs_equiv' : forall G pr1 pr2,
  prog_equiv G pr1 pr2
  -> forall s, length s = length G
    -> G = extendG (length G) nil
    -> funcs_equiv (length G) (makeClosures pr1 s) pr2.
  Hint Rewrite extendG_flip make_funcs_equiv_rewr using assumption : ltamer.

  Hint Extern 1 (_ = _) => simpl; congruence.

  induction 1; simpler;
    match goal with
      | [ H1 : _ = extendG _ _, H2 : forall F1 F2 v1 v2, exp_equiv _ _ _ |- _ ] => rewrite H1 in H2
    end; eauto.
Qed.

Lemma make_funcs_equiv : forall pr1 pr2,
  prog_equiv nil pr1 pr2
  -> funcs_equiv O (makeClosures pr1 nil) pr2.
  intros; generalize (@make_funcs_equiv' nil); eauto.
Qed.

Lemma makeClosures_prog_length : forall G pr1 pr2,
  prog_equiv G pr1 pr2
  -> forall s, length (makeClosures pr1 s) = prog_length (length s) pr2 + length s.
  induction 1; simpler;
    match goal with
      | [ H : _ |- _ ] => rewrite (H (VCont (length s)) (length s)); simpler
    end.
Qed.

Lemma Flatten_prog_length : forall G pr1 pr2,
  prog_equiv G pr1 pr2
  -> forall l e, (makeClosures pr1 nil) # l = Some e
    -> l < prog_length O pr2.
  intros; match goal with
            | [ H1 : _ = Some _, H2 : prog_equiv _ _ _ |- _ ] =>
              generalize (grab_oob' _ _ H1); rewrite (makeClosures_prog_length H2); simpler
          end.
Qed.

Lemma Flatten_n_slots' : forall pr2 Gf,
  p_nslots (flattenPr Gf pr2)
  = f_nslots (flattenE O (getBody2 Gf pr2) (funcEnv (prog_length Gf pr2 + Gf))).
  induction pr2; equation.
Qed.

Lemma Flatten_n_slots : forall pr2,
  length (filler (p_nslots (flattenPr O pr2)))
  >= f_nslots (flattenE O (getBody2 O pr2) (funcEnv (prog_length O pr2))).
  simpler; rewrite Flatten_n_slots'; simpler.
Qed.

Lemma Flatten_varOk : forall sls v n Gf,
  In (v, n) (extendG Gf nil)
  -> varOk sls (funcEnv Gf) v n.
  unfold varOk, lookup; call.
Qed.

Lemma Flatten_bound : forall Gf v n,
  In (v, n) (extendG Gf nil)
  -> n < length (funcEnv Gf).
  call.
Qed.

Lemma Flatten_slotOk : forall Gf v n,
  In (v, n) (extendG Gf nil)
  -> slotOk 0 (funcEnv Gf) n.
  unfold slotOk, lookup; call.
Qed.

Theorem FlattenProg_correct : forall P r1,
  Closed.EvalPr nil P r1
  -> Closed.Prog_wf P
  -> exists r2, Flat.evalPr (FlattenProg P) r2
    /\ compR r1 r2.
  Hint Rewrite flattenPr_body : ltamer.
  Hint Resolve flattenE_correct makeClosures_correct getBody_equiv.
  Hint Resolve make_funcs_equiv Flatten_prog_length Flatten_n_slots Flatten_varOk Flatten_bound Flatten_slotOk.

  unfold Closed.EvalPr, Closed.Prog_wf, FlattenProg, Flat.evalPr; simpler; eapply flattenE_correct; eauto.
Qed.
