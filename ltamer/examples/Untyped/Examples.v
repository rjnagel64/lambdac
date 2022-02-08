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

Require Import Source.
Require Import Core.
Require Import CPS.
Require Import Closed.
Require Import Flat.
Require Import Asm.

Require Import PHOASify.
Require Import CPSify.
Require Import CC.
Require Import CSE.
Require Import Flatten.
Require Import RegAlloc.
Require Import Codegen.
Require Import Compiler.

Require Import PHOASifyWf.
Require Import CPSifyWf.
Require Import CSEWf.

Set Implicit Arguments.


(** * Source programs *)

Section Source.
  Import Source.

  Definition eunit : exp O := Unit.

  Definition etrue : exp O := EInl Unit.

  Definition etrue_true : exp O := Pair etrue etrue.

  Definition eident : exp O := Abs (Var FO).

  Definition eident_app : exp O := App eident etrue.

  Definition efst : exp O := Abs (Abs (Var (FS FO))).
  Definition esnd : exp O := Abs (Abs (Var FO)).

  Definition efst_test : exp O := App (App efst etrue) eunit.
  Definition esnd_test : exp O := App (App esnd etrue) eunit.

  Definition ethrow : exp O := EThrow Unit.

  Definition ethrower : exp O := Abs (EThrow (Var FO)).

  Definition ethrower_app : exp O := App ethrower etrue.

  Definition echoosy : exp O := Abs (ECase (Var (FS FO)) (Var (FS FO)) (EThrow (Var (FS FO)))).

  Definition echoosy_normal : exp O := App echoosy (EInl Unit).
  Definition echoosy_ex : exp O := App echoosy (EInr Unit).

  Definition echoosy2 : exp O := Abs (ECase (Var (FS FO)) (ECase (Var FO) (Var FO) (EThrow (Var FO)))
    (ECase (Var FO) (EThrow (Var FO)) (Var FO))).

  Definition echoosy2_normal1 : exp O := App echoosy2 (EInl (EInl Unit)).
  Definition echoosy2_ex1 : exp O := App echoosy2 (EInl (EInr Unit)).
  Definition echoosy2_normal2 : exp O := App echoosy2 (EInr (EInr Unit)).
  Definition echoosy2_ex2 : exp O := App echoosy2 (EInr (EInl Unit)).

  Definition echoosy' : exp 2 := Abs (ECase (Var (FS FO)) (Var FO) (EThrow (Var FO))).
  Definition enew_read1 : exp O := App (Abs (App echoosy' (Read (Var (FS FO))))) (New (EInl Unit)).
  Definition enew_read2 : exp O := App (Abs (App echoosy' (Read (Var (FS FO))))) (New (EInr Unit)).

  Definition echoosy'' : exp 4 := Abs (ECase (Var (FS FO)) (Var FO) (EThrow (Var FO))).
  Definition enew_write_read1 : exp O := App (Abs (App (Abs (App echoosy'' (Read (Var (FS (FS (FS FO)))))))
    (Write (Var (FS FO)) (EInr Unit)))) (New (EInl Unit)).
  Definition enew_write_read2 : exp O := App (Abs (App (Abs (App echoosy'' (Read (Var (FS (FS (FS FO)))))))
    (Write (Var (FS FO)) (EInl Unit)))) (New (EInr Unit)).
End Source.

Definition normalS e := exists h, exists v, Source.eval nil e h (Source.Ans v).
Definition exS e := exists h, exists v, Source.eval nil e h (Source.Ex v).

Lemma SourceEvalNew' : forall v h2 h1 e l h2',
  Source.eval h1 e h2 (Source.Ans v)
  -> l = length h2
  -> h2' = v :: h2
  -> Source.eval h1 (Source.New e) h2' (Source.Ans (Source.VRef l)).
  simpler; econstructor; eauto.
Qed.

Lemma SourceEvalWrite' : forall h1 e1 h2 e2 r h3 v h3',
  Source.eval h1 e1 h2 (Source.Ans (Source.VRef r))
  -> Source.eval h2 e2 h3 (Source.Ans v)
  -> h3' = (h3 ## r <~ v)
  -> Source.eval h1 (Source.Write e1 e2) h3' (Source.Ans Source.VUnit).
  simpler; econstructor; eauto.
Qed.

Ltac s := lazy beta delta iota zeta; do 2 econstructor;
  repeat (lazy beta delta iota zeta;
    match goal with
      | [ |- Source.eval _ (Source.ECase (Value (Source.VInr _)) _ _) _ _ ] => eapply Source.EvalCaseR
      | _ => eapply SourceEvalNew' || eapply SourceEvalWrite' || econstructor
    end).

Theorem s_eunit : normalS eunit.
  s.
Qed.

Theorem s_etrue : normalS etrue.
  s.
Qed.

Theorem s_etrue_true : normalS etrue_true.
  s.
Qed.

Theorem s_eident : normalS eident.
  s.
Qed.

Theorem s_eident_app : normalS eident_app.
  s.
Qed.

Theorem s_efst : normalS efst.
  s.
Qed.

Theorem s_esnd : normalS esnd.
  s.
Qed.

Theorem s_efst_test : normalS efst_test.
  s.
Qed.

Theorem s_esnd_test : normalS esnd_test.
  s.
Qed.

Theorem s_ethrow : exS ethrow.
  s.
Qed.

Theorem s_ethrower : normalS ethrower.
  s.
Qed.

Theorem s_ethrower_app : exS ethrower_app.
  s.
Qed.

Theorem s_echoosy : normalS echoosy.
  s.
Qed.

Theorem s_echoosy_normal : normalS echoosy_normal.
  s.
Qed.

Theorem s_echoosy_ex : exS echoosy_ex.
  s.
Qed.

Theorem s_echoosy2 : normalS echoosy2.
  s.
Qed.

Theorem s_echoosy2_normal1 : normalS echoosy2_normal1.
  s.
Qed.

Theorem s_echoosy2_ex1 : exS echoosy2_ex1.
  s.
Qed.

Theorem s_echoosy2_normal2 : normalS echoosy2_normal2.
  s.
Qed.

Theorem s_echoosy2_ex2 : exS echoosy2_ex2.
  s.
Qed.

Theorem s_enew_read1 : normalS enew_read1.
  s.
Qed.

Theorem s_enew_read2 : exS enew_read2.
  s.
Qed.

Theorem s_enew_write_read1 : exS enew_write_read1.
  s.
Qed.

Theorem s_enew_write_read2 : normalS enew_write_read2.
  s.
Qed.


(** PHOASifications *)

Definition normalC e := exists s, exists h, exists v, Core.Eval nil nil (Phoasify e) s h (Core.Ans v).
Definition exC e := exists s, exists h, exists v, Core.Eval nil nil (Phoasify e) s h (Core.Ex v).

Lemma CoreEvalNew' : forall v h2 h1 e l h2' s1 s2,
  Core.eval s1 h1 e s2 h2 (Core.Ans v)
  -> l = length h2
  -> h2' = v :: h2
  -> Core.eval s1 h1 (Core.New e) s2 h2' (Core.Ans (Core.VRef l)).
  simpler; econstructor; eauto.
Qed.

Lemma CoreEvalWrite' : forall h1 e1 h2 e2 r h3 v h3' s1 s2 s3,
  Core.eval s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
  -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v)
  -> h3' = (h3 ## r <~ v)
  -> Core.eval s1 h1 (Core.Write e1 e2) s3 h3' (Core.Ans Core.VUnit).
  simpler; econstructor; eauto.
Qed.

Ltac c := lazy beta delta iota zeta; do 2 econstructor;
  repeat (lazy beta delta iota zeta;
    match goal with
      | [ |- Core.eval _ _ (Core.ECase (Core.Var (Core.VInr _)) _ _) _ _ _ ] => eapply Core.EvalCaseR
      | _ => eapply CoreEvalNew' || eapply CoreEvalWrite' || econstructor
    end).

Theorem c_eunit : normalC eunit.
  c.
Qed.

Theorem c_etrue : normalC etrue.
  c.
Qed.

Theorem c_etrue_true : normalC etrue_true.
  c.
Qed.

Theorem c_eident : normalC eident.
  c.
Qed.

Theorem c_eident_app : normalC eident_app.
  c.
Qed.

Theorem c_efst : normalC efst.
  c.
Qed.

Theorem c_esnd : normalC esnd.
  c.
Qed.

Theorem c_efst_test : normalC efst_test.
  c.
Qed.

Theorem c_esnd_test : normalC esnd_test.
  c.
Qed.

Theorem c_ethrow : exC ethrow.
  c.
Qed.

Theorem c_ethrower : normalC ethrower.
  c.
Qed.

Theorem c_ethrower_app : exC ethrower_app.
  c.
Qed.

Theorem c_echoosy : normalC echoosy.
  c.
Qed.

Theorem c_echoosy_normal : normalC echoosy_normal.
  c.
Qed.

Theorem c_echoosy_ex : exC echoosy_ex.
  c.
Qed.

Theorem c_echoosy2 : normalC echoosy2.
  c.
Qed.

Theorem c_echoosy2_normal1 : normalC echoosy2_normal1.
  c.
Qed.

Theorem c_echoosy2_ex1 : exC echoosy2_ex1.
  c.
Qed.

Theorem c_echoosy2_normal2 : normalC echoosy2_normal2.
  c.
Qed.

Theorem c_echoosy2_ex2 : exC echoosy2_ex2.
  c.
Qed.

Theorem c_enew_read1 : normalC enew_read1.
  c.
Qed.

Theorem c_enew_read2 : exC enew_read2.
  c.
Qed.

Theorem c_enew_write_read1 : exC enew_write_read1.
  c.
Qed.

Theorem c_enew_write_read2 : normalC enew_write_read2.
  c.
Qed.


(** * CPS translations *)

Definition normalCPS e := exists v, CPS.Eval nil nil (CpsExp (Phoasify e)) (CPS.Ans v).
Definition exCPS e := exists v, CPS.Eval nil nil (CpsExp (Phoasify e)) (CPS.Ex v).

Ltac cps := lazy beta delta iota zeta;
  repeat (simpl; unfold cpsFunc'; econstructor).

Theorem cps_eunit : normalCPS eunit.
  cps.
Qed.

Theorem cps_etrue : normalCPS etrue.
  cps.
Qed.

Theorem cps_etrue_true : normalCPS etrue_true.
  cps.
Qed.

Theorem cps_eident : normalCPS eident.
  cps.
Qed.

Theorem cps_eident_app : normalCPS eident_app.
  cps.
Qed.

Theorem cps_efst : normalCPS efst.
  cps.
Qed.

Theorem cps_esnd : normalCPS esnd.
  cps.
Qed.

Theorem cps_efst_test : normalCPS efst_test.
  cps.
Qed.

Theorem cps_esnd_test : normalCPS esnd_test.
  cps.
Qed.

Theorem cps_ethrow : exCPS ethrow.
  cps.
Qed.

Theorem cps_ethrower : normalCPS ethrower.
  cps.
Qed.

Theorem cps_ethrower_app : exCPS ethrower_app.
  cps.
Qed.

Theorem cps_echoosy : normalCPS echoosy.
  cps.
Qed.

Theorem cps_echoosy_normal : normalCPS echoosy_normal.
  cps.
Qed.

Theorem cps_echoosy_ex : exCPS echoosy_ex.
  cps.
Qed.

Theorem cps_echoosy2 : normalCPS echoosy2.
  cps.
Qed.

Theorem cps_echoosy2_normal1 : normalCPS echoosy2_normal1.
  cps.
Qed.

Theorem cps_echoosy2_ex1 : exCPS echoosy2_ex1.
  cps.
Qed.

Theorem cps_echoosy2_normal2 : normalCPS echoosy2_normal2.
  cps.
Qed.

Theorem cps_echoosy2_ex2 : exCPS echoosy2_ex2.
  cps.
Qed.

Theorem cps_enew_read1 : normalCPS enew_read1.
  cps.
Qed.

Theorem cps_enew_read2 : exCPS enew_read2.
  cps.
Qed.

Theorem cps_enew_write_read1 : exCPS enew_write_read1.
  cps.
Qed.

Theorem cps_enew_write_read2 : normalCPS enew_write_read2.
  cps.
Qed.


(** * Closure conversions *)

Definition normalCC e := exists v, Closed.EvalPr nil (CcProg (CpsExp_wf (Phoasify_wf e))) (Closed.Ans v).
Definition exCC e := exists v, Closed.EvalPr nil (CcProg (CpsExp_wf (Phoasify_wf e))) (Closed.Ex v).

Ltac cc := lazy beta delta iota zeta;
  repeat (simpl; unfold cpsFunc'; econstructor).

Theorem cc_eunit : normalCC eunit.
  cc.
Qed.

Theorem cc_etrue : normalCC etrue.
  cc.
Qed.

Theorem cc_etrue_true : normalCC etrue_true.
  cc.
Qed.

Theorem cc_eident : normalCC eident.
  cc.
Qed.

Theorem cc_eident_app : normalCC eident_app.
  cc.
Qed.

Theorem cc_efst : normalCC efst.
  cc.
Qed.

Theorem cc_esnd : normalCC esnd.
  cc.
Qed.

Theorem cc_efst_test : normalCC efst_test.
  cc.
Qed.

Theorem cc_esnd_test : normalCC esnd_test.
  cc.
Qed.

Theorem cc_ethrow : exCC ethrow.
  cc.
Qed.

Theorem cc_ethrower : normalCC ethrower.
  cc.
Qed.

Theorem cc_ethrower_app : exCC ethrower_app.
  cc.
Qed.

Theorem cc_echoosy : normalCC echoosy.
  cc.
Qed.

Theorem cc_echoosy_normal : normalCC echoosy_normal.
  cc.
Qed.

Theorem cc_echoosy_ex : exCC echoosy_ex.
  cc.
Qed.

Theorem cc_echoosy2 : normalCC echoosy2.
  cc.
Qed.

Theorem cc_echoosy2_normal1 : normalCC echoosy2_normal1.
  cc.
Qed.

Theorem cc_echoosy2_ex1 : exCC echoosy2_ex1.
  cc.
Qed.

Theorem cc_echoosy2_normal2 : normalCC echoosy2_normal2.
  cc.
Qed.

Theorem cc_echoosy2_ex2 : exCC echoosy2_ex2.
  cc.
Qed.

Theorem cc_enew_read1 : normalCC enew_read1.
  cc.
Qed.

Theorem cc_enew_read2 : exCC enew_read2.
  cc.
Qed.

Theorem cc_enew_write_read1 : exCC enew_write_read1.
  cc.
Qed.

Theorem cc_enew_write_read2 : normalCC enew_write_read2.
  cc.
Qed.


(** Flattenings *)

Definition normalF e := exists v, Flat.evalPr (FlattenProg (CcProg (CpsExp_wf (Phoasify_wf e)))) (Flat.Ans v).
Definition exF e := exists v, Flat.evalPr (FlattenProg (CcProg (CpsExp_wf (Phoasify_wf e)))) (Flat.Ex v).

Ltac f := repeat (lazy delta beta iota zeta;
  match goal with
    | [ |- Flat.eval _ _ ?sls (Flat.ECase ?x _ _ _ _) _ ] =>
      match eval lazy delta beta iota zeta in (Flat.get sls x) with
        | Some (Flat.VInl _) => eapply Flat.EvalCaseL
        | Some (Flat.VInr _) => eapply Flat.EvalCaseR
      end
      | _ => econstructor
  end).

Theorem f_eunit : normalF eunit.
  f.
Qed.

Theorem f_etrue : normalF etrue.
  f.
Qed.

Theorem f_etrue_true : normalF etrue_true.
  f.
Qed.

Theorem f_eident : normalF eident.
  f.
Qed.

Theorem f_eident_app : normalF eident_app.
  f.
Qed.

Theorem f_efst : normalF efst.
  f.
Qed.

Theorem f_esnd : normalF esnd.
  f.
Qed.

Theorem f_efst_test : normalF efst_test.
  f.
Qed.

Theorem f_esnd_test : normalF esnd_test.
  f.
Qed.

Theorem f_ethrow : exF ethrow.
  f.
Qed.

Theorem f_ethrower : normalF ethrower.
  f.
Qed.

Theorem f_ethrower_app : exF ethrower_app.
  f.
Qed.

Theorem f_echoosy : normalF echoosy.
  f.
Qed.

Theorem f_echoosy_normal : normalF echoosy_normal.
  f.
Qed.

Theorem f_echoosy_ex : exF echoosy_ex.
  f.
Qed.

Theorem f_echoosy2 : normalF echoosy2.
  f.
Qed.

Theorem f_echoosy2_normal1 : normalF echoosy2_normal1.
  f.
Qed.

Theorem f_echoosy2_ex1 : exF echoosy2_ex1.
  f.
Qed.

Theorem f_echoosy2_normal2 : normalF echoosy2_normal2.
  f.
Qed.

Theorem f_echoosy2_ex2 : exF echoosy2_ex2.
  f.
Qed.

Theorem f_enew_read1 : normalF enew_read1.
  f.
Qed.

Theorem f_enew_read2 : exF enew_read2.
  f.
Qed.

Theorem f_enew_write_read1 : exF enew_write_read1.
  f.
Qed.

Theorem f_enew_write_read2 : normalF enew_write_read2.
  f.
Qed.


(** Generated code *)

Definition n_regs := 3.
Definition normalA e := exists h2, exists v, Asm.evalPr (Compile n_regs e) h2 (Asm.Ans v).
Definition exA e := exists h2, exists v, Asm.evalPr (Compile n_regs e) h2 (Asm.Ex v).

Ltac a := lazy delta beta iota zeta; do 2 econstructor;
  repeat (match goal with
            | [ |- evalB _ ?rs ?h (?is, _) _ _ ] =>
              match eval lazy beta delta iota zeta in (evalIs rs h is) with
                | (_, _, Some _) => eapply EvalJnz
                | _ => econstructor
              end
          end; (lazy beta delta iota zeta; try reflexivity)).

Theorem a_etrue : normalA etrue.
  a.
Qed.

Theorem a_etrue_true : normalA etrue_true.
  a.
Qed.

Theorem a_eident : normalA eident.
  a.
Qed.

Theorem a_eident_app : normalA eident_app.
  a.
Qed.

Theorem a_efst : normalA efst.
  a.
Qed.

Theorem a_esnd : normalA esnd.
  a.
Qed.

Theorem a_efst_test : normalA efst_test.
  a.
Qed.

Theorem a_esnd_test : normalA esnd_test.
  a.
Qed.

Theorem a_ethrow : exA ethrow.
  a.
Qed.

Theorem a_ethrower : normalA ethrower.
  a.
Qed.

Theorem a_ethrower_app : exA ethrower_app.
  a.
Qed.

Theorem a_echoosy : normalA echoosy.
  a.
Qed.

Theorem a_echoosy_normal : normalA echoosy_normal.
  a.
Qed.

Theorem a_echoosy_ex : exA echoosy_ex.
  a.
Qed.

Theorem a_echoosy2 : normalA echoosy2.
  a.
Qed.

Theorem a_echoosy2_normal1 : normalA echoosy2_normal1.
  a.
Qed.

Theorem a_echoosy2_ex1 : exA echoosy2_ex1.
  a.
Qed.

Theorem a_echoosy2_normal2 : normalA echoosy2_normal2.
  a.
Qed.

Theorem a_echoosy2_ex2 : exA echoosy2_ex2.
  a.
Qed.

Theorem a_enew_read1 : normalA enew_read1.
  a.
Qed.

Theorem a_enew_read2 : exA enew_read2.
  a.
Qed.

Theorem a_enew_write_read1 : exA enew_write_read1.
  a.
Qed.

Theorem a_enew_write_read2 : normalA enew_write_read2.
  a.
Qed.
