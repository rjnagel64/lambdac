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

Require Import List.

Require Import LambdaTamer.

Require Import Base.

Require Import Source.
Require Import Asm.

Require Import Compiler.

Require Import PHOASify.
Require Import CPSify.
Require Import CC.
Require Import CSE.
Require Import Flatten.
Require Import RegAlloc.
Require Import Codegen.

Require Import PHOASifyCorrect.
Require Import CPSifyCorrect.
Require Import CCCorrect.
Require Import CSECorrect.
Require Import FlattenCorrect.
Require Import RegAllocCorrect.
Require Import CodegenCorrect.

Require Import PHOASifyWf.
Require Import CPSifyWf.
Require Import CCWf.
Require Import CSEWf.


Section comp.
  Variable h : Asm.heap.

  Inductive comp : Source.val -> nat -> Prop :=
  | CompFunc : forall l v,
    comp (Source.VFunc l) v

  | CompUnit : forall n,
    comp Source.VUnit n

  | CompPair : forall x y a,
    comp x (sel h a)
    -> comp y (sel h (S a))
    -> comp (Source.VPair x y) a

  | CompInl : forall v a,
    sel h a = 0
    -> comp v (sel h (S a))
    -> comp (Source.VInl v) a
  | CompInr : forall v a,
    sel h a = 1
    -> comp v (sel h (S a))
    -> comp (Source.VInr v) a

  | CompRef : forall l v,
    comp (Source.VRef l) v

  | CompBase : forall b,
    comp (Source.VBase b) (encode b).

  Inductive compR : Source.result -> Asm.result -> Prop :=
  | CompAns : forall v1 v2,
    comp v1 v2
    -> compR (Source.Ans v1) (Asm.Ans v2)
  | CompEx : forall v1 v2,
    comp v1 v2
    -> compR (Source.Ex v1) (Asm.Ex v2).
End comp.

Hint Constructors comp compR.

Lemma comp_trans : forall v1 v2,
  PHOASifyCorrect.comp v1 v2
  -> forall h v3 v4 v5 v6, CPSifyCorrect.comp v2 v3
  -> CCCorrect.comp v3 v4
  -> FlattenCorrect.comp v4 v5
  -> CodegenCorrect.comp h v5 v6
  -> comp h v1 v6.
  induction 1; auto; do 4 (inversion 1; subst); eauto.
Qed.

Hint Resolve comp_trans.

Lemma compR_trans : forall h v1 v2 v3 v4 v5 v6,
  PHOASifyCorrect.compR v1 v2
  -> CPSifyCorrect.compR v2 v3
  -> CCCorrect.compR v3 v4
  -> FlattenCorrect.compR v4 v5
  -> CodegenCorrect.compR h v5 v6
  -> compR h v1 v6.
  destruct 1; do 4 (inversion 1; subst); eauto.
Qed.

Hint Resolve compR_trans.

Theorem compile_correct : forall n_regs e h r1,
  Source.eval nil e h r1
  -> isSource e
  -> exists h, exists r2, Asm.evalPr (Compile n_regs e) h r2
    /\ compR h r1 r2.
  Hint Resolve Phoasify_wf CpsExp_wf CcProg_wf CseProg_wf.

  Ltac g vs e := guessWithKeep vs e; simpler.

  unfold Compile; intros;
    g tt Phoasify_correct; g tt CpsExp_correct;
    g (CpsExp (Phoasify e), CpsExp_wf (Phoasify_wf e)) CcProg_correct;
    g tt CseProg_correct; g tt FlattenProg_correct; g tt allocProg_correct;
    g n_regs genProg_correct; simpler; eauto.
Qed.
