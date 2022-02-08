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

Require Import Core.
Require Import CPS.
Require Import Result.

Require Import CPSifySpec.

Set Implicit Arguments.


Definition comp := Compilation
  (fun G e1 k ke e2 =>
    exists F1, exists F2, exists x1, exists x2, exists kx,
      G = (x1, x2) :: (F1, F2) :: nil
      /\ e1 = (#x1)%core
      /\ e2 = (kx @@@ x2)%cps
      /\ k = (fun x => kx @@@ x)%cps)
  (fun G f1 f2 =>
    G = nil
    /\ f1 = (fun _ x => #x)%core
    /\ f2 = (fun _ p => x <- Fst p; p' <- Snd p; k <- Fst p'; k @@@ x))%cps.

Module Self : COMPILATION with Definition self := comp.
  Definition self := comp.

  Lemma selfOk : compilationOk self.
    red; simpler; eauto 12 with cps_eval.
  Qed.

  Hint Resolve answer_Ans.

  Theorem VarCase : forall full, self [= full
    -> compilationOk full
    -> forall s h v, spec full self s h (#v) s h (Core.Ans v).
    unfold spec; simpler;
      match goal with
        | [ H : (#_) = (#_) |- _ ] => injection H; intros; subst
      end; eauto 11 with cps_eval.
  Qed.

  Ltac t := unfold spec; simpler.

  Theorem AppCase : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 l f0 s3 h3 v1 s4 h4 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> s2 # l = Some f0
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v1)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v1)
      -> Core.eval s3 h3 (f0 (VFunc l) v1) s4 h4 v2
      -> spec full full s3 h3 (f0 (VFunc l) v1) s4 h4 v2
      -> spec full self s1 h1 (e1 @ e2) s4 h4 v2.
    t.
  Qed.

  Theorem AppEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (e1 @ e2) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem AppEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall e1 e2 s1 h1 s2 h2 l s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (VFunc l))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full self s1 h1 (e1 @ e2) s3 h3 (Core.Ex v).
    t.
  Qed.

  Theorem AbsCase : forall full, self [= full
    -> compilationOk full
    -> forall s h e1,
      spec full self s h (Core.Abs e1) (e1 :: s) h (Core.Ans (VFunc (length s))).
    t.
  Qed.

  Theorem LetCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v s3 h3 e2 r,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (ELet e1 e2) s3 h3 r.
    t.
  Qed.

  Theorem LetExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (ELet e1 e2) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem PairCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v1)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v1)
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v2)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v2)
      -> spec full self s1 h1 [<e1, e2>] s3 h3 (Core.Ans (Core.VPair v1 v2)).
    t.
  Qed.

  Theorem PairEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 [<e1, e2>] s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem PairEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v1 e2 s3 h3 v2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v1)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v1)
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v2)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v2)
      -> spec full self s1 h1 [<e1, e2>] s3 h3 (Core.Ex v2).
    t.
  Qed.

  Theorem UnitCase : forall full, self [= full
    -> compilationOk full
    -> forall s h,
      spec full self s h () s h (Core.Ans Core.VUnit).
    t.
  Qed.

  Theorem FstCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v1 v2,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full self s1 h1 (Fst e) s2 h2 (Core.Ans v1).
    t.
  Qed.

  Theorem FstExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Fst e) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem SndCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v1 v2,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VPair v1 v2))
      -> spec full self s1 h1 (Snd e) s2 h2 (Core.Ans v2).
    t.
  Qed.

  Theorem SndExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Snd e) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem InlCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Inl e) s2 h2 (Core.Ans (Core.VInl v)).
    t.
  Qed.

  Theorem InlExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Inl e) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem InrCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Inr e) s2 h2 (Core.Ans (Core.VInr v)).
    t.
  Qed.

  Theorem InrExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Inr e) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem CaseLCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VInl v))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VInl v))
      -> Core.eval s2 h2 (e1 v) s3 h3 r
      -> spec full full s2 h2 (e1 v) s3 h3 r
      -> spec full self s1 h1 (Core.ECase e e1 e2) s3 h3 r.
    t.
  Qed.

  Theorem CaseRCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v s3 h3 r,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VInr v))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VInr v))
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (Core.ECase e e1 e2) s3 h3 r.
    t.
  Qed.

  Theorem CaseExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e e1 e2 s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Core.ECase e e1 e2) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem NewCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Ref e) s2 (v :: h2) (Core.Ans (Core.VRef (length h2))).
    t.
  Qed.

  Theorem NewExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Ref e) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem ReadCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 r v,
      Core.eval s1 h1 e s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e s2 h2 (Core.Ans (Core.VRef r))
      -> h2 # r = Some v
      -> spec full self s1 h1 (!e) s2 h2 (Core.Ans v).
    t.
  Qed.

  Theorem ReadExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e s2 h2 v,
      Core.eval s1 h1 e s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (!e) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem WriteCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ans v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ans v)
      -> spec full self s1 h1 (e1 ::= e2) s3 h3 ## r <~ v (Core.Ans Core.VUnit).
    t.
  Qed.

  Theorem WriteEx1Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (e1 ::= e2) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem WriteEx2Case : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 e2 r s3 h3 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans (Core.VRef r))
      -> Core.eval s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full full s2 h2 e2 s3 h3 (Core.Ex v)
      -> spec full self s1 h1 (e1 ::= e2) s3 h3 (Core.Ex v).
    t.
  Qed.

  Theorem ThrowCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (Throw e1) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem ThrowExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full self s1 h1 (Throw e1) s2 h2 (Core.Ex v).
    t.
  Qed.

  Theorem CatchCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2,
      Core.eval s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ans v)
      -> spec full self s1 h1 (ECatch e1 e2) s2 h2 (Core.Ans v).
    t.
  Qed.

  Theorem CatchExCase : forall full, self [= full
    -> compilationOk full
    -> forall s1 h1 e1 s2 h2 v e2 s3 h3 r,
      Core.eval s1 h1 e1 s2 h2 (Core.Ex v)
      -> spec full full s1 h1 e1 s2 h2 (Core.Ex v)
      -> Core.eval s2 h2 (e2 v) s3 h3 r
      -> spec full full s2 h2 (e2 v) s3 h3 r
      -> spec full self s1 h1 (ECatch e1 e2) s3 h3 r.
    t.
  Qed.
End Self.
