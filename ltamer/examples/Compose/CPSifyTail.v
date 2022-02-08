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

Set Implicit Arguments.


Reserved Notation "x <-- ke -- e1 ; e2" (right associativity, at level 80, e1 at next level).

Section cpsExp.
  Variable var : Type.

  Import Core.
  Open Scope cps_scope.

  Inductive cont : Type :=
  | CVar : var -> cont
  | CFunc : (var -> CPS.exp var) -> cont.

  Definition apply (c : cont) (x : var) : CPS.exp var :=
    match c with
      | CVar f => f @@@ x
      | CFunc f => f x
    end.

  Infix "@!" := apply (no associativity, at level 79).

  Definition bind (c : cont) (b : var -> CPS.exp var) : CPS.exp var :=
    match c with
      | CVar f => b f
      | CFunc f => Bind (\_, x, f x) b
  end.

  Definition cpsFunc' (cpsExp : Core.exp var -> cont -> cont -> CPS.exp var)
    (e' : var -> var -> Core.exp var) :=
    fun F p : var =>
      x <- Fst p;
      p' <- Snd p;
      k <- Fst p';
      ke <- Snd p';
      cpsExp (e' F x) (CVar k) (CVar ke).

  Fixpoint cpsExp (e : Core.exp var)
    : cont -> cont -> CPS.exp var :=
    match e with
      | Var x => fun k _ => k @! x

      | App e1 e2 => fun k ke =>
        f <-- ke -- e1;
        x <-- ke -- e2;
        bind k (fun k' =>
          bind ke (fun ke' =>
            p' <- [< k', ke' >];
            p <- [< x, p' >];
            f @@@ p))
      | Abs e' => fun k _ => Bind (CPS.Abs (cpsFunc' cpsExp e')) (apply k)

      | ELet e1 e2 => fun k ke =>
        x <-- ke -- e1;
        cpsExp (e2 x) k ke

      | Unit => fun k _ =>
        x <- ();
        k @! x

      | Pair e1 e2 => fun k ke =>
        x <-- ke -- e1;
        y <-- ke -- e2;
        p <- [< x, y>];
        k @! p
      | EFst e => fun k ke =>
        x <-- ke -- e;
        y <- Fst x;
        k @! y
      | ESnd e => fun k ke =>
        x <-- ke -- e;
        y <- Snd x;
        k @! y

      | EInl e => fun k ke =>
        x <-- ke -- e;
        y <- Inl x;
        k @! y
      | EInr e => fun k ke =>
        x <-- ke -- e;
        y <- Inr x;
        k @! y
      | ECase e e1 e2 => fun k ke => 
        x <-- ke -- e;
        Case x Of
          x => cpsExp (e1 x) k ke
        | y => cpsExp (e2 y) k ke        

      | New e => fun k ke =>
        x <-- ke -- e;
        y <- Ref x;
        k @! y
      | Read e => fun k ke =>
        x <-- ke -- e;
        y <- !x;
        k @! y
      | Write e1 e2 => fun k ke =>
        r <-- ke -- e1;
        x <-- ke -- e2;
        u <- r ::= x;
        k @! u

      | EThrow e1 => fun k ke =>
        x <-- ke -- e1;
        ke @! x
      | ECatch e1 e2 => fun k ke =>
        cpsExp e1 k (CFunc (fun x => cpsExp (e2 x) k ke))
    end

    where "x <-- ke -- e1 ; e2" := (cpsExp e1 (CFunc (fun x => e2)) ke) : cps_scope.

  Definition cpsFunc := cpsFunc' cpsExp.
End cpsExp.

Infix "@!" := apply (no associativity, at level 79).

Definition CpsExp (E : Core.Exp) : CPS.Exp := fun _ => cpsExp (E _)
  (CFunc (fun _ => EHalt)) (CFunc (fun _ => EUncaught)).
