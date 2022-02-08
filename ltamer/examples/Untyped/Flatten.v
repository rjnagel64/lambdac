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

Set Implicit Arguments.


Definition lookup (env : list var) (n : nat) : var :=
  match env # n with
    | None => Slot O
    | Some v => v
  end.

Fixpoint flattenP (p : Closed.primop nat) (env : list var) {struct p} : Flat.primop :=
  match p with
    | Closed.Unit => Unit

    | Closed.Pair x y => Pair (lookup env x) (lookup env y)
    | Closed.EFst x => EFst (lookup env x)
    | Closed.ESnd x => ESnd (lookup env x)

    | Closed.EInl x => EInl (lookup env x)
    | Closed.EInr x => EInr (lookup env x)

    | Closed.New x => New (lookup env x)
    | Closed.Read x => Read (lookup env x)
    | Closed.Write x y => Write (lookup env x) (lookup env y)

    | Closed.Const b => Const b
    | Closed.Eq x y => Eq (lookup env x) (lookup env y)
  end.

Fixpoint flattenE Gbase (e : Closed.exp nat) (env : list var) {struct e} : func :=
  match e with
    | Closed.EHalt x => Func Gbase (EHalt (lookup env x))
    | Closed.Call f x =>
      Func Gbase (Call (lookup env f) (lookup env x))
    | Closed.Bind p e' =>
      let er := flattenE (S Gbase) (e' (length env)) (Slot Gbase :: env) in
        Func (f_nslots er)
        (Assign Gbase
          (flattenP p env)
          (f_body er))
    | Closed.ECase x e1 e2 =>
      let er1 := flattenE (S Gbase) (e1 (length env)) (Slot Gbase :: env) in
      let er2 := flattenE (S (f_nslots er1)) (e2 (length env)) (Slot (f_nslots er1) :: env) in
        Func (f_nslots er2)
        (ECase (lookup env x)
          Gbase
          (f_body er1)
          (f_nslots er1)
          (f_body er2))

    | Closed.EUncaught x => Func Gbase (EUncaught (lookup env x))
  end.

Fixpoint funcEnv (Gf : nat) : list var :=
  match Gf with
    | O => nil
    | S Gf' => FuncVar Gf' :: funcEnv Gf'
  end.

Fixpoint flattenPr Gf (pr : Closed.prog nat) {struct pr} : Flat.prog :=
  match pr with
    | EBody e =>
      let er := flattenE O e (funcEnv Gf) in
        Prog nil (f_nslots er) (f_body er)
    | Abs e pr' =>
      let er := flattenE 2 (e (S Gf) Gf) (Slot 1 :: Slot O :: funcEnv Gf) in
      let p := flattenPr (S Gf) (pr' Gf) in
      Prog (p_funcs p ++ er :: nil)
      (p_nslots p) (p_body p)
  end.

Definition FlattenProg (P : Closed.Prog) : Flat.prog := flattenPr O (P _).
