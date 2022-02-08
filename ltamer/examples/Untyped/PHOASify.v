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
Require Import Source.

Set Implicit Arguments.

Open Local Scope core_scope.


Fixpoint phoasify var n (e : Source.exp n) {struct e} : ilist var n -> Core.exp var :=
  match e in Source.exp n return ilist var n -> _ with
    | Var _ f => fun il => #(iget il f)

    | App _ e1 e2 => fun il => phoasify e1 il @ phoasify e2 il
    | Abs _ e1 => fun il => \\F,x, phoasify e1 (F ::: x ::: il)

    | ELet _ e1 e2 => fun il => Let x := phoasify e1 il in phoasify e2 (x ::: il)

    | Unit _ => fun _ => ()

    | Pair _ e1 e2 => fun il => [<phoasify e1 il, phoasify e2 il>]
    | EFst _ e1 => fun il => Fst (phoasify e1 il)
    | ESnd _ e1 => fun il => Snd (phoasify e1 il)

    | EInl _ e1 => fun il => Inl (phoasify e1 il)
    | EInr _ e1 => fun il => Inr (phoasify e1 il)
    | ECase _ e1 e2 e3 => fun il => Case phoasify e1 il Of x => phoasify e2 (x ::: il) | y => phoasify e3 (y ::: il)

    | New _ e1 => fun il => Ref (phoasify e1 il)
    | Read _ e1 => fun il => !(phoasify e1 il)
    | Write _ e1 e2 => fun il => phoasify e1 il ::= phoasify e2 il

    | EThrow _ e1 => fun il => Throw (phoasify e1 il)
    | ECatch _ e1 e2 => fun il => phoasify e1 il Catch x => phoasify e2 (x ::: il)

    | Const _ b => fun _ => ^^b
    | Eq _ e1 e2 => fun il => phoasify e1 il == phoasify e2 il

    | Value _ _ => fun _ => ()
  end.

Definition Phoasify (e : Source.exp O) : Core.Exp := fun _ => phoasify e INil.
