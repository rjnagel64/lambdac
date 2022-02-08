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

Require Import Base.

Require Import Closed.

Set Implicit Arguments.

Open Local Scope closed_scope.


Inductive sval : Type :=
| SVar : nat -> sval
| SUnit : sval
| SPair : sval -> sval -> sval
| SInl : sval -> sval
| SInr : sval -> sval
| SBase : base -> sval.


Definition csePrimop var (p : primop (var * sval)) : primop var * option sval :=
  match p with
    | Unit => ((), Some SUnit)

    | Pair x1 x2 => ([<fst x1, fst x2>], Some (SPair (snd x1) (snd x2)))
    | EFst x =>
      (Fst (fst x),
        match snd x with
          | SPair sv _ => Some sv
          | _ => None
        end)
    | ESnd x =>
      (Snd (fst x),
        match snd x with
          | SPair _ sv => Some sv
          | _ => None
        end)

    | EInl x => (Inl (fst x), Some (SInl (snd x)))
    | EInr x => (Inr (fst x), Some (SInr (snd x)))

    | New x => (Ref (fst x), None)
    | Read x => (!(fst x), None)
    | Write x1 x2 => (fst x1 ::= fst x2, None)

    | Const b => (^^b, Some (SBase b))
    | Eq x1 x2 => (Eq (fst x1) (fst x2), None)
  end.

Definition sval_eq_dec : forall sv1 sv2 : sval, {sv1 = sv2} + {sv1 <> sv2}.
  decide equality; apply eq_nat_dec || apply base_eq_dec.
Defined.

Fixpoint lookup var (sv : sval) (xs : list (var * sval)) {struct xs} : option var :=
  match xs with
    | nil => None
    | (x, sv') :: xs' =>
      if sval_eq_dec sv' sv
        then Some x
        else lookup sv xs'
  end.

Fixpoint cseExp var (e : exp (var * sval)) (xs : list (var * sval)) {struct e} : exp var :=
  match e with
    | EHalt x => Halt (fst x)
    | EUncaught x => Uncaught (fst x)

    | Call f x => fst f @@@ fst x

    | Bind p e' =>
      let (p', svo) := csePrimop p in
        match svo with
          | None => x <- p'; let x' := (x, SVar (length xs)) in cseExp (e' x') (x' :: xs)
          | Some sv => match lookup sv xs with
                         | None => x <- p'; let x' := (x, sv) in cseExp (e' x') (x' :: xs)
                         | Some x' => cseExp (e' (x', sv)) xs
                       end
        end

    | ECase x e1 e2 =>
      let default := Case fst x Of
                       y => let y' := (y, SVar (length xs)) in cseExp (e1 y') (y' :: xs)
                     | y => let y' := (y, SVar (length xs)) in cseExp (e2 y') (y' :: xs) in
        match snd x with
          | SInl sv => match lookup sv xs with
                         | None => default
                         | Some x' => cseExp (e1 (x', sv)) xs
                       end
          | SInr sv => match lookup sv xs with
                         | None => default
                         | Some x' => cseExp (e2 (x', sv)) xs
                       end
          | _ => default
        end
  end.

Fixpoint cseProg var (pr : prog (var * sval)) (xs : list (var * sval)) {struct pr} : prog var :=
  match pr with
    | Abs e pr' => f <== \\F, x, let x' := (x, SVar (length xs)) in
      let F' := (F, SVar (S (length xs))) in
        cseExp (e F' x') (F' :: x' :: xs);
      let f' := (f, SVar (length xs)) in cseProg (pr' f') (f' :: xs)
    | EBody e => Body (cseExp e xs)
  end.

Definition CseProg (Pr : Prog) : Prog := fun _ => cseProg (Pr _) nil.
