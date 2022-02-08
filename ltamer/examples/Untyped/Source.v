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

Require Import Base.

Set Implicit Arguments.


Inductive exp : nat -> Type :=
| Var : forall n, fin n -> exp n

| App : forall n, exp n -> exp n -> exp n
| Abs : forall n, exp (S (S n)) -> exp n

| ELet : forall n, exp n -> exp (S n) -> exp n 

| Unit : forall n, exp n

| Pair : forall n, exp n -> exp n -> exp n
| EFst : forall n, exp n -> exp n
| ESnd : forall n, exp n -> exp n
  
| EInl : forall n, exp n -> exp n
| EInr : forall n, exp n -> exp n
| ECase : forall n, exp n -> exp (S n) -> exp (S n) -> exp n

| New : forall n, exp n -> exp n
| Read : forall n, exp n -> exp n
| Write : forall n, exp n -> exp n -> exp n

| EThrow : forall n, exp n -> exp n
| ECatch : forall n, exp n -> exp (S n) -> exp n

| Const : forall n, base -> exp n
| Eq : forall n, exp n -> exp n -> exp n

| Value : forall n, val -> exp n

with val : Type :=
| VFunc : exp 2 -> val
| VUnit : val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VRef : label -> val
| VBase : base -> val.

Implicit Arguments Unit [n].
Implicit Arguments Const [n].
Implicit Arguments Value [n].

Definition heap := list val.

Inductive result : Type :=
| Ans : val -> result
| Ex : val -> result.

Definition not_zero' n (f : fin n) : fin (S (pred n)) -> fin n :=
  match f in fin n return fin (S (pred n)) -> fin n with
    | FO _ => fun e => e
    | FS _ _ => fun e => e
  end.

Fixpoint substVar n (x : fin n) {struct x} : fin n -> option (fin (pred n)) :=
  match x in fin n return fin n -> option (fin (pred n)) with
    | FO _ => fun y =>
      match y in fin n' return option (fin (pred n')) with
        | FO _ => None
        | FS _ f' => Some f'
      end
    | FS _ x' => fun y =>
      match y in fin n' return fin (pred n') -> (fin (pred n') -> option (fin (pred (pred n'))))
        -> option (fin (pred n')) with
        | FO _ => fun x' _ => Some (not_zero' x' FO)
        | FS _ y' => fun _ fx' => match fx' y' with
                                    | None => None
                                    | Some f =>
                                      match y' in fin n1 return fin (pred n1) -> option (fin n1) with
                                        | FO _ => fun f => Some (FS f)
                                        | FS _ _ => fun f => Some (FS f)
                                      end f
                                  end
      end x' (substVar x')
  end.

Definition not_zero n (f : fin n) : exp n -> exp (S (pred n)) :=
  match f in fin n return exp n -> exp (S (pred n)) with
    | FO _ => fun e => e
    | FS _ _ => fun e => e
  end.

Definition not_zeroA n (f : fin n) : exp (S n) -> exp (S (S (pred n))) :=
  match f in fin n return exp (S n) -> exp (S (S (pred n))) with
    | FO _ => fun e => e
    | FS _ _ => fun e => e
  end.

Fixpoint subst' n (e : exp n) (v : val) {struct e} : fin n -> exp (pred n) :=
  match e in exp n return fin n -> exp (pred n) with
    | Var _ f' => fun f => match substVar f f' with
                             | None => Value v
                             | Some f'' => Var f''
                           end

    | Unit _ => fun _ => Unit

    | App _ e1 e2 => fun f => App (subst' e1 v f) (subst' e2 v f)
    | Abs _ e1 => fun f => Abs (not_zeroA f (subst' e1 v (FS (FS f))))

    | ELet _ e1 e2 => fun f => ELet (subst' e1 v f) (not_zero f (subst' e2 v (FS f)))

    | Pair _ e1 e2 => fun f => Pair (subst' e1 v f) (subst' e2 v f)
    | EFst _ e1 => fun f => EFst (subst' e1 v f)
    | ESnd _ e1 => fun f => ESnd (subst' e1 v f)

    | EInl _ e1 => fun f => EInl (subst' e1 v f)
    | EInr _ e1 => fun f => EInr (subst' e1 v f)
    | ECase _ e1 e2 e3 => fun f => ECase (subst' e1 v f)
      (not_zero f (subst' e2 v (FS f))) (not_zero f (subst' e3 v (FS f)))

    | New _ e1 => fun f => New (subst' e1 v f)
    | Read _ e1 => fun f => Read (subst' e1 v f)
    | Write _ e1 e2 => fun f => Write (subst' e1 v f) (subst' e2 v f)

    | EThrow _ e1 => fun f => EThrow (subst' e1 v f)
    | ECatch _ e1 e2 => fun f => ECatch (subst' e1 v f) (not_zero f (subst' e2 v (FS f)))

    | Const _ b => fun _ => Const b
    | Eq _ e1 e2 => fun f => Eq (subst' e1 v f) (subst' e2 v f)

    | Value _ v => fun _ => Value v
  end.

Definition subst n (e : exp (S n)) (v : val) : exp n := subst' e v FO.

Inductive eval : heap -> exp O -> heap -> result -> Prop :=
| EvalApp : forall e1 e2 h1 h2 f h3 v1 h4 v2,
  eval h1 e1 h2 (Ans (VFunc f))
  -> eval h2 e2 h3 (Ans v1)
  -> eval h3 (subst (subst f (VFunc f)) v1) h4 v2
  -> eval h1 (App e1 e2) h4 v2
| EvalAppEx1 : forall e1 e2 h1 h2 v,
  eval h1 e1 h2 (Ex v)
  -> eval h1 (App e1 e2) h2 (Ex v)
| EvalAppEx2 : forall e1 e2 h1 h2 f h3 v,
  eval h1 e1 h2 (Ans (VFunc f))
  -> eval h2 e2 h3 (Ex v)
  -> eval h1 (App e1 e2) h3 (Ex v)

| EvalAbs : forall h e1,
  eval h (Abs e1) h (Ans (VFunc e1))

| EvalLet : forall h1 e1 h2 v h3 e2 r,
  eval h1 e1 h2 (Ans v)
  -> eval h2 (subst e2 v) h3 r
  -> eval h1 (ELet e1 e2) h3 r
| EvalLetEx : forall h1 e1 h2 v e2,
  eval h1 e1 h2 (Ex v)
  -> eval h1 (ELet e1 e2) h2 (Ex v)

| EvalUnit : forall h,
  eval h Unit h (Ans VUnit)

| EvalPair : forall h1 e1 h2 v1 e2 h3 v2,
  eval h1 e1 h2 (Ans v1)
  -> eval h2 e2 h3 (Ans v2)
  -> eval h1 (Pair e1 e2) h3 (Ans (VPair v1 v2))
| EvalPairEx1 : forall h1 e1 h2 v e2,
  eval h1 e1 h2 (Ex v)
  -> eval h1 (Pair e1 e2) h2 (Ex v)
| EvalPairEx2 : forall h1 e1 h2 v1 e2 h3 v2,
  eval h1 e1 h2 (Ans v1)
  -> eval h2 e2 h3 (Ex v2)
  -> eval h1 (Pair e1 e2) h3 (Ex v2)

| EvalFst : forall h1 e h2 v1 v2,
  eval h1 e h2 (Ans (VPair v1 v2))
  -> eval h1 (EFst e) h2 (Ans v1)
| EvalFstEx : forall h1 e h2 v,
  eval h1 e h2 (Ex v)
  -> eval h1 (EFst e) h2 (Ex v)
| EvalSnd : forall h1 e h2 v1 v2,
  eval h1 e h2 (Ans (VPair v1 v2))
  -> eval h1 (ESnd e) h2 (Ans v2)
| EvalSndEx : forall h1 e h2 v,
  eval h1 e h2 (Ex v)
  -> eval h1 (ESnd e) h2 (Ex v)

| EvalInl : forall h1 e h2 v,
  eval h1 e h2 (Ans v)
  -> eval h1 (EInl e) h2 (Ans (VInl v))
| EvalInlEx : forall h1 e h2 v,
  eval h1 e h2 (Ex v)
  -> eval h1 (EInl e) h2 (Ex v)
| EvalInr : forall h1 e h2 v,
  eval h1 e h2 (Ans v)
  -> eval h1 (EInr e) h2 (Ans (VInr v))
| EvalInrEx : forall h1 e h2 v,
  eval h1 e h2 (Ex v)
  -> eval h1 (EInr e) h2 (Ex v)

| EvalCaseL : forall h1 e e1 e2 h2 v h3 r,
  eval h1 e h2 (Ans (VInl v))
  -> eval h2 (subst e1 v) h3 r
  -> eval h1 (ECase e e1 e2) h3 r
| EvalCaseR : forall h1 e e1 e2 h2 v h3 r,
  eval h1 e h2 (Ans (VInr v))
  -> eval h2 (subst e2 v) h3 r
  -> eval h1 (ECase e e1 e2) h3 r
| EvalCaseEx : forall h1 e e1 e2 h2 v,
  eval h1 e h2 (Ex v)
  -> eval h1 (ECase e e1 e2) h2 (Ex v)

| EvalNew : forall h1 e h2 v,
  eval h1 e h2 (Ans v)
  -> eval h1 (New e) (v :: h2) (Ans (VRef (length h2)))
| EvalNewEx : forall h1 e h2 v,
  eval h1 e h2 (Ex v)
  -> eval h1 (New e) h2 (Ex v)

| EvalRead : forall h1 e h2 r v,
  eval h1 e h2 (Ans (VRef r))
  -> h2 # r = Some v
  -> eval h1 (Read e) h2 (Ans v)
| EvalReadEx : forall h1 e h2 v,
  eval h1 e h2 (Ex v)
  -> eval h1 (Read e) h2 (Ex v)

| EvalWrite : forall h1 e1 h2 e2 r h3 v,
  eval h1 e1 h2 (Ans (VRef r))
  -> eval h2 e2 h3 (Ans v)
  -> eval h1 (Write e1 e2) (h3 ## r <~ v) (Ans VUnit)
| EvalWriteEx1 : forall h1 e1 h2 e2 v,
  eval h1 e1 h2 (Ex v)
  -> eval h1 (Write e1 e2) h2 (Ex v)
| EvalWriteEx2 : forall h1 e1 h2 e2 r h3 v,
  eval h1 e1 h2 (Ans (VRef r))
  -> eval h2 e2 h3 (Ex v)
  -> eval h1 (Write e1 e2) h3 (Ex v)

| EvalThrow : forall h1 e1 h2 v,
  eval h1 e1 h2 (Ans v)
  -> eval h1 (EThrow e1) h2 (Ex v)
| EvalThrowEx : forall h1 e1 h2 v,
  eval h1 e1 h2 (Ex v)
  -> eval h1 (EThrow e1) h2 (Ex v)

| EvalCatch : forall h1 e1 h2 v e2,
  eval h1 e1 h2 (Ans v)
  -> eval h1 (ECatch e1 e2) h2 (Ans v)
| EvalCatchEx : forall h1 e1 h2 v e2 h3 r,
  eval h1 e1 h2 (Ex v)
  -> eval h2 (subst e2 v) h3 r
  -> eval h1 (ECatch e1 e2) h3 r

| EvalConst : forall h b,
  eval h (Const b) h (Ans (VBase b))

| EvalEqT : forall e1 e2 h1 h2 b h3,
  eval h1 e1 h2 (Ans (VBase b))
  -> eval h2 e2 h3 (Ans (VBase b))
  -> eval h1 (Eq e1 e2) h3 (Ans (VInr VUnit))
| EvalEqF : forall e1 e2 h1 h2 b1 h3 b2,
  eval h1 e1 h2 (Ans (VBase b1))
  -> eval h2 e2 h3 (Ans (VBase b2))
  -> b1 <> b2
  -> eval h1 (Eq e1 e2) h3 (Ans (VInl VUnit))
| EvalEqEx1 : forall h1 e1 h2 e2 v,
  eval h1 e1 h2 (Ex v)
  -> eval h1 (Eq e1 e2) h2 (Ex v)
| EvalEqEx2 : forall h1 e1 h2 e2 b h3 v,
  eval h1 e1 h2 (Ans (VBase b))
  -> eval h2 e2 h3 (Ex v)
  -> eval h1 (Eq e1 e2) h3 (Ex v)

| EvalValue : forall h v,
  eval h (Value v) h (Ans v).
