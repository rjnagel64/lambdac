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


Inductive var : Type :=
| Slot : nat -> var
| FuncVar : nat -> var.

Inductive primop : Type :=
| Unit : primop

| Pair : var -> var -> primop
| EFst : var -> primop
| ESnd : var -> primop

| EInl : var -> primop
| EInr : var -> primop

| New : var -> primop
| Read : var -> primop
| Write : var -> var -> primop

| Const : base -> primop
| Eq : var -> var -> primop.

Inductive exp : Type :=
| EHalt : var -> exp
| Call : var -> var -> exp
| Assign : nat -> primop -> exp -> exp
| ECase : var -> nat -> exp -> nat -> exp -> exp
| EUncaught : var -> exp.

Record func : Type := Func {
  f_nslots : nat;
  f_body : exp
}.

Record prog : Type := Prog {
  p_funcs : list func;
  p_nslots : nat;
  p_body : exp
}.

Inductive val : Set :=
| VProc : nat -> val
| VUnit : val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VRef : label -> val
| VBase : base -> val.

Section get.
  Variable slots : list (option val).

  Definition get (x : var) : option val :=
    match x with
      | Slot f => match slots # f with
                    | Some o => o
                    | None => None
                  end
      | FuncVar f => Some (VProc f)
    end.

  Inductive evalP : list val -> primop -> list val -> val -> Prop :=
  | EvalUnit : forall h, evalP h Unit h VUnit

  | EvalPair : forall h x1 x2 v1 v2, get x1 = Some v1 -> get x2 = Some v2 -> evalP h (Pair x1 x2) h (VPair v1 v2)
  | EvalFst : forall h x v1 v2, get x = Some (VPair v1 v2) -> evalP h (EFst x) h v1
  | EvalSnd : forall h x v1 v2, get x = Some (VPair v1 v2) -> evalP h (ESnd x) h v2

  | EvalInl : forall h x v, get x = Some v -> evalP h (EInl x) h (VInl v)
  | EvalInr : forall h x v, get x = Some v -> evalP h (EInr x) h (VInr v)

  | EvalNew : forall h x v, get x = Some v -> evalP h (New x) (v :: h) (VRef (length h))
  | EvalRead : forall h x l v, get x = Some (VRef l) -> h # l = Some v -> evalP h (Read x) h v
  | EvalWrite : forall h x1 x2 l v, get x1 = Some (VRef l) -> get x2 = Some v
    -> evalP h (Write x1 x2) (h ## l <~ v) VUnit

  | EvalConst : forall h b, evalP h (Const b) h (VBase b)
  | EvalEqT : forall h x1 x2 b, get x1 = Some (VBase b) -> get x2 = Some (VBase b) -> evalP h (Eq x1 x2) h (VInr VUnit)
  | EvalEqF : forall h x1 x2 b1 b2, get x1 = Some (VBase b1) -> get x2 = Some (VBase b2)
    -> b1 <> b2 -> evalP h (Eq x1 x2) h (VInl VUnit).
End get.

Fixpoint filler (n : nat) : list (option val) :=
  match n with
    | O => nil
    | S n' => None :: filler n'
  end.

Inductive result : Type :=
| Ans : val -> result
| Ex : val -> result.

Section funcs.
  Variable funcs : list func.

  Inductive eval : list val -> list (option val) -> exp -> result -> Prop :=
  | EvalHalt : forall h sls x v,
    get sls x = Some v
    -> eval h sls (EHalt x) (Ans v)
  | EvalCall : forall h sls f fn fc x xv r,
    get sls f = Some (VProc fn)
    -> get sls x = Some xv
    -> funcs # fn = Some fc
    -> eval h (filler (pred (pred (f_nslots fc))) ++ Some (VProc fn) :: Some xv :: nil) (f_body fc) r
    -> eval h sls (Call f x) r
  | EvalAssign : forall sls h1 p h2 v sl e r,
    evalP sls h1 p h2 v
    -> sl < length sls
    -> eval h2 (sls ## sl <~ (Some v)) e r
    -> eval h1 sls (Assign sl p e) r
  | EvalCaseL : forall sls x v h sl1 e1 r sl2 e2,
    get sls x = Some (VInl v)
    -> sl1 < length sls
    -> eval h (sls ## sl1 <~ (Some v)) e1 r
    -> eval h sls (ECase x sl1 e1 sl2 e2) r
  | EvalCaseR : forall sls x v h sl1 e1 r sl2 e2,
    get sls x = Some (VInr v)
    -> sl2 < length sls
    -> eval h (sls ## sl2 <~ (Some v)) e2 r
    -> eval h sls (ECase x sl1 e1 sl2 e2) r
  | EvalUncaught : forall h sls x v,
    get sls x = Some v
    -> eval h sls (EUncaught x) (Ex v).
End funcs.

Definition evalPr (pr : prog) (r : result) :=
  eval (p_funcs pr) nil (filler (p_nslots pr)) (p_body pr) r.
