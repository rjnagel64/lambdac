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

Require Import Arith List.

Require Import LambdaTamer.LambdaTamer.

Require Import NatMap.

Set Implicit Arguments.


Fixpoint iupd A n (f : fin n) (v : A) {struct f} : ilist A n -> ilist A n :=
  match f in fin N return ilist A N -> ilist A N with
    | FO _ => fun il => v ::: itail il
    | FS _ f' => fun il => ihead il ::: iupd f' v (itail il)
  end.

Inductive result : Type :=
| Ans : nat -> result
| Ex : nat -> result.

Section n_regs.
  Variable n_regs : nat.

  Definition reg := fin (3 + n_regs).
  Definition label := nat.

  Inductive lval : Type :=
  | LReg : reg -> lval
  | LMemReg : reg -> nat -> lval
  | LMemImm : nat -> lval.

  Inductive rval : Type :=
  | RImm : nat -> rval
  | RReg : reg -> rval
  | RMemReg : reg -> nat -> rval
  | RMemImm : nat -> rval.

  Inductive instr : Type :=
  | Assgn : lval -> rval -> instr
  | Inc : reg -> nat -> instr
  | Jnz : rval -> label -> instr
  | Eq : reg -> rval -> rval -> instr.

  Inductive jump : Type :=
  | Halt : rval -> jump
  | Fail : rval -> jump
  | Jmp : rval -> jump.

  Definition block := (list instr * jump)%type.
  Definition prog := (list block * block)%type.

  Definition regs := ilist nat (3 + n_regs).
  Definition heap := NM.t nat.

  Definition sel := sel O.
  Definition upd := @upd nat.
  
  Definition set (rs : regs) (h : heap) (lv : lval) (v : nat) : regs * heap :=
    match lv with
      | LReg r => (iupd r v rs, h)
      | LMemReg r n => (rs, upd h (iget rs r + n) v)
      | LMemImm n => (rs, upd h n v)
    end.

  Definition get (rs : regs) (h : heap) (rv : rval) : nat :=
    match rv with
      | RImm l => l
      | RReg r => iget rs r
      | RMemReg r n => sel h (iget rs r + n)
      | RMemImm n => sel h n
    end.

  Definition evalI (rs : regs) (h : heap) (i : instr) : (regs * heap) + nat :=
    match i with
      | Assgn lv rv => inl _ (set rs h lv (get rs h rv))
      | Inc r n => inl _ (iupd r (iget rs r + n) rs, h)
      | Jnz rv l =>
        match get rs h rv with
          | O => inl _ (rs, h)
          | S _ => inr _ l
        end
      | Eq r rv1 rv2 => inl _ (iupd r (if eq_nat_dec (get rs h rv1) (get rs h rv2) then 1 else 0) rs, h)
    end.

  Fixpoint evalIs (rs : regs) (h : heap) (is : list instr) {struct is} : regs * heap * option nat :=
    match is with
      | nil => (rs, h, None)
      | i :: is => match evalI rs h i with
                     | inl (rs, h) => evalIs rs h is
                     | inr n => (rs, h, Some n)
                   end
    end.

  Section bls.
    Variable bls : list block.

    Inductive evalB : regs -> heap -> block -> heap -> result -> Prop :=
    | EvalHalt : forall rs h is rs' h' rv,
      evalIs rs h is = (rs', h', None)
      -> evalB rs h (is, Halt rv) h' (Ans (get rs' h' rv))
    | EvalFail : forall rs h is rs' h' rv,
      evalIs rs h is = (rs', h', None)
      -> evalB rs h (is, Fail rv) h' (Ex (get rs' h' rv))
    | EvalJmp : forall rs h is rs' h' rv b h'' r,
      evalIs rs h is = (rs', h', None)
      -> nth_error bls (get rs' h' rv) = Some b
      -> evalB rs' h' b h'' r
      -> evalB rs h (is, Jmp rv) h'' r
    | EvalJnz : forall rs h is j rs' h' l b h'' r,
      evalIs rs h is = (rs', h', Some l)
      -> nth_error bls l = Some b
      -> evalB rs' h' b h'' r
      -> evalB rs h (is, j) h'' r.
  End bls.

  Fixpoint zeroRegs (n : nat) : ilist nat n :=
    match n return ilist nat n with
      | O => INil
      | S _ => 0 ::: zeroRegs _
    end.

  Definition evalPr (p : prog) (h : heap) (r : result) : Prop :=
    evalB (fst p) (zeroRegs _) (NM.empty _) (snd p) h r.
End n_regs.

Implicit Arguments RImm [n_regs].
Implicit Arguments RMemImm [n_regs].
Implicit Arguments LMemImm [n_regs].
Implicit Arguments Halt [n_regs].
Implicit Arguments Fail [n_regs].
