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

Require Import Arith List Max.

Require Import LambdaTamer.LambdaTamer.

Require Import Base.

Require Import Flat.
Require Import Asm.

Set Implicit Arguments.

Section n_regs.
  Variable n_regs : nat.

  Definition hptr : reg n_regs := FO.
  Definition tmp : reg n_regs := FS FO.
  Definition arg : reg n_regs := FS FO.
  Definition self : reg n_regs := FS (FS FO).

  Fixpoint genSlot' (n_regs sl : nat) {struct n_regs} : option (fin n_regs) :=
    match n_regs return option (fin n_regs) with
      | O => None
      | S n_regs' =>
        match sl with
          | O => Some FO
          | S sl' =>
            match genSlot' n_regs' sl' with
              | Some f => Some (FS f)
              | None => None
            end
        end
    end.

  Definition genSlotL (sl : nat) : lval n_regs :=
    match genSlot' n_regs sl with
      | Some f => LReg (FS (FS (FS f)))
      | None => LMemImm (sl - n_regs)
    end.

  Definition genSlotR (sl : nat) : rval n_regs :=
    match genSlot' n_regs sl with
      | Some f => RReg (FS (FS (FS f)))
      | None => RMemImm (sl - n_regs)
    end.

  Fixpoint internalLabels (e : Flat.exp) : nat :=
    match e with
      | EHalt _ => O
      | Call _ _ => O
      | Assign _ _ e' => internalLabels e'
      | ECase _ _ e1 _ e2 => S (internalLabels e1 + internalLabels e2)
      | EUncaught _ => O
    end.

  Fixpoint genLabel (fs : list Flat.func) (l : nat) {struct fs} : nat :=
    match fs with
      | nil => O
      | f :: fs' =>
        if eq_nat_dec l (length fs')
          then O
          else S (internalLabels (f_body f) + genLabel fs' l)
    end.

  Section prog.
    Variable fs : list Flat.func.

    Definition genVar (v : var) : rval n_regs :=
      match v with
        | FuncVar l => RImm (genLabel fs l)
        | Slot sl => genSlotR sl
      end.

    Definition read (dst : lval n_regs) (src : rval n_regs) (n : nat) : list (instr n_regs) :=
      match src with
        | RImm n' => Assgn dst (RMemImm (n + n')) :: nil
        | RReg r => Assgn dst (RMemReg r n) :: nil
        | RMemReg r n' => Assgn (LReg tmp) (RMemReg r n') :: Assgn dst (RMemReg tmp n) :: nil
        | RMemImm n' => Assgn (LReg tmp) (RMemImm n') :: Assgn dst (RMemReg tmp n) :: nil
      end.

    Definition write (dst : rval n_regs) (n : nat) (src : rval n_regs) : list (instr n_regs) :=
      match dst with
        | RImm n' => Assgn (LMemImm (n + n')) src :: nil
        | RReg r => Assgn (LMemReg r n) src :: nil
        | RMemReg r n' => Assgn (LReg tmp) (RMemReg r n') :: Assgn (LMemReg tmp n) src :: nil
        | RMemImm n' => Assgn (LReg tmp) (RMemImm n') :: Assgn (LMemReg tmp n) src :: nil
      end.

    Fixpoint genPrimop (lv : lval n_regs) (p : primop) {struct p} : list (instr n_regs) :=
      match p with
        | Unit => nil

        | Pair x y =>
          Assgn (LMemReg hptr 0) (genVar x)
          :: Assgn (LMemReg hptr 1) (genVar y)
          :: Assgn lv (RReg hptr)
          :: Inc hptr 2
          :: nil
        | EFst x => read lv (genVar x) 0
        | ESnd x => read lv (genVar x) 1

        | EInl x =>
          Assgn (LMemReg hptr 0) (RImm 0)
          :: Assgn (LMemReg hptr 1) (genVar x)
          :: Assgn lv (RReg hptr)
          :: Inc hptr 2
          :: nil
        | EInr x =>
          Assgn (LMemReg hptr 0) (RImm 1)
          :: Assgn (LMemReg hptr 1) (genVar x)
          :: Assgn lv (RReg hptr)
          :: Inc hptr 2
          :: nil

        | New x =>
          Assgn (LMemReg hptr 0) (genVar x)
          :: Assgn lv (RReg hptr)
          :: Inc hptr 1
          :: nil
        | Read x => read lv (genVar x) 0
        | Write x y => write (genVar x) 0 (genVar y)

        | Const b =>
          Assgn lv (RImm (encode b))
          :: nil

        | Flat.Eq x y =>
          Eq tmp (genVar x) (genVar y)
          :: Assgn (LMemReg hptr 0) (RReg tmp)
          :: Assgn lv (RReg hptr)
          :: Inc hptr 2
          :: nil
      end.

    Fixpoint genExp (l : label) (e : exp) : block n_regs * list (block n_regs) :=
      match e with
        | EHalt x => ((nil, Halt (genVar x)), nil)
        | Call f x =>
          ((Assgn (LReg self) (genVar f)
            :: Assgn (LReg arg) (genVar x)
            :: nil,
            Jmp (genVar f)), nil)
        | Assign sl p e' =>
          let out := genExp l e' in
            ((genPrimop (genSlotL sl) p ++ fst (fst out), snd (fst out)), snd out)
        | ECase x sl1 e1 sl2 e2 =>
          let out1 := genExp l e1 in
            let out2 := genExp (S (length (snd out1) + l)) e2 in
              ((Assgn (LReg tmp) (genVar x)
                :: Jnz (RMemReg tmp 0) (length (snd out1) + l)
                :: Assgn (genSlotL sl1) (RMemReg tmp 1)
                :: fst (fst out1),
                snd (fst out1)),
              snd out1 ++ (Assgn (genSlotL sl2) (RMemReg tmp 1) :: fst (fst out2), snd (fst out2)) :: snd out2)
        | EUncaught x => ((nil, Fail (genVar x)), nil)
      end.
  End prog.

  Definition genProg (pr : Flat.prog) : Asm.prog n_regs :=
    let n_slots := fold_left (fun n f => max n (f_nslots f)) (p_funcs pr) (S (S (p_nslots pr))) in
    let bls := fold_left (fun bls f =>
      let (bl, bls') := genExp (p_funcs pr) (S (length bls)) (f_body f) in
        bls
        ++ (Assgn (genSlotL 0) (RReg arg)
          :: Assgn (genSlotL 1) (RReg self)
          :: fst bl,
          snd bl)
        :: bls') (p_funcs pr) nil in
    let (bl, bls') := genExp (p_funcs pr) (length bls) (p_body pr) in
      (bls ++ bls',
        (Assgn (LReg hptr) (RImm n_slots)
          :: fst bl,
          snd bl)).
End n_regs.

Implicit Arguments genSlotL [n_regs].
Implicit Arguments genSlotR [n_regs].
