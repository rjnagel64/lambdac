(* Copyright (c) 2008, Adam Chlipala
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

Require Import CPS.

Set Implicit Arguments.


Inductive ctype : Type :=
| CData : ptype -> ctype
| CCode : ptype -> ptype -> ctype.

Notation "[< p >]" := (CData p) (at level 62) : cc_scope.
Infix "<-->" := CCode (no associativity, at level 62) : cc_scope.

Bind Scope cc_scope with ctype.
Delimit Scope cc_scope with cc.

Section vars.
  Variable var : ctype -> Set.

  Inductive cprimop : ctype -> Type :=
  | CVar : forall t,
    var ([< t >])
    -> cprimop ([< t >])
    
  | CTrue : cprimop ([< Bool >])
  | CFalse : cprimop ([< Bool >])
    
  | CPack : forall env arg,
    var (env <--> arg)
    -> var ([< env >])
    -> cprimop ([< arg ---> >])

  | CUnitIntro : cprimop ([< Unit >])

  | CPair : forall t1 t2,
    var ([< t1 >])
    -> var ([< t2 >])
    -> cprimop ([< t1 ** t2 >])
  | CFst : forall t1 t2,
    var ([< t1 ** t2 >])
    -> cprimop ([< t1 >])
  | CSnd : forall t1 t2,
    var ([< t1 ** t2 >])
    -> cprimop ([< t2 >]).

  Variable result : ptype.

  Inductive cterm : Type :=
  | CHalt : var ([< result >]) -> cterm
  | CApp : forall t,
    var ([< t ---> >])
    -> var ([< t >])
    -> cterm
  | CBind : forall t,
    cprimop t
    -> (var t -> cterm)
    -> cterm.

  Section cfuncs.
    Variable T : Type.

    Inductive cfuncs : Type :=
    | CMain : T -> cfuncs
    | CAbs : forall env arg,
      (var ([< env >]) -> var ([< arg >]) -> cterm)
      -> (var (env <--> arg) -> cfuncs)
      -> cfuncs.
  End cfuncs.

  Definition cprog := cfuncs cterm.
End vars.

Implicit Arguments CVar [var t].
Implicit Arguments CTrue [var].
Implicit Arguments CFalse [var].
Implicit Arguments CPack [var env arg].
Implicit Arguments CUnitIntro [var].
Implicit Arguments CPair [var t1 t2].
Implicit Arguments CFst [var t1 t2].
Implicit Arguments CSnd [var t1 t2].

Implicit Arguments CHalt [var result].
Implicit Arguments CApp [var result t].
Implicit Arguments CBind [var result t].

Implicit Arguments CMain [var result T].
Implicit Arguments CAbs [var result T env arg].

Notation "# v" := (CVar v) (at level 70) : cc_scope.

Notation "'Tru'" := CTrue : cc_scope.
Notation "'Fals'" := CFalse : cc_scope.

Infix "##" := CPack (no associativity, at level 71) : cc_scope.

Notation "()" := CUnitIntro : cc_scope.

Notation "[ x1 , x2 ]" := (CPair x1 x2) (at level 73) : cc_scope.
Notation "#1 x" := (CFst x) (at level 72) : cc_scope.
Notation "#2 x" := (CSnd x) (at level 72) : cc_scope.

Notation "'Halt' x" := (CHalt x) (at level 75) : cc_scope.
Infix "@@" := CApp (no associativity, at level 75) : cc_scope.
Notation "x <- p ; e" := (CBind p (fun x => e))
  (right associativity, at level 76, p at next level) : cc_scope.
Notation "? <- p ; e" := (CBind p (fun _ => e))
  (right associativity, at level 76, p at next level) : cc_scope.

Notation "'Main' e" := (CMain e) (at level 79) : cc_scope.
Notation "f <= \\ x , y , e ; fs" :=
  (CAbs (fun x y => e) (fun f => fs))
  (right associativity, at level 80, e at next level) : cc_scope.
Notation "f <= \\ ? , y , e ; fs" :=
  (CAbs (fun _ y => e) (fun f => fs))
  (right associativity, at level 80, e at next level) : cc_scope.
Notation "f <= \\ x , ? , e ; fs" :=
  (CAbs (fun x _ => e) (fun f => fs))
  (right associativity, at level 80, e at next level) : cc_scope.
Notation "f <= \\ ? , ? , e ; fs" :=
  (CAbs (fun _ _ => e) (fun f => fs))
  (right associativity, at level 80, e at next level) : cc_scope.

Bind Scope cc_scope with cprimop cterm cfuncs cprog.

Open Local Scope cc_scope.

Definition ctypeDenote (t : ctype) : Set :=
  match t with
    | [< t >] => ptypeDenote t
    | env <--> arg => ptypeDenote env -> ptypeDenote arg -> bool
  end.

Fixpoint cprimopDenote t (p : cprimop ctypeDenote t) {struct p} : ctypeDenote t :=
  match p in (cprimop _ t) return (ctypeDenote t) with
    | CVar _ v => v

    | CTrue => true
    | CFalse => false

    | CPack _ _ f env => f env

    | CUnitIntro => tt

    | CPair _ _ v1 v2 => (v1, v2)
    | CFst _ _ v => fst v
    | CSnd _ _ v => snd v
  end.

Fixpoint ctermDenote result (e : cterm ctypeDenote result) (k : ptypeDenote result -> bool)
  {struct e} : bool :=
  match e with
    | CHalt v => k v
    | CApp _ f x => f x
    | CBind _ p x => ctermDenote (x (cprimopDenote p)) k
  end.

Fixpoint cfuncsDenote result T (p : cfuncs ctypeDenote result T) (k : ptypeDenote result -> bool)
  {struct p} : T :=
  match p with
    | CMain v => v
    | CAbs _ _ e fs =>
      cfuncsDenote (fs (fun env arg => ctermDenote (e env arg) k)) k
  end.

Definition cprogDenote result (p : cprog ctypeDenote result) (k : ptypeDenote result -> bool) : bool :=
  ctermDenote (cfuncsDenote p k) k.

Definition Cprimop t := forall var, cprimop var t.
Definition Cterm result := forall var, cterm var result.
Definition Cprog result := forall var, cprog var result.

Definition CprimopDenote t (p : Cprimop t) := cprimopDenote (p _).
Definition CtermDenote result (e : Cterm result) := ctermDenote (e _).
Definition CprogDenote result (e : Cprog result) := cprogDenote (e _).
