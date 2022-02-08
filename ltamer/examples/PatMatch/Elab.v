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

Require Import Source.

Set Implicit Arguments.


Section vars.
  Variable var : type -> Type.

  Inductive eterm : type -> Type :=
  | EVar : forall t,
    var t
    -> eterm t

  | EUnit : eterm Unit

  | EApp : forall t1 t2,
    eterm (t1 --> t2)
    -> eterm t1
    -> eterm t2
  | EAbs : forall t1 t2,
    (var t1 -> eterm t2)
    -> eterm (t1 --> t2)

  | EPair : forall t1 t2,
    eterm t1
    -> eterm t2
    -> eterm (t1 ** t2)
  | EFst : forall t1 t2,
    eterm (t1 ** t2)
    -> eterm t1
  | ESnd : forall t1 t2,
    eterm (t1 ** t2)
    -> eterm t2

  | EInl : forall t1 t2,
    eterm t1
    -> eterm (t1 ++ t2)
  | EInr : forall t1 t2,
    eterm t2
    -> eterm (t1 ++ t2)
  | ECase : forall t1 t2 t,
    eterm (t1 ++ t2)
    -> (var t1 -> eterm t)
    -> (var t2 -> eterm t)
    -> eterm t.
End vars.

Implicit Arguments EVar [var t].
Implicit Arguments EUnit [var].
Implicit Arguments EApp [var t1 t2].
Implicit Arguments EAbs [var t1 t2].
Implicit Arguments EPair [var t1 t2].
Implicit Arguments EFst [var t1 t2].
Implicit Arguments ESnd [var t1 t2].
Implicit Arguments EInl [var t1 t2].
Implicit Arguments EInr [var t1 t2].
Implicit Arguments ECase [var t1 t2 t].


Notation "# v" := (EVar v) (at level 70) : elab_scope.

Notation "()" := EUnit : elab_scope.

Infix "@" := EApp (left associativity, at level 77) : elab_scope.
Notation "\ x , e" := (EAbs (fun x => e)) (at level 78) : elab_scope.
Notation "\ ? , e" := (EAbs (fun _ => e)) (at level 78) : elab_scope.

Notation "[ x , y ]" := (EPair x y) (at level 72) : elab_scope.
Notation "#1 e" := (EFst e) (at level 72) : elab_scope.
Notation "#2 e" := (ESnd e) (at level 72) : elab_scope.

Notation "'Inl' e" := (EInl e) (at level 71) : elab_scope.
Notation "'Inr' e" := (EInr e) (at level 71) : elab_scope.
Notation "'Cases' e 'of' ||| x => e1 ||| y => e2" :=
  (ECase e (fun x => e1) (fun y => e2)) (at level 77, e at next level, e1 at next level, e2 at next level) : elab_scope.
Notation "'Cases' e 'of' ||| ? => e1 ||| y => e2" :=
  (ECase e (fun _ => e1) (fun y => e2)) (at level 77, e at next level, e1 at next level, e2 at next level) : elab_scope.
Notation "'Cases' e 'of' ||| x => e1 ||| ? => e2" :=
  (ECase e (fun x => e1) (fun _ => e2)) (at level 76, e at next level, e1 at next level, e2 at next level) : elab_scope.
Notation "'Cases' e 'of' ||| ? => e1 ||| ? => e2" :=
  (ECase e (fun _ => e1) (fun _ => e2)) (at level 77, e at next level, e1 at next level, e2 at next level) : elab_scope.

Bind Scope elab_scope with eterm.
Delimit Scope elab_scope with elab.

Open Local Scope elab_scope.

Fixpoint etermDenote t (e : eterm typeDenote t) {struct e} : typeDenote t :=
  match e in (eterm _ t) return (typeDenote t) with
    | EVar _ v => v

    | EUnit => tt

    | EApp _ _ e1 e2 => (etermDenote e1) (etermDenote e2)
    | EAbs _ _ e' => fun x => etermDenote (e' x)

    | EPair _ _ e1 e2 => (etermDenote e1, etermDenote e2)
    | EFst _ _ e' => fst (etermDenote e')
    | ESnd _ _ e' => snd (etermDenote e')

    | EInl _ _ e' => inl _ (etermDenote e')
    | EInr _ _ e' => inr _ (etermDenote e')
    | ECase _ _ _ e' e1 e2 =>
      match etermDenote e' with
        | inl v => etermDenote (e1 v)
        | inr v => etermDenote (e2 v)
      end
  end.

Definition Eterm t := forall var, eterm var t.
Definition EtermDenote t (E : Eterm t) := etermDenote (E _).
