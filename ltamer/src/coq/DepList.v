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

Require Import Arith Eqdep List.

Require Import Tactics.

Set Implicit Arguments.


Lemma plus_1 : forall n, n + 1 = S n.
  intros; omega.
Qed.



Section list.
  Variable A : Type.

  Definition tail (ls : list A) :=
    match ls with
      | nil => nil
      | _ :: ls' => ls'
    end.

  Lemma nth_error_app1 : forall v (ls2 : list A) n ls1,
    nth_error ls1 n = Some v
    -> nth_error (ls1 ++ ls2) n = Some v.
    induction n; destruct ls1; simpler; unfold error in *; simpler.
  Qed.

  Lemma nth_error_middle : forall (x : A) ls2 ls1,
    nth_error (ls1 ++ x :: ls2) (length ls1) = Some x.
    induction ls1; simpler.
  Qed.

  Hint Rewrite plus_1 : ltamer.

  Lemma nth_error_after : forall (x : A) ls2 ls1 n,
    nth_error (ls1 ++ x :: ls2) (n + S (length ls1)) = nth_error ls2 n.
    induction ls1; simpler;
      replace (n + S (S (length ls1))) with (S (n + S (length ls1))); simpler.
  Qed.

  Hint Rewrite nth_error_after : ltamer.

  Lemma nth_error_after' : forall (x y : A) ls2 ls1 n,
    nth_error ls2 n = Some y
    -> nth_error (ls1 ++ x :: ls2) (n + S (length ls1)) = Some y.
    simpler.
  Qed.

  Lemma nth_error_before : forall (x : A) ls2 n n' ls1,
    nth_error ls1 n' = Some x
    -> n' = n
    -> nth_error (ls1 ++ ls2) n = Some x.
    induction n; destruct ls1; simpler; unfold error in *; simpler; eauto.
  Qed.

  Lemma nth_error_skip : forall (ls2 : list A) n ls1,
    n >= length ls1
    -> nth_error (ls1 ++ ls2) n = nth_error ls2 (n - length ls1).
    induction n; destruct ls1; simpler; comega.
  Qed.

  Lemma nth_error_skip1 : forall (x : A) n ls2,
    n >= 1
    -> nth_error (x :: ls2) n = nth_error ls2 (n - 1).
    destruct n; simpler; comega.
  Qed.
End list.

Hint Immediate nth_error_app1 nth_error_middle.
Hint Rewrite nth_error_after : ltamer.
Hint Resolve nth_error_after' nth_error_before.
Hint Rewrite nth_error_skip nth_error_skip1 using omega : ltamer.

Section ilist.
  Variable A : Type.

  Inductive ilist : nat -> Type :=
  | INil : ilist O
  | ICons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint ilistOut n (il : ilist n) {struct il} : list A :=
    match il with
      | INil => nil
      | ICons _ x il' => x :: ilistOut il'
    end.

  Theorem length_ilistOut : forall n (il : ilist n),
    length (ilistOut il) = n.
    induction il; simpler.
  Qed.

  Definition ihead n (il : ilist (S n)) : A :=
    match il in ilist n' return match n' with
                                  | O => unit
                                  | S _ => A
                                end with
      | INil => tt
      | ICons _ x _ => x
    end.

  Definition itail n (il : ilist (S n)) : ilist n :=
    match il in ilist n' return match n' with
                                  | O => unit
                                  | S n'' => ilist n''
                                end with
      | INil => tt
      | ICons _ _ il' => il'
    end.

  Fixpoint iapp n1 n2 (il1 : ilist n1) (il2 : ilist n2) {struct il1} : ilist (n1 + n2) :=
    match il1 in ilist n1 return ilist (n1 + n2) with
      | INil => il2
      | ICons _ x il1' => ICons x (iapp il1' il2)
    end.

  Theorem app_ilistOut : forall n2 (il2 : ilist n2) n1 (il1 : ilist n1),
    ilistOut (iapp il1 il2) = ilistOut il1 ++ ilistOut il2.
    induction il1; simpler.
  Qed.

  Fixpoint iprefix n1 n2 {struct n1} : ilist (n1 + n2) -> ilist n1 :=
    match n1 return ilist (n1 + n2) -> ilist n1 with
      | O => fun _ => INil
      | S n1' => fun il => ICons (ihead il) (iprefix _ _ (itail il))
    end.

  Fixpoint isuffix n1 n2 {struct n1} : ilist (n1 + n2) -> ilist n2 :=
    match n1 return ilist (n1 + n2) -> ilist n2 with
      | O => fun il => il
      | S n1' => fun il => isuffix _ _ (itail il)
    end.
  
  Inductive fin : nat -> Type :=
  | FO : forall n, fin (S n)
  | FS : forall n, fin n -> fin (S n).

  Fixpoint finOut n (f : fin n) {struct f} : nat :=
    match f with
      | FO _ => O
      | FS _ f' => S (finOut f')
    end.

  Fixpoint flift n (f : fin n) {struct f} : fin (S n) :=
    match f in fin n return fin (S n) with
      | FO _ => FO _
      | FS _ f' => FS (flift f')
    end.

  Fixpoint flast (n : nat) : fin (S n) :=
    match n return fin (S n) with
      | O => FO _
      | S n' => FS (flast n')
    end.

  Fixpoint inth (ls : list A) : fin (length ls) -> A :=
    match ls return fin (length ls) -> A with
      | nil => fun f => match f in fin n' return match n' with
                                                   | O => A
                                                   | S _ => unit
                                                 end with
                          | FO _ => tt
                          | _ => tt
                        end
      | x :: ls' => fun f => match f in fin n' return match n' with
                                                        | O => unit
                                                        | S n'' => (fin n'' -> A) -> A
                                                      end with
                               | FO _ => fun _ => x
                               | FS _ f' => fun inth_ls' => inth_ls' f'
                             end (inth ls')
    end.

  Fixpoint fmiddle (ls1 : list A) x ls2 {struct ls1} : fin (length (ls1 ++ x :: ls2)) :=
    match ls1 return fin (length (ls1 ++ x :: ls2)) with
      | nil => FO _
      | _ :: ls1' => FS (fmiddle ls1' x ls2)
    end.

  Lemma fmiddle_inth : forall x ls2 ls1,
    inth (ls1 ++ x :: ls2) (fmiddle ls1 x ls2) = x.
    induction ls1; simpler.
  Qed.

  Lemma length_rev_append : forall (ls1 ls2 : list A),
    length (rev_append ls1 ls2)
    = length ls1 + length ls2.
    induction ls1; equation.
  Qed.

  Theorem rev_append_S : forall (x : A) ls2 ls1,
    S (length (rev_append ls1 ls2))
    = length (rev_append (x :: ls1) ls2).
    Hint Rewrite length_rev_append : ltamer.
    
    simpler.
  Qed.

  Fixpoint fmiddleR (ls1 : list A) x ls2 {struct ls1} : fin (length (rev_append ls1 (x :: ls2))) :=
    match ls1 return fin (length (rev_append ls1 (x :: ls2))) with
      | nil => FO _
      | _ :: ls1' => match rev_append_S _ _ _ in _ = N return fin N with
                       | refl_equal => FS (fmiddleR ls1' x ls2)
                     end
    end.

  Hint Rewrite app_length : ltamer.

  Lemma fmiddle_middler : forall x y ls2 ls1 Heq,
    fmiddle (ls1 ++ y :: nil) x ls2
    = match Heq in _ = N return fin N with
        | refl_equal => FS (fmiddle ls1 x ls2)
      end.
    induction ls1; simpler.

    match type of IHls1 with
      | forall (Heq : ?T), _ => assert (Heq' : T)
    end; [ simpler | rewrite (IHls1 Heq'); clear IHls1 ].
    generalize (FS (fmiddle ls1 x ls2)) Heq Heq'.
    rewrite Heq'.
    simpler.
  Qed.

  Lemma fmiddleR_fmiddle : forall x ls2 ls1 Heq,
    fmiddleR ls1 x ls2
    = match Heq in _ = N return fin N with
        | refl_equal => fmiddle (rev ls1) x ls2
      end.
    induction ls1; equation.

    match type of IHls1 with
      | forall (Heq : ?T), _ => assert (Heq' : T)
    end; [ simpler | rewrite (IHls1 Heq'); clear IHls1 ].

    generalize (fmiddle_middler x a ls2 (rev ls1)); intro Hmid.
    match type of Hmid with
      | forall (Heq : ?T), _ => assert (Heq'' : T)
    end; [ simpler | rewrite (Hmid Heq''); clear Hmid ].

    repeat match goal with
             | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
           end.
    generalize (fmiddle (rev ls1) x ls2).
    rewrite Heq'; simpler.

    repeat match goal with
             | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
           end.
    generalize f.
    rewrite Heq0.
    simpler.

    clear_all.
    repeat match goal with
             | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
           end.
    generalize (FS f0).
    rewrite e0.
    simpler.
  Qed.

  Hint Rewrite rev_length fmiddle_inth : ltamer.

  Lemma fmiddleR_inth : forall x ls1 ls2,
    inth (rev_append ls1 (x :: ls2)) (fmiddleR ls1 x ls2) = x.
    intros.
    generalize (fmiddleR_fmiddle x ls2 ls1); intro Hmid.
    match type of Hmid with
      | forall (Heq : ?T), _ => assert (Heq' : T)
    end; [ simpler | rewrite (Hmid Heq'); clear Hmid ].  
    generalize dependent Heq'.
    rewrite rev_append_rev.
    simpler.
  Qed.

  Definition fall n (P : fin n -> Prop) :=
    forall i, P i.

  Theorem fall_O : forall (P : fin O -> Prop), fall P.
    red; intros.
    inversion i.
  Qed.

  Theorem fall_S : forall n (P : fin (S n) -> Prop),
    P (FO _)
    -> fall (fun i => P (FS i))
    -> fall P.
    red; intros.
    dep_destruct i; simpler.
  Qed.

  Definition fin_O T (i : fin O) : T :=
    match i in fin n return match n with
                              | O => T
                              | _ => unit
                            end with
      | FO _ => tt
      | FS _ _ => tt
    end.

  Implicit Arguments FO [n].

  Definition fin_S n (i : fin (S n)) : {i' : fin n | i = FS i'} + {i = FO} :=
    match i in fin n return match n return forall i : fin n, Type with
                              | S n => fun i => {i' : fin n | i = FS i'} + {i = FO}
                              | _ => fun _ => unit
                            end i with
      | FO _ => inright _ (refl_equal _)
      | FS _ i' => inleft _ (exist _ i' (refl_equal _))
    end.

  Fixpoint iget n (il : ilist n) {struct il} : fin n -> A :=
    match il in ilist n return fin n -> A with
      | INil => fun f => match f in fin n' return match n' with
                                                    | O => A
                                                    | S _ => unit
                                                  end with
                           | FO _ => tt
                           | _ => tt
                         end
      | ICons _ x il' => fun f => match f in fin n' return match n' with
                                                             | O => unit
                                                             | S n'' => (fin n'' -> A) -> A
                                                           end with
                                    | FO _ => fun _ => x
                                    | FS _ f' => fun iget_il' => iget_il' f'
                                  end (iget il')
    end.

  Lemma ex_ilist_S : forall n (P : ilist (S n) -> Prop) x ils,
    P (ICons x ils)
    -> ex P.
    eauto.
  Qed.

  Lemma ilist_O : forall il : ilist O, il = INil.
    intro; dep_destruct il; reflexivity.
  Qed.
  
  Lemma ilookup_step : forall m n,
    m < S n
    -> m <> n
    -> m < n.
    intros; omega.
  Defined.

  Implicit Arguments lt_n_O [n].
  Implicit Arguments ilookup_step [m n].

  Fixpoint ilookup n (il : ilist n) m {struct il} : m < n -> A :=
    match il in ilist n return m < n -> A with
      | INil => fun Hlt => match lt_n_O Hlt with end
      | ICons n' x il' => fun Hlt =>
        match eq_nat_dec m n' with
          | left _ => x
          | right Hne => ilookup il' (ilookup_step Hlt Hne)
        end
    end.

  Theorem ilookup_irrel : forall m n (il : ilist n) (pf1 pf2 : m < n),
    ilookup il pf1 = ilookup il pf2.
    induction il; equation_expensive;
      match goal with
        | [ H : _ < 0 |- _ ] => inversion H
      end.
  Qed.

  Infix ":::" := ICons (at level 60, right associativity).
  Infix "+++" := iapp (at level 60, right associativity).

  Theorem ilookup_middle : forall x n2 (il2 : ilist n2) n1 (il1 : ilist n1) (wf : n2 < _),
    ilookup (il1 +++ x ::: il2) wf = x.
    induction il1; equation_expensive; elimtype False; omega.
  Qed.

  Theorem ilookup_middle' : forall x n2 y (il2 : ilist n2) n1 n3 (il1 : ilist n1) (wf1 : n3 < _) (wf2 : n3 < _),
    n3 <> n2
    -> ilookup (il1 +++ x ::: il2) wf1 = ilookup (il1 +++ y ::: il2) wf2.
    Hint Resolve ilookup_irrel.

    induction il1; equation_expensive; elimtype False; omega.
  Qed.

  Theorem ilookup_app2 : forall n n2 (il2 : ilist n2) n1 (il1 : ilist n1) (wf1 : n < _) (wf2 : n < _),
    n < n2
    -> ilookup (il1 +++ il2) wf1 = ilookup il2 wf2.
    induction il1; equation_expensive; elimtype False; omega.
  Qed.

  Theorem ilookup_app2' : forall x n n2 (il2 : ilist n2) n1 (il1 : ilist n1) (wf1 : n < _) (wf2 : n < _),
    n < n2
    -> ilookup (il1 +++ x ::: il2) wf1 = ilookup il2 wf2.
    induction il1; equation_expensive; elimtype False; omega.
  Qed.

  Theorem ilookup_not_middle1 : forall n3 (il3 : ilist n3) n n2 (il2 : ilist n2)
    n1 (il1 : ilist n1) (wf1 : n < _) (wf2 : n3 + n < _),
    n2 <= n
    -> ilookup (il1 +++ il2) wf1 = ilookup (il1 +++ il3 +++ il2) wf2.
    induction il1; equation_expensive; elimtype False; omega.
  Qed.

  Theorem ilookup_not_middle2 : forall n3 (il3 : ilist n3) n n2 (il2 : ilist n2)
    n1 (il1 : ilist n1) (wf1 : n < _) (wf2 : n < _),
    n < n2
    -> ilookup (il1 +++ il2) wf1 = ilookup (il1 +++ il3 +++ il2) wf2.
    induction il1; equation; try (elimtype False; omega);
      induction il3; equation_expensive; try (elimtype False; omega).
  Qed.

  Theorem ilookup_not_1middle1 : forall x n n2 (il2 : ilist n2) n1 (il1 : ilist n1) (wf1 : n < _) (wf2 : S n < _),
    n2 <= n
    -> ilookup (il1 +++ il2) wf1 = ilookup (il1 +++ x ::: il2) wf2.
    induction il1; equation_expensive; try (elimtype False; omega).
    change (a =
      match
        match
          n0 + S n2 as n return ({S (n0 + n2) = n} + {S (n0 + n2) = n -> False})
          with
          | 0 => right (S (n0 + n2) = 0) (sym_not_eq (O_S (n0 + n2)))
          | S m =>
            (fun m => sumbool_rec
              (fun _ : {n0 + n2 = m} + {n0 + n2 = m -> False} =>
                {S (n0 + n2) = S m} + {S (n0 + n2) = S m -> False})
              (fun a0 : n0 + n2 = m =>
                left (S (n0 + n2) = S m -> False) (f_equal S a0))
              (fun b : n0 + n2 = m -> False =>
                right (S (n0 + n2) = S m) (not_eq_S (n0 + n2) m b))
              (eq_nat_dec (n0 + n2) m)) m
        end
        with
        | left _ => a
        | right Hne => (fun Hne => ilookup (il1 +++ x ::: il2) (ilookup_step wf2 Hne)) Hne
      end).

    match goal with
      | [ |- _ = match (match _ with O => ?X | S m => ?Y m end) with
                   | left _ => _
                   | right Hne => ?F Hne
                 end ] =>
      assert (H' : if Y (n0 + n2) then True else False); [
        destruct (eq_nat_dec (n0 + n2) (n0 + n2)); simpl; tauto
        | generalize X Y F H'
      ]
    end.

    rewrite <- plus_Snm_nSm.
    simpler.
    destruct (s (n0 + n2)); tauto.

    change (ilookup (il1 +++ il2) (ilookup_step wf1 n1) =
      match
        match n0 + S n2 as n3 return ({S n = n3} + {S n = n3 -> False}) with
          | 0 => right (S n = 0) (sym_not_eq (O_S n))
          | S m =>
            (fun m => sumbool_rec
              (fun _ : {n = m} + {n = m -> False} =>
                {S n = S m} + {S n = S m -> False})
              (fun a0 : n = m => left (S n = S m -> False) (f_equal S a0))
              (fun b : n = m -> False => right (S n = S m) (not_eq_S n m b))
              (eq_nat_dec n m)) m
        end
        with
        | left _ => a
        | right Hne => (fun Hne => ilookup (il1 +++ x ::: il2) (ilookup_step wf2 Hne)) Hne
      end).
    
    match goal with
      | [ |- _ = match (match _ with O => ?X | S m => ?Y m end) with
                   | left _ => _
                   | right Hne => ?F _
                 end ] =>
      assert (H' : if Y (n0 + n2) then False else True); [
        destruct (eq_nat_dec n (n0 + n2)); simpl; tauto
        | assert (H'' : forall Hne, ilookup (il1 +++ il2) (ilookup_step wf1 n1)
          = F Hne); [
            auto
            | generalize X Y F H' H''
          ]
      ]
    end.

    rewrite <- plus_Snm_nSm.
    simpler.
    destruct (s (n0 + n2)); intuition.
  Qed.

  Theorem ilookup_not_1middle2 : forall x n n2 (il2 : ilist n2) n1 (il1 : ilist n1) (wf1 : n < _) (wf2 : n < _),
    n < n2
    -> ilookup (il1 +++ il2) wf1 = ilookup (il1 +++ x ::: il2) wf2.
    induction il1; equation_expensive; elimtype False; omega.
  Qed.

  Theorem ilist_nil : forall il : ilist O,
    il = INil.
    intro; dep_destruct il; reflexivity.
  Qed.
End ilist.

Implicit Arguments INil [A].
Infix ":::" := ICons (at level 60, right associativity).
Infix "+++" := iapp (at level 60, right associativity).
Implicit Arguments FO [n].
Implicit Arguments flast [n].
Implicit Arguments iprefix [A n2].
Implicit Arguments isuffix [A n2].
Implicit Arguments fin_O [T].

Hint Resolve ex_ilist_S.
(*Hint Rewrite ilookup_middle : ltamer.*)
Hint Resolve ilookup_middle' ilookup_app2 ilookup_app2'
  ilookup_not_middle1 ilookup_not_middle2
  ilookup_not_1middle1 ilookup_not_1middle2.

Hint Rewrite app_ilistOut length_ilistOut : ltamer.

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  Theorem map_inth : forall ls i pf,
    inth (map f ls) (match pf in _ = ls return fin ls with
                       | refl_equal => i
                     end)
    = f (inth ls i).
    induction ls; simpler; dep_destruct i; simpler.
      
    generalize pf; rewrite H; simpler.

    rewrite <- (IHls v H).
    generalize pf H (inth (map f ls)).
    rewrite <- H; simpler.
  Qed.

  Fixpoint imap n (il : ilist A n) {struct il} : ilist B n :=
    match il in ilist _ n return ilist B n with
      | INil => INil
      | ICons _ x il' => f x ::: imap il'
    end.

  Theorem iget_imap : forall n (il : ilist A n) i,
    iget (imap il) i = f (iget il i).
    induction il; intro i; dep_destruct i; simpler.
  Qed.

  Theorem imap_ilistOut : forall n (il : ilist A n),
    map f (ilistOut il) = ilistOut (imap il).
    induction il; simpler.
  Qed.
End map.

Section imap2.
  Variables A B C : Type.
  Variable f : A -> B -> C.

  Fixpoint imap2 n (il1 : ilist A n) {struct il1} : ilist B n -> ilist C n :=
    match il1 in ilist _ n return ilist B n -> ilist C n with
      | INil => fun _ => INil
      | ICons _ x1 il1' => fun il2 => f x1 (ihead il2) ::: imap2 il1' (itail il2)
    end.
End imap2.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall x ls, B x -> hlist ls -> hlist (x :: ls).

  Definition hhead x ls (hl : hlist (x :: ls)) : B x :=
    match hl in hlist ls' return match ls' with
                                   | nil => unit
                                   | x' :: _ => B x'
                                 end with
      | HNil => tt
      | HCons _ _ x _ => x
    end.

  Definition htail x ls (hl : hlist (x :: ls)) : hlist ls :=
    match hl in hlist ls' return match ls' with
                                   | nil => unit
                                   | _ :: ls'' => hlist ls''
                                 end with
      | HNil => tt
      | HCons _ _ _ hl' => hl'
    end.

  Section index.
    Variable x : A.

    Inductive index : list A -> Type :=
    | First : forall ls, index (x :: ls)
    | Next : forall y ls, index ls -> index (y :: ls).

    Fixpoint hget ls (hl : hlist ls) {struct hl} : index ls -> B x :=
      match hl in hlist ls return index ls -> B x with
        | HNil => fun i => match i in index ls' return match ls' with
                                                         | nil => B x
                                                         | _ :: _ => unit
                                                       end with
                             | First _ => tt
                             | _ => tt
                           end
        | HCons _ _ v hl' => fun i => match i in index ls' return match ls' with
                                                                    | nil => unit
                                                                    | x' :: ls'' => B x' -> (index ls'' -> B x) -> B x
                                                                  end with
                                        | First _ => fun v _ => v
                                        | Next _ _ i' => fun _ hget_hl' => hget_hl' i'
                                      end v (hget hl')
      end.
  End index.

  Section hmapND.
    Variable C : Type.

    Section f.
      Variable f : forall x, B x -> C.

      Fixpoint hmapND ls (hl : hlist ls) {struct hl} : ilist C (length ls) :=
        match hl in hlist ls return ilist _ (length ls) with
          | HNil => INil
          | HCons _ _ x hl' => f x ::: hmapND hl'
        end.
    End f.

    Theorem hmapND_ext : forall (f f' : forall x, B x -> C)
      ls (hl : hlist ls),
      (forall x (i : index x ls), f _ (hget hl i) = f' _ (hget hl i))
      -> hmapND f hl = hmapND f' hl.
      induction hl; equation.

      rewrite (H _ (First _ _)).
      f_equal.
      apply IHhl; intros.
      apply (H _ (Next _ i)).
    Qed.
  End hmapND.

  Lemma hlist_nil : forall hl : hlist nil, hl = HNil.
    intro; dep_destruct hl; reflexivity.
  Qed.

  Lemma hlist_cons : forall x ls (hl : hlist (x :: ls)), hl = HCons (hhead hl) (htail hl).
    intros; dep_destruct hl; reflexivity.
  Qed.
End hlist.

Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].
Infix "::::" := HCons (at level 60, right associativity).

Section imap_hmapND.
  Variable A : Type.
  Variable B : A -> Type.
  Variable C : Type.
  Variable f : forall x, B x -> C.
  Variable D : Type.
  Variable f' : C -> D.

  Theorem imap_hmapND : forall ls (hl : hlist B ls),
    imap f' (hmapND f hl) = hmapND (fun x (y : B x) => f' (f y)) hl.
    induction hl; equation.
  Qed.
End imap_hmapND.

Section hmap2.
  Variable A : Type.
  Variables B1 B2 B3 : A -> Type.
  Variable f : forall x, B1 x -> B2 x -> B3 x.
    
  Fixpoint hmap2 ls (hl1 : hlist B1 ls) {struct hl1} : hlist B2 ls -> hlist B3 ls :=
    match hl1 in hlist _ ls return hlist B2 ls -> hlist B3 ls with
      | HNil => fun _ => HNil
      | HCons _ _ x1 hl1' => fun hl2 => f x1 (hhead hl2) :::: hmap2 hl1' (htail hl2)
    end.
End hmap2.

Implicit Arguments hmap2 [A B1 B2 B3 ls].


Section ihmap.
  Variables A A' : Type.

  Fixpoint ihmap' n (il : ilist A n) {struct il} : forall ls, length ls = n -> hlist (fun _ : A' => A) ls :=
    match il in ilist _ n return forall ls, length ls = n -> hlist (fun _ => A) ls with
      | INil => fun ls =>
        match ls return length ls = O -> hlist (fun _ => A) ls with
          | nil => fun _ => HNil
          | _ :: _ => fun pf => match O_S _ (sym_eq pf) with end
        end
      | ICons n' x il' => fun ls =>
        match ls return length ls = S n' -> hlist (fun _ => A) ls with
          | nil => fun pf => match O_S _ pf with end
          | _ :: _ => fun pf => HCons (B := fun _ => A) x (ihmap' il' _ (eq_add_S _ _ pf))
        end
    end.

  Variable A'' : Type.
  Variable f : A'' -> A'.

  Definition ihmap ls (il : ilist A (length ls)) : hlist (fun _ => A) (map f ls) :=
    ihmap' il _ (map_length _ _).

  Lemma hmapND_ihmap' : forall n (il : ilist A n) ls pf,
    hmapND (fun _ (x : A) => x) (ihmap' il (map f ls) pf) =
    match sym_eq pf in _ = N return ilist A N with
      | refl_equal => il
    end.
    induction il; destruct ls; equation_expensive.
  Qed.

  Theorem hmapND_ihmap : forall ls (il : ilist A (length ls)),
    hmapND (fun _ (x : A) => x) (ihmap ls il)
    = match sym_eq (map_length _ _) in _ = N return ilist A N with
        | refl_equal => il
      end.
    unfold ihmap; intros; apply hmapND_ihmap'.
  Qed.
End ihmap.

Implicit Arguments ihmap [A A' A'' ls].

Section hmap.
  Variable A : Type.
  Variables B C : A -> Type.
  Variable f : forall x, B x -> C x.

  Fixpoint hmap ls (hl : hlist B ls) {struct hl} : hlist C ls :=
    match hl in hlist _ ls return hlist C ls with
      | HNil => HNil
      | HCons _ _ x hl' => f x :::: hmap hl'
    end.
End hmap.

Implicit Arguments hmap [A B C ls].

Section hmapC.
  Variables A A' : Type.
  Variable B : A -> Type.
  Variable B' : A' -> Type.
  
  Variable f : A -> A'.
  Variable g : forall x, B x -> B' (f x).

  Fixpoint hmapC ls (hl : hlist B ls) {struct hl} : hlist B' (map f ls) :=
    match hl in hlist _ ls return hlist B' (map f ls) with
      | HNil => HNil
      | HCons _ _ x hl' => g x :::: hmapC hl'
    end.

  Variable C : Type.
  Variable f' : forall x, B' x -> C.

  Require Import JMeq.
  Infix "==" := JMeq (no associativity, at level 70).

  Theorem ICons_JMeq : forall A x n1 (il1 : ilist A n1) n2 (il2 : ilist A n2),
    n1 = n2
    -> il1 == il2
    -> x ::: il1 == x ::: il2.
    simpler.
    rewrite H0.
    reflexivity.
  Qed.

  Hint Resolve ICons_JMeq map_length.

  Lemma hmapND_hmapC' : forall ls (hl : hlist B ls),
    hmapND f' (hmapC hl)
    == hmapND (fun x (v : B x) => f' (g v)) hl.
    induction hl; simpler.
  Qed.

  Theorem hmapND_hmapC : forall ls (hl : hlist B ls),
    hmapND f' (hmapC hl)
    = match sym_eq (map_length _ _) in _ = N return ilist C N with
        | refl_equal => hmapND (fun x (v : B x) => f' (g v)) hl
      end.
    intros; generalize (hmapND_hmapC' hl).
    generalize (hmapND f' (hmapC hl)) (hmapND (fun x (v : B x) => f' (g v)) hl)
      (sym_eq (map_length f ls)).
    rewrite map_length; equation.
  Qed.
End hmapC.

Implicit Arguments hmapC [A A' B B' f ls].
Implicit Arguments hmapND_hmapC [A A' B B' f C ls].

Section ihlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive ihlist : forall n, ilist A n -> Type :=
  | IHNil : ihlist INil
  | IHCons : forall v n (il : ilist A n), B v -> ihlist il -> ihlist (v ::: il).

  Definition ihhead n (il : ilist A (S n)) (ihl : ihlist il) : B (ihead il) :=
    match ihl in ihlist (n := n) il return match n return ilist _ n -> Type with
                                             | O => fun _ => unit
                                             | S _ => fun il => B (ihead il)
                                           end il with
      | IHNil => tt
      | IHCons _ _ _ x _ => x
    end.

  Definition ihtail n (il : ilist A (S n)) (ihl : ihlist il) : ihlist (itail il) :=
    match ihl in ihlist (n := n) il return match n return ilist _ n -> Type with
                                             | O => fun _ => unit
                                             | S _ => fun il => ihlist (itail il)
                                           end il with
      | IHNil => tt
      | IHCons _ _ _ _ ihl' => ihl'
    end.

  Fixpoint ihapp n1 (il1 : ilist A n1) (ihl1 : ihlist il1) n2 (il2 : ilist A n2) (ihl2 : ihlist il2)
    {struct ihl1} : ihlist (il1 +++ il2) :=
    match ihl1 in ihlist il1 return ihlist (il1 +++ il2) with
      | IHNil => ihl2
      | IHCons _ _ _ x ihl1 => IHCons x (ihapp ihl1 ihl2)
    end.

  Definition IHNil' (il : ilist A O) : ihlist il :=
    match il in ilist _ n return match n return ilist _ n -> Type with
                                   | S _ => fun _ => unit
                                   | O => fun il => ihlist il
                                 end il with
      | INil => IHNil
      | ICons _ _ _ => tt
    end.

  Definition ihlist_nil (ihl : ihlist INil) : ihl = IHNil :=
    match ihl in ihlist il return match il return ihlist il -> Prop with
                                    | INil => fun ihl => ihl = IHNil
                                    | _ => fun _ => True
                                  end ihl with
      | IHNil => refl_equal _
      | _ => I
    end.

  Fixpoint ihlistOut n (il : ilist A n) (ihl : ihlist il) {struct ihl} : list (sigT B) :=
    match ihl with
      | IHNil => nil
      | IHCons _ _ _ x il' => existT _ _ x :: ihlistOut il'
    end.

  Theorem length_ihlistOut : forall n (il : ilist A n) (ihl : ihlist il),
    length (ihlistOut ihl) = n.
    induction ihl; simpler.
  Qed.

  Definition ihlist_cons n (v : A) (il : ilist A n) (ihl : ihlist (v ::: il))
    : ihl = IHCons (ihhead ihl) (ihtail ihl) :=
    match ihl in ihlist il return match il return ihlist il -> Prop with
                                    | INil => fun _ => True
                                    | _ => fun ihl => ihl = IHCons (ihhead ihl) (ihtail ihl)
                                  end ihl with
      | IHNil => I
      | _ => refl_equal _
    end.
End ihlist.

Implicit Arguments IHNil [A B].
Implicit Arguments IHCons [A B v n il].
Infix ":::*" := IHCons (at level 60, right associativity).
Implicit Arguments ihapp [A B n1 il1 n2 il2].
Infix "+++*" := ihapp (at level 60, right associativity).
Implicit Arguments IHNil' [A B].


Hint Rewrite length_ihlistOut : ltamer.


Section ihmap2.
  Variables A1 A2 A3 : Type.
  Variable B1 : A1 -> Type.
  Variable B2 : A2 -> Type.
  Variable B3 : A3 -> Type.

  Variable f : A1 -> A2 -> A3.
  Variable g : forall x1 x2, B1 x1 -> B2 x2 -> B3 (f x1 x2).

  Fixpoint ihmap2 n (il1 : ilist A1 n) (hl1 : ihlist B1 il1) {struct hl1}
    : forall il2, ihlist B2 il2 -> ihlist B3 (imap2 f il1 il2) :=
      match hl1 in ihlist _ il1 return forall il2, ihlist B2 il2 -> ihlist B3 (imap2 f il1 il2) with
        | IHNil => fun _ _ => IHNil
        | IHCons _ _ _ x1 hl1' => fun _ hl2 =>
          g x1 (ihhead hl2) :::* ihmap2 hl1' (ihtail hl2)
      end.
End ihmap2.

Implicit Arguments ihmap2 [A1 A2 A3 B1 B2 B3 f n il1 il2].


Section hhlist.
  Variable A : Type.
  Variable B : A -> Type.
  Variable C : forall x, B x -> Type.

  Inductive hhlist : forall ls, hlist B ls -> Type :=
  | HHNil : hhlist HNil
  | HHCons : forall x (v : B x) ls (hl : hlist B ls), C v -> hhlist hl -> hhlist (v :::: hl).

  Definition hhhead x ls (hl : hlist B (x :: ls)) (hhl : hhlist hl) : C (hhead hl) :=
    match hhl in hhlist (ls := ls) hl return match ls return hlist _ ls -> Type with
                                               | nil => fun _ => unit
                                               | _ :: _ => fun hl => C (hhead hl)
                                             end hl with
      | HHNil => tt
      | HHCons _ _ _ _ x _ => x
    end.

  Definition hhtail x ls (hl : hlist B (x :: ls)) (hhl : hhlist hl) : hhlist (htail hl) :=
    match hhl in hhlist (ls := ls) hl return match ls return hlist _ ls -> Type with
                                               | nil => fun _ => unit
                                               | _ :: _ => fun hl => hhlist (htail hl)
                                             end hl with
      | HHNil => tt
      | HHCons _ _ _ _ _ hhl' => hhl'
    end.

  Definition HHNil' (hl : hlist B nil) : hhlist hl :=
    match hl in hlist _ ls return match ls return hlist _ ls -> Type with
                                    | _ :: _ => fun _ => unit
                                    | nil => fun hl => hhlist hl
                                  end hl with
      | HNil => HHNil
      | HCons _ _ _ _ => tt
    end.

  Definition hhlist_nil (hhl : hhlist HNil) : hhl = HHNil :=
    match hhl in hhlist hl return match hl return hhlist hl -> Prop with
                                    | HNil => fun hhl => hhl = HHNil
                                    | _ => fun _ => True
                                  end hhl with
      | HHNil => refl_equal _
      | _ => I
    end.

  Definition hhlist_cons x ls (v : B x) (hl : hlist B ls) (hhl : hhlist (v :::: hl))
    : hhl = HHCons (hhhead hhl) (hhtail hhl) :=
    match hhl in hhlist hl return match hl return hhlist hl -> Prop with
                                    | HNil => fun _ => True
                                    | _ => fun hhl => hhl = HHCons (hhhead hhl) (hhtail hhl)
                                  end hhl with
      | HHNil => I
      | _ => refl_equal _
    end.
End hhlist.

Implicit Arguments HHNil [A B C].
Implicit Arguments HHCons [A B C x v ls hl].
Infix "::::*" := HHCons (at level 60, right associativity).
Implicit Arguments HHNil' [A B C].


Section lall.
  Variable T : Type.

  Section lall_main.
    Variable P : T -> Prop.

    Fixpoint lall (ls : list T) : Prop :=
      match ls with
        | nil => True
        | x :: ls' => P x /\ lall ls'
      end.

    Fixpoint lall_get ls : forall i, lall ls -> P (inth ls i) :=
      match ls return forall i, lall ls -> P (inth ls i) with
        | nil => fun i _ => fin_O i
        | x :: ls' => fun i Hall =>
          match fin_S i with
            | inright Heq => match sym_eq Heq in _ = I return P (inth (x :: ls') I) with
                               | refl_equal => proj1 Hall
                             end
            | inleft (exist i' Heq) => match sym_eq Heq in _ = I return P (inth (x :: ls') I) with
                                         | refl_equal => lall_get ls' i' (proj2 Hall)
                                       end
          end
      end.

    Lemma lall_build : forall ls,
      (forall i, P (inth ls i))
      -> lall ls.
      induction ls; simpler.
      apply (H FO).
      app.
      intro.
      apply (H (FS i)).
    Qed.

    Theorem lall_app : forall ls2,
      lall ls2
      -> forall ls1, lall ls1
        -> lall (ls1 ++ ls2).
      induction ls1; simpler.
    Qed.

    Theorem lall_nil : lall nil.
      simpler.
    Qed.

    Theorem lall_cons : forall x ls,
      P x
      -> lall ls
      -> lall (x :: ls).
      simpler.
    Qed.
  End lall_main.

  Section lall_two.
    Variables P P' : T -> Prop.
  
    Theorem lall_weaken : forall ls, lall P ls -> (forall x, P x -> P' x) -> lall P' ls.
      induction ls; simpler.
    Qed.
  End lall_two.

  Section lall_three.
    Variables P P' P'' : T -> Prop.
  
    Theorem lall_weaken2 : forall ls, lall P ls -> lall P' ls -> (forall x, P x -> P' x -> P'' x) -> lall P'' ls.
      induction ls; simpler.
    Qed.
  End lall_three.
End lall.

Implicit Arguments lall_get [T P ls].

Section lall_map.
  Variable T : Type.
  Variables P P' : T -> Prop.

  Variable T' : Type.
  Variable P'' : T' -> Prop.
  Variable f : T -> T'.

  Theorem lall_weaken2f : forall ls, lall P ls -> lall P' ls -> (forall x, P x -> P' x -> P'' (f x))
    -> lall P'' (map f ls).
    induction ls; simpler.
  Qed.
End lall_map.

Section hall.
  Variable A : Type.
  Variable B : A -> Type.
  Variable P : forall x, B x -> Prop.

  Fixpoint hall ls (hl : hlist B ls) {struct hl} : Prop :=
    match hl with
      | HNil => True
      | HCons _ _ x hl' => P x /\ hall hl'
    end.

  Lemma hall_build : forall ls (hl : hlist B ls),
    (forall x (i : index x ls), P (hget hl i))
    -> hall hl.
    induction hl; simpler.
    apply (H _ (First _ _)).
    app.
    intros.
    apply (H _ (Next _ i)).
  Qed.
End hall.

Lemma pair_uneta : forall A B (p : A * B),
  (fst p, snd p) = p.
  destruct p; trivial.
Qed.
