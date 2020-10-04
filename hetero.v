From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.JMeq.
Require Import Coq.Init.Specif.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Logic.FinFun.

Inductive U : Set :=
   | I.

Inductive Or : Set :=
   | left 
   | right.

Notation "x ~=~ y" := (@JMeq _ x _ y) (at level 90, left associativity).

Axiom U_OR :  forall {A B : Type} (x : A) (y : B), (x ~=~ y) \/ ~ (x ~=~ y).

Axiom U_OR_Type :  forall {A B : Type} (x : A) (y : B), (x ~=~ y) + ~ (x ~=~ y).

Notation "x ** y" := (prod x y)  (at level 90, left associativity) : type_scope.
Definition eqv (A B : Type) (f : A -> B) (g : B -> A) : Prop := forall (x : A), 
  (g (f x)) = (@id A x).

Notation "H ´ 1" := (fst H) (at level 10, left associativity).
Notation "H ´ 2" := (snd H) (at level 10, left associativity).

Notation "A ~ B" := {H : (A -> B) ** (B -> A) |
   eqv (H´1) (H´2) ** eqv (H´2) (H´1)} (at level 90, left associativity).

Theorem iso_U : forall {A B : Type} {x : A} {y : B}, x ~=~ y -> A ~ B.
  intros.
  destruct H.
  apply : (@exist _ _ ((@id A) , (@id A))).
  simpl.
  by intuition.
Qed.

Theorem dec_inequality_arith : forall (x : U) (y : Or), U <> Or.
  intros.
  destruct (U_OR x y).
  destruct (iso_U H).
  destruct p.
  pose (e0 left).
  pose (e0 right).
  move : e1 e2.
  destruct (x0´2 left).
  destruct (x0´2 right).
  intros.
  rewrite e1 in e2.
  inversion e2.
  move => H'.
  cbv in H.
  move : x y H.
  rewrite <- H'.
  destruct x.
  by destruct y.
Qed.

Class cardinality (A B : Type) : Prop := {
   not_empty : {_ : A | True} ** {_ : B | True};
   less_eqv : A ~ B -> False;  
}.

Definition less_card x y := ~ (cardinality x y).


Theorem iso_eqv : forall x, x ~ x.
  move => x.
  set H := (@id x, @id x).
  apply : (@exist ((x -> x) ** (x -> x)) (fun H => eqv H.1 H.2 ** eqv H.2 H.1) H).
  constructor.
  by unfold eqv; move => x0.
  by unfold eqv; move => x0.
Qed.

Theorem sym_eqv : forall x y, x ~ y -> y ~ x.
  move => x y H.
  destruct H.
  destruct p.
  by eapply (@exist ((y -> x) ** (x -> y)) (fun H => eqv H.1 H.2 ** eqv H.2 H.1) (x0´2, x0´1)).
Qed.

Theorem trans_eqv : forall x y z, x ~ y -> y ~ z -> x ~ z.
  move => x y z H H'.
  destruct H.
  destruct H'.
  eapply (@exist _ _  ((fun x => x1.1 (x0.1 x)), (fun z => x0.2 (x1.2 z)))).
  destruct p.
  destruct p0.
  constructor.
  simpl.
  unfold eqv.
  move => x2.
  simpl in *.
  unfold eqv in *.
  by rewrite e1; rewrite e.
  simpl.
  unfold eqv.
  move => x2.
  by rewrite e0; rewrite e2.
Qed.
 
Instance Iso_equivalence : Equivalence (fun (x y : Prop) => x ~ y).
  constructor.
  apply : iso_eqv.
  apply : sym_eqv.
  apply : trans_eqv.
Qed.

Instance Isomorphism : Setoid Prop := {
    equiv := fun x y => x ~ y;
    setoid_equiv := Iso_equivalence;
}.

Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.

Theorem max_nat_leb : forall x y, x <= y -> max x y = y.
  intros.
  elim/@nat_double_ind : x/y H.
  by intros; destruct n.
  intros; inversion H.
  intros; simpl in *.
  by rewrite (H (le_S_n _  _ H0)).
Qed.

Theorem less_nat_leb : forall x y, x < y -> max y x = y.
  intros.
  elim/@nat_double_ind : x/y H.
  by intros; destruct n.
  intros; inversion H.
  intros; simpl in *.
  by rewrite (H (le_S_n _  _ H0)).
Qed.

Theorem max_nat_leb' : forall x y,  max x y = y -> x <= y.
  intros.
  elim/@nat_double_ind : x/y H.
  intros.
  destruct n.
  auto with arith.
  auto with arith.
  intros; inversion H.
  intros; simpl in *.
  apply : le_n_S.
  apply (f_equal Nat.pred) in H0.
  by apply : H.
Qed.

Theorem max_sym : forall x y, max x y = max y x.
  intros.
  elim/@nat_double_ind : x/y.
  by case.
  by case.
  move => n m //= H.
  by rewrite H.
Qed.

Theorem max_eqv : forall x y, x <= max x y.
  intros.
  elim/@nat_double_ind : x/y.
  case; auto with arith.
  case; auto with arith.
  move => n m H //=.
  auto with arith.
Qed.

Theorem list_leb : forall ls a, In a ls -> a <= fold_right Nat.max 0 ls.
  elim.
  intros.
  inversion H.
  intros.
  simpl in *.
  destruct H0.
  subst.
  apply : max_eqv.
  pose (H a0 H0).
  rewrite -> l0.
  rewrite max_sym.
  apply : max_eqv.
Qed.

Theorem plus_finite : forall ls, ~ In (1 + (fold_right max 0 ls)) ls.
      intros.
      induction ls.
      done.
      simpl.
      move => H.
      destruct H.
        have : forall a ls, a <= Nat.max a (fold_right Nat.max 0 ls).
        intros.
        generalize dependent a0.
        induction ls0.
        intros.
        simpl.
        by destruct a0.
        move => a1.
        generalize dependent (fold_right Nat.max 0 (a0 :: ls0)).
        move => n.
        destruct (le_lt_dec a1 n).
        pose(max_nat_leb l).
        by rewrite e.
        by rewrite (less_nat_leb l).
      move => H1'.
      pose (H1' a ls).
        have : 1 + Nat.max a (fold_right Nat.max 0 ls) <=  Nat.max a (fold_right Nat.max 0 ls).
        simpl.
        by rewrite <- H.
      move => H3.
      by apply PeanoNat.Nat.nle_succ_diag_l in H3.
      simpl in *.
      apply : IHls.
         destruct (le_lt_dec a  (fold_right Nat.max 0 ls)).
        pose(max_nat_leb l).
       by rewrite e in H.
        pose(less_nat_leb l).
        rewrite e in H.
        pose(list_leb H).
        destruct ((Gt.gt_not_le _ _ l0) (le_S_n _ _ (le_S _ _ l))).
Qed.

  
Theorem infinite_nat_absurd : ~ Finite nat.
      move => H'.
    unfold Finite in H'.
    destruct H'.
    unfold Full in H.

    destruct (@plus_finite x (H (1 + fold_right Nat.max 0 x))).
Qed.

Theorem map_is_bijective : forall {A B} (ls : list A) a (f : A -> B), In a ls -> In (f a) (map f ls).
 move => A B; elim.
 move => //=.
 intros.
 simpl in *.
 destruct H0.
 rewrite H0.
 by left.
 by right; apply : H.
Qed.


Theorem list_inequality_In : forall A (xs: list A) a b, In a xs -> ~ In b xs -> a <> b. 
  intros.
  induction xs.
  inversion H.
  simpl in *.
  destruct H.
  subst.
  move => H.
  apply : H0.
  by left.
  apply : IHxs.
  assumption.
  move => H2.
  apply : H0.
  by right.
Qed.

Theorem finite_incompletude :
  forall {A} (l : list A) (H : Full l) (f : A -> nat), {x : nat | forall (y : A), f y <> x}.
  intros.
  unfold Full in H.
  exists (1 + fold_right Nat.max 0 (map f l)).
  move => y H'.
  destruct ((list_inequality_In (map_is_bijective f (H y)) (@plus_finite (map f l)) H')).
Qed.

Theorem card_difference : forall {A} (H : Finite A) (x : nat) (y : A), A <> nat.
  intros.    
  pose (infinite_nat_absurd).
  destruct (U_OR x y).
  destruct (iso_U H0).
  destruct p.
  destruct H.
  destruct x0 as [f g].
  simpl in *.
    have : forall n, {x | g x = n}.
      move => n0.
      exists (f n0).
      apply : e.
  move => PF. 
  destruct (finite_incompletude H g).
  destruct (PF x0).
  pose (n0 x2).
  intuition.
  move => H3.
  rewrite H3 in H.
  by apply : infinite_nat_absurd.
Qed.

Theorem Uni : forall {A} (H : Finite A) (x : nat) (y : A), (A = nat) ~ (A ~ nat) -> False.
Admitted.
