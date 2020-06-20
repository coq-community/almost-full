Require Import Wf_nat.
Require Import Arith.
Require Import Wellfounded.
Require Import List.
Require Import Relations.
Require Import Logic.

From AlmostFull.PropBounded Require Import AlmostFull.
From AlmostFull.PropBounded Require Import AlmostFullInduction.
From AlmostFull.PropBounded Require Import AFConstructions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.


(*=DisjunctiveWF *)
Lemma disjunctive_wf : 
  forall (A:Set) (T R1 R2 : A -> A -> Prop) 
  (decR1 : dec_rel R1) (decR2 : dec_rel R2), 
  well_founded R1 -> well_founded R2 -> 
  (forall x y, clos_trans_1n A T x y ->  R1 x y \/ R2 x y) -> well_founded T.
(*=End *)
intros A T R1 R2 decR1 decR2 wfR1 wfR2 Hincl.
pose (R x y := not (R1 y x) /\ not (R2 y x)).
assert (almost_full R) as Raf.
  apply af_intersection. 
  apply (af_from_wf wfR1 decR1).
  apply (af_from_wf wfR2 decR2).
apply wf_from_af with (R:=R).
intros x y CT. destruct CT; firstorder. assumption.
Defined.

(*=TerminatorInduction *)
Lemma disj_wf_induction:
 forall (A:Set) (T : A -> A -> Prop)
 (R1 R2 : A -> A -> Prop) 
 (decR1 : dec_rel R1) (decR2 : dec_rel R2),
 well_founded R1 -> well_founded R2 -> 
 (forall x y, clos_trans_1n A T x y ->  R1 x y \/ R2 x y) -> 
 forall P : A -> Set, 
 (forall x, (forall y, T y x -> P y) -> P x)
 -> forall a, P a.
(*=End *)
intros A T R1 R2 decR1 decR2 wfR1 wfR2 Hincl P.
apply well_founded_induction with (R := T).
apply disjunctive_wf with (R1 := R1) (R2 := R2); auto.
Defined.

