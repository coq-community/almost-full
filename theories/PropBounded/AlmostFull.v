From Coq Require Import Wf_nat.
From Coq Require Import Arith.
From Coq Require Import Wellfounded.
From Coq Require Import List.
From Coq Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.

(* **************************************************************
 *                                                              *
 *  Basic setup, inductive trees, and almost-full relations     *
 *                                                              *
 ****************************************************************)

(* Decidable *)
Definition dec_rel (X:Type) (R:X->X->Prop) :=
  forall x y, {not (R y x)} + {R y x}.

(* AF *)
Inductive almost_full X : (X -> X -> Prop) -> Prop :=
| AF_ZT : forall (R : X -> X -> Prop), 
   (forall x y, R x y) -> almost_full R
| AF_SUP : forall R, 
   (forall x, almost_full (fun y z => R y z \/ R x y)) -> almost_full R.

(* AFStrengthen *)
Lemma af_strengthen: 
 forall (X:Type) (A : X -> X -> Prop), almost_full A -> 
 forall (B : X -> X -> Prop), (forall x y, A x y -> B x y) -> almost_full B.
Proof.
intros X A p.
induction p. 
intros. apply AF_ZT; auto.
intros. apply AF_SUP. intro x. apply H0 with (x := x). 
intros. destruct H2. 
left;  auto. 
right; auto.
Defined.

(* SecureBy implies that every infinite chain has two related elements *) 
(* InfiniteChain *)
Lemma sec_binary_infinite_chain : 
  forall (X:Type) R (f : nat -> X), almost_full R -> 
  forall (k:nat), exists n, exists m, (n > m) /\ (m >= k) /\ R (f m) (f n).
Proof.
intros X R f p. induction p.
intro k. exists (S k). exists k. auto with arith.
intro k.
remember (H0 (f k) (S k)). clear Heqe. 
destruct e as (n,e).
destruct e as (m,e). destruct e. destruct H2. destruct H3.
exists n. exists m. auto with arith. 
exists m. exists k. auto with arith.
Defined.

(* InfiniteChainCorollary *)
Corollary af_inf_chain (X : Type) (R : X -> X -> Prop): 
 almost_full R -> forall (f : nat -> X), exists n, exists m, (n > m) /\ R (f m) (f n).
Proof.
intros. 
destruct (@sec_binary_infinite_chain X R f H 0); firstorder.
Defined.

(* **************************************************************
 *                                                              * 
 *  From a decidable Well-founded relation to an AlmostFull     *
 *                                                              * 
 ****************************************************************)

(* Generalization to an arbitrary decidable well-founded relation *)
(* AfTreeIter *)
Lemma af_iter : forall (X:Type) (R : X -> X -> Prop) 
 (decR : dec_rel R) (x:X) (accX : Acc R x),
 almost_full (fun y z => not (R y x) \/ not (R z y)).
Proof.
intros.
induction accX.
apply AF_SUP; intro y.
destruct (decR x y).
apply AF_ZT. intros. right. left. apply n.
assert (almost_full (fun y0 z => ~ R y0 y \/ ~ R z y0)).
apply H0. apply r.
eapply af_strengthen. apply H1. intros. 
simpl in H2. destruct H2. right. right. auto.
left. right. auto.
Defined.

(* AfFromWfCor *)
Corollary af_from_wf (X:Type) (R : X -> X -> Prop) : 
  well_founded R -> dec_rel R -> almost_full (fun x y => not (R y x)).
Proof.
intros. 
apply AF_SUP. intro x.
assert (Acc R x). apply H.
remember (@af_iter X R X0 x H0). clear Heqa.
eapply af_strengthen. apply a. intros. simpl in H1.
destruct H1.
right; assumption. 
left;  assumption.
Defined.

(* **************************************************************
 *                                                              * 
 *  From an AlmostFull relation to a Well-Founded one           *
 *                                                              * 
 ****************************************************************)

Lemma trans_clos_left : forall X (T : X -> X -> Prop) z y z0, 
 T z y -> clos_refl_trans X T z0 z -> clos_refl_trans X T z0 y.
Proof.
intros. eapply rt_trans. apply H0. apply rt_step. apply H.
Qed.

Lemma trans_clos_left_aux : forall X (T : X -> X -> Prop) z y z0, 
 T z y -> clos_refl_trans X T z0 z -> clos_trans_1n X T z0 y.
Proof.
intros X T z y z0 H Hrt.
remember (@Relation_Operators.t1n_step X T z y H) as G. clear HeqG; clear H.
remember (@clos_rt_rt1n _ T z0 z Hrt) as F. clear HeqF. clear Hrt.
induction F. apply G. econstructor 2. apply H. apply IHF. apply G.
Qed.

(* AccFromAf *)
Lemma acc_from_af: forall (X:Type) (R : X -> X -> Prop), 
  almost_full R -> forall (T : X -> X -> Prop) y, 
  (forall x z, clos_refl_trans X T z y -> 
            clos_trans_1n X T x z /\ R z x -> False) -> Acc T y.
Proof.
intros X R afPred.
induction afPred.
intros. apply Acc_intro. intros.
edestruct H0. constructor 2. split.
constructor 1. apply H1. apply H.
intros. apply Acc_intro. intros z HT.
remember (H y).
eapply H0.
intros. 
intros. destruct H3. destruct H4.
eapply H1. eapply trans_clos_left. apply HT.
apply H2. split. apply H3. apply H4.
eapply H1. apply rt_refl. split. 2: apply H4.
eapply trans_clos_left_aux. apply HT. apply H2. 
Defined.

(* WfFromAf *)
Lemma wf_from_af :
 forall (X:Type) (R : X -> X -> Prop) (T : X -> X -> Prop), 
  (forall x y, clos_trans_1n X T x y /\ R y x -> False) ->
  almost_full R -> well_founded T.
Proof.
intros. unfold well_founded. intro y. 
eapply acc_from_af. 
2: { intros. eapply H. apply H2. }
induction H0. apply AF_ZT. apply H0.
apply AF_SUP. 
intros. apply H0.
Defined.

(* A reassuring lemma *)
(* WfFromWqo *)
Lemma wf_from_wqo : 
  forall (X:Type) (R : X -> X -> Prop), transitive X R -> almost_full R -> 
  well_founded (fun x y => R x y /\ not (R y x)).
Proof.
intros X R trH afR.
apply wf_from_af with (R := R).
intros. destruct H.
assert (~ R y x).
induction H. destruct H; auto.
destruct H. assert (R z y). 
  eapply trH. apply H0. apply H. 
assert (~ R z y). 
apply IHclos_trans_1n. 
assumption. firstorder. firstorder.
assumption.
Defined.

