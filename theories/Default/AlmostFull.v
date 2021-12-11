From Coq Require Import Arith Relations Lia.
From Coq Require Import FunctionalExtensionality.

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

(* WFT *)
Inductive WFT (X : Type) : Type := 
  | ZT : WFT X
  | SUP : (X -> WFT X) -> WFT X.

(* SecureBy *)
Fixpoint SecureBy (X:Type) (A : X->X->Prop) (p : WFT X) : Prop := 
 match p with 
 | ZT _ => forall x y, A x y
 | SUP p => 
     forall x, SecureBy (fun y z => A y z \/ A x y) (p x)
 end.

(* AlmostFull *)
Definition almost_full (X:Type) (A : X->X->Prop) := 
  exists p, SecureBy A p.

Lemma sup_rewrite: 
   forall (X:Type) (A : X -> X -> Prop) (f : X -> WFT X), 
   SecureBy A (SUP f) = 
   forall x, SecureBy (fun y z => A y z \/ A x y) (f x).
Proof. intros; auto. Qed.

Lemma sup_eq : forall (X:Type) (f : X -> WFT X) g, f = g -> SUP f = SUP g.
Proof.
intros.
auto.
rewrite H.
reflexivity.
Qed.

(* SecStrengthen *)
Lemma sec_strengthen: 
 forall (X:Type) (p : WFT X) (A B : X -> X -> Prop), 
 (forall x y, A x y -> B x y) -> SecureBy A p -> SecureBy B p.
Proof.
intros X p. induction p.
intros A B H H0. simpl in H0. simpl. auto.
intros A B H0 H1. simpl in H1. simpl. intro x. 
remember (H1 x) as G. eapply H. 2: apply G.
intros. simpl in H2. destruct H2. left. apply H0. apply H2. right. 
apply H0. apply H2.
Qed.

(* SecureBy implies that every infinite chain has two related elements *) 
(* InfiniteChain *)
Lemma sec_binary_infinite_chain : 
 forall (X:Type) (p : WFT X) R (f : nat -> X) (k : nat), 
 SecureBy R p -> 
 exists n, exists m, (n > m) /\ (m >= k) /\ R (f m) (f n).
Proof.
intro X. intro p. induction p. 
intros. simpl in H. exists (S k). exists k. split. auto. split. auto. apply H.
intros. simpl in H0. remember (H0 (f k)) as G. destruct (H _ _ f (S k) G).
destruct H1. destruct H1. destruct H2. destruct H3.
exists x. exists x0. split. apply H1. split. auto. auto with arith. apply H3.
exists x0. exists k. split. auto with arith. split. auto. apply H3.
Qed.

(* InfiniteChainCorollary *)
Corollary af_inf_chain (X : Type) (R : X -> X -> Prop): 
 almost_full R ->
 forall (f : nat -> X), exists n, exists m, (n > m) /\ R (f m) (f n).
Proof.
intros. destruct H as (p,Hsec).
destruct (@sec_binary_infinite_chain X p R f 0 Hsec); firstorder.
Defined.

(****************************************************************
 *                                                              * 
 *  From a decidable Well-founded relation to an AlmostFull     *
 *                                                              * 
 ****************************************************************)

(* Specific example: <= is AlmostFull *)
Fixpoint ltree_aux m (x:nat) : WFT nat :=
  match m with 
  | O   => ZT nat 
  | S n => SUP (fun y => if le_lt_dec x y then ZT nat else ltree_aux n y)
  end.

Definition le_tree x := ltree_aux (S x) x.

Lemma aux_le_tree_aux : 
  forall n m y, n > y -> m > y -> ltree_aux n y = ltree_aux m y.
Proof.
intro n. induction n. intros. inversion H.
intro m. induction m. intros. inversion H0.
intros. simpl. apply sup_eq. apply functional_extensionality. 
intro z. destruct (le_lt_dec y z). auto. apply IHn.
lia. lia.
Qed.

Lemma le_tree_rewrite_aux : 
  forall n x, n > x -> ltree_aux n x = le_tree x.
Proof.
intro n. induction n. intros. inversion H.
intros. destruct (gt_S _ _ H). simpl. 
unfold le_tree. simpl. apply sup_eq. 
apply functional_extensionality. intro y. 
destruct (le_lt_dec x y). auto. 
apply aux_le_tree_aux. lia. lia.
rewrite H0. unfold le_tree. reflexivity. 
Qed.

Lemma le_tree_rewrite : forall (x:nat),
 le_tree x = SUP (fun y => if le_lt_dec x y then ZT nat else le_tree y).
Proof.
intro x. rewrite <- (@le_tree_rewrite_aux (S x) x).
simpl. apply sup_eq. apply functional_extensionality. intro y.
destruct (le_lt_dec x y). auto. apply le_tree_rewrite_aux. firstorder.
firstorder.
Qed.

(* LeTreeLemma *)
Lemma af_le : SecureBy (fun x y => x <= y) (SUP le_tree).
Proof.
rewrite sup_rewrite. 
apply (@well_founded_induction nat lt).
apply lt_wf.
intros. unfold le_tree. simpl. 
intro y. destruct (le_lt_dec x y). simpl. intros. right. right. apply l.
rewrite -> le_tree_rewrite_aux. eapply sec_strengthen. 
2: { apply H. apply l. }
intros. simpl. simpl in H0. destruct H0.
left. left. apply H0. right. left. apply H0.
firstorder.
Qed.

(* Generalization to an arbitrary decidable well-founded relation *)
(* AfTreeIter *)
Fixpoint af_tree_iter (X:Type) (R : X -> X -> Prop) 
         (decR : dec_rel R) (x:X) (accX : Acc R x) :=
 match accX with 
 | Acc_intro _ f => SUP (fun y => 
     match decR x y with 
       | left _ => ZT X 
       | right Ry => af_tree_iter decR (f y Ry) 
     end)
 end.

(* AfTree *)
Definition af_tree (X:Type) (R : X -> X -> Prop) 
 (wfR : well_founded R) (decR : dec_rel R) : X -> WFT X.
Proof.
intro x. 
apply af_tree_iter with (R := R) (x := x). 
apply decR. apply wfR. 
Defined. (* Not Qed because we want to compute with it *)

(* AfFromWf *)
Lemma secure_from_wf :
 forall (X:Type) (R : X -> X -> Prop) 
 (wfR : well_founded R) (decR : dec_rel R),
 SecureBy (fun x y => not (R y x)) 
          (SUP (af_tree wfR decR)).
Proof.
intros. rewrite sup_rewrite.
unfold af_tree. 
intro x. remember (wfR x) as xAcc. clear HeqxAcc.
apply (@well_founded_induction X R wfR 
         (fun (x:X) => forall (xAcc : Acc R x), 
                       SecureBy (fun y z  => ~ R z y \/ ~ R y x) 
                                (af_tree_iter decR xAcc))).
intros y H. intro xAccy.
destruct xAccy. simpl.
intro z. destruct (decR y z). simpl. right. right. apply n.
eapply sec_strengthen. 2: { apply H. apply r. }
intros. simpl in H0. destruct H0. left. left. apply H0. 
right. left. apply H0.
Defined. (* Not Qed because we want to compute with it *)

(* AfFromWfCor *)
Corollary af_from_wf (X:Type) (R : X -> X -> Prop) : 
  well_founded R -> 
  dec_rel R -> almost_full (fun x y => not (R y x)).
Proof.
intros wfR decR. unfold almost_full.
exists (SUP (af_tree wfR decR)).
apply secure_from_wf.
Defined.

(* Example: <= is AF *) 
(* LeqAF *)
Corollary leq_af : almost_full le.
Proof.
unfold almost_full.
cut (dec_rel lt). intro decLt.
eexists (SUP (af_tree lt_wf decLt)).
 eapply sec_strengthen. 2: apply secure_from_wf.
intros. simpl in H. lia.
unfold dec_rel. intros. destruct (le_lt_dec x y).
left; lia.
right; lia.
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
Lemma acc_from_af: 
  forall (X:Type) (p : WFT X) (R : X -> X -> Prop) 
  (T : X -> X -> Prop) y, 
  (forall x z, clos_refl_trans X T z y -> 
               clos_trans_1n X T x z /\ R z x -> False) ->
  SecureBy R p -> Acc T y.
Proof.
intros X p. induction p.
intros. simpl in H0. 
apply Acc_intro. intros. edestruct (H y0 y). 
apply rt_refl. split. constructor 1. apply H1. apply H0.
intros. 
apply Acc_intro. intros z HT. 
simpl in H1. remember (H1 y). 
eapply H with (R := fun y0 z => R y0 z \/ R y y0). 
2: apply s. intros. simpl in H2.
simpl in H3. destruct H3. destruct H4.
eapply H0. eapply trans_clos_left. apply HT. apply H2.
split. apply H3. apply H4. eapply H0. eapply trans_clos_left. 
apply HT. apply H2. split. apply H3. 
destruct (H0 z0 y). apply rt_refl. split. 2: apply H4. 
eapply trans_clos_left_aux. apply HT. apply H2.
Defined.

(* WfFromAf *)
Lemma wf_from_af : 
   forall (X:Type) (p : WFT X) 
   (R : X -> X -> Prop) (T : X -> X -> Prop), 
   (forall x y, clos_trans_1n X T x y /\ R y x -> False) 
    -> SecureBy R p -> well_founded T.
Proof.
intros. unfold well_founded. intro y. 
eapply acc_from_af. 2: apply H0.
intros. eapply H. apply H2.
Defined.

(* A reassuring lemma *)
(* WfFromWqo *)
Lemma wf_from_wqo : 
  forall (X:Type) (p : WFT X) (R : X -> X -> Prop), 
         transitive X R -> SecureBy R p -> 
         well_founded (fun x y => R x y /\ not (R y x)).
Proof.
intros.
apply wf_from_af with (R := R) (p := p). 
intros. destruct H1. 
assert (~ R y x).
induction H1. destruct H1. apply H3.
unfold not in *. intros. apply IHclos_trans_1n. destruct H1.
apply (H _ _ _ H4 H1). destruct H1.
apply (H _ _ _ H4 H1). unfold not in H3. apply H3. apply H2. apply H0.
Qed.
