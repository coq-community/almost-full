Require Import Wf_nat.
Require Import Arith.
Require Import Lia.
Require Import Wellfounded.
Require Import List.
Require Import Relations.
Require Import Logic.

From AlmostFull.Default Require Import AlmostFull.
From AlmostFull.Default Require Import AFConstructions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.


(****************************************************************
 *                                                              * 
 *  af_induction principle                                      *
 *                                                              * 
 ****************************************************************)



(*=AfInduction *)
Theorem af_induction:
   forall (A:Set) (T : A -> A -> Prop) (R : A -> A -> Prop), 
   almost_full R -> 
   (forall x y, clos_trans_1n A T x y /\ R y x -> False) -> 
   forall P : A -> Set, 
         (forall x, (forall y, T y x -> P y) -> P x)
          -> forall a, P a.
(*=End *)
Proof.
intros A T R AF Disj P g.
apply well_founded_induction with (R := T).
destruct AF as (p,HSec); apply wf_from_af with (R := R) (p := p).
apply Disj. apply HSec. apply g.
Defined.

Check af_induction.
Check well_founded_induction.

(* A very simple test that the fixpoint combinator /indeed/ gives us a fixpoint *)
(*=Fibonacci *)
Definition fib : nat -> nat.
apply af_induction with (T := lt) (R := le).
(* (i) Prove <= is AF *)
apply leq_af.
(* (ii) Prove intersection emptyness *)
intros x y (CT,H). induction CT; try lia.
(* (iii) Give the functional *)
refine (fun x => 
  match x as w return (forall y, y < w -> nat) -> nat with 
    | O => fun frec => 1
    | 1 => fun frec => 1
    | (S (S x)) => fun frec => (frec (S x) _  + frec x _)%nat
  end); firstorder.
Defined.

Print fib.
(*=End *)

Eval compute in (fib 0). (* 1 *) 
Eval compute in (fib 1). (* 1 *)
Eval compute in (fib 2). (* 2 *)
Eval compute in (fib 3). (* 3 *)
Eval compute in (fib 4). (* 5 *)
Eval compute in (fib 5). (* 8 *)


(****************************************************************
 *                                                              * 
 * A principle more akin to size-change-termination             *
 *                                                              * 
 ****************************************************************)


(* Power of a relation *) 
Fixpoint power n X (R : X -> X -> Prop) (x y:X) :=
  match n with 
  | O => x = y
  | S m => exists z, R x z /\ power m R z y
  end.

(* Addition modulo k *) 
Fixpoint plus_mod_aux k n (x:nat) := 
 match n with 
 | O => x 
 | S m => match (k - S x) with 
          | O => plus_mod_aux k m O 
          | _ => plus_mod_aux k m (S x) 
          end 
 end.

(* Interesting lemmas about addition modulo k *) 
Lemma plus_mod_aux_fin k n (x:nat):
  (x < k) -> plus_mod_aux k n x < k.
generalize dependent k. generalize dependent x.
induction n. auto. intros. simpl. destruct k. lia.
simpl. destruct (eq_nat_dec (S k) (S x)). auto. inversion e.
rewrite minus_diag.  apply IHn. auto. lia.
assert (k - x <> O). lia. set (k - x) as diff.
fold diff in H0. destruct diff. firstorder.
apply IHn. lia. Defined.


Lemma plus_mod k (n:nat) (x:Finite k) : Finite k.
inversion x.
refine (@FinIntro k (plus_mod_aux k n x0) _). apply plus_mod_aux_fin. apply H.
Defined.

Lemma plus_mod_lt (m:nat): 
  forall k n, m+n < k -> plus_mod_aux k m n = (m+n)%nat.
induction m. firstorder. intros. simpl. 
remember (k - S n) as j. 
destruct j. lia.
assert (S (m + n) = (m + (S n))%nat). Focus 2. rewrite H0. apply IHm. lia.
lia. Defined.

Lemma plus_mod_gt (m:nat): 
   forall k x, k > 0 -> m < k -> x < k -> k <= m+x -> plus_mod_aux k m x = m + x - k.
induction m.
lia.
intros. 
simpl. remember (k - S x) as diff. destruct diff.
destruct k. lia.
assert (x = k). lia. subst x.
assert (plus_mod_aux (S k) m O = (m + O)%nat). apply plus_mod_lt. lia.
rewrite H3. lia.
destruct k. lia.
assert (plus_mod_aux (S k) m (S x) = m + (S x) - (S k)).
apply IHm. lia. lia. lia. lia.
rewrite H3. lia.
Defined.

Lemma plus_mod_diff: 
   forall m k x, k > 1 -> m > 0 -> x < k -> m < k -> x <> plus_mod_aux k m x.
intros.
destruct (le_lt_dec k (m+x)).
assert (plus_mod_aux k m x = m + x - k). 
apply plus_mod_gt. lia. lia. lia. lia.
rewrite H3. lia.
assert (plus_mod_aux k m x = (m + x)%nat). apply plus_mod_lt. lia. 
rewrite H3. lia.
Defined.

Lemma plus_mod_wraparound (m:nat):
 forall x n, x < m -> n > 0 -> 
     plus_mod_aux (n + m) m (n + x) = x.
induction m. lia. intros. simpl.
remember (n + S m - (S (n + x))) as diff.
destruct diff. 
assert (m = x). lia. rewrite H1.
assert (plus_mod_aux (n + S x) x O = (x + O)%nat). apply plus_mod_lt. lia.
lia.
assert (plus_mod_aux (S n + m) m (S n + x) = x).
apply IHm. lia. lia. 
assert ((S n + m)%nat = (n + S m)%nat). lia. rewrite <- H2.
assert (S (n+x) = (S n + x)%nat). lia. rewrite H3. apply H1.
Defined.

Lemma plus_mod_suc m: 
 forall x, x < m -> 
     plus_mod_aux (S m) m (S x) = x.
intros. assert (S m = (1 + m)%nat). firstorder. rewrite H0. 
assert (S x = (1 + x)%nat). firstorder. rewrite H1. apply plus_mod_wraparound. firstorder.
firstorder.
Defined.


Lemma ctr_from_ct X (T : X -> X -> Prop): 
 forall x y, 
 clos_trans_1n X T x y -> clos_refl_trans X T x y.
intros x y CT. induction CT. constructor 1. apply H.
econstructor 3. constructor 1. apply H. apply IHCT. Defined.

Lemma ct_from_ctr X (T : X -> X -> Prop): 
  forall x y z, 
  clos_trans X T x y -> 
  clos_refl_trans X T y z -> clos_trans_1n X T x z.
intros x y z Txy CTR.
induction CTR. apply clos_trans_t1n. apply clos_tn1_trans. 
econstructor 2. apply H. apply clos_trans_tn1. apply Txy. 
apply clos_trans_t1n. apply Txy. apply IHCTR2. apply clos_t1n_trans. 
apply IHCTR1. apply Txy.
Defined.

(* Some lemmas about composing diagonally *) 
Lemma diag_pow_decomp k X T: 
 forall x y, k > 1 -> 
 clos_trans_1n _ (@lift_diag k X T) x y -> 
    exists m, m < k /\ (eq_fin (fst y) (@plus_mod k m (fst x))) /\ 
      ((m = O /\ clos_trans_1n _ (power k T) (snd x) (snd y)) \/
      ((m > 0 /\ exists z: Finite k * X, power m T (snd x) (snd z) /\ clos_refl_trans _ (power k T) (snd z) (snd y)))).
intros x y kGt. 
intro CT.
induction CT. 
unfold lift_diag in H. unfold next_fin in H. simpl in H.
destruct x as ((kx,Hx),x). 
destruct y as ((ky,Hy),y). simpl in H.
exists 1. split. firstorder. split. destruct H. destruct H. destruct H. subst k.
unfold plus_mod. unfold fst. unfold eq_fin. auto. unfold plus_mod_aux. simpl. 
rewrite minus_diag. apply H1. unfold plus_mod. unfold fst. unfold eq_fin.
auto. unfold plus_mod_aux. remember (k - S kx) as diff. destruct diff.
lia. lia. right. split. lia. 
exists (@FinIntro k ky Hy, y).
split. simpl. exists y. firstorder.
simpl. apply rt_refl.
destruct IHCT as (m,(MltK,(HEqfin,G))).
destruct G. destruct H0. subst m.
destruct x as ((kx,Hx),x).
destruct y as ((ky,Hy),y).
destruct z as ((kz,Hz),z).
unfold fst in *. unfold snd in *. unfold lift_diag in H. unfold fst in *. unfold snd in *.
simpl in H. unfold next_fin in H. destruct H. 
unfold plus_mod in HEqfin. unfold eq_fin in HEqfin. 
exists (S O). split. lia. split. unfold plus_mod. unfold eq_fin.
destruct H. destruct H. subst ky.  simpl in HEqfin. subst kz. simpl.
remember (k - S kx) as diff. destruct diff. auto. lia. simpl.
destruct H. subst ky.  simpl in HEqfin. subst kz.
remember (k - S kx) as diff. destruct diff. lia. reflexivity.
right. split. auto. 
exists (@FinIntro k ky Hy,y). split. simpl. exists y. split. apply H0. reflexivity.
apply ctr_from_ct. apply H1.
destruct H0. destruct H1. destruct H1.

destruct (eq_nat_dec k (S m)).
  (* Case that we have to wrap-around *)
exists O. split. lia. split.
Focus 2. left.
assert (power k T (snd x) (snd x0)).
subst k. simpl. exists (snd y). split. destruct H. apply H3.
apply H1. split. reflexivity.
eapply ct_from_ctr. Focus 2. apply H2. Unfocus.
Focus 2. 
constructor 1.
subst k. simpl. exists (snd y). split. destruct H. apply H4. apply H1.
destruct x as ((kx,Hx),x).
destruct y as ((ky,Hy),y).
destruct z as ((kz,Hz),z).
unfold fst. 
unfold plus_mod. simpl. unfold eq_fin. unfold fst in HEqfin. 
unfold plus_mod in HEqfin. unfold eq_fin in HEqfin. subst kz. subst k. 
unfold lift_diag in H. unfold fst in H. unfold snd in H. unfold next_fin in H.
simpl in H. destruct H. destruct H. destruct H. subst ky. inversion H.
assert (plus_mod_aux (S m) m O = (m + O)%nat). apply plus_mod_lt. lia.
rewrite H4. auto. destruct H. subst ky. 
apply plus_mod_suc. lia. 
  (* No wraparound needed here *)
Show. 
exists (S m). split.  lia.
split. Focus 2. right. split. lia. 
exists x0. split. simpl. exists (snd y). split. destruct H. apply H3.
apply H1. apply H2.

destruct x as ((kx,Hx),x).
destruct y as ((ky,Hy),y).
destruct z as ((kz,Hz),z).
unfold fst. unfold plus_mod. unfold eq_fin. unfold plus_mod in HEqfin. 
unfold fst in *. unfold snd in *. unfold eq_fin in HEqfin. subst kz.
unfold lift_diag in H. unfold fst in H. unfold snd in H. destruct H.
unfold next_fin in H. destruct H. destruct H. subst. 
simpl. rewrite minus_diag. reflexivity. simpl.
destruct H. subst ky. 
remember (k - S kx) as diff. destruct diff. lia. reflexivity.
Defined.

Lemma diag_pow_decomp_mod k X T: 
 forall x y, k > 1 -> 
 clos_trans_1n _ (@lift_diag k X T) x y -> 
    clos_trans_1n X (power k T) (snd x) (snd y) /\ eq_fin (fst x) (fst y) \/ 
    not (eq_fin (fst x) (fst y)).
intros x y kGt CT. 
destruct (diag_pow_decomp kGt CT) as (m,H).
destruct H. destruct H0. destruct H1.
destruct H1. subst m. left. split. apply H2. destruct x. destruct y. unfold fst in *. unfold snd in *. simpl. 
unfold plus_mod in H0. destruct f. destruct f0. unfold eq_fin in *. simpl in H0. auto.
right. destruct H1. destruct x. destruct y. unfold plus_mod in H0. unfold fst in *. unfold snd in *.
destruct f. destruct f0. unfold eq_fin in *. subst x2.
apply plus_mod_diff. firstorder. firstorder. firstorder. apply H.
Defined.

Lemma af_power_induction_non_trivial: 
  forall (A:Set) k
  (T : A -> A -> Prop) 
  (R : A -> A -> Prop), 
  k > 1 -> almost_full R -> 
 (forall x y, @clos_trans_1n _ (power k T) x y /\ R y x -> False) -> 
 forall P : A -> Set, 
 (forall x, (forall y, T y x -> P y) -> P x) -> 
 forall x, P x.
intros X k T R kGt afR Hct P frec.
assert (forall (x: Finite k * X), P (snd x)).
apply af_induction with (T := @lift_diag k X T) (R := @lift_pointwise k X R).
(* Almost Full condition *)
unfold lift_pointwise; apply af_intersection. 
apply af_cofmap; apply af_finite. apply af_cofmap; apply afR.
(* Intersection emptyness *)
intros x y (CTxy,Tyx). 
induction CTxy. unfold lift_diag in H. unfold lift_pointwise in Tyx.
unfold next_fin in H.
destruct x. destruct y. simpl in H. destruct f. destruct f0. simpl in Tyx.
destruct H. unfold eq_fin in H. unfold eq_fin in Tyx. lia.
destruct x as ((kx,Hx),x).
destruct y as ((ky,Hy),y).
destruct z as ((kz,Hz),z).
unfold lift_diag in H. unfold next_fin in H. simpl in H. destruct H as (H2,H4).
unfold lift_pointwise in Tyx. simpl in Tyx. unfold eq_fin in Tyx. destruct Tyx as (H3,H5).
assert (clos_trans_1n X (power k T) x z /\ kx = kz \/ (kx <> kz)).
assert (@clos_trans_1n (Finite k * X) (@lift_diag k X T) 
                        (FinIntro (k:=k) (x:=kx) Hx, x) 
                        (FinIntro (k:=k) (x:=kz) Hz, z)).
constructor 2 with (y := (@FinIntro k ky Hy,y)).
unfold lift_diag. unfold fst. unfold snd. split. unfold next_fin.
apply H2. apply H4. apply CTxy.
destruct (diag_pow_decomp_mod kGt H). simpl in H0.
destruct H0. left. split. apply H0. unfold eq_fin in H1. apply H1.
unfold eq_fin in H0. unfold fst in H0. right. apply H0. 
firstorder.
(* Functional requirement *)
intros. destruct x as ((kx,Hx),x). unfold snd.
apply frec. intros. 
destruct kx.
  (* kx = O *) 
  assert (k-1 < k). lia.
  intros. apply (H (@FinIntro k (k-1) H1,y)). simpl. 
  unfold lift_diag. unfold fst. unfold snd. split. unfold next_fin. lia. apply H0.
  (* Now it is an (S kx) *) 
  assert (kx < k). lia.
  intros. apply (H (@FinIntro k kx H1,y)). simpl. unfold lift_diag. simpl. split. 
  simpl. unfold next_fin. right. lia. apply H0.
(* Show the goal *)
intros. apply frec. intros. apply (H (@FinIntro k 1 kGt, y)).
Defined.


(*=AfPowerInduction *)
Lemma af_power_induction: 
  forall (A:Set) k
  (T : A -> A -> Prop) (R : A -> A -> Prop), 
  k >= 1 -> almost_full R -> 
  (forall x y,
    clos_trans_1n A (power k T) x y /\ R y x -> False) -> 
  forall P : A -> Set, 
  (forall x, (forall y, T y x -> P y) -> P x) -> 
  forall x, P x.
(*=End *)
intros.
destruct (le_lt_dec k 1). assert (k = 1). lia. 
apply af_induction with (T := T) (R := R). apply H0. 
intros. eapply H1. split. Focus 2. destruct H4. apply r. 
subst k. simpl. 
destruct H4. clear H4 H H1 l. induction H3. constructor. exists y. auto.
constructor 2 with (y := y). exists y. auto. auto.
apply H2. 
apply af_power_induction_non_trivial with (k := k) (T := T) (R := R).
lia. assumption. assumption. assumption.
Defined.



(****************************************************************
 *                                                              * 
 * A particular mutual induction principle                      *
 *                                                              * 
 ****************************************************************)

Definition lift_rel_union (A:Set) (B:Set) 
                          (TA : A -> A -> Prop) (TB : B -> B -> Prop)
                          (SA : A -> B -> Prop) (SB : B -> A -> Prop) 
                          (x : A + B) 
                          (y : A + B) : Prop.
destruct x as [xl|xr]. 
destruct y as [yl|yr]. apply (TA xl yl). apply (SA xl yr).
destruct y as [yl|yr]. apply (SB xr yl). apply (TB xr yr).
Defined. 

(*=AfInduction *)

Check clos_trans_1n.

Lemma af_mut_induction_aux:
   forall (A:Set) (B:Set) 
          (TA : A -> A -> Prop) (SA : A -> B -> Prop) 
          (TB : B -> B -> Prop) (SB : B -> A -> Prop)
          (R : A + B -> A + B -> Prop),
          almost_full R -> 
          (forall x y, @clos_trans_1n (A+B) (@lift_rel_union _ _ TA TB SA SB) x y /\ R y x -> False) -> 
          forall (P : A -> Set) (Q : B -> Set),
             (forall x : A, (forall y, TA y x -> P y) ->
                            (forall y, SB y x -> Q y) -> P x) -> 
             (forall x : B, (forall y, TB y x -> Q y) -> 
                            (forall y, SA y x -> P y) -> Q x) ->  
          forall a: A+B, match a with 
                         | inl l => P l
                         | inr r => Q r
                         end.
intros A B TA SA TB SB R Raf HTrans P Q fA fB.
apply af_induction with (R := R) (T := @lift_rel_union _ _ TA TB SA SB).
apply Raf. intros. eapply HTrans. apply H. intros.
destruct x. apply fA. intros. remember (H (inl _ y)). simpl in y0. apply y0. apply H0.
intros. remember (H (inr _ y)). simpl in y0. apply y0. apply H0.
apply fB. intros. remember (H (inr _ y)). simpl in y0. apply y0. apply H0.
intros. remember (H (inl _ y)). simpl in y0. apply y0. apply H0. 
Defined.

Lemma af_mut_induction:
   forall (A:Set) (B:Set) 
          (TA : A -> A -> Prop) (SA : A -> B -> Prop) 
          (TB : B -> B -> Prop) (SB : B -> A -> Prop)
          (R : A + B -> A + B -> Prop),
          almost_full R -> 
          (forall x y, @clos_trans_1n (A+B) (@lift_rel_union _ _ TA TB SA SB) x y /\ R y x -> False) -> 
          forall (P : A -> Set) (Q : B -> Set),
             (forall x : A, (forall y, TA y x -> P y) ->
                            (forall y, SB y x -> Q y) -> P x) -> 
             (forall x : B, (forall y, TB y x -> Q y) -> 
                            (forall y, SA y x -> P y) -> Q x) ->  
          (forall a, P a) * (forall b, Q b).
intros. 
assert (forall a:A+B, match a with 
                      | inl l => P l 
                      | inr r => Q r
                      end).
eapply af_mut_induction_aux. apply H. apply H0. apply H1. apply H2.
split. intros. remember (H3 (inl _ a)). auto. 
intros. remember (H3 (inr _ b)). auto.
Defined.
