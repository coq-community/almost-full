Require Import Wf_nat.
Require Import Arith.
Require Import Omega.
Require Import Wellfounded.
Require Import List.
Require Import Relations.
Require Import Logic.

Require Import AlmostFull.
Require Import AlmostFullInduction.
Require Import AFConstructions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.


Section Lexicographic.

(* Lexicographic orders:
 * flex (Z,_) = 1 
 * flex (_,Z) = 1 
 * flex (S x, S y) = f(x,S (S y)) + f(S x, y)
 *************************************************) 
Definition flex : forall (x:nat*nat), nat.
pose (T x y := fst x < fst y \/ (fst x = fst y /\ snd x < snd y)).
pose (R x y := fst x <= fst y /\ snd x <= snd y).
eapply af_induction with (T := T) (R := R).
(* prove almost_full *)
apply af_product; repeat (apply leq_af).
(* prove intersection emptyness *)
intros x y (CT,H). induction CT. firstorder.
assert (fst y <= fst z). clear H IHCT. induction CT; repeat firstorder.
firstorder.
(* give the functional *) 
refine (fun x => match x as w return (forall y, T y w -> nat) -> nat with 
                   | (O,_) => fun frec => 1
                   | (_,O) => fun frec => 1 
                   | (S a,S b) => fun frec => (@frec (a,S (S b)) _ + @frec (S a,b) _)%nat
                 end); unfold T in *; auto with arith.
Defined.

(* Slightly more complicated: 
 * 
 * grok (Z,_) = 1 
 * grok (_,Z) = 1
 * grol (S x, S y) = grok (S y, y) + grok(x,x) 
 ****************************************************)
Definition grok : forall (x:nat*nat), nat. 
pose (T x y := (fst x <= snd y /\ snd x < snd y) \/ 
               (snd x < fst y /\ fst x < fst y)).
pose (R x y := fst x <= fst y /\ snd x <= snd y).
apply af_induction with (T := T) (R := R).
(* prove almost_full *)
apply af_product; repeat (apply leq_af).
(* prove intersection emptyness *)
intros x y (CT,H).
assert (T x y). clear H. 
induction CT; firstorder. firstorder.
(* give the functional *) 
refine (fun x => match x as w return (forall y, T y w -> nat) -> nat with 
                   | (O,_) => fun frec => 1
                   | (_,O) => fun frec => 1 
                   | (S a,S b) => fun frec => (@frec (S b,b) _ + @frec (a,a) _)%nat
                 end); unfold T in *; auto with arith.
Defined.

End Lexicographic.

Section Ranking.
(* Argument flipping by cheating (cofmap)
 *
 * flip (Z,_) = 1 
 * flip (_,Z) = 1 
 * flip (S x, S y) = flip (S y,x)
 ***********************************************)

Definition flip1 : forall (x:nat*nat), nat.
pose (T x y := fst x <= snd y /\ snd x < fst y).
pose (R x y := fst x + snd x <= fst y + snd y).
apply af_induction with (T := T) (R := R).
(* prove almost_full *)
apply af_cofmap with (f := fun z => (fst z + snd z)%nat). apply leq_af.
(* prove intersection emptyness *)
intros x y (CT,H).
assert (fst x + snd x < fst y + snd y). clear H.
induction CT. unfold T in *. firstorder. unfold T in *. omega.
unfold R in *. omega.
(* give the functional *) 
refine (fun x => match x as w return (forall y, T y w -> nat) -> nat with 
                   | (O,_) => fun frec => 1
                   | (_,O) => fun frec => 1 
                   | (S a,S b) => fun frec => @frec (S b,a) _ 
                 end); unfold T in *; auto with arith.
Defined.

End Ranking.



Section ArgFlip.

(* Argument flipping with no cheating (no cofmap) 
 *
 * flip (Z,_) = 1 
 * flip (_,Z) = 1 
 * flip (S x, S y) = flip (y,x)
 ****************************************************)

Definition flip2 : forall (x:nat*nat), nat.
pose (T x y := fst x < snd y /\ snd x < fst y).
pose (R x y := fst x <= fst y /\ snd x <= snd y).
eapply af_power_induction with (T := T) (R := R) (k := 2).
omega.
(* prove almost_full *) 
apply af_intersection. apply af_cofmap. apply leq_af.
apply af_cofmap; apply leq_af.
(* prove (power 2) intersection emptyness *)
intros x y (CT,Ryx). induction CT. 
  unfold T in *; unfold R in *. simpl in H. destruct H. destruct H.
  destruct H. destruct H0. destruct H0. destruct H0. destruct Ryx. subst x1. firstorder.
  assert (fst x < fst y /\ snd x < snd y). simpl in H. destruct H.
  unfold T in H. destruct H. destruct H0. destruct H0.
  clear CT. clear IHCT. subst x1. clear Ryx. destruct H; destruct H0. firstorder.
  unfold R in *. clear CT. firstorder.
(* give the functional *) 
refine (fun x => match x as w 
                 return (forall y, T y w -> nat) -> nat with
                 | (O,_) => fun frec => 1
                 | (_,O) => fun frec => 1 
                 | (S x, S y) => fun frec => frec (y,x) _
                end); firstorder.
Defined.

End ArgFlip.


Section SCT.
(* An example from size-change termination
 * [From Amir Ben-Amram's paper General Size-Change Termination and lexicographic descent]
 * gnlex (x,Z)     = 1 
 * gnlex (Z,y)     = 1
 * gnlex (S x,S y) = gnlex (S y, y) + gnlex (S y, x) 
 *******************************************************************************************)

(*=GNLexRelations *)
Definition T x y := (fst x = snd y /\ snd x < snd y) \/ 
                      (fst x = snd y /\ snd x < fst y).
Definition R x y := fst x <= fst y /\ snd x <= snd y.
(*=End *)
Lemma T2_invariant: 
  forall x y, power 2 T x y ->   
    fst x < fst y /\ snd x < fst y \/ 
    snd x < snd y /\ fst x < snd y \/ 
    fst x < fst y /\ snd x < snd y.
intros x y T2.
destruct T2 as (z,(Txz,(z0,(Tzz0,Zeq)))). unfold T in *.
simpl in Zeq.
destruct Txz as [T1 | T2]; destruct Tzz0 as [S1 | S2]; subst z0.
right; left; firstorder.
left; firstorder.
right; left; firstorder.
right; right; firstorder.
Defined.

Lemma T2_ct_invariant: 
  forall x y, clos_trans_1n _ (power 2 T) x y ->   
    fst x < fst y /\ snd x < fst y \/ 
    snd x < snd y /\ fst x < snd y \/ 
    fst x < fst y /\ snd x < snd y.
intros x y CT.
induction CT. 
(* base case *) 
apply T2_invariant; assumption.
(* inductive case *)  
remember (T2_invariant H) as G; clear HeqG CT H.
destruct G as [G1 | [G2 | G3]]; destruct IHCT as [IH1 | [IH2 | IH3]].
(* a little combinatorial search *)
  left; firstorder. 
  right; left; firstorder.
  left; firstorder.
  left; firstorder.
  right; left; firstorder.
  right; left; firstorder.
  left; firstorder.
  right; left; firstorder.
  right; right; firstorder.
Defined.

(*=GNLex *)
Definition gnlex_pow2 : forall (x:nat*nat), nat.
apply af_power_induction with (T:=T) (R:=R) (k:=2). omega.
(* prove almost_full *) 
apply af_intersection; 
   repeat (apply af_cofmap; apply leq_af).
(* prove intersection emptyness *) 
intros x y (CT,HR).
destruct (T2_ct_invariant CT); repeat firstorder.
(* give the functional *) 
refine (fun x => match x as w 
         return (forall y, T y w -> nat) -> nat with
         | (O,_) => fun frec => 1
         | (_,O) => fun frec => 1 
         | (S x, S y) => fun frec => (frec (S y, y) _ + frec (S y, x) _)%nat
                end).
unfold T in *. left. simpl; omega.
unfold T in *. right. simpl; omega.
Defined.
(*=End *)


Lemma T_empty_intersect: forall x y, 
        clos_trans_1n _ T x y -> R y x -> False.
intros x y CT HR.
assert (T x y \/ clos_trans_1n (nat*nat) (power 2 T) x y \/ 
        exists z, T x z /\ clos_trans_1n _ (power 2 T) z y).
Focus 2.
destruct H.
destruct H. destruct HR. firstorder.
destruct HR. firstorder.
destruct H.
destruct (T2_ct_invariant H). destruct HR. firstorder.
destruct HR. firstorder.
destruct H. destruct H.
destruct (T2_ct_invariant H0). firstorder.
firstorder.
clear HR.
induction CT. left; auto.
destruct IHCT. right. left. constructor. exists y. auto. split. apply H. 
exists z. split. auto. auto. unfold power. reflexivity.
destruct H0. right. right. 
exists y. split. apply H. apply H0.
destruct H0. destruct H0. 
right. left. constructor 2 with (y := x0).
exists y. split. apply H. exists x0. split. auto. simpl. reflexivity.
apply H1.
Defined.



(*=GNLexSimple *)
Definition gnlex: forall (x:nat*nat), nat.
apply af_induction with (T:=T) (R:=R).
(* prove almost_full *) 
apply af_intersection; 
   repeat (apply af_cofmap; apply leq_af).
(* prove intersection emptyness *) 
intros x y (CT,HR).
apply (T_empty_intersect CT HR).
(* give the functional *) 
refine (fun x => match x as w 
         return (forall y, T y w -> nat) -> nat with
         | (O,_) => fun frec => 1
         | (_,O) => fun frec => 1 
         | (S x, S y) => fun frec => (frec (S y, y) _ + frec (S y, x) _)%nat
                end).
unfold T in *. left. simpl; omega.
unfold T in *. right. simpl; omega.
Defined.
(*=End *)

End SCT.

Section SumExample.

(*=FSumRelations *)
Definition Tfsum := fun x y => 
   (exists x0, x = inr nat (x0+2)%nat /\ y = inl nat (S x0)) \/ 
   (exists x0, x = inl nat (x0-2) /\ y = inr nat x0).
Definition Rfsum := sum_lift le le.
(*=End *)

Lemma fsum_pow2_empty:
   forall x y : nat + nat,
   clos_trans_1n (nat + nat) (power 2 Tfsum) x y /\ Rfsum y x -> False.
intros.
destruct H.
induction H.
- destruct H. destruct H. destruct H1. destruct H1.
  destruct H. destruct H. destruct H. subst x. subst x0.
  destruct y. destruct H0.
  destruct H1. destruct H. destruct H. inversion H.
  destruct H. destruct H. inversion H1. unfold Rfsum in H0. unfold sum_lift in H0.
  inversion H.
  subst.
  inversion H2.
  subst.
  firstorder.
  unfold Rfsum in H0. unfold sum_lift in H0.
 destruct H1. destruct H. destruct H. destruct H1. subst.
 destruct y; auto.
 destruct H1.
 subst.
 inversion H.
 subst.
 simpl in H2.
 inversion H2.
 subst.
 firstorder.
 destruct H1.
 destruct H1.
 simpl in H2.
 destruct y.
 subst.
 inversion H2.
 destruct x; auto.
 subst.
 destruct H.
 destruct H.
 inversion H.
- unfold Rfsum in *. unfold sum_lift in *.
  clear H1.
  destruct z.
  * destruct x; auto.    
    destruct y; subst.
    + inversion H.
      destruct H1.
      inversion H2.
      destruct H3.
      inversion H4.
      subst.
      clear H2 H4.
      inversion H3.
      destruct H2.
      destruct H2.
      subst.
      inversion H4.
      subst.
      inversion H1.
      destruct H2.
      destruct H2.
      inversion H5.
      destruct H2.
      destruct H2.
      inversion H5.
      subst.
      inversion H2.
      subst.
      firstorder.
      destruct H2.
      destruct H2.
      subst.
      inversion H4.
   + firstorder.
     subst.
     inversion H4.
     subst.
     inversion H4.
     subst.
     inversion H.
     subst.
     inversion H2.
     subst.
     inversion H4.
     inversion H.
     subst.
     inversion H.
     subst.
     inversion H4.
   * destruct x; auto.
     destruct y; subst.
    + inversion H.
      destruct H1.
      inversion H2.
      destruct H3.
      inversion H4.
      subst.
      clear H2 H4.
      inversion H3.
      destruct H2.
      destruct H2.
      subst.
      inversion H4.
      subst.
      inversion H1.
      destruct H2.
      destruct H2.
      inversion H5.
      destruct H2.
      destruct H2.
      inversion H5.
      subst.
      inversion H2.
      subst.
      destruct H2.
      destruct H2.      
      subst.
      inversion H4.
   + destruct H.
     destruct H.
     inversion H1.
     destruct H2.
     inversion H3.
     subst.
     clear H1 H3.
     inversion H; clear H.
     destruct H1.
     destruct H.
     subst.
     inversion H.
     subst.
     clear H.
     inversion H2; clear H2.
     destruct H.
     destruct H.
     inversion H.
     destruct H.     
     destruct H.
     inversion H.
     inversion H1.
     subst.
     firstorder.
     destruct H1.
     destruct H.
     inversion H.
Qed.

(* fsum (inl 0)     = 1
 * fsum (inl (S x)) = fsum (inr (x+2))
 * fsum (inr x)     = fsum (inl (x-2)) 
 ******************************************************)

(*=FSum *)
Definition fsum: forall (x:nat+nat), nat.
apply af_power_induction 
  with (T := Tfsum) (R := Rfsum) (k := 2). omega.
(* prove almost_full *)
apply af_sum_lift. apply leq_af. apply leq_af.
(* prove intersection emptyness *)
apply fsum_pow2_empty.
(* give the functional *)
refine (fun x => match x as w 
        return (forall y, Tfsum y w -> nat) -> nat with 
        | inl O => fun frec => 1
        | inl (S x) => fun frec => frec (inr nat (x+2)%nat) _
        | inr x => fun frec => frec (inl nat (x-2)) _ 
        end).
left. exists x. intuition.
right. exists x. intuition.
Defined.
(*=End *)

End SumExample.



Section MutualInduction.

(* Here is an interesting example of mutual induction
    f x = g (x+1) + f (x-1) 
    g z = f (z-2)
 **********************************)
Definition TA := fun x y  => x < y.
Definition SB := fun x y  => x = S y.
Definition TB := fun (x:nat) (y:nat) => False. 
Definition SA := fun x y  => y = S (S x).

Definition funny_compare := fun x y => 
  match (x,y) with 
  | (inl x, inl y) => x < y
  | (inr x, inl y) => x <= y \/ x = (y+1)%nat
  | (inl x, inr y) => x + 2 <= y
  | (inr x, inr y) => x <= y
  end.

Lemma funny_compare_lemma: 
   forall x y,  clos_trans_1n (nat+nat) (lift_rel_union TA TB SA SB) x y -> 
                funny_compare x y.
intros. induction H.
destruct x; destruct y; unfold funny_compare in *; simpl in *.
unfold TA in *; firstorder.
unfold SA in *; firstorder.
unfold SB in *; firstorder.
unfold TB in *; firstorder.
destruct x; destruct y; destruct z; unfold funny_compare in *; simpl in *.
unfold TA in *; firstorder.
unfold TA in *; firstorder.
unfold SA in *; firstorder.
unfold SA in *; firstorder.
unfold SB in *; firstorder.
unfold SB in *; firstorder.
unfold TB in *; firstorder.
unfold TB in *; firstorder.
Defined.


Definition f_and_g : (nat -> nat) * (nat -> nat).
eapply af_mut_induction 
  with (R := sum_lift le le)
       (TA := TA)
       (SA := SA) 
       (TB := TB) 
       (SB := SB).
(* prove almost_full *)
apply af_sum_lift; apply leq_af.
(* prove intersection emptyness *)
intros x y (CTxy,Ryx). 
induction CTxy. destruct x; destruct y; unfold lift_rel_union in *; unfold sum_lift in *.
   unfold TA in *; firstorder. destruct Ryx. destruct Ryx. 
   unfold TB in *; firstorder.
assert (funny_compare y z). apply funny_compare_lemma. apply CTxy; clear CTxy.
destruct x; destruct y; destruct z; unfold funny_compare in *; simpl in *.
unfold TA in *; firstorder. 
unfold sum_lift in *; firstorder. 
unfold TA in *; firstorder.
unfold SA in *; firstorder.
unfold sum_lift in *; firstorder.
unfold sum_lift in *; firstorder.
unfold SA in *; firstorder. 
unfold SB in *; firstorder.
unfold SB in *; firstorder. 
unfold sum_lift in *; firstorder.
unfold TB in *; firstorder. 
unfold TB in *; firstorder.
(* give the functionals *)
  refine (fun x => match x as w return (forall y, TA y w -> nat) -> (forall y, SB y w -> nat) -> nat with 
                    | O   => fun self_rec other_rec => 1 
                    | S x => fun self_rec other_rec => (@self_rec x _ + @other_rec (S (S x)) _)%nat
                   end). firstorder. unfold TA. firstorder. unfold SB. auto.
  refine (fun x => match x as w return (forall y, TB y w -> nat) -> (forall y, SA y w -> nat) -> nat with 
                    | O       => fun self_rec other_rec => 1
                    | S O     => fun self_rec other_rec => 1 
                    | S (S x) => fun self_rec other_rec => @other_rec x _
                   end). firstorder. 
Defined.

End MutualInduction.
