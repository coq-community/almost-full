Require Import Wf_nat.
Require Import Arith.
Require Import Omega.
Require Import Wellfounded.
Require Import List.
Require Import Relations.
Require Import Logic.

From AlmostFull.PropBounded Require Import AlmostFull.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.


(****************************************************************
 *                                                              * 
 *                           Unions                             * 
 *                                                              * 
 ****************************************************************)

(*=AfUnion *)
Corollary af_union: 
 forall (X:Set) (A B : X -> X -> Prop),
 almost_full A -> almost_full (fun x y => A x y \/ B x y).
(*=End *)
intros X A B afA. eapply af_strengthen. apply afA. auto.
Defined.


(****************************************************************
 *                                                              * 
 *                       Intersections                          * 
 *      (the intuitionistic version of Ramsey's theorem)        *
 *                                                              * 
 ****************************************************************)

(*=OplusNullaryLemma *)
Lemma oplus_nullary (X:Set) (A B : Prop) (R : X -> X -> Prop) : 
  almost_full R ->
  forall C, 
  (forall x y, R x y <-> C x y \/ A) ->
  almost_full (fun (x:X) (y:X) => C x y \/ B) ->
  almost_full (fun (x:X) (y:X) => C x y \/ A /\ B).
(*=End *)
intro afR. induction afR. intros. eapply af_strengthen. apply H1.
intros. simpl in H2. destruct H2. left. auto. 
assert (C x y \/ A). apply H0. apply H. destruct H3. left. auto.
right. auto.
intros. 
apply AF_SUP. intro x. 
eapply af_strengthen. 
eapply H0 with (x := x) (C := fun y z => C x y \/ C y z).
intros. split. intros. destruct H3. remember (H1 x0 y).
destruct i. destruct (o H3). left. right. apply H4.
right. apply H4. destruct (H1 x x0). destruct (H4 H3).
left. left. apply H6. right. apply H6. intros.
destruct H3. destruct H3. destruct (H1 x x0).
firstorder. destruct (H1 x0 y). left. apply H5. left. apply H3.
destruct (H1 x0 y). left. apply H5. right. apply H3.
eapply af_strengthen. apply H2. intros. simpl in H3. destruct H3.
left. right. apply H3. right. apply H3. intros.
simpl in H3. destruct H3. destruct H3. right. left. apply H3.
left. left. apply H3. right. right. apply H3.
Defined.

(*=OplusNullaryCor *)
Lemma oplus_nullary_cor (X:Set) (A B : Prop) (C : X -> X -> Prop) : 
  almost_full (fun x y => C x y \/ A) -> 
  almost_full (fun x y => C x y \/ B) -> 
  almost_full (fun x y => C x y \/ (A /\ B)).
(*=End *)
intros. apply oplus_nullary with (R := fun x y => C x y \/ A).
apply H. auto. intros. firstorder. apply H0. 
Defined.

(*=OplusUnaryLemma *)
Lemma oplus_unary (X:Set) (A B : X -> Prop):
  forall R, almost_full R -> 
  forall T, almost_full T -> 
  forall C, 
  (forall x y, R x y -> C x y \/ A x) -> 
  (forall x y, T x y -> C x y \/ B x) -> 
  almost_full (fun x y => C x y \/ (A x /\ B x)).
(*=End *)
intros R afR. induction afR.
  (* ZT *) 
  intros T afT C Req Teq.
  eapply af_strengthen. apply afT. intros.
  assert (C x y \/ B x). apply Teq; apply H0.
  assert (C x y \/ A x). apply Req; apply H.
  destruct H1. left; auto.
  destruct H2. left. auto. right; auto.
  (* SUP *) 
  intros T afT.
  induction afT.
    (* ZT *) 
    intros C Req Teq. 
    assert (almost_full R). apply AF_SUP; apply H. eapply (af_strengthen H2).
    intros. assert (C x y \/ A x). apply Req; apply H3.
    assert (C x y \/ B x). apply Teq; apply H1. 
    destruct H4. left. auto. destruct H5. left. auto. right; auto.
    (* SUP *)
    intros C Req Teq.
    apply AF_SUP; intro x0.
    assert (almost_full (fun y z : X => ((C y z \/ A y /\ B y) \/ C x0 y) \/ A x0 /\ B x0)).
    eapply oplus_nullary_cor.
    assert (almost_full R0). apply AF_SUP. apply H1.
    remember (H0 x0 R0 H3 (fun x y => C x y \/ C x0 x \/ A x0)) as G0. clear HeqG0. clear H0.
    eapply af_strengthen. apply G0.
    intros. clear G0. clear H2. destruct H0. assert (C x y \/ A x). apply Req. apply H0.
    destruct H2. left. left. auto. right. auto. assert (C x0 x \/ A x0). apply Req. auto.
    destruct H2. left. right. left. auto. left. right. right. auto.
    intros. clear G0. clear H2. assert (C x y \/ B x). apply Teq. apply H0.
    destruct H2. left. left. auto. right. auto.
    intros. simpl in H0. destruct H0. destruct H0. left. left. left. auto.
    destruct H0. left. right. auto. right. auto. left. left. right. auto.
    clear H0.
    remember (H2 x0 (fun x y => C x y \/ C x0 x \/ B x0)) as G0. clear HeqG0. clear H2.
    eapply af_strengthen. apply G0.
    clear G0. intros. assert (C x y \/ A x). apply Req. apply H0. destruct H2.
    left. left. auto. right. auto.
    clear G0. intros. destruct H0. assert (C x y \/ B x). apply Teq. apply H0.
    destruct H2. left. left. auto. right. auto.
    assert (C x0 x \/ B x0). apply Teq. apply H0. destruct H2. left. right. left. auto.
    left. right. right. auto.
    intros. simpl in H0. destruct H0. destruct H0. left. left. left. auto. destruct H0.
    left. right. auto. right. auto. left. left. right. auto.
    apply (af_strengthen H3). intros.
    destruct H4. destruct H4. destruct H4. left. left. auto.
    left. right. auto. right. left. auto. right. right. auto. 
Defined.


(*=OplusUnaryCor *)
Lemma oplus_unary_cor (X:Set) (A B : X -> Prop) (C : X -> X -> Prop):
  almost_full(fun x y => C x y \/ A x) ->
  almost_full(fun x y => C x y \/ B x) -> 
  almost_full (fun x y => C x y \/ (A x /\ B x)).
(*=End *)
intros. apply oplus_unary with (R := fun x y => C x y \/ A x) (T := fun x y => C x y \/ B x).
apply H. apply H0. intros. apply H1. intros. apply H1.
Defined.


(*=OplusBinaryLemma *)
Lemma oplus_binary (X:Set):
  forall A, almost_full A -> 
  forall B, almost_full B -> 
    @almost_full X (fun x y => A x y /\ B x y).
(*=End *)
intros A afA. induction afA.
  (* ZT *) 
  intros B afB. 
  apply (af_strengthen afB). intros. split. apply H. apply H0.
  (* SUP *)
  intros B afB. induction afB.
    (* ZT *) 
    assert (almost_full R). apply AF_SUP; apply H. 
    apply (af_strengthen H2). intros. split. apply H3. apply H1.
    (* SUP *)
    apply AF_SUP; intro x0.
    apply oplus_unary_cor.
    assert (almost_full R0). apply AF_SUP; apply H1.
    apply (af_strengthen (H0 x0 R0 H3)).
    intros. destruct H4. destruct H4. left. auto. right. auto.
    apply (af_strengthen (H2 x0)).
    intros. destruct H3. destruct H4. left. auto. right. auto.
Defined.

(*=AfIntersection *)
Corollary af_intersection (X:Set) (A B :X->X->Prop):
  almost_full A -> almost_full B -> 
  almost_full (fun x y => A x y /\ B x y).
(*=End *)
intros. apply oplus_binary. apply H. apply H0. 
Defined.

(****************************************************************
 *                                                              * 
 *                  Type-based constructions                    * 
 *                                                              * 
 ****************************************************************)





(* Cofmap 
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(*=CoFmapLemma *)
Corollary af_cofmap (X Y:Set) (f:Y->X) (R:X->X->Prop):
  almost_full R -> almost_full (fun x y => R (f x) (f y)).
(*=End *)
intro afR. 
induction afR. apply AF_ZT. intros. apply H.
apply AF_SUP. intro y. apply H0.
Defined.

(* Products  
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(*=AfProduct *) 
Lemma af_product (X : Set) (Y : Set) : 
  forall (A : X -> X -> Prop) (B : Y -> Y -> Prop), 
  almost_full A -> almost_full B -> 
  almost_full (fun x y => A (fst x) (fst y) /\ B (snd x) (snd y)).
(*=End *)
intros A B afA afB. 
apply(af_intersection (@af_cofmap _ _ (@fst X Y) A afA) 
                        (@af_cofmap _ _ (@snd X Y) B afB)).
Defined.

(*=AfProductLeft *)
Lemma af_product_left (X Y : Set) (A:X->X->Prop) : 
  almost_full A -> 
  almost_full (fun (x:X*Y) (y:X*Y) => A (fst x) (fst y)).
intros afA. 
apply (@af_cofmap _ _ (@fst X Y) A afA).
Defined.
(*=End *)

(* Booleans 
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(*=AfBool *)
Lemma af_bool : almost_full (@eq bool).
(*=End *)
apply AF_SUP. intro x. apply AF_SUP. intro y.
apply AF_SUP. intro z. apply AF_ZT.
intros. destruct x. destruct y. firstorder. firstorder.
destruct z. firstorder. firstorder. destruct y.
firstorder. destruct z. firstorder. firstorder. firstorder.
Defined.

(* Sums (through products)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
 
(*=SumLift *)
Definition sum_lift (X Y:Set) 
  (A:X->X->Prop) (B:Y->Y->Prop) (x:X+Y) (y:X+Y) := 
  match (x,y) with 
  | (inl x0, inl y0) => A x0 y0 
  | (inl x0, inr y0) => False 
  | (inr x0, inl y0) => False 
  | (inr x0, inr y0) => B x0 y0
  end.
(*=End *)

(*=LeftSumLift *)
Definition left_sum_lift (X Y:Set) (A:X->X->Prop) (x y : X+Y) := 
  match (x,y) with 
  | (inl x0, inl y0) => A x0 y0 
  | (inl x0, inr y0) => False 
  | (inr x0, inl y0) => False 
  | (inr x0, inr y0) => True
  end.
(*=End *)

(* Fixpoint left_sum_tree (X Y:Set) (p:WFT X)  *)
(*   : WFT (X+Y) :=  *)
(*   match p with  *)
(*     | ZT => SUP (fun x => SUP (fun y =>  *)
(*                           SUP (fun z => ZT (X+Y)))) *)
(*     | SUP f => SUP (fun x =>  *)
(*       match x with  *)
(*         | inl x0 => left_sum_tree Y (f x0) *)
(*         | inr x0 => SUP (fun y =>  *)
(*           match y with  *)
(*             | inl y0 => left_sum_tree Y (f y0) *)
(*             | inr y0 => ZT (X+Y) *)
(*           end) *)
(*       end) *)
(*   end. *)

(*=SecLeftSumTree *)
Lemma af_left_sum (X Y : Set) (A : X -> X -> Prop) : 
  @almost_full X A -> @almost_full (X+Y) (left_sum_lift A).
(*=End *)
intro afA.
induction afA.
   (* ZT *) 
   apply AF_SUP; intro x. apply AF_SUP; intro y. apply AF_ZT.
   intros. 
     destruct x;  (repeat (auto; firstorder)).  
     destruct y;  (repeat (auto; firstorder)).
     destruct x0; (repeat (auto; firstorder)).
     destruct y;  (repeat (auto; firstorder)).
     destruct x0; (repeat (auto; firstorder)).
   (* SUP *)
   apply AF_SUP; intro x.
   destruct x.
   apply (af_strengthen (H0 x)). intros.
   destruct y;  (repeat (auto; firstorder)).
   destruct x0; (repeat (auto; firstorder)).
   apply AF_SUP; intro z.
   destruct z. 
       apply (af_strengthen (H0 x)). intros.
       destruct x0; (repeat (auto; firstorder)).
       destruct y0; (repeat (auto; firstorder)).
       apply AF_ZT. intros.
       destruct x; (repeat (auto; firstorder)).
Defined.

(*=Transpose *)
Definition transpose (X Y:Set) (x:X+Y) : Y+X := 
  match x with 
  | inl x0 => inr _ x0 
  | inr x0 => inl _ x0
  end.
(*=End *)

(*=RightTranspose *)
Definition right_sum_lift (X Y:Set) (B:Y->Y->Prop) (x y:X+Y) := 
  left_sum_lift B (transpose x) (transpose y).
(*=End *)

(*=SecRightSumTree *)			      
Lemma af_right_sum (X Y : Set) (B : Y -> Y -> Prop) : 
  @almost_full Y B -> @almost_full (X+Y) (right_sum_lift B).
intros. unfold right_sum_lift. eapply af_cofmap. apply af_left_sum. apply H.
Defined.
(*=End *)

(*=AfSumLift *)
Corollary af_sum_lift (X Y : Set) : 
  forall (A : X -> X -> Prop) (B : Y -> Y -> Prop), 
  almost_full A -> almost_full B -> almost_full (sum_lift A B).
(*=End *)
intros A B afA afB.
assert (almost_full (fun x y => left_sum_lift A x y /\ right_sum_lift B x y)).
apply af_intersection. apply af_left_sum. apply afA. apply af_right_sum. apply afB.
apply (af_strengthen H). 
intros. destruct x; repeat firstorder. destruct y; repeat firstorder.
Defined.


(* Finite naturals 
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* Finite natural values in the range [0 ... k-1] that is, k inhabitants *)
Inductive Finite (k:nat) : Set := FinIntro x (_ : x < k).
Print Finite.

Definition next_fin k (x : Finite k) (y : Finite k) := 
  match (x,y) with 
  | (@FinIntro _ x Hn, @FinIntro _ y Hm) => (S x = k /\ y = O) \/ (S x < k /\ y = S x)
  end.

Definition eq_fin k (x:Finite k) (y:Finite k) := 
  match (x,y) with 
  | (@FinIntro _ x Hn, @FinIntro _ y Hm) => x = y
  end.

Definition lift_diag n X (R : X -> X -> Prop) := 
  fun (x : Finite n * X) (y : Finite n * X) => 
  next_fin (fst x) (fst y) /\ R (snd x) (snd y).

Definition lift_pointwise n X (R : X -> X -> Prop) := 
  fun (x : Finite n * X) (y : Finite n * X) => 
  eq_fin (fst x) (fst y) /\ R (snd x) (snd y).

(*=LeqAF *)
Lemma leq_af : almost_full le.
(*=End *)
assert (almost_full (fun x y => not (y < x))).
apply af_from_wf. apply lt_wf. unfold dec_rel.
intros. destruct (le_lt_dec x y). firstorder. firstorder.
apply (af_strengthen H). intros. firstorder.
Defined. 

Lemma af_finite (k:nat) : almost_full (@eq_fin k).
set (f1 (x:Finite k) := match x with 
                        | @FinIntro _ kx _ => kx
                        end).
set (f2 (x:Finite k) := match x with 
                        | @FinIntro _ kx _ => k - kx
                        end).
assert (almost_full (fun x y => f1 x <= f1 y /\ f2 x <= f2 y)).
apply af_intersection. apply af_cofmap. apply leq_af.
                       apply af_cofmap. apply leq_af.
apply (af_strengthen H). intros. destruct H0. firstorder.
destruct x. destruct y. firstorder. unfold eq_fin. firstorder.
simpl in *. firstorder.
Defined.
