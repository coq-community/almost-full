From Coq Require Import Wf_nat.
From Coq Require Import Arith.
From Coq Require Import Lia.
From Coq Require Import Wellfounded.
From Coq Require Import List.
From Coq Require Import Relations.

From AlmostFull.Default Require Import AlmostFull.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.

(* **************************************************************
 *                                                              * 
 *                           Unions                             * 
 *                                                              * 
 ****************************************************************)

(* SecUnion *)
Lemma sec_union (X:Type) (A:X->X->Prop) (B:X->X->Prop): 
 forall p, SecureBy A p -> 
   SecureBy (fun x y => A x y \/ B x y) p.
Proof.
intros p Asec. 
eapply sec_strengthen. intros. left. apply H. apply Asec.
Defined.

(* AfUnion *)
Corollary af_union: 
 forall (X:Type) (A:X->X->Prop) (B:X->X->Prop),
 almost_full A -> 
 almost_full (fun x y => A x y \/ B x y).
Proof.
intros X A B (p,Asec). exists p. apply sec_union. apply Asec.
Defined.

(* **************************************************************
 *                                                              * 
 *                       Intersections                          * 
 *      (the intuitionistic version of Ramsey's theorem)        *
 *                                                              * 
 ****************************************************************)

(* OplusNullary *)
Fixpoint oplus_nullary (X:Type) (p:WFT X) (q:WFT X) := 
  match p with 
  | ZT _ => q
  | SUP f => SUP (fun x => oplus_nullary (f x) q)
  end.

(* OplusLemma *)
Lemma oplus_nullary_sec_intersection: 
  forall (X:Type) (p : WFT X) (q: WFT X) 
  (C : X -> X -> Prop) (A : Prop) (B : Prop),
  SecureBy (fun y z => C y z \/ A) p -> 
  SecureBy (fun y z => C y z \/ B) q -> 
  SecureBy (fun y z => C y z \/ (A /\ B)) 
            (oplus_nullary p q).
Proof.
intros X p. induction p. intros. simpl. simpl in H. eapply sec_strengthen.
2: apply H0. intros. simpl in H1. destruct H1. left. apply H1. 
destruct (H x y). left. apply H2. right. auto.
intros.
simpl. 
simpl in H0. intro x. remember (H0 x). 
remember (@H x q (fun y z => C y z \/ C x y) A B). eapply sec_strengthen.
2: { 
  apply s0. clear Heqs. clear H0. eapply sec_strengthen. 2: apply s.
  intros. simpl in H0. destruct H0. destruct H0. left. left. apply H0. right. apply H0.
  destruct H0. left. right. apply H0.
  right. apply H0.
  subst.
  eapply sec_strengthen. 2: apply H1.
  intros. simpl in H2. destruct H2.
  left. left.
  apply H2.
  right.
  apply H2.
}
intros.
simpl in H2.
destruct H2.
destruct H2.
left. left.
apply H2.
right; left.
apply H2.
right.
right.
apply H2.
Defined.

(* OplusUnary *)
Definition oplus_unary (X:Type) (p : WFT X): WFT X -> WFT X.
Proof.
induction p. 
intro q. apply q.
intro q. induction q. apply (SUP w).
apply SUP. intro x. apply oplus_nullary. 
apply (X0 x (SUP w0)).
apply (X1 x).
Defined.

Lemma oplus_unary_sup_sup : forall (X:Type) (f : X -> WFT X) (g : X -> WFT X),
     oplus_unary (SUP f) (SUP g) = 
     SUP (fun x => oplus_nullary (oplus_unary (f x) (SUP g))
                                 (oplus_unary (SUP f) (g x))).
Proof. intros; auto. Defined.

(* OplusUnaryLemma *)
Lemma oplus_unary_sec_intersection: 
  forall (X:Type) (p:WFT X) (q:WFT X) (C : X -> X -> Prop) 
  (A : X -> Prop) (B : X -> Prop), 
  SecureBy (fun y z => C y z \/ A y) p -> 
  SecureBy (fun y z => C y z \/ B y) q -> 
  SecureBy (fun y z => C y z \/ (A y /\ B y)) 
            (oplus_unary p q).
Proof.
intros X p.
induction p. simpl. intros. eapply sec_strengthen. 2: apply H0.
intros. simpl in H1. destruct (H x y). left. apply H2. destruct H1. left. apply H1. right. split. apply H2. apply H1.
intro q. induction q. intros. simpl. simpl in H1. intro x. simpl in H0.
remember (H0 x). eapply sec_strengthen. 2: apply s. intros.
simpl in H2. destruct H2. destruct H2. destruct (H1 x y). left. left. apply H2. left. left. apply H2.
destruct (H1 x0 y). left. left. apply H3. left. right. split. apply H2. apply H3.
destruct (H1 x x0). right. left. apply H3. destruct H2. right. left. apply H2. right. right. auto.
intros.
rewrite oplus_unary_sup_sup. rewrite sup_rewrite.
intro x.
assert (SecureBy (fun y z => (C y z \/ C x y \/ A y /\ B y) \/ (A x /\ B x)) 
           (oplus_nullary (oplus_unary (w x) (SUP w0)) (oplus_unary (SUP w) (w0 x)))).
apply oplus_nullary_sec_intersection.
simpl in H1. remember (H1 x) as G1. clear HeqG1. clear H1.
remember (@H x (SUP w0) C (fun y => C x y \/ A y \/ A x) B).
eapply sec_strengthen. 
2: { 
  apply s. eapply sec_strengthen.
  2: eapply G1. intros. simpl in H1.
  destruct H1. destruct H1.
  left; apply H1.
  right; right; left; apply H1.
  destruct H1. right; left; apply H1.
  right; right; right; apply H1.
  apply H2.
}
intros.
destruct H1.
left; left; auto.
destruct H1.
destruct H1.
left; right; left; auto.
destruct H1.
left; right; right; auto.
right; auto.

simpl in H2. remember (H2 x) as G2. clear HeqG2.
remember (@H0 x C A (fun y => C x y \/ B y \/ B x)).
eapply sec_strengthen.
2: { 
  apply s. eapply sec_strengthen.
  2: apply H1. intros. simpl in H3. auto.
  eapply sec_strengthen. 2: eapply G2.
  intros. simpl in H3. destruct H3. destruct H3. left. apply H3. right.
  right. left. apply H3. destruct H3. right. left. apply H3. right.
  right. right. apply H3.
}
2: {
eapply sec_strengthen. 2: apply H3.
intros. simpl in H4. destruct H4. destruct H4. left. left. apply H4.
destruct H4. right. left. apply H4. left. right. apply H4.
right. right. apply H4.
}

intros. destruct H3.
left; left; auto.
destruct H3; destruct H4.
left; right; left; auto.
destruct H4.
left; right; right; auto.
right; auto.
Qed.

(* OplusBinary *)
Definition oplus_binary (X:Type) (p : WFT X) : WFT X -> WFT X.
Proof.
induction p. 
intro q. apply q.
intro q.
induction q. apply (SUP w). 
apply SUP.
intro x. apply oplus_unary. apply (X0 x (SUP w0)).
apply (X1 x).
Defined.

Lemma oplus_binary_zt_sup : forall (X:Type) (f : X -> WFT X) q, 
     oplus_binary (ZT X) q = q.
Proof. intros; auto. Defined.

Lemma oplus_binary_sup_zt : forall (X:Type) (f : X -> WFT X) p, 
    oplus_binary p (ZT X) = p.
Proof.
intros.
induction p; auto.
Defined.

Lemma oplus_binary_sup_sup : forall (X:Type) (f : X -> WFT X) (g : X -> WFT X),
     oplus_binary (SUP f) (SUP g) = 
     SUP (fun x => oplus_unary  (oplus_binary (f x) (SUP g))
                                (oplus_binary (SUP f) (g x))).
Proof. intros; auto. Defined.

(* OplusBinaryLemma *)
Lemma oplus_binary_sec_intersection : 
 forall (X:Type) (p : WFT X) (q : WFT X) 
 (A : X -> X -> Prop) (B : X -> X -> Prop), 
 SecureBy A p -> SecureBy B q -> 
 SecureBy (fun x y => A x y /\ B x y) (oplus_binary p q).
Proof.
intros X p. induction p.
intros. simpl in H. simpl. eapply sec_strengthen. intros. split. apply H. apply H1.
apply H0.
intro q. induction q.
intros. simpl in H0. simpl in H1. simpl. intros. eapply sec_strengthen. 2: apply H0.
intros. simpl in H2. destruct H2. left. split. apply H2. apply H1. right. split. apply H2. apply H1.
intros.
rewrite oplus_binary_sup_sup. rewrite sup_rewrite.
intro x. 
remember H1 as G1. clear HeqG1.
simpl in G1. remember (@H _ _ _ _ (G1 x) H2) as IHp. clear HeqIHp.
remember H2 as G2. clear HeqG2. simpl in G2. 
remember (@H0 _ _ _ H1 (G2 x)) as IHq. clear HeqIHq. clear H0.
simpl in IHp. 
assert (SecureBy
          (fun x0 y : X => A x0 y /\ B x0 y \/ B x x0)
          (oplus_binary (SUP w) (w0 x))) as IHqSimpler.
eapply sec_strengthen. 2: apply IHq. intros. simpl in H0. firstorder.
clear IHq. clear G1. clear G2. clear H1. clear H. clear H2.
eapply oplus_unary_sec_intersection. eapply sec_strengthen.
2: apply IHp. intros. simpl in H.
destruct H. destruct H. left. auto. right. auto.
eapply sec_strengthen. 2: eapply IHqSimpler.
intros. simpl in H. destruct H. left. auto. right. auto.
Defined.

(* AfIntersection *)
Corollary af_intersection (X:Type) (A B :X->X->Prop):
 almost_full A -> almost_full B -> 
 almost_full (fun x y => A x y /\ B x y).
Proof.
intros (p,Asec) (q,Bsec).
exists (oplus_binary p q).
apply oplus_binary_sec_intersection; repeat auto.
Defined.

(* Some other facts, not used in the rest of the development *) 
Lemma sec_nullary_right : forall (X : Type) (q : WFT X) (s : WFT X) (R : X -> X -> Prop),
 SecureBy R s -> SecureBy R (oplus_nullary q s).
Proof.
intros X q. induction q.
intros. simpl. apply H.
intros. induction s. simpl. intros.
apply H. simpl in H0. simpl. intros. left. apply H0. 
simpl. intro x. simpl in H0.
remember (H0 x) as G0.
apply H. simpl. intros. eapply sec_strengthen.
2: apply H0.
intros. simpl in H2. destruct H2. left. left. apply H2.
right. left. apply H2.
Defined.

Lemma sec_nullary_left : forall (X : Type) (q : WFT X) (s : WFT X) (R : X -> X -> Prop),
 SecureBy R q -> SecureBy R (oplus_nullary q s).
Proof.
intros X q. induction q. intros. simpl in H. simpl.
induction s. simpl. apply H. simpl. intro x. eapply sec_strengthen.
2: apply H0. intros. left. apply H1.
intros. induction s.
simpl. simpl in H0. 
intro x. simpl. apply H. apply H0.
simpl. intro x. apply H. simpl in H0. apply H0. 
Defined.

Lemma sec_unary_left : forall (X : Type) (q : WFT X) (s : WFT X) (R : X -> X -> Prop),
 SecureBy R q -> SecureBy R (oplus_unary q s).
Proof.
intros X q. induction q. intros. simpl in H. simpl.
induction s. simpl. apply H. simpl. intro x. eapply sec_strengthen.
2: apply H0. intros. left. apply H1.
intros. induction s.
simpl. simpl in H0. 
intro x. apply H0. simpl.
intro x. apply sec_nullary_left. apply H.
simpl in H0. apply H0.
Defined.

Lemma sec_unary_right : forall (X : Type) (q : WFT X) (s : WFT X) (R : X -> X -> Prop),
 SecureBy R s -> SecureBy R (oplus_unary q s).
Proof.
intros X q. induction q.
intros. simpl. apply H. intros.
induction s. simpl in H0. apply sec_unary_left. simpl.
intros. remember (w x). clear Heqw0. induction w0. simpl. intros. left. apply H0.
simpl. intro x0. eapply sec_strengthen. 2: apply H1.
intros. simpl in H2. right. right. apply H0.
simpl. intro x.
apply sec_nullary_left.
apply H. eapply sec_strengthen. 2: apply H0.
intros. left. apply H2.
Defined.

Lemma sec_binary_left : forall (X : Type) (q : WFT X) (s : WFT X) (R : X -> X -> Prop),
 SecureBy R q -> SecureBy R (oplus_binary q s).
Proof.
intros X q. induction q. intros. simpl in H. simpl.
induction s. simpl. apply H. simpl. intro x. eapply sec_strengthen.
2: apply H0. intros. left. apply H1.
intros. induction s.
simpl. simpl in H0. 
intro x. apply H0. simpl.
intro x. apply sec_unary_left. apply H.
simpl in H0. apply H0. 
Defined.

Lemma sec_binary_right : forall (X : Type) (q : WFT X) (s : WFT X) (R : X -> X -> Prop),
 SecureBy R s -> SecureBy R (oplus_binary q s).
Proof.
intros X q. induction q.
intros. simpl. apply H. intros.
induction s. simpl in H0. apply sec_binary_left. simpl.
intros. remember (w x). clear Heqw0. induction w0. simpl. intros. left. apply H0.
simpl. intro x0. eapply sec_strengthen. 2: apply H1.
intros. simpl in H2. right. right. apply H0.
simpl. intro x.
apply sec_unary_left.
apply H. eapply sec_strengthen. 2: apply H0.
intros. left. apply H2.
Defined.

(****************************************************************
 *                                                              * 
 *                  Type-based constructions                    * 
 *                                                              * 
 ****************************************************************)

(* Cofmap *)
Fixpoint cofmap (X:Type) (Y:Type) (f:Y->X) (p:WFT X) :=
  match p with 
  | ZT _ => ZT Y
  | SUP w => SUP (fun y => cofmap f (w (f y)))
  end.

(* CofmapLemma *)
Lemma cofmap_secures: forall (X Y:Type)(f:Y->X) (p:WFT X) (R:X->X->Prop),
 SecureBy R p -> 
 SecureBy (fun x y => R (f x) (f y)) (cofmap f p).
Proof.
intros X Y f p.
induction p. intros. simpl.
intros. simpl in H. apply H.
intros. simpl in H. simpl in H0.
simpl. intros.  
remember (H (f x) (fun y z => R y z \/ R (f x) y)).
simpl in s. apply s. apply H0.
Defined.

(* CoFmapCorollary *)
Corollary af_cofmap (X Y:Type) (f:Y->X) (R:X->X->Prop):
 almost_full R -> almost_full (fun x y => R (f x) (f y)).
Proof.
intros (p,Rsec). exists (cofmap f p).
apply cofmap_secures; auto.
Defined.

(* Products *)

(* AfProduct *) 
Lemma af_product (X : Type) (Y : Type) : 
  forall (A : X -> X -> Prop) (B : Y -> Y -> Prop), 
  almost_full A -> almost_full B -> 
  almost_full (fun x y => A (fst x) (fst y) /\
                B (snd x) (snd y)).
Proof.
intros A B afA afB. 
apply(af_intersection
       (@af_cofmap _ _ (@fst X Y) A afA) 
       (@af_cofmap _ _ (@snd X Y) B afB)).
Defined.

(* AfProductLeft *)
Lemma af_product_left (X Y : Type) (A:X->X->Prop) : 
  almost_full A -> 
  almost_full (fun (x:X*Y) (y:X*Y) => A (fst x) (fst y)).
Proof.
intros afA. 
apply (@af_cofmap _ _ (@fst X Y) A afA).
Defined.

(* Booleans *)

(* BoolTree *)
Definition bool_tree : WFT bool := 
  SUP (fun x => SUP (fun y => SUP (fun z => ZT bool))).

Lemma sec_bool : SecureBy eq bool_tree.
Proof.
simpl. intros x y. 
destruct x; repeat (simpl;auto). destruct y; repeat (simpl;auto).
intros x y z. destruct x; repeat (simpl; auto).
destruct y; repeat (simpl; auto).
intros x y z. destruct x; repeat (simpl; auto).
Defined.

(* AfBool *)
Corollary af_bool : almost_full (@eq bool).
Proof. exists bool_tree; apply sec_bool. Defined.

(* Sums (through products) *)
 
(* SumLift *)
Definition sum_lift (X Y:Type) (A:X->X->Prop) (B:Y->Y->Prop) (x:X+Y) (y:X+Y) :=
  match (x,y) with 
  | (inl x0, inl y0) => A x0 y0 
  | (inl x0, inr y0) => False 
  | (inr x0, inl y0) => False 
  | (inr x0, inr y0) => B x0 y0
  end.

(* LeftSumLift *)
Definition left_sum_lift (X Y:Type) (A:X->X->Prop) 
  (x:X+Y) (y:X+Y) := 
  match (x,y) with 
  | (inl x0, inl y0) => A x0 y0 
  | (inl x0, inr y0) => False 
  | (inr x0, inl y0) => False 
  | (inr x0, inr y0) => True
  end.

(* LeftSumTree *)
Fixpoint left_sum_tree (X Y:Type) (p:WFT X) 
  : WFT (X+Y) := 
  match p with 
    | ZT _ => SUP (fun x => SUP (fun y => 
                          SUP (fun z => ZT (X+Y))))
    | SUP f => SUP (fun x => 
      match x with 
        | inl x0 => left_sum_tree Y (f x0)
        | inr x0 => SUP (fun y => 
          match y with 
            | inl y0 => left_sum_tree Y (f y0)
            | inr y0 => ZT (X+Y)
          end)
      end)
  end.

(* SecLeftSumTree *)
Lemma sec_left_sum_tree (X Y:Type) (p : WFT X): 
  forall (A : X -> X -> Prop), SecureBy A p -> 
  SecureBy (left_sum_lift A) (left_sum_tree Y p).
Proof.
induction p. 
intros A Zsec.
simpl in *. intros v w x y z.
destruct x; (repeat (auto; firstorder)).
destruct v; (repeat (auto; firstorder)).
destruct w; (repeat (auto; firstorder)).
destruct v; (repeat (auto; firstorder)).
destruct w; (repeat (auto; firstorder)).
intros. simpl. intro x. destruct x; repeat auto.
eapply sec_strengthen. 2: { apply H. apply H0. }
intros. destruct x0; repeat (auto; firstorder).
        destruct y; repeat (auto; firstorder).
simpl in *. intro x.
destruct x; repeat (auto; firstorder). 
eapply sec_strengthen. 2: { apply H. apply H0. }
intros. destruct x0; repeat (auto;firstorder).
        destruct y0; repeat (auto;firstorder).
Defined.

(* Transpose *)
Definition transpose (X Y:Type) (x:X+Y) : Y+X := 
  match x with 
  | inl x0 => inr _ x0 
  | inr x0 => inl _ x0
  end.

(* RightTranspose *)
Definition right_sum_lift (X Y:Type) (B:Y->Y->Prop) (x y:X+Y) := 
 left_sum_lift B (transpose x) (transpose y).

Definition right_sum_tree (X Y:Type) (p:WFT Y) : WFT (X+Y) :=
 cofmap (@transpose X Y) (@left_sum_tree Y X p).

Lemma sec_right_sum_tree (X Y:Type) (p : WFT Y) :
 forall (B : Y -> Y -> Prop), SecureBy B p -> 
  SecureBy (right_sum_lift B) (right_sum_tree X p).
Proof.
intros. 
unfold right_sum_lift.
apply cofmap_secures. 
apply sec_left_sum_tree; assumption.
Defined.

(* SecSumLift *)
Lemma sec_sum_lift (X Y : Type) :
  forall (A : X -> X -> Prop) (B : Y -> Y -> Prop)
  (p : WFT X) (q : WFT Y), 
  SecureBy A p -> SecureBy B q -> 
  SecureBy (sum_lift A B)
           (oplus_binary (left_sum_tree Y p) (right_sum_tree X q)).
Proof.
intros A B p q Asec Bsec.
apply sec_strengthen with (A := fun x y => left_sum_lift A x y /\ right_sum_lift B x y).
intros x y. destruct x; destruct y; repeat firstorder.
apply oplus_binary_sec_intersection. 
apply sec_left_sum_tree; assumption.
apply sec_right_sum_tree; assumption.
Defined.

(* AfSumLift *)
Corollary af_sum_lift (X Y : Type) : 
 forall (A : X -> X -> Prop) (B : Y -> Y -> Prop), 
  almost_full A -> almost_full B -> 
  almost_full (sum_lift A B).
Proof.
intros A B (p,Asec) (q,Bsec). 
exists (oplus_binary (left_sum_tree Y p) (right_sum_tree X q)).
apply sec_sum_lift; repeat assumption.
Defined.

(* Finite naturals *)

(* Finite natural values in the range [0 ... k-1] that is, k inhabitants *)
Inductive Finite (k:nat) : Type := FinIntro x (_ : x < k).

Definition next_fin k (x : Finite k) (y : Finite k) := 
  match (x,y) with 
  | (@FinIntro _ x Hx, @FinIntro _ y Hy) => (S x = k /\ y = O) \/ (S x < k /\ y = S x)
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

Lemma af_finite (k:nat) : almost_full (@eq_fin k).
Proof.
set (f1 (x:Finite k) := match x with 
                        | @FinIntro _ kx _ => kx
                        end).
set (f2 (x:Finite k) := match x with 
                        | @FinIntro _ kx _ => k - kx
                        end).
assert (almost_full (fun x y => f1 x <= f1 y /\ f2 x <= f2 y)).
apply af_intersection. apply af_cofmap. apply leq_af.
                       apply af_cofmap. apply leq_af.
unfold almost_full in *. destruct H. exists x.
eapply sec_strengthen. 2: apply H.
intros; simpl. destruct x0. destruct y. simpl in H0.
unfold eq_fin. lia.
Defined.
