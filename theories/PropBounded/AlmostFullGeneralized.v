Require Import Wf_nat.
Require Import Arith.
Require Import Wellfounded.
Require Import List.
Require Import Relations.

From AlmostFull Require Import PropBounded.AlmostFull.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.

(* LRel *)
Definition LRel (X:Type) := list X -> Prop.

(* AFLRel *)
Inductive almost_full_lrel X : LRel X -> Prop := 
 | AF_ZT  : forall (R : LRel X), 
    (forall xs, R xs) -> @almost_full_lrel X R
 | AF_SUP : forall (R : LRel X), 
    (forall x, @almost_full_lrel X (fun ys => R ys \/ R (x :: ys))) ->
    @almost_full_lrel X R.

(* AFStrengthenLRel *)
Lemma af_strengthen_lrel (X:Type) (A : LRel X) : 
   almost_full_lrel A -> 
   forall (B : LRel X), (forall xs, A xs -> B xs) -> 
   almost_full_lrel B.
Proof.
intro afA.
induction afA.
intros. apply AF_ZT. intros. apply H0. apply H.
intros. apply AF_SUP.
intros. apply H0 with (x := x). intros. destruct H2. left. apply H1. apply H2.
right. apply H1. apply H2.
Defined.

(* Arity *)
Inductive WFT (X:Type) := 
  | ZT  : WFT X 
  | SUP : (X -> WFT X) -> WFT X.
   
Fixpoint Arity (X:Type) (p : WFT X) (A : LRel X) := 
  match p with 
  | ZT _    => (forall ys, A ys <-> A nil)
  | SUP w => (forall x, Arity (w x) (fun ys => A (x::ys)))
    end.

(* AFIntersectLRel *)
Lemma af_intersection_lrel (X:Type):
   forall (p : WFT X), 
   forall (R : LRel X), almost_full_lrel R -> 
   forall (T : LRel X), almost_full_lrel T -> 
   forall (C : LRel X), 
   forall A B, Arity p A -> Arity p B -> 
      (forall xs, R xs -> C xs \/ A xs) -> 
      (forall xs, T xs -> C xs \/ B xs) -> 
      almost_full_lrel (fun xs => C xs \/ A xs /\ B xs).
Proof.
intro p.
induction p.
   (* Case Arity = 0 *)
   intros R afR.
   induction afR.
      (* Case AF_ZT *)
      intros. 
      apply (af_strengthen_lrel H0). intros.
      destruct (H4 xs H5). left; auto. destruct (H3 xs (H xs)). left; auto. right; auto.
      (* Case AF_SUP *)
      intros.
      apply AF_SUP. intros.
      remember (H0 x T H1 
        (fun ys => C ys \/ C (x::ys))) as G.
      clear HeqG. clear H0.
      assert(almost_full_lrel (X:=X)
        (fun xs : list X =>
         (fun ys : list X => C ys \/ C (x :: ys)) xs \/ A xs /\ B xs)).
      apply G. apply H2. apply H3. intros.
      destruct H0. destruct (H4 xs H0). left. left. auto. right. auto.
      destruct (H4 (x::xs) H0). left. right; auto. simpl in H2.
      destruct (H2 (x::xs)). assert (A nil). apply H7. apply H6. right.
      destruct (H2 xs). apply H11. apply H9. intros.
      destruct (H5 xs H0). left. left. auto. right. auto. 
      apply (af_strengthen_lrel H0). intros. 
      destruct H6. destruct H6. left. left. auto. right. left. auto. left. right. auto.
  (* Case Arity = SUP *)
  intros R afR.
  induction afR.
   (* Case R = AF_ZT *) 
   intros.
   apply (af_strengthen_lrel H1).
   intros. destruct (H5 xs H6). left. auto. destruct (H4 xs (H0 xs)). left. auto. right; auto.
   (* Case R = AF_SUP *)
   intros T afT.
   induction afT.
     (* Case T = AF_ZT *) 
     assert (almost_full_lrel R). apply (AF_SUP H0).
     intros. apply (af_strengthen_lrel H3). intros.
     destruct (H6 xs H8). left; auto. destruct (H7 xs (H2 xs)). left. auto. right; auto.
     (* Case T = AF_SUP *)
     intros.
     apply AF_SUP.
     intro x.
     assert (almost_full_lrel R) as afR.   apply (AF_SUP H0).
     assert (almost_full_lrel R0) as afR0. apply (AF_SUP H2).

     assert (almost_full_lrel (fun ys => 
        ((C ys \/ C (x::ys) \/ (A ys /\ B ys)) \/ A (x::ys)))) as GLeft.
     eapply af_strengthen_lrel.
     apply (H1 x R0 afR0 (fun ys => C ys \/ C (x::ys) \/ A (x::ys)) A B H4 H5).
     intros. destruct H8. destruct (H6 xs H8). left. left. auto. right. auto.
     destruct (H6 (x::xs) H8). left. right. left. auto. left. right. auto.
     intros. destruct (H7 xs H8). left. left. auto. right. auto.
     intros. destruct H8. destruct H8. left. auto. destruct H8.
     left. right. left. auto. right. auto. left. right. auto.

     assert (almost_full_lrel (fun ys => 
        ((C ys \/ C (x::ys) \/ (A ys /\ B ys)) \/ B (x::ys)))) as GRight.
     eapply af_strengthen_lrel.
     apply (H3 x (fun ys => C ys \/ C (x::ys) \/ B (x::ys)) A B H4 H5).
     intros. destruct (H6 xs H8). left. left. auto. right. auto.
     intros. destruct H8. destruct (H7 xs H8). left. left. auto. right. auto.
     destruct (H7 (x::xs) H8). left. right. left. auto. left. right. auto. 
     intros. destruct H8. destruct H8. left. auto. destruct H8. 
     left. right. left. auto. right. auto. left. right. right. auto.

     eapply af_strengthen_lrel.
     eapply (@H x (fun ys => (C ys \/ C (x::ys) \/ (A ys /\ B ys)) \/ A (x::ys)) GLeft
                  (fun ys => (C ys \/ C (x::ys) \/ (A ys /\ B ys)) \/ B (x::ys)) GRight
                  (fun ys => C ys \/ C (x::ys) \/ A ys /\ B ys)
                  (fun ys => A (x::ys))
                  (fun ys => B (x::ys))).
     apply H4.
     apply H5.
     Focus 3.
     intros. destruct H8. destruct H8. left. left. auto. destruct H8. right. left. auto.
     left. right; auto. right. auto. 
     auto. auto.
Defined.

(* AFIntersectLRelCor *)
Lemma af_intersection_lrel_cor (X:Type):
   forall (p : WFT X) A B,
   Arity p A -> Arity p B -> 
   almost_full_lrel A -> almost_full_lrel B -> 
   almost_full_lrel (fun xs => A xs /\ B xs).
Proof.
intros.
pose (C := fun (ys : list X) => False).
assert (almost_full_lrel (fun xs => C xs \/ (A xs /\ B xs))).
apply af_intersection_lrel with (p := p) (R := A) (T := B).
apply H1. apply H2. apply H. apply H0. auto. auto.
apply (af_strengthen_lrel H3). intros. auto.
destruct H4. destruct H4. auto.
Defined.

(* Let's get the familiar binary relation theorem from the nary *)

Fixpoint take (X : Type) (n : nat) (xs : list X) := 
  match n with 
  | O => nil
  | S n => match xs with 
           | nil => @nil X
           | cons y ys => y :: take n ys 
           end
  end.

(* BinRelExtension *)
Definition BinRelExtension (X:Type) (A : X -> X -> Prop) : LRel X := 
   fun ys => match ys with 
    | nil => False
    | cons x xs => match xs with 
        | nil => False
        | cons z zs => A x z
        end
    end.

(* Af2AfLrel *)
Lemma af_to_af_lrel (X:Type) (A : X -> X -> Prop) :
  almost_full A -> almost_full_lrel (BinRelExtension A).
Proof.
intro afA.
induction afA.
apply AF_SUP. intros. apply AF_SUP. intro z.
intros. apply AF_ZT. intros. right. right. simpl. apply H.
apply AF_SUP. intro x.
apply AF_SUP. intro y.
apply (af_strengthen_lrel (H0 x)).
intros. simpl in H1. destruct xs. destruct H1. destruct xs. simpl in H1. destruct H1.
simpl in H1. destruct H1. left. left. auto. left. right. auto.
Defined.

Lemma af_lrel_to_af (X:Type) (R : LRel X) : 
 (forall x y zs, R (x :: y :: zs) <-> R (x :: y :: nil)) -> 
 almost_full_lrel R -> almost_full (fun x y => R (x :: y :: nil)).
Proof.
intros.
induction H0.
intros. apply AlmostFull.AF_ZT. intros. apply H0.
apply AlmostFull.AF_SUP.
intro x.
assert ((forall (x0 y : X) (zs : list X),
        R (x0 :: y :: zs) \/ R (x :: x0 :: y :: zs) <->
        R (x0 :: y :: nil) \/ R (x :: x0 :: y :: nil))).
intros. split.
intros. destruct H2. left. remember (H x0 y zs). destruct i. apply r. apply H2.
right. assert (R (x::x0::nil)). remember (H x x0 (y::zs)). destruct i. apply r. apply H2.
remember (H x x0 (y::nil)). destruct i. apply r0. apply H3.
intros. destruct H2. left.
destruct (H x0 y zs). apply H4. apply H2. right.
destruct (H x x0 (y::zs)). apply H4. destruct (H x x0 (y::nil)). apply H5. apply H2.
apply (af_strengthen (H1 x H2)). intros.
destruct H3. left. auto. right. 
destruct (H x x0 (y::nil)). apply H4. apply H3.
Defined.

(* AfLrel2Af *)
Corollary af_lrel_to_af_cor (X:Type) (A : X -> X -> Prop) :
   almost_full_lrel (BinRelExtension A) -> almost_full A.
Proof.
intros. 
apply af_strengthen with (A := fun x y => BinRelExtension A (x::y::nil)).
apply af_lrel_to_af. intros. simpl. auto. split. intros. auto. intros. auto.
apply H.
intros. simpl in H0. auto.
Defined.

Corollary af_intersection_usual (X:Type) (A : X -> X -> Prop) (B : X -> X -> Prop) : 
 almost_full A -> 
 almost_full B -> 
 almost_full (fun x y => A x y /\ B x y).
Proof.
intros.
assert (almost_full_lrel (BinRelExtension A)).
apply af_to_af_lrel. apply H.
assert (almost_full_lrel (BinRelExtension B)).
apply af_to_af_lrel. apply H0.
assert (almost_full_lrel (fun ys => BinRelExtension A ys /\ BinRelExtension B ys)).
eapply af_intersection_lrel_cor with (p := SUP (fun _ => SUP (fun _ => @ZT X))).
simpl. firstorder. simpl. firstorder. apply H1. apply H2.
assert (almost_full_lrel (fun ys => BinRelExtension (fun x y => A x y /\ B x y) ys)).
apply (af_strengthen_lrel H3). intros. destruct H4.
destruct xs. simpl. destruct H4. destruct xs. destruct H4.
simpl. simpl in H5. simpl in H5. auto.
apply af_lrel_to_af_cor. apply H4.
Defined.
