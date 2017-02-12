Require Import List.
Require Import Omega.

Require Import Coq.Lists.List.
Require Export Coq.Lists.ListSet.

Add LoadPath "../Listkit" as Listkit.

Load "eztactics.v".

Require Import Listkit.logickit.
Require Import Listkit.Foreach.
Require Import NthError.

Notation "X ∪ Y" := (set_union eq_nat_dec X Y) (at level 600).
(*Notation "⋃ Xs" := (set_unions nat eq_nat_dec Xs) (at level 700).
    (* Looks too similar to (∪) *) *)

Definition incl_sets A (xs ys : set A) :=
  forall a, set_In a xs -> set_In a ys.

Lemma incl_sets_refl:
forall A X, incl_sets A X X.
Proof.
 unfold incl_sets.
 auto.
Qed.

Hint Resolve incl_sets_refl.

Lemma incl_sets_trans:
  forall A X Y Z,
    incl_sets A X Y -> incl_sets _ Y Z -> incl_sets _ X Z.
Proof.
 unfold incl_sets.
 auto.
Qed.

Definition eq_sets A X Y := incl_sets A X Y /\ incl_sets A Y X.

Lemma eq_sets_trans:
  forall A X Y Z,
    eq_sets A X Y ->
    eq_sets _ Y Z ->
    eq_sets _ X Z.
Proof.
 unfold eq_sets.
 intuition; eapply incl_sets_trans; eauto.
Qed.

Lemma eq_sets_refl:
  forall A X,
    eq_sets A X X.
Proof.
 unfold eq_sets.
 intuition.
Qed.

Lemma eq_sets_symm:
  forall A X Y,
    eq_sets A X Y -> eq_sets A Y X.
Proof.
 unfold eq_sets.
 intuition.
Qed.

Hint Resolve eq_sets_refl eq_sets_symm.

Require Import Setoid.

Add Parametric Relation A : (set A) (incl_sets A)
  reflexivity proved by (incl_sets_refl A)
  transitivity proved by (incl_sets_trans A)
    as incl_sets_relation.

Add Parametric Morphism A eq_dec : (set_union eq_dec) with
  signature (incl_sets A) ==> (incl_sets A) ==> (incl_sets A) as union_mor.
Proof.
 intros.
 unfold incl_sets in *.
 intuition.
 apply set_union_elim in H1.
 apply set_union_intro.
 intuition.
Qed.

Add Parametric Relation A : (set A) (eq_sets A)
  reflexivity proved by (eq_sets_refl A)
  symmetry proved by (eq_sets_symm A)
  transitivity proved by (eq_sets_trans A)
    as eq_sets_relation.

Add Parametric Morphism A eq_dec : (set_union eq_dec) with
  signature (eq_sets A) ==> (eq_sets A) ==> (eq_sets A) as union_eq_mor.
Proof.
 intros.
 split.
 destruct H0.
 destruct H.
 apply union_mor; auto.
 destruct H0.
 destruct H.
 apply union_mor; auto.
Qed.

Add Parametric Morphism A x : (cons x) with
  signature (incl_sets A) ==> (incl_sets A) as set_cons_mor.
Proof.
 unfold incl_sets.
 intros a b H0 a' H1.
 simpl in *.
 intuition.
Qed.

Add Parametric Morphism A x : (cons x) with
  signature (eq_sets A) ==> (eq_sets A) as set_cons_eq_mor.
Proof.
 unfold eq_sets.
 intros.
 split; apply set_cons_mor; tauto.
Qed.

Add Parametric Morphism A x eq_dec : (set_add eq_dec x) with
  signature (incl_sets A) ==> (incl_sets A) as set_add_mor.
Proof.
 intros.
 unfold incl_sets in *.
 intros a H0.
 apply set_add_intro.
 apply set_add_elim in H0.
 intuition.
Qed.

Add Parametric Morphism A x eq_dec : (set_add eq_dec x) with
  signature (eq_sets A) ==> (eq_sets A) as set_add_eq_mor.
Proof.
 unfold eq_sets.
 intros.
 split; apply set_add_mor; tauto.
Qed.

(* Alternate definition of set_remove, because the standard one makes it a little
   hard to prove things. *)
Fixpoint set_remove A (Aeq_dec:forall (x y: A), {x=y}+{x<>y}) (a:A) (x:set A)
  : set A :=
  match x with
  | nil => empty_set A
  | a1 :: x1 =>
    match Aeq_dec a a1 with
    | left _ => set_remove _ Aeq_dec a x1
    | right _ => a1 :: set_remove _ Aeq_dec a x1
    end
  end.

(* TODO: This should bind much tighter. *)
Notation "X ∖ { y }" := (set_remove _ eq_nat_dec y X) (at level 600).

Lemma set_remove_intro :
  forall A eq_dec (a b:A) xs,
    (set_In a xs /\ a <> b) -> set_In a (set_remove _ eq_dec b xs).
Proof.
 induction xs.
  intros [H H'].
  auto.
 simpl.
 destruct (eq_dec b a0); simpl; intuition.
 subst.
 intuition.
Qed.

Lemma set_remove_elim:
  forall A eq_dec (a b:A) xs,
    set_In a (set_remove _ eq_dec b xs) -> set_In a xs /\ a <> b.
Proof.
 induction xs.
  simpl; auto.
 simpl; intros.
 destruct (eq_dec b a0).
  firstorder.
 simpl in H.
 intuition.
 subst.
 intuition.
Qed.

Hint Resolve set_remove_intro set_remove_elim.

Add Parametric Morphism A x eq_dec : (set_remove A eq_dec x) with
  signature (incl_sets A) ==> (incl_sets A) as set_remove_incl_mor.
Proof.
 unfold incl_sets.
 intros.
 apply set_remove_elim in H0.
 apply set_remove_intro.
 intuition.
Qed.

Add Parametric Morphism A x eq_dec : (set_remove A eq_dec x) with
  signature (eq_sets A) ==> (eq_sets A) as set_remove_eq_mor.
Proof.
 unfold eq_sets; intuition; apply set_remove_incl_mor; auto.
Qed.

Add Parametric Morphism A x eq_dec : (set_mem eq_dec x) with
  signature (eq_sets A) ==> (@eq bool) as set_mem_eq_mor.
Proof.
 unfold eq_sets.
 intros.
 remember (set_mem eq_dec x y).
 unfold incl_sets in H.
 destruct b.
  apply set_mem_correct2.
  symmetry in Heqb; apply set_mem_correct1 in Heqb.
  intuition.
 apply set_mem_complete2.
 symmetry in Heqb; apply set_mem_complete1 in Heqb.
 intuition.
Qed.


Add Parametric Morphism A eq_dec xs : (set_union eq_dec xs) with
  signature (eq_sets A) ==> (eq_sets A) as union_eq_mor_1.
Proof.
 intros.
 split.
 destruct H.
 apply union_mor; auto.
 destruct H.
 apply union_mor; auto.
Qed.

Add Parametric Morphism A : (incl_sets A) with
  signature (eq_sets A) ==> (eq_sets A) ==> (iff) as incl_sets_mor_eq.
Proof.
 unfold eq_sets.
 intuition.
  eapply incl_sets_trans.
   eapply incl_sets_trans; eauto.
  eauto.
  eapply incl_sets_trans.
   eapply incl_sets_trans; eauto.
  eauto.
Qed.

Lemma set_map_image:
  forall A B eq_dec (f:A->B) x xs,
    set_In x (set_map eq_dec f xs) -> exists x', x = f x' /\ set_In x' xs.
Proof.
 induction xs.
  simpl; contradiction.
 simpl.
 intro H.
 apply set_add_elim in H.
 destruct H.
  exists a; auto.
 firstorder.
Qed.

Lemma set_add_elim_Type:
  forall (A : Type) (Aeq_dec : forall x y : A, {x = y} + {x <> y}) (a b : A) (xs : set A),
    (true = set_mem Aeq_dec a (set_add Aeq_dec b xs)) -> {a = b} + {true = set_mem Aeq_dec a xs}.
Proof.
  induction xs; simpl.
  intros.
  destruct (Aeq_dec a b); intuition.
 intros.
 destruct (Aeq_dec b a0).
  subst.
  simpl in H.
  destruct (Aeq_dec a a0).
   right; auto.
   right; sauto.
 destruct (Aeq_dec a a0).
  intuition.
 simpl in H.
 destruct (Aeq_dec a a0).
  contradiction.
 apply IHxs; sauto.
Qed.

Lemma set_map_elim_Type:
  forall A B eq_dec b (f : A -> B) X,
  (true = set_mem eq_dec b (set_map eq_dec f X)) -> {a : A & (In a X) /\ f a = b}.
Proof.
 induction X; simpl.
  intuition.
  discriminate.
 intros.
 apply set_add_elim_Type in H.
 destruct H.
  exists a.
  intuition.
 destruct (IHX e) as [x a0].
 exists x.
 intuition.
Qed.

Lemma set_map_image_Type:
  forall A B eq_dec (f:A->B) x xs,
    set_In x (set_map eq_dec f xs) -> { x' | ((x = f x') * (set_In x' xs))%type}.
Proof.
 induction xs.
  simpl; contradiction.
 simpl.
 intro H.
 assert (H0: true = set_mem eq_dec x (set_add eq_dec (f a) (set_map eq_dec f xs))).
 symmetry.
 apply set_mem_correct2; auto.
 apply set_add_elim_Type in H0.
 destruct H0.
  exists a; auto.
 symmetry in e; apply set_mem_correct1 in e.
 firstorder.
Qed.

Lemma set_map_intro:
  forall A B eq_dec (x:A) xs (f:A->B),
    set_In x xs -> set_In (f x) (set_map eq_dec f xs).
Proof.
 induction xs; intros f H.
  auto.
 simpl.
 apply set_add_intro.
 destruct H.
  left; f_equal; auto.
 right; apply IHxs; auto.
Qed.

Lemma set_map_elim:
  forall A B eq_dec (b:B) (f:A->B) X,
    set_In b (set_map eq_dec f X) -> exists (a:A), set_In a X /\ f a = b.
Proof.
 induction X.
  simpl.
  intros.
  contradiction.
 simpl.
 intros.
 apply set_add_elim in H.
 destruct H.
  exists a.
  intuition.
 firstorder.
Qed.

Add Parametric Morphism A B eq_dec f : (set_map eq_dec f) with
  signature (incl_sets A) ==> (incl_sets B) as set_map_mor.
Proof.
 unfold incl_sets.
 intros.
 apply set_map_image in H0.
 destruct H0 as [z [H1 H2]].
 subst a.
 apply set_map_intro.
 auto.
Qed.

Add Parametric Morphism A B eq_dec f : (set_map eq_dec f) with
  signature (eq_sets A) ==> (eq_sets B) as set_map_mor_eq.
Proof.
 intros.
 split.
 destruct H.
 apply set_map_mor; auto.
 destruct H.
 apply set_map_mor; auto.
Qed.

Add Parametric Morphism A x : (set_In x) with
  signature (eq_sets A) ==> (iff) as set_In_mor_eq.
Proof.
 unfold eq_sets.
 unfold incl_sets.
 intuition.
Qed.

Add Parametric Morphism A x : (set_In x) with
  signature (incl_sets A) ==> (Basics.impl) as set_In_mor_incl.
Proof.
 unfold incl_sets.
 unfold Basics.impl.
 intuition.
Qed.

Hint Resolve set_union_intro.

Hint Resolve set_add_intro set_add_elim : set_add_lib.

Lemma union_remove:
  forall A eq_dec (x:A) X Y,
    eq_sets _
      (set_remove _ eq_dec x (set_union eq_dec X Y))
      (set_union eq_dec (set_remove _ eq_dec x X) (set_remove _ eq_dec x Y)).
Proof.
 unfold eq_sets, incl_sets.
 intros A ? x X Y.
 split; intros a H.

  intros.
  apply set_remove_elim in H.
  destruct H.
  apply set_union_elim in H.
  apply set_union_intro.
  destruct H; [left|right]; auto.

 apply set_remove_intro.
 apply set_union_elim in H.
 destruct H;
  apply set_remove_elim in H; destruct H.
  auto.
 auto.
Qed.

Lemma set_add_remove_incl:
  forall A eq_dec x (xs:set A),
    incl_sets _
      xs
      (set_add eq_dec x (set_remove A eq_dec x xs)).
Proof.
 unfold incl_sets.
 intros.
 destruct (eq_dec a x).
  apply set_add_intro2; auto.
 apply set_add_intro1.
 apply set_remove_intro.
 auto.
Qed.

Lemma remove_add:
  forall A eq_dec x xs,
  eq_sets _ (set_remove A eq_dec x (set_add eq_dec x xs)) (set_remove A eq_dec x xs).
Proof.
 unfold eq_sets, incl_sets.
 split;
   intros;
   apply set_remove_intro;
   apply set_remove_elim in H;
   intuition.
 apply set_add_elim in H0; tauto.
Qed.

(* Program Instance eq_sets_equivalence A : Equivalence (eq_sets A). *)
(* Obligations. *)
(* Next Obligation. *)
(* unfold Transitive. *)
(* apply eq_sets_trans. *)
(* Qed. *)

(* Require Import SetoidClass. *)

(* Program Instance eq_sets_Setoid A : Setoid (set A) := *)
(*   { equiv := eq_sets A ; setoid_equiv := eq_sets_equivalence A }. *)

Lemma map_remove:
  forall A X eq_dec f (x:A),
    (forall y z, y <> x -> f y = f z -> y = z) ->
    eq_sets _ (set_map eq_dec f (set_remove _ eq_dec x X))
              (set_remove _ eq_dec (f x) (set_map eq_dec f X)).
Proof.
 unfold eq_sets.
 split.
  (* -> *)
  unfold incl_sets.
  intros.
  apply set_remove_intro.
  apply set_map_elim in H0.
  destruct H0 as [a' [Ha' f_a'_eq_a]].
  replace a with (f a').
  apply set_remove_elim in Ha'.
  split.
   apply set_map_intro.
   intuition.
  intuition.
 (* <- *)
 unfold incl_sets.
 intros.
 apply set_remove_elim in H0.
 destruct H0.
 apply set_map_elim in H0.
 destruct H0 as [a' [Ha' f_a'_eq_a]].
 replace a with (f a').
 apply set_map_intro.
 apply set_remove_intro.
 split.
  auto.
 congruence.
Qed.

Lemma map_add_1:
  forall A B (f:A->B) eq_dec_A eq_dec_B (a:A) X,
    incl_sets _
      (set_map eq_dec_B f (set_add eq_dec_A a X))
      (set_add eq_dec_B (f a) (set_map eq_dec_B f X)).
Proof.
 intros.
 unfold incl_sets.
 intros.
 apply set_add_intro.
 apply set_map_image in H.
 destruct H.
 destruct H.
 apply set_add_elim in H0.
 destruct H0.
  subst.
  auto.
 subst.
 auto using set_map_intro.
Qed.

Lemma map_add_2:
  forall A B (f:A->B) eq_dec_A eq_dec_B (a:A) X,
    incl_sets _
      (set_add eq_dec_B (f a) (set_map eq_dec_B f X))
      (set_map eq_dec_B f (set_add eq_dec_A a X)).
Proof.
 intros.
 unfold incl_sets.
 intros.
 apply set_add_elim in H.
 destruct H.
  subst a0.
  apply set_map_intro.
  apply set_add_intro2.
  auto.
 apply set_map_image in H.
 destruct H as [y [H H0]].
 subst a0.
 apply set_map_intro.
 apply set_add_intro1; auto.
Qed.

Lemma map_add_comm:
  forall A B (f:A->B) eq_dec_A eq_dec_B (a:A) X,
    eq_sets _
      (set_map eq_dec_B f (set_add eq_dec_A a X))
      (set_add eq_dec_B (f a) (set_map eq_dec_B f X)).
Proof.
 split.
  apply map_add_1.
 apply map_add_2.
Qed.

Lemma union_comm :
  forall A eq_dec (X Y : set A),
    incl_sets _ (set_union eq_dec X Y) (set_union eq_dec Y X).
Proof.
 unfold incl_sets.
 intros.
 apply set_union_intro.
 apply set_union_elim in H.
 intuition.
Qed.

Lemma union_comm_eq :
  forall A eq_dec (X Y : set A),
    eq_sets _ (set_union eq_dec X Y) (set_union eq_dec Y X).
Proof.
 unfold eq_sets.
 split; apply union_comm.
Qed.

Lemma set_union_nil :
  forall A eq_dec X,
    eq_sets _ (set_union eq_dec (nil:set A) X) X.
Proof.
 unfold eq_sets.
 intuition.
  apply incl_sets_trans with (Y:=set_union eq_dec X nil).
   apply union_comm.
  auto.
 apply incl_sets_trans with (Y:=set_union eq_dec X nil).
  auto.
 apply union_comm.
Qed.

Lemma map_union_1:
  forall A B eq_dec_A eq_dec_B (f:A->B) X Y,
    incl_sets _
      (set_union eq_dec_B (set_map eq_dec_B f X) (set_map eq_dec_B f Y))
      (set_map eq_dec_B f (set_union eq_dec_A X Y)).
Proof.
 intros.
 unfold incl_sets.
 intros.
 apply set_union_elim in H.
 destruct H.
  apply set_map_image in H.
  destruct H as [y [H H0]].
  subst a.
  apply set_map_intro.
  apply set_union_intro1; auto.
 apply set_map_image in H.
 destruct H as [y [H H0]].
 subst a.
 apply set_map_intro.
 apply set_union_intro2; auto.
Qed.

Lemma map_union_2:
  forall A B eq_dec_A eq_dec_B (f:A->B) X Y,
    incl_sets _
      (set_map eq_dec_B f (set_union eq_dec_A X Y))
      (set_union eq_dec_B (set_map eq_dec_B f X) (set_map eq_dec_B f Y)).
Proof.
 intros.
 unfold incl_sets.
 intros.
 apply set_map_image in H.
 destruct H.
 destruct H.
 subst a.
 apply set_union_intro.
 apply set_union_elim in H0.
 intuition.
  left.
  apply set_map_intro; auto.
 right.
 apply set_map_intro; auto.
Qed.

Lemma map_union:
  forall A B eq_dec_A eq_dec_B (f:A->B) X Y,
    eq_sets _
      (set_map eq_dec_B f (set_union eq_dec_A X Y))
      (set_union eq_dec_B (set_map eq_dec_B f X) (set_map eq_dec_B f Y)).
Proof.
 unfold eq_sets.
  intuition; [apply map_union_2 | apply map_union_1].
Qed.

Lemma in_set_remove_not_removed:
forall A eq_dec (x:A) y xs,
  set_In x (set_remove _ eq_dec y xs) -> x <> y.
Proof.
 intros A eq_dec x y xs H.
 apply set_remove_elim in H.
 intuition.
Qed.

Lemma in_set_remove_in_original:
  forall A eq_dec (x y:A) xs,
    set_In x (set_remove _ eq_dec y xs) -> set_In x xs.
Proof.
 intros ? ? ? ? ? H.
 apply set_remove_elim in H.
 intuition.
Qed.

Lemma set_In_map_out_of_range :
  forall A B eq_dec (y:A) f X,
    (forall x:B, f x <> y) ->
    ~set_In y (set_map eq_dec f X).
Proof.
 induction X; simpl; intro H.
  auto.
 destruct (eq_dec y (f a)).
  exfalso.
  apply (H a).
  auto.
 intro.
 apply set_add_elim in H0.
 intuition.
Qed.

Fixpoint set_unions A eq_dec (xss : list (set A)) : set A :=
  match xss with
    | nil => empty_set A
    | xs :: xss => set_union eq_dec xs (set_unions A eq_dec xss)
  end.

Require Import Foreach.

Definition compwise_eq_sets A :=
  fun x y => length x = length y /\ foreach2 (set A) (set A) x y (eq_sets A).

Add Parametric Morphism A eq_dec : (set_unions A eq_dec) with
  signature (compwise_eq_sets A) ==> (eq_sets A) as unions2_mor.
Proof.
 unfold compwise_eq_sets.
 induction x; destruct y.
    simpl.
    auto.
   simpl.
   intros.
   omega.
  simpl.
  intros.
  omega.
 unfold foreach2.
 simpl in *.
 intuition.
 assert (length x = length y).
  omega.
 apply union_eq_mor. (* Note: I should be able to do this with rewrite, but Coq complains some instances don't exist... *)
  auto.
 apply IHx.
 intuition.
Qed.

Fixpoint set_filter A (f : A -> bool) (xs: set A) :=
  match xs with
    | nil => nil
    | x :: xs => if f x then x :: set_filter A f xs else set_filter A f xs
  end.

Lemma filter_add_true :
  forall A eq_dec p X x,
    p x = true ->
    eq_sets _ (set_filter A p (set_add eq_dec x X))
      (set_add eq_dec x (set_filter A p X)).
Proof.
 induction X; simpl; intros.
  replace (p x) with true; auto.
 destruct (eq_dec x a).
  subst a.
  replace (p x) with true.
  simpl.
  destruct (eq_dec x x); [|congruence].
  replace (p x) with true.
  auto.
 case_eq (p a); intro H0; simpl; rewrite H0.
  destruct (eq_dec x a).
   contradiction.
  rewrite IHX; auto.
 auto.
Qed.

Lemma filter_add_false :
  forall A eq_dec p X x,
    p x = false ->
    set_filter A p (set_add eq_dec x X) =
    (set_filter A p X).
Proof.
 induction X; simpl; intros.
  replace (p x) with false; auto.
 destruct (eq_dec x a).
  subst a.
  replace (p x) with false.
  simpl.
  replace (p x) with false.
  auto.
 case_eq (p a); intro H0; simpl; rewrite H0.
  rewrite IHX; auto.
 rewrite IHX; auto.
Qed.

Lemma set_filter_map :
  forall A eq_dec f p (X:set A),
    eq_sets _
    (set_filter A (fun x => p x) (set_map eq_dec f X))
    (set_map eq_dec f (set_filter A (fun x => p (f x)) X)).
Proof.
 induction X; simpl; intros.
  auto.
 case_eq (p (f a)); intro H.
  simpl.
  rewrite <- IHX.
  rewrite filter_add_true; auto.
 rewrite <- IHX.
 rewrite filter_add_false; auto.
Qed.

Lemma filter_remove :
  forall A eq_dec p X x,
    set_filter A p (set_remove _ eq_dec x X) =
    set_remove _ eq_dec x (set_filter A p X).
Proof.
 induction X; simpl; intros.
  auto.
 case_eq (eq_dec x a); case_eq (p a); simpl; intros.
    rewrite H0.
    auto.
   auto.
  rewrite H.
  rewrite H0.
  congruence.
 rewrite H.
 auto.
Qed.

Lemma set_filter_set_remove:
  forall A eq_dec k xs,
   set_remove A eq_dec k xs =
   set_filter A (fun x => if eq_dec x k then false else true) xs.
Proof.
 induction xs; simpl; intros.
  auto.
 destruct (eq_dec k a);
   destruct (eq_dec a k); try (solve [exfalso; intuition]).
   rewrite IHxs.
   auto.
 rewrite IHxs.
 auto.
Qed.

Lemma set_filter_intro:
  forall A X (x:A) P,
    set_In x X -> true = P x -> set_In x (set_filter _ P X).
Proof.
 induction X; simpl; intros.
  auto.
 destruct H; [subst x|]; destruct (P a).
    simpl. auto.
   discriminate.
  simpl.
  right.
  apply IHX; auto.
 apply IHX; auto.
Qed.

Lemma set_filter_elim:
  forall A X (x:A) P,
    set_In x (set_filter _ P X) -> (set_In x X /\ true = P x).
Proof.
 induction X; simpl; intros.
  intuition.
 case_eq (P a); intro H0; rewrite H0 in *.
  simpl in H.
  firstorder congruence.
 firstorder.
Qed.

Hint Resolve set_filter_intro set_union_elim set_filter_elim set_union_intro : filter_union.

Lemma set_filter_union :
  forall A A_eq_dec f X Y,
    eq_sets _
      (set_filter A f (set_union A_eq_dec X Y))
      (set_union A_eq_dec (set_filter A f X) (set_filter A f Y)).
Proof.
 unfold eq_sets, incl_sets.
 intros.
 split; intros.
(* first inclusion *)
  apply set_union_intro.
  apply set_filter_elim in H.
  destruct H.
  apply set_union_elim in H.
  intuition (auto with filter_union).
(* other inclusion *)
 apply set_filter_intro.
  apply set_union_elim in H.
  destruct H.
   apply set_filter_elim in H.
   intuition (auto with filter_union).
  apply set_union_intro.
  apply set_filter_elim in H.
  intuition.
 apply set_union_elim in H.
 destruct H; apply set_filter_elim in H; intuition.
Qed.

Lemma set_union_assoc :
  forall A eq_dec (X Y Z : set A),
    eq_sets _
      (set_union eq_dec (set_union eq_dec X Y) Z)
      (set_union eq_dec X (set_union eq_dec Y Z)).
Proof.
 unfold eq_sets, incl_sets.
 intros.
 split.
  intros.
  apply set_union_elim in H.
  apply set_union_intro.
  intuition.
  apply set_union_elim in H0.
  intuition.
 intros.
 apply set_union_elim in H.
 apply set_union_intro.
 intuition.
 apply set_union_elim in H0.
 intuition.
Qed.

Lemma set_unions_map:
  forall A B eq_dec_A eq_dec_B f Xs,
    eq_sets
      _
      (set_unions B eq_dec_B (map (set_map eq_dec_B f) Xs))
      ((set_map eq_dec_B f) (set_unions A eq_dec_A Xs)).
Proof.
 induction Xs; simpl; intros.
  auto.
 setoid_rewrite IHXs.
 symmetry.
 setoid_rewrite map_union.
 auto.
Qed.

Lemma add_cons_incl A eq_dec:
  forall a xs,
    incl_sets A (set_add eq_dec a xs) (a::xs).
Proof.
 induction xs; simpl.
  simpl.
  auto.
 destruct (eq_dec a a0).
  unfold incl_sets.
  simpl.
  intuition.
 rewrite IHxs.
 unfold incl_sets.
 simpl.
 intuition.
Qed.

Lemma add_cons_incl_bwd A eq_dec:
  forall a xs,
    incl_sets A (a::xs) (set_add eq_dec a xs).
Proof.
 induction xs; simpl.
  simpl.
  auto.
 destruct (eq_dec a a0).
  unfold incl_sets.
  simpl.
  intuition congruence.
 intros.
 rewrite<- IHxs.
 unfold incl_sets.
 simpl.
 intuition.
Qed.

Hint Resolve add_cons_incl add_cons_incl_bwd.

Lemma add_cons_eq A eq_dec:
  forall a xs,
 eq_sets A (set_add eq_dec a xs) (a::xs).
Proof.
 unfold eq_sets.
 split; auto.
Qed.

Hint Resolve add_cons_eq.

Lemma empty_incl:
  forall A X, incl_sets _ (empty_set A) X.
 unfold incl_sets.
 simpl.
 easy.
Qed.

Hint Resolve empty_incl.

Lemma singleton_incl:
  forall A (x:A) X,
    set_In x X <-> incl_sets _ (x :: nil) X.
Proof.
 unfold incl_sets.
 unfold set_In at 2.
 unfold In.
 intuition.
 congruence.
Qed.

Lemma incl_sets_union1: forall A eq_dec X Y, incl_sets A X (set_union eq_dec X Y).
 unfold incl_sets.
 intros.
 apply set_union_intro.
 auto.
Qed.

Lemma incl_sets_union2: forall A eq_dec X Y, incl_sets A Y (set_union eq_dec X Y).
 intros.
 rewrite <- union_comm.
 apply incl_sets_union1.
Qed.

Lemma incl_sets_remove1:
  forall A eq_dec x X, incl_sets A (set_remove A eq_dec x X) X.
Proof.
 unfold incl_sets.
 intros.
 apply set_remove_elim in H.
 tauto.
Qed.

Lemma set_map_idy : forall A eq_dec xs, eq_sets _ (set_map eq_dec (idy A) xs) xs.
Proof.
 induction xs.
  auto.
 simpl.
 unfold idy at 1.
 rewrite IHxs.
 split; auto.
Qed.

Lemma union_idem:
forall A eq_dec X,
  eq_sets A X (set_union eq_dec X X).
Proof.
 unfold eq_sets, incl_sets.
 split; intros.
  apply set_union_intro.
  auto.
  apply set_union_elim in H.
 destruct H; auto.
Qed.

Lemma filter_extensionality:
  forall A f g (xs:set A),
    (forall x:A, set_In x xs -> f x = g x) ->
    set_filter _ f xs = set_filter _ g xs.
Proof.
 induction xs; simpl; intros.
  auto.
 rewrite IHxs by auto.
 rewrite H by auto.
 auto.
Qed.

Lemma nth_error_set_unions:
  forall A eq_dec V Ys n,
    nth_error Ys n = value V ->
    incl_sets _ V (set_unions A eq_dec Ys).
Proof.
 induction Ys; simpl; intros.
  rewrite nth_error_nil in H.
  discriminate.
 destruct n; simpl in H.
  replace a with V.
   apply incl_sets_union1.
  inversion H.
  auto.
 rewrite <- IHYs.
 rewrite <- union_comm. (* backwards because we are lacking some morphism (TODO) *)
  apply incl_sets_union1.
 eauto.
Qed.

Notation "x ∈ Y" := (set_In x Y) (at level 700).

Lemma set_unions_elim:
  forall A eq_dec (x:A) Xs,
    set_In x (set_unions _ eq_dec Xs)
    -> exists X, (X ∈ Xs) /\ (x ∈ X).
Proof.
 induction Xs; simpl.
  intuition.
 rename a into X.
 intro.
 apply set_union_elim in H.
 destruct H.
  exists X; intuition.
 apply IHXs in H.
 firstorder.
Qed.

Ltac solve_set_union_inclusion :=
(* TODO: need a solver for "conditional" set_union_inclusion. *)
  let x := fresh "x" in
  let H := fresh "H" in
    unfold incl_sets; intros x H;
    firstorder;
      repeat ((apply set_union_intro || apply set_union_elim in H); firstorder).

Ltac solve_set_union_equality :=
  unfold eq_sets; split; solve_set_union_inclusion.

Lemma incl_sets_union:
  forall A eq_dec X Y X' Y',
    incl_sets A Y Y' ->
    incl_sets A X X' ->
    incl_sets A (set_union eq_dec X Y)
                (set_union eq_dec X' Y').
Proof.
 intros.
 setoid_replace X with X' using relation (incl_sets A) by auto.
 setoid_replace Y with Y' using relation (incl_sets A) by auto.
 auto.
Qed.

Lemma unions_remove:
  forall A eq_dec x xs,
    eq_sets _ (set_remove A eq_dec x (set_unions A eq_dec xs))
              (set_unions _ eq_dec (map (set_remove _ eq_dec x) xs)).
Proof.
 induction xs. (* Would be better if set_unions used foldr so we could fuse it. *)
  simpl.
  auto.
 simpl.
 rewrite union_remove.
 rewrite IHxs.
 auto.
Qed.

Lemma compwise_eq_sets_map:
  forall A B f g,
   (forall (x:B), eq_sets A (f x) (g x)) ->
   forall env,
     compwise_eq_sets A
     (map f env)
     (map g env).
Proof.
 unfold compwise_eq_sets.
 unfold foreach2.
 split.
  do 2 rewrite map_length; auto.
 rewrite zip_map_diamond.
 rewrite map_map.
 cut (foreach _ env (fun x => eq_sets A (f x) (g x))).
  auto.
 apply foreach_universal.
 sauto.
Qed.

Lemma incl_union_left:
  forall A eq_dec X Y Z,
    incl_sets A X Y -> incl_sets A X (set_union eq_dec Y Z).
Proof.
 intros.
 apply incl_sets_trans with (set_union eq_dec X Z).
  apply incl_sets_union1.
 rewrite H.
 sauto.
Qed.

Lemma incl_union_right:
  forall A eq_dec X Y Z,
    incl_sets A X Z -> incl_sets A X (set_union eq_dec Y Z).
Proof.
 intros.
 apply incl_sets_trans with (set_union eq_dec Y X).
  apply incl_sets_union2.
 rewrite H.
 sauto.
Qed.
