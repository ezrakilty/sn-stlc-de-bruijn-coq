Load "eztactics.v".

Require Import List.

Add LoadPath "../Listkit" as Listkit.

Require Import Listkit.logickit.

Require Import Listkit.Sets.

Lemma map_lemma:
  forall (A B :Set) (f:A->B) (x:A) xs,
    map f (x::xs) = (f x) :: (map f xs).
Proof.
  unfold map; trivial.
Qed.

(** Might be in standard library? *)
Lemma map_app_commutes:
  forall (A B:Set) f l1 l2,
    map (A:=A)(B:=B) f (l1 ++ l2) = map f l1 ++ map f l2.
 intros.
 induction l1.
 replace (nil ++ l2) with l2; auto.
 replace ((a :: l1) ++ l2) with (a :: (l1 ++ l2)); auto.
 simpl.
 rewrite IHl1; trivial.
Qed.

Lemma map_idy : forall A xs, map (idy A) xs = xs.
Proof.
 induction xs.
  auto.
 simpl.
 unfold idy at 1.
 rewrite IHxs.
 auto.
Qed.

Lemma map_extensionality:
  forall A B (f g:A->B) xs,
    (forall x, set_In x xs -> f x = g x)
     -> map f xs = map g xs.
Proof.
 induction xs; simpl; intros; auto.
 rewrite IHxs; auto.
 rewrite H; auto.
Qed.

Lemma set_map_extensionality:
  forall A B B_eq_dec (f g:A->B) xs,
    (forall x, set_In x xs -> f x = g x)
     -> set_map B_eq_dec f xs = set_map B_eq_dec g xs.
Proof.
 induction xs; simpl; intros; auto.
 rewrite IHxs; auto.
 rewrite H; auto.
Qed.

(* Consider the nearly identical, but stronger, set_In_map_image in Sets. *)
Lemma map_image:
  forall A B (f:A->B) x xs,
    set_In x (map f xs) -> exists x', x = f x' /\ set_In x' xs.
Proof.
 induction xs.
  simpl; contradiction.
 simpl.
 intuition.
  exists a; auto.
 firstorder.
Qed.

Lemma set_map_idy_ext :
  forall A eq_dec (f:A->A) xs,
    (* TODO: Consider using set_In here? *)
    (forall x, set_In x xs -> f x = x)
    -> eq_sets _ (set_map eq_dec f xs) xs.
Proof.
 induction xs.
  auto.
 simpl.
 intros.
 pose (H0 := H a).
 assert (f a = a).
 apply H0.
 case (eq_dec a a).
 auto.
 intuition.
 replace (f a) with a.
 rewrite IHxs.
  sauto.
 intuition.
Qed.

Lemma set_map_idy :
  forall A eq_dec (xs:set A),
    eq_sets _ (set_map eq_dec (idy A) xs) xs.
Proof.
 induction xs; simpl.
  auto.
 unfold idy at 1.
 rewrite IHxs.
 auto.
Qed.

Lemma set_map_map :
  forall A B eq_dec f (g:A->B) xs,
    eq_sets _
      (set_map eq_dec f (set_map eq_dec g xs))
      (set_map eq_dec (fun x => f (g x)) xs).
Proof.
 induction xs; simpl; intros.
  auto.
 unfold eq_sets in IHxs |- *.
 destruct IHxs as [IHxs1 IHxs2].
 split.
  rewrite map_add_comm.
  rewrite IHxs1; auto.
(* Check (flip Basics.impl). *)
 rewrite map_add_comm.
 rewrite IHxs2; auto.
Qed.
