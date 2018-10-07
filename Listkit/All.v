Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Load eztactics.

(* TODO: Straighten out use of "set_In" and "In", etc. *)

Definition all A (P : A -> Prop) (xs:set A)
  := forall (x:A), (set_In x xs) -> P x.

Lemma all_nil:
  forall A P,
    all A P nil.
Proof.
 unfold all.
 unfold set_In.
 simpl.
 intros.
 contradiction.
Qed.

Add LoadPath "../Listkit" as Listkit.

Require Import Listkit.Sets. (* Consider NOT doing this. *)

Lemma all_map:
  forall A eq_dec pred f xs,
    all A pred (set_map eq_dec f xs) <-> all A (fun x => pred (f x)) xs.
Proof.
 unfold all, set_map.
 intros.
 intuition.
  apply H.
  change (set_In (f x) (set_map eq_dec f xs)).
  apply set_map_intro; auto.
 assert (H1:In x (set_map eq_dec f xs)).
  intuition.
 apply set_map_image in H1.
 destruct H1 as [y [H1 H2]].
 subst x.
 apply H; auto.
Qed.

Lemma all_cons:
  forall A P x xs,
    all A P (x::xs) <-> (P x /\ all A P xs).
Proof.
 intuition.
   unfold all in H.
   apply H.
   apply in_eq.
  unfold all in *.
  intros; apply H.
  apply in_cons; auto.
 unfold all in *.
 intros.
 apply in_inv in H.
 destruct H.
 subst; auto.
 auto.
Qed.

Lemma In_add_intro:
  forall A eq_dec (x y:A) xs,
  ({x = y} + {In x xs}) -> In x (set_add eq_dec y xs).
Proof.
 intros.
 induction xs.
  destruct H.
   subst y.
   apply in_eq.
  elimtype False.
  auto.
 simpl.
 destruct (eq_dec y a); subst.
  destruct H; subst.
   apply in_eq.
  auto.
 destruct H; subst.
 apply in_cons.
 auto.
 apply in_inv in i.
 destruct i.
  subst; apply in_eq.
 apply in_cons.
 apply IHxs.
 right; auto.
Qed.

(* Fucking classical Prop!!! *)
Lemma In_add_elim:
  forall A eq_dec (x y:A) xs,
    In x (set_add eq_dec y xs) ->
    (* ({x = y}+{In x xs}). *)
    (x = y \/ In x xs).
Proof.
 intros.
 induction xs.
  simpl in *.
  intuition.
 simpl in *.
 destruct (eq_dec y a); subst.
  intuition.
 destruct H; subst; intuition.
Qed.

(* Lemma In_add: *)
(*   forall A eq_dec (x:A) xs, *)
(*     In x (set_add eq_dec x xs). *)
(* Proof. *)
(*  intros. *)
(*  induction xs. *)
(*   apply in_eq. *)
(*  simpl. *)
(*  destruct (eq_dec x a). *)
(*   subst; apply in_eq. *)
(*  apply in_cons. *)
(*  auto. *)
(* Qed. *)

Lemma all_add_good (* TODO: rename to all_add; destroy the other all_add above *):
  forall A eq_dec P x xs,
    all A P (set_add eq_dec x xs) <-> P x /\ all A P xs.
Proof.
 intuition.
  unfold all in *.
  intros.
  apply H.
  apply In_add_intro.
  auto.
 unfold all in *.
 intros.
 apply In_add_elim in H.
 destruct H.
  congruence.
 auto.
Qed.

Lemma all_union:
  forall A eq_dec pred xs ys,
    all A pred (set_union eq_dec xs ys) <->
    (all A pred xs /\ all A pred ys).
Proof.
 intros.
 split.
  intros.
  unfold all in *.
  auto.

 unfold all.
 intros.
 apply set_union_elim in H0.
 intuition.
Qed.

(* Lemma all_all_Type: *)
(*   forall A eq_dec (pred1:A->Prop) (pred2:A->Type) xs, *)
(*     (forall x, pred1 x -> pred2 x) -> *)
(*     all A pred1 xs -> all_Type A eq_dec pred2 xs. *)
(* Proof. *)
(*  induction xs; unfold all; simpl. *)
(*   unfold all_Type; intros; discriminate. *)
(*  intros. *)
(*  apply all_Type_elim. *)
(*   intuition. *)
(*  apply IHxs. *)
(*   auto. *)
(*  unfold all. *)
(*  intuition. *)
(* Qed. *)


Lemma all_map_image:
  forall A (p:A -> Prop) f xs, (forall x:A, p (f x)) -> all _ p (map f xs).
Proof.
 intros.
 unfold all.
 intros.
 rewrite in_map_iff in H0.
 destruct H0 as [y [H0 H1]].
 subst x.
 auto.
Qed.
