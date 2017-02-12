Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Definition DecidableEquality A :=
  forall (x y : A), {x = y} + {x <> y}.

Definition
  all_Type A (A_eq_dec : DecidableEquality A) (P : A -> Type) (xs:set A)
  := forall (x:A),  set_In x xs -> P x.

Lemma all_nil_Type:
  forall A eq_dec P,
    all_Type A eq_dec P nil.
Proof.
 unfold all_Type.
 intros.
 simpl in H.
 contradiction.
Qed.

Lemma all_Type_cons_fwd:
  forall A eq_dec P (a:A) xs,
    (P a * all_Type _ eq_dec P xs)%type
    -> all_Type _ eq_dec P (a :: xs).
Proof.
 intros A eq_dec P a xs X.
 destruct X.
 unfold all_Type in *.
 intros x H.
 simpl in H.
 destruct (eq_dec a x).
  congruence.
 apply a0.
 destruct H; easy.
Qed.

Add LoadPath "../Listkit" as Listkit.

Require Import Sets. (* Consider NOT doing this. *)

Lemma all_Type_incl:
  forall A eq_dec f smaller bigger,
    incl_sets A smaller bigger ->
    all_Type _ eq_dec f bigger ->
    all_Type _ eq_dec f smaller.
Proof.
 unfold all_Type.
 unfold incl_sets.
 intuition.
Qed.

Lemma all_map_Type:
  forall A eq_dec P f (xs : set A),
    (all_Type _ eq_dec P (set_map eq_dec f xs))
    -> (all_Type _ eq_dec (fun x => P (f x)) xs).
Proof.
 intros ? ? ? ? ? H.
 unfold all_Type in *.
 intros.
 pose (H1:=H (f x)).
 apply H1.
 apply set_map_intro; auto.
Qed.

(* Lemma set_map_image_2: *)
(*   forall A B eq_dec (f:A->B) x xs, *)
(*     (true = set_mem eq_dec x (set_map eq_dec f xs)) -> {x' | x = f x' /\ set_In x' xs}. *)
(* Proof. *)
(*   induction xs. *)
(*   simpl. *)
(*   discriminate. *)
(*  simpl. *)
(*  intro H. *)
(*  apply set_add_elim in H. *)
(*  lapply IHxs. *)
(*   firstorder. *)
(*  destruct H. *)

(*  exists a; auto. *)
(*  firstorder. *)
(* Qed. *)

(* Lemma all_map_Type_rev: *)
(*   forall A eq_dec P f (xs : set A), *)
(*   (all_Type _ eq_dec (fun x => P (f x)) xs) *)
(*     -> (all_Type _ eq_dec P (set_map eq_dec f xs)). *)
(* Proof. *)
(*  intros ? ? ? ? ? H. *)
(*  unfold all_Type in *. *)
(*  intros. *)
(*  pose (H1:=H (f x)). *)
(*  apply H1. *)
(*  apply set_map_intro; auto. *)
(* Qed. *)

(* Lemma all_Type_add_rev: *)
(*   forall A eq_dec P (a:A) xs, *)
(*     all_Type _ eq_dec P (set_add eq_dec a xs) *)
(*     -> (P a * all_Type _ eq_dec P xs)%type. *)
(* Proof. *)
(*  unfold all_Type. *)
(*  intros. *)
(*  split. *)
(*   apply X. *)
(*   apply set_add_intro; auto. *)
(*  intros. *)
(*  apply X. *)
(*  apply set_add_intro; auto. *)
(* Qed. *)

Lemma all_Type_map_fwd:
  forall A eq_dec pred f xs,
    (all_Type A eq_dec pred (set_map eq_dec f xs) -> all_Type A eq_dec (fun x => pred (f x)) xs).
Proof.
 unfold all_Type, set_map.
 intros.
 apply X.
 change (set_In (f x) (set_map eq_dec f xs)).
 apply set_map_intro; auto.
Qed.

(* Lemma all_Type_map_rev: *)
(*   forall A eq_dec pred f xs, *)
(*     (all_Type A eq_dec (fun x => pred (f x)) xs -> all_Type A eq_dec pred (set_map eq_dec f xs)). *)
(* Proof. *)
(*  unfold all_Type, set_map. *)
(*  intros. *)
(*  assert (H1:In x (set_map eq_dec f xs)). *)
(*   intuition. *)
(*  apply set_map_image in H1. *)
(*  destruct H1 as [y [H1 H2]]. *)
(*  subst x. *)
(*  apply H; auto. *)
(* Qed. *)

Lemma all_cut_Type :
  forall A eq_dec P Q xs,
    (forall x, set_In x xs -> P x -> Q x) ->
    all_Type A eq_dec P xs ->
    all_Type A eq_dec Q xs.
Proof.
 unfold all_Type in *.
 intros.
 apply X; auto.
Qed.

Lemma In_add_intro:
  forall A eq_dec (x y:A) xs,
  ({x = y}+{In x xs}) -> In x (set_add eq_dec y xs).
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

Lemma all_Type_add_fwd:
  forall A eq_dec P (a:A) xs,
    (P a * all_Type _ eq_dec P xs)%type
    -> all_Type _ eq_dec P (set_add eq_dec a xs).
Proof.
 intuition.
 unfold all_Type.
 intros.
 apply Lists.ListSet.set_add_elim in H.
 destruct (eq_dec x a).
 subst; auto.
 assert (set_In x xs) by tauto.
 auto.
Qed.

Lemma all_Type_nil:
  forall A eq_dec P, all_Type A eq_dec P nil.
Proof.
 unfold all_Type.
 simpl.
 easy.
Qed.

Hint Resolve all_Type_nil.

Lemma Interesting_Lemma:
  forall A (eq_dec : DecidableEquality A) (x:A) xs,
    {set_In x xs} + {~set_In x xs}.
Proof.
 induction xs.
  intuition.
 destruct IHxs.
 left.
 simpl.
 auto.
 simpl.
 destruct (eq_dec a x).
  intuition.
 intuition.
Qed.

Lemma all_Type_union_fwd:
  forall A eq_dec pred xs ys,
    (all_Type A eq_dec pred xs * all_Type A eq_dec pred ys) ->
    all_Type A eq_dec pred (set_union eq_dec xs ys) .
Proof.
 intros ? ? ? ? ? [H0 H1].
 unfold all_Type in *.
 intros.
 apply set_union_elim in H.
 pose (Interesting_Lemma _ eq_dec x xs).
 destruct s.
 auto.
 assert (set_In x ys) by tauto.
 auto.
Qed.

Ltac sufficient H :=
  cut H; [solve[auto] | ].

Lemma all_Type_union_rev:
  forall A eq_dec pred xs ys,
    all_Type A eq_dec pred (set_union eq_dec xs ys) ->
    (all_Type A eq_dec pred xs * all_Type A eq_dec pred ys).
Proof.
 unfold all_Type.
 intros ? ? ? ? ? H.
 sufficient (forall x, (set_In x xs \/ set_In x ys) -> pred x).
 intros.
 auto.
Qed.

(* Lemma all_Type_union: *)
(*   forall A eq_dec P xs ys, *)
(*     all_Type A eq_dec P xs -> *)
(*     all_Type A eq_dec P ys -> *)
(*     all_Type A eq_dec P (set_union eq_dec xs ys). *)
(* Admitted. *)

(* Lemma all_Type_remove: *)
(*   forall A dec_eq (pred:A->Type) x xs, *)
(*     all_Type A dec_eq (fun y => sumor (y = x) (~ notT(pred y))) xs *)
(*     -> all_Type A dec_eq pred (set_remove _ dec_eq x xs). *)
(* Proof. *)
(*  induction xs; simpl; intros. *)
(*   unfold all_Type; simpl. *)
(*   intros. *)
(*   discriminate. *)
(*  unfold all_Type in X. *)
(* unfold set_mem in X. *)
(*  pose (H := X a). *)
(*  destruct (dec_eq x a). *)
(* Admitted. *)

Lemma all_Type_universal:
  forall A eq_dec pred xs,
    (forall x, pred x) -> all_Type A eq_dec pred xs.
Proof.
 induction xs; unfold all_Type; simpl; intros; auto.
Qed.

Lemma all_Type_filter : forall A eq_dec P P' xs,
                (forall x:A, true = P' x -> P x) ->
                all_Type _ eq_dec P (set_filter _ P' xs).
 intros.
 unfold all_Type.
 intros x H0.
 apply set_filter_elim in H0.
 intuition.
Qed.

Lemma all_Type_map_1 :
  forall A eq_dec pred f xs,
    all_Type A eq_dec pred (set_map eq_dec f xs)
      -> all_Type A eq_dec (fun x => pred (f x)) xs.
Proof.
 unfold all_Type in *.
 intros.
 specialize (X (f x)).
 apply X.
 apply set_map_intro.
 auto.
Qed.


Lemma all_Type_map_2 :
  forall A eq_dec pred f xs,
    all_Type A eq_dec (fun x => pred (f x)) xs
    -> all_Type A eq_dec pred (set_map eq_dec f xs).
Proof.
 unfold all_Type in *.
 intros.
 apply (set_mem_correct2 eq_dec) in H.
 symmetry in H.
 apply set_map_elim_Type in H.
 destruct H.
 pose (X x0).
 destruct a.
 subst x.
 apply p.
 auto.
Qed.