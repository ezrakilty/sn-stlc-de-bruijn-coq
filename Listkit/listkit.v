(** List Utilities *)

Require Import List.

Require Export NthError.

Require Export Foreach.

Require Export All.

Lemma nth_error_foreach_ty :
  forall A P v n xs,
    nth_error xs n = value v -> foreach_ty A xs P -> P v.
Proof.
 induction n; simpl; intros; (destruct xs; [discriminate | ]).
  destruct X as [H0 ?].
  inversion H.
  congruence.
 firstorder.
Qed.
Lemma nth_error_In:
  forall A xs x (v:A),
    nth_error xs x = value v -> ListSet.set_In v xs.
Proof.
 induction xs; unfold nth_error; simpl.
  intros.
  destruct x; discriminate.
 intros x v H.
 destruct x.
  inversion H.
  auto.
 right.
 eapply IHxs; eauto.
Qed.

Lemma nth_error_all:
  forall A xs x v f,
    nth_error xs x = value v ->
    all A f xs ->
    f v.
Proof.
 induction xs; unfold all; simpl; intros.
  unfold nth_error in H.
   destruct x; discriminate.
 apply H0.
 destruct x; simpl in *.
  left; inversion H; auto.
 right.
 apply nth_error_In with x; auto.
Qed.
