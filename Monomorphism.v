Require Import Coq.Lists.ListSet.

Require Import Listkit.Sets.

Definition monomorphism A B (f:A->B) : Prop := (forall x y, f x = f y -> x = y).

Lemma map_monomorphism:
  forall A B eq_dec X (f:A-> B) (x:A),
    (monomorphism _ _ f) ->
    (set_In x X <-> set_In (f x) (set_map eq_dec f X)).
Proof.
 unfold monomorphism.
 induction X; simpl; intros.
  split; auto.
 split; intros.
  destruct H0.
   subst a.
   apply set_add_intro.
   auto.
  apply set_add_intro.
  right.
  apply set_map_intro; auto.
 apply set_add_elim in H0.
 intuition.
 right.
 apply <- IHX; eauto.
Qed.
