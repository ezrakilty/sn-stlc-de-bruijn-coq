Require Import List.

Require Import Term.
(* TODO: Shift and Subst are needed only to appease the final line
where I offer a beta-reduced term for Coq's benefit. It should really
be able to deduce that term by itself, and I wouldn't need to name
these crotchety details. *)
Require Import Shift.
Require Import Subst.
Require Import Rewrites.
Require Import Norm.
Require Import sn3.

Definition Rewrites M := { Z : Term & M ~> Z }.
Definition Normal M := notT (Rewrites M).

(* Notation "M ~/" := (Normal M) (at level 100). *)

Inductive IsPair M :=
  is_pair_of A B : TmPair A B = M -> IsPair M.

Lemma Normal_decidable:
  forall M env T,
    Typing env M T -> Rewrites M + {Normal M}.
Proof.
 intros M.
 unfold Normal.
 induction M; simpl; intros env T tp; inversion tp; subst.
      right; intros [? r]; inversion r.
     right; intros [? r]; inversion r.
 (* Case TmPair *)
     specialize (IHM1 env s H1).
     specialize (IHM2 env t H3).
     destruct IHM1. (* Favor the first pair component; reduce it first. *)
      left.
      destruct r.
      exists (TmPair x M2); eauto.
     destruct IHM2.
      left.
      destruct r.
      exists (TmPair M1 x); eauto.
     right; intro H; destruct H; inversion r; firstorder.
 (* Case TmProj false *)
    specialize (IHM env (TyPair T t) H2).
    unfold Rewrites.
    destruct IHM.
     left.
     destruct r.
     eauto.
    destruct M; try (solve [right; intros [? r]; inversion r; firstorder]).
     left; eauto.
 (* Case TmProj true *)
   specialize (IHM env (TyPair s T) H2).
   unfold Rewrites.
   destruct IHM.
    left.
    destruct r.
    eauto.
   destruct M; try (solve [right; intros [? r]; inversion r; firstorder]).
    left; eauto.
 (* Case TmAbs *)
  destruct (IHM (s::env) t H0).
   left; unfold Rewrites in *.
   destruct r as [M' H].
   eauto.
  right.
  contrapose n.
  destruct n.
  unfold Rewrites.
  inversion r.
  eauto.
 (* Case TmApp *)
 destruct (IHM1 env _ H1).
  left.
  destruct r.
  exists (TmApp x M2); eauto.
 destruct (IHM2 env _ H3).
  left.
  destruct r.
  exists (TmApp M1 x); eauto.
 unfold Rewrites.
 destruct M1; try (solve [right; intros [? r]; inversion r; firstorder]).
 left.
 (* TODO: I shouldn't have to give this explicitly. Coq should be able to deduce it. :-( *)
 set (Z := unshift 0 1 (subst_env 0 (shift 0 1 M2 :: nil) M1)).
 exists Z.
 eauto.
Qed.

Lemma normalization_algorithm:
  forall M T,
    Typing nil M T ->
    { Z : Term & ((M ~>> Z) * Normal Z) %type}.
Proof.
 intros.
 assert (SN M).
  apply normalization with T; auto.
 redseq_induction M.
 assert (H2 : Typing nil M0 T) by eauto.
 assert (SN M0).
  eapply Rw_trans_preserves_SN; eauto. (* TODO: Hint Resolve *)

 destruct (Normal_decidable M0 nil T H2).
  destruct H3 as [s].
  destruct r as [M1 r].
  pose (s M1 r).
  pose (IHM M1 r).
  lapply s1; [intro| eauto].
   destruct H3 as [Z [H4 H5]].
   exists Z.
   intuition (eauto).
  eauto.
Qed.
