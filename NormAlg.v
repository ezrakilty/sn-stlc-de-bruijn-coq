Add LoadPath "Listkit" as Listkit.

Require Import Rewrites.
Require Import Term.
Require Import Norm.

Definition reduces M :=
  {M' : Term & M ~> M'}.

Definition normal V :=
  notT (reduces V).

Require Import Program.

Lemma normal_dec M :
  normal M + reduces M.
Proof.
 induction M.
 - left; intros [H0 r]; inversion r.
 - left; intros [H0 r]; inversion r.
 - destruct IHM1, IHM2.
   * left; intros [H0 r]; inversion r.
     -- unfold normal in *. apply n. unfold reduces. eauto.
     -- unfold normal in *. apply n0. unfold reduces. eauto.
   * right. unfold reduces in *. destruct r. eauto.
   * right. unfold reduces in *. destruct r. eauto.
   * right. unfold reduces in *. destruct r. eauto.
 - destruct IHM.
   * destruct M; try (solve [left; intros [H0 r]; inversion r; firstorder]).
     right.
     unfold reduces.
     destruct b; eauto.
   * right; destruct r; unfold reduces; eauto.

 - destruct IHM.
   * left; intros [H0 r]; inversion r; firstorder.
   * right; destruct r; unfold reduces; eauto.

 - destruct IHM1; [destruct IHM2|].
   destruct M1; try (solve [left; intros [H0 r]; inversion r; firstorder]).
   * right.
     unfold reduces.
     eauto.
   * right; unfold reduces; destruct r; eauto.
   * right; unfold reduces; destruct r; eauto.

 - left; intros [H0 r]; inversion r.
 - destruct IHM.
   * left; intros [H0 r]; inversion r; firstorder.
   * right; destruct r; unfold reduces; eauto.

 - destruct IHM1; [destruct IHM2|].
   * left; intros [H0 r]; inversion r; firstorder.
   * right; destruct r; unfold reduces; eauto.
   * right; destruct r; unfold reduces; eauto.

 - destruct IHM1; [destruct IHM2|].
   * destruct M1; try (solve [left; intros [H0 r]; inversion r; firstorder]).
     -- right; unfold reduces; eauto.
     -- right; unfold reduces; eauto.
     -- right; unfold reduces; eauto.
     -- right; unfold reduces; eauto.

   *  right; unfold reduces; destruct r; eauto.

   * right; unfold reduces; destruct r; eauto.

(* ??? *)
Unshelve.
exact 0.
Qed.

Require Import sn.

Lemma normalize M T :
  Typing nil M T ->
  {V : Term & M ~>> V & normal V}.
Proof.
 intros.
 assert (SN M).
 { eapply normalization; eauto. }
 induction H0.
 destruct (normal_dec m).
 { eauto. }
 destruct r.
 assert (Typing nil x T).
 { eauto using Rw_preserves_types. }
 destruct (H0 x r H1).
 assert (m ~>> x0) by eauto.
 eauto.
Qed.
