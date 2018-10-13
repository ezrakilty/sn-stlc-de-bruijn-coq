Require Import Omega.

Require Import Continuation.
Require Import Rewrites.
Require Import Norm.
Require Import Term.

(** * More Induction Principles on Reduction Sequences *)
(** These require knowledge of Continuation.v, so can't be placed in Norm.v *)
(** Continuations have their own "strong normalization" on their own reduction
    rule. *)
Inductive Krw_norm K :=
  reducts_Krw_norm : (forall K', Krw K K' -> Krw_norm K') -> Krw_norm K.

Inductive Triple_SN K M N :=
  | triple_sn :
       (forall K', (Krw K K') -> Triple_SN K' M N)
    -> (forall M', (M ~> M') -> Triple_SN K M' N)
    -> (forall N', (N ~> N') -> Triple_SN K M N')
    -> Triple_SN K M N.

Lemma triple_induction_via_TripleSN P:
  (forall K M N,
        (forall K',  (Krw K K') -> P K' M N)
     -> (forall M',  (M ~> M') ->  P K M' N)
     -> ((forall N', (N ~> N') ->  P K M N'))
     -> P K M N)
  ->
  forall K M N,
    Triple_SN K M N -> P K M N.
Proof.
 intros IH K M N SN_K_M_N.
 induction SN_K_M_N.
 auto.
Qed.

Lemma triple_induction_via_TripleSN_scoped P:
  forall K0 M0 N0,
  (forall K M N,
     Krw_rt K0 K -> (M0 ~>> M) -> (N0 ~>> N) ->
        (forall K',  (Krw K K') -> P K' M N)
     -> (forall M',  (M ~> M') ->  P K M' N)
     -> ((forall N', (N ~> N') ->  P K M N'))
     -> P K M N)
  ->
    Triple_SN K0 M0 N0 -> P K0 M0 N0.
Proof.
 intros K0 M0 N0 IH SN_K0_M0_N0.
 induction SN_K0_M0_N0.
 apply IH; auto.
 intros; apply X; auto.
 intros; apply IH; eauto.
 intros; apply X0; auto.
 intros; apply IH; eauto.
 intros; apply X1; auto.
 intros; apply IH; eauto.
Qed.

Lemma Triple_SN_intro:
  forall K, Krw_norm K -> forall M, SN M -> forall N, SN N -> Triple_SN K M N.
Proof.
 intros K SN_K.
 induction SN_K.
 intros M SN_M.
 induction SN_M.
 intros N SN_N.
 induction SN_N.
 constructor; sauto.
Qed.

Lemma triple_induction_scoped P:
  forall K0 M0 N0,
  (forall K M N,
     Krw_rt K0 K -> (M0 ~>> M) -> (N0 ~>> N) ->
        (forall K',  (Krw K K') -> P K' M N)
     -> (forall M',  (M ~> M') ->  P K M' N)
     -> ((forall N', (N ~> N') ->  P K M N'))
     -> P K M N)
  ->
    Krw_norm K0 -> SN M0 -> SN N0 -> P K0 M0 N0.
Proof.
 intros K0 M0 N0 IH SN_K0 SN_M0 SN_N0.
 apply triple_induction_via_TripleSN_scoped; auto.
 apply Triple_SN_intro; auto.
Qed.

(** A continuation that is part of, and downstream of, a SN term, is normalizing. *)
Lemma SN_context_Krw_norm:
  forall X X',
    SN X ->
    (X ~>> X') ->
    forall K,
    {M : Term & X' = plug K M} ->
    Krw_norm K.
Proof.
 intros X X' SN_X X_red_X'.
 assert (SN_X' : SN X').
  eauto.
 induction SN_X'.
 intros K ex_M.
 constructor.
 intros K' K_K'.
 destruct ex_M as [M H1].
 assert (plug K M ~> plug K' M) by auto.
 subst.
 apply H with (m':=plug K' M); eauto.
Qed.

Lemma SN_via_Krw_rt :
  forall K K' M,
    Krw_rt K K' -> SN (plug K M) -> SN (plug K' M).
Proof.
 intros.
 assert (plug K M ~>> plug K' M).
  auto using Krw_rt_Rw_rt.
 eauto using Rw_trans_preserves_SN.
Qed.

Lemma SN_via_Krw :
  forall K K' M,
    Krw K K' -> SN (plug K M) -> SN (plug K' M).
Proof.
 intros.
 assert (plug K M ~> plug K' M).
  auto.
 eauto using Rw_trans_preserves_SN.
Qed.

Lemma Krw_norm_from_SN:
  forall Q, SN Q -> forall K M, (Q ~>> plug K M) -> Krw_norm K.
Proof.
 intros Q H.
 induction H.
 constructor.
 intros.
 eapply last_step_first_step_lemma in H0.
  destruct H0.
  destruct p.
  eapply H; eauto.
 eauto.
Qed.

(** (Lemma 26) *)
Lemma SN_K_M_SN_K_Null:
  forall K M,
    SN (plug K M) ->
    SN (plug K TmNull).
Proof.
 induction K using Ksize_induction_strong.
 rename H into IHK.
 intros M H0.
 apply SN_embedding2 with
     (f := fun k => plug k M)
     (g := fun k => plug k TmNull)
     (Q := plug K M)
     (Q' := plug K TmNull); try auto.
 intros K0 Z H2 H3.

 let T := type of H3 in copy T.
 apply K_TmNull_rw in H3 as [[K_shorter [N H1a H1b]] | [K' H1a H1b]].
 (* Case [plug K0 TmNull] drops a frame. *)
  right.
  subst.

  (* XXX this is terribly ugly. must be a simpler way *)
  assert (relK_rt K K_shorter).
   assert (relK_rt K (Iterate N K_shorter)).
    apply K_TmNull_relK_rt.
    auto.
   apply trans with (K' := Iterate N K_shorter).
    auto.
   apply step.
   eapply strip; eauto.
  apply magic with (M:=M) in H1; auto.

  destruct H1 as [M' SN_M'].

  apply IHK with (M:=M'); auto.
  apply Rw_rt_conserves_Ksize in H2.
  simpl in *; sauto.

 (* Case K0 ~> K' *)
 left.
 exists K'.
 firstorder.
Qed.

(** (Lemma 30) *)
Lemma SN_K_Union:
  forall K,
  forall M N, SN (plug K M) -> SN (plug K N) -> SN (plug K (TmUnion M N)).
Proof.
 intros K'.
 pattern K'.
 apply Ksize_induction_strong; intros.

 clear K'.

 assert (SN M) by (eauto using SN_push_under_k).
 assert (SN N) by (eauto using SN_push_under_k).
 assert (Krw_norm K) by (eauto using Krw_norm_from_SN).
 apply triple_induction_scoped with (K0 := K) (M0 := M) (N0 := N); auto.
 intros.

 apply reducts_SN.
 intros Z H_rw.

 destruct K0.
 - simpl in *.
   inversion H_rw; subst; auto.

 - simpl in H_rw.

   apply three_ways_to_reduce_at_interface in H_rw as
       [[[[M' Z_def rw] | [K' Z_def rw]] | [H' [K' [M' ? [? ? H_bogus]]]]] | ?].
   * (* Case: rw is within TmBind (TmUnion M N) t *)
     subst.
     inversion rw; subst.
     -- (* Case: rw is zippering TmUnion thru TmBind _ _ *)
       assert (Ksize K0 < Ksize K).
       { assert (Ksize (Iterate t K0) <= Ksize K).
         { apply Krw_rt_conserves_Ksize with (K := K); auto. }
         simpl in *; omega. }
       apply H; auto.
       eapply plug_SN_rw_rt with (TmBind M t); auto.
       { auto using Rw_rt_Bind_left. }
       change (SN (plug (Iterate t K0) M)).
       { eauto using SN_via_Krw_rt. }
       eapply plug_SN_rw_rt with (TmBind N t); auto.
       { auto using Rw_rt_Bind_left. }
       change (SN (plug (Iterate t K0) N)).
       { eauto using SN_via_Krw_rt. }
     -- (* Case: rw is within TmUnion _ _ *)
       inversion H14; subst; seauto.

   (* Case: rw is within t of TmBind (TmUnion M N) t *)
     -- change (SN (plug (Iterate n' K0) (TmUnion M0 N0))).
        assert (Krw (Iterate t K0) (Iterate n' K0)).
        ** unfold Krw.
           simpl.
           intros.
           apply Rw_under_K.
           eauto.
        ** apply H8.
           sauto.

   (* Case: rw is within K *)
   * subst.
     change (SN (plug (Iterate t K') (TmUnion M0 N0))).
     apply H8; auto.
   * (* Case: M is not a bind but it consumes a K frame. *)
     refute.
     unfold not in *; eauto using H_bogus.
     apply NotBind_TmBind in H_bogus; auto.
   * (* Case: M is a TmBind and we assoc with the context. *)
     destruct s as [L [L' ? [K' [N' Ha Hb]]]].
     inversion e.
     subst.
     rewrite reverse_plug_defn.
     apply H.
     simpl.
     apply Krw_rt_conserves_Ksize in H5.
     simpl in *.
     omega.
     -- apply SN_via_Krw with (Iterate L' (Iterate N' K')).
        { apply assoc_in_K. }
        apply SN_via_Krw_rt with K.
        auto.
        apply Rw_trans_preserves_SN with (plug K M).
        { auto. }
        { apply Rw_rt_under_K; auto. }
     -- apply SN_via_Krw with (Iterate L' (Iterate N' K')).
        { apply assoc_in_K. }
        apply SN_via_Krw_rt with K.
        auto.
        apply Rw_trans_preserves_SN with (plug K N).
        { auto. }
        { apply Rw_rt_under_K; auto. }
Qed.
