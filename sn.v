(** To compile, from the parent directory:
  coqc sn-shipit/sn2 -R Listkit Listkit
*)

(******************************************************************************)

(** Strong Normalization for the Simply-Typed Lambda Calculus *)

Load "eztactics.v".

Add LoadPath "Listkit" as Listkit.

Require Import List.
Require Import Arith.

Require Import Listkit.logickit.
Require Import Listkit.NthError.
Require Import Listkit.Foreach.
Require Import Listkit.Sets.
Require Import Listkit.AllType.
Require Import Listkit.listkit.

(* Add LoadPath ".". *)

Require Import Term.
Require Import Shift.
Require Import Subst.
Require Import Rewrites.
Require Import Norm.
Require Import Typing.
Require Import Monomorphism.

Hint Rewrite app_comm_cons : list.

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Definition set_remove := Listkit.Sets.set_remove.

(* TODO Grumble, grumble. Coq makes macros of this sort useless. *)
(* Definition nat_set_map := set_map (A:=nat) eq_nat_dec.
   Hint Transparent nat_set_map.
   Hint Unfold nat_set_map. *)

Import Setoid.

Require Import Coq.Program.Basics. (* TODO: What's this for?? *)

Require Import Coq.Logic.FunctionalExtensionality.  (* Assumes an axiom. *)

Require Import Bool.

Require Import OutsideRange.

Require Import Continuation.

Hint Resolve subst_env_compat_Rw_trans.


(******************************** REDUCIBILITY ********************************)

Set Universe Polymorphism.

(* Set Printing Universes. *)

(** * Reducibility *)
Fixpoint Reducible (tm:Term) (ty:Ty)  {struct ty} : Type :=
  (** To be reducible, a term ... *)
  (Typing nil tm ty * (** ... must be well-typed at ty and *)
  match ty with
  | TyBase => SN tm (** ... at unit type, strongly normalizes *)
  | TyPair s t =>
    Reducible (TmProj false tm) s * Reducible (TmProj true tm) t
  | TyArr s t =>
    (forall l (s_tp:Typing nil l s),
       Reducible l s ->
        Reducible (TmApp tm l) t)
      (** ... at arrow type, must give a reducible term when applied
           to any reducible term. *)
  | TyList s =>
      let ReducibleK (K : Continuation) (T:Ty) :=
          forall M,
            Reducible M T ->
            SN (plug K (TmSingle M))
      in
      forall K, ReducibleK K s -> SN (plug K tm)
  end)%type
.

Fixpoint env_Reducible Vs Ts : Type :=
  match Vs, Ts with
    | nil, nil => True%type
    | V::Vs, T::Ts => (Reducible V T * env_Reducible Vs Ts)%type
    | _, _ => False
  end.

Lemma Reducible_welltyped_closed :
  forall tm ty, Reducible tm ty -> Typing nil tm ty.
Proof.
 destruct ty; firstorder auto.
Qed.

Hint Immediate Reducible_welltyped_closed.

(** The Rewrites relation preserves reducibility. *)
Lemma Rw_preserves_Reducible :
 forall T M, Reducible M T -> forall M', (M ~> M') -> Reducible M' T.
Proof.
 induction T; simpl.
    firstorder using Rw_preserves_types.
    inversion b; auto.
   solve [firstorder using Rw_preserves_types].
  solve [firstorder using Rw_preserves_types].
 intros.
 split; eauto using Rw_preserves_types.
 intros.
 assert (H2 : SN (plug K M)) by firstorder.
 inversion H2 as [H3].
 apply (H3 (plug K M')).
 apply Rw_under_K.
 auto.
Qed.

(** The reflexive-transitive Rewrites relation preserves reducibility. *)
Lemma Rw_rt_preserves_Reducible :
 forall T M, Reducible M T -> forall M', (M ~>> M') -> Reducible M' T.
Proof.
 intros T M R M' red.
 induction red; subst; auto.
 eapply Rw_preserves_Reducible; eauto.
Qed.

Hint Resolve Rw_rt_preserves_Reducible.

Lemma SN_TmSingle:
  forall M,
    SN M -> SN (TmSingle M).
Proof.
  intros.
  redseq_induction M.
 apply reducts_SN.
 intros.
 inversion H1.
 subst.
 apply IHM; eauto.
Qed.

Lemma Krw_preserves_ReducibleK :
  forall T K K',
  Krw K K' -> ReducibleK Reducible K T -> ReducibleK Reducible K' T.
Proof.
 unfold ReducibleK.
 intros.
 specialize (X M X0).
 inversion X.
 specialize (H0 (plug K' (TmSingle M))).
 apply H0.
 auto.
Qed.

Lemma Krw_rt_preserves_ReducibleK :
  forall T K K',
  Krw_rt K K' -> ReducibleK Reducible K T -> ReducibleK Reducible K' T.
Proof.
 intros T K K' H.
 induction H; subst; eauto using Krw_preserves_ReducibleK.
Qed.

Inductive Krw_norm K :=
  reducts_Krw_norm : (forall K', Krw K K' -> Krw_norm K') -> Krw_norm K.

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

(* TODO: This seems to be a cheesy way of helping the Reducible_properties.
Afterwards, one of the premises is always true, so we can simplify it. *)
Lemma ReducibleK_Krw_norm_helper:
  forall T K, ReducibleK Reducible K T ->
              {M : Term & Reducible M T} ->
              Krw_norm K.
Proof.
 unfold ReducibleK.
 intros.
 destruct X0.
 apply SN_context_Krw_norm with (X := plug K (TmSingle x)) (X' := plug K (TmSingle x)); eauto.
Qed.

(** The [Reducible] predicate has these important properties which
    must be proved in a mutually-inductive way. They are:
      1. Every type has a [Reducible] term,
      2. Every [Reducible] term is strongly normalizing.
      3. If [M] is a neutral term at type [T], and all of its reducts
         are [Reducible], then it is itself [Reducible].
   Below, we split these out into separate lemmas.
*)
(* TODO: A little messy. Clean up. *)
Lemma Reducible_properties:
  forall T,
    {tm : Term & Reducible tm T} *
    (forall tm, Reducible tm T -> SN tm) *
    (forall M,
      Neutral M -> Typing nil M T ->
      (forall M', (M ~> M') -> Reducible M' T)
      -> Reducible M T).
Proof.
 induction T.
 (* Case TyBase *)
    splitN 3.
    (* Exists a Reducible term at TyBase *)
      simpl; seauto.
    (* Reducible -> SN *)
     simpl.
     solve [tauto].
    (* Neutral terms withdraw *)
    unfold Reducible in *.
    intuition (apply reducts_SN).
    solve [firstorder].

 (* Case TyPair *)
    splitN 3.
    (* Case: exists a reducible term *)
     destruct IHT1 as [[[M M_red] Reducible_SN_T1] Neutral_Reducible_T1].
     destruct IHT2 as [[[N N_red] Reducible_SN_T2] Neutral_Reducible_T2].
     exists (TmPair M N).
     simpl.
     split; [auto | ].

     (* Case: When continuation frames (left & right projections) are applied, a
        reducible term is formed. *)
     split.

     (* Case: left projection *)
     (* TODO: double_induction_SN needs us to prove that an arbitrary
        transitive reduct of the term is reducible; but I think it
        would be fine to prove just that the term itself is so. *)
      double_induction_SN_intro M N.
      (* Because (TmProj _ _) is Neutral, it's sufficient to show that all its
         reducts are reducible. *)
      apply Neutral_Reducible_T1; [seauto | seauto | ].
      intros Z H.
      inversion H.
      (* Case: <M', N'> itself reduces *)
       subst.
       inversion H3.
       (* Case: reduction in rhs *)
        subst m1 n m2.
        apply IHM; seauto.
       (* Case: reduction in lhs *)
       subst m n1 m2.
       apply IHN; seauto.
      (* Case: The reduct is at the head; we project. *)
      subst m n Z.
      seauto.

     (* Case: right projection *)
     (* TODO: refactor between the TmProj true / TmProj false cases. *)
     double_induction_SN_intro M N.
     (* Because (TmProj _ _) is Neutral, it's sufficient to show that all its
        reducts are reducible. *)
     apply Neutral_Reducible_T2; [seauto | | ].
      (* TODO: why does the TProj1 case go with seauto but this needs me
         to tell is what lemma to use? *)
      apply TProj2 with T1; seauto.
     intros Z H.
     inversion H.
     (* Case: <M', N'> itself reduces *)
      subst.
      inversion H3.
       subst m1 n m2.
       apply IHM; seauto.
      subst m n1 m2.
      apply IHN; seauto.
     (* Case: The reduct is at the head; we project. *)
     subst m n Z.
     seauto.

   (* Case: Reducible pair-type terms are strongly normalizing *)
    simpl.
    intuition.
    assert (SN (TmProj false tm)) by auto.
    eapply SN_context_Proj; seauto.

   (* Case: Neutral terms at pair type whose reducts are reducible are
      themselves reducible (reducibility "withdraws"). *)
   intros M M_Neutral M_Typing M_reducts_Reducible.
   destruct IHT1 as [[? ?] l_withdraws].
   destruct IHT2 as [[? ?] r_withdraws].
   simpl. (* this is only true if both destructors (projections) are reducible. *)
   split; [sauto | ].
   (* Split into left and right projections. *)
   split; [apply l_withdraws | apply r_withdraws]; eauto.
   (* Case: left projection. *)
    intros M' H. (* Consider all reducts of the projection. *)
    inversion H.
    (* Case: The reduction is in the subject term. *)
     pose (M_reducts_Reducible m2 H3). (* Then the subject's reduct is Reducible. *)
     simpl in r.
     solve [intuition]. (* Which by definition entails our goal. *)
    (* Case: The reduction is at the head; it is the projection. But the subject
             being neutral, it is not a pair, so contradiction. *)
    subst m M.
    solve [inversion M_Neutral].
   (* Case: right projection. *)
   intros M' H.
   inversion H.
    pose (r := M_reducts_Reducible m2 H3).
    simpl in r.
    solve [intuition].
   subst n M.
   solve [inversion M_Neutral].

  (* Case TyArr *)
  splitN 3.
  (* Exists a reducible term at T1->T2 *)
    destruct IHT2 as [[[N N_Red] Red_T2_tms_SN] IHT2_Red_neutral_withdraw].
    (* Given any term at T2, we can abstract it with a dummy argument.
       (shift 0 1) gives us uniqueness of the argument. *)
    exists (TmAbs (shift 0 1 N)).
    split.
    (* The dummy abstraction has the appropriate type. *)
     sauto.
    (* It is reducible at -> type; it applied to any reducible term gives
       a reducible application. *)
    intros M M_tp M_Red.
    assert (SN N) by auto.
    destruct IHT1 as [[_ Red_T1_tms_SN] _].
    assert (SN M) by auto.
    pattern N, M.
    (* TODO: The double redseq induction pattern. Abstract out! *)
    double_induction_SN_intro M N.
    (* We'll show that all reducts are reducible. *)
    apply IHT2_Red_neutral_withdraw; eauto.
     apply TApp with T1; seauto.
    intros M'' red.
    (* Take cases on the reductions. *)
    inversion red as [ | ? Z ? redn_Z | | | | | | | | | | | | | | | ] ; subst.
    (* beta reduction *)
       (* BUG: should be able to put these all as args to congruence. *)
       pose subst_dummyvar; pose subst_nil; pose unshift_shift.
       replace (unshift 0 1 (subst_env 0 (shift 0 1 M' :: nil) (shift 0 1 N')))
         with N' by congruence.
       apply Rw_rt_preserves_Reducible with N; sauto.
    (* Reduction of the function position. *)
      inversion redn_Z.
      subst Z.
      destruct (shift_Rw_inversion _ _ _ H2) as [N'' [N''_def N'0_rew_N'']].
      subst n'.
      apply IHN; seauto.
    (* Reduction of the argument position. *)
     apply IHM; seauto.

  (* Reducibile S->T terms are SN. *)
   intros M M_red.
   destruct M_red as [M_tp M_applied_Red].
   destruct IHT1 as [[[X Red_X] _] _].
   assert (Reducible (M@X) T2).
    apply M_applied_Red; seauto.
   assert (SN (M@X)).
    solve [firstorder] (* Finds the needed lemma in IHT2 *).
   apply SN_context_App_left with X; sauto.

  (* Reducible Neutral withdraw for (->) *)
  intros M Neutral_M M_tp M_reducts_Reducible.
  simpl.
  split; [auto|].
  intros L L_tp L_Red.
  apply IHT2; [sauto|seauto|].
  (* Now to show that all the reducts of the application M@L are reducible. *)
  intros M_L_reduct H.
  assert (X : forall L', (L ~>> L') -> Reducible (TmApp M L') T2).
   intros L' L_redto_L'.
   assert (SN L').
    apply Rw_trans_preserves_SN with L; auto.
    apply IHT1; auto.
   redseq_induction L'.
   apply IHT2; auto.
    seauto (* typing *).
   intros Z Z_red.
   (* Take cases on the reduction M@M0 ~> Z *)
   inversion Z_red.
   (* Beta-reduction case: bogus because M is neutral. *)
     subst.
     solve [inversion Neutral_M].
   (* Left of (@) case: easy from M_reducts_Reducible. *)
    subst m1 n.
    assert (Reducible_m2: Reducible m2 (TyArr T1 T2)).
     apply M_reducts_Reducible; sauto.
    simpl in Reducible_m2.
    apply Reducible_m2; seauto.
   (* Right of (@) case: by inductive hypothesis. *)
   rename n2 into L''.
   apply IHL'; seauto.
  assert (Reducible (M@L) T2).
   apply X; sauto.
  seauto.

 (* Case TyList *)
 destruct IHT as [[[N N_Red] Red_T_tms_SN] IHT_Red_neutral_withdraw].
 splitN 3.
 (* Existence of a reducible term. *)
   exists (TmSingle N).
   simpl.
   auto.
 (* Reducible terms are strongly normalizing. *)
  simpl.
  intros tm X.
  destruct X as [X0 X1].
  set (X2 := X1 Empty).
  simpl in X2.
  apply X2.
  simpl.
  intros M H.
  apply SN_TmSingle; sauto.
 (* Reducible Neutral Withdrawal for list terms. *)
 intros.
 simpl.
 split; auto.
 intros.
 change (ReducibleK Reducible K T) in X0.
 assert (Krw_norm K).
  apply ReducibleK_Krw_norm_helper with T; seauto.

 induction H1.
 constructor.
 intros m' H3.
 let T := type of H3 in copy T.
 apply Neutral_Lists in H3; auto.
 destruct H3 as [[M' [s1 s2]] | [K1 [s1 s2]]].
  subst.
  apply X; auto.

 subst.
 apply X1; auto.
 apply Krw_preserves_ReducibleK with K; auto.
Qed.

(** Now we extract the three lemmas in their separate, useful form. *)

(** Every reducible term is strongly normalizing. *)
Lemma Reducible_SN:
 forall ty, forall tm, Reducible tm ty -> SN tm.
Proof.
 firstorder using Reducible_properties.
Qed.

Hint Resolve Reducible_SN.

(** Every neutral term whose reducts are all [Reducible] is itself
    [Reducible]. *)
Lemma Neutral_Reducible_withdraw :
  forall T M,
    Neutral M ->
    Typing nil M T ->
    (forall M', (M ~> M') -> Reducible M' T)
    -> Reducible M T.
Proof.
 firstorder using Reducible_properties.
Qed.

(** Every type has a [Reducible] term. *)
Lemma Reducible_inhabited:
  forall T,
  {tm : Term & Reducible tm T}.
Proof.
 intros T.
  destruct (Reducible_properties T) as [[H _] _].
  auto.
Qed.

Lemma ReducibleK_Krw_norm:
  forall T K, ReducibleK Reducible K T ->
              Krw_norm K.
Proof.
 intros.
 eapply ReducibleK_Krw_norm_helper.
 apply X.
 apply Reducible_inhabited.
Qed.

(* XXX should be a direct consequence of env_Reducible's definition, if it were
defined in terms of [zip] and [and]. *)
Lemma Reducible_env_value:
  forall Vs Ts x V T,
    env_Reducible Vs Ts ->
    value V = nth_error Vs x ->
    value T = nth_error Ts x ->
    Reducible V T.
Proof.
 induction Vs; intros.
 - exfalso.
   destruct x; simpl in *; easy.
 - destruct Ts.
   { simpl in X; contradiction. }
   destruct x; simpl in *.
   * destruct X.
     inversion H0.
     inversion H.
     auto.
   * destruct X.
     eapply IHVs; eauto.
Qed.

Lemma lambda_reducibility:
  forall N T S,
  forall (Ts : list Ty) Vs,
    Typing (S::Ts) N T ->
    env_typing Vs Ts ->
    env_Reducible Vs Ts ->
    (forall V,
      Reducible V S ->
      Reducible (subst_env 0 (V::Vs) N) T) ->
    Reducible (subst_env 0 Vs (TmAbs N)) (TyArr S T).
Proof.
 intros N T S Ts Vs N_tp Vs_tp Vs_red H.
 split.

 (* Typing *)
  solve [eauto].

 (* Reducibility *)
 intros P P_tp P_red.

 simpl.
 replace (map (shift 0 1) Vs) with Vs
   by (symmetry; eauto).

 assert (SN P) by eauto.
 set (N'' := subst_env 1 Vs N).
 assert (SN_N'' : SN N'').
  assert (forall V, Reducible V S -> SN (subst_env 0 (V::nil) N'')).
   intros.
   apply Reducible_SN with T.
   subst N''.
   rewrite subst_env_concat with (env:=S::Ts).
    apply H; auto.
   simpl.
   apply Reducible_welltyped_closed in X.
   apply env_typing_intro; auto.
  destruct (Reducible_inhabited S) as [V V_Red].
  pose (X V V_Red).
  apply SN_embedding with (f := subst_env 0 (V::nil)) (Q := subst_env 0 (V::nil) N'').
    intros.
    apply subst_env_compat_rw; auto.
   auto.
  auto.
 (* The following strange pattern puts the goal in a form where
    SN_double_induction can apply. It effectively generalizes the
    goal, so that we prove it not just for N'' and P, but for
    "anything downstream of" the respective terms. *)
 double_induction_SN_intro P N''.
 subst N''.

 assert (Typing nil P' S) by eauto.
 assert (Reducible P' S) by eauto.
 apply Neutral_Reducible_withdraw; [sauto | seauto |].
 intros M' redn.

 inversion redn as [N0 M0 V M'_eq| ? ? ? L_redn | | | | | | | | | | | | | | |].

 (* Case: beta reduction. *)
   subst V M0 N0.
   replace (shift 0 1 P') with P' in M'_eq by (symmetry; eauto).
   simpl in M'_eq.
   replace (unshift 0 1 (subst_env 0 (P' :: nil) N'''))
      with (subst_env 0 (P' :: nil) N''') in M'_eq.

    rewrite M'_eq.
    assert (subst_env 0 (P' :: Vs) N ~>> subst_env 0 (P' :: nil) N''').
     replace (subst_env 0 (P'::Vs) N)
        with (subst_env 0 (P'::nil) (subst_env 1 Vs N)).
      auto.
     eapply subst_env_concat; simpl; solve [eauto].
    assert (Reducible (subst_env 0 (P'::Vs) N) T) by auto.
    solve [eauto].
   (* To show that unshift 0 1 has no effect on (subst_env 0 [P'] N'''). *)
   (* First, N, after substitution of P'::Vs, is closed: *)
   assert (Typing nil (subst_env 0 (P'::Vs) N) T).
    apply subst_env_preserves_typing with (S::Ts); solve [auto].
   (* Next, N''', after substitution of [P'], is closed: *)
   assert (Typing nil (subst_env 0 (P'::nil) N''') T).
    assert (Typing nil (subst_env 0 (P'::nil) (subst_env 1 Vs N)) T).
     erewrite subst_env_concat; simpl; solve [eauto].
     (* Rw_rt_preserves_types is automatic *)
    eapply Rw_rt_preserves_types; solve [eauto].
   symmetry; apply unshift_closed_noop with T; solve [auto].
 (* Case: Reduction in left subterm. *)
  inversion L_redn.
  subst n m1 m2 n0.
  apply IHN''; solve [eauto].
 (* Case: Reduction in right subterm. *)
 apply IHP; solve [eauto].
Qed.

Lemma TmProj_reducible:
  forall (M N : Term)
         (S T : Ty)
         (b : bool),
  Reducible M S ->
  Reducible N T ->
  SN M ->
  SN N ->
     Reducible (TmProj b (〈M, N〉)) (if b then T else S).
Proof.
 intros.
 double_induction_SN N M.
 intros x y X1 X2 H1 H2.

 apply Neutral_Reducible_withdraw; auto.
 (* Discharge the typing obligation. *)
 - assert (Typing nil y T) by eauto.
   assert (Typing nil x S) by eauto.
   destruct b; eauto.
 (* All reducts are reducible. *)
 - intros M' H3.
   (* Take cases on the reduction. *)
   inversion H3 as [ | | | | | | m n1 n2 H7 | m n | m n | | | | | | | |]; subst.
   (* Case: reduction under the operation. *)
   * inversion H7; subst; eauto.
   (* Case: beta-reduction on the left *)
   * eauto.
   (* Case: beta-reduction on the right *)
   * eauto.
Qed.

Lemma pair_reducible:
  forall M N S T,
    Reducible M S -> Reducible N T -> Reducible (TmPair M N) (TyPair S T).
Proof.
 intros.
 simpl.
 assert (Typing nil M S) by auto.
 assert (Typing nil N T) by auto.
 assert (SN M) by (eapply Reducible_SN; eauto).
 assert (SN N) by (eapply Reducible_SN; eauto).
 intuition.
 (* Case TmProj false *)
 - apply (TmProj_reducible M N S T false X X0 H1 H2).
 (* Case TmProj true *)
 - apply (TmProj_reducible M N S T true X X0 H1 H2).
Qed.

Lemma ReducibleK_Empty :
  forall T, ReducibleK Reducible Empty T.
Proof.
 unfold ReducibleK.
 simpl.
 intros; auto.
 apply SN_TmSingle.
 eauto using Reducible_SN.
Qed.

Hint Resolve ReducibleK_Empty.

(**
 When we have a form of term, specified by g, whose reductions are
all "found within" the corresponding form f, then if we have an
example SN term in the image of f, the corresponding term in g's image
is also SN.

The lemma also offers the possibility that some reducts of g-form
terms are not g-form terms, but then they must be shown to be SN by
some other means.
*)
(* TO DO: currently unused, but seems like it would be useful for some other lemmas. *)
Lemma SN_embedding3 (f g : Continuation -> Term -> Term -> Term):
  (* TODO: Where we apply this lemma, we need to know that g K M N is a descendent
     of something in order to prove SN Z. How do we narrow the scope of the first premise? *)
  (forall K M N Z, (g K M N ~> Z) ->
             {K' : Continuation & {M' : Term & {N' :Term & Z = g K' M' N'}}} + (SN Z)) ->
  (forall K M N K' M' N', (g K M N ~> g K' M' N') -> (f K M N ~> f K' M' N')) ->
  forall Q, SN Q ->
            forall K M N,
              (Q ~>> f K M N) -> SN (g K M N).
Proof.
 intros Hz H0 Q H1.
 induction H1.
 rename m into q.
 intros K M N H2.
 apply reducts_SN.
 intros.
 assert (SN (f K M N)).
  eauto.
 inversion H3.
 pose (H6 := Hz _ _ _ _ H1).
 inversion H6 as [[K' [M' [N' def_m']]] | SN_m'].
  subst.
  pose (H0 _ _ _ _ _ _ H1).
  assert (H10 : {x : Term & ((q ~> x) * (x ~>> f K' M' N'))%type}).
   apply last_step_first_step_lemma with (f K M N); auto.
  destruct H10 as [x [q_to_x x_to_f_K'_M'_N']].
  apply H with x; solve [auto].
 auto.
Qed.

Definition injective A B (f : A -> B) := forall x y, f x = f y -> x = y.

(** When [P] is reflexive, and transitive, and [P x y] follows from [f x ~> f y],
    and [f] is injective, and any [f x] has all descendants of the form [f x'],
    Then two descendents [M] and [N] with [f x ~>> M ~>> N] are of the form
    [M = f y], [N = f z] with [P y z]. That seems pretty dumb.
 *)
Lemma rw_rt_f_induction:
  forall A f x P M N,
    (forall x, P x x) ->
    (injective _ _ f) ->
    (forall x M, (f x ~>> M) -> {x' : A & M = f x'}) ->
    (forall x y, (f x ~> f y) -> P x y) ->
    (forall x y z, P x y -> P y z -> P x z) ->
    (f x ~>> M) ->
    (M ~>> N) ->
    {y : A & M = f y & {z : A & N = f z & P y z}}.
Proof.
 intros A f x P M N X inj_f X0 X1 trans_P H H0.
 induction H0.
 - subst.
   apply X0 in H.
   destruct H.
   exists x0; auto.
   exists x0; auto.
 - assert (f x ~>> n).
   apply Rw_rt_trans with m; auto.
   apply X0 in H.
   apply X0 in H0.
   destruct H.
   destruct H0.
   subst.
   exists x0; auto.
   exists x1; auto.
 - assert (f x ~>> m) by (eapply Rw_rt_trans; eauto).
   assert (f x ~>> n) by (eapply Rw_rt_trans; eauto).
   Ltac clone H :=
     let T := type of H in
     copy T.
   clone H; clone H0; clone H1.
   apply X0 in H.
   apply X0 in H0.
   apply X0 in H1.
   destruct H.
   destruct H0.
   destruct H1.
   subst.
   exists x0; auto.
   exists x2; auto.
   apply IHRewritesTo_rt1 in H2.
   apply IHRewritesTo_rt2 in H3.
   destruct H2 as [y Ha [z Hb Hc]].
   destruct H3 as [y' Ha' [z' Hb' Hc']].
   apply inj_f in Ha.
   apply inj_f in Hb.
   apply inj_f in Ha'.
   apply inj_f in Hb'.
   subst.
   subst.
   eapply trans_P; eauto.
Qed.

Lemma Rw_rt_conserves_Ksize:
  forall K K',
    (plug K TmNull ~>> plug K' TmNull) -> Ksize K >= Ksize K'.
Proof.
 intros.
 apply rw_rt_f_induction
 with (A := Continuation)
        (f := fun k => plug k TmNull)
        (x:=K)
        (P:=fun k k'=>Ksize k >= Ksize k') in H.
 - destruct H.
   destruct s.
   apply unique_plug_null in e.
   apply unique_plug_null in e0.
   subst.
   auto...
 - eauto...
 - unfold injective.
   apply unique_plug_null...
 - intros.
   apply (rw_rt_preserves_plug_TmNull K (plug x TmNull)); auto.
   exists x; auto.
 - apply Rw_conserves_Ksize; auto.
 - intros; omega.
 - auto.
Qed.

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
 apply K_TmNull_rw in H3.
 destruct H3 as [[K_shorter [N [H1a H1b]]] | [K' [H1a H1b]]].
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

Lemma ReducibleK_Null:
  forall K T,
    ReducibleK Reducible K T
    -> SN (plug K TmNull).
Proof.
 unfold ReducibleK.
 intros.
 assert (Krw_rt K K).
  apply Krw_rt_refl; sauto.
 revert H.
 pattern K at 2 3.
 apply Ksize_induction with (K:=K); intros; auto.
  destruct K0; simpl in *.
   apply reducts_SN.
   intros m' H'.
   inversion H'.
  inversion H.
 destruct K'.
  inversion H0.

 destruct (Reducible_inhabited T) as [M M_H].
 pose (X M M_H).
 apply SN_K_M_SN_K_Null with (TmSingle M).
 apply Rw_trans_preserves_SN with (plug K (TmSingle M)); auto.
 apply Krw_rt_Rw_rt; auto.
Qed.

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

Lemma SN_via_Krw_rt :
  forall K K' M,
    Krw_rt K K' -> SN (plug K M) -> SN (plug K' M).
Proof.
 intros.
 assert (plug K M ~>> plug K' M).
  auto using Krw_rt_Rw_rt.
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
  simpl in *.
  inversion H_rw; subst; auto.
   
 simpl in H_rw.

 apply Neutral_Lists in H_rw; [| sauto].
 destruct H_rw as [[M' [Z_def rw]] | [K' [Z_def rw]]].
 (* Case: rw is within TmBind (TmUnion M N) t *)
  subst.
  inversion rw; subst.
    assert (Ksize K0 < Ksize K).
     assert (Ksize (Iterate t K0) <= Ksize K).
      apply Krw_rt_conserves_Ksize with (K := K); auto.
     simpl in *; omega.
    apply H; auto.
     eapply plug_SN_rw_rt with (TmBind M t); auto.
      apply Rw_rt_Bind_left; sauto.
     change (SN (plug (Iterate t K0) M)).
     eauto using SN_via_Krw_rt.
    eapply plug_SN_rw_rt with (TmBind N t); auto.
     apply Rw_rt_Bind_left; sauto.
    change (SN (plug (Iterate t K0) N)).
     eauto using SN_via_Krw_rt.
   inversion H14; subst; seauto.

 (* Case: rw is within t of TmBind (TmUnion M N) t *)
  change (SN (plug (Iterate n' K0) (TmUnion M0 N0))).
  assert (Krw (Iterate t K0) (Iterate n' K0)).
   unfold Krw.
   simpl.
   intros.
   apply Rw_under_K.
   eauto.
  apply H8.
  sauto.

 (* Case: rw is within K *)
 subst.
 change (SN (plug (Iterate t K') (TmUnion M0 N0))).
 apply H8; auto.
 apply iterate_reduce; sauto.
Qed.

Lemma ReducibleK_Union:
  forall T M N,
    Reducible M (TyList T) -> Reducible N (TyList T) -> Reducible (TmUnion M N) (TyList T).
Proof.
 simpl.
 intros T M N.
 intros.
 destruct X, X0.
 split.
  auto.
 intros.
 change (forall K, ReducibleK Reducible K T -> SN (plug K M)) in s.
 change (forall K, ReducibleK Reducible K T -> SN (plug K N)) in s0.
 change (ReducibleK Reducible K T) in X.
 eauto using SN_K_Union.
Qed.

Lemma beta_with_unshift:
  forall N M n n' k,
    n >= n' ->
    unshift n k (unshift n' 1 (subst_env n' (shift 0 1 M :: nil) N)) =
    unshift n' 1
            (subst_env n' (shift 0 1 (unshift n k M) :: nil) (unshift (S n) k N)).
Proof.
 induction N; intros; simpl.
          auto.
         destruct (nth_error_dichot _ (shift 0 1 M :: nil) (x - n')) as [[H1 H2] | [H1 H2]].
          simpl in H1.
          rewrite H2.
          destruct (nth_error_dichot _
                        (shift 0 1 (unshift n k M) :: nil)
                        (unshift_var (S n) k x - n'))
                as [[H3 H4]|[H3 H4]].
          rewrite H4.
           simpl.
           break; break.
              rewrite unshift_unshift_commute; solve [auto | omega].
             rewrite unshift_unshift_commute; solve [auto | omega].
            rewrite unshift_unshift_commute; solve [auto | omega].
           rewrite unshift_unshift_commute; solve [auto | omega].
          destruct H4 as [V H4].
          rewrite H4.
          simpl in *.
          exfalso.
          assert (H0 : unshift_var (S n) k x - n' = 0) by omega.
          unfold unshift_var in H0.
          destruct (le_gt_dec (k + S n) x) in H0; solve [omega].
         destruct H2 as [V H2].
         rewrite H2.
         simpl.
         destruct (nth_error_dichot _
                       (shift 0 1 (unshift n k M) :: nil)
                       (unshift_var (S n) k x - n'))
               as [[H3 H4]|[H3 H4]].
          rewrite H4.
          simpl in *.
          exfalso.
          unfold unshift_var in H3.
          destruct (le_gt_dec (k + S n) x); solve [omega].
         destruct H4 as [W H4].
         rewrite H4.
         simpl in *.
         break; break.
            assert (x < S n) by omega.
            assert (unshift_var (S n) k x = x).
             unfold unshift_var.
             destruct (le_gt_dec (k + S n) x); solve [omega].
            replace (unshift_var (S n) k x) with x in * by auto.
            replace (x - n') with 0 in * by omega.
            simpl in *.
            inversion H2. inversion H4.
            rewrite unshift_unshift_commute.
             rewrite unshift_shift_commute.
              auto.
             omega.
            omega.
           exfalso.
           unfold unshift_var in g.
           destruct (le_gt_dec (k + S n) x); solve [omega].
          exfalso.
          unfold unshift_var in l.
          destruct (le_gt_dec (k + S n) x); solve [omega].
         unfold unshift, unshift_var.
         break; break; break; break; solve [omega | auto].
        rewrite IHN1, IHN2; sauto.
       rewrite IHN; sauto.
      rewrite IHN.
       rewrite unshift_shift_commute; solve [omega | auto].
      solve [omega].
     rewrite IHN1, IHN2; sauto.
    trivial.
   rewrite IHN; sauto.
  rewrite IHN1, IHN2; sauto.
 rewrite IHN1, IHN2.
   rewrite unshift_shift_commute; solve [omega | auto].
  solve [omega].
 sauto.
Qed.

Lemma unshift_preserves_rw:
  forall M M' n k,
    (M ~> M') ->
    unshift n k M ~>
    unshift n k M'.
Proof.
 induction M; intros; inversion H; subst; simpl; eauto.

 apply Rw_beta.
 apply beta_with_unshift.
 omega.
Qed.

Lemma unshift_substitution_preserves_rw:
  forall M M' L,
    (M ~> M') ->
    unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) M) ~>
    unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) M').
Proof.
 intros.
 apply unshift_preserves_rw.
 apply subst_env_compat_rw.
 auto.
Qed.

Lemma SN_beta_withdraw:
  forall L N,
    SN (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)) ->
    SN N.
Proof.
 intros.
 apply SN_embedding with (f := fun x => unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) x))
                           (Q := unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)).
 intros.
   apply unshift_substitution_preserves_rw; sauto.
  sauto.
 sauto.
Qed.

Lemma shift_preserves_rw:
  forall L L' n,
    (L ~> L') ->
    shift n 1 L ~> shift n 1 L'.
Proof.
 induction L; intros; inversion H; subst; simpl; eauto.
 apply Rw_beta.
 rewrite <- shift_shift_commute by omega.
 replace (shift (S n) 1 (shift 0 1 L2) :: nil)
    with (map (shift (S n) 1) ((shift 0 1 L2) :: nil)) by auto.
 rewrite <- shift_subst_commute_hi by (simpl; omega).
 rewrite <- Shift.shift_unshift_commute; try omega.
  trivial.
 intro.
 pose (subst_Freevars N (shift 0 1 L2 :: nil) 0).
 apply set_union_elim with (a:=0) in i.
 simpl in i.
  destruct i.
   pose (shift_freevars L2 0 0).
   intuition.
 apply set_filter_elim in H1.
 intuition.
 auto.
Qed.

Lemma unshift_preserves_rw_rt
     : forall (M M' : Term) (n k : nat),
       (M ~>> M') -> unshift n k M ~>> unshift n k M'.
Proof.
 intros.
 induction H; subst; eauto.
 auto using Rw_rt_step, unshift_preserves_rw.
Qed.

Lemma unshift_substitution_preserves_rw_rt:
  forall M M' L : Term,
  (M ~>> M') ->
  unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) M) ~>>
  unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) M').
Proof.
  intros.
  induction H.
  * constructor 1.
    subst; auto.
  * constructor 2.
    apply unshift_substitution_preserves_rw; auto.
  * econstructor 3; eauto.
Qed.

Lemma Rw_rt_shift:
  forall L L', (L ~>> L') -> shift 0 1 L ~>> shift 0 1 L'.
Proof.
 intros.
 induction H; subst; eauto.
 auto using Rw_rt_step, shift_preserves_rw.
Qed.

Lemma subst_env_compat_rw_rt_A
: forall M L L' : Term,
    (L ~>> L') ->
    forall n : nat, subst_env n (L :: nil) M ~>> subst_env n (L' :: nil) M.
Proof.
 induction M; subst; simpl; eauto; intros.
        break; auto.
        destruct (x - n).
         destruct (le_gt_dec (x - n) 0); simpl; auto.
        unfold nth_error; destruct n0; simpl; auto.
       apply Rw_rt_trans with (TmPair (subst_env n (L'::nil) M1) (subst_env n (L::nil) M2)).
        apply Rw_rt_Pair_left; auto.
       apply Rw_rt_Pair_right; auto.
      apply Rw_rt_Proj; auto.
     apply Rw_rt_Abs; auto.
     apply IHM.
     apply Rw_rt_shift; auto.
    apply Rw_rt_trans with (TmApp (subst_env n (L'::nil) M1) (subst_env n (L::nil) M2)).
     apply Rw_rt_App_left; auto.
    apply Rw_rt_App_right; auto.
   apply Rw_rt_Single; auto.
  apply Rw_rt_trans with (TmUnion (subst_env n (L'::nil) M1) (subst_env n (L::nil) M2)).
   apply Rw_rt_Union_left; auto.
  apply Rw_rt_Union_right; auto.
 apply Rw_rt_trans with (TmBind (subst_env n (L'::nil) M1) (subst_env (S n) (shift 0 1 L::nil) M2)).
  apply Rw_rt_Bind_left; auto.
 apply Rw_rt_Bind_right; auto.
 apply IHM2.
 apply Rw_rt_shift; auto.
Qed.

Lemma subst_env_compat_rw_rt_B
: forall L M M' : Term,
    (M ~>> M') ->
    forall n : nat, subst_env n (L :: nil) M ~>> subst_env n (L :: nil) M'.
Proof.
 intros.
 induction H; subst; eauto using subst_env_compat_rw.
Qed.

Lemma subst_env_compat_rw_2_rt
: forall L L' M M' : Term,
    (L ~>> L') ->
    (M ~>> M') ->
    forall n : nat, subst_env n (L :: nil) M ~>> subst_env n (L' :: nil) M'.
Proof.
 intros.
  apply Rw_rt_trans with (subst_env n (L :: nil) M').
  apply subst_env_compat_rw_rt_B; auto.
  apply subst_env_compat_rw_rt_A; auto.
Qed.

Lemma unshift_substitution_doubly_preserves_rw_rt:
  forall M M' L L' : Term,
  (L ~>> L') ->
  (M ~>> M') ->
  unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) M) ~>>
  unshift 0 1 (subst_env 0 (shift 0 1 L' :: nil) M').
Proof.
 intros.
 apply unshift_preserves_rw_rt. (* Should be rw_compat_unshift *)
 apply subst_env_compat_rw_2_rt; auto.
 apply Rw_rt_shift; auto.
Qed.

Lemma plug_rw_rt:
  forall K K' M M', Krw_rt K K' -> (M ~>> M') -> (plug K M ~>> plug K' M').
Proof.
  intros.
 assert (plug K M ~>> plug K' M).
 apply Krw_rt_Rw_rt; auto.
 assert (plug K' M ~>> plug K' M').
  apply Rw_rt_under_K; auto.
 eauto.
Qed.

Lemma beta_reduct_under_K_rw_rt:
  forall K K0, Krw_rt K K0 ->
  forall N N0, (N ~>> N0) ->
  forall L L0, (L ~>> L0) ->
    plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)) ~>>
    plug K0 (unshift 0 1 (subst_env 0 (shift 0 1 L0 :: nil) N0)).
Proof.
 intros.
 assert (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N) ~>>
         unshift 0 1 (subst_env 0 (shift 0 1 L0 :: nil) N0)).
 apply unshift_substitution_doubly_preserves_rw_rt; auto.
 apply plug_rw_rt; auto.
Qed.

Lemma SN_beta_withdraw_under_k:
  forall K L N,
    SN L ->
    SN (plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))) ->
    SN (plug K (TmAbs N @ L)).
Proof.
 intros.
 assert (SN N).
  apply SN_push_under_k in H0.
  eauto using SN_beta_withdraw.
 assert (Krw_norm K).
  eauto using SN_context_Krw_norm.
 apply triple_induction_scoped with (K0:=K) (M0:=N) (N0:=L); auto.
 intros.
 apply reducts_SN.
 intros.
 apply Neutral_Lists in H9; auto.
 destruct H9 as [[M' [H7a H7b]] | [K' [H7a H7b]]]; subst.
 - inversion H7b; subst.
   * eauto using beta_reduct_under_K_rw_rt, Rw_trans_preserves_SN.
   * inversion H12; subst.
     apply H7; sauto.
   * apply H8; sauto.
 - auto using H6.
Qed.

Lemma bind_sn_withdraw:
  forall K L N,
    SN L ->
    SN (plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))) ->
    SN (plug K (TmBind (TmSingle L) N)).
Proof.
 intros.
 assert (SN N).
  apply SN_push_under_k in H0.
  eauto using SN_beta_withdraw.
 apply triple_induction_scoped with (K0:=K) (M0:=N) (N0:=L);
    eauto using SN_context_Krw_norm.  (* XXX rename to triple_induction_SN *)
 intros K0 N0 L0 ? ? ? IHK0 IHM0 IHL0.
 apply reducts_SN.
 intros Z redn.
 apply Neutral_Lists in redn; try auto.
 destruct redn as [[M' [redn_a redn_b]] | [K' [redn_a redn_b]]].
  inversion redn_b; subst.
    apply SN_beta_withdraw_under_k; auto.
     apply Rw_trans_preserves_SN with L; auto.
    eauto using beta_reduct_under_K_rw_rt, Rw_trans_preserves_SN.
   inversion H8.
  subst.
   apply IHL0; sauto.
  seauto.
 subst.
 eauto using IHK0.
Qed.

Lemma Bind_Reducible_core:
  forall (M : Term) (S : Ty) (N : Term) (T : Ty),
    Typing (S :: nil) N (TyList T) ->
    Reducible M (TyList S) ->
    SN M ->
    SN N ->
    forall K : Continuation,
      ReducibleK Reducible K T ->
      Krw_norm K ->
      (forall L : Term,
         Reducible L S ->
         SN (plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)))) ->
        SN (plug K (TmBind M N)).
Proof.
 intros.
 enough (SN (plug (Iterate N K) M)) by auto.
 simpl in X.
 apply X.
 simpl.
 intros.
 apply bind_sn_withdraw.
  eauto using Reducible_SN.
 auto.
Qed.

Lemma Bind_Reducible :
  forall M S N T,
    Typing (S :: nil) N (TyList T)
    -> Reducible M (TyList S)
    -> (forall L, Reducible L S
                  -> Reducible (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))
                               (TyList T))
    -> Reducible (TmBind M N) (TyList T).
Proof.
 intros.
 split.
  intuition; eauto.
 intros.
 simpl in X0.
 assert (forall L, Reducible L S ->
                   SN (plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)))).
 intros.
  apply X0; auto.
 assert (SN M).
 eapply Reducible_SN; eauto.
 assert (Krw_norm K).
 apply ReducibleK_Krw_norm with T.
  auto.
 assert (SN N).
  destruct (Reducible_inhabited S) as [L L_red].
  specialize (X0 L L_red).
  destruct X0 as [t s].
  specialize (s Empty).
  lapply s.
   simpl.
   apply SN_beta_withdraw.
  apply ReducibleK_Empty.
 clear X0.
 eapply Bind_Reducible_core; eauto.
Qed.

Lemma env_typing_cons_inv:
  forall V Vs T env,
    env_typing (V :: Vs) (T :: env) -> Typing nil V T * env_typing Vs env.
Proof.
 intros.
 unfold env_typing in H.
 destruct H.
 unfold foreach2_ty in f.
 (* XXX: Defining env_tpying in terms of foreach2_ty was a terrible
 idea. Must be a nice general inductive structure that gives the same
 thing and is easier to use. *)
 destruct f.
 auto.
Qed.

Lemma shift_closed_noop_map:
  forall n k vs ts,
    env_typing vs ts
    -> vs = map (shift n k) vs.
Proof.
 induction vs as [|a vs]; simpl; intros.
  auto.
 destruct ts; simpl in *; try (destruct H; discriminate).
 apply env_typing_cons_inv in H.
 destruct H.
 f_equal.
 erewrite shift_closed_noop; eauto.
 eauto.
Qed.

Lemma closing_subst_closes:
  forall vs ts m t,
    env_typing vs ts ->
    Typing ts m t ->
    Typing nil (subst_env 0 vs m) t.
Proof.
 intros.
 apply subst_env_preserves_typing with (env' := ts); simpl; auto.
Qed.

(** Every well-typed term, with a [reducible] environment that makes it a closed
    term, is [reducible] at its given type. *)
Theorem reducibility:
  forall M T tyEnv Vs,
    Typing tyEnv M T ->
    env_typing Vs tyEnv ->
    env_Reducible Vs tyEnv ->
    Reducible (subst_env 0 Vs M) T.
Proof.
 induction M; simpl; intros T tyEnv Vs tp Vs_tp Vs_red;
   inversion tp; inversion Vs_tp.
 (* Case TmConst *)
           simpl.
           intuition.

 (* Case TmVar *)
          replace (x - 0) with x by omega.
          case_eq (nth_error Vs x); [intros V V_H | intro H_bogus].
               eapply Reducible_env_value; eauto.
          absurd (length Vs <= x).
           cut (length tyEnv > x); [omega|]. (* todo: sufficient ... by omega. *)
           seauto.
          apply <- nth_error_overflow; sauto.

 (* Case TmPair *)
         assert (Reducible (subst_env 0 Vs M2) t) by eauto.
         assert (Reducible (subst_env 0 Vs M1) s) by eauto.
         simpl.
         assert (Reducible (TmPair (subst_env 0 Vs M1) (subst_env 0 Vs M2)) (TyPair s t)).
          apply pair_reducible; sauto.
         simpl in X1.
         trivial.

 (* Case TmpRoj false *)
        subst.
        rename M into M, T into S, t into T.
        assert (x0 : Reducible (subst_env 0 Vs M) (TyPair S T)).
         seauto.
        simpl in x0.
        tauto.

 (* Case TmProj true *)
       subst.
       rename M into M, s into S.
       assert (X0 : Reducible (subst_env 0 Vs M) (TyPair S T)).
        seauto.
       simpl in X0.
       tauto.

 (* Case TmAbs *)
      replace (map (shift 0 1) Vs) with Vs by (symmetry; eauto).
      replace (TmAbs (subst_env 1 Vs M)) with (subst_env 0 Vs (TmAbs M)).
      (* proof of reducibility of the lambda. *)
       apply lambda_reducibility with tyEnv; auto.
       intros V V_red.
       eapply IHM; eauto.
       simpl.
       intuition.

      (* Obligation: TmAbs (subst_env 1 Vs m)) = (subst_env 0 Vs (TmAbs m)). *)
      simpl.
      erewrite env_typing_shift_noop; eauto.

 (* Case TmApp *)
     subst.
     assert (Reducible (subst_env 0 Vs M1) (TyArr a T)) by eauto.
     assert (Reducible (subst_env 0 Vs M2) a) by eauto.
     firstorder.

 (* Case TmNull *)
    simpl.
    split.
     auto.
    intro K.
    apply ReducibleK_Null.

 (* Case TmSingle *)
   simpl.
   split.
    eauto.
   intros.
   eauto.

 (* Case TmUnion *)
  subst.
  assert (Reducible (subst_env 0 Vs M2) (TyList t)) by eauto.
  assert (Reducible (subst_env 0 Vs M1) (TyList t)) by eauto.
  apply ReducibleK_Union; sauto.

 (* Case TmBind *)
 subst.
 apply Bind_Reducible with s.
   eapply subst_env_preserves_typing with (env' := tyEnv); auto.
   rewrite env_typing_shift_noop with (env := tyEnv); auto.
  eapply IHM1; eauto.

 clear H1 IHM1 M1 tp.

 intros.
 pose (Reducible_welltyped_closed _ _ X).
 assert (Typing nil (subst_env 0 (L :: Vs) M2) (TyList t)).
  eapply closing_subst_closes; seauto.

 replace (shift 0 1 L) with L.
  replace (map (shift 0 1) Vs) with Vs.
   rewrite subst_env_concat with (env := s :: tyEnv).
    unfold app.
    erewrite unshift_closed_noop; eauto.
    eapply IHM2; eauto.
    simpl.
    sauto.
   apply env_typing_cons; sauto.
  eapply shift_closed_noop_map; seauto.
 erewrite shift_closed_noop; eauto.
Qed.

(** Every well-typed term is strongly normalizing. *)
Lemma normalization :
  forall M T,
    Typing nil M T ->
    SN M.
Proof.
 intros M T tp.

 assert (Reducible M T).
  replace M with (subst_env 0 nil M) by seauto.
  eapply reducibility; eauto; solve [firstorder].
 (* With reducibility comes strong normalization. *)
 seauto.
Qed.

(* Print normalization. *)

(* Print reducibility. (* Huzzah! *) *)

Print Assumptions normalization.

(* Until I did all this, I didn't realize that substitution was a big
ask; a complex function with an algorithm in its own right. *)