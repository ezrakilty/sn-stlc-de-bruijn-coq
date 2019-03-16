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

(** A term [M] is [Neutral] if, when it reduces in context, [C[M] ~> Z], the
    reduction either in [C] or in [M]: Either
      [C[M] ~> Z  ==  C[M] ~> C[M']]  or
      [C[M] ~> Z  ==  C[M] ~> C'[M]].
    In other words, [M] cannot react with [C] immediately.

    But we define it here by the cases that we know have that property.
 *)
Inductive Neutral : Term -> Type :=
  | Neutral_App : forall L M, Neutral (TmApp L M)
  | Neutral_Proj : forall b M, Neutral (TmProj b M).

Hint Resolve Neutral_App.
Hint Resolve Neutral_Proj.

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

Hint Resolve subst_env_compat_Rw_trans.


(******************************** REDUCIBILITY ********************************)

Set Universe Polymorphism.

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
  end)%type.

Lemma Reducible_welltyped_closed :
  forall tm ty, Reducible tm ty -> Typing nil tm ty.
Proof.
 destruct ty; firstorder eauto.
Qed.

Hint Immediate Reducible_welltyped_closed.

(** The rewrites relation preserves reducibility. *)
Lemma Rw_preserves_Reducible :
 forall T M, Reducible M T -> forall M', (M ~> M') -> Reducible M' T.
Proof.
 induction T; simpl.
   firstorder using Rw_preserves_types.
   inversion b; auto.
  firstorder using Rw_preserves_types.
 firstorder using Rw_preserves_types.
Qed.

(** The reflexive-transitive rewrites relation preserves reducibility. *)
Lemma Rw_rt_preserves_Reducible :
 forall T M, Reducible M T -> forall M', (M ~>> M') -> Reducible M' T.
Proof.
 intros T M R M' red.
 induction red; subst; auto.
 eapply Rw_preserves_Reducible; eauto.
Qed.

Hint Resolve Rw_rt_preserves_Reducible.

Ltac splitN n :=
  match n with
    | 2 => split
    | 3 => split; [splitN 2 | ]
  end.

Lemma pair_proj_reducible:
  forall T1 T2 M N,
    Reducible M T1 -> Reducible N T2 ->
    (forall b : bool, forall tm : Term,
          Reducible tm (if b then T2 else T1) -> SN tm) ->
    (forall b : bool,
        forall M0 : Term,
          Neutral M0 ->
          Typing nil M0 (if b then T2 else T1) ->
          (forall M' : Term, (M0 ~> M') -> Reducible M' (if b then T2 else T1)) ->
          Reducible M0 (if b then T2 else T1)) ->
    forall (b : bool),
      Reducible (TmProj b (〈M, N 〉)) (if b then T2 else T1).
Proof.
 intros T1 T2 M N M_red N_red Reducible_SN_Tn Neutral_Reducible_Tn b.
 (* double_induction_SN M N. (* FIXME: doesn't work! *) *)
 cut (M ~>> M); [|auto]; cut (N ~>> N); [|sauto]; pattern N at 2 3, M at 2 3;
 refine (SN_double_induction _ _ N M _ _).
   intros N' M' IHM' IHN' N_rw_N' M_rw_M'.

   (* Because (TmProj _ _) is Neutral, it's sufficient to show that all its
      reducts are reducible. *)
   assert (M_ty : Typing nil M T1) by auto.
   assert (N_ty : Typing nil N T2) by auto.
   apply Neutral_Reducible_Tn; [seauto |  | ].
    destruct b; seauto.

   intros Z H.
   inversion H.
   (* Case: <M', N'> itself reduces *)
     subst.
     inversion H3.
     (* Case: reduction in lhs *)
      subst m1 n m2.
      apply IHN'; seauto.
     (* Case: reduction in rhs *)
     subst m n1 m2.
     apply IHM'; seauto.
   (* Case: The reduct is at the head; we project. *)
    subst m n Z.
    seauto.
   (* Case: The reduct is at the head; we project. *)
   subst m n Z.
   seauto.
  apply Reducible_SN_Tn with (b:=true); sauto.
 apply Reducible_SN_Tn with (b:=false); sauto.
Qed.

(** The [Reducible] predicate has these important properties which
    must be proved in a mutually-inductive way. They are:
      (1) Every type has a [Reducible] term,
      (2) Every [Reducible] term is strongly normalizing.
      (3) If [M] is a neutral term at type [T], and all of its reducts
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
     simpl; eauto.
   (* Reducible -> SN *)
    simpl.
    tauto.
   (* Neutral terms withdraw *)
   unfold Reducible in *.
   intuition (apply reducts_SN).
   firstorder.

  (* Case TyPair *)
  splitN 3.
  (* Case: exists a reducible term *)
    destruct IHT1 as [[[M M_red] Reducible_SN_T1] Neutral_Reducible_T1].
    destruct IHT2 as [[[N N_red] Reducible_SN_T2] Neutral_Reducible_T2].
    exists (TmPair M N).
    simpl.
    split.
    (* Case: that <M, N> : TyPair T1 T2 *)
      auto.

  (* Case: When continuation frames (left & right projections) are applied, a
       reducible term is formed. *)
    split.
     set (b := false).
     replace T1 with (if b then T2 else T1) by auto.
     apply pair_proj_reducible; auto.
      intros; destruct b0; auto.
     intros; destruct b0; auto.
    set (b := true).
    replace T2 with (if b then T2 else T1) by auto.
    apply pair_proj_reducible; auto.
     intros; destruct b0; auto.
    intros; destruct b0; auto.

  (* Case: Reducible pair-type terms are strongly normalizing *)
   simpl.
   intuition.
   assert (SN (TmProj false tm)) by auto.
   eapply SN_context_Proj; eauto.

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
   inversion red as [ | ? Z ? redn_Z | | | | | | | ] ; subst.
   (* beta reduction *)
     (* BUG: should be able to put these all as args to congruence. *)
     pose subst_dummyvar; pose subst_nil; pose unshift_shift.
     replace (unshift 0 1 (subst_env 0 (shift 0 1 M' :: nil) (shift 0 1 N')))
       with N' by congruence.
     apply Rw_rt_preserves_Reducible with N; auto.
   (* Reduction of the function position. *)
    inversion redn_Z.
    subst Z.
    destruct (shift_Rw_inversion _ _ _ H2) as [N'' [N''_def N'0_rew_N'']].
    subst n'.
    apply IHN; eauto.
   (* Reduction of the argument position. *)
   apply IHM; eauto.

 (* Reducibile S->T terms are SN. *)
  intros M M_red.
  destruct M_red as [M_tp M_applied_Red].
  destruct IHT1 as [[[X Red_X] _] _].
  assert (Reducible (M@X) T2).
   apply M_applied_Red; eauto.
  assert (SN (M@X)).
   firstorder (* Finds the needed lemma in IHT2 *).
  apply SN_context_App_left with X; auto.

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
   eauto (* typing *).
  intros Z Z_red.
  (* Take cases on the reduction M@M0 ~> Z *)
  inversion Z_red.
  (* Beta-reduction case: bogus because M is neutral. *)
    subst.
    inversion Neutral_M.
  (* Left of (@) case: easy from M_reducts_Reducible. *)
   subst m1 n.
   assert (Reducible_m2: Reducible m2 (TyArr T1 T2)).
    apply M_reducts_Reducible; auto.
   simpl in Reducible_m2.
   apply Reducible_m2; eauto.
  (* Right of (@) case: by inductive hypothesis. *)
  rename n2 into L''.
  apply IHL'; eauto.
 assert (Reducible (M@L) T2).
  apply X; auto.
 eauto.
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

(** We say that an environment is reducible when it is a list of closed terms, together
with types, and each one is reducible at the corresponding type. *)
(* Grumble: I don't know why foreach2_ty doesn't work here. But it
gives a universe inconsistency when applied to Reducible. *)
Fixpoint env_Reducible Vs Ts : Type :=
  match Vs, Ts with
    | nil, nil => True%type
    | V::Vs, T::Ts => (Reducible V T * env_Reducible Vs Ts)%type
    | _, _ => False
  end.

(** Every term [λN] is [Reducible] in a closing, [Reducible]
    environment, provided that every [Reducible] argument [V] substituted
    into [N] gives a [Reducible] term. *)
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
 apply Neutral_Reducible_withdraw; [solve [auto] | solve [eauto] |].
 intros M' redn.

 inversion redn as [N0 M0 V M'_eq| ? ? ? L_redn | | | | | | | ].

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
  forall (M : Term)
  (N : Term)
  (S : Ty)
  (T : Ty)
  (b : bool),
  Reducible M S ->
  Reducible N T ->
  SN M ->
  SN N ->
     Reducible (TmProj b (〈M, N 〉)) (if b then T else S).
Proof.
 intros.
 double_induction_SN N M.
 intros x y X1 X2 H1 H2.

 apply Neutral_Reducible_withdraw; auto.
 (* Discharge the typing obligation. *)
  assert (Typing nil y T) by (eapply Rw_preserves_types; eauto).
  assert (Typing nil x S) by (eapply Rw_preserves_types; eauto).
  destruct b; eauto.
 (* All reducts are reducible. *)
 intros M' H3.
 (* Take cases on the reduction. *)
 inversion H3 as [ | | | | | | m n1 n2 H7 | m n | m n]; subst.
 (* Case: reduction under the operation. *)
   inversion H7; subst.
    apply X1; seauto.
   apply X2; seauto.
 (* Case: beta-reduction on the left *)
  seauto.
 (* Case: beta-reduction on the right *)
 seauto.
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
  apply (TmProj_reducible M N S T false X X0 H1 H2).
 (* Case TmProj true *)
 apply (TmProj_reducible M N S T true X X0 H1 H2).
Qed.

Lemma env_Reducible_member:
  forall x V Vs T Ts,
    value V = nth_error Vs x ->
    value T = nth_error Ts x -> env_Reducible Vs Ts -> Reducible V T.
Proof.
 induction x; intros.
  destruct Vs.
   simpl in H.
   discriminate.
  destruct Ts.
   simpl in H0.
   discriminate.
  simpl in *.
  inversion H.
  inversion H0.
  intuition.
 destruct Vs.
 simpl in H.
 discriminate.
 destruct Ts.
 simpl in H.
 discriminate.
 simpl in H, H0, X.
 apply IHx with Vs Ts; intuition.
Qed.

(** Every well-typed term, with a [Reducible] environment that makes it a closed
    term, is [Reducible] at its given type. *)
Theorem reducibility:
  forall m T tyEnv Vs,
    Typing tyEnv m T ->
    env_typing Vs tyEnv ->
    env_Reducible Vs tyEnv ->
    Reducible (subst_env 0 Vs m) T.
Proof.
 induction m; simpl; intros T tyEnv Vs tp Vs_tp Vs_red;
   inversion tp; inversion Vs_tp.
 (* Case TmConst *)
       simpl.
       intuition.

 (* Case TmVar *)
      replace (x - 0) with x by omega.
      case_eq (nth_error Vs x); [intros V V_H | intro H_bogus].
       eapply env_Reducible_member; eauto.
      absurd (length Vs <= x).
       cut (length tyEnv > x); [omega|]. (* TODO: sufficient ... by omega. *)
       seauto.
      apply <- nth_error_overflow; sauto.

 (* Case TmPair *)
     assert (Reducible (subst_env 0 Vs m2) t) by eauto.
     assert (Reducible (subst_env 0 Vs m1) s) by eauto.
     simpl.
     assert (Reducible (TmPair (subst_env 0 Vs m1) (subst_env 0 Vs m2)) (TyPair s t)).
      apply pair_reducible; sauto.
     simpl in X1.
     trivial.

 (* Case TmProj false *)
    subst.
    rename m into M, T into S, t into T.
    assert (X0 : Reducible (subst_env 0 Vs M) (TyPair S T)).
     seauto.
    simpl in X0.
    tauto.

 (* Case TmProj true *)
   subst.
   rename m into M, s into S.
   assert (X0 : Reducible (subst_env 0 Vs M) (TyPair S T)).
    seauto.
   simpl in X0.
   tauto.

 (* Case TmAbs *)
  replace (map (shift 0 1) Vs) with Vs by (symmetry; eauto).
  replace (TmAbs (subst_env 1 Vs m)) with (subst_env 0 Vs (TmAbs m)).
  (* Proof of reducibility of the lambda. *)
   apply lambda_reducibility with tyEnv; auto.
   intros V V_red.
   eapply IHm; eauto.
   constructor; auto.

  (* Obligation: TmAbs (subst_env 1 Vs m)) = (subst_env 0 Vs (TmAbs m)). *)
  simpl.
  erewrite env_typing_shift_noop; eauto.

 (* Case TmApp *)
 subst.
 assert (Reducible (subst_env 0 Vs m1) (TyArr a T)) by eauto.
 assert (Reducible (subst_env 0 Vs m2) a) by eauto.
 firstorder.
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

Print normalization.

Print reducibility. (* Huzzah! *)

Print Assumptions normalization.
