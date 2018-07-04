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
    reduction either in C or in M:
      C[M] ~> Z  ==  C[M] ~> C[M']  or
      C[M] ~> Z  ==  C[M] ~> C'[M].
    In other words, [M] cannot react with [C] immediately.

    But we define it here by the cases that we know have that property.
 *)
Inductive Neutral : Term -> Type :=
  | Neutral_App : forall L M, Neutral (TmApp L M)
  | Neutral_Proj : forall b M, Neutral (TmProj b M)
  | Neutral_TmBind : forall M N, Neutral (TmBind M N).

Hint Constructors Neutral.

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

Inductive Continuation :=
  Empty : Continuation
| Iterate : Term -> Continuation -> Continuation.

Fixpoint plug (K : Continuation) (M : Term) : Term :=
  match K with
      Empty => M
    | Iterate N K' => plug K' (TmBind M N)
  end.

(* Inductive Krw_explicit : Continuation -> Continuation -> Type := *)
(* | A : forall N N' K, (N ~> N') -> Krw_explicit (Iterate N K) (Iterate N' K) *)
(* | B : forall N K K', (Krw_explicit K K') -> Krw_explicit (Iterate N K) (Iterate N K') *)
(* . *)

Set Universe Polymorphism.

(* Set Printing Universes. *)

Definition SNK (K : Continuation) :=
  forall M,
    SN M ->
    SN (plug K (TmSingle M)).

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

Print Universes.

Fixpoint ahem Vs Ts : Type :=
  match Vs, Ts with
    | nil, nil => True%type
    | V::Vs, T::Ts => (Reducible V T * ahem Vs Ts)%type
    | _, _ => False
  end.

Check Reducible.
Check foreach2_ty.

Definition ReducibleK (Reducible:Term->Ty -> Type) (K : Continuation) (T : Ty) :=
    forall M,
      Reducible M T ->
      SN (plug K (TmSingle M)).

Lemma Reducible_welltyped_closed :
  forall tm ty, Reducible tm ty -> Typing nil tm ty.
Proof.
 destruct ty; firstorder eauto.
Qed.

Hint Immediate Reducible_welltyped_closed.

Lemma plug_SN_rw:
  forall K M M',
    (M ~> M') -> SN (plug K M) -> SN (plug K M').
Proof.
 induction K.
  simpl.
  intuition.
  inversion H0.
  auto.
 simpl.
 intros.
 apply IHK with (TmBind M t); sauto.
Qed.

(* Lemma KM_rw_inversion: *)
(*   forall K M km', *)
(*     (plug K M ~> km') -> {M' : Term & km' = plug K M'}. *)
(* Proof. *)
 
(* Qed. *)

Lemma rw_plug_lift :
  forall K M M',
    (M ~> M') -> (plug K M ~> plug K M').
Proof.
 induction K.
  auto.
  simpl.
 intros.
 apply IHK.
 auto.
Qed.

(** The rewrites relation preserves reducibility. *)
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
 assert (H2 : SN (plug K M)).
  apply X; auto.
 inversion H2 as [H3].
 apply (H3 (plug K M')).
 apply rw_plug_lift.
 auto.
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

Lemma mamma_mia:
  forall
  (T1 : Ty)
  (T2 : Ty)
  (M : Term)
  (M_red : Reducible M T1)
  (N : Term)
  (N_red : Reducible N T2)
  (Reducible_SN_Tn : forall b:bool, forall tm : Term,
                       Reducible tm (if b then T2 else T1) -> SN tm)
  (Neutral_Reducible_Tn : forall b: bool,
                          forall M0 : Term,
                          Neutral M0 ->
                          Typing nil M0 (if b then T2 else T1) ->
                          (forall M' : Term, (M0 ~> M') -> Reducible M' (if b then T2 else T1)) ->
                          Reducible M0 (if b then T2 else T1))
   (b:bool),
   Reducible (TmProj b (〈M, N 〉)) (if b then T2 else T1).
Proof.
 intros.
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

Definition HoleType K T :=
  forall M env, Typing env M T -> {S : Ty & Typing nil (plug K M) S}.

Definition Krw K K' := (forall M, plug K M ~> plug K' M).

(** Reflexive, transitive closure of Krw *)
Inductive Krw_rt : Continuation -> Continuation -> Type :=
| Krw_rt_refl : forall m n, m = n -> Krw_rt m n
| Krw_rt_step : forall m n, Krw m n -> Krw_rt m n
| Krw_rt_trans : forall l m n, Krw_rt l m -> Krw_rt m n
                -> Krw_rt l n.

(* Inductive SNK K := *)
(*   Reducts_SNK : (forall K', Krw K K' -> SNK K') -> SNK K. *)

Lemma TmBind_Neutral_reducts:
  forall M N Z,
    Neutral M ->
    (TmBind M N ~> Z) ->
    {M' : Term & ((Z = TmBind M' N) * (M ~> M'))%type}
  + {N' : Term & ((Z = TmBind M N') * (N ~> N'))%type}.
Proof.
 intros.
 inversion H0; subst; solve [inversion H | firstorder].
Qed.

(* Lemma Krw_Iterate: *)
(*   forall K K' t, *)
(*     Krw K K'-> Krw (Iterate t K) (Iterate t K'). *)
(* Proof. *)
(*  induction K; simpl. *)
(*   unfold Krw. *)
(*   intros. *)
(*   simpl in *. *)
(*   assert (K' = Empty). *)
  
(*   assert (TmBind M t ~> TmBind (plug K' M) t). *)
(*    apply Rw_Bind_subject. *)
(*    auto. *)

(* Qed. *)

Lemma iterate_reduce K K' : Krw K K' -> forall F, Krw (Iterate F K) (Iterate F K').
Proof.
unfold Krw.
intros.
simpl.
apply H.
Qed.

Lemma Rw_under_K:
  forall K M N,
    (M ~> N) -> (plug K M ~> plug K N).
Proof.
 induction K; simpl; intros.
  auto.
 apply IHK.
 auto.
Qed.

Lemma rw_in_K_body:
  forall K M M',
   (M ~> M') -> (Krw (Iterate M K) (Iterate M' K)).
Proof.
 intros.
 unfold Krw.
 intros.
 simpl.
 apply Rw_under_K.
 eauto.
Qed.

Lemma Neutral_Lists:
  forall K M,
    Neutral M ->
    forall Z, (plug K M ~> Z) ->
    {M' : Term & ((Z = plug K M') * (M ~> M'))%type} +
    {K' : Continuation & ((Z = plug K' M) * (Krw K K'))%type}.
Proof.
 induction K.
 (* Case : empty K *)
  left.
  simpl.
  firstorder.
 (* Case : K starts with an iterator. *)
 intros.
 apply IHK in H0; try apply Neutral_TmBind.
 destruct H0.
 (* Case : redn of K@M' is inside M'. *)
  destruct s as [x [H0 H1]].
  apply TmBind_Neutral_reducts in H1; auto.
  destruct H1 as [[M' [H1a H1b]] | [N' [H1a H1b]]].
   left.
   exists M'.
   subst x.
   sauto.
  right.
  exists (Iterate N' K).
  subst.
  simpl.
  split.
   auto.
  apply rw_in_K_body; sauto.

 (* Case : redn of K@M' in inside K. *)
 right.
 destruct s as [x [H0 H1]].
 exists (Iterate t x).
 simpl.
 intuition.
 apply iterate_reduce; sauto.
Qed.

Lemma Krw_SNK K K' : SNK K -> Krw K K' -> SNK K'.
Proof.
 unfold SNK, Krw in *.
 intros.
 specialize (H M H1).
 inversion H.
 auto.
Qed.

Lemma Krw_rt_SNK K K' : SNK K -> Krw_rt K K' -> SNK K'.
Proof.
 intros.
 induction H0.
   subst; auto.
  eauto using Krw_SNK.
 auto.
Qed.

Lemma plug_SN_rw_rt:
  forall (K : Continuation) (M M' : Term),
  (M ~>> M') -> SN (plug K M) -> SN (plug K M').
Proof.
 intros.
 induction H; subst; eauto using plug_SN_rw.
Qed.

Lemma TmSingle_rw_rt M M0:
  (M ~>> M0) -> (TmSingle M ~>> TmSingle M0).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma awesome_lemma K M:
  forall Z,
  (plug K (TmSingle M) ~> Z) ->
  {M' : Term
          & ((Z = plug K (TmSingle M')) * (M ~> M'))%type} +
  {K' : Continuation
          & ((Z = plug K' (TmSingle M)) * Krw K K')%type} +
  {K' : Continuation & {N : Term
                        & ((K = Iterate N K') * (Z = plug K' (TmApp (TmAbs N) M)))%type}}.
Proof.
Admitted (* unused *).

Lemma Empty_unrewritable: forall K, (Krw Empty K) -> False.
Proof.
 unfold Krw.
 intros.
 specialize (H TmConst).
 destruct K; simpl in H; inversion H.
Qed.

Inductive Ktyping : Continuation -> Ty -> Type :=
  Ktype : forall K T env S M, Typing env M T -> Typing nil (plug K M) S -> Ktyping K T.

Lemma Krw_characterization:
  forall K T K' N,
    Ktyping K T ->
    Krw (Iterate N K) K' ->
    {K1 : Continuation & ((K' = Iterate N K1) * (Krw K K1))%type} +
    {N' : Term & ((K' = Iterate N' K) * (N ~> N'))%type}.
Proof.
Admitted  (* unused *).

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

Lemma Krw_inhabited:
  Krw (Iterate (TmBind TmNull TmNull) Empty) (Iterate TmNull Empty).
Proof.
 unfold Krw.
 intros.
 simpl.
 eauto.
Qed.

Lemma ReducibleK_induction:
  forall T K, ReducibleK Reducible K T ->
  forall P,
      (forall K0, Krw_rt K K0 -> (forall K', Krw K0 K' -> P K') -> P K0) ->
      P K.
Proof.
 intros T K H P IH.
 apply IH.
   apply Krw_rt_refl; auto.
 intros.
Admitted.

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
    split.
    (* Case: that <M, N> : TyPair T1 T2 *)
      sauto.

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
   inversion red as [ | ? Z ? redn_Z | | | | | | | | | | | | | ] ; subst.
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
   apply IHT1; sauto.
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
 simpl; split; auto.
 simpl in X.
 change (ReducibleK Reducible K T) in X0.
 pattern K.
 apply ReducibleK_induction with (T:=T) (K:=K); [auto|].
 intros.
 apply Neutral_Lists in H3; auto.
 destruct H3 as [[M' [s1 s2]] | [K1 [s1 s2]]].
  Focus 2.
  apply reducts_SN; intros.
  subst m'.
  apply H2 with K1; auto.
  (* apply Krw_rt_SNK with K; sauto. *)

 subst m'.
 apply X; auto.
 change (ReducibleK Reducible K0 T).
 eapply Krw_rt_preserves_ReducibleK; seauto.
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

(** Every term [λN] is [Reducible] in a closing, [Reducible]
    environment, provided that every [Reducible] argument [V] substituted
    into [N] gives a [Reducible] term. *)
Set Printing Universes.

Definition env_property Vs Ts P := foreach2_ty Term Ty Vs Ts P.

(* Definition env_Reducible Vs Ts := env_property Vs Ts Reducible. *)
Definition env_Reducible Vs Ts := ahem Vs Ts.

Lemma Reducible_env_value:
  forall Vs Ts x V T,
    env_Reducible Vs Ts -> value V = nth_error Vs x -> value T = nth_error Ts x
    -> Reducible V T.
Proof.
 induction Vs; intros.
  exfalso.
  destruct x; simpl in *; discriminate.
 destruct Ts.
  simpl in X; contradiction.
 destruct x; simpl in *.
  destruct X.
  inversion H0.
  inversion H.
  subst.
  auto.
 destruct X.
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

 inversion redn as [N0 M0 V M'_eq| ? ? ? L_redn | | | | | | | | | | | | | ].

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
  assert (Typing nil y T).
  apply Rw_rt_preserves_types with N; auto.
  assert (Typing nil x S) by (eapply Rw_preserves_types; eauto).
  destruct b; eauto.
 (* All reducts are reducible. *)
 intros M' H3.
 (* Take cases on the reduction. *)
 inversion H3 as [ | | | | | | m n1 n2 H7 | m n | m n | | | | | | ]; subst.
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

Lemma SN_push_under_k:
  forall K M,
    SN (plug K M) ->
    SN M.
Proof.
 induction K.
  simpl.
  auto.
 intros.
 simpl in H.
 pose (s := IHK (TmBind M t) H).
 eapply SN_embedding with (f := fun x => TmBind x t) (Q := TmBind M t); sauto.
Qed.

(* Induction on the reduction sequences of two objects: K and M.
 Unused by might be good practice?
*)
Lemma double_induction_K P K M:
  (forall M0,
     (M ~>> M0) ->
     Neutral M0 ->
     (  (forall K', (Krw K K') -> P K' M0)
      -> (forall M', (M0 ~> M') -> P K M')
      -> P K M0))
  ->
  forall plug_K_M, (plug K M ~>> plug_K_M) ->
                   Neutral M ->
                   SN plug_K_M -> P K M.
Proof.
(* Idea: Use SN_embedding's approach instead. *)
Admitted.


(* (* TODO: Actually, the lemma that follows requires lexicographical *)
(*    induction on K followed by SN M * SN N *)
(*  *) *)

(* Lemma SN_triple_induction (P : Continuation -> Term -> Term -> Type): *)
(*   (forall k x y, *)
(*     (forall k' t, k = Iterate t k' -> P k' x y) -> *)
(*     (forall x', (x ~> x') -> P k x' y) -> *)
(*     (forall y', (y ~> y') -> P k x y') -> P k x y) -> *)
(*   forall k x y, SN x -> SN y -> P k x y. *)
(* Proof. *)
(*  intros. *)
(*  pose (Ind3 := nifty _ H _ H0 k). *)
(*  induction Ind3. *)
(*  apply X. *)
(*    intros. eapply X0; eauto. *)
(*   intros. apply X1; auto. *)
(*   inversion H; auto. *)
(*  intros. apply X2; auto. *)
(*  inversion H0; auto. *)
(* Qed. *)

(* Induction on the reduction sequences of three objects: K, M and N. *)
Lemma triple_induction P K M N:
  (forall M0 N0,
     (M ~>> M0) ->
     (N ~>> N0) ->
     (
       (forall K', (Krw K K') -> P K' M N)
       -> (forall M', (M ~> M') -> P K M' N)
       -> ((forall N', (N ~> N') -> P K M N'))
       -> P K M N))
  ->
  SN (plug K M) -> SN (plug K N) -> P K M N.
Proof.
Admitted.

(**
 When we have a form of term, specified by g, whose reductions are
all "found within" the corresponding form f, then if we have an
example SN term in the image of f, the corresponding term in g's image
is also SN.

The lemma also offers the possibility that some reducts of g-form
terms are not g-form terms, but then they must be shown to be SN by
some other means.
*)

Lemma g_reductions_are_in_f_SN (f g : Continuation -> Term -> Term -> Term):
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
  apply Rw_trans_preserves_SN with (M:=q); auto.
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

Lemma K_TmNull_rw:
  forall K Z,
    (plug K TmNull ~> Z) ->
    {K' : Continuation & { N : Term & ((Z = plug K' TmNull) * (K = (Iterate N K')))%type} } +
    {K' : Continuation & ((Krw K K') * (Z = plug K' TmNull))%type}.
Proof.
 destruct K; simpl; intros Z H.
  inversion H.
 apply Neutral_Lists in H; [| auto].
 destruct H as [[M' [Ha Hb]] | [K' [Ha Hb]]].
  inversion Hb.
    subst.
    left.
    exists K.
    exists t.
    sauto.
   solve [inversion H2].
  subst.
  right.
  exists (Iterate n' K).
  split.
   auto.
   apply rw_in_K_body; sauto.
  sauto.
 right.
 subst.
 exists (Iterate t K').
 simpl.
 firstorder.
Qed.

Lemma SN_embedding2 A f g:
  forall Q' : Term,
    (forall (M : A) (Z : Term),
       (Q' ~>> g M) ->
       (g M ~> Z) ->
       ({M' : A & ((Z = g M') *
                   (f M ~> f M'))%type}
        + SN Z)) ->
    forall Q : Term, SN Q ->
    forall M : A,
      (Q ~>> f M) ->
      (Q' ~>> g M) ->
      SN (g M).
Proof.
 intros Q' H Q H0.
 induction H0.
 rename m into q.
 intros M Q_def Q'_def.
 apply reducts_SN.
 assert (H2 : SN (f M)).
  eauto using Rw_trans_preserves_SN.
 inversion H2 as [H3].
 intros m' H4.
 copy (g M ~> m').
 apply H in H4; try auto.
 destruct H4 as [[M' [m'_form f_M_f_M']] | bailout].
  assert (H5 : {x:Term & ((q ~> x) * (x ~>> f M'))%type}).
   apply last_step_first_step_lemma with (f M); auto.
  destruct H5 as [x [q_x x_f_m']].
  subst m'.
  apply X with (m' := x); auto.
  eauto.
 auto.
Qed.

Lemma Krw_rt_Rw:
   forall K K' M, Krw_rt K K' -> (plug K M ~>> plug K' M).
 intros.
 induction H.
   subst; sauto.
  apply Rw_rt_step.
  sauto.
 seauto.
Qed.

Fixpoint Ksize K :=
  match K with
      Empty => 0
    | Iterate _ K' => S (Ksize K')
  end.

Lemma Ksize_induction P :
  (forall K, Ksize K = 0 -> P K) ->
  (forall n K', (forall K, Ksize K = n -> P K) ->
                (Ksize K' = S n) ->
                (P K')) ->
  forall K,
    P K.
Proof.
 intros H0 H_ind.
 intros K.
 pose (n := Ksize K).
 assert (n = Ksize K) by auto.
 clearbody n.
 revert n K H.
 induction n.
  auto.
 intros K H.
 destruct K.
  simpl in H; auto.
 apply H_ind with (n:=n); sauto.
Qed.

Lemma Ksize_induction_strong P :
  (forall K, (forall K', Ksize K' <  Ksize K -> P K') -> P K) ->
   forall K, P K.
Proof.
 intros X.
 cut (forall n, (forall K', Ksize K' <= n -> P K')).
 eauto.
 induction n.
 - intros.
   destruct K'; auto.
   apply X.
   simpl.
   intros.
   let T := type of H in absurd T.
   omega.
   auto.
   simpl in H; exfalso ; omega.
 - intros.
   apply X.
   intros.
   destruct (le_gt_dec (Ksize K'0) n).
   * apply IHn; auto.
   * apply X.
     intros.
     assert (Ksize K'0 = S n) by omega.
     assert (Ksize K'1 <= n) by omega.
     apply IHn.
     auto.
(* Seems like the above is dodgy; proving it twice? *)
Qed.

Lemma Krw_to_Iterate:
  forall K t K',
  Krw K (Iterate t K') ->
  {K0 : Continuation & { M : Term &
     K = Iterate M K0 }}.
Proof.
 destruct K.
  intros.
  unfold Krw in H.
  specialize (H TmNull).
  simpl in *.
  inversion H.
 intros.
 exists K.
 exists t.
 auto.
Qed.

Fixpoint appendK K1 K2 :=
  match K1 with
    | Empty => K2
    | Iterate N K1' => Iterate N (appendK K1' K2)
  end.

Fixpoint deepest_K M :=
match M with
| TmBind M' N' =>
  let (K, body) := deepest_K M' in
  (appendK K (Iterate N' Empty), body)
| _ => (Empty, M)
end.

(* Fixpoint drop_outermost K := *)
(* match K with *)
(* | Iterate t Empty => (t, Empty) *)
(* | Iterate t K' => let (f, K'') := drop_outermost K' in *)
(*                   (f, Iterate t K'') *)
(* | Empty => (TmNull, Empty) *)
(* end. *)

(* Lemma deepest_K_spec3 : *)
(*   forall K M, *)
(*     notT {M' : Term & {N' : Term & M = TmBind M' N'}} -> *)
(*     deepest_K (plug K M) = (K, M). *)
(* Proof. *)
(*  induction K using Ksize_induction_strong; destruct K; simpl; intros. *)
(*  - destruct M; simpl; auto. *)
(*    contradiction H0. *)
(*    eauto. *)
(*  - rewrite H. *)
(* Qed. *)

Lemma plug_appendK:
  forall K M M',
    plug (appendK K (Iterate M Empty)) M' = TmBind (plug K M') M.
Proof.
 induction K; simpl; auto.
Qed.

Lemma deepest_K_spec:
  forall M K' M',
    deepest_K M = (K', M') ->
    plug K' M' = M.
Proof.
 induction M; simpl; intros; inversion H; auto.
 pose (X := deepest_K M1).
 assert (X = deepest_K M1) by auto.
 destruct X.
 rewrite <- H0 in H.
 inversion H.
 subst.
 pose (IHM1 c M').
 rewrite <- e; auto.
 apply plug_appendK.
Qed.

Lemma appendK_Empty:
  forall K, appendK K Empty = K.
Proof.
 induction K; simpl; auto.
 rewrite IHK.
 auto.
Qed.

Lemma appendK_assoc:
  forall K1 K2 K3,
    appendK (appendK K1 K2) K3 = appendK K1 (appendK K2 K3).
Proof.
 induction K1; simpl; auto.
 intros.
 rewrite IHK1.
 auto.
Qed.

Lemma deepest_K_plug:
  forall K,
     forall M K' M',
       deepest_K M = (K', M') ->
       deepest_K (plug K M) = (appendK K' K, M').
Proof.
 induction K.
 - simpl.
   intros.
   rewrite appendK_Empty.
   auto.
 - simpl.
   intros.
   rewrite IHK with (K':=appendK K' (Iterate t Empty))(M':=M').
   * rewrite appendK_assoc.
     simpl.
     auto.
   * simpl.
     rewrite H.
     auto.
Qed.

(* Lemma deepest_K_spec2 : *)
(*   forall K M N, *)
(*     {M' : Term & {K' : Continuation & *)
(*       {f : Continuation->Continuation & *)
(*        deepest_K (plug K (TmBind M N)) = (f K', M')} & *)
(*        deepest_K (TmBind M N) = (Iterate N K', M')}}. *)
(* Proof. *)
(*  induction K. *)
(*  - simpl. *)
(*    intros. *)
(*    set (X := deepest_K M). *)
(*    destruct X as [K body]. *)
(*    eauto. *)
(*  - intros. *)
(*    simpl. *)
(*    pose (IHK (TmBind M N) t). *)
(*    destruct s as [M' [K' [f Ha] Hb]]. *)
(*    exists M'. *)
(*    exists K'. *)
(*    exists f. *)
(*    * auto. *)
(*    * assert (H0 : deepest_K (TmBind (TmBind M N) t) = *)
(*                   let (K0, M0) := deepest_K (TmBind M N) in *)
(*                   (Iterate t K0, M0)) by auto. *)

(*      rewrite H0 in Hb. *)

(*      pose (X := deepest_K (TmBind M N)). *)
(*      assert (H : X = deepest_K (TmBind M N)) by auto. *)
(*      clearbody X. *)
(*      destruct X. *)
(*      rewrite <- H in Hb. *)
(*      simpl in H. *)

(*      pose (X := deepest_K M). *)
(*      assert (H' : X = deepest_K M) by auto. *)
(*      clearbody X. *)
(*      destruct X. *)

(*      rewrite <- H. *)

(*      inversion Hb. *)
(*      subst. *)
(*      assert (let (K, body) := deepest_K M in *)
(*              (Iterate t (Iterate N K), body) = (Iterate t K', M')). *)

(* Qed. *)

Lemma deepest_K_TmNull K :
  deepest_K (plug K TmNull) = (K, TmNull).
Proof.
 pose (X := deepest_K TmNull).
 assert (X = deepest_K TmNull) by auto.
 simpl in H.
 erewrite deepest_K_plug; eauto.
 simpl.
 auto.
Qed.

Lemma unique_plug_null:
  forall K K',
    (plug K TmNull = plug K' TmNull) -> K = K'.
Proof.
 intros.
 assert (deepest_K (plug K TmNull) = (K, TmNull)).
  apply deepest_K_TmNull.
 assert (deepest_K (plug K' TmNull) = (K', TmNull)).
  apply deepest_K_TmNull.
 congruence.
Qed.

Hint Resolve unique_plug_null.

Lemma Rw_null_Krw:
  forall K' K,
    Ksize K = Ksize K' ->
    (plug K' TmNull ~> plug K TmNull) ->
    Krw K' K.
Proof.
 intros.
 let T := type of H0 in copy T.
 apply K_TmNull_rw in H0.
 destruct H0 as [[K0 [N [Ha Hb]]] | [K0 [Ha Hb]]].
  subst.
  assert (K = K0).
   apply unique_plug_null; auto.
  subst.
  simpl in H.
  exfalso.
  omega.
 assert (K = K0).
  apply unique_plug_null; auto.
 subst.
  auto.
Qed.

Lemma plug_form:
  forall K M,
    (plug K M = M) + ({M1 : Term & {N1 : Term & plug K M = TmBind M1 N1}}).
Proof.
 induction K; simpl.
 - left.
   auto.
 - right.
   destruct (IHK (TmBind M t)); eauto.
Qed.

Lemma Rw_conserves_Ksize:
  forall K K',
    (plug K TmNull ~> plug K' TmNull) -> Ksize K >= Ksize K'.
Proof.
 induction K.
  simpl.
  intros.
  inversion H.
 simpl.
 intros.
 let T := type of H in assert (H' : T) by auto.
 apply Neutral_Lists in H; try auto.
 destruct H as [[M' [Ha Hb]] | [K0 [Ha Hb]]].
  inversion Hb.
    subst.
    assert (K' = K).
     apply unique_plug_null; sauto.
    subst.
    omega.
   subst.
   inversion H2.
  subst.
  assert (K' = Iterate n' K).
   apply unique_plug_null.
   simpl in *; sauto.
  subst.
  simpl.
  omega.
 assert (K' = Iterate t K0).
  apply unique_plug_null.
  simpl in *; sauto.
 subst.
 replace (plug K (TmBind TmNull t)) with (plug (Iterate t K) TmNull) in H' by auto.
 simpl.
 assert (plug K TmNull ~> plug K0 TmNull).
  auto.
 apply IHK in H.
 omega.
Qed.

Lemma Krw_rt_conserves_Ksize:
  forall K K',
    Krw_rt K K' -> Ksize K >= Ksize K'.
Proof.
 intros.
 induction H.
   subst; sauto.
  specialize (k TmNull).
  apply Rw_conserves_Ksize; sauto.
 omega.
Qed.

Lemma rw_step_induction:
  forall P,
    (forall M N, (M ~> N) -> P M -> P N)
    -> forall M N,
         (M ~>> N)
         -> P M
         -> P N.
Proof.
 intros.
 induction H.
 subst.
 auto.
 eauto using X.
 eauto using X.
Qed.

Definition injective A B (f : A -> B) := forall x y, f x = f y -> x = y.

Lemma rw_rt_f_induction:
  forall A f x P M N,
    (forall x, P x x) ->
    (injective _ _ f) ->
    (forall x M, (f x ~>> M) -> {x' : A & M = f x'}) ->
    (forall x y, (f x ~> f y) -> P x y) ->
    (forall x y z, P x y -> P y z -> P x z) ->
    (f x ~>> M) -> (M ~>> N) -> {y : A & M = f y & {z : A & N = f z & P y z}}.
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

Lemma rw_rt_preserves_plug_TmNull:
  forall (x : Continuation) (M N : Term),
    (M ~>> N) -> {x : Continuation& M = plug x TmNull} -> {y : Continuation & N = plug y TmNull}.
Proof.
 intros x M N H H0.
 induction H.
 - subst.
   eauto.
 - destruct H0.
   subst.
   apply K_TmNull_rw in r.
   destruct r.
   destruct s.
   destruct s.
   destruct p.
   exists x1; auto.
   destruct s.
   destruct p.
   exists x1; auto.
 - firstorder.
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

Lemma SN_embedding2' A f g:
    (forall (M : A) (Z : Term),
       (g M ~> Z) ->
       ({M' : A & ((Z = g M') *
                   (f M ~> f M'))%type}
        + SN Z)) ->
    forall M : A,
      SN (f M) ->
        SN (g M).
Proof.
 intros.
 apply SN_embedding2 with (f:=f)(Q:=f M)(Q':=g M).
    intros.
    auto.
   auto.
  auto.
 auto.
Qed.

(* Lemma goofy: *)
(*   forall K M K', *)
(*     SN (plug K M) -> (plug K TmNull ~> plug K' TmNull) -> SN (plug K' M). *)
(* Proof. *)
(*  intros. *)
(*  apply SN_embedding2 with (f := fun m => plug K m) *)
(*                           (g := fun m => plug K' m) *)
(*                           (Q := plug K M) *)
(*                           (Q' := plug K' M); try auto. *)
(*  intros. *)

(* Qed. *)

Inductive prefix : Continuation -> Continuation -> Set :=
  prefix_refl : forall K, prefix K K
| prefix_frame :forall K K' N, prefix K' K -> prefix K' (Iterate N K).

Lemma reexamine:
  forall K' K,
    prefix K' K
    -> forall M, {M' : Term & plug K' M' = plug K M}.
Proof.
 induction K; simpl; intros.
  inversion H.
  subst.
  simpl.
  exists M; sauto.

 inversion H.
  subst.
  exists M.

   auto.

 subst.
 pose (IHK H2 (TmBind M t)).
 destruct s.
 eauto.
Qed.

(* Lemma dropoff_lemma: *)
(*   forall K K', *)
(*     (plug K TmNull ~>> plug K' TmNull) *)
(*     -> {K'' : Continuation & (Krw_rt K K'' * *)
(*         {K''' : Continuation & *)
(*           ((plug K'' TmNull ~> plug K''' TmNull) * *)
(*            (Ksize K''' < Ksize K'') * *)
(*            (plug K''' TmNull ~>> plug K' TmNull))%type})%type}. *)
(* Proof. *)

(* Qed. *)

Inductive relK : Continuation -> Continuation -> Set :=
  rw : forall K K', Krw K K' -> relK K K'
| strip : forall K K' t, K = Iterate t K' -> relK K K'.

Inductive relK_rt  : Continuation -> Continuation -> Set :=
  refl : forall K, relK_rt K K
| step : forall K K', relK K K' -> relK_rt K K'
| trans : forall K K' K'', relK_rt K K' -> relK_rt K' K'' -> relK_rt K K''.

Hint Constructors relK relK_rt.

Lemma magic:
forall K K',
  relK_rt K K'
  -> forall M,
       SN (plug K M)
  -> {M' : Term & SN (plug K' M')}.
Proof.
 intros K K' rel.
 induction rel; intros M sn.
   seauto.
  destruct r.
   pose (k M).
   exists M.
   inversion sn.
   seauto.
  lapply (reexamine K' (Iterate t K')).
   intros H.
   subst.
   specialize (H M).
   destruct H.
   exists x.
   simpl in *.
   rewrite e.
   sauto.
  apply prefix_frame.
  apply prefix_refl.
 pose (s := IHrel1 M sn).
 destruct s.
 pose (IHrel2 x s).
 sauto.
Qed.

Lemma K_TmNull_relK:
  forall K K',
    (plug K TmNull ~> plug K' TmNull)
    -> relK K K'.
Proof.
 intros.
 apply K_TmNull_rw in H.
 destruct H as [[K_shorter [N [H1a H1b]]] | [K'' [H1a H1b]]].
  subst.
  eapply strip.
  apply unique_plug_null in H1a.
  subst.
  eauto.
  apply rw.
 apply unique_plug_null in H1b.
 subst.
 auto.
Qed.

Definition is_K_null M := {K : Continuation & M = plug K TmNull}.

Definition gimme_K M (p : is_K_null M) := projT1 p.

Lemma K_TmNull_rw_abstract
     : forall (K : Continuation) (Z : Term),
       (plug K TmNull ~> Z) ->
       {K' : Continuation & Z = plug K' TmNull}.
Proof.
intros.
apply K_TmNull_rw in H.
destruct H; firstorder.
Qed.

Lemma K_TmNull_rw_rt:
  forall A Z,
    (A ~>> Z) ->
    is_K_null A -> is_K_null Z.
Proof.
 intros.
 induction H; unfold is_K_null; firstorder; subst.
  subst.
  eauto.
 eauto using K_TmNull_rw_abstract.
Qed.

Lemma K_TmNull_relK_rt_inner:
  forall A Z
    (pA : is_K_null A) (pZ: is_K_null Z),
    (A ~>> Z) ->
    relK_rt (gimme_K A pA) (gimme_K Z pZ).
Proof.
 intros.
 induction H; destruct pA; destruct pZ; subst; simpl in *.
   apply unique_plug_null in e.
   subst.
   apply refl.
  apply step.
  apply K_TmNull_rw in r.
  destruct r as [[K' [N [H1a H1b]]] | [K' [H1a H1b]]].
   subst x.
   replace x0 with K'.
    eapply strip; eauto.
   apply unique_plug_null; auto.
  apply rw.
  replace x0 with K'.
   sauto.
  apply unique_plug_null; auto.
 assert (is_K_null (plug x TmNull)).
  unfold is_K_null.
  eauto.
 specialize (IHRewritesTo_rt1 H1).
 assert (is_K_null m).
  apply K_TmNull_rw_rt with (A := plug x TmNull); auto.
 specialize (IHRewritesTo_rt1 H2).
 replace (gimme_K (plug x TmNull) H1) with x in IHRewritesTo_rt1.
  apply trans with (gimme_K m H2); auto.
  assert (H3 : is_K_null (plug x0 TmNull)).
   unfold is_K_null.
   eauto.
  specialize (IHRewritesTo_rt2 H2 H3).
  replace (gimme_K (plug x0 TmNull) H3) with x0 in IHRewritesTo_rt2.
   exact IHRewritesTo_rt2.
  unfold gimme_K.
  unfold projT1.
  destruct H3.
  apply unique_plug_null; auto.
 unfold gimme_K.
 unfold projT1.
 destruct H1.
 apply unique_plug_null; auto.
Qed.

Lemma K_TmNull_relK_rt:
  forall K K',
    (plug K TmNull ~>> plug K' TmNull)
    -> relK_rt K K'.
Proof.
 intros.
 assert (is_K_null (plug K TmNull)).
  unfold is_K_null.
  eauto.
 assert (is_K_null (plug K' TmNull)).
  unfold is_K_null.
  eauto.
 eapply K_TmNull_relK_rt_inner in H; eauto.
 replace (gimme_K (plug K TmNull) H0) with K in H.
  replace (gimme_K (plug K' TmNull) H1) with K' in H.
   auto.
  destruct H1.
  simpl.
  auto using unique_plug_null.
 destruct H0.
 simpl.
 auto using unique_plug_null.
Qed.

Lemma SN_K_M_SN_K_Null:
  forall K M,
    SN (plug K M)
    -> SN (plug K TmNull).
Proof.
 intros K.
 induction K using Ksize_induction_strong.
 intros M H0.
 rename H into IHK.
 apply SN_embedding2 with
     (f := fun k => plug k M)
     (g := fun k => plug k TmNull)
     (Q := plug K M)
     (Q' := plug K TmNull); try auto.
 intros K0 Z H2 H3.

 let T := type of H3 in copy T.
 apply K_TmNull_rw in H3.
 destruct H3 as [[K_shorter [N [H1a H1b]]] | [K' [H1a H1b]]].
  subst.
  right.

  assert (relK_rt K K_shorter).
   assert (relK_rt K (Iterate N K_shorter)).
    apply K_TmNull_relK_rt.
    auto.
   apply trans with (K' := Iterate N K_shorter).
    auto.
   apply step.
   eapply strip; eauto.

  apply magic with (M:=M) in H1.
   destruct H1 as [M' SN_M'].

   apply IHK with (M:=M').
    apply Rw_rt_conserves_Ksize in H2.
    simpl in *; sauto.
   auto.
  auto.

 left.
 exists K'.
 firstorder.
Qed.

Lemma Krw_rt_Rw_rt:
  forall K K' M, Krw_rt K K' -> (plug K M ~>> plug K' M).
Proof.
 intros.
 induction H; subst; eauto.
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
 assert (SN (plug (Iterate t K') (TmSingle M))).
  apply Rw_trans_preserves_SN with (plug K (TmSingle M)).
   apply X.
   sauto.
  apply Krw_rt_Rw_rt.
  sauto.
 apply SN_K_M_SN_K_Null with (TmSingle M).
 sauto.
Qed.

Lemma SN_Union: forall M N, SN M -> SN N -> SN (TmUnion M N).
Proof.
 intros.
 apply reducts_SN.
 intros Z H1.
 inversion H1.
Qed.

Lemma Rw_rt_under_K:
  forall K M N,
    (M ~>> N) -> (plug K M ~>> plug K N).
Proof.
 intros K M N red.
 induction red.
   subst; auto.
  eauto using Rw_rt_step, Rw_under_K.
 eauto.
Qed.

(* (* TODO: Should be able to get "induction on Krw sequences" directly
      from SN . plug like this: *)
SN (plug K M) ->
(forall K0, Krw_rt K K0 -> (forall K', Krw K0 K' -> (P K' -> P K0))) ->
P K.
 *)

(* Inductive Triple_SN K M N := *)
(*   | triple_sn : *)
(*        (forall K', (Krw K K') -> Triple_SN K' M N) *)
(*     -> (forall M', (M ~> M') -> Triple_SN K M' N) *)
(*     -> (forall N', (N ~> N') -> Triple_SN K M N') *)
(*     -> Triple_SN K M N. *)

Inductive Triple_SN K M N :=
  | triple_sn :
       (forall K' t, K = Iterate t K' -> Triple_SN K' M N)
    -> (forall M', (M ~> M') -> Triple_SN K M' N)
    -> (forall N', (N ~> N') -> Triple_SN K M N')
    -> Triple_SN K M N.

Lemma nifty:
  forall M, SN M -> forall N, SN N -> forall K, Triple_SN K M N.
Proof.
 intros M SN_M.
 induction SN_M.
 intros N SN_N.
 induction SN_N.
 rename m into M.
 rename m0 into N.
 induction K.
  apply triple_sn.
    discriminate.
   auto.
  auto.
  apply triple_sn.
   intros.
   inversion H1; subst.
   auto.
  intros.
  auto.
 auto.
Qed.

Lemma triple_induction2 P K M N:
  (forall M0 N0,
     (M ~>> M0) ->
     (N ~>> N0) ->
     (
       (forall K', (Krw K K') -> P K' M N)
       -> (forall M', (M ~> M') -> P K M' N)
       -> ((forall N', (N ~> N') -> P K M N'))
       -> P K M N))
  ->
  SN M -> SN N -> P K M N.
Proof.
Admitted.

Lemma SN_K_Union:
  forall K,
  forall M N, SN (plug K M) -> SN (plug K N) -> SN (plug K (TmUnion M N)).
Proof.
 induction K.
 intros.
  simpl in *.
  double_induction_SN M N.
  intros.
  apply SN_Union; auto.
   eauto using Rw_trans_preserves_SN.
  eauto using Rw_trans_preserves_SN.
  intros.
 remember (Iterate t K) as K0.
 apply triple_induction with (K := K0) (M := M) (N := N); [|sauto|sauto].
 intros.
 subst; simpl.

 apply reducts_SN.
 intros Z H_rw.
 simpl in H_rw.
 apply Neutral_Lists in H_rw; [| sauto].
 destruct H_rw as [[M' [Z_def rw]] | [K' [Z_def rw]]].
 (* Case: rw is within TmBind (TmUnion M N) t *)
  subst.
  inversion rw; subst.
    apply IHK.
     simpl in *.
     auto.
    simpl in *.
    auto.
   inversion H9.

 (* Case: rw is within t of TmBind (TmUnion M N) t *)
  subst.
  change (SN (plug (Iterate n' K) (TmUnion M N))).
  assert (Krw (Iterate t K) (Iterate n' K)).
  unfold Krw.
  simpl.
  intros.
  apply Rw_under_K.
  eauto.
  apply H3.
  auto.

 (* Case: rw is within K *)
 subst.
 change (SN (plug (Iterate t K') (TmUnion M N))).
 apply H3.
 apply iterate_reduce.
 auto.
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

Lemma unshift_var_unshift_var_commute:
  forall x k k' n,
    k' <= k ->
    unshift_var k n (unshift_var k' 1 x) =
    unshift_var k' 1 (unshift_var (S k) n x).
Proof.
 intros x k k' n H.
 unfold unshift_var at 2 4.
 break; break.
    unfold unshift_var.
    break; break; omega.
   unfold unshift_var.
   break; break; omega.
  unfold unshift_var.
  break; break; omega.
 unfold unshift_var.
 break; break; omega.
Qed.

Lemma unshift_unshift_commute:
  forall M k k' n,
    k' <= k ->
    unshift k n (unshift k' 1 M) =
    unshift k' 1 (unshift (S k) n M).
Proof.
 induction M; simpl; intros.
          auto.
         rewrite unshift_var_unshift_var_commute; sauto.
        rewrite IHM1, IHM2; sauto.
       rewrite IHM; sauto.
      rewrite IHM; auto.
      omega.
     rewrite IHM1, IHM2; sauto.
    auto.
   rewrite IHM; sauto.
  rewrite IHM1, IHM2; sauto.
 rewrite IHM1, IHM2; solve [auto|omega].
Qed.
(* TODO: Move above 2 lemmas to Shift.v *)

Lemma shift_var_unshift_var_commute:
  forall x k k' n,
    k' <= k ->
    unshift_var (S k) n (shift_var k' 1 x) = shift_var k' 1 (unshift_var k n x).
Proof.
 intros x k k' n H.
 unfold unshift_var.
 break; break.
    unfold shift_var.
    break; break; omega.
   unfold shift_var in *.
   break; omega.
  unfold shift_var in *.
  break; break; omega.
 unfold shift_var in *.
 break; omega.
Qed.

Lemma shift_unshift_commute:
  forall M k k' n,
    k' <= k ->
    unshift (S k) n (shift k' 1 M) = shift k' 1 (unshift k n M).
Proof.
 induction M; simpl; intros.
          auto.
         rewrite shift_var_unshift_var_commute; sauto.
        rewrite IHM1, IHM2; sauto.
       rewrite IHM; sauto.
      rewrite IHM; solve [auto|omega].
     rewrite IHM1, IHM2; sauto.
    auto.
   rewrite IHM; sauto.
  rewrite IHM1, IHM2; sauto.
 rewrite IHM1, IHM2; solve [auto|omega].
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
          destruct (nth_error_dichot _ (shift 0 1 (unshift n k M) :: nil) (unshift_var (S n) k x - n')) as [[H3 H4]|[H3 H4]].
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
         destruct (nth_error_dichot _ (shift 0 1 (unshift n k M) :: nil) (unshift_var (S n) k x - n')) as [[H3 H4]|[H3 H4]].
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
             rewrite shift_unshift_commute.
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
       rewrite shift_unshift_commute; solve [omega | auto].
      solve [omega].
     rewrite IHN1, IHN2; sauto.
    trivial.
   rewrite IHN; sauto.
  rewrite IHN1, IHN2; sauto.
 rewrite IHN1, IHN2.
   rewrite shift_unshift_commute; solve [omega | auto].
  solve [omega].
 sauto.
Qed.

Lemma unshift_preserves_rw:
  forall M M' n k,
    (M ~> M') ->
    unshift n k M ~>
    unshift n k M'.
Proof.
 induction M; intros; inversion H; subst; simpl.
               eauto.
              eauto.
             eauto.
            eauto.
           eauto.
          eauto.
         apply Rw_beta.
         apply beta_with_unshift.
         omega.
        eauto.
       eauto.
      eauto.
     eauto.
    eauto.
   eauto.
  eauto.
 eauto.
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

Lemma two:
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

Lemma SN_beta_withdraw_under_k:
  forall K L N,
    SN L ->
    SN (plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))) ->
    SN (plug K (TmAbs N @ L)).
Proof.
 intros.
 assert (SN N).
  apply SN_push_under_k in H0.
  eauto using two.
 apply triple_induction2 with (K:=K) (M:=N) (N:=L).  (* XXX rename to triple_induction_SN *)
 intros.
 apply reducts_SN.
 intros.
 apply Neutral_Lists in H7; try auto.
 destruct H7 as [[M' [H7a H7b]] | [K' [H7a H7b]]].
  inversion H7b; subst.
      auto.
     inversion H10.
     subst.
     apply H5.
     auto.
    apply H6.
    auto.
   subst.
   apply H4.
   auto.
  auto.
 auto.
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
  eauto using two.
 apply triple_induction2 with (K:=K) (M:=N) (N:=L); auto.  (* XXX rename to triple_induction_SN *)
 intros.
 apply reducts_SN.
 intros.
 apply Neutral_Lists in H7; try auto.
 destruct H7 as [[M' [H7a H7b]] | [K' [H7a H7b]]].
  inversion H7b; subst.
    apply SN_beta_withdraw_under_k; sauto.
   inversion H10.
   subst.
   apply H6.
   sauto.
  seauto.
 subst.
 eauto using H4.
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
 simpl.
 intros.
 intuition.
 apply TBind with S; auto.
  (* destruct (Reducible_inhabited S) as [x r]. *)
  (* pose (p := X0 x r). *)
  (* destruct p. *)
  (* eapply Rw_beta_preserves_types_conv; seauto. *)
 pose (K' := Iterate N K).
 assert (SN (plug K' M)).
  apply b.
  intros.
  subst K'.
  simpl.
  apply bind_sn_withdraw.
   solve [eauto using Reducible_SN].
  apply X0.
   auto.
  apply X.
 change (SN (plug (Iterate N K) M)).
 sauto.
Qed.

Lemma shift_closed_noop_map:
  forall n k vs ts,
    env_typing vs ts
    -> vs = map (shift n k) vs.
Proof.
 induction vs as [|a vs]; simpl; intros.
  auto.
 destruct ts.
  exfalso.
  destruct H.
  simpl in *.
  discriminate.
 destruct H.
  simpl in *.
 unfold foreach2_ty in f.
 simpl in f.
 destruct f.
 replace (shift n k a) with a.
  rewrite <- IHvs with (ts := ts).
   auto.
  auto.
 solve [erewrite shift_closed_noop; eauto].
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
  eapply subst_env_preserves_typing with (env' := tyEnv).
     rewrite env_typing_shift_noop with (env := tyEnv); auto.
    simpl.
    auto.
   auto.
  eapply IHM1; eauto.

 intros.
 pose (Reducible_welltyped_closed _ _ X).
 replace (shift 0 1 L) with L.
  replace (map (shift 0 1) Vs) with Vs.
   rewrite subst_env_concat with (env := s :: tyEnv).
    unfold app.
    replace (unshift 0 1 (subst_env 0 (L :: Vs) M2))
       with (subst_env 0 (L :: Vs) M2).
     eapply IHM2; eauto.
     simpl.
     auto.
    assert (Typing nil (subst_env 0 (L :: Vs) M2) (TyList t)).
     eapply closing_subst_closes; seauto.
    erewrite unshift_closed_noop; seauto.
   apply env_typing_cons; sauto.
   eapply shift_closed_noop_map; seauto.
  erewrite shift_closed_noop; seauto.
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
