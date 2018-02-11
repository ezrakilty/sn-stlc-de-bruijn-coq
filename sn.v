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

Lemma Neutral_TmBind_left:
  forall M N Z,
    (Neutral M) -> (TmBind M N ~> Z) ->
    {M' : Term & ((Z = TmBind M' N) * (M ~> M'))%type}.
Proof.
 intros.
 inversion H0.
 subst.
 inversion H.
 subst.
 inversion H.
 subst.
 inversion H.
 subst.
 firstorder.
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
 simpl.
 intros.
 apply IHK in H0; try apply Neutral_TmBind.
 destruct H0.
 (* Case : redn of K@M' is inside M'. *)
  left.
  destruct s as [x [H0 H1]].
  apply Neutral_TmBind_left in H1; auto.
  destruct H1 as [M' [H10 H11]].
  exists M'.
  subst x.
  auto.
 (* Case : redn of K@M' in inside K. *)
 right.
 destruct s as [x [H0 H1]].
 exists (Iterate t x).
 simpl.
 intuition.
 apply iterate_reduce; sauto.
Qed.

(* BEGIN garbage *)

(* Inductive f : Continuation -> Continuation -> Prop := *)
(*   | e : f Empty Empty *)
(*   | t : forall N N' K, (N ~> N') -> f (Iterate N K) (Iterate N' K) *)
(*   | b : forall N K K', f K K' -> f (Iterate N K) (Iterate N K'). *)

(* Inductive f_r K := *)
(*   | f_r_r : (forall K', f K K' -> f_r K') -> f_r K. *)

(* Lemma f_r_induction_1 K P: *)
(*   (forall K, (forall K', f K K' -> P K') -> P K) -> *)
(*   f_r K -> *)
(*   P K. *)
(* Proof. *)
(*  intros. *)
(*  induction H. *)
(*  eauto. *)
(* Qed. *)

(* Lemma Krw_implies_f K K': *)
(*   Krw K K' -> f K K'. *)
(* Proof. *)
(*  unfold Krw. *)
(*  intros. *)
(*  destruct K; destruct K'; simpl in H. *)
(*     apply e. *)
(*    exfalso. *)
(*    specialize (H TmConst). *)
(*    inversion H. *)
(*   exfalso. *)
(*   admit. *)
(*  admit. *)
(* Admitted. *)

(* Goal forall K, (forall K', Krw K K' -> SNK K') -> SNK K. *)
(* Proof. *)
(* intros. *)
(*  unfold SNK. *)
(*  intros. *)
(*  apply reducts_SN. *)
(*  intros. *)
(*  induction K; induction H0. *)
(*   simpl in *. *)
(*   inversion H1; subst. *)
(*   assert (SN m'0). *)
(*   inversion H1. *)
(*   eauto. *)
(*   apply SN_TmSingle; auto. *)
(*  simpl in *. *)
(*  apply Neutral_Lists in H1. *)
(*  destruct H1 as [[M' [H1 H2]] | [K' [H1 H2]]]. *)
(* Qed. *)

(* Lemma SNK_f_r K: *)
(*   (SNK K -> f_r K) *)
(*   * (f_r K -> SNK K). *)
(* Proof. *)
(*  split. *)
(*   admit. *)
(*  unfold SNK. *)
(*  intros. *)
(*  induction H. *)
(*  apply reducts_SN. *)
(*  intros. *)
(* Admitted. *)

(* Lemma SNK_induction K P: *)
(*   SNK K -> *)
(*   (forall K', Krw_rt K K' -> *)
(*               (forall K'', Krw K' K'' -> P K'') -> P K') -> *)
(*   P K. *)
(* Proof. *)
(*  intros. *)
(*  assert (f_r K). *)
(*  unfold SNK in H. *)
(*  assert (SN TmConst) by auto. *)
(*  specialize (H TmConst H0). *)
(*  cut (Krw_rt K K). *)
(*  pattern K at 2 3. *)
(*  induction H. *)
(* Admitted. *)

(* Lemma SNK_induction K P: *)
(*   SNK K -> *)
(*   (forall K', Krw_rt K K' -> *)
(*               (forall K'', Krw K' K'' -> P K'') -> P K') -> *)
(*   P K. *)
(* Proof. *)
(*  intros. *)
(*  unfold SNK in H. *)
(*  assert (SN TmConst) by auto. *)
(*  specialize (H TmConst H0). *)
(*  cut (Krw_rt K K). *)
(*  pattern K at 2 3. *)
(*  induction H. *)
(*   intros H1; specialize (H1 K); apply H1; apply Krw_rt_refl; auto. *)
(*  induction H. *)
(* Admitted. *)

(* END garbage *)

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
Admitted.

Lemma Empty_unrewritable: forall K, (Krw Empty K) -> False.
Proof.
 unfold Krw.
 intros.
 specialize (H TmConst).
 destruct K; simpl in H; inversion H.
Qed.

Inductive Ktyping : Continuation -> Ty -> Type :=
  Ktype : forall K T env S M, Typing env M T -> Typing nil (plug K M) S -> Ktyping K T.

(* Inductive immed_subterm : Term -> Term -> Prop := *)
(* | immed_subterm_pair_left : *)
(*     forall l r, immed_subterm l (TmPair l r) *)
(* | immed_subterm_pair_right : *)
(*     forall l r, immed_subterm r (TmPair l r) *)
(* | immed_subterm_proj : *)
(*     forall b m, immed_subterm m (TmProj b m) *)
(* | immed_subterm_abs : *)
(*     forall n, immed_subterm n (TmAbs n) *)
(* | immed_subterm_app_left : *)
(*     forall l r, immed_subterm l (TmApp l r) *)
(* | immed_subterm_app_right : *)
(*     forall l r, immed_subterm r (TmApp l r) *)
(* | immed_subterm_single : *)
(*     forall m, immed_subterm m (TmSingle m) *)
(* | immed_subterm_union_left : *)
(*     forall l r, immed_subterm l (TmUnion l r) *)
(* | immed_subterm_union_right : *)
(*     forall l r, immed_subterm r (TmUnion l r) *)
(* | immed_subterm_bind_left : *)
(*     forall l r, immed_subterm l (TmBind l r) *)
(* | immed_subterm_bind_right : *)
(*     forall l r, immed_subterm r (TmBind l r) *)
(* . *)

(* Hint Constructors immed_subterm. *)

(* Inductive subterm : Term -> Term -> Prop := *)
(*   subterm_immed_subterm : forall m m', immed_subterm m m' -> subterm m m' *)
(* | subterm_pair_left : *)
(*     forall l' l r, subterm l' l -> subterm l' (TmPair l r) *)
(* | subterm_pair_right : *)
(*     forall r' l r, subterm r' r -> subterm r' (TmPair l r) *)
(* | subterm_proj : *)
(*     forall m' b m, subterm m' m -> subterm m' (TmProj b m) *)
(* | subterm_abs : *)
(*     forall n' n, subterm n' n -> subterm n' (TmAbs n) *)
(* | subterm_app_left : *)
(*     forall l' l r, subterm l' l -> subterm l' (TmApp l r) *)
(* | subterm_app_right : *)
(*     forall r' l r, subterm r' r -> subterm r' (TmApp l r) *)
(* | subterm_single : *)
(*     forall m' m, subterm m' m -> subterm m' (TmSingle m) *)
(* | subterm_union_left : *)
(*     forall l' l r, subterm l' l -> subterm l' (TmUnion l r) *)
(* | subterm_union_right : *)
(*     forall r' l r, subterm r' r -> subterm r' (TmUnion l r) *)
(* | subterm_bind_left : *)
(*     forall l' l r, subterm l' l -> subterm l' (TmBind l r) *)
(* | subterm_bind_right : *)
(*     forall r' l r, subterm r' r -> subterm r' (TmBind l r) *)
(* . *)

(* Hint Constructors subterm. *)

(* Lemma no_self_immed_subterm : *)
(*   forall M, *)
(*     immed_subterm M M -> False. *)
(* Proof. *)
(*  induction M; intros; inversion H; try subst. *)
(*            subst l r. *)
(*            apply IHM1. *)
(*            replace M1 with (TmPair M1 M2) at 2. *)
(*            apply immed_subterm_pair_left. *)
(*           admit. *)
(*          apply IHM. *)
(*          replace M with (TmProj b M) at 2. *)
(*          apply immed_subterm_proj. *)
(* Admitted. *)

(* Lemma no_self_subterm : *)
(*   forall M, *)
(*     subterm M M -> False. *)
(* Proof. *)
(*  induction M; intros; inversion H; inversion H0; try subst. *)
(* Admitted. *)

(* Lemma no_self_reduction: *)
(*   forall M, *)
(*   (M ~> M) -> False. *)
(* Proof. *)
(*  induction M; intros; inversion H; try subst. *)
(*            apply IHM1; auto. *)
(*           apply IHM2; auto. *)
(*          apply IHM; auto. *)
(*         apply no_self_subterm with m. *)
(*         rewrite H0 at 2. *)
(*         auto. *)
(*        apply no_self_subterm with n. *)
(*        rewrite H0 at 2. *)
(*        auto. *)
(*       auto. *)
(* Qed. *)

Axiom no_Krw : forall K K', Krw K K' -> False.

Lemma Krw_characterization:
  forall K T K' N,
    Ktyping K T ->
    Krw (Iterate N K) K' ->
    {K1 : Continuation & ((K' = Iterate N K1) * (Krw K K1))%type} +
    {N' : Term & ((K' = Iterate N' K) * (N ~> N'))%type}.
Proof.
Admitted.

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
 apply no_Krw in H0.
 intuition.
 
 (* unfold ReducibleK in *. *)
 (* assert (X : {M : Term & Reducible M T}). *)
 (*  admit. *)
 (* destruct X as [M M_Red]. *)
 (* specialize (H M M_Red). *)

 (* induction K. *)
 (* apply IH. *)
 (*  intros. *)
 (*  apply Empty_unrewritable in H0. *)
 (*  inversion H0. *)
 (* apply IH. *)
 (* intros. *)
 (* apply Krw_characterization with (T:=T) in H0. *)
 (* destruct H0 as [[K1 [K'_def K_K1_rw]] *)
 (*                |[]]. *)
 (* subst K'. *)
 
 
 (*  (* OK: We absolutely need to define Krw inductively in its own right. *) *)
 (* remember (plug K (TmSingle M)) as M0. *)
 (* assert (M0 ~>> M0) by auto. *)
 (* revert H0. *)
 (* pattern M0 at 2. *)
 (* cut (forall M0', (M0 ~>> M0') -> P K). *)
 (*  firstorder. *)
 (* intros. *)
 (* assert (SN M0') by admit. *)
 (* induction H1. *)
 (* induction H; eauto. *)
 (* apply IH. *)
 (* intros. *)
 
Qed.

(* Lemma reducts_ReducibleK K T: *)
(*   (forall K', Krw K K' -> ReducibleK Reducible T K') -> ReducibleK Reducible T K. *)
(* Proof. *)
(*  unfold ReducibleK. *)
(*  intros H M H0. *)
(*  redseq_induction M. *)
(*  apply reducts_SN. *)
(*  intros. *)
(*  induction K; simpl in *. *)
(*   inversion H2; subst. *)
(*   apply SN_TmSingle. *)
(*   eapply Rw_trans_preserves_SN; eauto. *)
(*  apply Neutral_Lists in H2. *)
(*   destruct H2 as [[M' [H2 H3]] | [K' [H2 H3]]]; subst. *)
(*    inversion H3; subst. *)
(*     admit. *)
(*    assert (SN m'). *)
(*     inversion H6; subst. *)
(*     apply SN_TmSingle. *)
(*     eapply Rw_trans_preserves_SN; eauto. *)
(*    inversion H6; subst. *)
(*    apply IHM; eauto. *)
(*   assert (SN (plug (Iterate t K') (TmSingle M))). *)
(*    apply H; auto. *)
(*    apply iterate_reduce; auto. *)
(*   change (SN (plug (Iterate t K') (TmSingle M0))). *)
(*   assert (TmSingle M ~>> TmSingle M0). *)
(*    auto using TmSingle_rw_rt. *)
(*   eauto using plug_SN_rw_rt. *)
(*  solve [apply Neutral_TmBind]. *)
(* Qed. *)

(* Lemma reducts_SNK K: *)
(*   (forall K', Krw K K' -> SNK K') -> SNK K. *)
(* Proof. *)
(*  unfold SNK. *)
(*  intros H M H0. *)
(*  redseq_induction M. *)
(*  apply reducts_SN. *)
(*  intros. *)
(*  induction K; simpl in *. *)
(*   inversion H2; subst. *)
(*   apply SN_TmSingle. *)
(*   eapply Rw_trans_preserves_SN; eauto. *)
(*  apply Neutral_Lists in H2. *)
(*   destruct H2 as [[M' [H2 H3]] | [K' [H2 H3]]]; subst. *)
(*    inversion H3; subst. *)
(*     admit. *)
(*    assert (SN m'). *)
(*     inversion H6; subst. *)
(*     apply SN_TmSingle. *)
(*     eapply Rw_trans_preserves_SN; eauto. *)
(*    inversion H6; subst. *)
(*    apply IHM; eauto. *)
(*   assert (SN (plug (Iterate t K') (TmSingle M))). *)
(*    apply H; auto. *)
(*    apply iterate_reduce; auto. *)
(*   change (SN (plug (Iterate t K') (TmSingle M0))). *)
(*   assert (TmSingle M ~>> TmSingle M0). *)
(*    auto using TmSingle_rw_rt. *)
(*   eauto using plug_SN_rw_rt. *)
(*  solve [apply Neutral_TmBind]. *)
(* Admitted. *)

(* Lemma reducts_SNK K: *)
(*   (forall K', Krw K K' -> SNK K') -> SNK K. *)
(* Proof. *)
(*  unfold SNK. *)
(*  intros H M H0. *)
(*  redseq_induction M. *)
(*  apply reducts_SN. *)
(*  intros. *)
(*  induction K; simpl in *. *)
(*   inversion H2; subst. *)
(*   apply SN_TmSingle. *)
(*   eapply Rw_trans_preserves_SN; eauto. *)
(*  apply Neutral_Lists in H2. *)
(*   destruct H2 as [[M' [H2 H3]] | [K' [H2 H3]]]; subst. *)
(*    inversion H3; subst. *)
(*     admit. *)
(*    assert (SN m'). *)
(*     inversion H6; subst. *)
(*     apply SN_TmSingle. *)
(*     eapply Rw_trans_preserves_SN; eauto. *)
(*    inversion H6; subst. *)
(*    apply IHM; eauto. *)
(*   assert (SN (plug (Iterate t K') (TmSingle M))). *)
(*    apply H; auto. *)
(*    apply iterate_reduce; auto. *)
(*   change (SN (plug (Iterate t K') (TmSingle M0))). *)
(*   assert (TmSingle M ~>> TmSingle M0). *)
(*    auto using TmSingle_rw_rt. *)
(*   eauto using plug_SN_rw_rt. *)
(*  solve [apply Neutral_TmBind]. *)
(* Admitted. *)

(* Lemma SNK_induction_strong K P: *)
(*   SNK K -> *)
(*   (forall K', (forall K'', Krw K' K'' -> P K'') -> P K') -> *)
(*   P K. *)
(* Proof. *)
(*  intro H. *)
(*  assert (Krw_rt K K). *)
(*   apply Krw_rt_refl; auto. *)
(*  revert H0. *)
(*  pattern K at 2 3. *)
(*  generalize K at 2. *)
(*  intros. *)
(*  unfold SNK in H. *)
(*  specialize (H TmConst). *)
(*  assert (H1:SN TmConst) by auto. *)
(*  specialize (H H1). *)
(*  remember (plug K (TmSingle TmConst)) as M. *)
(*  redseq_induction M. *)
(*  apply X. *)
(*  intros. *)
 
(* Qed. *)

(* Lemma SNK_induction K P: *)
(*   SNK K -> *)
(*   (forall K', Krw_rt K K' -> *)
(*               (forall K'', Krw K' K'' -> P K'') -> P K') -> *)
(*   P K. *)
(* Proof. *)
(* Admitted. *)

(* Lemma reducts_ReducibleK K T: *)
(*   (forall M, Reducible M T -> SN M) -> *)
(*   (forall K', Krw K K' -> ReducibleK Reducible T K') -> ReducibleK Reducible T K. *)
(* Proof. *)
(*  unfold ReducibleK. *)
(*  intros Ass H M H0. *)
(*  assert (SN_M : SN M) by auto. *)
(*  redseq_induction M. *)
(*  apply reducts_SN. *)
(*  intros. *)
(*  induction K; simpl in *. *)
(*   inversion H2; subst. *)
(*   apply SN_TmSingle. *)
(*   eapply Rw_trans_preserves_SN; eauto. *)
(*  apply Neutral_Lists in H2. *)
(*   destruct H2 as [[M' [H2 H3]] | [K' [H2 H3]]]; subst. *)
(*    inversion H3; subst. *)
(*     assert (Reducible M0 T). *)
(*      admit. *)
(* (* Ugh *) *)
(*     cut (SN (plug K (subst_env 0 (M0::nil) t))). *)
(*      admit. *)
    
(*     admit. *)
(*    assert (SN m'). *)
(*     inversion H6; subst. *)
(*     apply SN_TmSingle. *)
(*     eapply Rw_trans_preserves_SN; eauto. *)
(*    inversion H6; subst. *)
(*    apply IHM; eauto. *)
(*   assert (SN (plug (Iterate t K') (TmSingle M))). *)
(*    apply H; auto. *)
(*    apply iterate_reduce; auto. *)
(*   change (SN (plug (Iterate t K') (TmSingle M0))). *)
(*   assert (TmSingle M ~>> TmSingle M0). *)
(*    auto using TmSingle_rw_rt. *)
(*   eauto using plug_SN_rw_rt. *)
(*  solve [apply Neutral_TmBind]. *)
(* Admitted. *)

(* Lemma RedKRed K T: *)
(*   (forall M : Term, *)
(*      Reducible M T -> SN (plug K (TmSingle M))) -> *)
(*   (forall M : Term, *)
(*      Reducible M (TyList T) -> SN (plug K M)). *)
(* Proof. *)
(*  intros. *)
(*  simpl in X0. *)
(*  destruct X0. *)
(*  auto. *)
(* Qed. *)

(* Lemma ReducibleK_induction P K T: *)
(*   ReducibleK Reducible T K -> *)
(*   (forall K' K'', (Krw K' K'') -> P K'' -> P K') -> *)
(*   P K. *)
(* Proof. *)
(*  intros. *)
(*  unfold ReducibleK in X. *)
 
(* Admitted. *)

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
   inversion red as [ | ? Z ? redn_Z | | | | | | | | | | | | ] ; subst.
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
 apply Neutral_Reducible_withdraw; [solve [auto] | solve [eauto] |].
 intros M' redn.

 inversion redn as [N0 M0 V M'_eq| ? ? ? L_redn | | | | | | | | | | | | ].

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
 inversion H3 as [ | | | | | | m n1 n2 H7 | m n | m n | | | | | ]; subst.
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
Admitted.

Hint Resolve ReducibleK_Empty.

Lemma ReducibleK_lose_frame :
  forall T K T' N,
    Ktyping K T' ->
    ReducibleK Reducible (Iterate N K) T -> ReducibleK Reducible K T'.
Proof.
 induction K; simpl; intros.
  eauto.
Admitted.

Lemma ReducibleK_Null:
  forall K T,
    (forall M : Term,
       Reducible M T -> SN (plug K (TmSingle M)))
    -> SN (plug K TmNull).
Proof.
 induction K.
  simpl.
  intros.
  apply reducts_SN.
  intros.
  inversion H.
 intros.
 change (ReducibleK Reducible (Iterate t K) T) in X.
 change (forall T, ReducibleK Reducible K T -> SN (plug K TmNull)) in IHK.
 assert ({T' : Ty & Ktyping K T'}).
  admit.
 destruct H as [T' H0].
 assert (ReducibleK Reducible K T').
 solve [eauto using ReducibleK_lose_frame].
 specialize (IHK T' X0).
 simpl.
 assert (forall KZ, Krw_rt K KZ -> SN (plug KZ TmNull)).
 intros.
  admit. (* SN is preserved by Krw_rt. *)

 pattern K.
 apply ReducibleK_induction with T'; auto.
 intros.
 apply reducts_SN.
 intros.
 apply Neutral_Lists in H3.
  destruct H3.
   destruct s as [M' [m'_def rw]].
   inversion rw; subst.
    auto.
   inversion H6.
  destruct s as [K' [m'_def rw]].
  subst.
  apply H2; auto.
 eauto.
Admitted.

Lemma SN_Union: forall M N, SN M -> SN N -> SN (TmUnion M N).
Proof.
 intros.
 apply reducts_SN.
 intros Z H1.
 inversion H1.
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
 (* Case: rw is within K *)
 subst.
 change (SN (plug (Iterate t K') (TmUnion M N))).
 apply H3.
 apply iterate_reduce.
 auto.
Qed.

(* Lemma ReducibleK_peel: *)
(*   forall K N T, *)
(*    ReducibleK Reducible (Iterate N K) T -> *)
(*    ReducibleK Reducible K T. *)
(* Proof. *)
(*  induction K; simpl; intros. *)
(*   auto. *)
(*  unfold ReducibleK in *. *)
(*  simpl in X |- *. *)
(*  intros. *)
(* Admitted. *)

(* Lemma x: *)
(*   forall K T, *)
(*   (forall M : Term, *)
(*      Reducible M T -> *)
(*      SN (plug K (TmSingle M))) -> *)
(*   forall M N, *)
(*     Reducible M (TyList T) -> *)
(*     Reducible N (TyList T) -> *)
(*     SN (plug K (TmUnion M N)). *)
(* Proof. *)
(*  induction K; simpl; intros. *)
(*   intuition. *)
(*   apply SN_Union. *)
(*    apply (b Empty); auto. *)
(*   apply (b0 Empty); auto. *)
(*  apply reducts_SN. *)
(*  intros. *)
(*  apply Neutral_Lists in H; [ | sauto]. *)
(*  destruct H as [[M' [m'_def rw]] | [K' [m'_def rw]]]. *)
(*   subst. *)
(*   inversion rw. *)
(*    subst. *)
   
(* Qed. *)

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

Lemma twostep:
  forall L N,
    SN L -> SN N ->
    SN (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))
    -> SN (TmBind (TmSingle L) N).
Proof.
 intros.
 double_induction_SN L N.
 intros.
 apply reducts_SN.
 intros.
 inversion H6; subst.
  apply reducts_SN.
  intros.
  inversion H7; subst.
    assert (SN (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) x))).
     eapply Rw_trans_preserves_SN with (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)).
      auto.
     admit. (* rw_rt under unshift. *)
    eapply Rw_trans_preserves_SN with (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) x)).
     auto.
    admit. (* rw_rt under unshift. *)
   admit. (* Might be easier to prove the twostep in two steps. *)
  admit.
 admit.
Admitted.

Lemma substitution_preserves_rw:
  forall L M M',
    (M ~> M') ->
    unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) M) ~>
    unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) M').
Proof.
 intros.
 induction M.
          inversion H.
         inversion H.
        inversion H.
         subst.
         rename M1 into M1_0, m2 into M1_1.
Admitted.

Lemma bind_sn_withdraw:
  forall K T S L N,
    ReducibleK Reducible K T ->
    Reducible L S ->
    SN (plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))) ->
    SN (plug K (TmBind (TmSingle L) N)).
Proof.
 induction K.
 simpl; intros.
  apply twostep.
    eauto using Reducible_SN.
   apply SN_embedding with (f := fun x => unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) x))
                             (Q := unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)).
     apply substitution_preserves_rw.
    auto.
   auto.
  auto.
 intros.
 apply triple_induction with (K:=Iterate t K) (M := TmSingle L) (N:=N).
   intros.
   apply reducts_SN.
   intros.
   apply Neutral_Lists in H5.
    destruct H5 as [[M' [eq red]] | [K' [eq red]]].
     inversion red.
      subst.
      admit (* easy: show that K[TmAbs N @ L] is sn because K[N{L}] is. *).
     subst.
     apply H3; auto.
    subst.
    apply H2; auto.
   auto.
  unfold ReducibleK in X.
  admit. (* Maybe this isn't right: it's a goofy precondition of our induction principle, triple_induction. Might need a different induction principle for this. *)
 admit. (* Maybe this isn't right: it's a goofy precondition of our induction principle, triple_induction. Might need a different induction principle for this. *)
Admitted.

Lemma bind_sn_withdraw_alt:
  forall K L N,
    SN L ->
    SN (plug K (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))) ->
    SN (plug K (TmBind (TmSingle L) N)).
Proof.
 induction K.
  simpl; intros.
  apply twostep.
    auto.
   apply SN_embedding with (f := fun x => unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) x))
                             (Q := unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)).
     apply substitution_preserves_rw.
    auto.
   auto.
  auto.
 intros.
 apply triple_induction with (K:=Iterate t K) (M := TmSingle L) (N:=N).
   intros.
   apply reducts_SN.
   intros.
   apply Neutral_Lists in H6.
    destruct H6 as [[M' [eq red]] | [K' [eq red]]].
     inversion red.
      subst.
      admit (* easy: show that K[TmAbs N @ L] is sn because K[N{L}] is. *).
     subst.
     apply H4; auto.
    subst.
    apply H3; auto.
   auto.
  admit. (* Maybe this isn't right: it's a goofy precondition of our induction principle, triple_induction. Might need a different induction principle for this. *)
 admit. (* Maybe this isn't right: it's a goofy precondition of our induction principle, triple_induction. Might need a different induction principle for this. *)
Admitted.

(** Beta reduction preserves types, specialized to reduce at the head
    of the environment. *)
Lemma Rw_beta_preserves_types_conv:
  forall S env' N T M,
   Typing env' M S ->
   Typing env' (unshift 0 1 (subst_env 0 (shift 0 1 M :: nil) N)) T ->
   Typing (S::env') N T.
Proof.
Admitted.
(* TODO: put this in Rewrites, state it as a <-> ? *)

Lemma Bind_Reducible :
  forall M S N T,
    Reducible M (TyList S)
    -> (forall L, Reducible L S
                  -> Reducible (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N))
                               (TyList T))
    -> Reducible (TmBind M N) (TyList T).
Proof.
 simpl.
 intros.
 intuition.
 apply TBind with S; auto.
  destruct (Reducible_inhabited S) as [x r].
  pose (p := X0 x r).
  destruct p.
  eapply Rw_beta_preserves_types_conv; seauto.
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
  forall n k Vs Ts,
    env_typing Vs Ts
    -> Vs = map (shift n k) Vs.
Proof.
 induction Vs; simpl; intros.
  auto.
 destruct Ts.
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
  rewrite <- IHVs with (Ts := Ts).
   auto.
  auto.
 solve [erewrite shift_closed_noop; eauto].
Qed.

Lemma closing_subst_closes:
  forall Vs Ts M T,
    env_typing Vs Ts ->
    Typing Ts M T ->
    Typing nil (subst_env 0 Vs M) T.
Proof.
 induction M; simpl; intros; inversion H0; subst.
           apply TBase.
          admit.
         apply TPair; sauto.
        eapply TProj1; seauto.
       eapply TProj2; seauto.
      eapply TAbs.
      admit.
     eapply TApp; seauto.
    apply TNull.
   apply TSingle; sauto.
  apply TUnion; sauto.
 eapply TBind.
  admit.
 admit.
Admitted.

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
               eapply Reducible_env_value; eauto.
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
       simpl.
       intuition.

      (* Obligation: TmAbs (subst_env 1 Vs m)) = (subst_env 0 Vs (TmAbs m)). *)
      simpl.
      erewrite env_typing_shift_noop; eauto.

 (* Case TmApp *)
     subst.
     assert (Reducible (subst_env 0 Vs m1) (TyArr a T)) by eauto.
     assert (Reducible (subst_env 0 Vs m2) a) by eauto.
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
  assert (Reducible (subst_env 0 Vs m2) (TyList t)) by eauto.
  assert (Reducible (subst_env 0 Vs m1) (TyList t)) by eauto.
  apply ReducibleK_Union; sauto.

 (* Case TmBind *)
 subst.
 apply Bind_Reducible with s.
  seauto.
 intros.
 pose (Reducible_welltyped_closed _ _ X).
 replace (shift 0 1 L) with L.
  replace (map (shift 0 1) Vs) with Vs.
   rewrite subst_env_concat with (env := s :: tyEnv).
    unfold app.
    replace (unshift 0 1 (subst_env 0 (L :: Vs) m2))
       with (subst_env 0 (L :: Vs) m2).
     eapply IHm2; eauto.
     simpl.
     auto.
    assert (Typing nil (subst_env 0 (L :: Vs) m2) (TyList t)).
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
