Require Import Arith.
Require Import List.

Add LoadPath "Listkit" as Listkit.

Require Import NthError.

Require Import Term.
Require Import Shift.
Require Import Subst.

Inductive RewritesTo : Term -> Term -> Type :=
| Rw_beta : forall N M V,
    V = unshift 0 1 (subst_env 0 (shift 0 1 M :: nil) N) ->
    RewritesTo (TmApp (TmAbs N) M) V
| Rw_App_left : forall m1 m2 n,
    RewritesTo m1 m2 ->
    RewritesTo (TmApp m1 n) (TmApp m2 n)
| Rw_App_right : forall m n1 n2,
    RewritesTo n1 n2 ->
    RewritesTo (TmApp m n1) (TmApp m n2)
| Rw_Abs_body : forall n n',
    RewritesTo n n' ->
    RewritesTo (TmAbs n) (TmAbs n')
| Rw_Pair_left : forall m1 m2 n,
    RewritesTo m1 m2 ->
    RewritesTo (TmPair m1 n) (TmPair m2 n)
| Rw_Pair_right : forall m n1 n2,
    RewritesTo n1 n2 ->
    RewritesTo (TmPair m n1) (TmPair m n2)
| Rw_Proj : forall m1 m2 b,
    RewritesTo m1 m2 ->
    RewritesTo (TmProj b m1) (TmProj b m2)
| Rw_Proj_beta1 : forall m n,
    RewritesTo (TmProj false (TmPair m n)) m
| Rw_Proj_beta2 : forall m n,
    RewritesTo (TmProj true (TmPair m n)) n
.

Hint Constructors RewritesTo.

Notation "M ~> M'" := (RewritesTo M M') (at level 100).

(** Reflexive, transitive closure of RewritesTo *)
Inductive RewritesTo_rt : Term -> Term -> Type :=
| Rw_rt_refl : forall m n, m = n -> RewritesTo_rt m n
| Rw_rt_step : forall m n, RewritesTo m n -> RewritesTo_rt m n
| Rw_rt_trans : forall l m n, RewritesTo_rt l m -> RewritesTo_rt m n
                -> RewritesTo_rt l n.

Notation "M ~>> M'" := (RewritesTo_rt M M') (at level 100).

Hint Constructors RewritesTo_rt.

(** Recognizes an empty reduction sequence. *)
Fixpoint Is_empty_Rw_rt (a z : Term) (redn : a ~>> z) :=
  match redn with
    | Rw_rt_refl _ _ _ => True
    | Rw_rt_step _ _ _ => False
    | Rw_rt_trans a b z r1 r2 =>
      Is_empty_Rw_rt a b r1 /\ Is_empty_Rw_rt b z r2
  end.

(** When we know a reduction sequence "is empty," we know its start
    and end terms are equal. *)
Lemma empty_Rw_rt_elim:
  forall l m redn,
    Is_empty_Rw_rt l m redn -> l = m.
Proof.
 intros l m redn H. induction redn.
   auto.
  simpl in H.
  contradiction.
 simpl in H.
 intuition.
 congruence.
Qed.

(** A transitive reduction sequence is either empty or decomposable
    into a first step and the remainder. *)
Lemma Rw_rt_destruct:
  forall a z,
    forall redn: a ~>> z,
      sum (Is_empty_Rw_rt a z redn) ({x : Term & ((a ~> x) * (x ~>> z))%type}).
(* TODO: A bit ugly! *)
Proof.
 intros.
 induction redn.
   left.
   simpl.
   auto.
  right.
  exists n; auto.
 destruct (IHredn1);
   destruct (IHredn2).
    left; simpl; auto.
   assert (l = m) by (eapply empty_Rw_rt_elim; eauto).
   subst. right; auto.
  assert (m = n) by (eapply empty_Rw_rt_elim; eauto).
  subst. right; auto.
 destruct s as [x [l_x x__m]].
 right; exists x.
 destruct s0 as [y [m_y y__n]].
 split; eauto.
Qed.

(** Any reduction sequence with a last step also has a first step,
    which we can construct. *)
Lemma last_step_first_step_lemma:
  forall a y,
  (a ~>> y) -> forall z, (y ~> z) -> {x : Term & ((a ~> x) * (x ~>> z))%type}.
Proof.
 intros a y H_a_downto_y.
 intros.
 pose (redn := Rw_rt_trans a y z H_a_downto_y (Rw_rt_step _ _ H)).
 destruct (Rw_rt_destruct a z redn).
  subst redn.
  simpl in *.
  intuition.
 auto.
Qed.


(** Beta reduction preserves types:
      [E      |- N{M/k} : T] when
      [E, x:S |- N : T] and
      [E      |- M : S]
*)
Lemma Rw_beta_preserves_types_general:
  forall S env' N T M env k,
   k = length env ->
   Typing env' M S ->
   Typing (env++(S::env')) N T ->
      Typing (env++env')
             (unshift k 1 (subst_env k (shift 0 (k+1) M :: nil) N))
	     T.
Proof.
 induction N; intros T M env k k_def M_tp N_tp; simpl; inversion N_tp; eauto.
(* TmConst--handled by eauto *)
(* TmVar *)
    subst.
    assert (H: x < length (env++(S::env'))).
     eapply nth_error_to_length; eauto.
    rewrite app_length in H.
    simpl in H.
    destruct (le_gt_dec (length env) x).
     destruct (eq_nat_dec x (length env)).
     (* 'x' points to the type 'S' *)
      subst x.
      replace (length env - length env) with 0 by omega.
      replace (nth_error (shift 0 1 M :: nil) 0)
        with (value (shift 0 1 M)); auto.
      simpl.
      rewrite fancy_unshift_shift; auto; [|omega].
      replace (length env+1-1) with (length env); auto; [|omega].
      replace (env++env') with (nil++env++env'); auto.
      eapply shift_preserves_typing with env'; auto.
      apply nth_error_app in H0; auto.
      replace (length env - length env) with 0 in H0 by omega.
      simpl in H0.
      inversion H0.
      auto.
     (* 'x' is in the second environment. *)
     assert (length env < x) by omega.
     assert (0 < x-length env) by omega.
     replace (nth_error (shift 0 (length env + 1) M::nil) (x-length env))
       with (error : option Term).
      simpl.
      apply TVar.
      unfold unshift_var.
      destruct (le_gt_dec (1 + length env) x); [ | omega].
      apply nth_error_app in H0; auto.
      replace (S::env') with ((S::nil)++env') in H0; auto.
      apply nth_error_app in H0; auto.
      simpl in H0.
      rewrite rewrite_nth_error_app.
       replace (x - 1 - length env) with (x - length env - 1) by omega.
       auto.
      omega.

     (* Prove that nth_error (_::nil) z = error when z > 0. *)
     symmetry; apply nth_error_overflow.
     simpl.
     omega.

    (* x is in the first environment *)
    apply TVar.
    replace (unshift_var (length env) 1 x) with x.
     rewrite <- nth_error_ext_length; auto.
     rewrite <- nth_error_ext_length in H0; auto.
    rewrite unshift_var_lo; auto.

(* TmPair *)
 (* handled by eauto *)

(* TmProj *)
 (* handled by eauto *)

(* TmAbs *)
 apply TAbs.
 replace (s::env++env') with ((s::env)++env') by auto.
 replace (shift 0 1 (shift 0 (k+1) M)) with (shift 0 (Datatypes.S k+1) M)
   by (rewrite shift_shift; auto).
 apply IHN; simpl; auto.

(* TmApp *)
  (* handled by [eauto] at the top. *)
Qed.

(** Beta reduction preserves types, specialized to reduce at the head
    of the environment. *)
Lemma Rw_beta_preserves_types:
  forall S env' N T M,
   Typing env' M S ->
   Typing (S::env') N T ->
      Typing env' (unshift 0 1 (subst_env 0 (shift 0 1 M :: nil) N)) T.
Proof.
 intros.
 replace env' with (nil++env'); auto.
 eapply Rw_beta_preserves_types_general; eauto.
Qed.

(** The rewrite relation preserves the [Typing] judgment. *)
Lemma Rw_preserves_types:
  forall M M',
    (M ~> M') -> forall env T,
    Typing env M T -> Typing env M' T.
Proof.
 intros M M' red.
 induction red;
   intros env T T_tp;
   inversion T_tp as [| | | ? ? S T' TmAbs_N_tp | | |]; eauto.
 (* Case Beta_reduction -> *)
    inversion TmAbs_N_tp.
    subst.
    eapply Rw_beta_preserves_types; eauto.
 (* Case Beta reduction TPair (1) *)
  subst T.
  inversion H0; auto.
 (* Case Beta reduction TPair (2) *)
 subst T.
 inversion H0; auto.
Qed.

(** The reflexive-transitive rewrite relation preserves the [Typing] judgment. *)
Lemma Rw_rt_preserves_types:
  forall env M M' T,
    Typing env M T -> (M ~>> M') -> Typing env M' T.
Proof.
 intros env M M' T M_tp M_red_M'.
 induction M_red_M'; eauto using Rw_preserves_types; try congruence.
Qed.

Hint Resolve Rw_rt_preserves_types.

Require Import Listkit.All.
Require Import Listkit.AllType.
Require Import Listkit.Sets.
Require Import OutsideRange.

Lemma subst_env_compat_rw:
  forall M M',
    (M ~> M') ->
    forall n env,
      (subst_env n env M ~> subst_env n env M').
Proof.
 intros M M' H.
 induction H as [ | M1 M2 N
                  | M N1 N2
                  | N N'
                  | M1 M2 N
                  | M N1 N2
                  | M1 M2 b
                  | M N
                  | M N ];
   intros n env.

 (* Case BetaRed *)
         (* Write out the beta reduction: *)
         simpl.
         apply Rw_beta.
         (* Now we only have to show that certain complex substitutions are equal.

            The situation at this point can be summarized as:

              (1) -----------> (2) -----------> (4)
                 subst 0 {M''}      unshift 0 1
               ^                                 ^
               |                                 |
               | subst n+1 env'                  | subst n env
               |                                 |

               N ----------->  (3) ----------->  V
                 subst 0 {M'}      unshift 0 1

               where
                   env' = map shift01 env
                   M'   = shift01 M
                   M''  = shift01 (subst n env M)
         *)

         subst V.

         (* Push subst_env inside unshift. *)
         rewrite subst_unshift (*if this used outside_range, how would it be different? *);
           [ | omega | ].
          f_equal.

          (* From here on we're just working with the left-hand square of the above diagram,

              (1) -----------> (2)
                 subst 0 {M''}
               ^                ^
               |                |
               | subst n+1 env' | subst n+1 env'
               |                |

               N ------------> (3)
                 subst 0 {M'}

           *)

          replace (n+1) with (S n) by omega.

          remember (shift 0 1 M) as M'.
          remember (shift 0 1 (subst_env n env M)) as M''.
          remember (map (shift 0 1) env) as env'.

          (* Push shift inside subst_env in M''. *)
          rewrite shift_subst_commute_lo in HeqM'' by omega.
          replace (n+1) with (S n) in HeqM'' by omega.

          (* We have reduced the problem to subst_factor and some obligations. *)
          rewrite <- subst_factor. (* with m:= 0, n:= S n *)
            subst; sauto.

          (* Obligations of subst_factor: *)
          (* Obl 1: All freevars of every term in [map (shift 0 1) env] are not in
             the env_domain of _::nil, i.e. the interval [0,1). *)
           unfold in_env_domain.
           simpl.
           subst env'.
           apply all_map_image.
           intros X.
           pose (shift_freevars X 0).
           firstorder.
          (* Obl 2: Substitutions do not overlap:
               (0, [_]) does not overlap (S n, _). *)
          simpl.
          solve [omega].

         (* Obligations of subst_unshift: *)
         (* Obl 1: That fvs of N{[shift 0 1 M]/0} are all outside [0,1). *)
            (* TODO some redundancy with the above obl 1 *)
         pose (fvs_M := freevars (shift 0 1 M)).
         pose (fvs_N := freevars N).
         remember (freevars (subst_env 0 (shift 0 1 M :: nil) N)) as fvs.
         (* Assert: fvs ⊆ (fvs_N ∖ {0}) ∪ fvs_M *)
         assert (H : incl_sets _
                         fvs
                         (set_union eq_nat_dec
                           fvs_M
                           (set_filter _
                                (fun x => outside_range 0 (1+0) x) fvs_N))).
          subst fvs fvs_M fvs_N.
          replace (freevars (shift 0 1 M))
             with (set_unions _ eq_nat_dec (map freevars (shift 0 1 M :: nil)))
               by auto.
          apply subst_Freevars; sauto.

         (* Now we have H : fvs ⊆ (fvs_N ∖ {0}) ∪ fvs_M *)
         (* TODO: From here out, basically just set math, plus shift_freevars *)
         eapply all_Type_incl.
          apply H.
         apply all_Type_union_fwd.
         split.
          subst fvs_M.
          pose (shift_freevars M 0). (* only need another step because all /= all_Type. *)
          firstorder.
         apply all_Type_filter.
         apply outside_range_elim.

 (* Case Reduction in lhs of apply *)
        simpl.
        apply Rw_App_left.
        apply IHRewritesTo.

 (* Case Reduction in rhs of apply *)
       simpl.
       apply Rw_App_right.
       apply IHRewritesTo.

 (* Case Reduction in Abs body. *)
      simpl.
      apply Rw_Abs_body.  (* TODO: Can we somehow set up a congruence to obviate this step? *)
      apply IHRewritesTo.

 (* Case: Reduction in left side of pair *)
     simpl.
     apply Rw_Pair_left.
     eauto.

 (* Case: Reduction in right side of pair *)
    simpl.
    apply Rw_Pair_right.
    eauto.

 (* Case: Reduction under a TmProj *)
   simpl.
   apply Rw_Proj.    (* eauto works fine! *)
   eauto.

 (* Case: Beta reduction of TmProj false *)
  simpl.
  apply Rw_Proj_beta1.

 (* Case: Beta reduction of TmProj false *)
 simpl.
 apply Rw_Proj_beta2.
Qed.

Lemma subst_env_compat_Rw_trans:
  forall M M' n env,
    (M ~>> M') -> (subst_env n env M ~>> subst_env n env M').
Proof.
 intros M M' n env H.
 induction H.
  apply Rw_rt_refl.
   subst m.
   auto.
  apply Rw_rt_step.
  apply subst_env_compat_rw.
  auto.
 apply Rw_rt_trans with (subst_env n env m); auto.
Qed.

Import Setoid.
Require Import Listkit.Foreach.

(** If [shift k 1 N] reduces, then that reduct is equal to the
    [shift k 1] of some term which is a reduct of [N]. *)
Lemma shift_Rw_inversion:
  forall N M k,
    (shift k 1 N ~> M) ->
    {N' : Term & ((M = shift k 1 N') * (N ~> N')) %type}.
Proof.
 induction N; simpl; intros M k red.
 (* Case TmConst *)
      inversion red.
 (* Case TmVar *)
     inversion red.
 (* Case TmPair *)
    inversion red.
     destruct (IHN1 m2 k) as [x [e r]]; [auto | ].
     exists (TmPair x N2).
     simpl.
     subst m2.
     eauto.
    destruct (IHN2 n2 k) as [x [? ?]]; [auto | ].
    exists (TmPair N1 x).
    simpl.
    subst n2.
    eauto.
 (* Case TmProj *)
   inversion red; subst.
     destruct (IHN m2 k) as [N' [? ?]]; [auto|].
     exists (TmProj b N').
     simpl.
     subst m2.
     eauto.
    descrim N (* must be pair *).
    simpl in *.
    exists N1.
    simpl.
    intuition (congruence ||auto).
   descrim N.
   simpl in *.
   exists N2.
   simpl.
   intuition (congruence || auto).

 (* Case TmAbs *)
  inversion red.
  subst.
  destruct (IHN n' (S k) H0) as [N' N'_def].
  exists (TmAbs N').
  destruct (N'_def) as [N'_def N_red_N'].
  simpl.
  subst.
  eauto.

 (* Case TmApp *)
 (* Take cases on the reductions: *)
 inversion red.
 (* Case: Beta reduction. *)
  (* Show that N1 is an abstraction. *)
   destruct N1; simpl in H; unfold shift_var; try discriminate.
   (* Now the old N1 is (TmAbs N1) *)
   simpl in red.
   inversion H.
   subst N.
   exists (unshift 0 1 (subst_env 0 (shift 0 1 N2::nil) N1)).
   subst M.
   subst V.
   split; [ | auto].
   rewrite shift_unshift_commute; [ | | solve[omega]].
    rewrite shift_subst_commute_hi ; [ | simpl; omega].
    simpl.
    rewrite shift_shift_commute; [ | omega].
    solve [trivial]...

   (* Obligation of shift_unshift_commute: that 0 \not\in subst_env 0 [shift 0 1 N2] N1. *)
   clear red H H1 M0 k IHN2 IHN1.
   rewrite subst_Freevars by auto.
   simpl.
   intro H0.
   apply set_union_elim in H0.
   destruct H0.
    apply shift_freevars in H.
    omega.
   apply set_filter_elim in H.
   destruct H.
   unfold outside_range in *.
   revert H0.
   break; try break; intros; (try omega; try discriminate).

 (* Case: reduction in left part of application. *)
  destruct (IHN1 m2 k) as [m2' [m2'_def m2'_red]]; [auto | ].
  exists (m2'@N2).
  simpl.
  subst m2.
  eauto.

 (* Case: reduction in right part of application. *)
 destruct (IHN2 n2 k) as [n2' [n2'_def n2'_red]]; [auto | ].
 exists (N1@n2').
 simpl.
 subst n2.
 eauto.
Qed.
