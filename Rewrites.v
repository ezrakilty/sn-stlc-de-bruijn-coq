Require Import Arith.
Require Import List.

Add LoadPath "Listkit" as Listkit.

Require Import Listkit.NthError.

Require Import Term.
Require Import Shift.
Require Import Subst.
Require Import Omega.

Lemma beta_reduct_typing_general_var:
  forall S env' x T M env k,
   k = length env ->
   Typing env' M S ->
   Typing (env++(S::env')) (TmVar x) T ->
      Typing (env++env')
             (unshift k 1 (subst_env k (shift 0 (k+1) M :: nil) (TmVar x)))
	     T.
Proof.
 intros S env' x.
 intros T M env k k_def M_tp N_tp; simpl; inversion N_tp; eauto.
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
Qed.

(** Beta reduction preserves types:
      [E      |- N{M/k} : T] when
      [E, x:S |- N : T] and
      [E      |- M : S]
*)
Lemma beta_reduct_typing_general:
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
   eapply beta_reduct_typing_general_var; seauto.

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
(* TmBind *)
 apply TBind with s.
  apply IHN1; sauto.
 (* copy and paste of TmAbs case :-( *)
 replace (s::env++env') with ((s::env)++env') by auto.
 replace (shift 0 1 (shift 0 (k+1) M)) with (shift 0 (Datatypes.S k+1) M)
   by (rewrite shift_shift; auto).
 apply IHN2; simpl; auto.
Qed.

(** Let's make [N */ L] a notation for the result of a beta-reduction
    (including all the de Bruijn monkeying). Makes the lemmas a lot easier to read.
    Precedence is not correct. *)
Notation "N */ L" := (unshift 0 1 (subst_env 0 (shift 0 1 L :: nil) N)) (at level 99).

(** Beta reduction preserves types, specialized to reduce at the head
    of the environment. *)
Lemma beta_reduct_typing:
  forall S env' N T M,
   Typing env' M S ->
   Typing (S::env') N T ->
      Typing env' (N */ M) T.
Proof.
 intros.
 replace env' with (nil++env'); auto.
 eapply beta_reduct_typing_general; eauto.
Qed.

(** The rewrite system. The object of our study. *)
Inductive RewritesTo : Term -> Term -> Type :=
| Rw_beta : forall N M V,
    V = (N */ M) ->
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
| Rw_Union_left : forall M N M',
    RewritesTo M M' ->
    RewritesTo (TmUnion M N) (TmUnion M' N)
| Rw_Union_right : forall M N N',
    RewritesTo N N' ->
    RewritesTo (TmUnion M N) (TmUnion M N')
| Rw_Bind_null : forall n,
    RewritesTo (TmBind (TmNull) n) TmNull
| Rw_Bind_beta : forall n x V,
    V = (n */ x) -> RewritesTo (TmBind (TmSingle x) n) V
| Rw_Bind_union : forall n xs ys,
    RewritesTo (TmBind (TmUnion xs ys) n) (TmUnion (TmBind xs n) (TmBind ys n))
| Rw_Bind_subject : forall m n m',
    RewritesTo m m' -> RewritesTo (TmBind m n) (TmBind m' n)
| Rw_Bind_assoc : forall l m n,
    RewritesTo (TmBind (TmBind l m) n) (TmBind l (TmBind m (shift 1 1 n)))
| Rw_Bind_body : forall m n n',
                   RewritesTo n n' -> RewritesTo (TmBind m n) (TmBind m n')
| Rw_Single : forall m m',
                RewritesTo m m' -> RewritesTo (TmSingle m) (TmSingle m')
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

(** The rewrite relation preserves the [Typing] judgment. *)
Lemma Rw_preserves_types:
  forall M M',
    (M ~> M') -> forall env T,
    Typing env M T -> Typing env M' T.
Proof.
 intros M M' red.
 induction red;
    intros env T T_tp;
    inversion T_tp as
        [| | | ? ? S T' TmAbs_N_tp | | ? ? ? H | ? ? ? H | ? ? H | | |? ? ? ? H H0];
    eauto.
 (* Case Beta_reduction -> *)
     inversion TmAbs_N_tp.
     subst.
     eapply beta_reduct_typing; eauto.
 (* Case Beta reduction TPair (1) *)
     subst T.
     inversion H; sauto.
 (* Case Beta reduction TPair (2) *)
    subst T.
    inversion H; sauto.
 (* Case Beta reduction [] *)
   subst T n0 m.
   inversion H.
   subst.
   eauto using beta_reduct_typing.
 (* Case TmUnion/TmBind *)
  inversion H.
  subst.
  apply TUnion; eapply TBind; eauto.
 (* Case TmBind_assoc *)
 inversion H.
 subst.
 eapply TBind; eauto.
 eapply TBind with (s := s); eauto. 
 replace (s :: s0 :: env) with ((s::nil) ++ (s0::nil) ++ env) by auto.
 eapply shift_preserves_typing; eauto.
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

Lemma commute_subst_with_beta_reduct:
  forall N M n env,
    subst_env n env (N */ M) =
    (subst_env (S n) (map (shift 0 1) env) N */ subst_env n env M).
Proof.
 intros.
 (* Now we only have to show that certain complex substitutions are equal.

    The situation at this point can be summarized as:

      (1) -----------> (2) -----------> (4)
         subst 0 {M''}      unshift 0 1
       ^                                 ^
       |                                 |
       | subst n+1 env'                  | subst n env
       |                                 |

       N ----------->  (3) ----------->  N */ M
         subst 0 {M'}      unshift 0 1

       where
           env' = map shift01 env
           M'   = shift01 M
           M''  = shift01 (subst n env M)
 *)

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
   pose (shift_freevars_range X 0).
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
 (* TODO: From here out, basically just set math, plus shift_freevars_range *)
 eapply all_Type_incl.
  apply H.
 apply all_Type_union_fwd.
 split.
  subst fvs_M.
  pose (shift_freevars_range M 0). (* only need another step because all /= all_Type. *)
  firstorder.
 apply all_Type_filter.
 apply outside_range_elim.
Qed.

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
                  | M N
                  |
                  |
                  | N
                  | M N
                  | M N
                  | M N
                  | L M N
                  | M N
                  | M];
   intros n env.

 (* Case BetaRed *)
         (* Write out the beta reduction: *)
         simpl.
         apply Rw_beta.
         subst V.
         apply commute_subst_with_beta_reduct.

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

 (* Case: Union left *)
 simpl.
 apply Rw_Union_left.
 apply IHRewritesTo.

 (* Case: Union right *)
 simpl.
 apply Rw_Union_right.
 apply IHRewritesTo.

 (* Case: Bind with subject null *)
 simpl.
 solve [apply Rw_Bind_null].

 (* Case: Beta reduction of TmBind *)
 simpl.
 apply Rw_Bind_beta; subst.
 apply commute_subst_with_beta_reduct.

 (* Case: Union/Bind commuting-conversion *)
 simpl.
 apply Rw_Bind_union.

 (* Case: Subject reduction of TmBind *)
 simpl.
 apply Rw_Bind_subject.
 eauto.

 (* Case: TmBind Associativity *)
 simpl.
 replace (TmBind (subst_env n env L)
                 (TmBind (subst_env (S n) (map (shift 0 1) env) M)
                         (subst_env (S (S n)) (map (shift 0 1) (map (shift 0 1) env)) (shift 1 1 N))))
   with
     (TmBind (subst_env n env L)
             (TmBind (subst_env (S n) (map (shift 0 1) env) M)
                     (shift 1 1 (subst_env (S n) (map (shift 0 1) env) N)))).
 { auto. }
 rewrite shift_subst_commute_lo by omega.
 simpl.
 replace (n + 1) with (S n) by omega.
 rewrite map_map.
 rewrite map_map.
 f_equal.
 f_equal.
 f_equal.
 apply map_ext.
 intros.
 rewrite shift_shift' by omega.
 rewrite shift_shift' by omega.
 simpl.
 auto.

(* Case: Body reduction of TmBind *)
 simpl.
 apply Rw_Bind_body.
 eauto.

 (* Case: Singleton list contents *)
 simpl.
 apply Rw_Single.
 eauto.
Qed.

Lemma TmSingle_shift_inversion:
  forall x k M,
    TmSingle x = shift k 1 M -> {M' : Term & TmSingle M' = M}.
Proof.
 intros.
 destruct M; simpl in *; try discriminate.
 exists M; auto.
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

Lemma commute_shift_beta_reduct :
  forall k N1 N2,
    (shift (S k) 1 N1 */ shift k 1 N2) = shift k 1 (N1 */ N2).
Proof.
 intros.
 rewrite shift_unshift_commute; [ | | solve[omega]].
 { rewrite shift_subst_commute_hi by (simpl; omega).
   simpl.
   rewrite shift_shift_commute by omega.
   easy. }
 rewrite subst_Freevars by auto.
 intro H0.
 apply set_union_elim in H0.
 destruct H0.
 - apply shift_freevars_range in H; intuition.
 - apply set_filter_elim in H; intuition.
Qed.

(** If [shift k 1 N] reduces, then that reduct is equal to the
    [shift k 1] of some term which is a reduct of [N]. *)
Lemma shift_Rw_inversion:
  forall N M k,
    (shift k 1 N ~> M) ->
    {N' : Term & ((M = shift k 1 N') * (N ~> N')) %type}.
Proof.
(*
    N - - - -> N'
    |          :
    | f        : f = shift k 1
    |          :
    V          V
   f N ------> M
          R
 *)
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
    seauto.
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
  destruct N'_def as [N'_def N_red_N'].
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
   apply commute_shift_beta_reduct.

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

 (* Case TmNull *)
 inversion red.

 (* Case TmSingle *)
 inversion red.

 subst.
 destruct (IHN m' k); auto.
 exists (TmSingle x).
 simpl.
 intuition.
 subst.
 sauto.

 (* Case: TmUnion *)
  inversion red.
  destruct (IHN1 M' k) as [x [e r]]; [sauto | ].
  subst; simpl.
  exists (TmUnion x N2).
  simpl.
  subst.
  seauto.
 destruct (IHN2 N' k) as [x [? ?]]; [auto | ].
 exists (TmUnion N1 x).
 simpl.
 subst.
 seauto.

 (* Case TmBind *)
 inversion red.

 (* Case: Null for Bind *)
 subst.
 assert (N1 = TmNull).
 destruct N1; simpl in *; try discriminate.
 auto.
 subst N1.
 exists TmNull.
 solve [intuition].

 (* Case: Beta for Bind *)
 subst.
 destruct (TmSingle_shift_inversion x _ _ H).
 subst N1.
 exists (N2 */ x0).
 simpl in H.
 inversion H.
 subst.
 split; auto.
 apply commute_shift_beta_reduct.

 (* Case: Bind/Union *)
 assert (A : {xs' : Term & {ys' : Term & ((N1 = TmUnion xs' ys') * (xs = shift k 1 xs') * (ys = shift k 1 ys'))%type}}).
 destruct N1; simpl in H0; try discriminate.
 exists N1_1; exists N1_2.
 inversion H0.
 intuition.
 destruct A as [xs' [ys' [[]]]].
 subst N1.
 exists (TmUnion (TmBind xs' N2) (TmBind ys' N2)).
 simpl.
 subst xs ys.
 split; auto.

 (* Case: reduction in subject of TmBind. *)
 destruct (IHN1 m' k) as [x [e r]]; [auto | ].
 exists (TmBind x N2).
 simpl.
 subst m'.
 eauto.

 (* Case: TmBind assoc *)
 subst.
 destruct N1; simpl in H0; try discriminate.
 inversion H0.
 subst.
 exists (TmBind N1_1 (TmBind N1_2 (shift 1 1 N2))).
 simpl.
 split.
 { rewrite <- shift_shift_commute by omega; auto. }
 auto.

(* Case: reduction in body of TmBind. *)
 destruct (IHN2 n' (S k)) as [x [e r]]; [auto | ].
 exists (TmBind N1 x).
 simpl.
 subst n'.
 eauto.
Qed.

(** * Compatibility of rewriting with each of the term forms. *)

Lemma Rw_rt_Pair_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (〈 m1, n 〉) ~>> (〈 m2, n 〉).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Pair_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (〈 m, n1 〉) ~>> (〈 m, n2 〉).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_App_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (m1@n) ~>> (m2@n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_App_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (m@n1) ~>> (m@n2).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Proj:
  forall (b:bool) (M M' : Term), (M ~>> M') -> (TmProj b M) ~>> (TmProj b M').
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Abs:
  forall (M M' : Term), (M ~>> M') -> (TmAbs M) ~>> (TmAbs M').
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Single:
  forall (M M' : Term), (M ~>> M') -> (TmSingle M) ~>> (TmSingle M').
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Union_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (TmUnion m1 n) ~>> (TmUnion m2 n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Union_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (TmUnion m n1) ~>> (TmUnion m n2).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Bind_left:
  forall m1 m2 n : Term, (m1 ~>> m2) -> (TmBind m1 n) ~>> (TmBind m2 n).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Lemma Rw_rt_Bind_right:
  forall m n1 n2 : Term, (n1 ~>> n2) -> (TmBind m n1) ~>> (TmBind m n2).
Proof.
 intros.
 induction H; subst; eauto.
Qed.

Hint Resolve Rw_rt_Pair_left Rw_rt_Pair_right Rw_rt_App_left Rw_rt_App_right
     Rw_rt_Proj Rw_rt_Abs Rw_rt_Single Rw_rt_Union_left Rw_rt_Union_right
     Rw_rt_Bind_left Rw_rt_Bind_right.

(** * [( */ )] and unshift. *)

Lemma beta_with_unshift_var:
  forall x M n n' k,
    n >= n' ->
    unshift n k (unshift n' 1 (subst_env n' (shift 0 1 M :: nil) (TmVar x))) =
    unshift n' 1
            (subst_env n' (shift 0 1 (unshift n k M) :: nil) (unshift (S n) k (TmVar x))).
Proof.
 simpl.
 intros.
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
Qed.

Lemma beta_with_unshift:
  forall N M n n' k,
    n >= n' ->
    unshift n k (unshift n' 1 (subst_env n' (shift 0 1 M :: nil) N)) =
    unshift n' 1
            (subst_env n' (shift 0 1 (unshift n k M) :: nil) (unshift (S n) k N)).
Proof.
 induction N; intros; simpl.
 (* TmConst *)
 - auto.
 (* TmVar *)
 - apply beta_with_unshift_var; auto.
 (* TmPair *)
 - rewrite IHN1, IHN2; auto.
 (* TmProj *)
 - rewrite IHN; auto.
 (* TmAbs *)
 - rewrite IHN by omega.
   rewrite unshift_shift_commute; solve [omega | auto].
 (* TmApp *)
 - rewrite IHN1, IHN2; auto.
 (* TmNull *)
 - trivial.
 (* TmSingle *)
 - rewrite IHN; auto.
 (* TmUnion *)
 - rewrite IHN1, IHN2; auto.
 (* TmBind *)
 - rewrite IHN1, IHN2 by omega.
   rewrite unshift_shift_commute; solve [omega | auto].
Qed.

Lemma unshift_preserves_rw:
  forall M M' n k,
    (M ~> M') ->
    unshift n k M ~>
    unshift n k M'.
Proof.
 induction M; intros; inversion H; subst; simpl; eauto.

 - apply Rw_beta.
   apply beta_with_unshift.
   omega.
 - apply Rw_Bind_beta.
   apply beta_with_unshift.
   omega.
 - rewrite unshift_shift_commute by omega.
   apply Rw_Bind_assoc.
Qed.

Lemma shift_preserves_rw:
  forall L L' n,
    (L ~> L') ->
    shift n 1 L ~> shift n 1 L'.
Proof.
 induction L; intros; inversion H; subst; simpl; eauto.
 - apply Rw_beta.
   rewrite commute_shift_beta_reduct; auto.
 - apply Rw_Bind_beta.
   rewrite commute_shift_beta_reduct; auto.
 - rewrite shift_shift_commute by omega.
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

(* TODO: Need a better place for the below stuff, which is interactions btwn
shift/subst and rewriting. *)
Lemma Rw_rt_shift:
  forall L L', (L ~>> L') -> shift 0 1 L ~>> shift 0 1 L'.
Proof.
 intros.
 induction H; subst; eauto.
 auto using Rw_rt_step, shift_preserves_rw.
Qed.

Lemma subst_env_compat_rw_rt_var:
  forall x, forall L L' : Term,
    (L ~>> L') ->
    forall n : nat, subst_env n (L :: nil) (TmVar x) ~>> subst_env n (L' :: nil) (TmVar x).
Proof.
 simpl; intros.
 break; auto.
 destruct (x - n).
 - auto.
 - unfold nth_error; auto.
Qed.

Lemma subst_env_compat_rw_rt_A
: forall M L L' : Term,
    (L ~>> L') ->
    forall n : nat, subst_env n (L :: nil) M ~>> subst_env n (L' :: nil) M.
Proof.
 induction M; subst;
   try (apply subst_env_compat_rw_rt_var);
   simpl; eauto; intros.
 - eapply Rw_rt_trans; eauto.
 - eauto using Rw_rt_Abs, IHM, Rw_rt_shift.
 - eapply Rw_rt_trans; eauto.
 - eapply Rw_rt_trans; eauto.
 - eapply Rw_rt_trans; eauto using IHM2, Rw_rt_shift.
Qed.

Lemma subst_env_compat_rw_rt_B
: forall L M M' : Term,
    (M ~>> M') ->
    forall n : nat, subst_env n (L :: nil) M ~>> subst_env n (L :: nil) M'.
Proof.
 intros.
 induction H; subst; eauto using subst_env_compat_rw.
Qed.

Lemma subst_env_bicompat_rw_rt
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

(** * Rewrites Inside Structures That Look Like A Beta-Reduct. *)

Lemma unshift_substitution_preserves_rw:
  forall M M' L,
    (M ~> M') ->
    M */ L ~> M' */ L.
Proof.
 intros.
 apply unshift_preserves_rw.
 apply subst_env_compat_rw.
 auto.
Qed.

Lemma unshift_substitution_preserves_rw_rt:
  forall M M' L : Term,
  (M ~>> M') ->
  M */ L ~>>  M' */ L.
Proof.
  intros.
  induction H.
  * constructor 1.
    subst; auto.
  * constructor 2.
    apply unshift_substitution_preserves_rw; auto.
  * econstructor 3; eauto.
Qed.

Lemma unshift_substitution_doubly_preserves_rw_rt:
  forall M M' L L' : Term,
  (L ~>> L') ->
  (M ~>> M') ->
  M */ L ~>>
    M' */ L'.
Proof.
 intros.
 apply unshift_preserves_rw_rt. (* Should be rw_compat_unshift *)
 apply subst_env_bicompat_rw_rt; auto.
 apply Rw_rt_shift; auto.
Qed.
