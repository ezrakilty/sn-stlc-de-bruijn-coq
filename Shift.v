Load "eztactics.v".

Require Import Arith.
Require Import List.

Add Rec LoadPath "Listkit" as Listkit.

Require Import Listkit.NthError.
Require Import Listkit.Foreach.

Require Import Term.

Definition shift_var k n :=
  fun x => if le_gt_dec k x then (x+n) else x.

(** Shifting De Bruijn indexes *)
Fixpoint shift k n tm {struct tm} :=
  match tm with
| TmConst => TmConst
| TmVar x => TmVar (shift_var k n x)
| TmPair L M => TmPair (shift k n L) (shift k n M)
| TmProj b M => TmProj b (shift k n M)
| TmAbs N' => TmAbs (shift (S k) n N')
| TmApp L M => TmApp (shift k n L) (shift k n M)
| TmNull => TmNull
| TmSingle x => TmSingle (shift k n x)
| TmUnion L R => TmUnion (shift k n L) (shift k n R)
| TmBind M N => TmBind (shift k n M) (shift (S k) n N)
  end.

(*
| TmNull => 0
| TmSingle x => 0
| TmUnion l r => 0
 *)

Definition unshift_var k n :=
  fun x => if le_gt_dec (n+k) x then (x-n) else x.

Fixpoint unshift k n tm {struct tm} :=
  match tm with
| TmConst => TmConst
| TmVar x => TmVar (unshift_var k n x)
| TmPair L M => TmPair (unshift k n L) (unshift k n M)
| TmProj b m => TmProj b (unshift k n m)
| TmAbs N => TmAbs (unshift (S k) n N)
| TmApp L M =>TmApp (unshift k n L) (unshift k n M)
| TmNull => TmNull
| TmSingle x => TmSingle (unshift k n x)
| TmUnion l r => TmUnion (unshift k n l) (unshift k n r)
| TmBind M N => TmBind (unshift k n M) (unshift (S k) n N)
end.

Hint Unfold unshift_var shift_var.
Hint Transparent unshift_var shift_var.

Lemma unshift_var_shift_var :
  forall x k n,
    unshift_var k n (shift_var k n x) = x.
Proof.
 intros x k n.
 unfold unshift_var, shift_var.
 break; break; omega.
Qed.

Lemma unshift_shift :
  forall N k n,
    unshift k n (shift k n N) = N.
Proof.
 induction N; intros k n; simpl.
          trivial.
         f_equal.
         apply unshift_var_shift_var.
        f_equal; sauto.
       f_equal; sauto.
      f_equal; sauto.
     f_equal; sauto.
    f_equal; sauto.
   f_equal; sauto.
  f_equal; sauto.
 f_equal; sauto.
Qed.

Lemma unshift_shift_alt : (* Alternate proof of unshift_shift *)
  forall N k n,
    unshift k n (shift k n N) = N.
Proof.
 induction N; intros k n; simpl; f_equal; try sauto.
 apply unshift_var_shift_var.
Qed.


(** (Un)Shifting at De Bruijn index k when k is above the greatest free
    index is a no-op. *)
Lemma shift_nonfree_noop :
  forall n M k env T,
    length env <= k ->
    Typing env M T -> shift k n M = M.
Proof.
 induction M; simpl; intros k env T k_big M_tp; intuition;
   inversion M_tp as [| ? ? T_is_env_x | | | | | | | | |];
     try (f_equal; eauto).
 (* Case TmVar *)
   unfold shift_var.
   break; trivial.
   pose (nth_error_to_length _ _ _ _ T_is_env_x).
   omega.
 (* Case TmAbs *)
  apply IHM with (s :: env) t; simpl; auto; omega.
 (* Case TmBind *)
 apply IHM2 with (s :: env) (TyList t); simpl; auto; omega.
Qed.

Lemma unshift_nonfree_noop :
  forall n M k env T,
    length env <= k ->
    Typing env M T -> unshift k n M = M.
Proof.
 induction M; simpl; intros k env T k_big M_tp; intuition;
   inversion M_tp as [| ? ? T_is_env_x | | | | | | | | |];
     try (f_equal; eauto).
   unfold unshift_var.
   break; trivial.
   absurd (x < length env); efinish.
  eapply IHM with (s :: env) t; auto; simpl; omega.
 eapply IHM2 with (s :: env) (TyList t); auto; simpl; omega.
Qed.

(** (Un)Shifting a closed term is a no-op. *)
Lemma shift_closed_noop :
  forall n M k T,
    Typing nil M T -> shift k n M = M.
Proof.
 intros; eapply shift_nonfree_noop; eauto.
 simpl; apply le_O_n.
Qed.

Lemma unshift_closed_noop :
  forall n M k T,
    Typing nil M T -> unshift k n M = M.
Proof.
 intros; eapply unshift_nonfree_noop; eauto.
 simpl; apply le_O_n.
Qed.

Hint Resolve shift_closed_noop.
Hint Rewrite shift_closed_noop : terms.

Hint Resolve shift_nonfree_noop.
Hint Rewrite shift_nonfree_noop : terms.

Lemma shift_nonfree_preserves_typing :
  forall M T k n env,
    length env <= k ->
    Typing env M T -> Typing env (shift k n M) T.
Proof.
  intros.
  rewrite (shift_nonfree_noop n M k env T); auto.
Qed.

Lemma shift_var_nth_error:
  forall A (x:A) n env2 env1 env',
       value x = nth_error (env1 ++ env2) n
    -> value x = nth_error (env1 ++ env' ++ env2)
                           (shift_var (length env1) (length env') n).
Proof.
 unfold shift_var.
 intros ? x n env2 env1 env' H.
 destruct (le_gt_dec (length env1) n).
  assert (n < length (env1++env2)) by eauto.
  rewrite app_length in H0.
  rewrite nth_error_app_eq; repeat (rewrite app_length); try finish.
  rewrite nth_error_app_eq; repeat (rewrite app_length); try finish.
  replace (n + length env' - length env1 - length env')
     with (n - length env1) by omega.
  sauto.
 rewrite <- nth_error_ext_length; auto.
 rewrite <- nth_error_ext_length in H by auto.
 auto.
Qed.

(** Shift preserves typing. *)
Lemma shift_preserves_typing:
  forall M k n env1 env2 env env' T,
    env1 ++ env2 = env ->
    k = length env1 ->
    n = length env' ->
    Typing env M T -> Typing (env1++env'++env2) (shift k n M) T.
Proof.
 induction M; intros k n env1 env2 env env' T env_split k_def n_def M_tp;
   inversion M_tp as [| ? ? T_is_env_x| | | | | | | | |]; simpl.
 (* TmConst *)
           auto.
 (* TmVar *)
          subst x0 ty env n k.
          apply TVar.
          apply shift_var_nth_error; auto.
 (* TmPair *)
         apply TPair; eauto.
 (* TmProj *)
        eapply TProj1; eauto.
       eapply TProj2; eauto.
 (* TmAbs *)
      subst n0 T env k.
      apply TAbs.
      replace (s :: env1 ++ env' ++ env2)
         with ((s::env1) ++ env' ++ env2) by auto.
      eauto using IHM.
 (* TmApp *)
      eauto.
     auto.
   apply TSingle; eauto.
  apply TUnion; eauto.
 (* TmBind *)
 eapply TBind.
  eapply IHM1; seauto.
 subst env.
 replace (s :: env1 ++ env' ++ env2)
   with ((s::env1) ++ env' ++ env2) by auto.
 eapply IHM2 with (s::env1 ++ env2); auto.
 simpl.
 sauto.
Qed.

(** Shifting a term by just one preserves typing. *)
Lemma shift1_preserves_typing :
  forall M env S T,
    Typing env M T -> Typing (S::env) (shift 0 1 M) T.
Proof.
 intros.
 replace (S::env) with (nil ++ (S::nil) ++ env) by trivial.
 apply shift_preserves_typing with env; auto.
Qed.

Hint Resolve shift1_preserves_typing.

(** For a closed list of terms (as indicated when env_typing applies
to the list), shifting by any amount is a noop. *)
Lemma env_typing_shift_noop :
  forall Vs env,
    env_typing Vs env ->
    forall n k, map (shift n k) Vs = Vs.
Proof.
 induction Vs; simpl; intros env H; auto.
 intros n k.
 inversion H as [len tps].
 destruct env; [refute; simpl in *; omega| ].
 unfold foreach2_ty in tps.
 simpl in tps.
 f_equal.
  inversion tps.
  eapply shift_nonfree_noop; eauto.
  simpl; omega.
 rewrite IHVs with env n k; auto.
 intuition.
Qed.

Hint Resolve env_typing_shift_noop.

Hint Rewrite env_typing_shift_noop : typing.

(** Applying [unshift k _] to a variable _smaller_ than [k] as no effect. *)
Lemma unshift_var_lo :
  forall x k n,
    x < k -> unshift_var k n x = x.
Proof.
 simpl.
 intros x k n H.
 unfold unshift_var.
 destruct (le_gt_dec (n+k) x);
   [solve[omega]|solve[auto]].
Qed.

(** Composing one [shift] with another, at the same [k], can be
    reduced to a single [shift]. *)
Lemma shift_shift:
  forall n n' M k,
    shift k n (shift k n' M) = shift k (n+n') M.
Proof.
 induction M; intros k; simpl; try (solve [f_equal; eauto]).
(* Case TmVar *)
 f_equal.
 unfold shift_var.
 destruct (le_gt_dec k x).
  destruct (le_gt_dec k (x+n')); omega.
 destruct (le_gt_dec k x); omega.
Qed.

(** Composing [unshift] with [shift], given certain conditions (TODO)
    on the indices, produces the effect of a single [shift] *)
Lemma fancy_unshift_shift:
  forall n M k n' j,
    k + n <= j + n' ->
    j <= k ->
    unshift k n (shift j n' M) = shift j (n'-n) M.
Proof.
 induction M; intros k n' j n'_big j_small; simpl; f_equal; try eauto.
 (* Case TmVar *)
  unfold unshift_var, shift_var.
  destruct (le_gt_dec j x).
   break; omega.
  break; omega.
 (* Case TmAbs *)
  apply IHM; omega.
 (* Case TmBind *)
 apply IHM2; omega.
Qed.

Lemma shift_var_shift_var_commute:
  forall x k k' n,
    k' <= k ->
    shift_var (S k) n (shift_var k' 1 x) =
    shift_var k' 1 (shift_var k n x).
Proof.
 intros x k k' n H.
 unfold shift_var at 2 4.
 break; break.
    unfold shift, shift_var.
    break; break; omega.
   unfold shift, shift_var.
   break; break; omega.
  unfold shift, shift_var.
  break; break; omega.
 unfold shift, shift_var.
 break; break; omega.
Qed.

(** "Shifting by one" commutes with "shifting by [k]" for appropriate
   conditions and adjustment of [k]. *)
Lemma shift_shift_commute:
  forall M k k' n,
    k' <= k ->
    shift (S k) n (shift k' 1 M) =
    shift k' 1 (shift k n M).
Proof.
 induction M; intros k k' n H; try (solve [simpl;f_equal;eauto]).
 (* TmVar *)
  unfold shift at 2 4.
  unfold shift.
  f_equal.
  apply shift_var_shift_var_commute; auto.
 (* TmAbs *)
 simpl; f_equal.
 assert (S k' <= S k) by omega.
 eauto.
 simpl; f_equal.
  apply IHM1; auto.
 apply IHM2; auto.
 omega.
Qed.

Require Import Listkit.logickit.

Lemma shift_var_S_pred:
  forall x k n,
    x <> 0 ->
    shift_var (S k) n x - 1 = shift_var k n (x-1).
Proof.
 unfold shift_var.
 intros.
 pose (pred := fun x => x-1).
 replace ((if le_gt_dec (S k) x then x+n else x) - 1)
    with (pred (if le_gt_dec (S k) x then x+n else x)) by auto.
 replace (pred (if le_gt_dec (S k) x then x+n else x))
    with (if le_gt_dec (S k) x then pred (x+n) else pred x).
  unfold pred.
  break; break; omega.
 symmetry; apply if_cc.
Qed.

(** Good lemma; unused. Mis-spelled. *)
Lemma shift_preservs_env_typing:
  forall (Vs : list Term) (k n : nat)
    (env1 env2 env env' : list Ty)
    (Ts : list Ty),
  env1 ++ env2 = env ->
  k = length env1 ->
  n = length env' ->
  env_typing_env env Vs Ts
   -> env_typing_env (env1 ++ env' ++ env2) (map (shift k n) Vs) Ts.
Proof.
 induction Vs; intros k n env1 env2 env env' Ts H H0 H1 X.
(* Case Vs = nil *)
  simpl.
  unfold env_typing_env.
  unfold foreach2_ty.
  inversion X.
  simpl in *.
  auto.

(* Case Vs = _ : _ *)
 simpl.
 replace env with (env1++env2) in *.
 destruct Ts.
  inversion X.
  simpl in H2.
  omega.
 apply env_typing_elim in X.
 destruct X.
 apply env_typing_intro.
  apply shift_preserves_typing with (env := env1++env2); auto.
 apply IHVs with (env:= env1++env2); auto.
Qed.

Require Import Coq.Lists.ListSet.

(* TODO: grumble, why this? *)
Definition set_remove := Listkit.Sets.set_remove.

Require Import Monomorphism.
Require Import Listkit.Map.
Require Import Listkit.Sets.

Import Setoid.

Lemma shift_unshift_commute :
  forall M k k',
    ~ set_In k' (freevars M) ->
    k' <= k ->
    shift k 1 (unshift k' 1 M) = unshift k' 1 (shift (S k) 1 M).
Proof.
 induction M; intros k k' k'_not_free k'_le_k.

 (* Case TmConst *)
         sauto.

 (* Case TmVar *)
        simpl in *.
        unfold not in *.
        intuition.
        unfold shift_var, unshift_var.
        f_equal.
        break; break; break; break; omega.

 (* Case TmPair *)
       simpl.
       simpl in k'_not_free.

       (* TODO: Would be nice to just throw set_union_intro at k'_not_free. *)
       (* I have H: A->B  and a lemma foo_intro: C->A and I want H': C->B*)
       assert (~(set_In k' (freevars M1) \/ set_In k' (freevars M2))) by auto.
       f_equal; eauto.

 (* Case TmProj *)
      simpl.
      f_equal; eauto.

 (* Case TmAbs *)
     simpl in *.
     rewrite IHM; [auto | | ].
      cut (~ set_In (S k') (set_remove _ eq_nat_dec 0 (freevars M))).
       auto.
      remember (set_remove _ eq_nat_dec 0 (freevars M)) as M_fvs_less_0.
      assert (H : ~set_In (S k')
                     (set_map eq_nat_dec S
                        (set_map eq_nat_dec (fun x => x - 1)
                           M_fvs_less_0))).
       subst M_fvs_less_0.
       rewrite <- (map_monomorphism _ _ _ _ S _); auto.
       unfold monomorphism.
       auto.

      rewrite set_map_map in H.
      setoid_replace (set_map eq_nat_dec (fun x => S (x-1)) M_fvs_less_0)
         with (M_fvs_less_0) (* using eq_sets *) in H.
       auto.
      rewrite set_map_extensionality with (g:=idy nat).
       rewrite set_map_idy; auto.
      intros x H0.
      assert (x <> 0).
       subst M_fvs_less_0.
       apply set_remove_elim in H0.
       intuition...
      unfold idy.
      omega...
     omega...

 (* Case TmApp *)
    simpl in *.
    rewrite IHM1; [ | auto | auto].
    rewrite IHM2; [auto | | auto].
    auto.

   simpl in *.
   trivial.

  simpl in *.
  rewrite IHM; auto.

 simpl in *.
 rewrite IHM1; [ | auto | auto].
 rewrite IHM2; [auto | | auto].
 auto.
 (* Case TmBind *)
 simpl in *.
 rewrite IHM1; [ | sauto | sauto].
 rewrite IHM2; [sauto | | omega].
 contrapose k'_not_free.
 rename k'_not_free into S_k'_in_fvs_M2.
 apply set_union_intro2.
 assert (monomorphism _ _ S).
  firstorder.
 rewrite map_monomorphism with (f:=S) by auto.
 rewrite set_map_map.
 apply set_map_idy_ext.
  intros.
  assert (H1 : (x ∈ (Term.set_remove nat eq_nat_dec 0 (freevars M2))))
    by (eauto using set_mem_correct1).
  apply set_remove_elim in H1.
  omega.
 apply set_remove_intro.
 sauto.
Qed.

Lemma freevars_shift_1 :
  forall M k n,
    eq_sets _
      (freevars (shift k n M))
      (set_map eq_nat_dec (shift_var k n) (freevars M)).
Proof.
 induction M; simpl; intros k n.
 (* Case TmConst *)
         sauto.

 (* Case TmVar *)
        unfold shift_var; break; auto.

 (* Case TmPair *)
       apply eq_sets_symm.
       setoid_replace (freevars (shift k n M1))
           with (set_map eq_nat_dec (shift_var k n) (freevars M1)) by auto.
       setoid_replace (freevars (shift k n M2))
           with (set_map eq_nat_dec (shift_var k n) (freevars M2)) by auto.
       apply map_union.

 (* Case TmProj *)
      simpl; f_equal; eauto.

 (* Case TmAbs *)
     rewrite set_map_map.
     assert (eq_sets _ (set_remove _ eq_nat_dec 0 (freevars (shift (S k) n M)))
       (set_remove _ eq_nat_dec 0 (set_map eq_nat_dec (shift_var (S k) n) (freevars M)))).
      rewrite IHM.
      auto.
     assert (eq_sets _
       (set_map eq_nat_dec
         (fun x => x-1) (set_remove _ eq_nat_dec 0 (freevars (shift (S k) n M))))
       (set_map eq_nat_dec
         (fun x => x-1)
         (set_remove _ eq_nat_dec 0
           (set_map eq_nat_dec (shift_var (S k) n) (freevars M))))).
      rewrite H; auto.
     apply eq_sets_trans with
       (set_map eq_nat_dec (fun x => x-1)
         (set_remove _ eq_nat_dec 0
           (set_map eq_nat_dec (shift_var (S k) n) (freevars M)))).
      auto.
     assert (0 = shift_var (S k) n 0).
     unfold shift_var.
      break; finish.
     rewrite H1 at 1.
      rewrite <- map_remove.
       rewrite set_map_map.
      replace set_remove with Sets.set_remove by auto.
      rewrite set_map_extensionality with (g := fun x => shift_var k n (x-1)).
       auto.
      intros.
      (* subst f. *)
      apply in_set_remove_not_removed in H2.
      apply shift_var_S_pred; auto.
     unfold shift_var.
     intros y z H2.
     break; break; solve [omega].

 (* Case TmApp *)
    apply eq_sets_symm.
    setoid_replace (freevars (shift k n M1))
        with (set_map eq_nat_dec (shift_var k n) (freevars M1)) by auto.
    setoid_replace (freevars (shift k n M2))
        with (set_map eq_nat_dec (shift_var k n) (freevars M2)) by auto.
    apply map_union.

   trivial.

  rewrite IHM.
  auto.

 rewrite IHM1.
 rewrite IHM2.
 rewrite map_union.
 trivial.
 (* Case TmBind *)
 (* TODO: the TmAbs case should be as simple as this. *)
 rewrite IHM1.
 rewrite IHM2.
 rewrite map_union.
 apply union_eq_mor.
  auto.
 replace 0 with (shift_var (S k) n 0) at 1 by auto.
 rewrite <- map_remove.
  rewrite set_map_map.
  rewrite set_map_map.
  rewrite set_map_extensionality with (g := (fun x => shift_var k n (x - 1))).
   auto.
  intros.
  unfold shift_var.
  assert (x <> 0).
   apply set_remove_elim in H; intuition.
  break; break; try omega.
 intros.
 unfold shift_var in H0.
 destruct (le_gt_dec (S k) y); destruct (le_gt_dec (S k) z); omega.
Qed.

Lemma pred_shift :
  forall x,
      pred (shift_var 0 1 x) = x.
Proof.
 intros.
 unfold shift_var.
 simpl.
 omega.
Qed.

Lemma pred_freevars_shift :
  forall M,
    eq_sets _
      (set_map eq_nat_dec pred (freevars (shift 0 1 M)))
      (freevars M).
Proof.
 intros.
 rewrite freevars_shift_1.
 rewrite set_map_map.
 apply set_map_idy_ext.
 intros.
 apply pred_shift.
Qed.

Require Import Listkit.All.

Lemma all_remove A A_dec (x:A) P xs:
  all _ (fun y => y = x \/ P y) xs -> all _ P (set_remove _ A_dec x xs).
 unfold all.
intros.
 pose (H x0).
 apply set_remove_elim in H0.
 intuition.
Qed.

(* TODO: Use outside_range? *)
Lemma shift_freevars:
  forall M k,
    all _ (fun x => x < k \/ k+1 <= x) (freevars (shift k 1 M)).
Proof.
 induction M; simpl; intros k.
 (* Case TmConst *)
          unfold empty_set; unfold all; simpl; intros; easy.
 (* Case TmVar *)
         unfold all.
         simpl.
         intros.
         unfold shift_var in *.
         destruct (le_gt_dec k x); omega.
 (* Case TmPair *)
        apply all_union.
        split; [apply IHM1 | apply IHM2].
 (* Case TmProj *)
       auto.
 (* Case TmAbs *)
      rewrite all_map.
      apply all_remove.
      pose (H := IHM (S k)).
      unfold all in H |- *.
      intros x H0.
      pose (H1 := H x H0).
      omega.

 (* Case TmApp *)
     rewrite all_union.
     split.
      apply IHM1; auto.
     apply IHM2; auto...

 (* Case TmNull *)
    unfold all. intros. easy.

 (* Case TmSingle *)
   auto.

 (* Case TmUnion *)
  rewrite all_union.
  auto.
 (* Case TmBind *)
 rewrite all_union.
 split.
  apply IHM1.
 rewrite all_map.
 apply all_remove.
 pose (H := IHM2 (S k)).
 unfold all in H |- *.
 intros; specialize (H x H0).
 omega.
Qed.

Lemma remove_0_shift_0_1:
  forall x,
    eq_sets nat (set_remove nat eq_nat_dec 0 (freevars (shift 0 1 x)))
            (freevars (shift 0 1 x)).
Proof.
 unfold eq_sets.
 split.
  unfold incl_sets.
  intros.
  apply set_remove_elim in H.
  tauto.
 unfold incl_sets.
 intros.
 apply set_remove_intro.
 intuition.
 apply shift_freevars in H.
 omega.
Qed.
