Load eztactics.

Require Import List.
Require Import Omega.

(* Add LoadPath "../Listkit" as Listkit. *)

Require Import logickit.

Lemma nth_error_ok A :
  forall n (xs : list A), length xs > n ->
    exists v, nth_error xs n = value v.
Proof.
 induction n; destruct xs; simpl; intros; try (elimtype False; omega).
  eauto.
 assert (H0 : (length xs) > n).
 omega.
 apply (IHn xs H0).
Qed.

Lemma nth_error_overflow :
  forall A (l:list A) n, length l <= n <-> nth_error l n = error.
Proof.
 induction l; induction n; firstorder.
   simpl in H.
   inversion H.
  discriminate.
 simpl in H1 |- *.
 apply le_n_S.
 apply <- IHl.
 trivial.
Qed.

Lemma nth_error_overflow_errors:
  forall A (l:list A) n, length l <= n -> nth_error l n = error.
Proof.
 intros; apply -> nth_error_overflow; trivial.
Qed.

Lemma nth_error_app_strong A :
  forall (x:A) xs ys n,
  value x = nth_error (xs ++ ys) n ->
  {n >= length xs /\ value x = nth_error ys (n - length xs)}
  + {n < length xs /\ value x = nth_error xs n}.
Proof.
Unset Ltac Debug.
 induction xs; simpl; intros ys n H.
  replace (n-0) with n by omega.
  left; split; [omega|auto].
 destruct n; simpl in * |- *.
  right.
  intuition.
 destruct (IHxs ys n).
   auto.
  left; intuition.
 right; intuition.
Qed.

Lemma nth_error_ok_rev :
  forall A (x:A) xs n, value x = nth_error xs n -> n < length xs.
Proof.
 induction xs; simpl; intros n H.
  unfold nth_error in *.
  destruct n;
    discriminate.
 destruct n; simpl in H.
  omega.
 assert (n < length xs).
  auto.
 omega.
Qed.

Lemma nth_error_nil A : forall x, nth_error (nil: list A) x = error.
Proof.
 intros.
 apply -> nth_error_overflow.
 simpl; apply le_O_n.
Qed.

Hint Resolve nth_error_nil nth_error_ok nth_error_ok_rev
        nth_error_overflow_errors
        nth_error_overflow.

Lemma nth_error_ext_length:
  forall A (a b: list A) n,
    n < length a ->
    nth_error a n = nth_error (a++b) n.
 induction a; simpl; intros b n H.
  by_omega.
 (* rewrite <- app_comm_cons.*)
 destruct n; simpl.
  auto.
 apply IHa.
 omega.
Qed.

Lemma nth_error_ext:
  forall A (a b: list A) n v,
    nth_error a n = value v ->
    value v = nth_error (a++b) n.
Proof.
 intros; rewrite <- nth_error_ext_length; auto.
 eauto.
Qed.

Lemma nth_error_app A :
  forall (x:A) xs ys n,
   n >= length xs ->
  value x = nth_error (xs ++ ys) n ->
    value x = nth_error ys (n - length xs).
Proof.
 induction xs; simpl; intros ys n n_big H.
  replace (n-0) with n; [trivial|omega].
 destruct n; simpl in * |- *.
  elimtype False; omega.
 apply IHxs; trivial.
  omega.
Qed.

Lemma rewrite_nth_error_app A :
  forall (xs ys : list A) n,
   n >= length xs ->
  nth_error (xs ++ ys) n =
    nth_error ys (n - length xs).
Proof.
 induction xs; simpl; intros ys n n_big.
  replace (n-0) with n; [trivial|omega].
 destruct n; simpl in * |- *.
  elimtype False; omega.
 apply IHxs; trivial.
 omega.
Qed.

Hint Resolve nth_error_ext nth_error_ext_length nth_error_app.

Lemma nth_error_map:
  forall A B (f:A->B) xs n,
  nth_error (map f xs) n = fmap _ _ f (nth_error xs n).
Proof.
 intros A B f.
 induction xs; intro n;
  destruct n; simpl; auto.
Qed.

Lemma nth_error_S :
  forall A (h:A) t n, nth_error (h::t) (S n) = nth_error t n.
Proof.
 induction n; simpl;
  destruct t; auto.
Qed.

Lemma nth_error_app_eq:
  forall (A : Type) (xs ys : list A) (n : nat),
     n >= length xs ->
     n < length (xs ++ ys) ->
     nth_error (xs ++ ys) n =
     nth_error ys (n - length xs).
Proof.
 intros A xs ys n n_lb n_ub.
 pose (H:=nth_error_ok A n (xs++ys)).
 destruct H.
 omega.
 transitivity (value x); trivial.
 apply nth_error_app; auto.
Qed.

Lemma nth_error_app_split :
  forall A (xs:list A) ys n v,
    nth_error (xs++ys) n = value v ->
    (n < length xs /\ nth_error xs n = value v)
    \/ (n >= length xs /\ nth_error ys (n-length xs) = value v).
Proof.
 induction xs;
 intros ys n v H;
  simpl in H |- *.
  right; intuition; eauto.
  replace (n-0) with n; auto; omega.
 destruct n; simpl in *; firstorder.
Qed.

Lemma nth_error_app_split_error :
  forall A (xs:list A) ys n,
    nth_error (xs++ys) n = error ->
    n >= length xs + length ys /\ nth_error xs n = error
    /\ nth_error ys (n-length xs) = error.
Proof.
 induction xs;
 intros ys n H;
  simpl in *.
  intuition; eauto.
   cut (length ys <= n); [omega|apply <- nth_error_overflow]; trivial.
  replace (n-0) with n; auto; omega.
 destruct n; try discriminate; simpl in *; firstorder.
Qed.

(** When two lists are equally long, we can take the same index into
    each one and we will either get two hits or two misses. *)
Lemma equilong_nth_error:
  forall A B (xs : list A) (ys : list B) n,
  length xs = length ys ->
  {n < length xs /\
    exists x, exists y, nth_error xs n = value x /\ nth_error ys n = value y} +
  {n >= length xs /\ nth_error xs n = error /\ nth_error ys n = error}.
Proof.
(* intros A.*)
 induction xs as [|x xs]; destruct ys as [|y ys]; destruct n; simpl;
    intuition; try discriminate.
 left; split; [omega|]; exists x; exists y; auto.
 destruct (IHxs ys n); [omega| |];
 try (solve[right; intuition]); try (solve[left; intuition]).
Qed.

Lemma nth_error_exists:
  forall A (xs: list A) n,
  n < length xs -> exists x, nth_error xs n = value x.
Proof.
 induction xs; destruct n; simpl; intros H;
 try (elimtype False; omega); eauto; (apply IHxs; omega).
Qed.

Lemma nth_error_to_length :
  forall A (v:A) xs n, value v = nth_error xs n -> n < length xs.
Proof.
 induction xs; simpl; intros n H.
  destruct n; simpl in H; discriminate.
 destruct n; simpl in H.
  omega.
 apply lt_n_S.
 apply IHxs; trivial.
Qed.

Lemma nth_error_dichot A (xs : list A):
  forall n,
  {n >= length xs /\ nth_error xs n = error} +
  {n < length xs /\ exists v, nth_error xs n = value v}.
Proof.
 induction xs; destruct n; simpl.
    left; auto.
   left; split.
    omega.
   auto.
  right.
  split.
   omega.
  eauto.
 destruct (IHxs n).
  left; intuition.
 right; intuition.
Qed.

(* TBD: Move to listkit. *)
Ltac nth_error_dichotomize bounds is_error v v_def :=
  match goal with
    | |- context C [nth_error ?xs ?n] =>
      (destruct (nth_error_dichot _ xs n)
       as [[bounds is_error] | [bounds [v v_def]]];
         [rewrite is_error; simpl | rewrite v_def; simpl])
  end.

Lemma nth_error_rewrite_app_right:
  forall A (xs ys:list A) n,
    length xs <= n ->
    nth_error (xs ++ ys) n = nth_error ys (n-length xs).
 induction xs; simpl; intros.
  replace (n-0) with (n) by omega.
  auto.
 destruct n.
  easy.
 simpl.
 apply IHxs.
 omega.
Qed.

Lemma nth_error_rewrite_app_left:
  forall A (xs ys:list A) n,
    n < length xs ->
    nth_error (xs ++ ys) n = nth_error xs n.
Proof.
 induction xs; simpl; intros.
  easy.
 destruct n.
  auto.
 simpl.
 apply IHxs.
 omega.
Qed.

Hint Resolve nth_error_ok nth_error_overflow nth_error_overflow_errors
        nth_error_app_strong nth_error_ok_rev nth_error_nil
        nth_error_ext_length nth_error_ext nth_error_app rewrite_nth_error_app
        nth_error_map nth_error_S nth_error_app_eq nth_error_app_split
        nth_error_app_split_error equilong_nth_error nth_error_exists
        nth_error_to_length nth_error_dichot nth_error_rewrite_app_right
        nth_error_rewrite_app_left : NthError.
