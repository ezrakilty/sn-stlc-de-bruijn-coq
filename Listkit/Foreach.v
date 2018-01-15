Require Import List.

Set Universe Polymorphism.

Fixpoint zip A B xs ys {struct xs} : list (A*B) :=
  match xs with
  | nil => nil
  | x::xs' => match ys with
        | nil => nil
        | y::ys' => (x, y) :: zip A B xs' ys'
        end
end.

Fixpoint zip_with A B C (f : A->B->C) xs ys {struct xs} : list C :=
  match xs with
  | nil => nil
  | x::xs' => match ys with
        | nil => nil
        | y::ys' => f x y :: zip_with A B C f xs' ys'
        end
end.

(** Assert that a predicate is true for each element of a list. *)
Definition foreach A (xs : list A) (P : A -> Prop) :=
  fold_right and True (map P xs).

(** When we have [foreach xs P] then indexing with [nth_error] into
    [xs] gives something with [P] *)
Lemma foreach_member : forall A P v n xs,
    foreach A xs P -> value v = nth_error xs n -> P v.
Proof.
 induction n; simpl; intros; destruct xs; try discriminate.
  unfold foreach in H.
  simpl in H.
  inversion H0.
  cut (P a); intuition.
 firstorder.
Qed.

(** Assert that a (Type-valued) predicate is true for each element of a list. *)
Definition foreach_ty A (xs : list A) (P : A -> Type) :=
  fold_right (fun x y => x*y)%type True (map P xs).

(** Assert that all corresponding elements of two lists stand in a certain relation. *)
Definition foreach2 A B (xs : list A) (ys : list B ) (P : A -> B -> Prop) :=
  fold_right and True
    (map (fun pr:A*B => let (x, y) := pr in P x y)
         (zip A B xs ys)).

Lemma foreach2_member : forall A B R v w n xs ys,
    (foreach2 A B xs ys R) ->
    value v = nth_error xs n ->
    value w = nth_error ys n ->
    R v w.
Proof.
 induction n; simpl; intros; destruct xs; destruct ys; try discriminate.
  unfold foreach2 in H.
  simpl in H.
  inversion H0.
  inversion H1.
  firstorder.
 firstorder.
Qed.

(** Assert that all corresponding elements of two lists stand in a
    certain (Type-valued) relation. *)
Definition foreach2_ty A B (xs : list A) (ys : list B ) (P : A -> B -> Type) :=
  fold_right
    (fun x y => x*y)%type
    unit%type
    (map (fun pr:A*B => let (x, y) := pr in P x y) (zip A B xs ys)).

Lemma foreach2_ty_member : forall A B R v w n xs ys,
    (foreach2_ty A B xs ys R) ->
    value v = nth_error xs n ->
    value w = nth_error ys n ->
    R v w.
Proof.
 induction n; simpl; intros; destruct xs; destruct ys; try discriminate.
  unfold foreach2_ty in X.
  simpl in X.
  inversion H.
  inversion H0.
  firstorder.
 firstorder.
Qed.

(* Unused: remove? *)
Lemma foreach_cut A (P Q : A -> Prop) xs:
   (forall x, In x xs -> P x -> Q x) -> foreach _ xs P -> foreach _ xs Q.
Proof.
 induction xs; firstorder.
Qed.

(* Unused: remove? *)
Lemma foreach2_cut A B (P Q : A -> B -> Prop):
  forall xs ys,
    (forall x y, In x xs -> In y ys -> P x y -> Q x y) ->
    foreach2 _ _ xs ys P -> foreach2 _ _ xs ys Q.
Proof.
 induction xs; [idtac|destruct ys]; firstorder.
Qed.

Lemma foreach2_ty_cons :
  forall A B x xs y ys R,
  foreach2_ty A B (x::xs) (y::ys) R =
   (R x y * foreach2_ty A B xs ys R)%type.
Proof.
 intuition.
Qed.

Hint Resolve foreach2_ty_cons.

(* Unused: remove? *)
Lemma foreach2_ty_cut A B (P Q : A -> B -> Type):
  forall xs ys,
    (forall x y, In x xs -> In y ys -> P x y -> Q x y) ->
    foreach2_ty _ _ xs ys P -> foreach2_ty _ _ xs ys Q.
Proof.
 induction xs; [idtac|destruct ys]; firstorder.
Qed.

Lemma foreach_ty_map :
  forall A f P xs,
    foreach_ty A (map f xs) P = foreach_ty A xs (fun x => P (f x)).
Proof.
 induction xs; unfold foreach_ty; auto.
 rewrite map_map.
 trivial.
Qed.

Lemma foreach_ty_impl :
  forall A P Q xs,
    (forall x, P x -> Q x) -> foreach_ty A xs P -> foreach_ty A xs Q.
Proof.
 unfold foreach_ty.
 unfold fold_right.
 induction xs; simpl; intros P_impl_Q H.
  auto.
 inversion H.
 split.
  auto.
 apply IHxs; auto.
Qed.

Lemma foreach_ty_member : forall A P v,
  forall n xs,
    (foreach_ty A xs P) ->
    value v = nth_error xs n -> P v.
Proof.
 induction n; simpl; intros; destruct xs; try discriminate.
  unfold foreach_ty in X.
  simpl in X.
  inversion H.
  intuition.
 firstorder.
Qed.

Lemma foreach_universal:
  forall A (f:A->Prop), (forall x, f x) -> forall xs, foreach _ xs f.
Proof.
 induction xs; unfold foreach; simpl; intros.
  auto.
 auto.
Qed.

Lemma zip_map_diamond:
  forall A B1 B2 (f1:A->B1) (f2:A->B2) xs,
    zip _ _ (map f1 xs) (map f2 xs) = map (fun x => (f1 x, f2 x)) xs.
Proof.
 induction xs; simpl; intros.
  auto.
 f_equal.
 auto.
Qed.
