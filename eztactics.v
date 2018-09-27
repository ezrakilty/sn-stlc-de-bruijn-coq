Require Import Omega.

Ltac refute := elimtype False.

Ltac easy := solve [discriminate | contradiction | auto | f_equal; auto |
                    try omega | try (refute; omega)].

(* Notation "f ∘ g" := (fun x => f(g(x))) (at level 100). *)

Ltac copy p := assert p; [solve [trivial] | idtac].

Ltac careful_case t :=
  generalize (refl_equal t); pattern t at -1; case t; intros.

Ltac careful_case_names t names :=
  generalize (refl_equal t); pattern t at -1; case t; intro names.

Ltac absurd_omega stmt :=
  absurd stmt; [solve [omega] | trivial].

Ltac by_omega :=
  solve [refute; omega | omega].

Ltac eabsurd stmt lemma :=
  (absurd stmt; auto);
  (eapply lemma; eauto).

Require Import Peano_dec.

Ltac choose_equal_refl e :=
  destruct (Peano_dec.eq_nat_dec e e);
  [idtac | absurd (e = e); trivial].

Ltac choose_equal d e :=
  destruct (Peano_dec.eq_nat_dec d e);
  [idtac | absurd (d = e); omega].

Ltac choose_unequal d e :=
  destruct (Peano_dec.eq_nat_dec d e);
  [absurd (d = e); omega | idtac].

Ltac say_impl nm stmt :=
  assert (nm : stmt); [solve [auto] | idtac].

Ltac say_anon stmt :=
  let H := fresh "H" "H" in
  assert (stmt); [solve [auto] | idtac].

Tactic Notation "say" constr(prop) := say_anon prop.

Tactic Notation "say" ident(nm) ":" constr(stmt) := say_impl nm stmt.

(* (* use "say stmt" instead *)
Ltac say_anon stmt :=
  assert (stmt); [solve [auto] | idtac].
*)

Ltac all_cases_equal t :=
  destruct t as [p|q]; try (destruct p); simplify_eq.

(* given an inductive term that can only be formed by
   one of its constructors, descrim breaks it into that thing. *)
Ltac descrim t :=
  destruct t; try discriminate.

Ltac irrel_case :=
  simpl; let H := fresh in intro H; discriminate.

Ltac decide_yes comp :=
  destruct (comp) ; [trivial | contradiction].

Ltac decide_no comp :=
  destruct (comp) ; [contradiction | trivial].

Ltac assertby name stmt lemma :=
  assert (name:stmt);
      [solve [(apply lemma; auto) ||
              (eapply lemma; eauto)] | idtac].

Ltac assert_w name stmt tac :=
  assert (name:stmt); [solve [tac] | idtac].

Tactic Notation "show" constr(stmt) "with" tactic(tac) :=
  assert_w fresh stmt tac.

Tactic Notation "show" hyp(H) ":" constr(stmt) "with" tactic(tac) :=
  assert_w H stmt tac.

Tactic Notation "prove" constr(stmt) "with" tactic(tac) :=
  let h := fresh in
    assert_w h stmt tac.

(*Tactic Notation "say" ident(H) ":" constr(stmt) := say_impl H stmt.*)

Tactic Notation "prove" ident(H) ":" constr(stmt) "via" constr(reason) :=
   assertby H stmt reason.

Require Import Arith.

Ltac introversion :=
  let H := fresh in
  intro H; inversion H.

Tactic Notation "introvert" "with" simple_intropattern(names) :=
  let H := fresh in
  intro H; inversion H as names.

(* Swap the goal with the chosen hypothesis, negating both. *)
Ltac contrapose H :=
  hnf in H |- *;
  match goal with
  |- (?xxx -> False) =>
    let X := fresh in
    match type of H with
      (?stmt -> False) =>
        intro X; unfold not in H; apply H; clear H
    end;
   rename X into H
  end.

Ltac call_spade x :=
  destruct (eq_nat_dec x x); [trivial | absurd (x = x); auto].

Ltac existence_ridiculous hyp :=
  let H1 := fresh in
  hnf in hyp; inversion hyp as [x H1]; inversion H1.

Ltac second := left; right.
Ltac third := left; left; right.
Ltac fourth := left; left; left; right.

Ltac nth n :=
  match n with
  | 0 => right
  | S ?n' => left; nth n'
  end.

(* From Benjamin Pierce:
   "A similar annoyance arises in situations where the context contains
   a contradictory assumption and we want to use [inversion] on it to
   solve the goal.  We'd like to be able to say to Coq, "find a
   contradictory assumption and invert it" without giving its name
   explicitly.

   Unfortunately (and a bit surprisingly), Coq does not provide a
   built-in tactic that does this.  However, it is not too hard to
   define one ourselves.  (Thanks to Aaron Bohannon for this nice
   hack.)" *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(** Finds a decidable comparison and takes cases on the decision *)
Ltac break :=
  match goal with
  | |- context C [le_gt_dec ?x ?y] =>
(*    let X := fresh in let Y := fresh in case_eq (le_gt_dec x y); intros X Y*)
    destruct (le_gt_dec x y)
  | |- context C [eq_nat_dec ?x ?y] =>
(*    let X := fresh in let Y := fresh in case_eq (eq_nat_dec x y); intros X Y*)
    destruct (eq_nat_dec x y)
  end.

(** Finds a decidable comparison and takes cases on the decision *)
Ltac break_in H :=
  match goal with
  | H : context C [le_gt_dec ?x ?y] |- _ =>
(*    let X := fresh in let Y := fresh in case_eq (le_gt_dec x y); intros X Y*)
    destruct (le_gt_dec x y)
  | H : context C [eq_nat_dec ?x ?y] |- _ =>
(*    let X := fresh in let Y := fresh in case_eq (eq_nat_dec x y); intros X Y*)
    destruct (eq_nat_dec x y)
  end.

Ltac suff H tac :=   (* TODO: replaced by Coq's 'enough' *)
  cut H; [solve[tac] | ].

Tactic Notation "sufficient" reference(H) "by" tactic(tac) := suff H tac.
Tactic Notation "sufficient" reference(H) := suff H auto.

(** Moves a hypothesis back into the conclusion as a premise--the inverse of intro H. *)
Ltac extro H :=
  let t := type of H in
    cut t; [clear H | auto].

Ltac breakauto := break; try omega; try auto.

Ltac finish := solve [auto | omega].
Ltac efinish := solve [simpl;eauto | simpl;omega].

Ltac sauto := solve [auto].
Ltac seauto := solve [eauto].

Ltac double_case := (* Another form of if_irrelevant! *)
  match goal with
    | |- context C[if ?X then ?Y else ?Y] =>
          replace (if X then Y else Y) with (Y) by breakauto
  end.

Ltac splitN n :=
  match n with
    | 2 => split
    | 3 => split; [splitN 2 | ]
    | S n => split; [splitN n | ]
  end.
