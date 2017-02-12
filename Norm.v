Load "eztactics.v".

Require Import Term.
Require Import Rewrites.

(** Strong normalization: a term is strongly normalizing if all its
    reducts are strongly normalizing. 

    The well-foundedness of inductive objects in Coq means that the
    reduction trees are well-founded or strongly-normalizing.
*)
Inductive SN m :=
  reducts_SN : (forall m', (m ~> m') -> SN m') -> SN m.

Hint Constructors SN.
Hint Resolve reducts_SN.

Lemma SN_Const : SN TmConst.
 apply reducts_SN.
 intros.
 solve by inversion 1.
Qed.

Lemma SN_Var : forall x, SN (TmVar x).
 intros.
 apply reducts_SN.
 intros.
 solve by inversion.
Qed.

(*
Lemma SN_Abs : forall n, SN n -> SN (TmAbs n).
 intros; apply reducts_SN; intros.
 intros ; solve by inversion.
Qed.
*)

Hint Resolve SN_Const SN_Var (*SN_Abs*).

(** If a property is preserved by reduction, then it holds for all
    strongly normalizing terms. *)
Lemma SN_induction P:
  (forall M, (forall M', (M ~> M') -> P M') -> P M) ->
  forall M,
    SN M ->
    P M.
Proof.
 intros IH M H.
 induction H; eauto.
Qed.

Lemma SN_double_induction_weak P:
  (forall x y,
    (forall x', (x ~> x') -> P x' y) -> P x y) ->
  (forall x y,
    (forall y', (y ~> y') -> P x y') -> P x y) ->
  forall x y, SN x -> SN y -> P x y.
Proof.
 intros IH_x IH_y x y SN_x SN_y.
 induction SN_x; induction SN_y.
 eauto.
Qed.

(** [Double_SN] holds for a pair of terms iff all of the immediate
    reducts of each one is also [Double_SN]. TODO: I think this is the
    same as each one separately being strongly normalizing, so what do I
    need it for? *)
Inductive Double_SN M N :=
  | both_reducts_sn :
       (forall M', (M ~> M') -> Double_SN M' N)
    -> (forall N', (N ~> N') -> Double_SN M N')
    -> Double_SN M N.

Lemma double_sn_intro :
  forall M, SN M -> forall N, SN N -> Double_SN M N.
Proof.
 intros M SN_M.
 induction SN_M.
 intros N SN_N.
 induction SN_N.
 rename m into N.
 apply both_reducts_sn; solve [auto].
Qed.

Lemma double_sn_elim :
  forall M N, Double_SN M N -> SN M * SN N.
Proof.
 intros.
 induction H.
 split.
  apply reducts_SN.
  firstorder.
 apply reducts_SN.
 firstorder.
Qed.

Lemma Double_SN_induction P:
  (forall x y,
    (forall x', (x ~> x') -> P x' y) ->
    (forall y', (y ~> y') -> P x y') -> P x y) ->
  forall x y, Double_SN x y -> P x y.
Proof.
 intros IH x y SN_x_y.
 induction SN_x_y.
 auto.
Qed.

(** An induction principle on pairs of SN terms simultaneously. If a
    relation [P] between terms holds given its holding for every reduct of
    either term, then it holds for all strongly normalizing terms. *)
Lemma SN_double_induction P:
  (forall x y,
    (forall x', (x ~> x') -> P x' y) ->
    (forall y', (y ~> y') -> P x y') -> P x y) ->
  forall x y, SN x -> SN y -> P x y.
Proof.
 intros IH x y SN_x SN_y.
 apply Double_SN_induction; auto.
 apply double_sn_intro; auto.
Qed.

Ltac double_induction_SN M N :=
  cut (M ~>> M); [|auto]; cut (N ~>> N); [|sauto]; pattern N at 2 3, M at 2 3;
  refine (SN_double_induction _ _ N M _ _) ; [ | sauto | sauto].

Ltac double_induction_SN_intro M N :=
  cut (M ~>> M); [|auto]; cut (N ~>> N); [|sauto]; pattern N at 2 3, M at 2 3;
  refine (SN_double_induction _ _ N M _ _) ; [ | sauto | sauto];
  let N' := fresh N "'" in
  let M' := fresh M "'" in
  let IHN := fresh "IH" N in
  let IHM := fresh "IH" M in
  let N_rw_N' := fresh N "_rw_" N' in
  let M_rw_M' := fresh M "_rw_" M' in
  intros N' M' IHN IHM N_rw_N' M_rw_M'.

(** The tactic [redseq_induction M] allows us to prove the current
   goal [P M] by proving that [P] holds for an arbitrary transitive
   reduct of [M], provided that all of ITS immediate reducts have the
   property. *)
Ltac redseq_induction M :=
   cut (M ~>> M); [|auto];
   pattern M at 2 3; (* The reduct and the other position *)
   refine (SN_induction _ _ M _); [
   let M' := fresh M in
     let IH_M := fresh "IH" M in
         let M_to_M' := fresh M "to" M' in
           intros M' IH_M; intros
     | try trivial].

(** Reducing a term transitively preserves its SN status. *)
Lemma Rw_trans_preserves_SN :
  forall M M',
    SN M -> (M ~>> M') -> SN M'.
Proof.
 intros M M' H red.
 induction red.
   congruence.
  inversion_clear H; auto.
 auto.
Qed.


(* (        ~>          )      (               )
   (   M ---------> M'  )      (            N  )
   (   |            |   )      (            |  )
   ( f |          f |   )  ->  (          f |  ) -> SN Q -> SN N
   (   |            |   )      (            |  )
   (   V    ~>      V   )      (     ~>>    V  )
   (  f M · · · ·> f M' )      ( Q ------> f N ) *)

(** If we have a function [f] that is compatible with rewriting, then
    for any SN term [Q], if [Q] reduces (transitively) to some [f M],
    and [f M] is SN, then [M] is too. (Oy, that's awkward. Any simpler
    lemma we could use instead?) *)
Lemma SN_embedding f:
  (forall M M', (M ~> M') -> (f M ~> f M')) ->
  forall Q, SN Q ->
    forall M, (Q ~>> f M) -> SN M.
(* TODO: I can't believe how hard this was!
   TODO: Wrap this up in something that instantiates Q as f M, which is how we use it. *)
Proof.
 intros H Q H0.
 induction H0.
 rename m into q.
 intros.
 apply reducts_SN.
 assert (H2 : SN (f M)).
  apply Rw_trans_preserves_SN with (M := q); auto.
 inversion H2.
 intros.
 assert (H5 : {x:Term & ((q ~> x) * (x ~>> f m'))%type}).
  apply last_step_first_step_lemma with (f M); auto.
 destruct H5 as [x [q_x x_f_m']].
 apply H0 with x; auto.
Qed.

Lemma SN_context_Proj : forall b M,
                          SN (TmProj b M) -> SN M.
Proof.
 intros b M H.
 apply (SN_embedding (TmProj b)) with (TmProj b M); auto.
Qed.

Lemma SN_context_App_left:
  forall L M, SN (L@M) -> SN L.
Proof.
 intros L M H.
 apply (SN_embedding (fun x => (x @ M))) with (L @ M); auto.
Qed.
