Add LoadPath "Listkit" as Listkit.

Require Import Norm.
Require Import Rewrites.
Require Import Term.
Require Import Omega.

Inductive Continuation :=
  Empty : Continuation
| Iterate : Term -> Continuation -> Continuation.

Fixpoint plug (K : Continuation) (M : Term) : Term :=
  match K with
      Empty => M
    | Iterate N K' => plug K' (TmBind M N)
  end.

Definition SNK (K : Continuation) :=
  forall M,
    SN M ->
    SN (plug K (TmSingle M)).

Definition ReducibleK (Reducible:Term->Ty -> Type) (K : Continuation) (T : Ty) :=
    forall M,
      Reducible M T ->
      SN (plug K (TmSingle M)).

Lemma Rw_under_K:
  forall K M N,
    (M ~> N) -> (plug K M ~> plug K N).
Proof.
 induction K; simpl; intros; auto.
Qed.

Hint Resolve Rw_under_K.

Lemma plug_SN_rw:
  forall K M M',
    (M ~> M') -> SN (plug K M) -> SN (plug K M').
Proof.
 intros.
 inversion H0.
 apply H1.
 auto.
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

Hint Constructors Krw_rt.

Lemma iterate_reduce K K' : Krw K K' -> forall F, Krw (Iterate F K) (Iterate F K').
Proof.
 unfold Krw.
 intros.
 simpl.
 apply H.
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
 Unused but might be good practice?
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

Lemma Krw_inhabited:
  Krw (Iterate (TmBind TmNull TmNull) Empty) (Iterate TmNull Empty).
Proof.
 unfold Krw.
 intros.
 simpl.
 eauto.
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

Lemma Krw_rt_Rw_rt:
  forall K K' M, Krw_rt K K' -> (plug K M ~>> plug K' M).
Proof.
 intros.
 induction H; subst; eauto.
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
