(**
  This file represents an abortive effort to write code the enumerates
  all the reducts of any tree, which would also allow us to quantify
  the length of the maximum reduction sequence of any SN term.
*)

Fixpoint enumerate_reducts M :=
  match M with
      TmConst => nil
    | TmVar x => nil
    | TmPair M N => map (fun m => TmPair m N) (enumerate_reducts M) ++
                        map (TmPair M) (enumerate_reducts N)
    | TmProj b M =>
      match M with
          TmPair M1 M2 =>
          if b then
            M2 :: nil
          else M1 :: nil
        | _ => nil
      end ++ map (TmProj b) (enumerate_reducts M)
    | TmAbs N => map TmAbs (enumerate_reducts N)
    | TmApp L M =>
      (match L with
           TmAbs N => unshift 0 1 (subst_env 0 (shift 0 1 M :: nil) N) :: nil
         | _ => nil
       end) ++
           map (fun l => TmApp l M) (enumerate_reducts L) ++
           map (TmApp L) (enumerate_reducts M)
    | TmNull => nil
    | TmSingle M => map TmSingle (enumerate_reducts M)
    | TmUnion M N =>
      map (fun m => TmPair m N) (enumerate_reducts M) ++ map (TmPair M) (enumerate_reducts N)
    | TmBind N L =>
      (match N with
           TmNull => TmNull :: nil
         | TmSingle N' => TmApp (TmAbs L) N' :: nil
         | TmUnion N1 N2 => TmUnion (TmBind N1 L) (TmBind N2 L) :: nil
         | _ => nil
       end) ++
            map (fun n => TmBind n L) (enumerate_reducts N) ++
            map (TmBind N) (enumerate_reducts L)
  end.

Lemma enumerate_reducts_complete :
  forall M M',
    (M ~> M') ->
    In M' (enumerate_reducts M).
Proof.
 induction M; intros M' H; inversion H; simpl; subst.
 (* Case Rw_Pair_left *)
              apply in_or_app.
              left.
              rename m2 into m1.
              assert (In m1 (enumerate_reducts M1)) by (auto using IHM1).
              remember (fun m => TmPair m M2) as f.
              replace (TmPair m1 M2) with (f m1).
               apply in_map.
               auto.
              subst f.
              auto.
 (* Case Rw_Pair_right *)
             apply in_or_app.
             right.
             rename n2 into m2.
             assert (In m2 (enumerate_reducts M2)) by (auto using IHM2).
             apply in_map.
             auto.
 (* Case Rw_Proj *)
            apply in_or_app; right.
            apply in_map.
            auto.
 (* Case Rw_Proj_beta1 *)
           auto.
 (* Case Rw_Proj_beta2 *)
          auto.
 (* Case Rw_Abs_body *)
         auto using in_map, IHM.
 (* Case Rw_beta *)
        auto.
 (* Case Rw_App_left *)
       rename m2 into m1.
       apply in_or_app; right.
       apply in_or_app; left.
       remember (fun l => (l @ M2)) as f.
       replace (m1 @ M2) with (f m1).
       auto using in_map, IHM1, IHM2.
       subst; sauto.
 (* Case Rw_App_right *)
      rename n2 into m2.
      apply in_or_app; right.
      apply in_or_app; right.
      solve [eauto using in_map, IHM2].
 (* Case Rw_Single *)
     solve [auto using in_map, IHM].
 (* Case Rw_Bind_null *)
    sauto.
 (* Case Rw_Bind_beta *)
   sauto.
 (* Case Rw_Bind_union *)
  auto.
 (* Case Rw_Bind_subject *)
 apply in_or_app; right.
 apply in_or_app; left.
 remember (fun n => TmBind n M2) as f.
 replace (TmBind m' M2) with (f m').
 auto using in_map, IHM1.
 subst; sauto.
Qed.

Lemma enumerate_reducts_sound :
  forall M M',
    In M' (enumerate_reducts M) ->
    (M ~> M').
Proof.
 induction M; simpl; intros M' H.
          intuition.
         intuition.
        apply in_app_or in H.
        admit.
        (* destruct H. (* FIXME: Set vs Prop!!! *) *)
Admitted.

(* (* Next we have a function that enumerates all the reducts, together *)
(* with the witness of the reduction. Not sure the type-checker will take it. *) *)

(* Fixpoint enumerate_reducts_2 M : list ({M' : Term & M ~> M'}) := *)
(*   match M with *)
(*       TmConst => nil *)
(*     | TmVar x => nil *)
(*     | TmPair M N => map (fun X => *)
(*                            match X with *)
(*                                existT _ m r => existT _ (TmPair m N) (Rw_Pair_left _ _ _ r) *)
(*                            end) *)
(*                         (enumerate_reducts_2 M) ++ *)
(*                     map (fun (X: {N' : Term & N ~> N'}) => *)
(*                            match X with *)
(*                                existT _ n r => *)
(*                                existT _ (TmPair M n) (Rw_Pair_right _ _ _ r) *)
(*                            end) *)
(*                     (enumerate_reducts_2 N) *)
(*     | TmProj b M => *)
(*       match M with *)
(*           TmPair M1 M2 => *)
(*           if b then *)
(*             (* (existT _ M2 (Rw_Proj_beta2 _ _)) :: *) nil *)
(*           else *)
(*             (* (existT _ M1 (Rw_Proj_beta1 _ _)) :: *) nil *)
(*         | _ => nil *)
(*       end ++ *)
(*           map (fun X => *)
(*                  match X with *)
(*                      existT _ M' r => *)
(*                      existT _ (TmProj b M') (Rw_Proj _ _ _ r) *)
(*                  end) (enumerate_reducts_2 M) *)
(*     | TmAbs N => map (fun X => *)
(*                         match X with *)
(*                             existT _ n' r => *)
(*                             existT _ (TmAbs n') (Rw_Abs_body _ _ r) *)
(*                         end) *)
(*                      (enumerate_reducts_2 N) *)
(*     | TmApp (TmAbs N) M => *)
(*            (* existT _ (unshift 0 1 (subst_env 0 (shift 0 1 M :: nil) N)) *) *)
(*            (*        (Rw_beta _ _ _) *) *)
(*           ( Rw_beta N M (unshift 0 1 (subst_env 0 (shift 0 1 M :: nil) N)) _ *)
(*                    :: nil *)
(* ) ++ *)
(*             map (fun X => *)
(*                    match X with *)
(*                        existT _ l r => existT _ (TmApp l M) (Rw_App_left _ _ _ r) *)
(*                    end) *)
(*             (enumerate_reducts_2 L) ++ *)
(*             map (fun X => *)
(*                    match X with *)
(*                        existT _ m r => *)
(*                        existT _ (TmApp (TmAbs N) m) (Rw_App_right _ _ _ r) *)
(*                    end) *)
(*             (enumerate_reducts_2 M) *)
(*     | TmApp L M => *)
(*             map (fun X => *)
(*                    match X with *)
(*                        existT _ l r => existT _ (TmApp l M) (Rw_App_left _ _ _ r) *)
(*                    end) *)
(*             (enumerate_reducts_2 L) ++ *)
(*             map (fun X => *)
(*                    match X with *)
(*                        existT _ m r => *)
(*                        existT _ (TmApp L m) (Rw_App_right _ _ _ r) *)
(*                    end) *)
(*             (enumerate_reducts_2 M) *)
(*     | TmNull => nil *)
(*     | TmSingle M => map TmSingle (enumerate_reducts_2 M) *)
(*     | TmUnion M N => *)
(*       map (fun m => TmPair m N) (enumerate_reducts_2 M) ++ map (TmPair M) (enumerate_reducts_2 N) *)
(*     | TmBind N L => *)
(*       (match N with *)
(*            TmNull => TmNull :: nil *)
(*          | TmSingle N' => TmApp (TmAbs L) N' :: nil *)
(*          | TmUnion N1 N2 => TmUnion (TmBind N1 L) (TmBind N2 L) :: nil *)
(*          | _ => nil *)
(*        end) ++ *)
(*             map (fun n => TmBind n L) (enumerate_reducts_2 N) ++ *)
(*             map (TmBind N) (enumerate_reducts_2 L) *)
(*   end. *)

(* Fixpoint maxred M (X : SN M) {struct X} := *)
(*   match X with *)
(*       reducts_SN _ reduct_normalizer => *)
(*         1 + fold_left max (map (fun M' => maxred M' (reduct_normalizer M' _)) (enumerate_reducts M)) 0 *)
(*   end. *)
