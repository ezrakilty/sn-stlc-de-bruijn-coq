
Ltac exfalso := elimtype False. (* Coq 8.3 feature. *)

Lemma if_cc:
  forall A B Z W (f:Z->W) (a:{A}+{B}) (b c : Z),
    f (if a then b else c) = if a then f b else f c.
Proof.
 intros.
 destruct a; auto.
Qed.

Lemma if_irrelevant:
  forall A B Z (a:{A}+{B}) (b : Z),
    (if a then b else b) = b.
Proof.
 intros.
 destruct a; auto.
Qed.

Definition fmap A B (f:A->B) x :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.

(* Not list-related. Relocate. *)
Definition uncurry A B C (f:A->B->C) (xy:A*B) :=
    let (x, y) return C := xy in f x y.

Definition idy A (x:A) := x.

(* Not list-related. Relocate. *)
Lemma inhabits_cut A B (f : A -> B) : inhabited A -> inhabited B.
 intros H.
 destruct H as [X].
 exact (inhabits (f X)).
Qed.
