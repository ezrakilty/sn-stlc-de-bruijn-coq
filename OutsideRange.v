Require Import Arith.

Load "eztactics.v".

Definition outside_range a b x :=
  if le_gt_dec a x then
    if le_gt_dec b x then true else false
  else true.

(* TODO: Use this everywhere, instead of outside_range *)
Definition Outside_Range a b x :=
  {x < a} + {x >= b}.

Lemma outside_range_elim a b x: true = outside_range a b x -> Outside_Range a b x.
 unfold outside_range.
 unfold Outside_Range.
 break; try break; solve [intuition | discriminate].
Qed.
