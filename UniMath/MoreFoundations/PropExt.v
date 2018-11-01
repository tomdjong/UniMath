Require Import UniMath.Foundations.All.

Definition propext {X Y : UU} : isaprop X -> isaprop Y -> (X <-> Y) -> X = Y.
Proof.
  intros i j iff.
  use (invmap (univalence X Y)).
  use weqiff.
  - exact iff.
  - exact i.
  - exact j.
Defined.
