(**

Tom de Jong

January 2019

*******************************************************************************)

(** * Propositional extensionality *)
(** ** Contents
- A proof using just propositional extensionality of the fact that:
  if P and Q are propositions, then so is P = Q.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.WeaklyConstant.

Definition propext {X Y : UU} : isaprop X -> isaprop Y -> (X <-> Y) -> X = Y.
Proof.
  intros i j iff.
  apply (invmap (univalence X Y)).
  apply weqiff.
  - exact iff.
  - exact i.
  - exact j.
Defined.

Definition weaklyconstant_propext {X Y : UU} (i : isaprop X) (j : isaprop Y) :
  weaklyconstant (propext i j).
Proof.
  intros f g.
  apply maponpaths.
  apply proofirrelevance.
  apply isapropdirprod.
  - apply impred_isaprop.
    exact (λ _, j).
  - apply impred_isaprop.
    exact (λ _, i).
Defined.

Definition isaprop_pathsprop {X Y : UU} : isaprop X -> isaprop Y -> isaprop (X = Y).
Proof.
  intros i j.
  apply wconst_endomap_prop_path_prop.
  - exact i.
  - intros Z k.
    set (f := λ p : X = Z, (propext i k (weq_to_iff (eqweqmap p)))).
    exists f.
    unfold f.
    intros p q.
    apply weaklyconstant_propext.
  - exact j.
Defined.