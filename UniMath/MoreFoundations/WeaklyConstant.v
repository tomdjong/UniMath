Require Import UniMath.Foundations.All.

Definition weaklyconstant {X Y : UU} (f : X -> Y) : UU := ∏ (x x' : X), f x = f x'.

Lemma weaklyconstanttoaset_haspropimage {X Y : UU} (f : X -> Y) :
  isaset Y -> weaklyconstant f -> isaprop (image f).
Proof.
  intros Yisaset fweaklyconstant.
  use invproofirrelevance.
  intros [y u] [y' u'].
  assert (w : hfiber f y -> hfiber f y' -> y = y').
  { intros [x p] [x' p']. rewrite <- p; rewrite <- p'. use fweaklyconstant. }
  assert (w' : hfiber f y -> ∥ hfiber f y' ∥ -> y = y').
  { intro yfib. use factor_through_squash.
    - use Yisaset.
    - exact (w yfib). }
  assert (w'' : ∥ hfiber f y ∥ -> ∥ hfiber f y' ∥ -> y = y').
  { use factor_through_squash.
    - use isapropimpl. use Yisaset.
    - exact w'. }
  apply total2_paths_equiv.
  split with (w'' u u').
  use proofirrelevance.
  use isapropishinh.
Qed.

Definition weaklyconstanttoaset_factorsthroughsquash {X Y : UU} (f : X -> Y) :
  isaset Y -> weaklyconstant f -> ∑ (f' : ∥ X ∥ -> Y), f ~ (f' ∘ (@hinhpr X)).
Proof.
  intros Yisaset fweaklyconstant.
  (* f factors through its image, which is propostional by the lemma above,
     hence, X -> im(f) factors through ∥ X ∥. *)
  set (h := factor_through_squash
            (weaklyconstanttoaset_haspropimage f Yisaset fweaklyconstant)
            (prtoimage f)).
  split with ((pr1image f) ∘ h).
  intro x. unfold pr1image, hinhpr, h, funcomp; simpl. use idpath.
Defined.