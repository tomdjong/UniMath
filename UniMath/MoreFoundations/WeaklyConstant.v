(**

Tom de Jong

Created: November 2018

Refactored: January 2019

*******************************************************************************)

(** * Some results on weakly constant functions *)
(** ** Contents
- Definition of weakly constant functions as functions for which any two values
  are equal
- Any weakly constant function from X into a set factors through the
  propositional truncation ∥ X ∥ of X (Theorem 5.4 in [1])
- A weakly constant endomap on the path space implies that the path space is
  propositional (Lemma 3.11 in [1])
[1] "Notions of Anonymous Existence in Martin-Löf Type Theory" by Kraus et al.
*)

Require Import UniMath.Foundations.All.

Definition weaklyconstant {X Y : UU} (f : X -> Y) : UU :=
  ∏ (x x' : X), f x = f x'.

Lemma weaklyconstanttoaset_haspropimage {X Y : UU} (f : X -> Y) :
  isaset Y -> weaklyconstant f -> isaprop (image f).
Proof.
  intros Yisaset fweaklyconstant.
  apply invproofirrelevance.
  intros [y u] [y' u'].
  assert (w : hfiber f y -> hfiber f y' -> y = y').
  { intros [x p] [x' p']. rewrite <- p; rewrite <- p'.
    apply fweaklyconstant. }
  assert (w' : hfiber f y -> ∥ hfiber f y' ∥ -> y = y').
  { intro yfib. apply factor_through_squash.
    - apply Yisaset.
    - exact (w yfib). }
  assert (w'' : ∥ hfiber f y ∥ -> ∥ hfiber f y' ∥ -> y = y').
  { use factor_through_squash.
    - apply isapropimpl. apply Yisaset.
    - exact w'. }
  apply total2_paths_equiv.
  exists (w'' u u').
  apply proofirrelevance.
  apply isapropishinh.
Qed.

(** Any function f : X → Y factors through its image.
    If f is weakly constant, then the image is propositional
    by the lemma above, so then f : X → im(f) factors through ∥ X ∥. *)
Definition weaklyconstanttoaset_factorsthroughsquash {X Y : UU} (f : X -> Y) :
  isaset Y -> weaklyconstant f -> ∥X∥ -> Y.
Proof.
  intros Yisaset fweaklyconstant.
  set (h := factor_through_squash
            (weaklyconstanttoaset_haspropimage f Yisaset fweaklyconstant)
            (prtoimage f)).
  exact ((pr1image f) ∘ h).
Defined.

Definition weaklyconstanttoaset_factorsthroughsquash_eq {X Y : UU} (f : X -> Y)
                                             (Yisaset : isaset Y)
                                             (fconst : weaklyconstant f) :
  weaklyconstanttoaset_factorsthroughsquash f Yisaset fconst ∘ (@hinhpr X) ~ f.
Proof.
  intro x. cbn.
  apply idpath.
Defined.

Definition weaklyconstant_endomap (X : UU) := ∑ (f : X -> X), weaklyconstant f.

Definition wconst_endomap_prop_path_prop {X : UU} :
  isaprop X ->
  (∏ (Y : UU), isaprop Y -> weaklyconstant_endomap (X = Y)) ->
  ∏ Y : UU, isaprop Y -> isaprop (X = Y).
Proof.
  intros Xaprop wconstendo.
  intros Y Yaprop.
  assert (patheq : ∏ (p : X = Y), p = !(pr1 (wconstendo X Xaprop) (idpath X)) @
                                       pr1 (wconstendo Y Yaprop) p).
  { induction p. apply pathsinv0.
    assert (propaprop : Yaprop = Xaprop).
    { apply proofirrelevance, isapropisaprop. }
    rewrite propaprop.
    apply pathsinv0l. }
  apply invproofirrelevance.
  intros p q.
  rewrite (patheq p).
  rewrite (patheq q).
  apply maponpaths.
  apply (pr2 (wconstendo Y Yaprop)).
Defined.