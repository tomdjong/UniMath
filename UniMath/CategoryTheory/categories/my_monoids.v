(** * Category of monoids *)
(** ** Contents
- Category of monoids
- Characterising isomorphisms
- Category of monoids is univalent
*)

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Algebra.Monoids_and_Groups.

Local Open Scope Cat.

(** * Category of monoids *)
(** One can define the monoid precategory first, but this is
    cleaner/faster. The coercions allow one to get the precategory
    anyway, if one wishes.
*)

Section def_monoid_category.

  Definition monoid_category : category.
  Proof.
    use makecategory.
    exact monoid.
    exact monoidfun.
    exact isasetmonoidfun.
    use idmonoidiso.
    do 3 intro. exact monoidfuncomp.
    do 2 intro. exact monoidfunidleft.
    do 2 intro. exact monoidfunidright.
    do 4 intro. exact monoidfunassoc.
  Defined.

End def_monoid_category.
(** * Characterising isomorphisms in the monoid category *)

Section char_monoid_iso.

  Lemma monoidiso_is_monoid_cat_iso (X Y : monoid_category) : monoidiso X Y -> z_iso X Y.
  Proof.
    intro f.
    set (g := invmonoidiso f).
    use mk_z_iso.
    - use (f : monoidfun X Y).
    - use (g : monoidfun Y X).
    - use mk_is_inverse_in_precat.
      + use monoidfun_paths. use funextfun. intro x. use homotinvweqweq.
      + use monoidfun_paths. use funextfun. intro y. use homotweqinvweq.
  Defined.

  Lemma monoidiso_is_equiv (X Y : monoid_category) (z_f : z_iso X Y) : isweq (pr1 (pr1 z_f)).
  Proof.
    unfold z_iso in z_f.
    induction z_f as [f h]. induction h as [g h']. induction h' as [p q].
    use isweq_iso.
    - use (g : monoidfun Y X).
    - intro x. unfold identity in p. unfold monoid_category in p.
      simpl in p. unfold compose in p. simpl in p. simpl.
      admit.
    - intro y. unfold identity in q. unfold monoid_category in q.
      simpl in q. unfold compose in q. simpl in q. simpl.
      admit.
  Admitted.

  Lemma monoid_cat_iso_is_monoidiso (X Y : monoid_category) : z_iso X Y -> monoidiso X Y.
  Proof.
    intro f.
    use monoidisopair.
    - use weqpair.
      + exact (pr1 (pr1 f)).
      + exact (monoidiso_is_equiv X Y f).
    - exact (pr2 (pr1 f)).
  Defined.

  Lemma monoidiso_is_monoid_cat_iso_is_equiv (X Y : monoid_category) : isweq (monoidiso_is_monoid_cat_iso X Y).
  Proof.
    - Search isweq.


End char_monoid_iso.

Definition monoid_univalent_category : univalent_category.
Proof.
  use mk_category.
  - exact monoid_category.
  - use mk_is_univalent.
    + intros X Y. exact (monoid_univalence_isweq X Y).
      apply monoid_univalence_isweq.
      unfold idtoiso. unfold isweq. intro. unfold iscontr.