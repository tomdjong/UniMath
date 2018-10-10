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

  Lemma monoidiso_is_monoid_cat_iso (X Y : ob monoid_category) : monoidiso X Y -> z_iso X Y.
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

  Lemma monoid_cat_iso_is_isweq {X Y : ob monoid_category} (f : X --> Y) : is_z_isomorphism f -> isweq (pr1 f).
  Proof.
    intro z_f. unfold is_z_isomorphism in z_f.
    induction z_f as [g h']. induction h' as [p q].
    use isweq_iso.
    - use (g : monoidfun Y X).
    - use toforallpaths. exact (maponpaths pr1 p).
    - use toforallpaths. exact (maponpaths pr1 q).
  Defined.

  Lemma monoid_cat_iso_is_monoidiso (X Y : ob monoid_category) : z_iso X Y -> monoidiso X Y.
  Proof.
    intro f.
    use monoidisopair.
    - use weqpair.
      + exact (pr1 (pr1 f)).
      + exact (monoid_cat_iso_is_isweq (pr1 f) (pr2 f)).
    - exact (pr2 (pr1 f)).
  Defined.

  (* Lemma monoidiso_is_monoid_cat_iso_is_equiv (X Y : ob monoid_category) : isweq (monoidiso_is_monoid_cat_iso X Y).
  Proof.
    use isweq_iso.
    - exact (monoid_cat_iso_is_monoidiso X Y).
    - intro f. use monoidiso_paths.  use subtypeEquality.
      + unfold isPredicate. intro x. use isapropisweq.
      + use idpath.
    - intro g. use eq_z_iso.
      + exact (homset_property monoid_category).
      + use monoidfun_paths. use idpath.
  Defined. *)

  Lemma monoidiso_is_monoid_cat_iso_equiv (X Y : ob monoid_category) : monoidiso X Y ≃ z_iso X Y.
  Proof.
    use weqpair.
    - exact (monoidiso_is_monoid_cat_iso X Y).
    - use isweq_iso.
      + exact (monoid_cat_iso_is_monoidiso X Y).
      + intro f. use monoidiso_paths.  use subtypeEquality.
        * unfold isPredicate. intro x. use isapropisweq.
        *use idpath.
      + intro g. use eq_z_iso.
        * exact (homset_property monoid_category).
        * use monoidfun_paths. use idpath.
  Defined.

End char_monoid_iso.

Definition monoid_univalent_category : univalent_category.
Proof.
  use mk_category.
  - exact monoid_category.
  - use mk_is_univalent.
    + intros X Y.
      use isweqhomot.
      *
        exact (
            funcomp (funcomp (monoid_univalence_map X Y) (monoidiso_is_monoid_cat_iso X Y)) (invmap z_isomorphism_iso_equiv)).
      * intro t. induction t. unfold funcomp.  use total2_paths_f.
        ** use idpath.
        ** unfold transportf. use proofirrelevance. use isaprop_is_iso.
      * Search invmap.