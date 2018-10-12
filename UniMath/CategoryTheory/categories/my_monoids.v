(** * Category of monoids *)
(** ** Contents
- Category of monoids
- Characterising isomorphisms of monoid category as monoid isomorphisms
- Category of monoids is univalent
*)

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Algebra.Monoids_and_Groups.

Local Open Scope Cat.

(** ** Category of monoids *)

Definition monoid_category : category.
Proof.
  use makecategory.
  - exact monoid.
  - exact monoidfun.
  - exact isasetmonoidfun.
  - use idmonoidiso.
  - do 3 intro. exact monoidfuncomp.
  - do 2 intro. exact monoidfunidleft.
  - do 2 intro. exact monoidfunidright.
  - do 4 intro. exact monoidfunassoc.
Defined.

(** ** Characterising isomorphisms in the monoid category as monoid isomorphisms *)

Definition monoidiso_is_monoid_cat_z_iso {X Y : ob monoid_category} : monoidiso X Y -> z_iso X Y.
Proof.
  intro f. set (g := invmonoidiso f).
  use mk_z_iso.
  - use (f : monoidfun X Y).
  - use (g : monoidfun Y X).
  - use mk_is_inverse_in_precat.
    + use monoidfun_paths. use funextfun. intro x. use homotinvweqweq.
    + use monoidfun_paths. use funextfun. intro y. use homotweqinvweq.
Defined.

Definition monoid_cat_z_iso_isweq {X Y : ob monoid_category} (f : X --> Y) :
  is_z_isomorphism f -> isweq (pr1 f).
Proof.
  intro z_f. unfold is_z_isomorphism in z_f.
  induction z_f as [g h']. induction h' as [p q].
  use isweq_iso.
  - use (g : monoidfun Y X).
  - use toforallpaths. exact (maponpaths pr1 p).
  - use toforallpaths. exact (maponpaths pr1 q).
Defined.

Definition monoid_cat_z_iso_is_monoidiso {X Y : ob monoid_category} : z_iso X Y -> monoidiso X Y.
Proof.
  intro f.
  use monoidisopair.
  - use weqpair.
    + exact (pr1 (pr1 f)).
    + exact (monoid_cat_z_iso_isweq (pr1 f) (pr2 f)).
  - exact (pr2 (pr1 f)).
Defined.

Definition monoidiso_is_monoid_cat_z_iso_equiv (X Y : ob monoid_category) :
  monoidiso X Y ≃ z_iso X Y.
Proof.
  use weqpair.
  - exact (monoidiso_is_monoid_cat_z_iso).
  - use isweq_iso.
    + exact (monoid_cat_z_iso_is_monoidiso).
    + intro f. use monoidiso_paths. use subtypeEquality.
      * unfold isPredicate. intro x. use isapropisweq.
      * use idpath.
    + intro g. use eq_z_iso.
      * exact (homset_property monoid_category).
      * use monoidfun_paths. use idpath.
Defined.

(** ** Category of monoids is univalent **)

Definition monoid_univalent_category : univalent_category.
(** We use the sequence of equivalences:
    -  X = Y ≃ monoidiso X Y (this is monoid_univalence from Monoids_and_Groups)
    -  monoidiso X Y ≃ z_iso X Y (proven above)
    -  z_iso X Y ≃ iso X Y (this is z_isomorphism_iso_equiv from Categories) *)
Proof.
  use mk_category.
  - exact monoid_category.
  - use mk_is_univalent.
    + intros X Y.
      set (equiv_comp := weqcomp (monoid_univalence X Y)
             (weqcomp (monoidiso_is_monoid_cat_z_iso_equiv X Y) (z_isomorphism_iso_equiv X Y))).
      use isweqhomot.
      * exact (pr1 equiv_comp).
      * intro p. induction p. use subtypeEquality.
        ** unfold isPredicate. intro f. use isaprop_is_iso.
        ** use idpath.
      * exact (pr2 equiv_comp).
    + exact (homset_property monoid_category).
Defined.