Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Section fix_a_D_and_prop_selection.

Context (D : UU -> UU).

Definition selects_propositions : UU := ∏ X, D X -> isaprop X.

Context (sel : selects_propositions).

Definition lift (Y : UU) := ∑ (P : UU), isaprop P × (P -> Y).

Definition lift_embedding {Y : UU} : Y -> lift Y.
Proof.
  intro y. split with unit. split.
  - exact isapropunit.
  - exact (λ _, y).
Defined.

Definition ispropunit_proj {Y : UU} : isaprop unit × (unit -> Y) -> (unit -> Y) := pr2.

Definition ispropunit_proj_inv {Y : UU} : (unit -> Y) -> (isaprop unit × (unit -> Y)).
Proof.
  intro f. split.
  - exact (isapropunit).
  - exact f.
Defined.

Definition ispropunit_equiv {Y : UU} : isaprop unit × (unit -> Y) ≃ (unit -> Y).
Proof.
  use weqpair.
  - exact ispropunit_proj.
  - use isweq_iso.
    + exact ispropunit_proj_inv.
    + intro pair. induction pair as [p f].
      simpl. unfold ispropunit_proj_inv.
      assert (e : isapropunit = p).
      { use proofirrelevance.
        exact (isapropisaprop unit). }
      rewrite e. use idpath.
    + intro f. use idpath.
Defined.

Lemma unit_is_unit_iscontr : iscontr(unit = unit).
Proof.
  use isofhlevel0pathspace. (* Note that this uses univalence *)
  - exact (iscontrunit).
  - exact (iscontrunit).
Qed.

Definition unit_is_unit_isproofirrelevant : isProofIrrelevant(unit = unit).
Proof.
  use proofirrelevance.
  use isapropifcontr.
  exact (unit_is_unit_iscontr).
Defined.

Lemma unit_is_unit_isproofirrelevant_idpath (e : unit = unit) : unit_is_unit_isproofirrelevant e e = idpath _.
Proof.
  unfold unit_is_unit_isproofirrelevant. unfold proofirrelevance.
  set (eq := iscontr_uniqueness (isapropifcontr unit_is_unit_iscontr e e) (idpath e)).
  rewrite eq. use idpath.
Qed.

Definition mapa {Y : UU} {y y' : Y} :
  (isapropunit,, λ _ : unit, y) = (isapropunit,, λ _ : unit, y') ->
  ∑ (e : unit = unit),
  (transportf (λ P : UU, isaprop P × (P -> Y)) e (isapropunit,, λ _ : unit, y)) =
  (isapropunit,, λ _ : unit, y').
Proof.
  intro u. split with (idpath unit).
  rewrite (idpath_transportf _ _).
  exact u.
Defined.

Definition mapa_inv {Y : UU} {y y' : Y} :
  (∑ (e : unit = unit),
  (transportf (λ P : UU, isaprop P × (P -> Y)) e (isapropunit,, λ _ : unit, y)) =
  (isapropunit,, λ _ : unit, y')) ->
  (isapropunit,, λ _ : unit, y) = (isapropunit,, λ _ : unit, y').
Proof.
  intro v.
  set (v' := pr2 v).
  set (eq := unit_is_unit_isproofirrelevant (pr1 v) (idpath unit)).
  rewrite eq in v'.
  rewrite (idpath_transportf _ _) in v'.
  exact v'.
Defined.

Definition mapa_equiv {Y : UU} {y y' : Y} :
  (∑ (e : unit = unit),
  (transportf (λ P : UU, isaprop P × (P -> Y)) e (isapropunit,, λ _ : unit, y)) =
  (isapropunit,, λ _ : unit, y')) ≃
  (isapropunit,, λ _ : unit, y) = (isapropunit,, λ _ : unit, y').
Proof.
  use weqpair.
  - exact mapa_inv.
  - use isweq_iso.
    + exact mapa.
    + intro v. induction v as [v1 v2].
      set (eq1 := unit_is_unit_isproofirrelevant (idpath unit) v1).
      use total2_paths_f.
      * simpl. exact eq1.
      * simpl. unfold mapa_inv. simpl. rewrite eq1.
        rewrite (idpath_transportf _ _).
        unfold internal_paths_rew.
        rewrite (unit_is_unit_isproofirrelevant_idpath v1).
        use idpath.
    + intro u.
      unfold mapa. simpl. unfold mapa_inv. simpl.
      unfold internal_paths_rew.
      rewrite (unit_is_unit_isproofirrelevant_idpath (idpath unit)).
      use idpath.
Defined.

Definition lift_embedding_eq_to_eq {Y : UU} {y y' : Y} :
  lift_embedding y = lift_embedding y' -> y = y'.
Proof.
  unfold lift_embedding. intro e.
  set (fiber_e := fiber_paths e).
  unfold base_paths in fiber_e. simpl in fiber_e.

  (* We want to show that maponpaths pr1 e = idpath unit *)
  assert (eq : maponpaths pr1 e = idpath unit).
  {
    set (lem := pr2 unit_is_unit_iscontr).
    set (eq1 := lem (maponpaths pr1 e)).
    set (eq2 := lem (idpath unit)).
    rewrite eq2. exact eq1.
  }

  (* Now we use the equality in fiber_e *)
  rewrite eq in fiber_e.
  set (transportf_idpath :=
         idpath_transportf (λ x : UU, isaprop x × (x -> Y)) (isapropunit,, (λ _ : unit, y))).
  rewrite transportf_idpath in fiber_e.

  (* We extract the constant functions *)
  set (const_func_eq := maponpaths dirprod_pr2 fiber_e). simpl in const_func_eq.
  exact ((eqtohomot const_func_eq) tt).
Defined.

(* Try isincl *)

Definition lift_embedding_is_embedding {Y : UU}: @isInjective Y _ lift_embedding.
Proof.
  unfold isInjective. intros y y'.
  use isweqhomot. Search weq.
  - intro e.
    unfold lift_embedding.
    apply total2_paths_equiv.
    unfold PathPair.
    apply mapa.
    apply dirprodeq.
    + simpl. use idpath.
    + simpl. use funextfun. intro u. exact e.
  - intro e. unfold maponpaths. simpl.
    simpl. rewrite (idpath_transportf _ _).

    apply ispropunit_proj.
    apply ispropunit_proj_inv.
    apply (invmap (weqfunfromunit _)).

    set (equiv1 := @maponpaths _ _ (invmap (weqfunfromunit Y)) y y').
    set (equiv2 := @maponpaths _ _ (@ispropunit_proj_inv Y)).
    set (equiv3 := @mapa _ y y').
    set (equiv4 := invmap (total2_paths_equiv
Defined.

Definition D_lift (Y : UU) := ∑ (P : UU), D P × (P -> Y).

(* For there to be an embedding into the D_lift, we need an inhabitant of D unit *)
Definition D_lift_embedding (v : D unit) {Y : UU} : Y -> D_lift Y.
Proof.
  intro y. split with unit. split.
  - exact v.
  - exact (λ _, y).
Defined.

Definition defined  {Y : UU} : lift Y -> hProp.
Proof.
  intro u. induction u as [P pair]. induction pair as [d f].
  unfold hProp. split with P. exact d.
Defined.

Definition value {Y : UU} : ∏ (u : lift Y), (defined u) -> Y.
Proof.
  intro u. induction u as [P pair]. induction pair as [d f].
  simpl. exact f.
Defined.

Definition canonical_embedding {Y : UU} : D_lift Y -> lift Y.
Proof.
  intro h. induction h as [P pair]. induction pair as [d g].
  split with P. split.
  - use sel. exact d.
  - exact g.
Defined.

Definition tame {X Y : UU} : (X -> D_lift Y) -> (X -> lift Y).
Proof.
  intros f x.
  use canonical_embedding.
  exact (f x).
Defined.

Definition is_disciplined {X Y : UU} (f : X -> lift Y) : UU :=
  ∃ (f' : X -> D_lift Y), tame f' = f.

Definition disciplined (X Y : UU) : UU :=
  ∑ f : X -> lift Y, is_disciplined f.

Definition disciplined_carrier {X Y : UU} (m : disciplined X Y) : X -> lift Y :=
  pr1 m.

End fix_a_D_and_prop_selection.

(* Structural dominances *)

Definition sigma_closure (D : UU -> UU) : UU :=
  ∏ (P : UU), ∏ (Q : P -> UU),
  D P -> (∏ (p : P), D (Q p)) ->
  D(∑ (p : P), Q p).

Definition structural_dominance : UU :=
  ∑ (D : UU -> UU), selects_propositions D × D unit × sigma_closure D.

Definition structural_dominance_carrier (struc_dom : structural_dominance) :
  UU -> UU := pr1 struc_dom.
Definition structural_dominance_selection (struc_dom : structural_dominance) :
  selects_propositions (structural_dominance_carrier struc_dom) :=
  pr1 (pr2 struc_dom).