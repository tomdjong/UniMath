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

Lemma unit_is_unit_iscontr : iscontr(unit = unit).
Proof.
  use isofhlevel0pathspace. (* Note that this uses univalence *)
  - exact (iscontrunit).
  - exact (iscontrunit).
Qed.

Lemma unit_is_unit_isproofirrelevant : isProofIrrelevant(unit = unit).
Proof.
  use proofirrelevance.
  use isapropifcontr.
  exact (unit_is_unit_iscontr).
Qed.

(* Easier example? *)
Definition Ł (Y : UU) : UU := ∑ (P : UU), (P -> Y).

Definition η' {Y: UU} : (unit -> Y) -> Ł Y := λ f, unit,, f.

Definition maponpaths_η'_section {Y : UU} {f g : unit -> Y} :
  η' f = η' g -> f = g.
Proof.
  unfold η'. intro q. set (q' := fiber_paths q).
  unfold base_paths in q'. simpl in q'.
  set (eq := unit_is_unit_isproofirrelevant (maponpaths pr1 q) (idpath unit)).
  set (q'' := maponpaths (λ e : unit = unit, transportf (λ x : UU, x -> Y) e f) eq).
  simpl in q''.
  set (q''' := idpath_transportf (λ x : UU, x -> Y) f).
  exact ((! q''') @ (! q'') @ q').
Defined.

Lemma maponpaths_η'_form {Y : UU} {f g : unit -> Y} (e : f = g) :
  maponpaths η' e = @total2_paths_f _ _ (unit,, f) (unit,, g) (idpath unit) e.
Proof.
  induction e. use idpath.
Qed.

Lemma η'_eq_first_component {Y : UU} {f g : unit -> Y} (q : η' f = η' g) :
  base_paths _ _ q = idpath unit.
Proof.
  exact (unit_is_unit_isproofirrelevant _ _).
Qed.

Definition maponpaths_η'_is_retract {Y : UU} {f g : unit -> Y} :
  ∑ (s : η' f = η' g -> f = g), (maponpaths η') ∘ s ~ idfun _.
Proof.
  split with maponpaths_η'_section. unfold idfun. unfold funcomp.
  intro q.
  unfold maponpaths_η'_section. simpl.
  rewrite maponpaths_η'_form.
  rewrite <- total2_fiber_paths.

  assert (eq : (base_paths (η' f) (η' g) q) = idpath unit).
  { exact (unit_is_unit_isproofirrelevant _ _). }
  assert (eq2 : maponpaths_η'_section q = fiber_paths q). { admit. }
  unfold maponpaths_η'_section.

  simpl.
  rewrite (@η'_eq_first_component Y f g q).
  unfold η' in q.
  rewrite maponpaths_η'_triv_first_component. unfold invmap. simpl.
  rewrite (idpath_transportf _ _).
  apply (invmap (total2_paths_equiv _ (maponpaths η' (maponpaths_η'_section q)) q)).

  unfold maponpaths_η'_section. simpl.
  rewrite maponpaths_η'_triv_first_component.
  apply (total2_paths_equiv).

  unfold fiber_paths.
  use total2_paths_equiv.
  rewrite <- maponpathsinv0.
Definition maponpaths_lift_embedding_section {Y : UU} {y y' : Y} :
  lift_embedding y = lift_embedding y' -> y = y'.
Proof.
  intro q. unfold lift_embedding in q.
  set (q1 := unit_is_unit_isproofirrelevant (maponpaths pr1 q) (idpath unit)).
  set (q2 := fiber_paths q). unfold base_paths in q2.
  simpl in q2.
  set (q2' := maponpaths
                (λ e : unit=unit, transportf (λ x : UU, isaprop x × (x → Y)) e
                (isapropunit,, (λ _ : unit, y))) q1).
  simpl in q2'.
  set (q3 := idpath_transportf (λ x : UU, isaprop x × (x -> Y)) (isapropunit,, λ _ : unit, y)).

  set (q4 := ! q3 @ ! q2' @ q2).
  set (q5 := (maponpaths dirprod_pr2) q4).
  exact (maponpaths (λ f, f tt) q5).
  (* rewrite q1 in q2. rewrite (idpath_transportf _ _) in q2. *)
  (*  set (eq1 := (maponpaths dirprod_pr2) q2). simpl in eq1.
  exact (maponpaths (λ f, f tt) eq1). *)
Defined.

Definition maponmaps_lift_embedding_is_section {Y : UU} (y y' : Y):
  ∑ (s : lift_embedding y = lift_embedding y' -> y = y'),
  (maponpaths lift_embedding) ∘ s ~ idfun _.
Proof.
  split with maponpaths_lift_embedding_section.
  unfold idfun. unfold funcomp. intro e.
  unfold maponpaths_lift_embedding_section. simpl.

Definition maponmaps_lift_embedding_is_retraction {Y : UU} (y y' : Y):
  ∑ (s : lift_embedding y = lift_embedding y' -> y = y'),
  (maponpaths lift_embedding) ∘ s ~ idfun _.
Proof.
  split with maponpaths_lift_embedding_section.
  unfold idfun. unfold funcomp. simpl. intro q.
  change (unit,, isapropunit,, (λ _ : unit, y) = unit,, isapropunit,, (λ _ : unit, y')) with
      (unit,, isapropunit,, (λ _ : unit, y) ╝ unit,, isapropunit,, (λ _ : unit, y')).
  rewrite (total2_paths_equiv  (λ P : UU, isaprop P × (P -> Y))
                               (unit,, isapropunit,, (λ _ : unit, y))
                               (unit,, isapropunit,, (λ _ : unit, y'))
          ) in q.

  unfold maponpaths_lift_embedding_section. simpl.
  Check (fiber_paths q).
  unfold fiber_paths. simpl. unfold base_paths.

  rewrite <- total2_fiber_paths. unfold base_paths. simpl.
  unfold paths_rect.
  set (q' := maponpaths pr2 q).
  simpl.
  set (
      e :=  (maponpaths dirprod_pr2
          (! maponpaths
               (λ e : unit = unit,
                transportf (λ x : UU, isaprop x × (x → Y)) e (isapropunit,, (λ _ : unit, y)))
               (unit_is_unit_isproofirrelevant (maponpaths pr1 q) (idpath unit)) @
               fiber_paths q))).
  change
    ( (maponpaths dirprod_pr2
          (! maponpaths
               (λ e : unit = unit,
                transportf (λ x : UU, isaprop x × (x → Y)) e (isapropunit,, (λ _ : unit, y)))
               (unit_is_unit_isproofirrelevant (maponpaths pr1 q) (idpath unit)) @
               fiber_paths q))) with e.
  rewrite (maponpathscomp (λ f : unit -> Y, f tt) lift_embedding e).
  (*rewrite (maponpathscomp (λ f : unit -> Y, f tt) lift_embedding _).*) admit.
Admitted.

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