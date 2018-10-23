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

Lemma fun_unit_is_unit_isproofirrelevant {Y : UU} {y y' : Y} :
  (λ e : unit = unit,
         transportf (λ x : UU, isaprop x × (x → Y)) e (isapropunit,, (λ _ : unit, y)))
  = (λ e : unit = unit, (isapropunit,, (λ _ : unit, y))).
Proof.
  use funextfun. intro p.
  set (eq := unit_is_unit_isproofirrelevant p (idpath unit)).
  rewrite eq. rewrite idpath_transportf. use idpath.
Qed.

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

Definition maponmaps_lift_embedding_is_retract {Y : UU} (y y' : Y):
  ∑ (s : lift_embedding y = lift_embedding y' -> y = y'),
  (maponpaths lift_embedding) ∘ s ~ idfun _.
Proof.
  split with maponpaths_lift_embedding_section.
  intro q. unfold idfun. unfold funcomp.
  unfold lift_embedding in q.
  unfold maponpaths_lift_embedding_section. simpl.
  assert (eq : (λ e : unit = unit,
                transportf (λ x : UU, isaprop x × (x → Y)) e (isapropunit,, (λ _ : unit, y)))
               = (λ e : unit = unit, (isapropunit,, (λ _ : unit, y)))).
  {
    use funextfun. intro e.
    set (eq := unit_is_unit_isproofirrelevant e (idpath unit)).
    rewrite eq. rewrite idpath_transportf. use idpath.
  }
  rewrite eq.

  unfold internal_paths_rew.

  assert (eq' : maponpaths pr1 q = idpath unit).
  {
    exact (unit_is_unit_isproofirrelevant (maponpaths pr1 q) (idpath unit)).
  }

  rewrite eq'.
  unfold unit_is_unit_isproofirrelevant.
  assert (e : (unit_is_unit_isproofirrelevant (maponpaths pr1 q) (idpath unit)) = idpath (unit=unit)).
  rewrite fun_unit_is_unit_isproofirrelevant.

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