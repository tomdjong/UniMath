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

Definition η' {Y: UU} : (unit -> Y) -> Ł Y := λ f, (unit,, f).

Lemma maponpaths_η'_form {Y : UU} {f g : unit -> Y} (e : f = g) :
  maponpaths η' e = @total2_paths_f _ _ (unit,, f) (unit,, g) (idpath unit) e.
Proof.
  induction e. use idpath.
Qed.

Lemma η'_eq_form' {Y : UU} {f g : unit -> Y} (q : η' f = η' g) :
  let e := unit_is_unit_isproofirrelevant (base_paths _ _ q) (idpath unit) in
  (base_paths _ _ q,, fiber_paths q) = (idpath unit,,
                      (transportf (λ v : unit = unit, transportf
                                                        (λ P : UU, P -> Y) v f = g)
                                  e (fiber_paths q))).
Proof.
  simpl. use transportf_eq.
Defined.

Definition sum_eq_to_pair {A : UU} {B : A -> UU} {x y : ∑ (x : A), B x} : x = y -> x ╝ y.
Proof.
  use total2_paths_equiv.
Defined.

Definition section {Y : UU} {f g : unit -> Y} :
  η' f = η' g -> f = g.
Proof.
  intro q.
  set (e := unit_is_unit_isproofirrelevant (base_paths _ _ q) (idpath unit)).
  exact (transportf (λ v : unit = unit, transportf
                                                        (λ P : UU, P -> Y) v f = g)
                    e (fiber_paths q)).
Defined.

(* Definition maponpaths_η'_is_retract {Y : UU} {f g : unit -> Y} :
  ∑ (s : η' f = η' g -> f = g), (maponpaths η') ∘ s ~ idfun _.
Proof.
  split with section. unfold idfun. unfold funcomp.
  intro q.
  rewrite maponpaths_η'_form.
  set (e := unit_is_unit_isproofirrelevant (base_paths _ _ q) (idpath unit)).
  unfold section.
  assert (eq : q = @total2_paths_f _ _ (unit,, f) (unit,, g) (idpath unit)
                                  (transportf (λ v : unit = unit, transportf
                                                        (λ P : UU, P -> Y) v f = g)
                                              e (fiber_paths q))).
  {
    etrans.
    - apply pathsinv0. apply total2_fiber_paths.
    - admit. }
  change (unit_is_unit_isproofirrelevant (base_paths _ _ q) _) with e.
  exact (! eq).
Admitted. *)

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

Definition fiber_into_defined {Y : UU} {l : lift Y} :
  (∑ (y : Y), lift_embedding y = l) -> defined l.
Proof.
  intro fib. induction fib as [y q].
  set (q1 := base_paths _ _ q). simpl in q1.
  exact (transportf (λ Q : UU, Q) q1 (tt : unit)).
Defined.

Definition retraction_fiber_into_defined {Y : UU} {l : lift Y} :
  defined l -> ∑ (y : Y), lift_embedding y = l.
Proof.
  intro p. induction l as [P pair]. induction pair as [i f].
  split with (f p).
  unfold lift_embedding.
  use total2_paths_f.
  - simpl. admit.
  - simpl. admit.
Admitted.

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