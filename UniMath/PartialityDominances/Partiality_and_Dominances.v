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

(* Definition eq_to_lift_embedding_eq {Y : UU} {y y' : Y} :
  y = y' -> lift_embedding y = lift_embedding y'.
Proof.
  intro e.
  exact (maponpaths lift_embedding e).
Defined. *)
(*
  unfold lift_embedding.
  apply total2_paths_equiv. unfold PathPair. simpl.
  split with (idpath unit).
  set (transportf_idpath :=
         idpath_transportf (λ x : UU, isaprop x × (x -> Y)) (isapropunit,, (λ _ : unit, y))).
  rewrite transportf_idpath.
  use dirprodeq.
  - simpl. use idpath.
  - simpl. use funextfun. intro u. exact e.
Defined.
*)

Definition eq_is_trans {X : UU} {x y z : X} : x = y -> y = z -> x = z.
Proof.
  intros p q. rewrite p. rewrite q. use idpath.
Defined.

Definition eq_is_sym {X : UU} {x y : X} : x = y -> y = x.
Proof.
  intro p. rewrite p. use idpath.
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
    exact (eq_is_trans eq1 (eq_is_sym eq2)).
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

Definition lift_embedding_is_embedding {Y : UU}: @isInjective Y _ lift_embedding.
Proof.
  unfold isInjective.
  intros y y'.
  use isweq_iso.
  - exact (lift_embedding_eq_to_eq).
  - intro e.
    unfold lift_embedding_eq_to_eq. simpl.

    change (λ p : unit = unit,
           transportf (λ x : UU, isaprop x × (x → Y)) p (isapropunit,, (λ _ : unit, y)) =
           isapropunit,, (λ _ : unit, y'))
    with
    (λ p : unit = unit,
           transportf (λ x : UU, isaprop x × (x → Y)) (idpath unit) (isapropunit,, (λ _ : unit, y)) =
           isapropunit,, (λ _ : unit, y')).

    change (λ p : unit = unit, (transportf (λ x : UU, isaprop x × (x -> Y)) p (isapropunit,, (λ _ : unit, y)))) with
    (λ p : unit = unit, (transportf (λ x : UU, isaprop x × (x -> Y)) (idpath unit) (isapropunit,, (λ _ : unit, y)))).

    unfold maponpaths. unfold lift_embedding_eq_to_eq. simpl. unfold maponpaths. simpl. admit.
  - intro e'.

    Search maponpaths. unfold maponpaths. Search paths_rect.
    unfold lift_embedding_eq_to_eq. simpl.
    Search isweq.
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