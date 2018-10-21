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

Definition unit_is_unit_isproofirrelevant : isProofIrrelevant(unit = unit).
Proof.
  use proofirrelevance.
  use isapropifcontr.
  exact (unit_is_unit_iscontr).
Defined.

(* A function is an embedding if it has propositional fibers *)
Definition is_embedding {X Y : UU} (f : X -> Y) : UU := ∏ (y : Y), isaprop (∑ (x : X), f x = y).

Lemma test (X : UU) (p : isaprop X) : isProofIrrelevant (unit = X).
Proof.
  admit.
Admitted.

(*
Lemma lift_eq_isaprop {Y : UU} (y : Y) (l : lift Y) : isaprop(lift_embedding y = l).
Proof.
  use invproofirrelevance.
  unfold isProofIrrelevant. intros u v.
  unfold lift_embedding in u. unfold lift_embedding in v.
  unfold lift in l.
  induction l as [l1 l2].
  induction u.
 *)

Definition lift_embedding_eq_to_eq {Y : UU} {y y' : Y} :
  lift_embedding y = lift_embedding y' -> y = y'.
Proof.
  intro u.
  apply total2_paths_equiv in u. unfold PathPair in u. simpl in u.
  induction u as [u1 u2].
  set (u1isid := unit_is_unit_isproofirrelevant u1 (idpath unit)).
  rewrite u1isid in u2. rewrite (idpath_transportf _ _) in u2.
  set (u3 := maponpaths dirprod_pr2 u2). simpl in u3.
  exact (eqtohomot u3 tt).
Defined.

Definition lift_embedding_eq_equiv {Y : UU} {y y' : Y} :
  y = y' ≃ lift_embedding y = lift_embedding y'.
Proof.
  use weqpair.
  - exact (maponpaths lift_embedding).
  - use isweq_iso.
    + exact lift_embedding_eq_to_eq.
    + intro u. admit.
    + intro v. simpl. unfold maponpaths. simpl.

      unfold lift_embedding_eq_to_eq. simpl.
      Search isweq.
Lemma lift_embedding_is_embedding {Y : UU} : is_embedding (@lift_embedding Y).
Proof.
  unfold is_embedding. intro l.
  use invproofirrelevance.
  unfold isProofIrrelevant.
  intros p q.
  induction p as [y_p p']. induction q as [y_q q'].
  assert (yeq : y_p = y_q).
  {
    assert (r : lift_embedding y_p = lift_embedding y_q).
    { rewrite p'. rewrite q'. use idpath. }
    apply total2_paths_equiv in r. unfold PathPair in r.
    induction r as [r1 r2]. unfold lift_embedding in r1. simpl in r1.
    set (r1isid := unit_is_unit_isproofirrelevant r1 (idpath unit)).
    rewrite r1isid in r2. rewrite (idpath_transportf _ _) in r2.
    unfold lift_embedding in r2. simpl in r2.
    set (r3 := maponpaths dirprod_pr2 r2). simpl in r3.
    rewrite (eqtohomot r3 tt). use idpath.
  }
  apply total2_paths_equiv. unfold PathPair.
  simpl. split with yeq.
  induction p'.

  assert (transportf (λ x : Y, lift_embedding x = lift_embedding y_p) yeq (idpath (lift_embedding y_p)) = idpath (lift_embedding y_q)).
  {
  change (transportf (λ x : Y, lift_embedding x = lift_embedding y_p) yeq (idpath (lift_embedding y_p))) with (maponpaths lift_embedding yeq).
  apply total2_paths_equiv in q'.
  unfold lift_embedding in q'.
  set (q'1 := maponpaths pr1 q'). simpl in q'1.
  unfold transportf. unfold constr1. simpl.

  destruct q'.
  set (q'2 := maponpaths r1 q'1) q'). simpl in q'2.






















(*

  unfold lift_embedding.
  intros p q. induction p as [x p']. induction q as [y q'].
  apply total2_paths_equiv.
  unfold PathPair. simpl.
  assert (eq : x = y).
  {
    apply total2_paths_equiv in p'. unfold PathPair in p'. simpl in p'.
    apply total2_paths_equiv in q'. unfold PathPair in q'. simpl in q'.
    induction p' as [puniteq ptranseq]. induction q' as [quniteq qtranseq].
    set (eq' := test (pr1 l) (pr1 (pr2 l)) puniteq quniteq).
    rewrite eq' in ptranseq.

    assert (eq'' : transportf (λ x : UU, isaprop x × (x -> Y)) quniteq (isapropunit,, (λ _ : unit, x)) = transportf (λ x : UU, isaprop x × (x -> Y)) puniteq (isapropunit,, (λ _ : unit, y))).
    {
      rewrite ptranseq. rewrite

    generalize ptranseq. generalize puniteq.
    rewrite quniteq. *)

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