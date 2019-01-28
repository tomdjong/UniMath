(**

Tom de Jong

Created: October - November 2018

Refactored: January 2019

*******************************************************************************)

(** * Partial Elements *)
(** ** Contents
- Definition of Partial Elements of X (or Lift (𝓛 X) of X) ([lift])
  , basic lemmas on [isdefined] and [value] and a (logical) characterisation
  of equality on 𝓛 X
- An order on the lift of X ([liftorder])
- The lift of X as a dcpo with bottom ([liftdcpo])
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PropExt.
Require Import UniMath.MoreFoundations.WeaklyConstant.
Require Import UniMath.Algebra.DCPO.

(** * The lift of a type *)

Delimit Scope PartialElements with PartialElements.
Local Open Scope PartialElements.

Section lift.

Definition lift (X : UU) := ∑ (P : UU), isaprop P × (P -> X).

Notation "'𝓛'" := lift : PartialElements.

Definition lift_embedding {X : UU} (x : X) : 𝓛 X :=
  (unit,, isapropunit,, termfun x).

Notation "'η'" := lift_embedding : PartialElements.

Definition isdefined {X : UU} (l : 𝓛 X) : UU := pr1 l.

Lemma isaprop_isdefined {X : UU} (l : 𝓛 X) : isaprop (isdefined l).
Proof.
  induction l as [P pair].
  exact (pr1 pair).
Qed.

Definition lifteq_isdefined {X : UU} {l m : 𝓛 X} :
  l = m -> isdefined l -> isdefined m.
Proof.
  intros eq dl.
  eapply transportf.
  - exact eq.
  - exact dl.
Defined.

Definition value {X : UU} (l : 𝓛 X) : isdefined l -> X.
Proof.
  induction l as [P pair].
  exact (pr2 pair).
Defined.

Definition weaklyconstant_value {X : UU} (l : 𝓛 X) : weaklyconstant (value l).
Proof.
  intros p q.
  apply maponpaths.
  apply proofirrelevance.
  apply isaprop_isdefined.
Defined.

Definition lifteq_valueeq {X : UU} {l m : 𝓛 X} :
  l = m -> ∏ (d : isdefined l), ∏ (d' : isdefined m), value l d = value m d'.
Proof.
  intros eq d d'. induction eq. apply weaklyconstant_value.
Defined.

Definition lifteq_necc {X : UU} {l m : 𝓛 X} :
  l = m -> ∑ (e : isdefined l <-> isdefined m), value l ∘ pr2 e ~ value m.
Proof.
  intro eq.
  apply total2_paths_equiv in eq.
  induction eq as [e1 e2].
  exists (weq_to_iff (eqweqmap e1)).
  intro d.
  assert (lem : value l ∘ pr2 (weq_to_iff (eqweqmap e1)) =
                pr2 (transportf _ e1 (pr2 l))).
  { generalize e1 as e1'; induction e1'; apply idpath. }
  etrans.
  + apply (eqtohomot lem).
  + change (value m d) with (pr2 (pr2 m) d).
    use eqtohomot.
    exact (maponpaths dirprod_pr2 e2).
Defined.


Definition lifteq_suff {X : UU} {l m : 𝓛 X} :
  (∑ (e : isdefined l <-> isdefined m), value l ∘ pr2 e ~ value m) -> l = m.
Proof.
  intros [e veq].
  apply total2_paths_equiv.
  assert (eq : isdefined l = isdefined m).
  { apply propext.
    - apply isaprop_isdefined.
    - apply isaprop_isdefined.
    - exact e. }
  split with eq.
  apply dirprod_paths.
  + apply proofirrelevance. apply isapropisaprop.
  + assert (lem : pr2 (transportf _ eq (pr2 l)) = value l ∘ pr2 e).
    { assert (inveq : invmap (eqweqmap eq) = pr2 e).
      { apply funextfun. intro d. apply proofirrelevance.
        apply isaprop_isdefined. }
      rewrite <- inveq.
      generalize eq as eq'; induction eq'; apply idpath. }
    etrans.
    ++ apply lem.
    ++ apply funextfun. exact veq.
Defined.

End lift.

(** * The 'order' on the lift *)
Section liftorder.

Notation "'𝓛'" := lift : PartialElements.

Definition liftorder {X : UU} (l m : 𝓛 X) : UU :=
  isdefined l -> l = m.

Notation "l ⊑ m" := (liftorder l m) (at level 30) : PartialElements.

Definition liftorder_antisymmetric {X : UU} :
  ∏ (l m : 𝓛 X), l ⊑ m -> m ⊑ l -> l = m.
Proof.
  intros l m ineqlm ineqml.
  apply lifteq_suff.
  assert (e : isdefined l <-> isdefined m).
  { split.
    - intro dl.
      eapply lifteq_isdefined.
      + exact (ineqlm dl).
      + exact dl.
    - intro dm.
      eapply lifteq_isdefined.
      + exact (ineqml dm).
      + exact dm. }
  exists e.
  intro dm.
  apply lifteq_valueeq.
  exact (!(ineqml dm)).
Defined.

Definition liftorder_reflexive {X : UU} : ∏ (l : 𝓛 X), l ⊑ l.
Proof.
  intros l d.
  apply idpath.
Defined.

Definition liftorder_transitive {X : UU} :
  ∏ (l m n : 𝓛 X), l ⊑ m -> m ⊑ n -> l ⊑ n.
Proof.
  intros l m n ineqlm ineqmn.
  intro dl.
  etrans.
  - exact (ineqlm dl).
  - apply ineqmn.
    exact (transportf isdefined (ineqlm dl) dl).
Defined.

Definition liftorder_least {X : UU} : 𝓛 X := (empty,, isapropempty,, fromempty).
Notation "'⊥'" := liftorder_least : PartialElements.

Definition liftorder_least_isleast {X : UU} : ∏ (l : 𝓛 X), ⊥ ⊑ l.
Proof.
  intro l. intro dbot.
  induction dbot.
Defined.

End liftorder.

(** * The lift as a dcpo with bottom *)
Section liftdcpo.

Notation "'𝓛'" := lift : PartialElements.
Notation "l ⊑ m" := (liftorder l m) (at level 30) : PartialElements.

Lemma liftofhset_isaset {X : hSet} : isaset (𝓛 X).
Proof.
  intros l m.
  eapply (isapropretract) with (f := (total2_paths_equiv _ l m))
                               (g := invmap (total2_paths_equiv _ l m)).
  - apply isofhleveltotal2.
    + apply isaprop_pathsprop.
      1-2: apply isaprop_isdefined.
    + intros eq.
      assert (helper : isaset (isaprop (pr1 m) × ((pr1 m) -> X))).
      { apply isaset_dirprod.
        - apply isasetaprop. apply isapropisaprop.
        - apply isaset_set_fun_space. }
      apply helper.
  - use homotinvweqweq.
Qed.

Lemma liftorder_ispropvalued {X : hSet} : ∏ (l m : 𝓛 X), isaprop (l ⊑ m).
Proof.
  intros l m.
  unfold liftorder.
  apply isapropimpl.
  apply liftofhset_isaset.
Qed.

Close Scope PartialElements.

Definition liftofhSet (X : hSet) : hSet := hSetpair (lift X) liftofhset_isaset.
Delimit Scope LiftIsPoset with LiftIsPoset.
Local Open Scope LiftIsPoset.

Definition liftorder_hrel {X : hSet} (l m : liftofhSet X) :=
  hProppair (liftorder l m) (liftorder_ispropvalued l m).

Notation "l ⊑ m" := (liftorder_hrel l m) (at level 30) : LiftIsPoset.

Definition liftposet (X : hSet) : Poset.
Proof.
  use Posetpair.
  - exact (liftofhSet X).
  - exists liftorder_hrel.
    unfold isPartialOrder. split.
    + unfold ispreorder. split.
      * use liftorder_transitive.
      * use liftorder_reflexive.
    + use liftorder_antisymmetric.
Defined.

Notation "'𝓛'" := liftposet : LiftIsPoset.

(** The following map will be used to define the value of the lub of a
   (directed) family. *)
Definition lubvaluemap {X : hSet} {I : UU} (u : I -> 𝓛 X) :
                       (∑ (i : I), isdefined (u i)) -> X.
Proof.
  intros [i d].
  exact (value (u i) d).
Defined.

(** The map is weakly constant if the family is directed. *)
Definition lubvaluemap_weaklyconstant {X : hSet} {I : UU} (u : I -> 𝓛 X) :
  isdirected u -> weaklyconstant (lubvaluemap u).
Proof.
  intros isdirec [i d] [i' d'].
  apply (@factor_through_squash (directeduntruncated u i i')).
  - apply setproperty.
  - intros [k ineqs].
    unfold lubvaluemap.
    apply lifteq_valueeq.
    etrans.
    + exact (pr1 ineqs d).
    + exact (!(pr2 ineqs d')).
  - exact (isdirected_order isdirec i i').
Defined.

(** The construction of the lub; a proof that this element is actually
    the lub follows later. *)
Definition mkdirectedlubinlift {X : hSet} {I : UU} {u : I -> 𝓛 X}
           (isdirec : isdirected u) : 𝓛 X.
Proof.
  exists (∥∑ (i : I), isdefined (u i)∥).
  split.
  - apply isapropishinh.
  - eapply weaklyconstanttoaset_factorsthroughsquash.
    + apply setproperty.
    + apply lubvaluemap_weaklyconstant.
      exact isdirec.
Defined.

Lemma isdefinedlub_toprop {X : hSet} {I Q : UU} {u : I -> 𝓛 X}
      (isdirec : isdirected u) :
  ((∑ (i : I), isdefined (u i)) -> Q) ->
  isaprop Q ->
  isdefined (mkdirectedlubinlift isdirec) -> Q.
Proof.
  intros f Qisaprop p.
  exact (factor_through_squash Qisaprop f p).
Qed.

Lemma liftlub_isdefined {X : hSet} {I : UU} {u : I -> 𝓛 X}
      (isdirec : isdirected u) :
  ∏ (i : I), isdefined (u i) -> u i = mkdirectedlubinlift isdirec.
Proof.
  intros i di.
  apply lifteq_suff.
  assert (e : isdefined (u i) <-> isdefined (mkdirectedlubinlift isdirec)).
  { split.
    - exact (λ d, hinhpr (i,,d)).
    - exact (λ _, di). }
  exists e.
  intro d.
  unfold mkdirectedlubinlift; cbn.
  assert (dinsquash : d = hinhpr (i,,di)).
  { apply proofirrelevance, isapropishinh. }
  unfold funcomp.
  assert (defeq : pr2 e d = di).
  { apply proofirrelevance, isaprop_isdefined. }
  rewrite defeq.
  change (value (u i) di) with (lubvaluemap u (i,,di)).
  rewrite dinsquash.
  use weaklyconstanttoaset_factorsthroughsquash_eq.
  - apply setproperty.
  - apply weaklyconstant_value.
Qed.

Lemma mkdirectedlubinlift_islub {X : hSet} {I : UU} (u : I -> 𝓛 X)
      (isdirec : isdirected u) : islub u (mkdirectedlubinlift isdirec).
Proof.
  split.
  - intro i.
    intro di.
    exact (liftlub_isdefined isdirec i di).
  - intros v upperbound.
    intro d.
    apply (isdefinedlub_toprop isdirec).
    + intros [i di].
      etrans.
      * exact (!(liftlub_isdefined isdirec i di)).
      * exact (upperbound i di).
    + apply liftofhset_isaset.
    + exact d.
Qed.

Theorem lift_isdirectedcomplete (X : hSet) :
  isdirectedcomplete (𝓛 X).
Proof.
  unfold isdirectedcomplete. intros I u isdirec.
  exists (mkdirectedlubinlift isdirec).
  apply mkdirectedlubinlift_islub.
Qed.
Close Scope LiftIsPoset.

Definition liftdcpo (X : hSet) : dcpo.
Proof.
  eapply dcpopair.
  exact (lift_isdirectedcomplete X).
Defined.

Definition liftdcpowithbottom (X : hSet) : dcpowithbottom.
Proof.
  exists (liftdcpo X).
  exists (empty,, isapropempty,, fromempty).
  intro l.
  intro d.
  induction d.
Defined.

End liftdcpo.