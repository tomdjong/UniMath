Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.PropExt.
Require Import UniMath.MoreFoundations.RetractOfIdentityType.

(* The type of partial elements of a type X is denoted by 𝓛 X, for "lift of X". *)
Definition 𝓛 (X : UU) := ∑ (P : UU), isaprop P × (P -> X).

(* We can map X into its lift. *)
Definition η {X : UU} (x : X) : 𝓛 X := (unit,, isapropunit,, termfun x).

(* We define meaningful projections. *)
Definition isdefined {X : UU} (l : 𝓛 X) : UU := pr1 l.

Definition value {X : UU} (l : 𝓛 X) : isdefined l -> X.
Proof.
  induction l as [P pair]. induction pair as [i f].
  intro p. exact (f p).
Defined.

Lemma isdefined_isaprop {X : UU} (l : 𝓛 X) : isaprop(isdefined l).
Proof.
  induction l as [P pair]. induction pair as [i f]. exact i.
Qed.

(* Lemma on equality of partial elements *)
Lemma isdefined_value_eq {X : UU} {l m : 𝓛 X} (e : isdefined l = isdefined m) :
  transportf (λ Q : UU, Q -> X) e (value l) = value m -> l = m.
Proof.
  intro transp.
  induction l as [P r]. induction r as [i f].
  induction m as [P' r']. induction r' as [i' f'].
  apply total2_paths_equiv.
  unfold isdefined in e. simpl in e.
  split with e. simpl.
  use dirprod_paths.
  - use proofirrelevance. use isapropisaprop.
  - simpl. unfold value in transp. unfold isdefined in transp. simpl in transp.
    change (λ p : P, f p) with f in transp. change (λ p : P', f' p) with f' in transp.
    etrans.
    + assert (eq : pr2 (transportf (λ x : UU, isaprop x × (x -> X)) e (i,, f)) =
              transportf (λ x : UU, (x -> X)) e f).
      { generalize e as e'. intro e'. induction e'. use idpath. }
      exact eq.
    + exact transp.
Defined.

(* It is useful to derive equality of partial elements by using the "order".
   It only is a proper order if the underlying type is a set (TO DO) .*)
Definition information_order {X : UU} (l m : 𝓛 X) : UU :=
  ∑ (t : isdefined l -> isdefined m), ∏ (d : isdefined l), value l d = value m (t d).

Delimit Scope PartialElements with PartialElements.
Local Open Scope PartialElements.

(* TO DO: Check level *)
Notation "l ⊑ m" := (information_order l m) (at level 30) : PartialElements.

Lemma information_order_is_antisymmetric {X : UU} {l m : 𝓛 X} :
  l ⊑ m -> m ⊑ l -> l = m.
Proof.
  intros ineq1 ineq2.
  set (t := pr1 ineq1). set (s := pr1 ineq2).
  set (e := propext (isdefined_isaprop l) (isdefined_isaprop m) (tpair _ t s)).
  apply (isdefined_value_eq e).
  assert (eq : transportf (λ Q : UU, Q -> X) e (value l) = (value l) ∘ (pr1weq (eqweqmap (!e)))).
  { generalize e as e'. induction e'.  use idpath. }
  etrans.
  - exact eq.
  - use funextfun. intro d.
    assert (seq : pr1weq (eqweqmap (!e )) = s).
    {
      use funextfun. intro p. use proofirrelevance. use isdefined_isaprop.
    }
    rewrite seq. exact (!(pr2 ineq2) d).
Defined.

Lemma information_order_is_reflexive {X : UU} {l : 𝓛 X} : l ⊑ l.
Proof.
  split with (idfun _).
  intro d. use idpath.
Defined.

Lemma information_order_is_transitive {X : UU} {l m n : 𝓛 X} :
  l ⊑ m -> m ⊑ n -> l ⊑ n.
Proof.
  intros ineq1 ineq2.
  set (t := pr1 ineq1). set (s := pr1 ineq2).
  split with (s ∘ t). intro d.
  etrans.
  - exact ((pr2 ineq1) d).
  - exact ((pr2 ineq2) (t d)).
Defined.

(* Next, we wish to prove that η is an embedding. We first need a series of lemmas. *)

(* The first lemma shows that unit = unit is proofirrelevant.
   We need propositional univalence + funext (or equivalently, funext + propext). *)
Lemma unit_eq_unit_isproofirr : isProofIrrelevant (unit = unit).
Proof.
  assert (equiv' : (unit ≃ unit) ≃ unit).
  { use weq_iso.
    - exact (λ _, tt).
    - exact (λ _, idweq unit).
    - intro f. simpl. use subtypeEquality.
      + exact (isapropisweq).
      + simpl. use funextfun. intro x. use (proofirrelevance unit isapropunit).
    - intro u. simpl. induction u. use idpath. }
  assert (equiv : (unit = unit) ≃ unit).
  { eapply weqcomp.
    - use (univalence unit unit).
    - exact equiv'. }
   (* Not strictly needed, but we are using univalence anyway and it allows for a shorter proof. *)
  rewrite (invmap (univalence (unit = unit) unit) equiv).
  exact (proofirrelevance unit (isapropunit)).
Qed.

(* We describe the action on paths of η.
   A path e : x = y gets mapped to (idpath unit,, idpath isapropunit,, ap₁ e),
   where 1 is the obvious map X -> (unit -> X). *)
Lemma maponpaths_η_eq {X : UU} {x y : X} (e : x = y) :
  let to_pair := total2_paths_equiv (λ P : UU, isaprop P × (P -> X))
                 (unit,, isapropunit,, termfun x) (unit,, isapropunit,, termfun y) in
  to_pair (maponpaths η e) = (idpath unit,,
                              @dirprod_paths _ _ (isapropunit,, termfun x)
                              (isapropunit,, termfun y) (idpath isapropunit)
                              (maponpaths termfun e)).
Proof.
  induction e. use idpath.
Qed.

(* Moreover, we can show that we may assume that the first component
   of a path between η-values is trivial. *)
Lemma η_values_eq {X : UU} {x y : X} (q : η x = η y) :
  let q1 := base_paths _ _ q in
  let q2 := fiber_paths q in
  let q1eq := unit_eq_unit_isproofirr q1 (idpath unit) in
  let transp_fun' := (λ P : UU, isaprop P × (P -> X)) in
  let transp_fun := (λ v : unit = unit, transportf transp_fun' v
                    (isapropunit,, termfun x) = (isapropunit,, termfun y)) in
  let to_pair := total2_paths_equiv (λ P : UU, isaprop P × (P -> X))
                 (unit,, isapropunit,, termfun x) (unit,, isapropunit,, termfun y) in
  to_pair q = (idpath unit,, (transportf transp_fun q1eq q2)).
Proof.
  use transportf_eq.
Qed.

Definition maponpaths_η_section {X : UU} {x y : X} : η x = η y -> x = y.
Proof.
  intro q.
  (* We take q apart, as in the above lemma. *)
  set (q1 := base_paths _ _ q).
  set (q2 := fiber_paths q).
  set (q1eq := unit_eq_unit_isproofirr q1 (idpath unit)).
  set (transp_fun' := (λ P : UU, isaprop P × (P -> X))).
  set (transp_fun := (λ v : unit = unit, transportf transp_fun' v
                     (isapropunit,, termfun x) = (isapropunit,, termfun y))).
  set (t := transportf transp_fun q1eq q2).
  set (t':= maponpaths dirprod_pr2 t). simpl in t'.
  (* t' is now a proof of termfun x = termfun y, so x = y. *)
  exact (maponpaths (λ f : unit -> X, f tt) t').
Defined.

Lemma dirprod_paths_pr2 {A B : UU} {x y : A × B} (e : x = y) (e' : pr1 x = pr1 y) :
  isaset A -> dirprod_paths e' (maponpaths dirprod_pr2 e) = e.
Proof.
  intro isasetA. induction e. induction x as [a b].
  simpl. simpl in e'.
  rewrite (proofirrelevance _ (isasetA _ _) e' (idpath a)).
  use idpath.
Qed.

Lemma maponpaths_η_is_retraction {X : UU} {x y : X} :
  maponpaths η ∘ @maponpaths_η_section X x y ~ idfun _.
Proof.
  intro q. unfold funcomp, idfun. simpl.
  set (to_pair := total2_paths_equiv (λ P : UU, isaprop P × (P -> X))
                  (unit,, isapropunit,, termfun x) (unit,, isapropunit,, termfun y)).
  set (from_pair := invmap to_pair).
  set (m := maponpaths η (maponpaths_η_section q)).
  assert (eq : to_pair m = to_pair q).
  { unfold m. unfold to_pair. rewrite maponpaths_η_eq. rewrite η_values_eq.
    unfold maponpaths_η_section.
    set (transp := transportf (λ v : unit = unit, transportf
                    (λ P : UU, isaprop P × (P → X)) v (isapropunit,, termfun x) =
                    isapropunit,, termfun y)
                    (unit_eq_unit_isproofirr (base_paths (η x) (η y) q)
                                             (idpath unit)) (fiber_paths q)).
    (* We should be able to finish this, but Coq is being difficult. *)
    admit. }
  set (eq' := maponpaths from_pair eq).
  assert (meq : from_pair (to_pair m) = m).
  { use homotinvweqweq. }
  assert (qeq : from_pair (to_pair q) = q).
  { use homotinvweqweq. }
  rewrite <- meq. rewrite <- qeq. exact eq'.
Admitted.

Theorem η_is_embedding {X : UU} : isInjective (@η X).
Proof.
  use isInjective'.
  split with (@maponpaths_η_section X).
  exact (@maponpaths_η_is_retraction X).
Qed.

(* Next, we wish to show that the fiber of η is equivalent to isdefined. *)
Definition fiber_to_isdefined {X : UU} {l : 𝓛 X} : hfiber η l -> isdefined l.
Proof.
  intro fib. induction fib as [x p].
  (* l ≡ (P,...) = (unit,...); so we transfer the inhabitant tt of unit *)
  exact (transportf (λ Q : UU, Q) (maponpaths pr1 p) tt).
Defined.

Definition isdefined_to_fiber {X : UU} {l : 𝓛 X} : isdefined l -> hfiber η l.
Proof.
  intro p. induction l as [P r]. induction r as [i f].
  split with (f p).
  set (t := (λ _, p) : unit -> P).
  set (s := (λ _, tt) : P -> unit).
  apply information_order_is_antisymmetric.
  - split with t. intro d. unfold value. simpl. unfold t. use idpath.
  - split with s. intro d. unfold value. unfold termfun. simpl.
    assert (eq : d = p). { use proofirrelevance. use isdefined_isaprop. }
    exact (maponpaths f eq).
Defined.

Theorem isdefined_equiv_fiber {X : UU} {l : 𝓛 X} : isdefined l ≃ hfiber η l.
Proof.
  use weqiff.
  - exact (tpair _ isdefined_to_fiber fiber_to_isdefined).
  - use isdefined_isaprop.
  - use isinclweqonpaths. exact η_is_embedding.
Defined.



(*** Domain Theory and Partial Elements ***)
(* First some preliminaries for relations into the universe (not hprop). *)
(* Definition istransitive {X : UU} (R : X -> X -> UU) {x y z : X} : UU :=
  R x y -> R y z -> R x z.
Definition issymmetric {X : UU} (R : X -> X -> UU) {x : X} : UU := R x x.
Definition isreflexive {X : UU} (R : X -> X -> UU) {x y : X} : UU := R x y -> R y x. *)

(* Definition isdirected {X I : UU} (R : X -> X -> UU) (f : I -> X) : UU :=
  ∏ (i j : I), ∑ (k : I), R (f i) (f k) × R (f j) (f k).

Definition isupperbound {X I : UU} (R : X -> X -> UU) (f : I -> X) (u : X) : UU :=
  ∏ (i : I), R (f i) u.

Definition islub {X I : UU} (R : X -> X -> UU) (f : I -> X) (u : X) : UU :=
  isupperbound R f u × ∏ (y : X), (∏ (i : I), R (f i) u) -> R u y.

Definition isdirectedcomplete {X : UU} (R : X -> X -> UU) : UU :=
  ∏ (I : UU), ∏ (f : I -> X), isdirected R f -> ∑ (u : X), islub R f u. *)

(* It seems that we need X to be an hSet for this to work. *)
(* Lemma information_order_is_directed_complete {X : UU} : @isdirectedcomplete (𝓛 X) (information_order). *)