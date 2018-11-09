Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* The type of partial elements of a type X is denoted by 𝓛 X, for "lift of X". *)
Definition lift (X : UU) := ∑ (P : UU), isaprop P × (P -> X).

Delimit Scope PartialElements with PartialElements.
Local Open Scope PartialElements.
Notation "'𝓛'" := lift : PartialElements.

(* We can map X into its lift. *)
Definition lift_embedding {X : UU} (x : X) : 𝓛 X := (unit,, isapropunit,, termfun x).
Notation "'η'" := lift_embedding : PartialElements.

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

(* TO DO: Check level *)
Notation "l ⊑ m" := (information_order l m) (at level 30) : PartialElements.

Definition information_order_antisymmetric {X : UU} {l m : 𝓛 X} :
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

Definition information_order_reflexive {X : UU} {l : 𝓛 X} : l ⊑ l.
Proof.
  split with (idfun _).
  intro d. use idpath.
Defined.

Definition information_order_transitive {X : UU} {l m n : 𝓛 X} :
  l ⊑ m -> m ⊑ n -> l ⊑ n.
Proof.
  intros ineq1 ineq2.
  set (t := pr1 ineq1). set (s := pr1 ineq2).
  split with (s ∘ t). intro d.
  etrans.
  - exact ((pr2 ineq1) d).
  - exact ((pr2 ineq2) (t d)).
Defined.


(*** Martin's proof ***)
Definition iscontr_lift (X : UU) : UU := ∑ (P : UU), iscontr P × (P -> X).

Delimit Scope LiftEmbeddingProof with LiftEmbeddingProof.
Local Open Scope LiftEmbeddingProof.
Notation "'𝓜'" := iscontr_lift : LiftEmbeddingProof.

Definition iscontr_lift_embedding {X : UU} (x : X) : 𝓜 X := (unit,, iscontrunit,, termfun x).
Notation "'μ'" := iscontr_lift_embedding : LiftEmbeddingProof.

Lemma iscontr_lift_embedding_isweq {X : UU} : isweq (@iscontr_lift_embedding X).
Proof.
  use isweq_iso.
  - intro m; induction m as [P pair]; induction pair as [i f].
    exact (f (pr1 i)).
  - simpl. intro x. use idpath.
  - simpl. intro m.
    induction m as [P pair]; induction pair as [i f].
    apply total2_paths_equiv. assert (e : unit = P).
    { use propext.
      + exact isapropunit.
      + use isapropifcontr. exact i.
      + split.
        * exact (λ _ : unit, (pr1 i)).
        * exact (λ _ : P, tt). }
    split with e.
    use dirprod_paths.
    + simpl. use proofirrelevance. use isapropiscontr.
    + simpl.
      assert (transpeq : pr2 (transportf (λ x : UU, iscontr x × (x -> X)) e
                              (iscontrunit,, termfun (f (pr1 i)))) =
                              termfun (f (pr1 i)) ∘ (pr1weq (eqweqmap (!e)))).
      { generalize e as e'. induction e'. use idpath. }
      rewrite transpeq.
      use funextfun. intro p. unfold funcomp, termfun.
      use maponpaths. exact (!(pr2 i p)).
Qed.

Definition 𝓜_to_𝓛 {X : UU} : 𝓜 X -> 𝓛 X.
Proof.
  use sumfun. intro P; simpl.
  use dirprodfun.
  - exact isapropifcontr.
  - exact (idfun _).
Defined.

(* Every map between hprops is an embedding. *)
Definition maponprops_isincl {P Q : UU} (f : P -> Q) :
  isaprop P -> isaprop Q -> isincl f.
Proof.
  intros i j. unfold isincl, isofhlevelf.
  intro q. use invproofirrelevance.
  intros fib fib'; induction fib as [p s]; induction fib' as [p' t].
  induction s. assert (eq : p = p').
  { use proofirrelevance. exact i. }
  apply total2_paths_equiv; split with eq; simpl.
  use proofirrelevance. use isasetaprop. exact j.
Defined.

(* Finally, we can prove that the map from 𝓜 to 𝓛 is an embedding. *)
Lemma 𝓜_to_𝓛_isincl {X : UU} : isincl (@𝓜_to_𝓛 X).
Proof.
  use sumfun_preserves_incl. intro P.
  use dirprodfun_preserves_incl.
  - use maponprops_isincl.
    + exact (isapropiscontr P).
    + exact (isapropisaprop P).
  - use isinclweq. exact (idisweq _).
Qed.
(* Now we show that η is an embedding by proving that it is pointwise equal
   to the composition of the two embeddings X -> 𝓜 X -> 𝓛 X. *)
Theorem lift_embedding_isincl {X : UU} : isincl (@lift_embedding X).
Proof.
  set (comp := (@𝓜_to_𝓛 X) ∘ (@iscontr_lift_embedding X)).
  apply (isinclhomot comp η).
  - intro x. unfold comp, funcomp.
    unfold iscontr_lift_embedding; unfold 𝓜_to_𝓛; unfold sumfun.
    unfold dirprodfun. simpl. unfold idfun.
    apply total2_paths_equiv.
    split with (idpath unit).
    simpl. apply dirprod_paths.
    + simpl. use proofirrelevance. exact (isapropisaprop unit).
    + simpl. use idpath.
  - set (incl1 := weqtoincl _ _ (weqpair (@iscontr_lift_embedding X)
                                         (@iscontr_lift_embedding_isweq X))).
    set (incl2 := inclpair (@𝓜_to_𝓛 X) (@𝓜_to_𝓛_isincl X)).
    apply (isinclcomp incl1 incl2).
Qed.
Close Scope LiftEmbeddingProof.
(*** End of Martin's Proof ***)

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
  apply information_order_antisymmetric.
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
  - use lift_embedding_isincl.
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

(*** Map into lift of product ***)
(* Useful for PCA
Definition into_lift_product {X : UU} : 𝓛 X -> 𝓛 X -> 𝓛 (X × X).
Proof.
  intros l m.
  set (Q := isdefined l × isdefined m).
  split with Q. split.
  - use isapropdirprod.
    + use isdefined_isaprop.
    + use isdefined_isaprop.
  - intro q. exact (value l (pr1 q),, value m (pr2 q)).
Defined. *)

Close Scope PartialElements.