Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.ClosureOfHrel.
Require Import UniMath.Algebra.DCPO.
Require Import UniMath.PartialityDominances.PartialElements.
Require Import UniMath.PartialityDominances.PartialFunctions.

Inductive type : UU :=
  | base       : type
  | functional : type -> type -> type.

Delimit Scope PCF with PCF.
Local Open Scope PCF.

Notation "'ι'" := base : PCF.
(* Check level? *)
Notation "σ ⇨ τ" := (functional σ τ) (at level 60, right associativity) : PCF.

Inductive term : type -> UU :=
  | zero                : term ι
  | succ                : term (ι ⇨ ι)
  | pred                : term (ι ⇨ ι)
  | ifz                 : term (ι ⇨ ι ⇨ ι ⇨ ι)
  | fixp {σ : type}     : term ((σ ⇨ σ) ⇨ σ)
  | 𝓀    {σ τ : type}   : term (σ ⇨ τ ⇨ σ)
  | 𝓈    {σ τ ρ : type} : term ((σ ⇨ τ ⇨ ρ) ⇨ (σ ⇨ τ) ⇨ σ ⇨ ρ)
  | app  {σ τ : type}   : term (σ ⇨ τ) -> term σ -> term τ.

Notation "s ` t" := (app s t) (at level 50, left associativity) : PCF.

Fixpoint numeral (n : nat) : term ι :=
  match n with
  | O   => zero
  | S k => succ ` (numeral k)
  end.

Inductive smallstep' : ∏ (σ : type), term σ -> term σ -> UU :=
  | predzerostep : smallstep' ι (pred ` zero) zero
  | predsuccstep (t : term ι) : smallstep' ι (pred ` (succ ` t)) t
  | ifzzerostep (s t : term ι) : smallstep' ι ((ifz ` s) ` t ` zero) s
  | ifzsuccstep (r s t : term ι) : smallstep' ι (ifz ` s ` t ` (succ ` r)) t
  | fixpstep {σ : type} (t : term (σ ⇨ σ)) : smallstep' σ (fixp ` t) (t ` (fixp ` t))
  | 𝓀step {σ τ : type} (s : term σ) (t : term τ) : smallstep' σ (𝓀 ` s ` t) s
  | 𝓈step {σ τ ρ : type} (s : term (σ ⇨ τ ⇨ ρ)) (t : term (σ ⇨ τ)) (r : term σ) :
            smallstep' ρ (𝓈 ` s ` t ` r) (s ` r ` (t ` r))
  | appstep {σ τ : type} (s t : term (σ ⇨ τ)) (r : term σ) :
      smallstep' (σ ⇨ τ) s t -> smallstep' τ (s ` r) (t ` r)
  | predargstep (s t : term ι) : smallstep' ι s t -> smallstep' ι (pred ` s) (pred ` t)
  | succargstep (s t : term ι) : smallstep' ι s t -> smallstep' ι (succ ` s) (succ ` t)
  | ifzargstep  (r r' s t : term ι) : smallstep' ι r r' -> smallstep' ι (ifz ` s ` t ` r)
                                                                      (ifz ` s ` t ` r').

Definition smallstep {σ : type} : hrel (term σ) :=
  λ (s t : term σ), ∥ smallstep' σ s t ∥.

Notation "s ▹ t" := (smallstep s t) (at level 40) : PCF.

Definition bigstep {σ : type} : hrel (term σ) := refl_trans_clos_hrel (smallstep).

Notation "s ⇓ t" := (bigstep s t) (at level 40) : PCF.

(* On to denotational semantics *)
Local Open Scope DCPO.

Fixpoint denotational_semantics_type (σ : type) : dcpowithleast :=
  match σ with
  | ι => liftdcpowithleast natset
  | τ ⇨ ρ => denotational_semantics_type τ --> denotational_semantics_type ρ
  end.

Notation "⦃ σ ⦄" := (denotational_semantics_type σ) : PCF.
Notation "'𝓛ℕ'" := (liftdcpowithleast natset) : PCF.

Local Open Scope PartialElements.
Local Open Scope PartialFunctionsDCPO.

Definition lifted_succ : 𝓛ℕ --> 𝓛ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : natset, η (S n)).
Defined.

Fixpoint P (n : nat) : nat :=
  match n with
  | O   => O
  | S m => m
  end.

Definition lifted_pred : 𝓛ℕ --> 𝓛ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : natset, η (P n)).
Defined.

Fixpoint ifz' (n : nat) (a b : 𝓛ℕ) : 𝓛ℕ :=
  match n with
  | O   => a
  | S m => b
  end.

Definition lifted_ifz' (a b : 𝓛ℕ) : 𝓛ℕ --> 𝓛ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : nat, ifz' n a b).
Defined.

Definition lifted_ifz : 𝓛ℕ --> (𝓛ℕ --> (𝓛ℕ --> 𝓛ℕ)).
Proof.
  use dcpomorphismpair.
  - intro a.
    use dcpomorphismpair.
    + intro b.
      exact (lifted_ifz' a b).
    + admit.
  - admit.
Admitted.

(*intros I u isdirec v islubv.
      split.
      * intro i. simpl. intro l.
        unfold Kleisli_extension. simpl.
        induction l as [P pair]; induction pair as [isprop φ]; simpl.
        assert (t : (∑ (p : P), isdefined (ifz' (φ p) a (u i))) ->
                    (∑ (p : P), isdefined (ifz' (φ p) a v))).
        { intros [p di]. split with p.
          destruct (φ p).
          ** simpl in *. exact di.
          ** simpl in *. apply (pr1 (pr1 islubv i)). exact di. }
        split with t. intros [p di]; cbn.
(*        assert (eq : ifz' (φ p) a (u i)).
        { use proofirrelevance. exact isprop. }
        destruct (φ (pr1 (t (p,, di)))).
        ** simpl.
        unfold value; cbn. *)
        admit.
      * intros g ineqs. intro l.
        cbn. unfold Kleisli_extension; simpl.
        induction l as [P pair]; induction pair as [isprop φ]; simpl.
        assert (t : (∑ (p : P), isdefined (ifz' (φ p) a v)) ->
                    isdefined (pr1 g (P,,isprop,,φ))).
        { intros [p d]. eapply isdefinedlub_toprop.
          - intros [i di]. use (pr1 ((ineqs i) _)).
            simpl. exact (p,,di).
          - use isdefined_isaprop.
          - admit. }
        split with t. intros [p d]. cbn.
        a
        admit.
  - split.
    + intro i. simpl. intros l m.*)

Definition 𝓀_dcpo {D D' : dcpowithleast} : D --> (D' --> D).
Proof.
  use dcpomorphismpair.
  - intro x. use dcpomorphismpair.
    + exact (λ y : D', x).
    + intros I u isdirec v islubv. split.
      * intro i; unfold funcomp; simpl. use isrefl_posetRelation.
      * intros d ineqs. apply (@factor_through_squash I).
        ** use (pr2 (pr1 (dcpoorder _) x d)).
        ** intro i. use (ineqs i).
        ** exact (pr1 (isdirec)).
  - intros I u isdirec v islubv. split.
    + intro i; simpl. intro d'. use (pr1 islubv i).
    + intros g ineqs; simpl in *.
      intro d'. use (pr2 islubv).
      intro i. use (ineqs i d').
Defined.

Definition 𝓈_dcpo {A B C : dcpowithleast} : (A --> (B --> C)) --> ((A --> B) --> (A --> C)).
Proof.
  use dcpomorphismpair.
  - intro f.
    use dcpomorphismpair.
    + intro g.
      use dcpomorphismpair.
      * intro a. exact (pr1 (pr1 f a) (pr1 g a)).
      * admit.
    + admit.
 - admit.
Admitted.

Fixpoint denotational_semantics_terms {σ : type} (t : term σ) : ⦃ σ ⦄ :=
  match t with
  | zero     => η O
  | succ     => lifted_succ
  | pred     => lifted_pred
  | ifz      => lifted_ifz
  | fixp     => leastfixedpoint
  | 𝓀        => 𝓀_dcpo
  | 𝓈        => 𝓈_dcpo
  | app s t  => pr1 (denotational_semantics_terms s) (denotational_semantics_terms t)
  end.

Notation "⟦ t ⟧" := (denotational_semantics_terms t) : PCF.

Fixpoint adequacy_relation (σ : type) : ⦃ σ ⦄ -> term σ -> UU :=
  match σ with
  | base => λ l, λ t, ∏ (p : isdefined l), t ⇓ numeral (value l p)
  | functional τ ρ => λ l, λ t, ∏ (m : ⦃ τ ⦄), ∏ (s : term τ),
                      adequacy_relation τ m s -> adequacy_relation ρ (pr1 l m) (t ` s)
  end.

Definition adequacy_least {σ : type} (t : term σ) :
  adequacy_relation σ (dcpowithleast_least ⦃ σ ⦄) t.
Proof.
  induction σ as [ | τ IH ρ IH'].
  - simpl. intro p. destruct p.
  - simpl. intros m s rel. exact (IH' (t ` s)).
Defined.

Lemma appbigstep {σ τ : type} (s t : term (σ ⇨ τ)) (r : term σ) : s ⇓ t -> (s ` r) ⇓ (t ` r).
Proof.
  use hinhfun. intro bstep.
  induction bstep.
  - use refl_trans_clos_extends. use factor_through_squash.
    exact (smallstep' _ x y).
    + use isapropishinh.
    + intro sstep. use hinhpr. apply appstep. exact sstep.
    + exact h.
  - use refl_trans_clos_refl.
  - eapply refl_trans_clos_trans.
    + exact IHbstep1.
    + exact IHbstep2.
Qed.

Definition adequacy_step {σ : type} (s t : term σ) (l : ⦃ σ ⦄) :
  s ⇓ t -> adequacy_relation σ l t -> adequacy_relation σ l s.
Proof.
  induction σ as [ | τ IH ρ IH'].
  - intros step rel.
    intro p.
    set (step' := rel p).
    eapply refl_trans_clos_hrel_istrans.
    + exact step.
    + exact step'.
  - intros step rel.
    simpl. intros m r rel'.
    apply (IH' (s ` r) (t ` r)).
    + apply appbigstep. exact step.
    + exact (rel m r rel').
Defined.

Definition adequacy_zero : adequacy_relation ι (η O) zero.
Proof.
  simpl. intro t. use hinhpr.
  use refl_trans_clos_refl.
Defined.

Definition succbigstep (s t : term ι) : bigstep s t -> bigstep (succ ` s) (succ ` t).
Proof.
  use hinhfun.
  intro bstep.
  induction bstep.
  - use refl_trans_clos_extends. use factor_through_squash.
    exact (smallstep' _ x y).
    + use isapropishinh.
    + intro sstep. use hinhpr. apply succargstep. exact sstep.
    + exact h.
  - use refl_trans_clos_refl.
  - eapply refl_trans_clos_trans.
    + exact IHbstep1.
    + exact IHbstep2.
Defined.

Definition adequacy_succ : adequacy_relation (ι ⇨ ι) lifted_succ succ.
Proof.
  intros l t rel q.
  induction q as [p q'].
  set (reduces := rel p).
  change (numeral (value (pr1 lifted_succ l) (p,,q'))) with
  (succ ` (numeral (value l p))).
  apply succbigstep. exact reduces.
Defined.

Definition predbigstep (s t : term ι) : bigstep s t -> bigstep (pred ` s) (pred ` t).
Proof.
  use hinhfun.
  intro bstep.
  induction bstep.
  - use refl_trans_clos_extends. use factor_through_squash.
    exact (smallstep' _ x y).
    + use isapropishinh.
    + intro sstep. use hinhpr. apply predargstep. exact sstep.
    + exact h.
  - use refl_trans_clos_refl.
  - eapply refl_trans_clos_trans.
    + exact IHbstep1.
    + exact IHbstep2.
Defined.

Definition adequacy_pred : adequacy_relation (ι ⇨ ι) lifted_pred pred.
Proof.
  intros l t rel q.
  induction q as [p u].
  induction l as [Q pair]. induction pair as [isprop φ].
  destruct (φ p) eqn:eq.
  - eapply refl_trans_clos_hrel_istrans.
    + eapply predbigstep. exact (rel p).
    + cbn. rewrite eq. simpl. use hinhpr.
      use refl_trans_clos_extends. use hinhpr.
      exact predzerostep.
  - eapply refl_trans_clos_hrel_istrans.
    + eapply predbigstep. exact (rel p).
    + cbn. rewrite eq. simpl. use hinhpr.
      use refl_trans_clos_extends. use hinhpr.
      use predsuccstep.
Defined.