(**

Tom de Jong

Created: November - December 2018

Refactored: January 2019

*******************************************************************************)

(** * Operational Semantics and the constructive Scott Model of PCF *)
(** ** Contents
- Definition of PCF ([pcf])
- Operational smallstep semantics of PCF and its reflexive transitive closure
  ([operationalsemantics])
- The Scott model of PCF ([denotationalsemantics])
- Soundness of the Scott model with respect to the operational semantics
  ([soundness])
- Adequacy ([adequacy])
*)



Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.ClosureOfHrel.
Require Import UniMath.Algebra.DCPO.
Require Import UniMath.Partiality.PartialElements.
Require Import UniMath.Partiality.LiftMonad.
Require Import UniMath.MoreFoundations.PropExt.

(** * Definition of PCF *)
Delimit Scope PCF with PCF.
Local Open Scope PCF.

Section pcf.
Inductive type : UU :=
  | base       : type
  | functional : type -> type -> type.

Notation "'ι'" := base : PCF.

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
  | 0   => zero
  | S k => succ ` (numeral k)
  end.

End pcf.

Notation "'ι'" := base : PCF.
Notation "σ ⇨ τ" := (functional σ τ) (at level 60, right associativity) : PCF.
Notation "s ` t" := (app s t) (at level 50, left associativity) : PCF.

Section operationalsemantics.

Inductive smallstep' : ∏ (σ : type), term σ -> term σ -> UU :=
  | predzerostep :
      smallstep' ι (pred ` zero) zero
  | predsuccstep (n : nat) :
      smallstep' ι (pred ` (numeral (S n))) (numeral n)
  | ifzzerostep (s t : term ι) :
      smallstep' ι ((ifz ` s) ` t ` zero) s
  | ifzsuccstep (s t : term ι) (n : nat) :
      smallstep' ι (ifz ` s ` t ` (succ ` (numeral n))) t
  | fixpstep {σ : type} (t : term (σ ⇨ σ)) :
      smallstep' σ (fixp ` t) (t ` (fixp ` t))
  | 𝓀step {σ τ : type} (s : term σ) (t : term τ) :
      smallstep' σ (𝓀 ` s ` t) s
  | 𝓈step {σ τ ρ : type} (s : term (σ ⇨ τ ⇨ ρ)) (t : term (σ ⇨ τ)) (r : term σ) :
      smallstep' ρ (𝓈 ` s ` t ` r) (s ` r ` (t ` r))
  | appstep {σ τ : type} (s t : term (σ ⇨ τ)) (r : term σ) :
      smallstep' (σ ⇨ τ) s t -> smallstep' τ (s ` r) (t ` r)
  | predargstep (s t : term ι) :
      smallstep' ι s t -> smallstep' ι (pred ` s) (pred ` t)
  | succargstep (s t : term ι) :
      smallstep' ι s t -> smallstep' ι (succ ` s) (succ ` t)
  | ifzargstep  (r r' s t : term ι) :
      smallstep' ι r r' -> smallstep' ι (ifz ` s ` t ` r)  (ifz ` s ` t ` r').

Definition smallstep {σ : type} : hrel (term σ) :=
  λ (s t : term σ), ∥ smallstep' σ s t ∥.

Notation "s ▹ t" := (smallstep s t) (at level 40) : PCF.

Definition refltrans_smallstep {σ : type} : hrel (term σ) :=
  refl_trans_clos_hrel (smallstep).

Notation "s ▹* t" := (refltrans_smallstep s t) (at level 40) : PCF.

Lemma reflect_to_refltrans {σ τ : type} (f : term σ -> term τ) :
  (∏ (s t : term σ), (smallstep' σ s t -> smallstep' τ (f s) (f t))) ->
  (∏ (s t : term σ), (s ▹* t) -> (f s ▹* f t)).
Proof.
  intro hyp.
  intros s t.
  apply hinhfun.
  intro rtstep.
  induction rtstep.
  - apply refl_trans_clos_extends.
    apply (@factor_through_squash (smallstep' _ x y)).
    + apply isapropishinh.
    + intro sstep. apply hinhpr. apply hyp. exact sstep.
    + exact h.
  - apply refl_trans_clos_refl.
  - eapply refl_trans_clos_trans.
    + exact IHrtstep1.
    + exact IHrtstep2.
Qed.

Lemma app_refltrans_smallstep {σ τ : type} (s t : term (σ ⇨ τ)) (r : term σ) :
  s ▹* t -> (s ` r) ▹* (t ` r).
Proof.
  apply (reflect_to_refltrans (λ x : term (σ ⇨ τ), x ` r)).
  intros ? ?. apply appstep.
Qed.

Lemma succ_refltrans_smallstep (s t : term ι) :
  s ▹* t -> (succ ` s) ▹* (succ ` t).
Proof.
  apply (reflect_to_refltrans (λ x : term ι, succ ` x)).
  apply succargstep.
Qed.

Lemma pred_refltrans_smallstep (s t : term ι) :
  s ▹* t -> (pred ` s) ▹* (pred ` t).
Proof.
  apply (reflect_to_refltrans (λ x : term ι, pred ` x)).
  apply predargstep.
Qed.

Lemma ifz_refltrans_smallstep (s t r r' : term ι) :
  r ▹* r' -> (ifz ` s ` t ` r) ▹* (ifz ` s ` t ` r').
Proof.
  apply (reflect_to_refltrans (λ x: term ι, ifz ` s ` t ` x)).
  intros ? ?. apply ifzargstep.
Qed.

End operationalsemantics.

Notation "s ▹ t" := (smallstep s t) (at level 40) : PCF.
Notation "s ▹* t" := (refltrans_smallstep s t) (at level 40) : PCF.

(** * The constructive Scott model of PCF *)
Section denotationalsemantics.

Local Open Scope DCPO.
Local Open Scope LiftDcpo.
Local Open Scope LiftMonadDcpo.

Fixpoint denotational_semantics_type (σ : type) : dcpowithbottom :=
  match σ with
  | ι => 𝓛 natset
  | τ ⇨ ρ => denotational_semantics_type τ --> denotational_semantics_type ρ
  end.

Notation "⦃ σ ⦄" := (denotational_semantics_type σ) : PCF.
Notation "'ℕ'" := natset : PCF.

Definition lifted_succ : 𝓛 ℕ --> 𝓛 ℕ.
Proof.
  eapply liftfunctor_dcpo.
  use S.
Defined.

Fixpoint P (n : nat) : nat :=
  match n with
  | 0   => O
  | S m => m
  end.

Definition lifted_pred : 𝓛 ℕ --> 𝓛 ℕ.
Proof.
  eapply liftfunctor_dcpo.
  use P.
Defined.

Fixpoint ifz' (n : nat) (a b : 𝓛 ℕ) : 𝓛 ℕ :=
  match n with
  | 0   => a
  | S m => b
  end.

Definition lifted_ifz' (a b : 𝓛 ℕ) : 𝓛 ℕ --> 𝓛 ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : nat, ifz' n a b).
Defined.

Definition lifted_ifz : 𝓛 ℕ --> (𝓛 ℕ --> (𝓛 ℕ --> 𝓛 ℕ)).
Proof.
  use mkdcpomorphism.
  - intro a.
    use mkdcpomorphism.
    + intro b.
      exact (lifted_ifz' a b).
    + intros I u isdirec v islubv.
      split.
      * intro i. cbn.
        intro l.
        intros [d1 d2].
        assert (eq : l = η (value l d1)).
        { apply isdefined_lift_embedding. }
        assert (d2' : isdefined (ifz' (value l d1) a (u i))).
        { exact d2. }
        rewrite eq.
        do 2 (rewrite fun_extension_after_eta).
        induction (value l d1) as [| n _].
        -- apply idpath.
        -- simpl.
           use (islub_isupperbound _ islubv i).
           exact d2'.
      * intros f ineqs l.
        cbn.
        intros [d1 d2].
        assert (eq : l = η (value l d1)).
        { apply isdefined_lift_embedding. }
        assert (d2' : isdefined (ifz' (value l d1) a v)).
        { exact d2. }
        rewrite eq.
        rewrite fun_extension_after_eta.
        induction (value l d1) as [| n _ ].
        -- cbn. apply (@factor_through_squash I).
           ++ assert (helper : isaset (𝓛 ℕ)).
              { apply liftofhset_isaset. }
              use helper.
           ++ intro i.
              set (ineq := ineqs i (η 0)). cbn in ineq.
              apply pathsinv0.
              etrans.
              ** apply pathsinv0, ineq.
                 rewrite fun_extension_after_eta.
                 cbn. exact d2'.
              ** rewrite fun_extension_after_eta.
                 apply idpath.
           ++ exact (isdirected_inhabited isdirec).
        -- cbn.
           apply (isdefinedlub_toprop isdirec islubv).
           ++ intros [i di].
              set (eq' := liftlub_isdefined isdirec islubv i di).
              rewrite <- eq'.
              set (ineq := ineqs i (η (S n))).
              cbn in ineq. rewrite fun_extension_after_eta in ineq.
              cbn in ineq. apply ineq. exact di.
           ++ set (helper := @liftofhset_isaset ℕ).
              use helper.
           ++ exact d2'.
  - intros I u isdirec v islubv; split.
    + intro i; cbn.
      intros l m.
      intros [d1 d2].
      assert (d2' : isdefined (ifz' (value m d1) (u i) l)).
      { exact d2. }
      assert (eq : m = η (value m d1)).
      { apply isdefined_lift_embedding. }
      rewrite eq. do 2 (rewrite fun_extension_after_eta).
      induction (value m d1) as [| n _].
      * cbn. exact (liftlub_isdefined isdirec islubv i d2').
      * apply idpath.
    + intros f ineqs; cbn in *.
      intros l m.
      intros [d1 d2].
      assert (d2' : isdefined (ifz' (value m d1) v l)).
      { exact d2. }
      assert (eq : m = η (value m d1)).
      { apply isdefined_lift_embedding. }
      rewrite eq. rewrite fun_extension_after_eta.
      induction (value m d1) as [| n _].
      * cbn. apply (isdefinedlub_toprop isdirec islubv).
        -- intros [i di].
           set (eq' := liftlub_isdefined isdirec islubv i di).
           rewrite <- eq'.
           set (ineq := (ineqs i l (η 0))). cbn in ineq.
           rewrite fun_extension_after_eta in ineq; cbn in ineq.
           apply ineq.
           exact di.
        -- set (helper := @liftofhset_isaset ℕ).
           use helper.
        -- exact d2'.
      * cbn. apply (@factor_through_squash I).
        -- set (helper := @liftofhset_isaset ℕ).
           use helper.
        -- intro i.
           set (ineq := ineqs i l (η (S n))).
           rewrite fun_extension_after_eta in ineq; cbn in ineq.
           apply ineq.
           exact d2'.
        -- exact (isdirected_inhabited isdirec).
Defined.

Definition k_dcpo {D D' : dcpowithbottom} : D --> (D' --> D).
Proof.
  use mkdcpomorphism.
  - intro x. use mkdcpomorphism.
    + exact (λ y : D', x).
    + intros I u isdirec v islubv. split.
      * intro i; unfold funcomp; cbn. apply isrefl_posetRelation.
      * intros d ineqs. apply (@factor_through_squash I).
        -- apply propproperty.
        -- intro i. exact (ineqs i).
        -- exact (isdirected_inhabited isdirec).
  - intros I u isdirec v islubv. split.
    + intro i; cbn. intro d'. exact (islub_isupperbound u islubv i).
    + intros g ineqs; cbn in *.
      intro d'. apply (islub_isleast u islubv).
      intro i. exact (ineqs i d').
Defined.

Definition s_dcpo {A B C : dcpowithbottom} :
  (A --> (B --> C)) --> ((A --> B) --> (A --> C)).
Proof.
  use mkdcpomorphism.
  - intro f.
    use mkdcpomorphism.
    + intro g.
      use mkdcpomorphism.
      * intro a. exact (pr1 (pr1 f a) (pr1 g a)).
      * intros I u isdirec v islubv. split.
        -- intro i; unfold funcomp; cbn.
           assert (ineqf : (pr1 f (u i) ≤ pr1 f v)%poset).
           { apply dcpomorphism_preservesorder.
             exact (islub_isupperbound _ islubv i). }
           eapply istrans_posetRelation.
           ++ eapply dcpomorphism_preservesorder.
              eapply dcpomorphism_preservesorder.
              exact (islub_isupperbound _ islubv i).
           ++ use ineqf.
        -- intros c ineqs.
           set (fpreslub := dcpomorphism_preserveslub f isdirec v islubv).
           set (gpreslub := dcpomorphism_preserveslub g isdirec v islubv).
           set (isdirecg := dcpomorphism_preservesdirected g isdirec).
           set (isdirecf := dcpomorphism_preservesdirected f isdirec).
           set (fpreslub' := dcpomorphism_preserveslub (pr1 f v)
                                                       isdirecg _ gpreslub).
           use (pr2 fpreslub').
           intro i.
           set (const := mkconst_dcpomor B C c).
           change c with (const (pr1 g (u i))).
           unfold funcomp.
           set (islubpt := islub_islubpointwise isdirecf fpreslub).
           use (islub_isleast _ (islubpt _)).
           intro j. unfold funcomp, pointwisefamily. cbn.
           apply (@factor_through_squash (directeduntruncated u i j)).
           ++ apply propproperty.
           ++ intros [k greater].
              eapply istrans_posetRelation.
              ** eapply dcpomorphism_preservesorder.
                 eapply dcpomorphism_preservesorder.
                 exact (pr1 greater).
              ** assert (ineqf : (pr1 f (u j) ≤ pr1 f (u k))%poset).
                 { use dcpomorphism_preservesorder. exact (pr2 greater). }
                 eapply istrans_posetRelation.
                 --- use ineqf.
                 --- exact (ineqs k).
           ++ exact (isdirected_order isdirec i j).
    + intros I F isdirec g islubg; split.
      * intro i; cbn. intro a.
        apply dcpomorphism_preservesorder.
        use (islub_isupperbound F islubg _).
      * intros h ineqs; cbn in *.
        intro a.
        set (islubpt := islub_islubpointwise isdirec islubg a).
        set (fpreslub := dcpomorphism_preserveslub (pr1 f a)
                          (pointwisefamily_isdirected F isdirec a) _ islubpt).
        apply (islub_isleast _ fpreslub).
        intro i. unfold pointwisefamily, funcomp.
        exact (ineqs i a).
  - intros I 𝓕 isdirec F islubF; split.
    + intro i; cbn. intros f a.
      use (islub_isupperbound _ islubF).
    + intros 𝓖 ineqs; cbn in *.
      intros f a.
      set (islubpt := islub_islubpointwise isdirec islubF).
      set (islubpt' := islub_islubpointwise (pointwisefamily_isdirected
                                             𝓕 isdirec a)
                                            (islubpt a)).
      use (islub_isleast _ (islubpt' (pr1 f a))).
      intro i. exact (ineqs i f a).
Defined.

Fixpoint denotational_semantics_terms {σ : type} (t : term σ) : ⦃ σ ⦄ :=
  match t with
  | zero     => η O
  | succ     => lifted_succ
  | pred     => lifted_pred
  | ifz      => lifted_ifz
  | fixp     => leastfixedpoint
  | 𝓀        => k_dcpo
  | 𝓈        => s_dcpo
  | app s r  => pr1 (denotational_semantics_terms s)
                    (denotational_semantics_terms r)
  end.

Notation "⟦ t ⟧" := (denotational_semantics_terms t) : PCF.

Lemma denotational_semantics_numerals (n : nat) : ⟦ numeral n ⟧ = η n.
Proof.
  induction n as [| m IH].
  - apply idpath.
  - cbn. rewrite IH. apply idpath.
Qed.

End denotationalsemantics.

Notation "⦃ σ ⦄" := (denotational_semantics_type σ) : PCF.
Notation "'ℕ'" := natset : PCF.
Notation "⟦ t ⟧" := (denotational_semantics_terms t) : PCF.

(** * Soundness of the Scott model with respect to the operational semantics *)
Section soundness.
Theorem soundness {σ : type} (s t : term σ) : s ▹* t -> (⟦ s ⟧) = (⟦ t ⟧).
Proof.
  intro step.
  apply (@factor_through_squash ((refl_trans_clos smallstep) s t)).
  - apply setproperty.
  - intro step'.
    induction step'.
    + apply (@factor_through_squash (smallstep' σ x y)).
      * use setproperty.
      * intro step'.
        induction step'.
        -- apply idpath.
        -- apply idpath.
        -- cbn. rewrite fun_extension_after_eta.
           apply idpath.
        -- change (⟦ ifz ` s ` t ` (succ ` numeral n) ⟧) with
           (pr1 (⟦ ifz ` s ` t ⟧) (⟦ numeral (S n) ⟧)).
           rewrite (denotational_semantics_numerals (S n)).
           cbn. rewrite fun_extension_after_eta.
           apply idpath.
        -- apply pathsinv0. apply leastfixedpoint_isfixedpoint.
        -- apply idpath.
        -- apply idpath.
        -- cbn. apply (@eqtohomot _ _ (pr1 (⟦ s ⟧))).
           apply maponpaths.
           apply IHstep'.
           ++ apply refl_trans_clos_hrel_extends.
              apply hinhpr. exact step'.
           ++ apply hinhpr. exact step'.
        -- cbn. apply maponpaths. apply IHstep'.
           ++ apply refl_trans_clos_hrel_extends.
              apply hinhpr. exact step'.
           ++ apply hinhpr. exact step'.
        -- cbn; apply maponpaths, IHstep'.
           ++ apply refl_trans_clos_hrel_extends;
              apply hinhpr; exact step'.
           ++ apply hinhpr; exact step'.
        -- cbn; apply maponpaths, IHstep'.
           ++ apply refl_trans_clos_hrel_extends;
              apply hinhpr; exact step'.
           ++ apply hinhpr; exact step'.
      * exact h.
    + apply idpath.
    + etrans.
      ++ apply IHstep'1.
         apply hinhpr. exact step'1.
      ++ apply IHstep'2.
         apply hinhpr. exact step'2.
  - exact step.
Qed.

End soundness.

(** * Adequacy *)
Section adequacy.

Fixpoint adequacy_relation (σ : type) : ⦃ σ ⦄ -> term σ -> UU :=
  match σ with
  | ι     => λ (l : ⦃ ι ⦄) (t : term ι),
             ∏ (p : isdefined l), t ▹* numeral (value l p)
  | τ ⇨ ρ => λ (l : ⦃ τ ⇨ ρ ⦄) (t : term (τ ⇨ ρ)),
             ∏ (m : ⦃ τ ⦄), ∏ (s : term τ),
             adequacy_relation τ m s -> adequacy_relation ρ (pr1 l m) (t ` s)
  end.

Definition adequacy_bottom {σ : type} (t : term σ) :
  adequacy_relation σ (dcpowithbottom_bottom ⦃ σ ⦄) t.
Proof.
  induction σ as [ | τ _ ρ IHρ].
  - cbn. intro p. induction p.
  - cbn. intros _ s _. exact (IHρ (t ` s)).
Defined.

Definition adequacy_step {σ : type} (s t : term σ) (l : ⦃ σ ⦄) :
  s ▹* t -> adequacy_relation σ l t -> adequacy_relation σ l s.
Proof.
  induction σ as [ | τ _ ρ IHρ].
  - intros step rel.
    intro p.
    set (step' := rel p).
    eapply refl_trans_clos_hrel_istrans.
    + exact step.
    + exact step'.
  - intros step rel.
    cbn. intros m r rel'.
    apply (IHρ (s ` r) (t ` r)).
    + apply app_refltrans_smallstep. exact step.
    + exact (rel m r rel').
Defined.

Definition adequacy_zero : adequacy_relation ι (lift_embedding O) zero.
Proof.
  cbn. intro t. apply hinhpr.
  apply refl_trans_clos_refl.
Defined.

Definition adequacy_succ : adequacy_relation (ι ⇨ ι) lifted_succ succ.
Proof.
  intros l t rel q.
  change (numeral (value (pr1 lifted_succ l) q)) with
  (succ ` (numeral (value l q))).
  apply succ_refltrans_smallstep.
  exact (rel q).
Defined.

Definition adequacy_pred : adequacy_relation (ι ⇨ ι) lifted_pred pred.
Proof.
  intros l t rel q.
  change (value (pr1 lifted_pred l) q) with (P ((value l q))).
  induction (value l q) as [| m _] eqn:eq.
  - unfold P, numeral.
    eapply refl_trans_clos_hrel_istrans.
    + eapply pred_refltrans_smallstep.
      exact (rel q).
    + rewrite eq. unfold numeral.
      apply hinhpr, refl_trans_clos_extends.
      apply hinhpr. exact predzerostep.
  - unfold P. eapply refl_trans_clos_hrel_istrans.
    + eapply pred_refltrans_smallstep. exact (rel q).
    + rewrite eq. apply hinhpr.
      apply refl_trans_clos_extends, hinhpr.
      apply predsuccstep.
Defined.

Definition adequacy_ifz : adequacy_relation (ι ⇨ ι ⇨ ι ⇨ ι) lifted_ifz ifz.
Proof.
  intros l1 t1 rel1 l2 t2 rel2 l3 t3 rel3.
  intros [p d].
  induction (value l3 p) as [| m _ ] eqn:eq.
  - change (numeral (value (pr1 (pr1 (pr1 lifted_ifz l1) l2) l3) (p,,d))) with
    (numeral (value (ifz' (value l3 p) l1 l2) d)).
    assert (eq' : ifz' (value l3 p) l1 l2 = l1).
    { rewrite eq. apply idpath. }
    set (d' := lifteq_isdefined eq' d).
    rewrite (lifteq_valueeq eq' d d').
    apply (refl_trans_clos_hrel_istrans _ _ (ifz ` t1 ` t2 ` zero)).
    + apply ifz_refltrans_smallstep.
      change zero with (numeral 0).
      rewrite <- eq.
      apply rel3.
    + apply (refl_trans_clos_hrel_istrans _ _ t1).
      * apply refl_trans_clos_hrel_extends.
        apply hinhpr, ifzzerostep.
      * apply rel1.
  - change (numeral (value (pr1 (pr1 (pr1 lifted_ifz l1) l2) l3) (p,,d))) with
    (numeral (value (ifz' (value l3 p) l1 l2) d)).
    assert (eq' : ifz' (value l3 p) l1 l2 = l2).
    { rewrite eq. apply idpath. }
    set (d' := lifteq_isdefined eq' d).
    rewrite (lifteq_valueeq eq' d d').
    apply (refl_trans_clos_hrel_istrans _ _ (ifz ` t1 ` t2 ` (succ ` (numeral m)))).
    + apply ifz_refltrans_smallstep.
      change (succ ` numeral m) with (numeral (S m)).
      rewrite <- eq.
      apply rel3.
    + apply (refl_trans_clos_hrel_istrans _ _ t2).
      * apply refl_trans_clos_hrel_extends.
        apply hinhpr, ifzsuccstep.
      * apply rel2.
Defined.

Definition adequacy_k {σ τ : type} : adequacy_relation (σ ⇨ τ ⇨ σ) k_dcpo 𝓀.
Proof.
  intros l t rel m s rel'.
  cbn.
  eapply adequacy_step.
  - apply refl_trans_clos_hrel_extends.
    apply hinhpr.
    apply 𝓀step.
  - exact rel.
Defined.

Definition adequacy_s {σ τ ρ : type} : adequacy_relation
                                         ((σ ⇨ τ ⇨ ρ) ⇨ (σ ⇨ τ) ⇨ σ ⇨ ρ)
                                         s_dcpo 𝓈.
Proof.
  intros l1 t1 rel1 l2 t2 rel2 l3 t3 rel3.
  cbn.
  eapply adequacy_step.
  - apply refl_trans_clos_hrel_extends.
    apply hinhpr.
    apply 𝓈step.
  - set (rel' := rel2 _ _ rel3).
    exact (rel1 _ _ rel3 _ _ rel').
Defined.

Definition adequacy_lubs {σ : type} {I : UU} (u : I -> ⦃ σ ⦄)
           (isdirec : isdirected u) (t : term σ) :
  (∏ (i : I), adequacy_relation σ (u i) t) ->
  ∏ (v : ⦃ σ ⦄), islub u v -> adequacy_relation σ v t.
Proof.
  induction σ as [ | τ _ ρ IHρ].
  - intros adequacy_I v islubv p.
    eapply (isdefinedlub_toprop isdirec islubv).
    + intros [i di].
      set (eq := liftlub_isdefined isdirec islubv i di).
      set (p' := lifteq_isdefined (!eq) p).
      rewrite (lifteq_valueeq (!eq) p di).
      apply adequacy_I.
    + apply isapropishinh.
    + exact p.
  - intros adequacy_I v islubv m s rel.
    set (ptfam := pointwisefamily u m).
    set (ptfamdirec := pointwisefamily_isdirected u isdirec m).
    apply (IHρ ptfam ptfamdirec).
    + intro i. unfold ptfam. unfold pointwisefamily.
      apply (adequacy_I i); exact rel.
    + apply (islub_islubpointwise isdirec islubv).
Defined.

Definition adequacy_fixp {σ : type} : adequacy_relation ((σ ⇨ σ) ⇨ σ)
                                                        leastfixedpoint fixp.
Proof.
  intros f t rel.
  set (ptfam := pointwisefamily (@iter' ⦃ σ ⦄) f).
  set (ptfamdirec := pointwisefamily_isdirected (@iter' ⦃ σ ⦄)
                                                (iter'_isdirected ⦃ σ ⦄) f).
  apply (adequacy_lubs ptfam ptfamdirec).
  - intro n. induction n as [ | m IH].
    + apply adequacy_bottom.
    + eapply adequacy_step.
      ++ apply refl_trans_clos_hrel_extends, hinhpr.
         apply fixpstep.
      ++ exact (rel _ _ IH).
  - apply pointwiselub_islubpointwise.
Defined.

Definition adequacy_allterms {σ : type} (t : term σ) :
  adequacy_relation σ (⟦ t ⟧) t.
Proof.
  induction t.
  - exact adequacy_zero.
  - exact adequacy_succ.
  - exact adequacy_pred.
  - exact adequacy_ifz.
  - exact adequacy_fixp.
  - exact adequacy_k.
  - exact adequacy_s.
  - exact (IHt1 _ _ IHt2).
Defined.

Theorem adequacy (t : term ι) :
  ∏ (p : isdefined (⟦ t ⟧)), t ▹* numeral (value (⟦ t ⟧) p).
Proof.
  exact (@adequacy_allterms ι t).
Qed.

End adequacy.
