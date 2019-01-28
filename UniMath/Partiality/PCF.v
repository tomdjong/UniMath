Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.ClosureOfHrel.
Require Import UniMath.Algebra.DCPO.
Require Import UniMath.Partiality.PartialElements.
Require Import UniMath.Partiality.LiftMonad.
Require Import UniMath.MoreFoundations.PropExt.

Inductive type : UU :=
  | base       : type
  | functional : type -> type -> type.

Delimit Scope PCF with PCF.
Local Open Scope PCF.

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

Definition refltrans_smallstep {σ : type} : hrel (term σ) :=
  refl_trans_clos_hrel (smallstep).

Notation "s ▹* t" := (refltrans_smallstep s t) (at level 40) : PCF.

(* On to denotational semantics *)
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
  eapply Kleisli_extension_dcpo.
  exact (λ n : natset, η (S n)).
Defined.

Fixpoint P (n : nat) : nat :=
  match n with
  | 0   => O
  | S m => m
  end.

Definition lifted_pred : 𝓛 ℕ --> 𝓛 ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : natset, η (P n)).
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
        do 2 (rewrite fun_extension_after_η).
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
        rewrite fun_extension_after_η.
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
                 rewrite fun_extension_after_η.
                 cbn. exact d2'.
              ** rewrite fun_extension_after_η.
                 apply idpath.
           ++ exact (isdirected_inhabited isdirec).
        -- cbn.
           apply (isdefinedlub_toprop isdirec islubv).
           ++ intros [i di].
              set (eq' := liftlub_isdefined isdirec islubv i di).
              rewrite <- eq'.
              set (ineq := ineqs i (η (S n))).
              cbn in ineq. rewrite fun_extension_after_η in ineq.
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
      rewrite eq. do 2 (rewrite fun_extension_after_η).
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
      rewrite eq. rewrite fun_extension_after_η.
      induction (value m d1) as [| n _].
      * cbn. apply (isdefinedlub_toprop isdirec islubv).
        -- intros [i di].
           set (eq' := liftlub_isdefined isdirec islubv i di).
           rewrite <- eq'.
           set (ineq := (ineqs i l (η 0))). cbn in ineq.
           rewrite fun_extension_after_η in ineq; cbn in ineq.
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
           rewrite fun_extension_after_η in ineq; cbn in ineq.
           apply ineq.
           exact d2'.
        -- exact (isdirected_inhabited isdirec).
Defined.

Definition 𝓀_dcpo {D D' : dcpowithbottom} : D --> (D' --> D).
Proof.
  use mkdcpomorphism.
  - intro x. use mkdcpomorphism.
    + exact (λ y : D', x).
    + intros I u isdirec v islubv. split.
      * intro i; unfold funcomp; simpl. use isrefl_posetRelation.
      * intros d ineqs. apply (@factor_through_squash I).
        ** apply propproperty.
        ** intro i. use (ineqs i).
        ** exact (pr1 (isdirec)).
  - intros I u isdirec v islubv. split.
    + intro i; simpl. intro d'. use (pr1 islubv i).
    + intros g ineqs; simpl in *.
      intro d'. use (pr2 islubv).
      intro i. use (ineqs i d').
Defined.

Definition 𝓈_dcpo {A B C : dcpowithbottom} : (A --> (B --> C)) --> ((A --> B) --> (A --> C)).
Proof.
  use mkdcpomorphism.
  - intro f.
    use mkdcpomorphism.
    + intro g.
      use mkdcpomorphism.
      ++ intro a. exact (pr1 (pr1 f a) (pr1 g a)).
      ++ intros I u isdirec v islubv. split.
         * intro i; unfold funcomp; simpl.
           assert (ineqf : (pr1 f (u i) ≤ pr1 f v)%poset).
           { use dcpomorphism_preservesorder. exact (pr1 islubv i). }
           eapply istrans_posetRelation.
           ** eapply dcpomorphism_preservesorder.
               eapply dcpomorphism_preservesorder. exact (pr1 islubv i).
           ** use ineqf.
         * intros c ineqs.
           set (fpreslub := dcpomorphism_preserveslub f isdirec v islubv).
           set (gpreslub := dcpomorphism_preserveslub g isdirec v islubv).
           set (isdirecg := dcpomorphism_preservesdirected g isdirec).
           set (isdirecf := dcpomorphism_preservesdirected f isdirec).
           set (fpreslub' := dcpomorphism_preserveslub (pr1 f v) isdirecg _ gpreslub).
           use (pr2 fpreslub'). intro i.
           set (const := mkconst_dcpomor B C c).
           change c with (const (pr1 g (u i))).
           unfold funcomp.
           assert (lubeq : (pr1 f v) = mkdcpomorphism
                                         (pointwiselub (pr1 f ∘ u) isdirecf)
                                         (pointwiselub_isdcpomorphism' (pr1 f ∘ u) isdirecf)).
           { eapply lubsareunique.
             - exact fpreslub.
             - use pointwiselub_islub. }
           rewrite lubeq.
           use (pr2 (pointwiselub_islubpointwise (pr1 f ∘ u) isdirecf (pr1 g (u i)))).
           intro j.
           unfold pointwisefamily; simpl. unfold funcomp; simpl.
           use factor_through_squash. exact (directeduntruncated u i j).
           ** apply propproperty.
           ** intros [k greater].
              eapply istrans_posetRelation.
              *** eapply dcpomorphism_preservesorder.
                   eapply dcpomorphism_preservesorder. exact (pr1 greater).
              *** eapply istrans_posetRelation.
                   assert (ineqf : (pr1 f (u j) ≤ pr1 f (u k))%poset).
                   { use dcpomorphism_preservesorder. exact (pr2 greater). }
                   **** apply (ineqf (pr1 g (u k))).
                   **** exact (ineqs k).
           ** exact (pr2 isdirec i j).
    + intros I F isdirec g islubg; split.
      ++ intro i; simpl. intro a.
         use dcpomorphism_preservesorder. exact ((pr1 islubg i) a).
      ++ intros h ineqs; simpl in *.
         intro a.
         set (ptfam := pointwisefamily F a).
         set (ptfamisdirec := pointwisefamily_isdirected F isdirec a).
         set (geq := lubsareunique _ islubg (pointwiselub_islub F isdirec)).
         rewrite geq; simpl.
         (* We use that f a preserves the lub *)
         use (pr2 (dcpomorphism_preserveslub (f a) ptfamisdirec
                  (pointwiselub F isdirec a)
                  (pointwiselub_islubpointwise F isdirec a))).
         intro i. unfold funcomp, ptfam; simpl.
         unfold pointwisefamily; simpl. exact (ineqs i a).
  - intros I 𝓕 isdirec F islubF; split.
    + intro i; simpl. intros f a.
      use (pr1 islubF i a).
    + intros 𝓖 ineqs; simpl in *.
      intros f a.
      set (Feq := lubsareunique _ islubF (pointwiselub_islub 𝓕 isdirec)).
      rewrite Feq; simpl.
      set (islubpt := (pointwiselub_islubpointwise 𝓕 isdirec a)).
      set (ptFeq := lubsareunique _ islubpt (pointwiselub_islub
                                               (pointwisefamily 𝓕 a)
                                               (pointwisefamily_isdirected 𝓕 isdirec a))).
      rewrite ptFeq; simpl.
      apply (pr2 (pointwiselub_islubpointwise (pointwisefamily 𝓕 a)
             (pointwisefamily_isdirected 𝓕 isdirec a) (pr1 f a))).
      intro i. exact (ineqs i f a).
Defined.

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
  | base => λ l, λ t, ∏ (p : isdefined l), t ▹* numeral (value l p)
  | functional τ ρ => λ l, λ t, ∏ (m : ⦃ τ ⦄), ∏ (s : term τ),
                      adequacy_relation τ m s -> adequacy_relation ρ (pr1 l m) (t ` s)
  end.

Definition adequacy_least {σ : type} (t : term σ) :
  adequacy_relation σ (dcpowithbottom_bottom ⦃ σ ⦄) t.
Proof.
  induction σ as [ | τ IH ρ IH'].
  - simpl. intro p. destruct p.
  - simpl. intros m s rel. exact (IH' (t ` s)).
Defined.

Lemma appbigstep {σ τ : type} (s t : term (σ ⇨ τ)) (r : term σ) : s ▹* t -> (s ` r) ▹* (t ` r).
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
  s ▹* t -> adequacy_relation σ l t -> adequacy_relation σ l s.
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

Lemma succbigstep (s t : term ι) : refltrans_smallstep s t ->
                                   refltrans_smallstep (succ ` s) (succ ` t).
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
Qed.

Definition adequacy_succ : adequacy_relation (ι ⇨ ι) lifted_succ succ.
Proof.
  intros l t rel q.
  induction q as [p q'].
  set (reduces := rel p).
  change (numeral (value (pr1 lifted_succ l) (p,,q'))) with
  (succ ` (numeral (value l p))).
  apply succbigstep. exact reduces.
Defined.

Lemma predbigstep (s t : term ι) : refltrans_smallstep s t ->
                                   refltrans_smallstep (pred ` s) (pred ` t).
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
Qed.

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

Lemma ifzbigstep (s t r r' : term ι) : r ▹* r' -> (ifz ` s ` t ` r) ▹* (ifz ` s ` t ` r').
Proof.
  use hinhfun.
  intro bstep.
  induction bstep.
  - use refl_trans_clos_extends. eapply (@factor_through_squash (smallstep' _ x y)).
    + use isapropishinh.
    + intro sstep. use hinhpr. apply ifzargstep. exact sstep.
    + exact h.
  - use refl_trans_clos_refl.
  - eapply refl_trans_clos_trans.
    + exact IHbstep1.
    + exact IHbstep2.
Qed.

Definition adequacy_ifz : adequacy_relation (ι ⇨ ι ⇨ ι ⇨ ι) lifted_ifz ifz.
Proof.
  intros l1 t1 rel1 l2 t2 rel2 l3 t3 rel3.
  induction l3 as [P pair]; induction pair as [isprop φ].
  intros [p d].
  admit.
  (*
  destruct (nateq0orS (φ p)) as [φpeq | φpeq'].
  - assert (l1eq : pr1 (pr1 (pr1 lifted_ifz l1) l2) (P,,isprop,,φ) = l1).
    { change (pr1 (pr1 (pr1 lifted_ifz l1) l2) (P,,isprop,,φ)) with
      (pr1 (lifted_ifz' l1 l2) (P,,isprop,,φ)).
      exact (lifted_ifz_case_0 _ _ (P,,isprop,,φ) p φpeq). }
    set (eq := eq_value_eq l1eq).
    assert (d' : isdefined l1).
    { rewrite φpeq in d. exact d. }
    rewrite (eq (p,,d) d').
    assert (ifzad : adequacy_relation ι l1 (ifz ` t1 ` t2 ` t3)).
    { eapply adequacy_step.
      - apply (ifzbigstep t1 t2 t3 zero).
        set (helper := rel3 p).
        unfold value in helper. rewrite φpeq in helper.
        exact helper.
      - eapply adequacy_step.
        + use refl_trans_clos_hrel_extends. use hinhpr.
          use ifzzerostep.
        + exact rel1. }
    exact (ifzad d').
  - induction φpeq' as [m φpeq].
    assert (l2eq : pr1 (pr1 (pr1 lifted_ifz l1) l2) (P,,isprop,,φ) = l2).
    { change (pr1 (pr1 (pr1 lifted_ifz l1) l2) (P,,isprop,,φ)) with
      (pr1 (lifted_ifz' l1 l2) (P,,isprop,,φ)).
      exact (lifted_ifz_case_S _ _ (P,,isprop,,φ) p (m,,φpeq)). }
    set (eq := eq_value_eq l2eq).
    assert (d' : isdefined l2).
    { rewrite φpeq in d. exact d. }
    rewrite (eq (p,,d) d').
    assert (ifzad : adequacy_relation ι l2 (ifz ` t1 ` t2 ` t3)).
    { eapply adequacy_step.
      - apply (ifzbigstep t1 t2 t3 (numeral (S m))).
        set (helper := rel3 p).
        unfold value in helper. rewrite φpeq in helper.
        exact helper.
      - eapply adequacy_step.
        + use refl_trans_clos_hrel_extends. use hinhpr.
          use ifzsuccstep.
        + exact rel2. }
    exact (ifzad d').*)
Admitted.

Definition adequacy_𝓀 {σ τ : type} : adequacy_relation (σ ⇨ τ ⇨ σ) 𝓀_dcpo 𝓀.
Proof.
  intros l t rel m s rel'.
  simpl.
  eapply adequacy_step.
  - use refl_trans_clos_hrel_extends.
    use hinhpr.
    use 𝓀step.
  - exact rel.
Defined.

Definition adequacy_𝓈 {σ τ ρ : type} : adequacy_relation
                                         ((σ ⇨ τ ⇨ ρ) ⇨ (σ ⇨ τ) ⇨ σ ⇨ ρ)
                                         𝓈_dcpo 𝓈.
Proof.
  intros l1 t1 rel1 l2 t2 rel2 l3 t3 rel3.
  simpl.
  eapply adequacy_step.
  - use refl_trans_clos_hrel_extends.
    use hinhpr.
    use 𝓈step.
  - set (rel' := rel2 _ _ rel3).
    exact (rel1 _ _ rel3 _ _ rel').
Defined.

Definition adequacy_lubs {σ : type} {I : UU} (u : I -> ⦃ σ ⦄) (isdirec : isdirected u)
           (t : term σ) : (∏ (i : I), adequacy_relation σ (u i) t) ->
                          ∏ (v : ⦃ σ ⦄), islub u v -> adequacy_relation σ v t.
Proof.
  induction σ as [ | τ IH ρ IH'].
  - intro adequacy_I.
    intros v islubv p.
    assert (lubeq : v = mkdirectedlubinlift isdirec).
    { eapply (lubsareunique u).
      - exact islubv.
      - use mkdirectedlubinlift_islub. }
    set (p' := transportf isdefined lubeq p).
    eapply (isdefinedlub_toprop' isdirec).
    + intros [i di].
      rewrite (lifteq_valueeq lubeq p p').
      admit.
      (*
      rewrite <- (lubvalue_eq u isdirec i di).
      exact (adequacy_I i di).
    + use isapropishinh.
    + exact p'.
  - intro adequacy_I.
    intros v islubv m s rel.
    set (ptfam := pointwisefamily u m).
    set (ptfamdirec := pointwisefamily_isdirected u isdirec m).
    apply (IH' ptfam ptfamdirec).
    + intro i. unfold ptfam. unfold pointwisefamily.
      apply (adequacy_I i).
      exact rel.
    + assert (lubeq : v = dcpomorphismpair (pointwiselub u isdirec)
                                           (pointwiselub_isdcpomorphism u isdirec)).
      { apply (lubsareunique u).
        - exact islubv.
        - use pointwiselub_islub. }
      rewrite lubeq.
      use pointwiselub_islubpointwise.*)
Admitted.

Definition adequacy_fixp {σ : type} : adequacy_relation ((σ ⇨ σ) ⇨ σ)
                                                        leastfixedpoint fixp.
Proof.
  intros f t rel.
  (* We wish to apply the previous lemma. *)
  set (ptfam := pointwisefamily (@iter' ⦃ σ ⦄) f).
  set (ptfamdirec := pointwisefamily_isdirected (@iter' ⦃ σ ⦄)
                                                (iter'_isdirected ⦃ σ ⦄) f).
  apply (adequacy_lubs ptfam ptfamdirec).
  - intro n. induction n as [ | m IH].
    + use adequacy_least.
    + eapply adequacy_step.
      ++ use refl_trans_clos_hrel_extends. use hinhpr.
         use fixpstep.
      ++ exact (rel _ _ IH).
  - use pointwiselub_islubpointwise.
Defined.

Definition adequacy_allterms {σ : type} (t : term σ) : adequacy_relation σ (⟦ t ⟧) t.
Proof.
  induction t.
  - use adequacy_zero.
  - use adequacy_succ.
  - use adequacy_pred.
  - use adequacy_ifz.
  - use adequacy_fixp.
  - use adequacy_𝓀.
  - use adequacy_𝓈.
  - simpl. exact (IHt1 _ _ IHt2).
Defined.

Theorem adequacy (t : term ι) :
  ∏ (p : isdefined (⟦ t ⟧)), t ▹* numeral (value (⟦ t ⟧) p).
Proof.
  use (@adequacy_allterms ι t).
Qed.
