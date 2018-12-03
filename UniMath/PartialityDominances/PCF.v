Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.ClosureOfHrel.
Require Import UniMath.Algebra.DCPO.
Require Import UniMath.PartialityDominances.PartialElements.
Require Import UniMath.PartialityDominances.PartialFunctions.
Require Import UniMath.MoreFoundations.PropExt.

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
  | 0   => O
  | S m => m
  end.

Definition lifted_pred : 𝓛ℕ --> 𝓛ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : natset, η (P n)).
Defined.

Fixpoint lifted_ifz' (n : nat) (a b : 𝓛ℕ) : 𝓛ℕ :=
  match n with
  | 0   => a
  | S m => b
  end.

Definition lifted_ifz (a b : 𝓛ℕ) : 𝓛ℕ --> 𝓛ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : nat, lifted_ifz' n a b).
Defined.

Lemma nateq0orS (n : nat) : (n = 0) ⨿ (∑ (m : nat), n = S m).
Proof.
  destruct n.
  - use inl. use idpath.
  - use inr. split with n. use idpath.
Qed.

Lemma lifted_ifz_case_0 (a b l : 𝓛ℕ):
  ∏ (p : isdefined l), value l p = 0 -> pr1 (lifted_ifz a b) l = a.
Proof.
  intros p valueeq.
  induction l as [P pair]; induction pair as [isprop ϕ].
  unfold value in valueeq.
  unfold lifted_ifz. simpl.
  unfold Kleisli_extension; simpl.
  assert (valueeq' : ∏ (p' : P), ϕ p' = 0).
  { intro p'. rewrite <- valueeq.
    change ϕ with (value (P,,isprop,,ϕ)). use value_weaklyconstant. }
  use information_order_antisymmetric.
  - assert (t : isdefined (pr1 (lifted_ifz a b) (P,,isprop,,ϕ)) -> isdefined a).
    { intros [p' d].
      rewrite (valueeq' p') in d; simpl in d. exact d. }
    split with t.
    unfold value; simpl.
    intros [p' d].
    use eq_value_eq.
    rewrite (valueeq' p'). simpl.
    use idpath.
  - assert (s : isdefined a -> isdefined (pr1 (lifted_ifz a b) (P,,isprop,,ϕ))).
    { intro d. split with p.
      rewrite valueeq. simpl. exact d. }
    split with s.
    unfold value; simpl.
    intro d. use eq_value_eq. simpl.
    rewrite (valueeq' (pr1 (s d))).
    simpl; use idpath.
Qed.


Definition lifted_ifz : 𝓛ℕ --> (𝓛ℕ --> (𝓛ℕ --> 𝓛ℕ)).
Proof.
  use dcpomorphismpair.
  - intro a.
    use dcpomorphismpair.
    + intro b.
      exact (lifted_ifz a b).
    + intros I u isdirec v islubv.
      admit. (* Use alternative information_order (?) *)
      (* split.
      ++ intro i. intro l. simpl.
         induction l as [P pair]; induction pair as [isprop φ]; simpl in *.
         unfold Kleisli_extension; simpl.
         assert (t : (∑ (p : P), isdefined (ifz' (φ p) a (u i))) ->
                     (∑ (p : P), isdefined (ifz' (φ p) a v))).
         { intros [p di]. split with p.
           destruct (φ p).
           - simpl in *. exact di.
           - simpl in *. apply (pr1 (pr1 islubv i)). exact di. }
         split with t. intros t'; cbn; cbn in t'.
         set (s := t t').
         induction s as [p' d'].
         induction t' as [p di].
         assert (eq : p = p').
         { use proofirrelevance. exact isprop. }
         apply eq_value_eq.
         destruct (nateq0orS (φ p)) as [φpeq|φpeq'].
         +++ rewrite φpeq.
             rewrite ((!maponpaths φ eq) @ φpeq).
             use idpath.
         +++ induction φpeq' as [m φpeq]. rewrite φpeq.
             rewrite ((!maponpaths φ eq) @ φpeq).
             simpl. use (pr1 (information_order_eq_ifisdefined _ _)).
             exact (pr1 islubv i).
             rewrite φpeq in di. simpl in di. exact di.
      ++ intros f ineqs.
         unfold funcomp in ineqs.
         intro l.
         assert (t : isdefined (pr1 (lifted_ifz' a v) l) -> isdefined (pr1 f l)).
         {
           induction l as [P pair]; induction pair as [isprop φ].
           intros [p d].
           destruct (nateq0orS (φ p)) as [eql|eql'].
           - apply (@factor_through_squash I).
             + use isdefined_isaprop.
             + intro i. apply (ineqs i).
               simpl. split with p.
               rewrite eql. simpl.
               rewrite eql in d. simpl in d.
               exact d.
             + exact (pr1 isdirec).
           - apply (isdefinedlub_toprop u isdirec).
             + intros [i di].
               apply (ineqs i).
               split with p.
               induction eql' as [m eql].
               rewrite eql in *; simpl; simpl in d.
               exact di.
             + use isdefined_isaprop.
             + apply (@factor_through_squash I).
               ++ use isdefined_isaprop.
               ++ intro i. induction eql' as [m eql].
                  rewrite eql in d; simpl in d.
                  exact (transportf isdefined (lubsareunique u islubv
                        (mkdirectedlubinlift_islub u isdirec)) d).
               ++ exact (pr1 isdirec). }
         split with t. induction l as [P pair]; induction pair as [isprop φ].
         intros [p d]. unfold value; cbn.
         destruct (nateq0orS (φ p)) as [eql|eql'].
         +++ apply (@factor_through_squash I).
             * use (pr2 natset).
             * intro i.
               use eq_value_eq.
               rewrite eql. simpl. rewrite eql in d; simpl in d.
               assert (di : isdefined (ifz' (φ p) a (u i))).
               { rewrite eql. simpl. exact d. }
               assert (eq : pr1 (lifted_ifz' a (u i)) (P,,isprop,,φ) = pr1 f (P,,isprop,,φ)).
               { use (pr1 (information_order_eq_ifisdefined _ _)).
                 - use (ineqs i (P,,isprop,,φ)).
                 - simpl. split with p. rewrite eql; simpl. exact d. }
               assert (eq' : a = pr1 (lifted_ifz' a (u i)) (P,,isprop,,φ)).
               { use isdefined_value_eq.
                 - simpl. use propext.
                   + use isdefined_isaprop.
                   + use isaprop_total2.

               set (helper := g (p,,di)).
               simpl in helper.*)
  - admit.
Admitted.



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
           set (fpreslub := pr2 f I u isdirec v islubv).
           set (gpreslub := pr2 g I u isdirec v islubv).
           set (isdirecg := dcpomorphism_preservesdirected g isdirec).
           set (isdirecf := dcpomorphism_preservesdirected f isdirec).
           set (fpreslub' := pr2 (pr1 f v) I (pr1 g ∘ u) isdirecg _ gpreslub).
           use (pr2 fpreslub'). intro i.
           set (const := const_dcpomor B C c).
           change c with (const (pr1 g (u i))).
           unfold funcomp.
           assert (lubeq : (pr1 f v) = dcpomorphismpair
                                         (pointwiselub (pr1 f ∘ u) isdirecf)
                                         (pointwiselub_isdcpomorphism (pr1 f ∘ u) isdirecf)).
           { eapply lubsareunique.
             - exact fpreslub.
             - use pointwiselub_islub. }
           rewrite lubeq.
           use (pr2 (pointwiselub_islubpointwise (pr1 f ∘ u) isdirecf (pr1 g (u i)))).
           intro j.
           unfold pointwisefamily; simpl. unfold funcomp; simpl.
           use factor_through_squash. exact (directeduntruncated u i j).
           ** use dcpoorder_propvalued.
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
         use (pr2 (pr2 (f a) I ptfam ptfamisdirec
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