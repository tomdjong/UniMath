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

Fixpoint ifz' (n : nat) (a b : 𝓛ℕ) : 𝓛ℕ :=
  match n with
  | 0   => a
  | S m => b
  end.

Definition lifted_ifz' (a b : 𝓛ℕ) : 𝓛ℕ --> 𝓛ℕ.
Proof.
  eapply Kleisli_extension_dcpo.
  exact (λ n : nat, ifz' n a b).
Defined.

Lemma nateq0orS (n : nat) : (n = 0) ⨿ (∑ (m : nat), n = S m).
Proof.
  destruct n.
  - use inl. use idpath.
  - use inr. split with n. use idpath.
Qed.

Lemma lifted_ifz_case_0 (a b l : 𝓛ℕ):
  ∏ (p : isdefined l), value l p = 0 -> pr1 (lifted_ifz' a b) l = a.
Proof.
  intros p valueeq.
  induction l as [P pair]; induction pair as [isprop ϕ].
  unfold value in valueeq.
  unfold lifted_ifz'. simpl.
  unfold Kleisli_extension; simpl.
  assert (valueeq' : ∏ (p' : P), ϕ p' = 0).
  { intro p'. rewrite <- valueeq.
    change ϕ with (value (P,,isprop,,ϕ)). use value_weaklyconstant. }
  use information_order_antisymmetric.
  - assert (t : isdefined (pr1 (lifted_ifz' a b) (P,,isprop,,ϕ)) -> isdefined a).
    { intros [p' d].
      rewrite (valueeq' p') in d; simpl in d. exact d. }
    split with t.
    unfold value; simpl.
    intros [p' d].
    use eq_value_eq.
    rewrite (valueeq' p'). simpl.
    use idpath.
  - assert (s : isdefined a -> isdefined (pr1 (lifted_ifz' a b) (P,,isprop,,ϕ))).
    { intro d. split with p.
      rewrite valueeq. simpl. exact d. }
    split with s.
    unfold value; simpl.
    intro d. use eq_value_eq. simpl.
    rewrite (valueeq' (pr1 (s d))).
    simpl; use idpath.
Qed.

Lemma lifted_ifz_case_S (a b l : 𝓛ℕ):
  ∏ (p : isdefined l), (∑ (m : nat), value l p = S m) -> pr1 (lifted_ifz' a b) l = b.
Proof.
  intros p valueeqsum.
  induction l as [P pair]; induction pair as [isprop ϕ].
  unfold value in valueeqsum. induction valueeqsum as [m valueeq].
  unfold lifted_ifz'. simpl.
  unfold Kleisli_extension; simpl.
  assert (valueeq' : ∏ (p' : P), ϕ p' = S m).
  { intro p'. rewrite <- valueeq.
    change ϕ with (value (P,,isprop,,ϕ)). use value_weaklyconstant. }
  use information_order_antisymmetric.
  - assert (t : isdefined (pr1 (lifted_ifz' a b) (P,,isprop,,ϕ)) -> isdefined b).
    { intros [p' d].
      rewrite (valueeq' p') in d; simpl in d. exact d. }
    split with t.
    unfold value; simpl.
    intros [p' d].
    use eq_value_eq.
    rewrite (valueeq' p'). simpl.
    use idpath.
  - assert (s : isdefined b -> isdefined (pr1 (lifted_ifz' a b) (P,,isprop,,ϕ))).
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
      exact (lifted_ifz' a b).
    + intros I u isdirec v islubv.
      split.
      * intros i l. unfold funcomp.
         induction l as [P pair]; induction pair as [isprop φ].
         use (pr2 (information_order_eq_ifisdefined _ _)).
         intros [p d].
         destruct (nateq0orS (φ p)) as [φpeq | φpeq'].
         ** rewrite φpeq in d.
             etrans.
             *** apply (lifted_ifz_case_0 a (u i) (P,,isprop,,φ) p φpeq).
             *** apply (!(lifted_ifz_case_0 a v (P,,isprop,,φ) p φpeq)).
         ** induction φpeq' as [m φpeq].
            etrans.
            *** apply (lifted_ifz_case_S a (u i) (P,,isprop,,φ) p (m,,φpeq)).
            *** etrans.
                **** rewrite φpeq in d. simpl in d.
                     set (ineq := (pr1 islubv i)).
                     apply (pr1 (information_order_eq_ifisdefined _ _) ineq d).
                **** apply (!(lifted_ifz_case_S a v (P,,isprop,,φ) p (m,,φpeq))).
      * intros f ineqs l.
         induction l as [P pair]; induction pair as [isprop φ].
         use (pr2 (information_order_eq_ifisdefined _ _)).
         intros [p d].
         destruct (nateq0orS (φ p)) as [φpeq | φpeq'].
         ** etrans.
            *** apply (lifted_ifz_case_0 a v (P,,isprop,,φ) p φpeq).
            *** eapply (@factor_through_squash I).
                **** use (pr2 (dcpocarrier (liftdcpowithleast natset))).
                **** intro i. set (ineq := ineqs i (P,,isprop,,φ)).
                     unfold funcomp in ineq.
                     set (eq := !(lifted_ifz_case_0 a (u i) (P,,isprop,,φ) p φpeq)).
                     set (helper := pr1 (information_order_eq_ifisdefined _ _) ineq).
                     assert (d' : isdefined (pr1 (lifted_ifz' a (u i)) (P,,isprop,,φ))).
                     { split with p. rewrite φpeq in *. simpl; simpl in d; exact d. }
                     set (eq' := helper d').
                     exact (eq @ eq').
                **** exact (pr1 isdirec).
         ** induction φpeq' as [m φpeq].
            eapply (isdefinedlub_toprop u isdirec).
            *** intros [i di].
                etrans.
                **** apply (lifted_ifz_case_S a v (P,,isprop,,φ) p (m,,φpeq)).
                **** etrans.
                     ***** set (ineq := pr1 islubv i).
                           apply (!(pr1 (information_order_eq_ifisdefined _ _) ineq) di).
                     ***** etrans.
                           ****** apply (!(lifted_ifz_case_S a (u i) (P,,isprop,,φ) p (m,,φpeq))).
                           ****** apply (pr1 (information_order_eq_ifisdefined _ _) (ineqs i _)).
                                  split with p. rewrite φpeq. simpl. exact di.
            *** use (pr2 (dcpocarrier (liftdcpowithleast natset))).
            *** rewrite φpeq in d. simpl in d.
                assert (lubeq : v = mkdirectedlubinlift u isdirec).
                { eapply (lubsareunique u).
                  - exact islubv.
                  - use mkdirectedlubinlift_islub. }
                exact (transportf isdefined lubeq d).
  - intros I u isdirec v islubv; split.
    + intro i; simpl.
      intros l l'.
      use (pr2 (information_order_eq_ifisdefined _ _)).
      induction l' as [Q pair]; induction pair as [isprop' ψ].
      intros [q d].
      change (((λ n : nat, ifz' n (u i) l) #)%PartialFunctionsDCPO (Q,,isprop',,ψ))
      with (pr1 (lifted_ifz' (u i) l) (Q,,isprop',,ψ)).
      change (((λ n : nat, ifz' n v l) #)%PartialFunctionsDCPO (Q,,isprop',,ψ))
      with (pr1 (lifted_ifz' v l) (Q,,isprop',,ψ)).
      destruct (nateq0orS (ψ q)) as [ψqeq | ψqeq'].
      * etrans.
        ** apply (lifted_ifz_case_0 (u i) l (Q,,isprop',,ψ) q ψqeq).
        ** etrans.
           *** apply (pr1 (information_order_eq_ifisdefined _ _) (pr1 islubv i)).
               rewrite ψqeq in d. exact d.
           *** apply (!(lifted_ifz_case_0 v l (Q,,isprop',,ψ) q ψqeq)).
      * induction ψqeq' as [m ψqeq].
        etrans.
        ** apply (lifted_ifz_case_S (u i) l (Q,,isprop',,ψ) q (m,,ψqeq)).
        ** apply (!(lifted_ifz_case_S v l (Q,,isprop',,ψ) q (m,,ψqeq))).
    + intros f ineqs; simpl in ineqs; simpl.
      intros l l'. use (pr2 (information_order_eq_ifisdefined _ _)).
      induction l' as [Q pair]; induction pair as [isprop' ψ].
      intros [q d].
      destruct (nateq0orS (ψ q)) as [ψqeq | ψqeq'].
      * change (((λ n : nat, ifz' n v l) #)%PartialFunctionsDCPO (Q,,isprop',,ψ)) with
        (pr1 (lifted_ifz' v l) (Q,,isprop',,ψ)).
        etrans.
        ** apply (lifted_ifz_case_0 v l (Q,,isprop',,ψ) q ψqeq).
        ** eapply (isdefinedlub_toprop u isdirec).
           *** intros [i di]. etrans.
               **** apply pathsinv0.
                    apply (pr1 (information_order_eq_ifisdefined _ _) (pr1 islubv i)).
                    exact di.
               **** etrans.
                    ***** apply (!(lifted_ifz_case_0 (u i) l (Q,,isprop',,ψ) q ψqeq)).
                    ***** apply (pr1 (information_order_eq_ifisdefined _ _) (ineqs i _ _)).
                          simpl. split with q. rewrite ψqeq; simpl. exact di.
           *** use (pr2 (dcpocarrier 𝓛ℕ)).
           *** assert (lubeq : v = mkdirectedlubinlift u isdirec).
               { eapply (lubsareunique u).
                 - exact islubv.
                 - use mkdirectedlubinlift_islub. }
               rewrite ψqeq in d; simpl in d.
               exact (transportf isdefined lubeq d).
      * change (((λ n : nat, ifz' n v l) #)%PartialFunctionsDCPO (Q,,isprop',,ψ)) with
        (pr1 (lifted_ifz' v l) (Q,,isprop',,ψ)).
        induction ψqeq' as [m ψqeq].
        etrans.
        ** apply (lifted_ifz_case_S v l (Q,,isprop',,ψ) q (m,,ψqeq)).
        ** eapply (@factor_through_squash I).
           *** use (pr2 (dcpocarrier 𝓛ℕ)).
           *** intro i.
               set (ineq := ineqs i l (Q,,isprop',,ψ)).
               change (((λ n : nat, ifz' n (u i) l)# )%PartialFunctionsDCPO (Q,,isprop',,ψ))
               with (pr1 (lifted_ifz' (u i) l) (Q,,isprop',,ψ)) in ineq.
               set (eq := lifted_ifz_case_S (u i) l (Q,,isprop',,ψ) q (m,,ψqeq)).
               etrans.
               **** apply (!eq).
               **** apply (pr1 (information_order_eq_ifisdefined _ _) ineq).
                    simpl. split with q. rewrite ψqeq in *. exact d.
           *** exact (pr1 isdirec).
Defined.

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

Lemma adequacy_relation_propvalued {σ : type} (l : ⦃ σ ⦄) (t : term σ) :
  isaprop (adequacy_relation σ l t).
Proof.
  induction σ as [ | τ IH ρ IH'].
  - simpl. use impred.
    intro p. use isapropishinh.
  - simpl. use impred; intro m;
             use impred; intro s; use impred; intro rel.
    use IH'.
Qed.

Lemma adequacy_least {σ : type} (t : term σ) :
  adequacy_relation σ (dcpowithleast_least ⦃ σ ⦄) t.
Proof.
  induction σ as [ | τ IH ρ IH'].
  - simpl. intro p. destruct p.
  - simpl. intros m s rel. exact (IH' (t ` s)).
Qed.

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

Lemma adequacy_step {σ : type} (s t : term σ) (l : ⦃ σ ⦄) :
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
Qed.

Lemma adequacy_zero : adequacy_relation ι (η O) zero.
Proof.
  simpl. intro t. use hinhpr.
  use refl_trans_clos_refl.
Qed.

Lemma succbigstep (s t : term ι) : bigstep s t -> bigstep (succ ` s) (succ ` t).
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

Lemma adequacy_succ : adequacy_relation (ι ⇨ ι) lifted_succ succ.
Proof.
  intros l t rel q.
  induction q as [p q'].
  set (reduces := rel p).
  change (numeral (value (pr1 lifted_succ l) (p,,q'))) with
  (succ ` (numeral (value l p))).
  apply succbigstep. exact reduces.
Qed.

Lemma predbigstep (s t : term ι) : bigstep s t -> bigstep (pred ` s) (pred ` t).
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

Lemma adequacy_pred : adequacy_relation (ι ⇨ ι) lifted_pred pred.
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
Qed.

Lemma ifzbigstep (s t r r' : term ι) : bigstep r r' ->
                                            bigstep (ifz ` s ` t ` r) (ifz ` s ` t ` r').
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

Lemma adequacy_ifz : adequacy_relation (ι ⇨ ι ⇨ ι ⇨ ι) lifted_ifz ifz.
Proof.
  intros l1 t1 rel1 l2 t2 rel2 l3 t3 rel3.
  induction l3 as [P pair]; induction pair as [isprop φ].
  intros [p d].
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
    exact (ifzad d').
Qed.

Lemma adequacy_𝓀 {σ τ : type} : adequacy_relation (σ ⇨ τ ⇨ σ) 𝓀_dcpo 𝓀.
Proof.
  intros l t rel m s rel'.
  simpl.
  eapply adequacy_step.
  - use refl_trans_clos_hrel_extends.
    use hinhpr.
    use 𝓀step.
  - exact rel.
Qed.

Lemma adequacy_𝓈 {σ τ ρ : type} : adequacy_relation
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
Qed.

Lemma adequacy_lubs {σ : type} {I : UU} (u : I -> ⦃ σ ⦄) (isdirec : isdirected u)
      (t : term σ) : (∏ (i : I), adequacy_relation σ (u i) t) ->
                     ∏ (v : ⦃ σ ⦄), islub u v -> adequacy_relation σ v t.
Proof.
  induction σ as [ | τ IH ρ IH'].
  - intro adequacy_I.
    intros v islubv p.
    assert (lubeq : v = mkdirectedlubinlift u isdirec).
    { eapply (lubsareunique u).
      - exact islubv.
      - use mkdirectedlubinlift_islub. }
    set (p' := transportf isdefined lubeq p).
    eapply (isdefinedlub_toprop u isdirec).
    + intros [i di].
      rewrite (eq_value_eq lubeq p p').
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
      use pointwiselub_islubpointwise.
Qed.

Lemma adequacy_fixp {σ : type} : adequacy_relation ((σ ⇨ σ) ⇨ σ) leastfixedpoint fixp.
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

Lemma adequacy_allterms {σ : type} (t : term σ) : adequacy_relation σ (⟦ t ⟧) t.
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
Qed.

Theorem adequacy (t : term ι) :
  ∏ (p : isdefined (⟦ t ⟧)), t ⇓ numeral (value (⟦ t ⟧) p).
Proof.
  use (@adequacy_allterms ι t).
Qed.

Theorem soudness {σ : type} (s t : term σ) : s ⇓ t -> (⟦ s ⟧) = (⟦ t ⟧).
Proof.
  intro step.
  use (@factor_through_squash ((refl_trans_clos smallstep) s t)).
  - use setproperty.
  - intro step'.
    induction step'.
    + use (@factor_through_squash (smallstep' σ x y)).
      ++ use setproperty.
      ++ intro step'.
         induction step'.
         +++ simpl.
             use fun_extension_after_η.
         +++ simpl.
             etrans.
             ++++ apply pathsinv0. use extension_comp.
             ++++ change (λ n : nat, η (S n)) with (η ∘ S).
                  rewrite funcomp_assoc.
                  rewrite (funextfun _ _ (fun_extension_after_η _)).
                  change ((λ n : nat, η (P n)) ∘ S) with (@lift_embedding natset).
                  use η_extension.
         +++ simpl. use fun_extension_after_η.
         +++ simpl. etrans.
             ++++ apply pathsinv0. use extension_comp.
             ++++ change (λ n : nat, η (S n)) with (η ∘ S).
                  rewrite funcomp_assoc.
                  rewrite (funextfun _ _ (fun_extension_after_η _)).
                  unfold funcomp. simpl.
                  (* The problem is with the operational semantics! *)

         +++ use pathsinv0. use leastfixedpoint_isfixedpoint.
         +++ use idpath.
         +++ use idpath.
         +++ simpl. apply (@eqtohomot _ _ (pr1 (⟦ s ⟧)) (pr1 (⟦ t ⟧))).
        (* Three times the 'same' proof. *)
             use maponpaths.
             apply IHstep'.
             ++++ use refl_trans_clos_hrel_extends.
                  use hinhpr. exact step'.
             ++++ use hinhpr. exact step'.
         +++ simpl; use maponpaths.
             apply IHstep'.
             ++++ use refl_trans_clos_hrel_extends;
                    use hinhpr; exact step'.
             ++++ use hinhpr; exact step'.
         +++ simpl; use maponpaths.
             apply IHstep'.
             ++++ use refl_trans_clos_hrel_extends;
                    use hinhpr; exact step'.
             ++++ use hinhpr; exact step'.
         +++ simpl; use maponpaths.
             apply IHstep'.
             ++++ use refl_trans_clos_hrel_extends;
                    use hinhpr; exact step'.
             ++++ use hinhpr; exact step'.
      ++ exact h.
    + use idpath.
    + etrans.
      ++ apply IHstep'1.
         use hinhpr. exact step'1.
      ++ apply IHstep'2.
         use hinhpr. exact step'2.
  - exact step.
Qed.