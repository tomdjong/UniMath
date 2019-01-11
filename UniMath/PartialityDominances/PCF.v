Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.ClosureOfHrel.
Require Import UniMath.Algebra.DCPO.
Require Import UniMath.PartialityDominances.PartialElements.
Require Import UniMath.PartialityDominances.PartialFunctions.
Require Import UniMath.MoreFoundations.PropExt.
Require Import Coq.Init.Specif.

Inductive type : UU :=
  | base       : type
  | functional : type -> type -> type.

Delimit Scope PCF with PCF.
Local Open Scope PCF.

Notation "'ι'" := base : PCF.
(* Check level? *)
Notation "σ ⇨ τ" := (functional σ τ) (at level 60, right associativity) : PCF.

Fixpoint typecode (σ τ : type) : UU :=
  match σ with
  | ι       => match τ with
               | ι       => unit
               | τ ⇨ ρ   => empty
               end
  | σ₁ ⇨ σ₂ => match τ with
               | ι       => empty
               | τ₁ ⇨ τ₂ => (typecode σ₁ τ₁) × (typecode σ₂ τ₂)
               end
  end.

Fixpoint typeleft (σ : type) : type :=
  match σ with
  | ι     => ι
  | τ ⇨ _ => τ
  end.

Fixpoint typeright (σ : type) : type :=
  match σ with
  | ι     => ι
  | _ ⇨ ρ => ρ
  end.

Definition refl_typecode (σ : type) : typecode σ σ.
Proof.
  induction σ.
  - exact tt.
  - exact (IHσ1,,IHσ2).
Defined.

Definition type_encode (σ τ : type) : σ = τ -> typecode σ τ.
Proof.
  intro eq.
  exact (transportf (typecode σ) eq (refl_typecode σ)).
Defined.

Definition typehasdeceq : isdeceq type.
Proof.
  intro σ. induction σ.
  - intro τ. induction τ.
    + apply inl. apply idpath.
    + apply inr. intro eq.
      exact (type_encode _ _ eq).
  - intro τ. induction τ.
    + apply inr. intro eq.
      exact (type_encode _ _ eq).
    + induction (IHσ1 τ1) as [eq1 | neq1].
      induction (IHσ2 τ2) as [eq2 | neq2].
      ++ apply inl.
         exact (map_on_two_paths functional eq1 eq2).
      ++ apply inr. intro eq'. apply neq2.
         exact (maponpaths typeright eq').
      ++ apply inr. intro eq'. apply neq1.
         exact (maponpaths typeleft eq').
Defined.

Definition type_decode : ∏ (σ τ : type), typecode σ τ -> σ = τ.
Proof.
  intro σ. induction σ.
  - intros τ c. induction τ.
    + apply idpath.
    + induction c.
  - intros τ c. induction τ.
    + induction c.
    + induction c as [c1 c2]. apply map_on_two_paths.
      ++ apply IHσ1.
         exact c1.
      ++ apply IHσ2.
         exact c2.
Defined.

Definition functtransportf2 {X Y Z : UU} (f : X -> Y -> Z) (P : Z -> UU) {x x' : X} {y y' : Y}
           (ex : x = x') (ey : y = y') (p : P (f x y)) :
  transportf (λ z : X × Y, P (f (pr1 z) (pr2 z))) (@dirprod_paths X Y (x,,y) (x',,y') ex ey) p =
  transportf P (map_on_two_paths f ex ey) p.
Proof.
  induction ex, ey. apply idpath.
Defined.

Definition transportf_dirprod_pr1 {X Y : UU} (P : X -> UU) {x x' : X} {y y' : Y}
           (ex : x = x') (ey : y = y') (p : P x) :
  transportf (λ a : X × Y, P (pr1 a)) (@dirprod_paths X Y (x,,y) (x',,y') ex ey) p =
  transportf P ex p.
Proof.
  induction ex, ey. apply idpath.
Defined.

Definition transportf_dirprod_pr2 {X Y : UU} (P : Y -> UU) {x x' : X} {y y' : Y}
           (ex : x = x') (ey : y = y') (p : P y) :
  transportf (λ a : X × Y, P (pr2 a)) (@dirprod_paths X Y (x,,y) (x',,y') ex ey) p =
  transportf P ey p.
Proof.
  induction ex, ey. apply idpath.
Defined.

Definition typeeq_typecode_equiv (σ τ : type) : σ = τ ≃ typecode σ τ.
Proof.
  use weq_iso.
  - apply type_encode.
  - apply type_decode.
  - intro p. induction p.
    unfold type_encode.
    rewrite idpath_transportf.
    induction σ.
    + apply idpath.
    + simpl. rewrite IHσ1. rewrite IHσ2. apply idpath.
  - generalize τ as ρ. clear τ. induction σ.
    + intros ρ c. induction ρ.
      ++ induction c. apply iscontrunit.
      ++ induction c.
    + intros ρ c. induction ρ.
      ++ induction c.
      ++ induction c as [c1 c2]. simpl. unfold type_encode.
         set (IH1 := IHσ1 ρ1 c1).
         set (IH2 := IHσ2 ρ2 c2).
         assert (lem : transportf (typecode (σ1 ⇨ σ2))
                                  (map_on_two_paths functional
                                                    (type_decode σ1 ρ1 c1)
                                                    (type_decode σ2 ρ2 c2))
                                                    (refl_typecode (σ1 ⇨ σ2)) =
                       transportf (typecode σ1) (type_decode σ1 ρ1 c1) (refl_typecode σ1) ,,
                       transportf (typecode σ2) (type_decode σ2 ρ2 c2) (refl_typecode σ2)).
         { rewrite <- functtransportf2.
           change (λ z : type × type, typecode (σ1 ⇨ σ2) (pr1 z ⇨ pr2 z)) with
           (λ z : type × type, (typecode σ1 (pr1 z)) × typecode σ2 (pr2 z)).
           etrans.
           - (* I would use transportf_dirprod here, but for some reason Coq
                does not like it. *)
             set (p := @dirprod_paths type type (σ1,,σ2) (ρ1,,ρ2)
                                      (type_decode σ1 ρ1 c1) (type_decode σ2 ρ2 c2)).
             set (A := type × type : UU).
             set (B1 := λ a : A, typecode σ1 (pr1 a)).
             set (B2 := λ a : A, typecode σ2 (pr2 a)).
             set (x := ((σ1,,σ2),,refl_typecode (σ1 ⇨ σ2)) : ∑ (a : A), B1 a × B2 a).
             set (x' := ((ρ1,,ρ2),,(c1,,c2)) : ∑ (a : A), B1 a × B2 a).
             change (λ z : A, typecode σ1 (pr1 z) × typecode σ2 (pr2 z)) with
                    (λ a : A, B1 a × B2 a).
             change (refl_typecode (σ1 ⇨ σ2)) with (pr2 x).
             assert (helper : transportf (λ a : A, B1 a × B2 a) p (pr2 x) =
                     dirprodpair (transportf (λ a : A, B1 a) p (pr1 (pr2 x)))
                                 (transportf (λ a : A, B2 a) p (pr2 (pr2 x)))).
             { generalize p as p'. clear x' p. induction p'; use idpath. }
             apply helper.
           - simpl. apply dirprod_paths.
             + simpl. rewrite transportf_dirprod_pr1. apply idpath.
             + simpl. rewrite transportf_dirprod_pr2. apply idpath. }
         rewrite lem. apply dirprod_paths; simpl.
         +++ exact IH1.
         +++ exact IH2.
Defined.

Definition decidableweq {X Y : UU} (w : X ≃ Y) : decidable X -> decidable Y.
Proof.
  intro decX.
  induction decX as [x | nx].
  - exact (inl (w x)).
  - apply inr. intro y. apply nx.
    exact (invmap w y).
Defined.

Lemma typehasdeceq' : isdeceq type.
Proof.
  intros σ τ.
  apply (decidableweq (invweq (typeeq_typecode_equiv σ τ))).
  generalize τ as ρ. clear τ. induction σ.
  - induction ρ.
    + apply inl. exact tt.
    + apply inr. exact fromempty.
  - induction ρ.
    + apply inr. exact fromempty.
    + set (IH1 := IHσ1 ρ1); set (IH2 := IHσ2 ρ2).
      induction IH1 as [c1 | nc1]. induction IH2 as [c2 | nc2].
      ++ exact (inl (c1,,c2)).
      ++ apply inr. intro d. induction d as [d1 d2].
         apply nc2. exact d2.
      ++ apply inr. intro d. induction d as [d1 d2].
         apply nc1. exact d1.
Qed.


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
  | ifzsuccstep (s t : term ι) (n : nat) : smallstep' ι (ifz ` s ` t ` (succ ` (numeral n))) t
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

(* Definition smallstep'_rightextensional (σ : type) (s t r : term σ) :
  smallstep' σ s t -> smallstep' σ s r -> t = r.
Proof.
  intro step1. induction step1.
  - induction r. *)

Definition smallstep'_rightextensional (σ : type) (s t : term σ) :
  smallstep' σ s t -> ∏ (τ : type) (r : term τ) (typeeq : σ = τ),
                         smallstep' σ s (transportb term typeeq r) -> t = (transportb term typeeq r).
Proof.
  intros step1. induction step1.
  - intros τ r typeeq step2. induction r.
    + admit. (* Easy *)
    + admit. (* Type non-sense *)
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + (* term non-sense *) admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - intros ρ p typeeq step2.





  - inversion step2.

  induction s.
  - inversion_clear step1.
  - inversion_clear step1.
  - inversion_clear step1.
  - inversion_clear step1.
  - inversion_clear step1.
  - inversion_clear step1.
  - inversion_clear step1.
  - induction t.
    + inversion_clear step1.
*)

(*Definition sumdec_smallstep' (σ : type) (s : term σ) :
  decidable (∑ (t : term σ), smallstep' σ s t).
Proof.
  induction s.
  - apply inr.
    intros [t rel].
    inversion_clear rel.
  - apply inr. intros [t rel]. inversion_clear rel.
  - apply inr. intros [t rel]. inversion_clear rel.
  - apply inr. intros [t rel]. inversion_clear rel.
  - apply inr. intros [t rel]. inversion_clear rel.
  - apply inr. intros [t rel]. inversion_clear rel.
  - apply inr. intros [t rel]. inversion_clear rel.
  - induction IHs1 as [pos | npos].
    + induction pos as [t step].
      apply inl. exists (t ` s2).
      apply appstep. exact step.
    + induction s1.
      ++ induction s1.
      apply inr. intro step'.
      induction step' as [t step]. induction t.
      ++ inversion_clear step.
      ++
*)

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

Lemma denotational_semantics_numerals (n : nat) : ⟦ numeral n ⟧ = η n.
Proof.
  induction n as [ | m IHm].
  - use idpath.
  - simpl. rewrite IHm. use fun_extension_after_η.
Qed.

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

Theorem soundness {σ : type} (s t : term σ) : s ⇓ t -> (⟦ s ⟧) = (⟦ t ⟧).
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
         +++ change (succ ` numeral n) with (numeral (S n)).
             change (⟦ ifz ` s ` t ` numeral (S n) ⟧) with
             (pr1 (⟦ ifz ` s ` t ⟧) (⟦ numeral (S n) ⟧)).
             rewrite (denotational_semantics_numerals (S n)).
             simpl. use fun_extension_after_η.

             (* simpl. etrans.
             ++++ apply pathsinv0. use extension_comp.
             ++++ change (λ n : nat, η (S n)) with (η ∘ S).
                  rewrite funcomp_assoc.
                  rewrite (funextfun _ _ (fun_extension_after_η _)).
                  unfold funcomp. simpl.
                  rewrite (denotational_semantics_numerals n).
                  use fun_extension_after_η. *)
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

Theorem isdefined_pcf (t : term ι) :
  isdefined (⟦ t ⟧) <-> ∑ (n : nat), t ⇓ numeral n.
Proof.
  split.
  - intro p.
    split with (value (⟦ t ⟧) p).
    use adequacy.
  - intros [n step].
    assert (denoteq : ⟦ t ⟧ = η n).
    { etrans.
      - eapply soundness.
        exact step.
      - use denotational_semantics_numerals. }
    rewrite denoteq.
    exact tt.
Qed.
