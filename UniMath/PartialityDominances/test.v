Require Import UniMath.Foundations.All.

Inductive type : UU :=
  | base       : type
  | functional : type -> type -> type.

Delimit Scope test with test.
Local Open Scope test.

Notation "'ι'" := base : test.
Notation "σ ⇨ τ" := (functional σ τ) (at level 60, right associativity) : test.

(* Alternatively, we could write these as regular Definitions using the
   induction tactic. *)
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

Inductive term : type -> UU :=
  | zero                : term ι
  | succ                : term (ι ⇨ ι)
  | app  {σ τ : type}   : term (σ ⇨ τ) -> term σ -> term τ.

Notation "s ` t" := (app s t) (at level 50, left associativity) : test.

Definition termcode {σ : type} : term σ -> term σ -> UU.
Proof.
  intro s. induction s as [| | σ1 σ2 s1 IHs1 s2 IHs2].
  - (* s is zero *)
    intro t. induction t.
    + (* t is zero *)
      exact unit.
    + (* t is succ *)
      exact empty.
    + (* t is t1 ` t2 *)
      exact empty.
  - (* s is succ *)
    intro t. induction t.
    + exact empty.
    + exact unit.
    + exact empty.
  - (* s is s1 ` s2 *)
    intro t. induction t as [| | τ1 τ2 t1 _ t2 _].
    + exact empty.
    + exact empty.
    + (* t is t1 ` t2 *)
      induction (typehasdeceq σ1 τ1) as [eq1 | neq1].
      ++ apply dirprod.
         +++ apply IHs1.
             (* Are s1 and t1 'equal'? *)
             exact (transportb (λ x, term (x ⇨ τ2)) eq1 t1).
         +++ apply IHs2.
             (* Are s2 and t2 'equal'? *)
             exact (transportb term eq1 t2).
      ++ exact empty.
Defined.

Definition idpath_transportb {X : UU} (P : X -> UU) {x : X} (p : P x) :
  transportb P (idpath x) p = p.
Proof.
  apply idpath.
Defined.

Definition refl_termcode {σ : type} (t : term σ) : termcode t t.
Proof.
  induction t.
  - exact tt.
  - exact tt.
  - simpl. unfold coprod_rect.
    induction (typehasdeceq σ σ) as [eq | neq].
    + assert (eqistriv : eq = idpath σ).
      { apply proofirrelevance.
        apply isasetifdeceq.
        exact typehasdeceq. }
      rewrite eqistriv.
      rewrite idpath_transportb.
      rewrite idpath_transportb.
      exact (IHt1,,IHt2).
    + apply neq. apply idpath.
Defined.

Definition term_encode {σ : type} (s t : term σ) : s = t -> termcode s t.
Proof.
  intro eq.
  exact (transportf (termcode s) eq (refl_termcode s)).
Defined.

Definition term_right {σ : type} (s : term σ) : ∑ (τ : type), term τ.
Proof.
  induction s.
  - exact (ι,,zero).
  - exact ((ι ⇨ ι),,succ).
  - exact (σ,,s2).
Defined.

Definition term_right_app {σ τ : type} (s : term (σ ⇨ τ)) (t : term σ) :
  term_right (s ` t) = (σ,,t).
Proof.
  apply idpath.
Defined.

Definition term_left {σ : type} (s : term σ) : ∑ (τ : type), term τ.
Proof.
  induction s.
  - exact (ι,,zero).
  - exact ((ι ⇨ ι),,succ).
  - exact ((σ ⇨ τ),,s1).
Defined.

Definition term_left_app {σ τ : type} (s : term (σ ⇨ τ)) (t : term σ) :
  term_left (s ` t) = ((σ ⇨ τ),,s).
Proof.
  apply idpath.
Defined.

Definition termhasdeceq_transportb {σ : type} (s : term σ) :
  ∏ (τ : type) (typeeq : σ = τ) (t : term τ),
  decidable (s = transportb term typeeq t).
Proof.
  induction s as [| | σ1 σ2 s1 IHs1 s2 IHs2].
  - intros τ typeeq. induction t.
    + apply inl.
      assert (eqlem : typeeq = idpath ι).
      { apply proofirrelevance. apply isasetifdeceq. exact typehasdeceq. }
      rewrite eqlem.
      apply idpath.
    + apply fromempty.
      exact (type_encode _ _ typeeq).
    + apply inr. intro eq.
      set (t1' := transportb (λ ρ : type, term (σ ⇨ ρ)) typeeq t1); simpl in t1'.
      set (t3 := transportb term typeeq (t1 ` t2)).
      assert (termeq : t3 = t1' ` t2).
      { unfold t1', t3. generalize typeeq as e. induction e. apply idpath. }
      set (c := term_encode zero t3 eq).
      rewrite termeq in c.
      apply c.
  - intros τ typeeq. induction t.
    + apply inr. apply fromempty.
      exact (type_encode _ _ typeeq).
    + apply inl.
      assert (eqlem : typeeq = idpath _).
      { apply proofirrelevance, isasetifdeceq; exact typehasdeceq. }
      rewrite eqlem. apply idpath.
    + apply inr. intro eq.
      set (t1' := transportb (λ ρ : type, term (σ ⇨ ρ)) typeeq t1); simpl in t1'.
      set (t3 := transportb term typeeq (t1 ` t2)).
      assert (termeq : t3 = t1' ` t2).
      { unfold t1', t3. generalize typeeq as e. induction e. apply idpath. }
      set (c := term_encode succ t3 eq).
      rewrite termeq in c.
      apply c.
  - intros τ typeeq. induction t as [| | τ1 τ2 t1 _ t2 _ ].
    + apply inr. intro eq.
      set (s1' := transportf (λ ρ : type, term (σ1 ⇨ ρ)) typeeq s1); simpl in s1'.
      set (s3 := s1' ` s2).
      assert (termeq1 : transportf _ typeeq (s1 ` s2) = s3).
      { clear eq. induction typeeq. apply idpath. }
      assert (termeq2 : transportf _ typeeq (transportb term typeeq zero) = zero).
      { rewrite transport_f_b. rewrite pathsinv0l. apply idpath. }
      assert (termeq : s3 = zero).
      { rewrite <- termeq1, <- termeq2.
        apply maponpaths.
        exact eq. }
      exact (term_encode s3 zero termeq).
    + apply inr. intro eq.
      set (s1' := transportf (λ ρ : type, term (σ1 ⇨ ρ)) typeeq s1); simpl in s1'.
      set (s3 := s1' ` s2).
      assert (termeq1 : transportf _ typeeq (s1 ` s2) = s3).
      { clear eq. induction typeeq. apply idpath. }
      assert (termeq2 : transportf _ typeeq (transportb term typeeq succ) = succ).
      { rewrite transport_f_b. rewrite pathsinv0l. apply idpath. }
      assert (termeq : s3 = succ).
      { rewrite <- termeq1, <- termeq2.
        apply maponpaths.
        exact eq. }
      exact (term_encode s3 succ termeq).
    + induction (typehasdeceq σ1 τ1) as [eq1 | neq1].
      induction (typehasdeceq σ2 τ2) as [eq2 | neq2].
      ++ set (eqfunc := map_on_two_paths functional eq1 eq2).
         set (dec_s2t2 := IHs2 τ1 eq1 t2).
         set (dec_s1t1 := IHs1 (τ1 ⇨ τ2) eqfunc t1).
         induction (dec_s1t1) as [term_eq1 | term_neq1].
         induction (dec_s2t2) as [term_eq2 | term_neq2].
         +++ apply inl.
             rewrite term_eq1, term_eq2.
             assert (helper : typeeq = eq2).
             { apply proofirrelevance. apply isasetifdeceq. apply typehasdeceq. }
             rewrite helper.
             unfold eqfunc.
             generalize eq1 as x. generalize eq2 as y.
             induction x. induction y. apply idpath.
         +++ apply inr. intro term_eq.
             apply term_neq2.
             set (term_eq2 := maponpaths term_right term_eq).
             assert (helper : term_right (transportb term typeeq (t1 ` t2)) =
                     (σ1,,transportb term eq1 t2)).
             { generalize typeeq as x. generalize eq1 as y.
               induction x, y. apply idpath. }
             rewrite helper in term_eq2.
             rewrite term_right_app in term_eq2.
             apply total2_paths_equiv in term_eq2.
             induction term_eq2 as [tyeq tmeq]; simpl in tyeq.
             assert (patheq : tyeq = idpath σ1).
             { apply proofirrelevance. apply isasetifdeceq. apply typehasdeceq. }
             rewrite patheq in tmeq. exact tmeq.
         +++ apply inr. intro term_eq.
             apply term_neq1.
             set (term_eq2 := maponpaths term_left term_eq).
             assert (helper : term_left (transportb term typeeq (t1 ` t2)) =
                              ((σ1 ⇨ σ2),,transportb term eqfunc t1)).
             { unfold eqfunc.
               assert (patheq : typeeq = eq2).
               { apply proofirrelevance, isasetifdeceq, typehasdeceq. }
               rewrite patheq.
               generalize eq1 as x. generalize eq2 as y.
               clear eqfunc dec_s1t1 term_neq1.
               induction x, y. apply idpath. }
             rewrite helper in term_eq2.
             rewrite term_left_app in term_eq2.
             apply total2_paths_equiv in term_eq2.
             induction term_eq2 as [tyeq tmeq]; simpl in tyeq.
             assert (patheq : tyeq = idpath _).
             { apply proofirrelevance, isasetifdeceq, typehasdeceq. }
             rewrite patheq in tmeq. exact tmeq.
      ++ apply fromempty.
         apply neq2. exact typeeq.
      ++ apply inr. intro termeq.
         apply neq1.
         set (eq := maponpaths term_right termeq).
         rewrite term_right_app in eq.
         apply total2_paths_equiv in eq.
         induction eq as [tyeq tmeq]; simpl in tyeq.
         assert (helper : pr1 (term_right (transportb term typeeq (t1 ` t2))) = τ1).
         { generalize typeeq as x. induction x. apply idpath. }
         exact (tyeq @ helper).
Defined.

Definition termhasdeceq (σ : type) : isdeceq (term σ).
Proof.
  intros s t.
  exact (termhasdeceq_transportb s σ (idpath σ) t).
Defined.