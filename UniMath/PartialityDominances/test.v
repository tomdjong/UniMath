Require Import UniMath.Foundations.All.

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

Inductive term : type -> UU :=
  | zero                : term ι
  | succ                : term (ι ⇨ ι)
  | app  {σ τ : type}   : term (σ ⇨ τ) -> term σ -> term τ.

Notation "s ` t" := (app s t) (at level 50, left associativity) : PCF.

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
             exact (transportb (λ x, term (x ⇨ τ2)) eq1 t1). (* Are s1 and t1 'equal'? *)
         +++ apply IHs2.
             exact (transportb term eq1 t2). (* Are s2 and t2 'equal'? *)
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

Definition termhasdeceq (σ τ : type) : ∏ (s : term σ), ∏ (typeeq : σ = τ), ∏ (t : term τ),
  decidable (s = transportb term typeeq t).
Proof.
  induction s as [| | σ1 σ2 s1 IHs1 s2 IHs2].
  - intro typeeq. induction t.
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
  - intro typeeq. induction t.
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
  - intro typeeq. induction t as [| | τ1 τ2 t1 _ t2 _ ].
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
      ++ (* Wrong IH *)
      ++ apply fromempty.
         apply neq2. exact typeeq.
      ++ apply inr. intro eq.
         use term_encode.
         apply neq1.




Defined.