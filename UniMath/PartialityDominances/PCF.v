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
  | predsuccstep : ∏ (t : term ι), smallstep' ι (pred ` (succ ` t)) t
  | ifzzerostep : ∏ (s t : term ι), smallstep' ι ((ifz ` zero) ` s ` t) s
  | ifzsuccstep : ∏ (r s t : term ι),
                  smallstep' ι (ifz ` (succ ` r) ` s ` t) t
  | fixpstep : ∏ (σ : type), ∏ (t : term (σ ⇨ σ)),
               smallstep' σ (fixp ` t) (t ` (fixp ` t))
  | 𝓀step : ∏ (σ τ : type), ∏ (s : term σ), ∏ (t : term τ),
            smallstep' σ (𝓀 ` s ` t) s
  | 𝓈step : ∏ (σ τ ρ : type), ∏ (s : term (σ ⇨ τ ⇨ ρ)),
            ∏ (t : term (σ ⇨ τ)), ∏ (r : term σ),
            smallstep' ρ (𝓈 ` s ` t ` r) (s ` r ` (t ` r))
(* We (probably?) need to add leftmost (inductive) steps *)
  | leftapp  : ∏ (σ τ : type), ∏ (s t : term (σ ⇨ τ)), ∏ (r : term σ),
               smallstep' (σ ⇨ τ) s t -> smallstep' τ (t ` r) (s ` r)
  | leftsucc : ∏ (s t : term ι), smallstep' ι s t -> smallstep' ι (succ ` s) (succ ` t)
  | leftpred : ∏ (s t : term ι), smallstep' ι s t -> smallstep' ι (pred ` s) (pred ` t)
  | leftifz  : ∏ (s t u v : term ι), smallstep' ι s t -> smallstep' ι (ifz ` s ` u ` v)
                                                                    (ifz ` t ` u ` v).

Definition smallstep (σ : type) : hrel (term σ) :=
  λ (s t : term σ), ∥ smallstep' σ s t ∥.

Notation "s ▹ t" := (smallstep s t) (at level 40) : PCF.

Definition bigstep (σ : type) : hrel (term σ) := refl_trans_clos_hrel (smallstep σ).

Notation "s ⇓ t" := (bigstep s t) (at level 40) : PCF.

(* On to denotational semantics *)
Local Open Scope DCPO.

Fixpoint denotational_semantics_type (σ : type) : dcpo :=
  match σ with
  | ι => liftdcpo natset
  | τ ⇨ ρ => denotational_semantics_type τ --> denotational_semantics_type ρ
  end.

Notation "⟦ σ ⟧" := (denotational_semantics_type σ) : PCF.
Notation "'𝓛ℕ'" := (liftdcpo natset) : PCF.

Definition lifted_succ : 𝓛ℕ --> 𝓛ℕ.
Proof.
  use dcpomorphismpair.
  - exact (liftfunctor S).
  - intros I u isdirec d islubd.
    split.
    + intro i.
      unfold funcomp, liftfunctor; simpl.
      induction (pr1 islubd i) as [t g].
      split with t.
      intro p. unfold value.
      unfold value in g. unfold funcomp.
      use maponpaths. exact (g p).
    + intros d' ineqs. simpl.
      unfold liftfunctor; simpl.
      unfold liftfunctor in ineqs; simpl in ineqs.


Local Open Scope PartialElements.
Local Open Scope PartialFunctions.
Fixpoint denotational_semantics_terms {σ : type} (t : term σ) : ⟦ σ ⟧ :=
  match t with
  | zero => η O
  | succ => liftfunctor S end.