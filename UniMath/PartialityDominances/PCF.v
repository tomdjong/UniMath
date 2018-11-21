Require Import UniMath.Foundations.All.

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

Inductive smallstep : ∏ (σ : type), term σ -> term σ -> UU :=
  | predzerostep : smallstep ι (pred ` zero) zero
  | predsuccstep : ∏ (n : nat), smallstep ι (pred ` (numeral (S n))) (numeral n)
  | succstep : ∏ (n : nat), smallstep ι (succ ` (numeral n)) (numeral (S n))
  | ifzzerostep : ∏ (s t : term ι), smallstep ι ((ifz ` zero) ` s ` t) s
  | ifzsuccstep : ∏ (n : nat), ∏ (s t : term ι),
                  smallstep ι (ifz ` (numeral (S n)) ` s ` t) t
  | fixpstep : ∏ (σ : type), ∏ (t : term (σ ⇨ σ)),
               smallstep σ (fixp ` t) (t ` (fixp ` t))
  | 𝓀step : ∏ (σ τ : type), ∏ (s : term σ), ∏ (t : term τ),
            smallstep σ (𝓀 ` s ` t) s
  | 𝓈step : ∏ (σ τ ρ : type), ∏ (s : term (σ ⇨ τ ⇨ ρ)),
            ∏ (t : term (σ ⇨ τ)), ∏ (r : term σ),
            smallstep ρ (𝓈 ` s ` t ` r) (s ` r ` (t ` r)).

Notation "s ▹ t" := (smallstep s t) (at level 40) : PCF.
