Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Inductive type : UU :=
  | base       : type
  | functional : type -> type -> type.

Delimit Scope PCF with PCF.
Local Open Scope PCF.

Notation "'ι'" := base : PCF.
(* Check level? *)
Notation "σ ⇨ τ" := (functional σ τ) (at level 60, right associativity) : PCF.

(* *** Combinatory PCF ***
Inductive term : type -> UU :=
  | zero                : term ι
  | succ                : term (ι ⇨ ι)
  | pred                : term (ι ⇨ ι)
  | ifz                 : term (ι ⇨ ι ⇨ ι ⇨ ι)
  | fixp {σ : type}     : term ((σ ⇨ σ) ⇨ σ)
  | k    {σ τ : type}   : term (σ ⇨ τ ⇨ σ)
  | s    {σ τ ρ : type} : term ((σ ⇨ τ ⇨ ρ) ⇨ (σ ⇨ τ) ⇨ σ ⇨ ρ)
  | app  {σ τ : type}   : term (σ ⇨ τ) -> term σ -> term τ.
*)

Inductive preterm : type -> UU :=
  | zero : preterm ι
  | succ : preterm ι -> preterm ι.

Fixpoint numeral (n : nat) : preterm ι :=
  match n with
  | O   => zero
  | S k => succ (numeral k)
  end.

Inductive bigstep : ∏ (σ : type), preterm σ -> preterm σ -> UU :=
  | zerobigstep : bigstep ι zero zero.
  (*| succbigstep {M : preterm ι} {n : nat} : bigstep ι M (numeral n) ->
                                            bigstep ι (succ M) (numeral (S n)).*)

Lemma bigstep_base_isaprop (M N : preterm ι) : isaprop (bigstep ι M N).
Proof.
  use invproofirrelevance.
  intros p. induction p.
  intro y.
  einduction y.