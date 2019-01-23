Require Import UniMath.PartialityDominances.PartialFunctions.
Require Import UniMath.PartialityDominances.PartialElements.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Definition pas : UU :=
  ∑ (A : UU), nonempty A × (A × A -> 𝓛 A).

Definition pas_carrier (𝓐 : pas) : UU := pr1 𝓐.

Definition pas_app (𝓐 : pas) : (pas_carrier 𝓐) × (pas_carrier 𝓐) -> 𝓛 (pas_carrier 𝓐) :=
  pr22 𝓐.

(* Terms over a pas *)

Section fix_a_pas.
Context (𝓐 : pas).
Context (A := pas_carrier 𝓐).
Context (app_𝓐 := pas_app 𝓐).

Section fix_a_var_type.
Context (X : UU).

Inductive term_over_pas : UU :=
  | var : X -> term_over_pas
  | con : A -> term_over_pas
  | app : term_over_pas -> term_over_pas -> term_over_pas.

End fix_a_var_type.

Fixpoint substitution {X Y : Type} (t : term_over_pas X) (sub : X -> term_over_pas Y)
  : term_over_pas Y :=
  match t with
  | var _ x => sub x
  | con _ a => con _ a
  | app _ t1 t2 => app _ (substitution t1 sub) (substitution t2 sub)
  end.

Local Open Scope PartialFunctions.
Definition rep_app (n : nat) : A -> iterprod n A ⇀ A.
Proof.
  intro a.
  induction n as [|m IHm].
  - intro u. exact (η a).
  - intro tuple. induction tuple as [b tuple'].
    set (app_tw := λ y x : A, app_𝓐 (x,,y)).
    exact ((app_tw b) # (IHm tuple')).
Defined.

Definition term_to_partial_function (n : nat) :
  term_over_pas (stn n) -> (iterprod n A ⇀ A).
Proof.
  intros t tuple.
  set (sub := λ m, con empty (nth' n tuple m)).
  set (s := substitution t sub).
  induction s as [var | con | s1 IHs1 s2 IHs2].
  + destruct var.
  + exact (η con).
  + exact ((app_𝓐 #) (@into_lift_product A IHs1 IHs2)).
Defined.

(* A pas is called combinatorially complete if we can represent any term in it. *)
Definition combinatoriallycomplete : UU :=
  ∏ (n : nat), ∏ (t : term_over_pas (stn n)),
  ∑ (a : A), rep_app n a = term_to_partial_function n t.

End fix_a_pas.

Definition pca : UU := ∑ (𝓐 : pas), combinatoriallycomplete 𝓐.
Definition pca_carrier (𝓐 : pca) : UU := pas_carrier (pr1 𝓐).
Definition pca_app (𝓐 : pca) : pca_carrier 𝓐 × pca_carrier 𝓐 -> 𝓛 (pca_carrier 𝓐) :=
  pas_app (pr1 𝓐).
Definition pca_complete (𝓐 : pca) : combinatoriallycomplete (pr1 𝓐) := pr2 𝓐.
Definition pca_to_pas (𝓐 : pca) : pas := pr1 𝓐.
Coercion pca_to_pas : pca >-> pas.

Section fix_a_pca.
Context (𝓐 : pca).
Context (A := pca_carrier 𝓐).
Context (app_𝓐 := pca_app 𝓐).

Definition to_iterprod_2 {X : UU} : X -> X -> iterprod 2 X.
Proof.
  intros x y.
  exact (pr2 (cons x (cons y nil))).
Defined.

(* Section fix_some_vars.
Context (x :

Lemma pca_has_k_s_combinators : ∑ (k : A), ∏ (a b : A), rep_app 𝓐 2 k (to_iterprod_2 a b) = η a.
Proof.
  set (t := var 𝓐 (stn 2) 1: term_over_pas 𝓐 (stn 2)). *)