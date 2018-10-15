Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Search unit.

Definition selects_propositions (D : UU -> UU) : UU := ∏ X, D X -> isaprop X.
Definition sigma_closure (D : UU -> UU) : UU := ∏ (P : UU), ∏ (Q : P -> UU), D P -> (∏ (p : P), D (Q p)) -> D(∑ (p : P), Q p).
Definition structural_dominance : UU := ∑ (D : UU -> UU), selects_propositions D × D unit × sigma_closure D.

Definition structural_dominance_underlying_function (D : structural_dominance) : UU -> UU := pr1 D.
Definition structural_dominance_selection (D : structural_dominance) :
  ∏ X, structural_dominance_underlying_function D X -> isaprop X := pr1 (pr2 D).

(* Definition function_on_universe_from_structural_dominance (D : structural_dominance) :
     UU -> UU := pr1 D.
Coercion function_on_universe_from_structural_dominance :
  structural_dominance >-> Funclass. *)

Definition lift (Y : UU) := ∑ (P : UU), isaprop P × (P -> Y).
Definition D_lift (D : UU -> UU) (Y : UU) := ∑ (P : UU), D P × (P -> Y).

Definition canonical_embedding (D : UU -> UU) (sel : selects_propositions D) {Y : UU} : D_lift D Y -> lift Y.
Proof.
  intro h. induction h as [P pair]. induction pair as [d g].
  split with P. split.
  - use sel. exact d.
  - exact g.
Defined.

Definition tame (D : UU -> UU) (sel : selects_propositions D) {X Y : UU} : (X -> D_lift D Y) -> (X -> lift Y).
Proof.
  intros f x.
  use canonical_embedding.
  - exact D.
  - exact sel.
  - exact (f x).
Defined.

Definition isDis_D (D : UU -> UU) (sel : selects_propositions D) {X Y : UU} (f : X -> lift Y) : UU :=
  ∃ (f' : X -> D_lift D Y), tame D sel f' = f.

Definition Dis_D (D : UU -> UU) (sel : selects_propositions D) (X Y : UU) : UU :=
  ∑ f : X -> lift Y, isDis_D D sel f.

Definition D_pas (D : structural_dominance) : UU :=
  ∑ (A : UU), nonempty A ×
    Dis_D (structural_dominance_underlying_function D) (structural_dominance_selection D) A A.

Definition D_pas_carrier (D : structural_dominance) (A : D_pas D) : UU := pr1 A.

(* Terms over a pas *)

Inductive terms_over_pas (D : structural_dominance) (A : D_pas D) : UU :=
  | var : nat -> terms_over_pas D A
  | con : D_pas_carrier D A -> terms_over_pas D A
  | app : terms_over_pas D A -> terms_over_pas D A -> terms_over_pas D A.