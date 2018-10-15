Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Definition selects_propositions (D : UU -> UU) : UU := ∏ X, D X -> isaprop X.
Definition sigma_closure (D : UU -> UU) : UU := ∏ (P : UU), ∏ (Q : P -> UU), D P -> (∏ (p : P), D (Q p)) -> D(∑ (p : P), Q p).
Definition structural_dominance : UU := ∑ (D : UU -> UU), selects_propositions D × D unit × sigma_closure D.

Definition structural_dominance_carrier (D : structural_dominance) : UU -> UU := pr1 D.
Definition structural_dominance_selection (D : structural_dominance) :
  ∏ X, structural_dominance_carrier D X -> isaprop X := pr1 (pr2 D).

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

Definition Dis_D_carrier {D : UU -> UU} {sel : selects_propositions D} {X Y : UU} (m : Dis_D D sel X Y) : X -> lift Y :=
  pr1 m.

Definition defined  {Y : UU} : lift Y -> hProp.
Proof.
  intro u. induction u as [P pair]. induction pair as [d f].
  unfold hProp. split with P. exact d.
Defined.

Definition value {Y : UU} : ∏ (u : lift Y), (defined u) -> Y.
Proof.
  intro u. induction u as [P pair]. induction pair as [d f].
  simpl. exact f.
Defined.

Definition D_pas (D : structural_dominance) : UU :=
  ∑ (A : UU), nonempty A ×
    Dis_D (structural_dominance_carrier D) (structural_dominance_selection D) (A × A) A.

Definition D_pas_carrier {D : structural_dominance} (A : D_pas D) : UU := pr1 A.

Definition D_pas_app {D : structural_dominance} (A : D_pas D) : Dis_D (structural_dominance_carrier D) (structural_dominance_selection D) (D_pas_carrier A × D_pas_carrier A) (D_pas_carrier A) :=
  pr2 (pr2 A).

(* Terms over a pas *)

Inductive terms_over_pas {D : structural_dominance} (A : D_pas D) : UU :=
  | var : nat -> terms_over_pas A
  | con : D_pas_carrier A -> terms_over_pas A
  | app : terms_over_pas A -> terms_over_pas A -> terms_over_pas A.

Inductive term_denotes_element {D : structural_dominance} {A : D_pas D} : terms_over_pas A -> D_pas_carrier A -> UU :=
  | con_denotes : ∏ (a : D_pas_carrier A), term_denotes_element (con A a) a
  | app_denotes : ∏ (s t : terms_over_pas A), ∏ (a b : D_pas_carrier A),
                  ∏ (u : Dis_D_carrier (D_pas_app A) (a ,, b)),
                  ∏ (p : defined u),
      term_denotes_element s a -> term_denotes_element t b -> term_denotes_element (app s t) (value u p).