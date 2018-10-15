Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Section fix_a_D_and_prop_selection.

Context (D : UU -> UU).

Definition selects_propositions : UU := ∏ X, D X -> isaprop X.

Context (sel : selects_propositions).

Definition lift (Y : UU) := ∑ (P : UU), isaprop P × (P -> Y).
Definition D_lift (Y : UU) := ∑ (P : UU), D P × (P -> Y).

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

Definition canonical_embedding {Y : UU} : D_lift Y -> lift Y.
Proof.
  intro h. induction h as [P pair]. induction pair as [d g].
  split with P. split.
  - use sel. exact d.
  - exact g.
Defined.

Definition tame {X Y : UU} : (X -> D_lift Y) -> (X -> lift Y).
Proof.
  intros f x.
  use canonical_embedding.
  exact (f x).
Defined.

Definition isDis_D {X Y : UU} (f : X -> lift Y) : UU :=
  ∃ (f' : X -> D_lift Y), tame f' = f.

Definition Dis_D (X Y : UU) : UU :=
  ∑ f : X -> lift Y, isDis_D f.

Definition Dis_D_carrier {X Y : UU} (m : Dis_D X Y) : X -> lift Y :=
  pr1 m.

End fix_a_D_and_prop_selection.

(* Structural dominances *)

Definition sigma_closure (D : UU -> UU) : UU :=
  ∏ (P : UU), ∏ (Q : P -> UU),
  D P -> (∏ (p : P), D (Q p)) ->
  D(∑ (p : P), Q p).

Definition structural_dominance : UU :=
  ∑ (D : UU -> UU), selects_propositions D × D unit × sigma_closure D.

Definition structural_dominance_carrier (struc_dom : structural_dominance) :
  UU -> UU := pr1 struc_dom.
Definition structural_dominance_selection (struc_dom : structural_dominance) :
  selects_propositions (structural_dominance_carrier struc_dom) :=
  pr1 (pr2 struc_dom).

Section fix_a_structural_dominance.

Context (struc_dom : structural_dominance).

Definition pas : UU :=
  ∑ (A : UU), nonempty A ×
  Dis_D (structural_dominance_carrier struc_dom)
        (structural_dominance_selection struc_dom)
        (A × A) A.

Section fix_a_pas.

Context (A : pas).

Definition pas_carrier : UU := pr1 A.

Definition pas_disciplined_map :
  Dis_D (structural_dominance_carrier struc_dom)
        (structural_dominance_selection struc_dom)
        (pas_carrier × pas_carrier) (pas_carrier)
  := pr2 (pr2 A).

Definition pas_app : pas_carrier × pas_carrier -> lift(pas_carrier) := pr1 pas_disciplined_map.

(* Terms over a pas *)

Section fix_a_var_type.

Context (X : Type).

Inductive terms_over_pas : UU :=
  | var : X -> terms_over_pas
  | con : pas_carrier -> terms_over_pas
  | app : terms_over_pas -> terms_over_pas -> terms_over_pas.

Inductive term_denotes_element : terms_over_pas -> pas_carrier -> UU :=
| con_denotes : ∏ (a : pas_carrier), term_denotes_element (con a) a
| app_denotes : ∏ (s t : terms_over_pas), ∏ (a b : pas_carrier),
                let u := pas_app (a ,, b) in
                ∏ (p : defined(u)),
                term_denotes_element s a -> term_denotes_element t b ->
                defined u ->
                term_denotes_element (app s t) (value u p).