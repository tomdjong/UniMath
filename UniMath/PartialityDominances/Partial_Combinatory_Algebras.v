Require Import UniMath.PartialityDominances.Partiality_and_Dominances.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Lists.

(* Since we only want one partial map, the application map, we are not really
interested in composition, so we might not need a structural dominance. A type
transformer D that selects propositions might be enough, at least to define everything. *)

Section fix_a_D_and_selection.
Context (D : UU -> UU).
Context (sel : selects_propositions D).

Definition pas : UU :=
  ∑ (A : UU), nonempty A × disciplined D sel (A × A) A.

Section fix_a_pas.

Context (A : pas).

Definition pas_carrier : UU := pr1 A.

Definition pas_disciplined_map :
  disciplined D sel (pas_carrier × pas_carrier) (pas_carrier) := pr2 (pr2 A).

Definition pas_app : pas_carrier × pas_carrier -> lift(pas_carrier) :=
  pr1 pas_disciplined_map.

(* Terms over a pas *)

Section fix_a_var_type.

Context (X : Type).

Inductive terms_over_pas : UU :=
  | var : X -> terms_over_pas
  | con : pas_carrier -> terms_over_pas
  | app : terms_over_pas -> terms_over_pas -> terms_over_pas.

(* We only have this for *closed terms* *)
(*
Inductive term_denotes_element : terms_over_pas -> pas_carrier -> UU :=
| con_denotes : ∏ (a : pas_carrier), term_denotes_element (con a) a
| app_denotes : ∏ (s t : terms_over_pas), ∏ (a b : pas_carrier),
                let u := pas_app (a ,, b) in
                ∏ (p : defined(u)),
                term_denotes_element s a -> term_denotes_element t b ->
                defined u ->
                term_denotes_element (app s t) (value u p).

Definition term_denotes (t : terms_over_pas) : UU
  := ∑ (a : pas_carrier), term_denotes_element t a.

Delimit Scope pca with pca.
Local Open Scope pca.

(* TO DO: check level *)
Notation "t ↓ a" := (term_denotes_element t a) (at level 50) : pca.
Notation "t ↓" := (term_denotes t) (at level 50) : pca.

Example constants_denote : ∏ (a : pas_carrier), con a ↓ a.
Proof.
  intro a.
  exact (con_denotes a).
Defined.

End fix_a_var_type.

Fixpoint substitution {X Y : Type} (t : terms_over_pas X) (sub : X -> terms_over_pas Y)
  : terms_over_pas Y :=
  match t with
  | var _ x => sub x
  | con _ a => con _ a
  | app _ t1 t2 => app _ (substitution t1 sub) (substitution t2 sub)
  end. *)

(* We will also need an embedding into the D_lift, so fix an inhabitant of D unit. *)
Context (Dunit : D unit).

Definition rep_app (n : nat) :
  pas_carrier -> disciplined D sel (iterprod n pas_carrier) pas_carrier.
Proof.
  induction n as [ | m].
  - intro a. unfold disciplined. simpl.
    split with (λ _, lift_embedding a).
    unfold is_disciplined.
    use wittohexists.
    + exact (λ _, D_lift_embedding D Dunit a).
    + use funextfun. intro u.
      unfold tame. unfold canonical_embedding. simpl.
      unfold lift_embedding.
      use subtypeEquality'.
      * simpl. use idpath.
      * simpl. use isapropdirprod.
        ** admit.
        ** unfold isaprop. unfold isofhlevel. intros f f'.
           unfold iscontr.
    use subtypeEquality.
    + unfold isPredicate. intro Y.
    + simpl. use idpath.
  -
Definition term_to_partial_function : (∑ (n : nat), terms_over_pas (stn n)) ->
  ∑ (m : nat), disciplined D sel (iterprod m pas_carrier) pas_carrier.
Proof.
  intro hyp. induction hyp as [n t].
  split with n.
