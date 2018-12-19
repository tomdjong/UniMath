Require Import UniMath.Foundations.All.

Section reflexive_closure_hrel.
  Context {X : UU}.

Inductive refl_clos (R : hrel X) : X -> X -> UU :=
  | base_step' (x y : X) : R x y -> refl_clos R x y
  | refl_step' (x : X) : refl_clos R x x.

Delimit Scope reflclos with reflclos.
Local Open Scope reflclos.

Context (R : hrel X).
Notation "'R''" := (refl_clos R) : reflclos.

Lemma refl_clos_extends : ∏ (x y : X), R x y -> R' x y.
Proof.
  use base_step'.
Qed.

Lemma refl_clos_refl : ∏ (x : X), R' x x.
Proof.
  use refl_step'.
Qed.

Lemma refl_clos_univprop : ∏ (S : X -> X -> UU),
                           (∏ (x y : X), R x y -> S x y) ->
                           (∏ (x : X), S x x) ->
                           ∏ (x y : X), R' x y -> S x y.
Proof.
  intros S extends refl x y. intro hyp.
  induction hyp.
  - use extends. exact h.
  - use refl.
Qed.

Definition refl_clos_hrel (x y : X) := ∥ R' x y ∥.

Notation "'R*'" := (refl_clos_hrel) : reflclos.

Lemma refl_clos_hrel_ishrel : ∏ (x y : X), isaprop (R* x y).
Proof.
  intros x y. use isapropishinh.
Qed.

Lemma refl_clos_hrel_extends : ∏ (x y : X), R x y -> R* x y.
Proof.
  intros x y R1. use hinhpr. use refl_clos_extends. exact R1.
Qed.

Lemma refl_clos_hrel_isrefl : isrefl R*.
Proof.
  intro x. use hinhpr. use refl_clos_refl.
Qed.

Lemma refl_clos_hrel_univprop : ∏ (S : hrel X),
                                      (∏ (x y : X), R x y -> S x y) ->
                                      (∏ (x : X), S x x) ->
                                      ∏ (x y : X), R* x y -> S x y.
Proof.
  intros S extends refl x y. intro hyp.
  use factor_through_squash.
  - exact (R' x y).
  - use (pr2 (S x y)).
  - use (refl_clos_univprop (λ x y : X, (pr1 (S x y)))).
    + use extends.
    + use refl.
  - exact hyp.
Qed.

End reflexive_closure_hrel.

Section reflexive_transitive_closure_hrel.
  Context {X : UU}.

Inductive refl_trans_clos (R : hrel X) : X -> X -> UU :=
  | base_step (x y : X) : R x y -> refl_trans_clos R x y
  | refl_step (x : X) : refl_trans_clos R x x
  | trans_step (x y z : X) : refl_trans_clos R x y ->
                             refl_trans_clos R y z -> refl_trans_clos R x z.

Delimit Scope refltransclos with refltransclos.
Local Open Scope refltransclos.

Context (R : hrel X).
Notation "'R''" := (refl_trans_clos R) : refltransclos.

Lemma refl_trans_clos_extends : ∏ (x y : X), R x y -> R' x y.
Proof.
  use base_step.
Qed.

Lemma refl_trans_clos_refl : ∏ (x : X), R' x x.
Proof.
  use refl_step.
Qed.

Lemma refl_trans_clos_trans : ∏ (x y z : X), R' x y -> R' y z -> R' x z.
Proof.
  use trans_step.
Qed.

Lemma refl_trans_clos_univprop : ∏ (S : X -> X -> UU),
                           (∏ (x y : X), R x y -> S x y) ->
                           (∏ (x : X), S x x) ->
                           (∏ (x y z : X), S x y -> S y z -> S x z) ->
                           ∏ (x y : X), R' x y -> S x y.
Proof.
  intros S extends refl trans x y. intro hyp.
  induction hyp.
  - use extends. exact h.
  - use refl.
  - use trans.
    + exact y.
    + use IHhyp1.
    + use IHhyp2.
Qed.

Definition refl_trans_clos_hrel (x y : X) := ∥ R' x y ∥.

Notation "'R*'" := (refl_trans_clos_hrel) : refltransclos.

Lemma refl_trans_clos_hrel_ishrel : ∏ (x y : X), isaprop (R* x y).
Proof.
  intros x y. use isapropishinh.
Qed.

Lemma refl_trans_clos_hrel_extends : ∏ (x y : X), R x y -> R* x y.
Proof.
  intros x y R1. use hinhpr. use refl_trans_clos_extends. exact R1.
Qed.

Lemma refl_trans_clos_hrel_isrefl : isrefl R*.
Proof.
  intro x. use hinhpr. use refl_trans_clos_refl.
Qed.

Lemma refl_trans_clos_hrel_istrans : istrans R*.
Proof.
  intros x y z R1 R2. use factor_through_squash.
  - exact (R' x y × R' y z).
  - use refl_trans_clos_hrel_ishrel.
  - intros [R1' R2']. use hinhpr.
    use (refl_trans_clos_trans _ _ _ R1' R2').
  - set (f := idfun (R' x y × R' y z)).
    set (g := λ r : (R' x y), λ s : (R' y z), f (r,,s)).
    set (h := λ r : (R' x y), hinhfun (g r)).
    assert (h' : R* x y -> R* y z -> ∥ R' x y × R' y z ∥).
    { use factor_through_squash.
      - use impred; intro r. use isapropishinh.
      - exact h. }
    exact (h' R1 R2).
Qed.

Lemma refl_trans_clos_hrel_univprop : ∏ (S : hrel X),
                                      (∏ (x y : X), R x y -> S x y) ->
                                      (∏ (x : X), S x x) ->
                                      (∏ (x y z : X), S x y -> S y z -> S x z) ->
                                      ∏ (x y : X), R* x y -> S x y.
Proof.
  intros S extends refl trans x y. intro hyp.
  use factor_through_squash.
  - exact (R' x y).
  - use (pr2 (S x y)).
  - use (refl_trans_clos_univprop (λ x y : X, (pr1 (S x y)))).
    + use extends.
    + use refl.
    + use trans.
  - exact hyp.
Qed.


End reflexive_transitive_closure_hrel.