Require Import UniMath.Foundations.All.

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

Context {X : UU}.
Inductive refltransclos_left (R : hrel X) : X -> X -> UU :=
  | reflstep' : ∏ (x : X), refltransclos_left R x x
  | leftstep  : ∏ (x y z : X), R x y -> refltransclos_left R y z ->
                               refltransclos_left R x z.

Definition refltransclos_left_trans (R : hrel X) (x y z : X) :
  refltransclos_left R x y -> refltransclos_left R y z -> refltransclos_left R x z.
Proof.
  intros rel1 rel2.
  induction rel1.
  - exact rel2.
  - eapply leftstep.
    + exact h.
    + apply IHrel1.
      exact rel2.
Defined.

Definition left_regular_equiv (R : hrel X) (x y : X) :
  refltransclos_left R x y <-> refl_trans_clos R x y.
Proof.
  split.
  - intro rel.
    induction rel.
    + apply refl_step.
    + eapply trans_step.
      * apply base_step.
        exact h.
      * exact IHrel.
  - intro rel.
    induction rel.
    + eapply leftstep.
      * exact h.
      * apply reflstep'.
    + apply reflstep'.
    + eapply refltransclos_left_trans.
      * exact IHrel1.
      * exact IHrel2.
Defined.

Definition refltransclos_step (R : hrel X) : nat -> X -> X -> UU.
Proof.
  intro n. induction n as [| m IH].
  - intros x y. exact (x=y).
  - intros x z. exact (∑ (y : X), R x y × IH y z).
Defined.

Definition lefttostep (R : hrel X) (x y : X) :
  refltransclos_left R x y -> ∑ (k : nat), refltransclos_step R k x y.
Proof.
  intro rel.
  induction rel.
  - exists 0. cbn. apply idpath.
  - induction IHrel as [m IH].
    exists (S m).
    simpl.
    exists y.
    exact (h,,IH).
Defined.

Definition steptoleft (R : hrel X) (k : nat) :
  ∏ (x y : X), refltransclos_step R k x y -> refltransclos_left R x y.
Proof.
  induction k as [| m IH].
  - intros x y rel. cbn in rel.
    rewrite rel.
    apply reflstep'.
  - intros x z. simpl.
    intros [y rels].
    eapply leftstep.
    + exact (pr1 rels).
    + apply IH.
      exact (pr2 rels).
Defined.

Definition stepleftequiv (R : hrel X) (x y : X) :
  refltransclos_left R x y <-> ∑ (k : nat), refltransclos_step R k x y.
Proof.
  split.
  - apply lefttostep.
  - intros [k rel].
    eapply steptoleft.
    exact rel.
Defined.

Definition refltransclos_step_hrel (R : hrel X) : nat -> X -> X -> UU :=
  λ (k : nat) (x y : X), ∥ refltransclos_step R k x y ∥.

Definition refltransclos_left_hrel (R : hrel X) : X -> X -> UU :=
  λ (x y : X), ∥ refltransclos_left R x y ∥.

Definition lefttostep_hrel (R : hrel X) (x y : X) :
  refltransclos_left_hrel R x y -> ∥ ∑ (k : nat), refltransclos_step_hrel R k x y ∥.
Proof.
  apply hinhfun.
  intro rel.
  set (helper := lefttostep R x y rel).
  induction helper as [m rel'].
  exists m.
  apply hinhpr.
  exact rel'.
Defined.

Definition steptoleft_hrel_helper (R : hrel X) (k : nat) :
  ∏ (x y : X), refltransclos_step_hrel R k x y -> refltransclos_left_hrel R x y.
Proof.
  intros x y.
  apply hinhfun.
  apply steptoleft.
Defined.

Definition steptoleft_hrel_helper' (R : hrel X) (x y : X) :
  (∑ (k : nat), refltransclos_step_hrel R k x y) -> refltransclos_left_hrel R x y.
Proof.
  intros [k rel].
  eapply steptoleft_hrel_helper.
  exact rel.
Defined.

Definition steptoleft_hrel (R : hrel X) (x y : X) :
  ∥ ∑ (k : nat), refltransclos_step_hrel R k x y ∥ -> refltransclos_left_hrel R x y.
Proof.
  eapply factor_through_squash.
  - apply isapropishinh.
  - apply steptoleft_hrel_helper'.
Defined.

Definition stepleftequiv_hrel (R : hrel X) (x y : X) :
  refltransclos_left_hrel R x y <-> ∥ ∑ (k : nat), refltransclos_step_hrel R k x y ∥.
Proof.
  split.
  - apply lefttostep_hrel.
  - apply steptoleft_hrel.
Defined.
