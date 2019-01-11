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

Section reflexive_transitive_closure_step_hrel.
  Context {X : UU}.

Inductive refl_trans_clos_step (R : hrel X) : nat -> X -> X -> UU :=
  | base_step' (x y : X)              : R x y -> refl_trans_clos_step R 0 x y
  | refl_step' (x : X)                : refl_trans_clos_step R 0 x x
  | trans_step' (x y z : X) (n : nat) : R x y -> refl_trans_clos_step R n y z ->
                                        refl_trans_clos_step R (S n) x z.
(*  | monotone_step' (x y : X) (n : nat) : refl_trans_clos_step R n x y ->
                                         refl_trans_clos_step R (S n) x y.*)

Inductive refl_trans_clos' (R : hrel X) : X -> X -> UU :=
  | refl_step'' (x : X) : refl_trans_clos' R x x
  | trans_step'' (x y z : X) : refl_trans_clos' R x y -> R y z ->
                               refl_trans_clos' R x z.

Delimit Scope refltransclos' with refltransclos'.
Local Open Scope refltransclos'.

Context (R : hrel X).
Notation "'R''" := (refl_trans_clos' R) : refltransclos'.

Lemma refl_trans_clos'_extends : ∏ (x y : X), R x y -> R' x y.
Proof.
  intros x y. apply trans_step''.
  use refl_step''.
Qed.

Lemma refl_trans_clos'_refl : ∏ (x : X), R' x x.
Proof.
  use refl_step''.
Qed.

Lemma refl_trans_clos'_trans : ∏ (x y z : X), R' x y -> R' y z -> R' x z.
Proof.
  intros x y z R1 R2.
  induction R2.
  - exact R1.
  - eapply trans_step''.
    + apply IHR2.
      exact R1.
    + exact h.
Qed.

End reflexive_transitive_closure_step_hrel.

Definition refl_trans_clos_equiv {X : UU} (R : hrel X) (x y : X) :
  refl_trans_clos R x y <-> refl_trans_clos' R x y.
Proof.
  split.
  - use refl_trans_clos_univprop.
    + use refl_trans_clos'_extends.
    + use refl_trans_clos'_refl.
    + use refl_trans_clos'_trans.
  - intro left. induction left.
    + use refl_step.
    + eapply trans_step.
      ++ exact IHleft.
      ++ apply base_step.
         exact h.
Defined.

(*Definition refl_trans_clos'_approx {X : UU} (R : hrel X) (x y : X) :
  refl_trans_clos' R x y <-> ∑ (k : nat), refl_trans_clos_step R k x y.
Proof.
  split.
  - intro left.
    induction left.
    + split with 0. use refl_step'.
    + induction IHleft as [m rel].
      split with (S m).
      eapply trans_step'.
      ++ exact rel.
      ++ exact h.
  - intros [k left].
    induction left.
    + use refl_trans_clos'_extends.
      exact h.
    + use refl_trans_clos'_refl.
    + eapply trans_step''.
      ++ exact IHleft.
      ++ exact h.
(*    + exact IHleft.      *)
Defined.*)

Definition refl_trans_clos_step_dec {X : UU} (R : hrel X) :
  (∏ (x y z : X), R x y -> R x z -> y = z) ->
  isdecrel R -> (∏ (x : X), decidable (∑ (y : X), R x y)) ->
  isdeceq X -> ∏ (k : nat) (x y : X) , decidable (refl_trans_clos_step R k x y).
Proof.
  intros Rext Rdec Rsumdec Xdec.
  induction k as [| m IHm].
  - intros x y. induction (Rdec x y) as [r | nr].
    + apply inl, base_step'. exact r.
    + induction (Xdec x y) as [eq | neq].
      ++ apply inl. rewrite eq. apply refl_step'.
      ++ apply inr. intro Rstep. inversion Rstep.
         +++ apply nr. assumption.
         +++ apply neq. rewrite H1. apply idpath.
  - intros x z. induction (Rsumdec x) as [Rx | nRx].
    + induction Rx as [y Rxy].
      induction (IHm y z) as [Ryz | nRyz].
      ++ apply inl. eapply trans_step'.
         +++ exact Rxy.
         +++ exact Ryz.
      ++ apply inr. intro Rsm.
         inversion_clear Rsm.
         set (yeq := Rext x y y0 Rxy X0).
         rewrite <- yeq in X1.
         assert (nmeq : n = m).
         { apply invmaponpathsS. rewrite H. apply idpath. }
         rewrite nmeq in X1.
         apply nRyz. exact X1.
    + apply inr. intro Rsm.
      inversion_clear Rsm.
      apply nRx. exists y.
      assumption.
Defined.

Definition refl_trans_clos_step_hrel {X : UU} (R : hrel X) (k : nat) (x y : X) :=
  ∥ refl_trans_clos_step R k x y ∥.

Definition refl_trans_clos_step_hrel_dec {X : UU} (R : hrel X) :
  (∏ (x y z : X), R x y -> R x z -> y = z) ->
  isdecrel R -> (∏ (x : X), decidable (∑ (y : X), R x y)) ->
  isdeceq X -> ∏ (k : nat) (x y : X) , decidable (refl_trans_clos_step_hrel R k x y).
Proof.
  intros Rext Rdec Rsumdec Xdec k x y. apply decidable_ishinh.
  exact (refl_trans_clos_step_dec R Rext Rdec Rsumdec Xdec k x y).
Defined.