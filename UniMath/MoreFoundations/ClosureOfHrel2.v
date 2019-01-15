Require Import UniMath.Foundations.All.

(*Delimit Scope refltransclos with refltransclos.
Local Open Scope refltransclos.*)

Section FixARelation.
  Context {X : UU}.
  Context (R : hrel X).

Definition refl_trans_clos_univprop (R' : X -> X -> UU) :=
  ∏ (S : X -> X -> UU),
  (∏ (x y : X), R x y -> S x y) ->
  (∏ (x : X), S x x) ->
  (∏ (x y z : X), S x y -> S y z -> S x z) ->
  ∏ (x y : X), R' x y -> S x y.

Inductive refl_trans_clos_right : X -> X -> UU :=
  | refl_step_right  (x : X)     : refl_trans_clos_right x x
  | trans_step_right (x y z : X) : refl_trans_clos_right x y -> R y z ->
                                   refl_trans_clos_right x z.

Lemma refl_trans_clos_right_refl (x : X) : refl_trans_clos_right x x.
Proof.
  apply refl_step_right.
Qed.

Lemma refl_trans_clos_right_trans (x y z : X) : refl_trans_clos_right x y ->
                                                refl_trans_clos_right y z ->
                                                refl_trans_clos_right x z.
Proof.
  intros Rxy Ryz. induction Ryz.
  - exact Rxy.
  - eapply trans_step_right.
    + apply IHRyz.
      exact Rxy.
    + exact h.
Qed.

Lemma refl_trans_clos_right_ext (x y : X) : R x y -> refl_trans_clos_right x y.
Proof.
  intro Rxy. eapply trans_step_right.
  - apply refl_step_right.
  - exact Rxy.
Qed.

Lemma refl_trans_clos_right_univprop :
  refl_trans_clos_univprop (refl_trans_clos_right).
Proof.
  intros S extends refl trans x y hyp.
  induction hyp.
  - apply refl.
  - eapply trans.
    + exact IHhyp.
    + apply extends. exact h.
Qed.

Inductive refl_trans_clos_left : X -> X -> UU :=
  | refl_step_left  (x : X)     : refl_trans_clos_left x x
  | trans_step_left (x y z : X) : R x y -> refl_trans_clos_left y z ->
                                   refl_trans_clos_left x z.

Lemma refl_trans_clos_left_refl (x : X) : refl_trans_clos_left x x.
Proof.
  apply refl_step_left.
Qed.

Lemma refl_trans_clos_left_trans (x y z : X) : refl_trans_clos_left x y ->
                                               refl_trans_clos_left y z ->
                                               refl_trans_clos_left x z.
Proof.
  intros Rxy Ryz. induction Rxy.
  - exact Ryz.
  - eapply trans_step_left.
    + exact h.
    + apply IHRxy.
      exact Ryz.
Qed.

Lemma refl_trans_clos_left_ext (x y : X) : R x y -> refl_trans_clos_left x y.
Proof.
  intro Rxy. eapply trans_step_left.
  - exact Rxy.
  - apply refl_step_left.
Qed.

Lemma refl_trans_clos_left_univprop :
  refl_trans_clos_univprop (refl_trans_clos_left).
Proof.
  intros S extends refl trans x y hyp.
  induction hyp.
  - apply refl.
  - eapply trans.
    + apply extends. exact h.
    + exact IHhyp.
Qed.

(*******************************************************************************************)

Inductive refl_trans_clos_k_left : nat -> X -> X -> UU :=
(*  | base_step_k_left  (x y : X)              : R x y -> refl_trans_clos_k_left 0 x y*)
  | refl_step_k_left  (x : X)                : refl_trans_clos_k_left 0 x x
  | trans_step_k_left (x y z : X) (n : nat)  : R x y -> refl_trans_clos_k_left n y z ->
                                               refl_trans_clos_k_left (S n) x z.

Inductive refl_trans_clos_k_right : nat -> X -> X -> UU :=
(*  | base_step_k_right  (x y : X)              : R x y -> refl_trans_clos_k_right 0 x y*)
  | refl_step_k_right  (x : X)                : refl_trans_clos_k_right 0 x x
  | trans_step_k_right (x y z : X) (n : nat)  : refl_trans_clos_k_right n x y -> R y z ->
                                                refl_trans_clos_k_right (S n) x z.

Lemma refl_trans_clos_left_approx (x y : X) :
  refl_trans_clos_left x y <-> ∑ (k : nat), refl_trans_clos_k_left k x y.
Proof.
  split.
  - intro rel.
    induction rel.
    + exists 0.
      apply refl_step_k_left.
    + induction IHrel as [m relkyz].
      exists (S m).
      eapply trans_step_k_left.
      * exact h.
      * exact relkyz.
  - intros [k relk].
    induction relk.
    + apply refl_step_left.
    + eapply trans_step_left.
      * exact h.
      * exact IHrelk.
Qed.


Lemma refl_trans_clos_k_left_dec : isdeceq X -> isdecrel R ->
  (∏ (x y z : X), R x y -> R x z -> y = z) ->
  (∏ (x : X), decidable (∑ (y : X), R x y)) ->
  ∏ (k : nat) (x y : X) , decidable (refl_trans_clos_k_left k x y).
Proof.
  intros Xdec Rdec Rext Rsumdec.
  induction k as [| m IHm].
  - intros x y. induction (Xdec x y) as [eq | neq].
    + rewrite eq. apply inl, refl_step_k_left.
    + apply inr. intro rel.
      inversion rel.
      apply neq. rewrite H1. apply idpath.
  - intros x z. induction (Rsumdec x) as [Rx | nRx].
    + induction Rx as [y Rxy].
      induction (IHm y z) as [Ryz | nRyz].
      ++ apply inl. eapply trans_step_k_left.
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


Lemma refl_trans_clos_k_right_dec : isdeceq X -> isdecrel R ->
  (∏ (x y z : X), R x z -> R y z -> x = y) ->
  (∏ (y : X), decidable (∑ (x : X), R x y)) ->
  ∏ (k : nat) (x y : X) , decidable (refl_trans_clos_k_right k x y).
Proof.
  intros Xdec Rdec Rext Rsumdec.
  induction k as [| m IHm].
  - intros x y. induction (Xdec x y) as [eq | neq].
    + rewrite eq. apply inl, refl_step_k_right.
    + apply inr. intro rel.
      inversion rel.
      apply neq. rewrite H1. apply idpath.
  - intros x z. induction (Rsumdec z) as [Rz | nRz].
    + induction Rz as [y Ryz].
      induction (IHm x y) as [relxy | nrelxy].
      ++ apply inl. eapply trans_step_k_right.
         +++ exact relxy.
         +++ exact Ryz.
      ++ apply inr. intro Rsm.
         inversion_clear Rsm.
         set (yeq := Rext _ _ _ Ryz X1).
         rewrite <- yeq in X0.
         assert (nmeq : n = m).
         { apply invmaponpathsS. rewrite H. apply idpath. }
         rewrite nmeq in X0.
         apply nrelxy. exact X0.
    + apply inr. intro Rsm.
      inversion_clear Rsm.
      apply nRz. exists y.
      assumption.
Defined.



(***********************************************************************************)



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