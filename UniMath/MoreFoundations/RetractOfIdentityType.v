Require Import UniMath.Foundations.All.

(* An endofunction f is idempotent if it f ∘ f is pointwise equal to f. *)
Definition funisidempotent {X : UU} (f : X -> X) := f ∘ f ~ f.

Lemma funfamilyonpaths {X : UU} (f : ∏ (x y : X), x = y -> x = y) (x y : X) (p : x = y) :
  f x y p = f x x (idpath x) @ p.
Proof.
  induction p. rewrite pathscomp0rid. use idpath.
Qed.

Lemma idempotentfunfamonpaths_homotopictoid {X : UU} (f : ∏ (x y : X), x = y -> x = y) :
  (∏ (x y : X), funisidempotent (f x y)) -> ∏ (x y : X), idfun (x = y) ~ f x y.
Proof.
  intros idemp x y p. unfold idfun. induction p.
  apply (pathscomp_cancel_left (f x x (idpath x)) _ _).
  etrans.
  - use pathscomp0rid.
  - etrans.
    + exact (!(idemp x x (idpath x))).
    + exact (funfamilyonpaths f x x (f x x (idpath x))).
Qed.

Theorem retraction_of_pathspace_is_section {X : UU} {R : X -> X -> UU}
  {r : ∏ (x y : X), x = y -> R x y} {s : ∏ (x y : X), R x y -> x = y} :
  (∏ (x y : X), (r x y) ∘ (s x y) ~ idfun _) ->
  ∏ (x y : X), (s x y) ∘ (r x y) ~ idfun _.
Proof.
  intro retraction. intros x y.
  (* Since r has a section s, the function s ∘ r is idempotent. *)
  assert (idemp : ∏ (x' y' : X), funisidempotent (s x' y' ∘ r x' y')).
  {
    intros x' y' p. rewrite funcomp_assoc.
    unfold funcomp. unfold funcomp in retraction. rewrite (retraction x' y').
    unfold idfun. use idpath.
  }
  use invhomot.
  set (f := λ (x y : X), (s x y) ∘ r x y).
  apply (idempotentfunfamonpaths_homotopictoid f).
  exact idemp.
Qed.

Corollary isInjective' {X Y : UU} {f : X -> Y} :
  (∑ (s : ∏ (x y : X), f x = f y -> x = y),
  (∏ (x y : X), (@maponpaths _ _ f x y) ∘ (s x y) ~ idfun _)) ->
  isInjective f.
Proof.
  intro has_section. unfold isInjective. intros x y.
  set (s := pr1 has_section).
  set (s_proof := pr2 has_section).
  use isweq_iso.
  - exact (s x y).
  - intro p. apply retraction_of_pathspace_is_section.
    exact (s_proof).
  - exact (s_proof x y).
Qed.
