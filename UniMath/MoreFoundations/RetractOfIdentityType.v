Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(* An endofunction f is idempotent if it f ∘ f is pointwise equal to f. *)
Definition funisidempotent {X : UU} (f : X -> X) := f ∘ f ~ f.

Lemma funfamilyonpaths {X : UU} (f : ∏ (x y : X), x = y -> x = y) (x y : X) (p : x = y) :
  f x y p = f x x (idpath x) @ p.
Proof.
  induction p. rewrite pathscomp0rid. use idpath.
Qed.

Theorem idempotentfunfamonpaths_homotopictoid {X : UU} (f : ∏ (x y : X), x = y -> x = y) :
  (∏ (x y : X), funisidempotent (f x y)) -> ∏ (x y : X), f x y ~ idfun _.
Proof.
  intros idem x y p. unfold idfun. induction p.
  unfold funisidempotent in idem.
  assert (eq : f x x (idpath x) = f x x (idpath x) @ (f x x (idpath x))).
  { etrans.
    - use (!(idem x x (idpath x))).
    - use (funfamilyonpaths f x x (f x x (idpath x))).
  }
  assert (eq' : f x x (idpath x) @ (idpath x) = f x x (idpath x) @ f x x (idpath x)).
  {
    etrans.
    - use pathscomp0rid.
    - exact eq.
  }
  exact (!(pathscomp_cancel_left _ _ _ eq')).
Defined.