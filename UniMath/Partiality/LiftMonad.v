(**

Tom de Jong

Created: November 2018

Refactored: January 2019

*******************************************************************************)

(** * Lift Monad *)
(** ** Contents
- Monad structure of the lift, i.e. Kleisli extension and Kleisli laws
  ([liftmonad])
- The Kleisli extension as a dcpo morphism ([liftmonaddcpo])
*)


Require Import UniMath.Foundations.All.
Require Import UniMath.Partiality.PartialElements.
Require Import UniMath.Algebra.DCPO.

(** * The monad structure of the lift *)
Delimit Scope LiftMonad with LiftMonad.
Local Open Scope LiftMonad.

Section liftmonad.
Local Open Scope PartialElements.

Definition Kleisli_extension {X Y : UU} : (X -> 𝓛 Y) -> (𝓛 X -> 𝓛 Y).
Proof.
  intros f [P pair].
  induction pair as [i φ].
  set (Q := ∑ (p : P), isdefined (f (φ p))).
  exists Q. split.
  - apply isofhleveltotal2.
    + exact i.
    + intro p'. apply isaprop_isdefined.
  - intro q. induction q as [p d].
    exact (value (f (φ p)) d).
Defined.

Notation "f #" := (Kleisli_extension f) (at level 30) : LiftMonad.

Definition η_extension {X : UU} : η # ~ idfun (𝓛 X).
Proof.
  intro l.
  apply lifteq_suff.
  exists (tpair _ pr1 (λ d, (d,,tt))).
  intro d. cbn. apply idpath.
Defined.

(** We avoid expressing this using ∘, because that does not work well
    with the rewrite tactic. *)
Definition fun_extension_after_η {X Y : UU} (f : X -> 𝓛 Y) :
  ∏ (x : X), f # (η x) = f x.
Proof.
  intro x. apply lifteq_suff.
  exists (tpair _ pr2 (λ d, (tt,,d))).
  intro d. cbn. apply idpath.
Defined.

(** This is essentially just the equivalence between
    ∑(a : A), (b : Ba), C(a, b) and
    ∑((a, b) : ∑(a : A), B(a)), C(a, b). *)
Definition extension_comp {X Y Z : UU} (f : X -> 𝓛 Y) (g : Y -> 𝓛 Z) :
  ∏ (l : 𝓛 X), (g # ∘ f) # l = g # (f # l).
Proof.
  intro l.
  apply lifteq_suff.
  exists (weq_to_iff (weqtotal2asstol _ _)).
  intro d. cbn. apply idpath.
Defined.

Definition liftfunctor {X Y : UU} (f : X -> Y) : 𝓛 X -> 𝓛 Y.
Proof.
  intros [P r]. induction r as [i φ].
  exact (P,,i,,f ∘ φ).
Defined.

Definition liftfunctor' {X Y : UU} (f : X -> Y) : 𝓛 X -> 𝓛 Y := (η ∘ f) #.

Definition liftfunctor_eq {X Y : UU} : ∏ (f : X -> Y), liftfunctor f ~ liftfunctor' f.
Proof.
  intros f l.
  apply lifteq_suff.
  exists (tpair _ (λ d, (d,,tt)) pr1).
  intro d; cbn. apply idpath.
Defined.

End liftmonad.

Notation "f #" := (Kleisli_extension f) (at level 30) : LiftMonad.

Delimit Scope LiftMonadDcpo with LiftMonadDcpo.
Local Open Scope LiftMonadDcpo.

(** * Kleisli extension as a dcpo morphism *)
Section liftmonaddcpo.
Local Open Scope DCPO.
Local Open Scope LiftDcpo.

Lemma Kleisli_extension_preservesorder {X Y : hSet} (f : X -> 𝓛 Y)
           (u v : liftdcpo X) : u ⊑ v -> (f # u) ⊑ (f # v).
Proof.
  intro inequv.
  intros [d1 d2].
  apply maponpaths.
  exact (inequv d1).
Qed.

Definition Kleisli_extension_dcpo {X Y : hSet} (f : X -> 𝓛 Y) :
  𝓛 X --> 𝓛 Y.
Proof.
  use mkdcpomorphism.
  - exact (Kleisli_extension f).
  - intros I u isdirec v islubv.
    split.
    + intro i; cbn.
      unfold funcomp; cbn.
      apply Kleisli_extension_preservesorder.
      apply (islub_isupperbound _ islubv).
    + intros l ineqs; cbn.
      intro q.
      apply (isdefinedlub_toprop isdirec islubv).
      * intros [i di].
        set (eq := liftlub_isdefined isdirec islubv i di).
        rewrite <- eq.
        use (ineqs i).
        unfold funcomp.
        rewrite eq.
        exact q.
      * apply (liftofhset_isaset).
      * exact (pr1 q).
Defined.

Definition liftfunctor_dcpo {X Y : hSet} (f : X -> Y) : 𝓛 X --> 𝓛 Y.
Proof.
  use mkdcpomorphism.
  - exact (liftfunctor f).
  - set (liftfunc' := Kleisli_extension_dcpo (η ∘ f)).
    assert (eq : ∏ (l : 𝓛 X), liftfunctor f l = pr1 liftfunc' l).
    { use liftfunctor_eq. }
    rewrite (funextfun _ _ eq).
    exact (pr2 (pr2 liftfunc')).
Defined.

Close Scope LiftMonad.
End liftmonaddcpo.

Notation "f #" := (Kleisli_extension_dcpo f) : LiftMonadDcpo.
