Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.PartialityDominances.PartialElements.

(* The type of partial function from X to Y is the type of functions from X
   into the partial elements of Y. *)
Definition partialfun (X Y : UU) : UU := X -> 𝓛 Y.

Delimit Scope PartialFunctions with PartialFunctions.
Local Open Scope PartialFunctions.

Notation "X ⇀ Y" := (partialfun X Y) (at level 50) : PartialFunctions.

(* We can lift partial functions to total ones. *)
Definition Kleisli_extension {X Y : UU} : (X ⇀ Y) -> (𝓛 X -> 𝓛 Y).
Proof.
  intro f. intro l. induction l as [P r]. induction r as [i φ].
  set (Q := ∑ (p : P), isdefined (f (φ p))).
  split with Q. split.
  - use isofhleveltotal2.
    + exact i.
    + intro p'. use isdefined_isaprop.
  - intro q. induction q as [p e].
    exact (value (f (φ p)) e).
Defined.
(* Note that isdefined (f # (P, i, φ)) ≡ ∑ (p : P), isdefined (f (φ p)) and
   value (f # (P, i, φ)) ≡ value (f (φ p)). *)

Notation "f #" := (Kleisli_extension f) (at level 50) : PartialFunctions.

Lemma η_extension {X : UU} : η # = idfun (𝓛 X).
Proof.
  use funextfun. intro l.
  apply information_order_is_antisymmetric.
  - split with pr1.
    intro d. use idpath.
  - split with (λ p : isdefined l, (p,, tt)).
    intro d. use idpath.
Qed.

Lemma fun_extension_after_η {X Y : UU} (f : X ⇀ Y) : f # ∘ η = f.
Proof.
  use funextfun.
  intro x. apply information_order_is_antisymmetric.
  - split with pr2.
    intro d. use idpath.
  - split with (λ d : isdefined (f x), (tt,, d)).
    intro d. use idpath.
Qed.

Lemma extension_comp {X Y Z : UU} (f : X ⇀ Y) (g : Y ⇀ Z) :
  (g # ∘ f) # = g # ∘ (f #).
Proof.
  use funextfun. intro l.
  apply information_order_is_antisymmetric.
  (* This is essentially just the equivalence between
     ∑(a : A), (b : Ba), C(a, b) and
     ∑((a, b) : ∑(a : A), B(a)), C(a, b). *)
  - split with (λ d : isdefined((g # ∘ f) # l), ((pr1 d,, pr12 d),, pr22 d)).
    intro d. use idpath.
  - split with (λ d : isdefined(g # ( (f #) l)), (pr11 d,, (pr21 d,, pr2 d))).
    intro d. use idpath.
Qed.

Definition Kleisli_comp {X Y Z : UU} (f : X ⇀ Y) (g : Y ⇀ Z) : X ⇀ Z := g # ∘ f.

Notation "g □ f" := (Kleisli_comp f g) (at level 50) : PartialFunctions.

Definition Kleisli_id {X : UU} : X ⇀ X := @η X.

(* The three lemmas above now say that we have associative composition and identities. *)
Lemma Kleisli_comp_id_right {X Y : UU} (f : X ⇀ Y) : f □ Kleisli_id = f.
Proof.
  unfold Kleisli_id, Kleisli_comp. exact (fun_extension_after_η f).
Qed.

Lemma Kleisli_comp_id_left {X Y : UU} (f : X ⇀ Y) : Kleisli_id □ f = f.
Proof.
  unfold Kleisli_id, Kleisli_comp. rewrite η_extension. use idpath.
Qed.

Lemma Kleisli_comp_assoc {X Y W Z : UU} (f : X ⇀ Y) (g : Y ⇀ W) (h : W ⇀ Z) :
  h □ (g □ f) = (h □ g) □ f.
Proof.
  unfold Kleisli_comp.
  rewrite funcomp_assoc.
  now rewrite extension_comp.
Qed.