Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.PartialityDominances.PartialElements.
Require Import UniMath.Algebra.DCPO.

(* The type of partial function from X to Y is the type of functions from X
   into the partial elements of Y. *)
Local Open Scope PartialElements.
Definition partialfun (X Y : UU) : UU := X -> 𝓛 Y.

Delimit Scope PartialFunctions with PartialFunctions.
Local Open Scope PartialFunctions.

(* TO DO: Check levels *)
Notation "X ⇀ Y" := (partialfun X Y) (at level 30) : PartialFunctions.

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

Notation "f #" := (Kleisli_extension f) (at level 30) : PartialFunctions.

Lemma η_extension {X : UU} : η # = idfun (𝓛 X).
Proof.
  use funextfun. intro l.
  apply information_order_antisymmetric.
  - split with pr1.
    intro d. use idpath.
  - split with (λ p : isdefined l, (p,, tt)).
    intro d. use idpath.
Qed.

Lemma fun_extension_after_η {X Y : UU} (f : X ⇀ Y) : f # ∘ η = f.
Proof.
  use funextfun.
  intro x. apply information_order_antisymmetric.
  - split with pr2.
    intro d. use idpath.
  - split with (λ d : isdefined (f x), (tt,, d)).
    intro d. use idpath.
Qed.

Lemma extension_comp {X Y Z : UU} (f : X ⇀ Y) (g : Y ⇀ Z) :
  (g # ∘ f) # = g # ∘ (f #).
Proof.
  use funextfun. intro l.
  apply information_order_antisymmetric.
  (* This is essentially just the equivalence between
     ∑(a : A), (b : Ba), C(a, b) and
     ∑((a, b) : ∑(a : A), B(a)), C(a, b). *)
  - split with (λ d : isdefined((g # ∘ f) # l), ((pr1 d,, pr12 d),, pr22 d)).
    intro d. use idpath.
  - split with (λ d : isdefined(g # ( (f #) l)), (pr11 d,, (pr21 d,, pr2 d))).
    intro d. use idpath.
Qed.

Definition Kleisli_comp {X Y Z : UU} (f : X ⇀ Y) (g : Y ⇀ Z) : X ⇀ Z := g # ∘ f.

Notation "g □ f" := (Kleisli_comp f g) (at level 30) : PartialFunctions.

Definition Kleisli_id {X : UU} : X ⇀ X := @lift_embedding X.

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

(* Equivalently, 𝓛(f) = (f ∘ η)# *)
Definition liftfunctor {X Y : UU} (f : X -> Y) : 𝓛 X -> 𝓛 Y := (η ∘ f) #.

Definition liftfunctor' {X Y : UU} (f : X -> Y) : 𝓛 X -> 𝓛 Y.
Proof.
  intros [P r]. induction r as [i φ].
  exact (P,,i,,f ∘ φ).
Defined.

Definition liftfunctor_eq {X Y : UU} : ∏ (f : X -> Y), liftfunctor f = liftfunctor' f.
Proof.
  intro f . use funextfun. intro l.
  induction l as [P r]. induction r as [i φ].
  unfold liftfunctor'. unfold liftfunctor. unfold Kleisli_extension. simpl.
  use information_order_antisymmetric.
  - split with (λ x : (∑ _ : P, unit), pr1 x).
    intro d. use idpath.
  - split with (λ p : P, (p,,tt)).
    intro d. use idpath.
Defined.

Local Open Scope DCPO.

Definition Kleisli_extension_isdefinedmap {X Y : hSet} (f : X -> liftdcpo Y)
           (u v : liftdcpo X) (t : isdefined u -> isdefined v)
           (g : ∏ (d : isdefined u), value u d = value v (t d)) :
  isdefined (f # u) -> isdefined (f # v).
Proof.
  unfold Kleisli_extension; simpl.
  intros [p d]. split with (t p).
  set (eq := !(g p)).
  set (eq' := maponpaths f eq).
  set (eq'' := maponpaths isdefined eq').
  apply (invmap (eqweqmap eq'')).
  exact d.
Defined.

Definition Kleisli_extension_dcpo {X Y : hSet} (f : X -> liftdcpo Y) : liftdcpo X --> liftdcpo Y.
Proof.
  use dcpomorphismpair.
  - exact (Kleisli_extension f).
  - intros I u isdirec v islubv.
    induction islubv as [isuppv isleastv].
    split.
    + intro i. simpl.
      unfold funcomp; simpl.
      induction (isuppv i) as [isdefmap valuesmap].
      set (isdefmap' := Kleisli_extension_isdefinedmap f (u i) v
                                                       isdefmap
                                                       valuesmap).
      split with isdefmap'.
      intro d. induction d as [pi di].
      unfold value; simpl.
      unfold isdefmap'. unfold Kleisli_extension_isdefinedmap.
      set (eq := valuesmap pi).
      set (eq' := maponpaths f eq).
      set (eq'' := maponpaths isdefined eq').
      assert (lem : ∏ (l m : liftdcpo Y), ∏ (p : l = m),
                    transportf (λ d : isdefined l, Y) (maponpaths isdefined p) (value l) = value m).
      {
      unfold value; simpl.
      set (eq''' := maponpaths value eq'').
      * apply eq'.
      set (eq'' := maponpaths value eq').