Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.PropExt.
Require Import UniMath.MoreFoundations.RetractOfIdentityType.

(* The type of partial elements of a type X is denoted by 𝓛 X, for "lift of X". *)
Definition 𝓛 (X : UU) := ∑ (P : UU), isaprop P × (P -> X).

(* We can map X into its lift. *)
Definition η {X : UU} (x : X) : 𝓛 X := (unit,, isapropunit,, termfun x).

(* We define meaningful projections. *)
Definition isdefined {X : UU} (l : 𝓛 X) : UU := pr1 l.

Definition value {X : UU} (l : 𝓛 X) : isdefined l -> X.
Proof.
  induction l as [P pair]. induction pair as [i f].
  intro p. exact (f p).
Defined.

Lemma isdefined_isaprop {X : UU} (l : 𝓛 X) : isaprop(isdefined l).
Proof.
  induction l as [P pair]. induction pair as [i f]. exact i.
Qed.

(* Lemma on equality of partial elements *)
Lemma isdefined_value_eq {X : UU} {l m : 𝓛 X} (e : isdefined l = isdefined m) :
  transportf (λ Q : UU, Q -> X) e (value l) = value m -> l = m.
Proof.
  intro transp.
  induction l as [P r]. induction r as [i f].
  induction m as [P' r']. induction r' as [i' f'].
  apply total2_paths_equiv.
  unfold isdefined in e. simpl in e.
  split with e. simpl.
  use dirprod_paths.
  - use proofirrelevance. use isapropisaprop.
  - simpl. unfold value in transp. unfold isdefined in transp. simpl in transp.
    change (λ p : P, f p) with f in transp. change (λ p : P', f' p) with f' in transp.
    etrans.
    + assert (eq : pr2 (transportf (λ x : UU, isaprop x × (x -> X)) e (i,, f)) =
              transportf (λ x : UU, (x -> X)) e f).
      { generalize e as e'. intro e'. induction e'. use idpath. }
      exact eq.
    + exact transp.
Defined.

(* It is useful to derive equality of partial elements by using the "order".
   It only is a proper order if the underlying type is a set (TO DO) .*)
Definition information_order {X : UU} (l m : 𝓛 X) : UU :=
  ∑ (t : isdefined l -> isdefined m), ∏ (d : isdefined l), value l d = value m (t d).

Delimit Scope PartialElements with PartialElements.
Local Open Scope PartialElements.

(* TO DO: Check level *)
Notation "l ⊑ m" := (information_order l m) (at level 30) : PartialElements.

Lemma information_order_is_antisymmetric {X : UU} {l m : 𝓛 X} :
  l ⊑ m -> m ⊑ l -> l = m.
Proof.
  intros ineq1 ineq2.
  set (t := pr1 ineq1). set (s := pr1 ineq2).
  set (e := propext (isdefined_isaprop l) (isdefined_isaprop m) (tpair _ t s)).
  apply (isdefined_value_eq e).
  assert (eq : transportf (λ Q : UU, Q -> X) e (value l) = (value l) ∘ (pr1weq (eqweqmap (!e)))).
  { generalize e as e'. induction e'.  use idpath. }
  etrans.
  - exact eq.
  - use funextfun. intro d.
    assert (seq : pr1weq (eqweqmap (!e )) = s).
    {
      use funextfun. intro p. use proofirrelevance. use isdefined_isaprop.
    }
    rewrite seq. exact (!(pr2 ineq2) d).
Defined.

Lemma information_order_is_reflexive {X : UU} {l : 𝓛 X} : l ⊑ l.
Proof.
  split with (idfun _).
  intro d. use idpath.
Defined.

Lemma information_order_is_transitive {X : UU} {l m n : 𝓛 X} :
  l ⊑ m -> m ⊑ n -> l ⊑ n.
Proof.
  intros ineq1 ineq2.
  set (t := pr1 ineq1). set (s := pr1 ineq2).
  split with (s ∘ t). intro d.
  etrans.
  - exact ((pr2 ineq1) d).
  - exact ((pr2 ineq2) (t d)).
Defined.


(*** Martin's proof ***)
Definition 𝓜 (X : UU) : UU := ∑ (P : UU), iscontr P × (P -> X).

Definition iscontr_lift_equiv' {X : UU} : (unit -> X) ≃ 𝓜 X.
Proof.
  use weq_iso.
  - exact (λ f : (unit -> X), (unit,, iscontrunit,, f)).
  - intro l. induction l as [Q pair]. induction pair as [i g].
    set (c := pr1 i). set (h := λ _ : unit, c).
    exact (g ∘ h).
  - intro f. use funextfun. intro u. induction u. use idpath.
  - intro l. induction l as [Q pair]. induction pair as [i g].
    apply total2_paths_equiv.
    unfold PathPair. simpl.
    assert (e : unit = Q).
    { use propext.
      + exact isapropunit.
      + use isapropifcontr. exact i.
      + split.
        * exact (λ _ : unit, (pr1 i)).
        * exact (λ _ : Q, tt). }
    split with e.
    use dirprod_paths.
    + simpl. use proofirrelevance. use isapropiscontr.
    + simpl.
      assert (transpeq : pr2 (transportf (λ x : UU, iscontr x × (x -> X)) e
                              (iscontrunit,, g ∘ (λ _ : unit, pr1 i))) =
                              g ∘ (λ _ : unit, pr1 i) ∘ (pr1weq (eqweqmap (!e)))).
      { generalize e as e'. induction e'. use idpath. }
      rewrite transpeq.
      use funextfun. intro q. unfold funcomp, eqweqmap.
      use maponpaths. exact (!(pr2 i q)).
Defined.

Definition iscontr_lift_equiv {X : UU} : X ≃ 𝓜 X.
Proof.
  use weqcomp.
  apply (unit -> X).
  - exact (invweq (weqfunfromunit X)).
  - exact iscontr_lift_equiv'.
Defined.

Definition 𝓜_to_𝓛 {X : UU} : 𝓜 X -> 𝓛 X.
Proof.
  intro m. induction m as [P pair]. induction pair as [i f].
  split with P. split.
  - use isapropifcontr. exact i.
  - exact f.
Defined.

Definition dirprodfun {A B X Y : UU} (f : A -> X) (g : B -> Y) : A × B -> X × Y :=
  λ z : A × B, dirprodpair (f (dirprod_pr1 z)) (g (dirprod_pr2 z)).

Definition dirprodfun_fiber_incl {A B X Y : UU} (f : A -> X) (g : B -> Y) (z : X × Y) :
  hfiber (dirprodfun f g) z -> hfiber f (dirprod_pr1 z) × hfiber g (dirprod_pr2 z).
Proof.
  intro hfib. induction hfib as [ab p]. induction ab as [a b].
  split.
  - split with a.
    exact (maponpaths dirprod_pr1 p).
  - split with b.
    exact (maponpaths dirprod_pr2 p).
Defined.

Definition dirprodfun_fiber_retraction {A B X Y : UU} (f : A -> X) (g : B -> Y) (x : X) (y : Y) :
  hfiber f x × hfiber g y -> hfiber (dirprodfun f g) (x,,y).
Proof.
  intro fiberpair. induction fiberpair as [fibf fibg].
  induction fibf as [a p]. induction fibg as [b q].
  split with (a,,b).
  apply dirprod_paths.
  - exact p.
  - exact q.
Defined.

Definition dirprodfun_fiber_incl_isretraction {A B X Y : UU} (f : A -> X) (g : B -> Y) (z : X × Y) :
  dirprodfun_fiber_retraction f g (dirprod_pr1 z) (dirprod_pr2 z) ∘
    dirprodfun_fiber_incl f g z ~ idfun _.
Proof.
  intro fibprod. induction fibprod as [ab p].
  induction p. use idpath.
Defined.

Definition dirprodfun_preserves_embeddings {A B X Y : UU} (f : A -> X) (g : B -> Y) :
  isincl f -> isincl g -> isincl (dirprodfun f g).
Proof.
  intros fincl gincl. unfold isincl, isofhlevelf. intro z.
  induction z as [x y].
  apply (hlevelretract _ (dirprodfun_fiber_retraction f g x y)
                         (dirprodfun_fiber_incl f g (x,,y))).
  - use dirprodfun_fiber_incl_isretraction.
  - use isapropdirprod.
    + exact (fincl x).
    + exact (gincl y).
Defined.

Definition fun_on_sum {A : UU} {B C : A -> UU} :
  (∏ (a : A), B a -> C a) -> (∑ (a : A), B a) -> ∑ (a : A), C a.
Proof.
  intro f. intro x. induction x as [a b].
  exact (a,, f a b).
Defined.

(*** End of Martin's Proof ***)
(*
Theorem η_is_embedding {X : UU} : isInjective (@η X).
Proof.
  use isInjective'.
  split with (@maponpaths_η_section X).
  exact (@maponpaths_η_is_retraction X).
Qed.

(* Next, we wish to show that the fiber of η is equivalent to isdefined. *)
Definition fiber_to_isdefined {X : UU} {l : 𝓛 X} : hfiber η l -> isdefined l.
Proof.
  intro fib. induction fib as [x p].
  (* l ≡ (P,...) = (unit,...); so we transfer the inhabitant tt of unit *)
  exact (transportf (λ Q : UU, Q) (maponpaths pr1 p) tt).
Defined.

Definition isdefined_to_fiber {X : UU} {l : 𝓛 X} : isdefined l -> hfiber η l.
Proof.
  intro p. induction l as [P r]. induction r as [i f].
  split with (f p).
  set (t := (λ _, p) : unit -> P).
  set (s := (λ _, tt) : P -> unit).
  apply information_order_is_antisymmetric.
  - split with t. intro d. unfold value. simpl. unfold t. use idpath.
  - split with s. intro d. unfold value. unfold termfun. simpl.
    assert (eq : d = p). { use proofirrelevance. use isdefined_isaprop. }
    exact (maponpaths f eq).
Defined.

Theorem isdefined_equiv_fiber {X : UU} {l : 𝓛 X} : isdefined l ≃ hfiber η l.
Proof.
  use weqiff.
  - exact (tpair _ isdefined_to_fiber fiber_to_isdefined).
  - use isdefined_isaprop.
  - use isinclweqonpaths. exact η_is_embedding.
Defined. *)



(*** Domain Theory and Partial Elements ***)
(* First some preliminaries for relations into the universe (not hprop). *)
(* Definition istransitive {X : UU} (R : X -> X -> UU) {x y z : X} : UU :=
  R x y -> R y z -> R x z.
Definition issymmetric {X : UU} (R : X -> X -> UU) {x : X} : UU := R x x.
Definition isreflexive {X : UU} (R : X -> X -> UU) {x y : X} : UU := R x y -> R y x. *)

(* Definition isdirected {X I : UU} (R : X -> X -> UU) (f : I -> X) : UU :=
  ∏ (i j : I), ∑ (k : I), R (f i) (f k) × R (f j) (f k).

Definition isupperbound {X I : UU} (R : X -> X -> UU) (f : I -> X) (u : X) : UU :=
  ∏ (i : I), R (f i) u.

Definition islub {X I : UU} (R : X -> X -> UU) (f : I -> X) (u : X) : UU :=
  isupperbound R f u × ∏ (y : X), (∏ (i : I), R (f i) u) -> R u y.

Definition isdirectedcomplete {X : UU} (R : X -> X -> UU) : UU :=
  ∏ (I : UU), ∏ (f : I -> X), isdirected R f -> ∑ (u : X), islub R f u. *)

(* It seems that we need X to be an hSet for this to work. *)
(* Lemma information_order_is_directed_complete {X : UU} : @isdirectedcomplete (𝓛 X) (information_order). *)

(*** Map into lift of product ***)
Definition into_lift_product {X : UU} : 𝓛 X -> 𝓛 X -> 𝓛 (X × X).
Proof.
  intros l m.
  set (Q := isdefined l × isdefined m).
  split with Q. split.
  - use isapropdirprod.
    + use isdefined_isaprop.
    + use isdefined_isaprop.
  - intro q. exact (value l (pr1 q),, value m (pr2 q)).
Defined.