Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

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

(* Next, we wish to prove that η is an embedding. We first need a series of lemmas. *)

(* The first lemma shows that unit = unit is proofirrelevant.
   We need propositional univalence + funext (or equivalently, funext + propext). *)
Lemma unit_eq_unit_isproofirr : isProofIrrelevant (unit = unit).
Proof.
  assert (equiv' : (unit ≃ unit) ≃ unit).
  {
    use weq_iso.
    - exact (λ _, tt).
    - exact (λ _, idweq unit).
    - intro f. simpl. use subtypeEquality.
      + exact (isapropisweq).
      + simpl. use funextfun. intro x. use (proofirrelevance unit isapropunit).
    - intro u. simpl. induction u. use idpath.
  }
  assert (equiv : (unit = unit) ≃ unit).
  {
    eapply weqcomp.
    - use (univalence unit unit).
    - exact equiv'.
  }
   (* Not strictly needed, but we are using univalence anyway and it allows for a shorter proof. *)
  assert (eq : (unit = unit) = unit).
  {
    exact (invmap (univalence (unit = unit) unit) equiv).
  }
  rewrite eq.
  exact (proofirrelevance unit (isapropunit)).
Qed.

(* We describe the action on paths of η.
   A path e : x = y gets mapped to (idpath unit,, idpath isapropunit,, ap₁ e),
   where 1 is the obvious map X -> (unit -> X). *)
Lemma maponpaths_η_eq {X : UU} {x y : X} (e : x = y) :
  maponpaths η e = @total2_paths_f _ _
                    (unit,, isapropunit,, termfun x)
                    (unit,, isapropunit,, termfun y)
                    (idpath unit)
                    (@dirprod_paths _ _
                     (isapropunit,, termfun x)
                     (isapropunit,, termfun y)
                     (idpath isapropunit)
                     (maponpaths termfun e)).
  (*  let m := maponpaths η e in
  let m1 := base_paths _ _ m in
  let m2 := fiber_paths m in
  m1,,m2 = idpath unit,, (@dirprod_paths _ _ (isapropunit,, termfun x) (isapropunit,, termfun y)
                  (idpath isapropunit) (maponpaths termfun e)).
(* (idpath isapropunit,, (maponpaths termfun e)). *)
  (*
  maponpaths η e = invmap (total2_paths_equiv (λ P : UU, isaprop P × (P -> X)) (unit,, isapropunit,, termfun x) (unit,, isapropunit,, termfun y))
                                               (idpath unit,, @dirprod_paths _ _
                                                 (isapropunit,, termfun x)
                                                 (isapropunit,, termfun y)
                                                 (idpath isapropunit)
                                                 (maponpaths termfun e)). *)*)
Proof.
  induction e. use idpath.
Qed.

(* Moreover, we can show that we may assume that the first component
   of a path between η-values is trivial. *)
Lemma η_values_eq {X : UU} {x y : X} (q : η x = η y) :
  let q1 := base_paths _ _ q in
  let q2 := fiber_paths q in
  let q1eq := unit_eq_unit_isproofirr q1 (idpath unit) in
  let transp_fun' := (λ P : UU, isaprop P × (P -> X)) in
  let transp_fun := (λ v : unit = unit, transportf transp_fun' v
                    (isapropunit,, termfun x) = (isapropunit,, termfun y)) in
  q1,, q2 = (idpath unit,, (transportf transp_fun q1eq q2)).
Proof.
  use transportf_eq.
Qed.

Definition maponpaths_η_section {X : UU} {x y : X} : η x = η y -> x = y.
Proof.
  intro q.
  (* We take q apart, as in the above lemma. *)
  set (q1 := base_paths _ _ q).
  set (q2 := fiber_paths q).
  set (q1eq := unit_eq_unit_isproofirr q1 (idpath unit)).
  set (transp_fun' := (λ P : UU, isaprop P × (P -> X))).
  set (transp_fun := (λ v : unit = unit, transportf transp_fun' v
                    (isapropunit,, termfun x) = (isapropunit,, termfun y))).
  set (t := transportf transp_fun q1eq q2).
  set (t':= maponpaths dirprod_pr2 t). simpl in t'.
  (* t' is now a proof of termfun x = termfun y, so x = y. *)
  exact (maponpaths (λ f : unit -> X, f tt) t').
Defined.

Lemma maponpaths_η_is_retraction {X : UU} {x y : X} :
  maponpaths η ∘ @maponpaths_η_section X x y ~ idfun _.
Proof.
  intro q. unfold funcomp, idfun. simpl.
  set (to_pair := total2_paths_equiv (λ P : UU, isaprop P × (P -> X)) (unit,, isapropunit,, termfun x) (unit,, isapropunit,, termfun y)).
  set (from_pair := invmap to_pair).
