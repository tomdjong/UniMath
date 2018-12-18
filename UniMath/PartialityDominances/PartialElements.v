Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.DCPO.

(* The type of partial elements of a type X is denoted by 𝓛 X, for "lift of X". *)
Definition lift (X : UU) := ∑ (P : UU), isaprop P × (P -> X).

Delimit Scope PartialElements with PartialElements.
Local Open Scope PartialElements.
Notation "'𝓛'" := lift : PartialElements.

(* We can map X into its lift. *)
Definition lift_embedding {X : UU} (x : X) : 𝓛 X := (unit,, isapropunit,, termfun x).
Notation "'η'" := lift_embedding : PartialElements.

(* We define meaningful projections. *)
Definition isdefined {X : UU} (l : 𝓛 X) : UU := pr1 l.

Definition value {X : UU} (l : 𝓛 X) : isdefined l -> X.
Proof.
  induction l as [P pair]. induction pair as [i f].
  intro p. exact (f p).
Defined.

Definition value_weaklyconstant {X : UU} (l : 𝓛 X) : weaklyconstant (value l).
Proof.
  intros p q.
  use maponpaths.
  use proofirrelevance.
  use (pr1 (pr2 l)).
Defined.

Lemma isdefined_isaprop {X : UU} (l : 𝓛 X) : isaprop(isdefined l).
Proof.
  induction l as [P pair]. induction pair as [i f]. exact i.
Qed.

(* Lemma on equality of partial elements *)
Definition isdefined_value_eq {X : UU} {l m : 𝓛 X} (e : isdefined l = isdefined m) :
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

Definition eq_value_eq {X : UU} {l m : 𝓛 X} :
  l = m -> ∏ (d : isdefined l), ∏ (d' : isdefined m), value l d = value m d'.
Proof.
  intro eq. induction eq. intros d d'. use value_weaklyconstant.
Defined.

(*** Martin's proof ***)
Definition iscontr_lift (X : UU) : UU := ∑ (P : UU), iscontr P × (P -> X).

Delimit Scope LiftEmbeddingProof with LiftEmbeddingProof.
Local Open Scope LiftEmbeddingProof.
Notation "'𝓜'" := iscontr_lift : LiftEmbeddingProof.

Definition iscontr_lift_embedding {X : UU} (x : X) : 𝓜 X := (unit,, iscontrunit,, termfun x).
Notation "'μ'" := iscontr_lift_embedding : LiftEmbeddingProof.

Lemma iscontr_lift_embedding_isweq {X : UU} : isweq (@iscontr_lift_embedding X).
Proof.
  use isweq_iso.
  - intro m; induction m as [P pair]; induction pair as [i f].
    exact (f (pr1 i)).
  - simpl. intro x. use idpath.
  - simpl. intro m.
    induction m as [P pair]; induction pair as [i f].
    apply total2_paths_equiv. assert (e : unit = P).
    { use propext.
      + exact isapropunit.
      + use isapropifcontr. exact i.
      + split.
        * exact (λ _ : unit, (pr1 i)).
        * exact (λ _ : P, tt). }
    split with e.
    use dirprod_paths.
    + simpl. use proofirrelevance. use isapropiscontr.
    + simpl.
      assert (transpeq : pr2 (transportf (λ x : UU, iscontr x × (x -> X)) e
                              (iscontrunit,, termfun (f (pr1 i)))) =
                              termfun (f (pr1 i)) ∘ (pr1weq (eqweqmap (!e)))).
      { generalize e as e'. induction e'. use idpath. }
      rewrite transpeq.
      use funextfun. intro p. unfold funcomp, termfun.
      use maponpaths. exact (!(pr2 i p)).
Qed.

Definition 𝓜_to_𝓛 {X : UU} : 𝓜 X -> 𝓛 X.
Proof.
  use sumfun. intro P; simpl.
  use dirprodfun.
  - exact isapropifcontr.
  - exact (idfun _).
Defined.

(* Every map between hprops is an embedding. *)
Definition maponprops_isincl {P Q : UU} (f : P -> Q) :
  isaprop P -> isaprop Q -> isincl f.
Proof.
  intros i j. unfold isincl, isofhlevelf.
  intro q. use invproofirrelevance.
  intros fib fib'; induction fib as [p s]; induction fib' as [p' t].
  induction s. assert (eq : p = p').
  { use proofirrelevance. exact i. }
  apply total2_paths_equiv; split with eq; simpl.
  use proofirrelevance. use isasetaprop. exact j.
Defined.

(* Finally, we can prove that the map from 𝓜 to 𝓛 is an embedding. *)
Lemma 𝓜_to_𝓛_isincl {X : UU} : isincl (@𝓜_to_𝓛 X).
Proof.
  use sumfun_preserves_incl. intro P.
  use dirprodfun_preserves_incl.
  - use maponprops_isincl.
    + exact (isapropiscontr P).
    + exact (isapropisaprop P).
  - use isinclweq. exact (idisweq _).
Qed.
(* Now we show that η is an embedding by proving that it is pointwise equal
   to the composition of the two embeddings X -> 𝓜 X -> 𝓛 X. *)
Theorem lift_embedding_isincl {X : UU} : isincl (@lift_embedding X).
Proof.
  set (comp := (@𝓜_to_𝓛 X) ∘ (@iscontr_lift_embedding X)).
  apply (isinclhomot comp η).
  - intro x. unfold comp, funcomp.
    unfold iscontr_lift_embedding; unfold 𝓜_to_𝓛; unfold sumfun.
    unfold dirprodfun. simpl. unfold idfun.
    apply total2_paths_equiv.
    split with (idpath unit).
    simpl. apply dirprod_paths.
    + simpl. use proofirrelevance. exact (isapropisaprop unit).
    + simpl. use idpath.
  - set (incl1 := weqtoincl (weqpair (@iscontr_lift_embedding X)
                                         (@iscontr_lift_embedding_isweq X))).
    set (incl2 := inclpair (@𝓜_to_𝓛 X) (@𝓜_to_𝓛_isincl X)).
    apply (isinclcomp incl1 incl2).
Qed.
Close Scope LiftEmbeddingProof.
(*** End of Martin's Proof ***)

(*** Next, we wish to show that the fiber of η is equivalent to isdefined. ***)
Definition fiber_to_isdefined {X : UU} {l : 𝓛 X} : hfiber η l -> isdefined l.
Proof.
  intro fib. induction fib as [x p].
  (* l ≡ (P,...) = (unit,...); so we transfer the inhabitant tt of unit *)
  exact (transportf (λ Q : UU, Q) (maponpaths pr1 p) tt).
Defined.

(* It is useful to derive equality of partial elements by using the "order".
   It only is a proper order if the underlying type is a set. *)
Definition information_order {X : UU} (l m : 𝓛 X) : UU :=
  ∑ (t : isdefined l -> isdefined m), ∏ (d : isdefined l), value l d = value m (t d).

(* TO DO: Check level *)
Notation "l ⊑ m" := (information_order l m) (at level 30) : PartialElements.

Definition information_order_antisymmetric {X : UU} :
  ∏ (l m : 𝓛 X), l ⊑ m -> m ⊑ l -> l = m.
Proof.
  intros l m [t t'] [s s'].
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
    rewrite seq. exact (!(s' d)).
Defined.

Definition information_order_reflexive {X : UU} : ∏ (l : 𝓛 X), l ⊑ l.
Proof.
  intro l. split with (idfun _).
  intro d. use idpath.
Defined.

Definition information_order_transitive {X : UU} :
  ∏ (l m n : 𝓛 X), l ⊑ m -> m ⊑ n -> l ⊑ n.
Proof.
  intros l m n [t p] [s q].
  split with (s ∘ t). intro d.
  etrans.
  - exact (p d).
  - exact (q (t d)).
Defined.

Definition information_order_eq_ifisdefined {X : UU} (l m : 𝓛 X) :
  l ⊑ m <-> (isdefined l -> l = m).
Proof.
  split.
  - intros ineq dl.
    use information_order_antisymmetric.
    + exact ineq.
    + split with (λ _, dl).
      intro dm.
      induction ineq as [t g].
      etrans.
      ++ eapply value_weaklyconstant.
      ++ exact (!(g dl)).
  - intro ineq'.
    assert (s : isdefined l -> isdefined m).
    { intro dl. set (eq := ineq' dl).
      exact (transportf isdefined eq dl). }
    split with s.
    intro dl.
    use eq_value_eq. exact (ineq' dl).
Defined.

Definition information_order_isdefined_hyp {X : UU} (l m : 𝓛 X) :
  (isdefined l -> l ⊑ m) -> l ⊑ m.
Proof.
  intro isdefinedhyp.
  split with (λ d : isdefined l, (pr1 (isdefinedhyp d) d)).
  intro d.
  use (pr2 (isdefinedhyp d)).
Defined.

Definition information_order_least {X : UU} : 𝓛 X := (empty,, isapropempty,, fromempty).
Notation "'⊥'" := information_order_least : PartialElements.

Definition information_order_least_isleast {X : UU} : ∏ (l : 𝓛 X), ⊥ ⊑ l.
Proof.
  intro l. split with fromempty.
  intro d. apply fromempty. exact d.
Defined.

Definition isdefined_to_fiber {X : UU} {l : 𝓛 X} : isdefined l -> hfiber η l.
Proof.
  intro p. induction l as [P r]. induction r as [i f].
  split with (f p).
  set (t := (λ _, p) : unit -> P).
  set (s := (λ _, tt) : P -> unit).
  apply information_order_antisymmetric.
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
  - use lift_embedding_isincl.
Defined.

(*** If X is a set, then 𝓛 X with the information order
     is a dcpo with least element. ***)

Lemma liftofhset_isaset {X : hSet} : isaset (𝓛 X).
Proof.
  intros [P pair] [Q pair'].
  use invproofirrelevance.
  intros e e'. induction e.
  etrans.
  apply (homotinvweqweq0 (total2_paths_equiv _ _ _)).
  etrans.
  assert (eq : total2_paths_equiv _ _ _ (idpath (P,, pair)) =
                 total2_paths_equiv _ _ _ e').
  {
    simpl. apply total2_paths_equiv. unfold base_paths; simpl.
    assert (eq' : idpath P = maponpaths pr1 e').
    { use proofirrelevance. use isofhlevelpathspace.
      - exact (pr1 pair).
      - exact (pr1 pair). }
    split with eq'.
    simpl; use proofirrelevance.
    assert (helper : isaset ((isaprop P) × (P -> X))).
    { use isaset_dirprod.
      - use isasetaprop. use isapropisaprop.
      - use isaset_set_fun_space. }
    use helper.
  }
  - apply maponpaths. apply eq.
  - use homotinvweqweq.
Qed.

Lemma information_order_ispropvalued {X : hSet} : ∏ (l m : 𝓛 X), isaprop (l ⊑ m).
Proof.
  intros l m.
  unfold information_order.
  use isofhleveltotal2.
  - use isapropimpl. use isdefined_isaprop.
  - intro t. use impred. intro d. use (pr2 X).
Qed.
Close Scope PartialElements.

Definition liftofhSet (X : hSet) : hSet := hSetpair (lift X) liftofhset_isaset.
Delimit Scope LiftIsPoset with LiftIsPoset.
Local Open Scope LiftIsPoset.

Definition information_order_hrel {X : hSet} (l m : liftofhSet X) :=
  hProppair (information_order l m) (information_order_ispropvalued l m).
(* TO DO: Check level *)
Notation "l ⊑ m" := (information_order_hrel l m) (at level 30) : LiftIsPoset.

(* The partial elements with the information order are a poset. *)
Definition liftposet (X : hSet) : Poset.
Proof.
  use Posetpair.
  - exact (liftofhSet X).
  - split with information_order_hrel.
    unfold isPartialOrder. split.
    + unfold ispreorder. split.
      * use information_order_transitive.
      * use information_order_reflexive.
    + use information_order_antisymmetric.
Defined.

Notation "'𝓛'" := liftposet : LiftIsPoset.

(* The following map will be used to define the value of the lub of a
   (directed) family. *)
Definition lubvaluemap {X : hSet} {I : UU} (u : I -> 𝓛 X) :
                       (∑ (i : I), isdefined (u i)) -> X.
Proof.
  intro hyp. induction hyp as [i d].
  exact (value (u i) d).
Defined.

(* The map is weakly constant if the family is directed. *)
Definition lubvaluemap_weaklyconstant {X : hSet} {I : UU} (u : I -> 𝓛 X) :
  isdirected u -> weaklyconstant (lubvaluemap u).
Proof.
  intros isdirec [i d] [i' d'].
  (* Since ϕ (i, d) = ϕ(i', d') is a prop (as X is a set), we can use
     untruncated isdirected, and then factor through squash. *)
  assert (tofactor : (∑ (k : I), (u i) ⊑ (u k) × (u i') ⊑ (u k)) ->
                     lubvaluemap u (i,, d) = lubvaluemap u (i',, d')).
  {
    intro direc. induction direc as [k pair].
    induction pair as [ineqi ineqi'].
    induction ineqi as [t f]. induction ineqi' as [s g].
    etrans.
    - apply (f d).
    - etrans.
      + apply (value_weaklyconstant (u k) (t d) (s d')).
      + apply (!(g d')).
   }
   use (@factor_through_squash (∑ (k : I), (u i) ⊑ (u k) × (u i') ⊑ (u k))
                               (lubvaluemap u (i,, d) = lubvaluemap u (i',, d'))).
   - use (pr2 X).
   - exact tofactor.
   - use (pr2 isdirec i i').
Defined.

(* The construction of the lub; a proof that this element is actually
   the lub follows later. *)
Definition mkdirectedlubinlift {X : hSet} {I : UU}
           (u : I -> 𝓛 X) : isdirected u -> 𝓛 X.
Proof.
  intro isdirec. split with (∥∑ (i : I), isdefined (u i)∥).
  split.
  - use isapropishinh.
  - use weaklyconstanttoaset_factorsthroughsquash.
    use lubvaluemap.
    + exact (pr2 X).
    + use lubvaluemap_weaklyconstant.
      exact isdirec.
Defined.

Definition mkisdefinedlubmap {X : hSet} {I : UU} (u : I -> 𝓛 X)
           (isdirec : isdirected u) :
           ∏ (i : I), isdefined (u i) -> isdefined (mkdirectedlubinlift u isdirec).
Proof.
  intros i d. unfold mkdirectedlubinlift; simpl.
  use hinhpr. exact (i,,d).
Defined.

Lemma isdefinedlub_toprop {X : hSet} {I Q : UU} (u : I -> 𝓛 X) (isdirec : isdirected u) :
  ((∑ (i : I), isdefined (u i)) -> Q) ->
  isaprop Q ->
  isdefined (mkdirectedlubinlift u isdirec) -> Q.
Proof.
  intros f Qisaprop p.
  eapply factor_through_squash.
  - exact Qisaprop.
  - exact f.
  - exact p.
Qed.

Lemma lubvalue_eq {X : hSet} {I : UU} (u : I -> 𝓛 X) (isdirec : isdirected u) :
  ∏ (i : I), ∏ (d : isdefined (u i)),
  let v := mkdirectedlubinlift u isdirec in
  ∏ (p : isdefined v),
  value (u i) d = value v p.
Proof.
  intros i d v p. change (value (u i) d) with (lubvaluemap u (i,,d)).
  unfold mkdirectedlubinlift, value; simpl.
  assert (pinsquash : p = hinhpr (i,,d)).
  { use proofirrelevance. use isapropishinh. }
  rewrite pinsquash.
  use weaklyconstanttoaset_factorsthroughsquash_eq.
  - use (pr2 X).
  - use value_weaklyconstant.
Qed.

Lemma mkdirectedlubinlift_islub {X : hSet} {I : UU} (u : I -> 𝓛 X)
      (isdirec : isdirected u) : islub u (mkdirectedlubinlift u isdirec).
Proof.
  split.
  - intro i.
    split with (mkisdefinedlubmap u isdirec i). intro d.
    use lubvalue_eq.
  - intros v upperbound.
    assert (t : isdefined (mkdirectedlubinlift u isdirec) -> isdefined v).
    { use factor_through_squash.
      + exact (pr1 (pr2 v)).
      + intros  [i d].
        induction (upperbound i) as [s g].
        exact (s d). }
    split with t.
    intro d.
    use factor_through_squash.
    + exact (∑ (i : I), isdefined (u i)).
    + use (pr2 X).
    + intros [i p]. unfold mkdirectedlubinlift, value; simpl.
      unfold mkdirectedlubinlift in d; simpl in d.
      assert (dinsquash : d = hinhpr (i,,p)).
      { use proofirrelevance. use isapropishinh. }
      rewrite dinsquash. etrans.
      * use weaklyconstanttoaset_factorsthroughsquash_eq.
        ** exact (pr2 X).
        ** intros q q'. use value_weaklyconstant.
      * simpl. induction (upperbound i) as [s g].
        etrans.
        ** apply (g p).
        ** use value_weaklyconstant.
    + exact d.
Qed.

Theorem lift_isdirectedcomplete (X : hSet) :
  isdirectedcomplete (𝓛 X).
Proof.
  unfold isdirectedcomplete. intros I u isdirec.
  split with (mkdirectedlubinlift u isdirec).
  use mkdirectedlubinlift_islub.
Qed.
Close Scope LiftIsPoset.

Definition liftdcpo (X : hSet) : dcpo.
Proof.
  use dcpopair.
  - exact (liftposet X).
  - use lift_isdirectedcomplete.
Defined.

Definition liftdcpowithleast (X : hSet) : dcpowithleast.
Proof.
  split with (liftdcpo X).
  split with (empty,, isapropempty,, fromempty).
  intro l.
  split with (fromempty).
  intro d.
  destruct d.
Defined.

(* Delimit Scope LiftIsDCPO with LiftIsDCPO.
Local Open Scope LiftIsDCPO.

Notation "'𝓛'" := liftdcpowithleast : LiftIsDCPO.

Close Scope LiftIsDCPO. *)