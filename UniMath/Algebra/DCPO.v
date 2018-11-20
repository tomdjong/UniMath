Require Import UniMath.Foundations.All.

Section DirectedComplete.
Context {X : Poset}.
Context (R := posetRelation X).

Definition isleast (l : X) : UU := ∏ (x : X), R l x.
Lemma isleast_isaprop (l : X) : isaprop (isleast l).
Proof.
  use impred. intro x. use (pr2 (R l x)). (* R is prop-valued. *)
Qed.

Section FixIndexingFamily.
Context {I : UU}.
Context (f : I -> X). (* Indexing family *)

Definition isupperbound (u : X) : UU := ∏ (i : I), R (f i) u.
Lemma isupperbound_isaprop (u : X) : isaprop(isupperbound u).
Proof.
  use impred. intro i.
  use (pr2 (R (f i) u)). (* R is prop-valued. *)
Qed.

Definition islub (u : X) : UU := isupperbound u ×
                                 ∏ (y : X), (∏ (i : I), R (f i) y) -> R u y.
Lemma islub_isaprop (u : X) : isaprop(islub u).
Proof.
  use isapropdirprod.
  - exact (isupperbound_isaprop u).
  - use impred. intro x. use impred. intro hyp.
    use (pr2 (R u x)). (* R is prop-valued. *)
Qed.

Lemma lubsareunique {u v : X} : islub u -> islub v -> u = v.
Proof.
  intros islubu islubv.
  use isantisymm_posetRelation.
  - apply islubu. use (pr1 islubv).
  - apply islubv. use (pr1 islubu).
Qed.

Definition isdirected : UU := ∏ (i j : I), ∥∑ (k : I), R (f i) (f k) × R (f j) (f k)∥.
Lemma isdirected_isaprop : isaprop isdirected.
Proof.
  use impred. intro i. use impred. intro j.
  use isapropishinh.
Qed.
Definition directeduntruncated (i j : I) : UU :=
  ∑ (k : I), R (f i) (f k) × R (f j) (f k).
End FixIndexingFamily.
End DirectedComplete.

Definition isdirectedcomplete (X : Poset) : UU :=
  ∏ (I : UU), ∏ (f : I -> X), isdirected f -> ∑ (u : X), islub f u.
Lemma isdirectedcomplete_isaprop (X : Poset) : isaprop (isdirectedcomplete X).
Proof.
  use impred; intro I. use impred; intro f.
  use isapropimpl. use invproofirrelevance.
  intros [u p] [v q].
  apply total2_paths_equiv; split with (lubsareunique _ p q).
  use proofirrelevance. use islub_isaprop.
Qed.

Definition dcpo := ∑ (X : Poset), isdirectedcomplete X.
Definition dcpoposet (D : dcpo) : Poset := pr1 D.
Coercion dcpoposet : dcpo >-> Poset.
Definition dcpocarrier (D : dcpo) : hSet := carrierofposet (dcpoposet D).
Definition dcpoorder (D : dcpo) : PartialOrder (dcpocarrier D) :=
  pr2 (dcpoposet D).
Definition dcpoisdirectedcomplete (D : dcpo) : isdirectedcomplete D := pr2 D.
Definition dcpowithleast := ∑ (D : dcpo), ∑ (l : dcpocarrier D), isleast l.
Definition dcpowithleastdcpo : dcpowithleast -> dcpo := pr1.
Coercion dcpowithleastdcpo : dcpowithleast >-> dcpo.
Definition dcpowithleast_least (D : dcpowithleast) := (pr2 (pr2 D)).

Definition dcpopair (X : Poset) (i : isdirectedcomplete X) : dcpo := (X,,i).

Definition preserveslub {P Q : Poset} (f : P -> Q) {I : UU} (u : I -> P) : UU :=
  ∏ (v : P), islub u v -> islub (f ∘ u) (f v).
Lemma preserveslub_isaprop {P Q : Poset} (f : P -> Q) {I : UU} (u : I -> P) :
  isaprop (preserveslub f u).
Proof.
  use impred; intro v.
  use isapropimpl. use islub_isaprop.
Qed.

Definition isdcpomorphism {D D' : dcpo} (f : D -> D') :=
  ∏ (I : UU), ∏ (u : I -> D), isdirected u -> preserveslub f u.
Lemma isdcpomorphism_isaprop {D D' : dcpo} (f : D -> D') :
  isaprop (isdcpomorphism f).
Proof.
  use impred; intro I; use impred; intro u.
  use isapropimpl. use preserveslub_isaprop.
Qed.

Definition dcpomorphism (D D' : dcpo) := ∑ (f : D -> D'), isdcpomorphism f.
Definition dcpomorphismpair (D D': dcpo) :
  ∏ (t : D -> D'), isdcpomorphism t -> dcpomorphism D D'.
Proof.
  intros t i. exact (t,,i).
Defined.

Definition dcpomorphismcarrier {D D' : dcpo} :
  dcpomorphism D D' -> (D -> D') := pr1.
Coercion dcpomorphismcarrier : dcpomorphism >-> Funclass.

Lemma dcpomorphism_preservesorder {D D' : dcpo} (f : dcpomorphism D D') :
  isaposetmorphism f.
Proof.
  intros x y ineq. set (two := coprod unit unit).
  set (fam := (λ t : two, match t with | inl _ => x | inr _ => y end)).
  assert (isdirec : isdirected fam).
  { intros i j. use hinhpr. split with (inr tt).
    induction i, j.
    - simpl. exact (ineq,, ineq).
    - simpl. exact (ineq,, (isrefl_posetRelation (dcpoposet D) y)).
    - simpl. exact (isrefl_posetRelation (dcpoposet D) y,, ineq).
    - simpl. exact (isrefl_posetRelation (dcpoposet D) y,,
                    isrefl_posetRelation (dcpoposet D) y).
  }
  assert (lubfam : islub fam y).
  { split.
    - intro t. induction t.
      + simpl. use ineq.
      + simpl. use isrefl_posetRelation.
    - intros d hyp. exact (hyp (inr tt)). }
  assert (lubfam' : islub (f ∘ fam) (f y)).
  { use (pr2 f). exact isdirec. exact lubfam. }
  set (ineq' := pr1 lubfam'). use (ineq' (inl tt)).
Qed.

Definition pointwiseorder (D D' : dcpo) : hrel (dcpomorphism D D').
Proof.
  intros f g. use hProppair.
  - exact (∏ (d : D), (dcpoorder D') (f d) (g d)).
  - use impred; intro d. exact (pr2 (dcpoorder D' (f d) (g d))).
Defined.

Lemma pointwiseorder_ispartialorder (D D' : dcpo) :
  isPartialOrder (pointwiseorder D D').
Proof.
  split.
  - split.
    + intros f g h ineq1 ineq2 p.
      exact (istrans_posetRelation _ _ (g p) _ (ineq1 p) (ineq2 p)).
    + intros f p. use isrefl_posetRelation.
  - intros f g ineq1 ineq2. apply total2_paths_equiv.
    assert (funeq : pr1 f = pr1 g).
    { use funextfun. intro p. use isantisymm_posetRelation.
      ** use ineq1.
      ** use ineq2. }
    split with funeq.
    use proofirrelevance. use isdcpomorphism_isaprop.
Qed.

Definition posetofdcpomorphisms (D D' : dcpo) : Poset.
Proof.
  use Posetpair.
  - use hSetpair.
    + exact (dcpomorphism D D').
    + change isaset with (isofhlevel 2).
      use isofhleveltotal2.
      use impred; intro p. use (pr2 (dcpocarrier D')).
      intro f. use isasetaprop. use isdcpomorphism_isaprop.
  - use PartialOrderpair.
    + use pointwiseorder.
    + use pointwiseorder_ispartialorder.
Defined.

Lemma lubpreservesorder {X : Poset} {I : UU} (u v : I -> X) :
  (∏ (i : I), (posetRelation X) (u i) (v i)) ->
  ∏ (lu lv : X), islub u lu -> islub v lv ->
                 (posetRelation X) lu lv.
Proof.
  intros ineqs lu lv islubu islubv.
  apply (pr2 islubu).
  intro i. use istrans_posetRelation.
  - exact (v i).
  - exact (ineqs i).
  - use (pr1 islubv).
Qed.

(*** Next, we show that the dcpomorphisms form a dcpo themselves. ***)
Definition pointwisefamily {D D' : dcpo} {I : UU} (F : I -> posetofdcpomorphisms D D') :
  D -> I -> D' := λ (d : D), λ (i : I), pr1 (F i) d.

Lemma pointwisefamily_isdirected {D D' : dcpo} {I : UU} (F : I -> posetofdcpomorphisms D D') :
  isdirected F -> ∏ (d : D), isdirected (pointwisefamily F d).
Proof.
  intros isdirec d i j. use factor_through_squash.
  - exact (directeduntruncated F i j).
  - use isapropishinh.
  - intro direc. use hinhpr.
    induction direc as [k ineqs].
    split with k; simpl.
    induction ineqs as [ineq1 ineq2]. split.
    + exact (ineq1 d).
    + exact (ineq2 d).
  - exact (isdirec i j).
Qed.

(* Pointwise lub *)
Definition pointwiselub {D D' : dcpo} {I : UU} (F : I -> posetofdcpomorphisms D D') :
           isdirected F -> D -> D'.
Proof.
  intro isdirec.
  (* The lub of F will be g where g(d) = lub of (pointwisefamily F) d. *)
  intro d.
  exact (pr1 (dcpoisdirectedcomplete D' _ _
                                     (pointwisefamily_isdirected F isdirec d))).
Defined.

Lemma pointwiselub_islubpointwise {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  ∏ (d : D), islub (pointwisefamily F d) (pointwiselub F isdirec d).
Proof.
  intro d. unfold pointwiselub.
  use (pr2 (dcpoisdirectedcomplete D' _ _ _)).
Qed.

Lemma pointwiselub_preservesorder {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  isaposetmorphism (pointwiselub F isdirec).
Proof.
  intros x y ineq. use lubpreservesorder.
  - exact I.
  - exact (λ i : I, pr1 (F i) x).
  - exact (λ i : I, pr1 (F i) y).
  - intro i. simpl. use dcpomorphism_preservesorder.
    exact ineq.
  - use pointwiselub_islubpointwise.
  - use pointwiselub_islubpointwise.
Qed.

Lemma pointwiselub_isdcpomorphism {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  isdcpomorphism (pointwiselub F isdirec).
Proof.
  unfold isdcpomorphism. intros J v isdirecv.
  intros w wislub.
  unfold funcomp. split.
  - intro j. use pointwiselub_preservesorder. use (pr1 wislub).
  - intros d' ineqs.
    use (pr2 (pointwiselub_islubpointwise F isdirec w)).
    intro i. unfold pointwisefamily; simpl.
    set (Fi_preslub := pr2 (F i)); unfold isdcpomorphism in Fi_preslub;
      simpl in Fi_preslub.
    set (Fi_preslub' := (Fi_preslub J v isdirecv w wislub)).
    use (pr2 Fi_preslub').
    intro j. unfold funcomp; simpl.
    use istrans_posetRelation.
    + exact (pointwiselub F isdirec (v j)).
    + use (pr1 (pointwiselub_islubpointwise F isdirec (v j))).
    + exact (ineqs j).
Qed.

Lemma pointwiselub_islub {D D' : dcpo} {I : UU}
      (F : I -> posetofdcpomorphisms D D') (isdirec : isdirected F) :
  islub F (dcpomorphismpair _ _
                            (pointwiselub F isdirec)
                            (pointwiselub_isdcpomorphism F isdirec)).
Proof.
  split.
  - intro i; simpl. intro d; simpl.
    use (pr1 (pointwiselub_islubpointwise F isdirec d)).
  - intros h ineqs; simpl. intro d; simpl.
    use (pr2 (pointwiselub_islubpointwise F isdirec d)).
    intro i. use (ineqs i).
Qed.

Lemma posetofdcpomorphisms_isdirectedcomplete (D D' : dcpo) :
  isdirectedcomplete (posetofdcpomorphisms D D').
Proof.
  intros I F isdirec.
  split with (dcpomorphismpair D D' (pointwiselub F isdirec)
                               (pointwiselub_isdcpomorphism F isdirec)).
  use pointwiselub_islub.
Qed.

(* DCPO of dcpo morphisms *)
Definition dcpoofdcpomorphisms (D D' : dcpo) : dcpo.
Proof.
  use dcpopair.
  - exact (posetofdcpomorphisms D D').
  - exact (posetofdcpomorphisms_isdirectedcomplete D D').
Defined.

Delimit Scope DCPO with DCPO.
Local Open Scope DCPO.
Notation "A --> B" := (dcpoofdcpomorphisms A B) : DCPO.

(*** Least fixed points (μ) ***)
(* The chain ⊥, f(⊥), f²(⊥), ... *)
Definition leastfixedpointchain {D : dcpowithleast} (f : D --> D ) :
  nat -> D.
Proof.
  intro n. induction n as [ | m IH].
  induction D as [D' bottom].
  - exact (pr1 bottom).
  - exact ((pr1 f) (IH)).
Defined.

Lemma leastfixedpointchain_isomegachain {D : dcpowithleast} (f : D --> D) :
  ∏ (n : nat), ((leastfixedpointchain f n) ≤ leastfixedpointchain f (S n))%poset.
Proof.
  induction n as [ | m IH].
  - simpl. use dcpowithleast_least.
  - simpl. use dcpomorphism_preservesorder. use IH.
Qed.

Lemma leastfixedpointchain_increases {D : dcpowithleast} (f : D --> D) :
  ∏ (n m : nat), n ≤ m ->
                 (leastfixedpointchain f n ≤ leastfixedpointchain f m)%poset.
Proof.
  intros n m ineq.
  induction m as [ | m' IH].
  - set (nis0 := natleh0tois0 ineq).
    rewrite nis0. use isrefl_posetRelation.
  - set (cases := natlehchoice _ _ ineq).
    induction cases as [less | equal].
    + use istrans_posetRelation.
      * exact (leastfixedpointchain f m').
      * apply IH. use less.
      * use leastfixedpointchain_isomegachain.
    +  rewrite equal. use isrefl_posetRelation.
Qed.

Lemma leastfixedpointchain_isdirected {D : dcpowithleast} (f : D --> D) :
  isdirected (leastfixedpointchain f).
Proof.
  intros n m. use hinhpr. split with (n + m).
  split.
  + use leastfixedpointchain_increases. use natlehnplusnm.
  + use leastfixedpointchain_increases. use natlehmplusnm.
Qed.

(* Definition of μ *)
Definition leastfixedpoint {D : dcpowithleast} (f : D --> D) : D.
Proof.
  exact (pr1 ((dcpoisdirectedcomplete D) nat (leastfixedpointchain f)
                         (leastfixedpointchain_isdirected f))).
Defined.

Notation "'μ'" := leastfixedpoint : DCPO.

Lemma leastfixedpoint_islub {D : dcpowithleast} (f : D --> D) :
  islub (leastfixedpointchain f) (μ f).
Proof.
  unfold leastfixedpoint. induction (dcpoisdirectedcomplete D) as [d p].
  use p.
Qed.

Lemma leastfixedpoint_isfixedpoint {D : dcpowithleast} :
  ∏ (f : D --> D), (pr1 f) (μ f) = μ f.
Proof.
  intro f.
  (* We use that f preserves lubs of directed families *)
  set (fpreslub := ((pr2 f) nat (leastfixedpointchain f)
                            (leastfixedpointchain_isdirected f)
                            (leastfixedpoint f))).
  set (lubf := fpreslub (leastfixedpoint_islub f)).
  use isantisymm_posetRelation.
  - use (pr2 lubf).
    intro n. unfold funcomp; simpl.
    change (pr1 f (leastfixedpointchain f n)) with (leastfixedpointchain f (S n)).
    use (pr1 (leastfixedpoint_islub f)).
  - use (pr2 (leastfixedpoint_islub f)).
    intro n. destruct n as [ | m].
    + simpl. use dcpowithleast_least.
    + simpl. use dcpomorphism_preservesorder.
      use (pr1 (leastfixedpoint_islub f)).
Qed.

Lemma leastfixedpoint_isleast {D : dcpowithleast} (f : D --> D) :
  ∏ (d : D), ((pr1 f) d ≤ d)%poset -> (μ f ≤ d)%poset.
Proof.
  intros d ineq.
  use (pr2 (leastfixedpoint_islub f)).
  intro n; induction n as [ | m IH].
  - simpl. use (pr2 (pr2 D)).
  - simpl. use istrans_posetRelation.
    + exact ((pr1 f) d).
    + use dcpomorphism_preservesorder. exact IH.
    + exact ineq.
Qed.

Lemma leastfixedpointchain_preservesorder {D : dcpowithleast} (f g : D --> D) :
  (f ≤ g)%poset ->
  ∏ (n : nat), (leastfixedpointchain f n ≤ leastfixedpointchain g n)%poset.
Proof.
  intros ineq n; induction n as [ | m IH].
  - use isrefl_posetRelation.
  - simpl. use istrans_posetRelation.
    + exact (pr1 f (leastfixedpointchain g m)).
    + use dcpomorphism_preservesorder; exact IH.
    + use ineq.
Qed.

Lemma leastfixedpoint_isdcpomorphism (D : dcpowithleast) :
  isdcpomorphism (@leastfixedpoint D).
Proof.
  intros I F isdirec g islubg.
  split.
  - intro i.
    unfold funcomp; simpl.
    use (lubpreservesorder (leastfixedpointchain (F i))
                           (leastfixedpointchain g)).
    + use leastfixedpointchain_preservesorder.
      use (pr1 islubg).
    + use leastfixedpoint_islub.
    + use leastfixedpoint_islub.
  - intros d ineqs.
    use (pr2 (leastfixedpoint_islub g)). intro n.
    set (islub' := pointwiselub_islub F isdirec).
    set (eq := lubsareunique _ islubg islub').
    rewrite eq.
    set (h := dcpomorphismpair D D (pointwiselub F isdirec) (pointwiselub_isdcpomorphism F isdirec)).
    set (Fchain := λ (i : I), leastfixedpointchain (F i) n).
    assert (islubh : islub Fchain (leastfixedpointchain h n)).
    { unfold Fchain. split.
      - intro i. use leastfixedpointchain_preservesorder.
        use (pr1 (pointwiselub_islub F isdirec)).
      - intros y ineqs'. induction n as [ | m IH].
        + use dcpowithleast_least.
        + simpl. use (pr2 (pointwiselub_islubpointwise F isdirec _)).
          intro i. unfold pointwisefamily; simpl. admit. }
      (* use (pointwiselub_islubpointwise F isdirec (leastfixedpointchain (F i) n)). } *)

    use (pr2 islubh).
    intro i. unfold Fchain.
    use istrans_posetRelation.
    + exact (μ (F i)).
    + use (pr1 (leastfixedpoint_islub (F i))).
    + exact (ineqs i).
Qed.
