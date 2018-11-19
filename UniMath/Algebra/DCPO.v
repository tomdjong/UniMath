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
  assert (ueqv : u = v).
  { (* Use antisymmetry of R *)
    use isantisymm_posetRelation.
    - apply p. use (pr1 q).
    - apply q. use (pr1 p). }
  apply total2_paths_equiv; split with ueqv.
  use proofirrelevance. use islub_isaprop.
Qed.

Definition dcpo := ∑ (X : Poset), isdirectedcomplete X.
Definition dcpoposet (D : dcpo) : Poset := pr1 D.
Coercion dcpoposet : dcpo >-> Poset.
Definition dcpocarrier (D : dcpo) : hSet := carrierofposet (dcpoposet D).
Definition dcpoorder (D : dcpo) : PartialOrder (dcpocarrier D) :=
  pr2 (dcpoposet D).
Definition dcpowithleast := ∑ (D : dcpo), ∑ (l : dcpocarrier D), isleast l.
Definition dcpowithleastdcpo : dcpowithleast -> dcpo := pr1.
Coercion dcpowithleastdcpo : dcpowithleast >-> dcpo.

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

(* This could use a cleanup. *)
Lemma posetofdcpomorphisms_isdirectedcomplete (D D' : dcpo) :
  isdirectedcomplete (posetofdcpomorphisms D D').
Proof.
  intros I F isdirec.
  (* For any d : D, the family (f (d))_(f : F) is directed. *)
  set (Fatd := λ d : D, λ i : I, pr1 (F i) d).
  assert (isdirec' : ∏ (d : D), isdirected (Fatd d)).
  { intros d i j. use factor_through_squash.
    - exact (directeduntruncated F i j).
    - use isapropishinh.
    - intro direc. use hinhpr.
      induction direc as [k ineqs].
      split with k; simpl.
      induction ineqs as [ineq1 ineq2]. split.
      + exact (ineq1 d).
      + exact (ineq2 d).
    - exact (isdirec i j). }
  (* The lub of (f : F) will be g with g(d) = lub (f(d))_(f : F) *)
  set (isdireccompl := pr2 D'); simpl in isdireccompl.
  set (gdata := λ d : D, isdireccompl I _ (isdirec' d)).
  set (g := λ d : D, pr1 (gdata d)).
  assert (gpreservesorder : isaposetmorphism g).
  { intros x y ineq. use lubpreservesorder.
    - exact I.
    - exact (λ i : I, pr1 (F i) x).
    - exact (λ i : I, pr1 (F i) y).
    - intro i. simpl. use dcpomorphism_preservesorder.
      exact ineq.
    - exact (pr2 (gdata x)).
    - exact (pr2 (gdata y)). }
  assert (gdirlub : isdcpomorphism g).
  { intros J u isdirecu v islubv. split.
    - intro j. unfold funcomp; simpl. use gpreservesorder.
      use (pr1 islubv j).
    - intros v' ineqs.
      assert (v'ineq : ∏ (i : I), ∏ (j : J),
                       (pr1 (F i) (u j) ≤ v')%poset).
      { intros i j. use istrans_posetRelation.
        - exact (g (u j)).
        - set (gislub := pr2 (gdata (u j))); simpl in gislub.
          exact (pr1 gislub i).
        - exact (ineqs j). }
      assert (v'ineq' : ∏ (i : I), (pr1 (F i) v ≤ v')%poset).
      { intro i. set (preslub := pr2 (F i));
        simpl in preslub; unfold isdcpomorphism in preslub.
        set (preslub' := preslub J u isdirecu).
        set (preslub'' := preslub' v islubv).
        unfold funcomp in preslub''; simpl in preslub''.
        set (helper := pr2 preslub'' v'). apply helper.
        use v'ineq. }
      set (gislub := pr2 (gdata v)); unfold Fatd in gislub; simpl in gislub.
      use (pr2 gislub). intros i; simpl. exact (v'ineq' i). }
  split with (dcpomorphismpair D D' g gdirlub).
  split.
  - intro i. simpl. intro d.
    set (gdata' := pr1 (pr2 (gdata d)) i). use gdata'.
  - intros h ineqs; simpl. intro d.
    use (pr2 (pr2 (gdata d))). unfold Fatd.
    intro i. exact (ineqs i d).
Qed.

  (* DCPO of dcpo morphisms *)
Definition dcpoofdcpomorphisms {D D' : dcpo} : dcpo.
Proof.
  use dcpopair.
  - exact (posetofdcpomorphisms D D').
  - exact (posetofdcpomorphisms_isdirectedcomplete D D').
Defined.

(*** Least fixed points (μ) ***)
(* The chain ⊥, f(⊥), f²(⊥), ... *)
Definition leastfixedpointchain {D : dcpowithleast} (f : dcpomorphism D D) :
  nat -> D.
Proof.
  intro n. induction n as [ | m IH].
  induction D as [D' bottom].
  - exact (pr1 bottom).
  - exact (f (IH)).
Defined.

Lemma leastfixedpointchain_isomegachain {D : dcpowithleast} (f : dcpomorphism D D) :
  ∏ (n : nat), ((leastfixedpointchain f n) ≤ leastfixedpointchain f (S n))%poset.
Proof.
  induction n as [ | m IH].
  - simpl. use (pr2 (pr2 D)). (* ⊥ is least *)
  - simpl. use dcpomorphism_preservesorder. use IH.
Qed.
