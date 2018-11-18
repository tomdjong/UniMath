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

Definition islub (u : X) : UU := isupperbound u × ∏ (y : X), (∏ (i : I), R (f i) y) -> R u y.
Lemma islub_isaprop (u : X) : isaprop(islub u).
Proof.
  use isapropdirprod.
  - exact (isupperbound_isaprop u).
  - use impred. intro x. use impred. intro hyp.
    use (pr2 (R u x)). (* R is prop-valued. *)
Qed.

(* Definition directed : UU := ∏ (i j : I), ∑ (k : I), R (f i) (f k) × R (f j) (f k). *)
Definition isdirected : UU := ∏ (i j : I), ∥∑ (k : I), R (f i) (f k) × R (f j) (f k)∥.
Lemma isdirected_isaprop : isaprop isdirected.
Proof.
  use impred. intro i. use impred. intro j.
  use isapropishinh.
Qed.
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
Definition dcpoorder (D : dcpo) : PartialOrder (dcpocarrier D) := pr2 (dcpoposet D).
Definition dcpowithleast := ∑ (D : dcpo), ∑ (l : dcpocarrier D), isleast l.

Definition dcpopair (X : Poset) (i : isdirectedcomplete X) : dcpo := (X,,i).

Definition preservesdirected {P Q : Poset} (f : P -> Q) : UU :=
  ∏ (I : UU), ∏ (u : I -> P), isdirected u -> isdirected (f ∘ u).
Lemma preservesdirected_isaprop {P Q : Poset} (f : P -> Q) : isaprop (preservesdirected f).
Proof.
  use impred; intro I. use impred; intro u.
  use isapropimpl. use isdirected_isaprop.
Qed.

Definition preserveslub {P Q : Poset} (f : P -> Q) {I : UU} (u : I -> P) : UU :=
  ∏ (v : P), islub u v -> islub (f ∘ u) (f v).
Lemma preserveslub_isaprop {P Q : Poset} (f : P -> Q) {I : UU} (u : I -> P) :
  isaprop (preserveslub f u).
Proof.
  use impred; intro v.
  use isapropimpl. use islub_isaprop.
Qed.

Definition isdcpomorphism {D D' : dcpo} (f : D -> D') :=
  preservesdirected f × ∏ (I : UU), ∏ (u : I -> D), isdirected u ->
                                                    preserveslub f u.
Lemma isdcpomorphism_isaprop {D D' : dcpo} (f : D -> D') : isaprop (isdcpomorphism f).
Proof.
  use isapropdirprod.
  - use preservesdirected_isaprop.
  - use impred; intro I; use impred; intro u. use isapropimpl. use preserveslub_isaprop.
Qed.

Definition dcpomorphism (D D' : dcpo) := ∑ (f : D -> D'), isdcpomorphism f.
Definition dcpomorphismpair (D D': dcpo) : ∏ (t : D -> D'), isdcpomorphism t ->
                                                            dcpomorphism D D'.
Proof.
  intros t i. exact (t,,i).
Defined.

Definition dcpomorphismcarrier {D D' : dcpo} : dcpomorphism D D' -> (D -> D') := pr1.
Coercion dcpomorphismcarrier : dcpomorphism >-> Funclass.

Lemma dcpomorphism_preservesorder {D D' : dcpo} (f : dcpomorphism D D') : isaposetmorphism f.
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
  { use (pr2 (pr2 f)). exact isdirec. exact lubfam. }
  set (ineq' := pr1 lubfam'). use (ineq' (inl tt)).
Qed.

Definition posetmorphismorder (P Q : Poset) : hrel (posetmorphism P Q).
Proof.
  intros f g. use hProppair.
  - exact (∏ (p : P), (posetRelation Q) (f p) (g p)). (* Pointwise *)
  - use impred; intro p. exact (pr2 (posetRelation Q (f p) (g p))).
Defined.

Definition posetmorphismorder_ispartialorder (P Q : Poset) :
  isPartialOrder (posetmorphismorder P Q).
Proof.
  split.
  - split.
    + intros f g h ineq1 ineq2 p.
      exact (istrans_posetRelation Q _ (g p) _ (ineq1 p) (ineq2 p)).
    + intros f p. use isrefl_posetRelation.
  - intros f g ineq1 ineq2. apply total2_paths_equiv.
    assert (funeq : pr1 f = pr1 g).
    { use funextfun. intro p. use isantisymm_posetRelation.
      ** use ineq1.
      ** use ineq2. }
    split with funeq.
    use proofirrelevance. use isaprop_isaposetmorphism.
Defined.

Definition posetofposetmorphisms (P Q : Poset) : Poset.
Proof.
  use Posetpair.
  - use hSetpair.
    + exact (posetmorphism P Q).
    + unfold posetmorphism. change isaset with (isofhlevel 2).
      use isofhleveltotal2.
      use impred; intro p. use (pr2 (carrierofposet Q)).
      intro f. use isasetaprop. use isaprop_isaposetmorphism.
  - use PartialOrderpair.
    + use posetmorphismorder.
    + use posetmorphismorder_ispartialorder.
Defined.