Require Import UniMath.Foundations.All.

Section DirectedComplete.
Context {X : hSet}.
Context (R : PartialOrder X).

Definition isleast (l : X) : UU := ∏ (x : X), R l x.
Lemma isleast_isaprop (l : X) : isaprop (isleast l).
Proof.
  use impred. intro x. use (pr2 (pr1 R l x)). (* R is prop-valued. *)
Qed.

Section FixIndexingFamily.
Context {I : UU}.
Context (f : I -> X). (* Indexing family *)

Definition isupperbound (u : X) : UU := ∏ (i : I), R (f i) u.
Lemma isupperbound_isaprop (u : X) : isaprop(isupperbound u).
Proof.
  use impred. intro i.
  use (pr2 (pr1 R (f i) u)). (* R is prop-valued. *)
Qed.

Definition islub (u : X) : UU := isupperbound u × ∏ (y : X), (∏ (i : I), R (f i) y) -> R u y.
Lemma islub_isaprop (u : X) : isaprop(islub u).
Proof.
  use isapropdirprod.
  - exact (isupperbound_isaprop u).
  - use impred. intro x. use impred. intro hyp.
    use (pr2 (pr1 R u x)). (* R is prop-valued. *)
Qed.

(* Definition directed : UU := ∏ (i j : I), ∑ (k : I), R (f i) (f k) × R (f j) (f k). *)
Definition isdirected : UU := ∏ (i j : I), ∥∑ (k : I), R (f i) (f k) × R (f j) (f k)∥.
Lemma isdirected_isaprop : isaprop isdirected.
Proof.
  use impred. intro i. use impred. intro j.
  use isapropishinh.
Qed.
End FixIndexingFamily.

Definition isdirectedcomplete : UU := ∏ (I : UU), ∏ (f : I -> X), isdirected f -> ∑ (u : X), islub f u.
Lemma isdirectedcomplete_isaprop : isaprop isdirectedcomplete.
Proof.
  use impred; intro I. use impred; intro f.
  use isapropimpl. use invproofirrelevance.
  intros [u p] [v q].
  assert (ueqv : u = v).
  { (* Use antisymmetry of R *)
    use (pr2 (pr2 R)).
    - apply p. use (pr1 q).
    - apply q. use (pr1 p). }
  apply total2_paths_equiv; split with ueqv.
  use proofirrelevance. use islub_isaprop.
Qed.
End DirectedComplete.

Definition dcpo := ∑ (X : Poset), isdirectedcomplete (pr2 X).
Definition dcpocarrier (D : dcpo) : hSet := carrierofposet (pr1 D).
Definition dcpoorder (D : dcpo) : PartialOrder (dcpocarrier D) := pr2 (pr1 D).
Definition dcpowithleast := ∑ (D : dcpo), ∑ (l : dcpocarrier D), isleast (dcpoorder D) l.