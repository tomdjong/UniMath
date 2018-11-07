Require Import UniMath.Foundations.All.

(* Definition of f × g *)
Definition dirprodfun {A B X Y : UU} (f : A -> X) (g : B -> Y) : A × B -> X × Y :=
  λ z : A × B, dirprodpair (f (pr1 z)) (g (pr2 z)).

Lemma pr1_dirprod_paths {A B : UU} {s s' : A × B} (p : pr1 s = pr1 s') (q : pr2 s = pr2 s') :
  maponpaths pr1 (@dirprod_paths _ _ s s' p q) = p.
Proof.
  induction s as [a b]. induction s' as [a' b']. simpl in p, q.
  induction p. induction q. use idpath.
Qed.

Lemma pr2_dirprod_paths {A B : UU} {s s' : A × B} (p : pr1 s = pr1 s') (q : pr2 s = pr2 s') :
  maponpaths dirprod_pr2 (@dirprod_paths _ _ s s' p q) = q.
Proof.
  induction s as [a b]. induction s' as [a' b']. simpl in p, q.
  induction p. induction q. use idpath.
Qed.

(* Describing the fiber of f × g in terms of the fibers of f and of g *)
Definition dirprodfun_fiber_equiv {A B X Y : UU} (f : A -> X) (g : B -> Y) (z : X × Y) :
  hfiber (dirprodfun f g) z ≃ hfiber f (dirprod_pr1 z) × hfiber g (dirprod_pr2 z).
Proof.
  use weq_iso.
  - intro prodfib. induction prodfib as [ab p]. induction ab as [a b]. split.
    + split with a. exact (maponpaths pr1 p).
    + split with b. exact (maponpaths dirprod_pr2 p).
  - intro fibers. induction fibers as [ffib gfib].
    induction ffib as [a p]. induction gfib as [b q].
    split with (a,,b).
    use dirprod_paths.
    + exact p.
    + exact q.
  - intro prodfib. induction prodfib as [ab p]. induction p. use idpath.
  - intro fibers. induction fibers as [ffib gfib]. induction ffib as [a p]. induction gfib as [b q].
    rewrite pr1_dirprod_paths. rewrite pr2_dirprod_paths. use idpath.
Defined.

Definition dirprodfun_preserves_incl {A B X Y : UU} (f : A -> X) (g : B -> Y) :
  isincl f -> isincl g -> isincl (dirprodfun f g).
Proof.
  intros fincl gincl. unfold isincl, isofhlevelf. intro z.
  eapply isofhlevelweqb.
  - exact (dirprodfun_fiber_equiv f g z).
  - use isapropdirprod.
    + use fincl.
    + use gincl.
Defined.

Definition sumfun {A : UU} {B C : A -> UU} :
  (∏ (a : A), B a -> C a) -> (∑ (a : A), B a) -> ∑ (a : A), C a.
Proof.
  intro f. intro x. induction x as [a b].
  exact (a,, f a b).
Defined.

Definition sumfun_fiber_equiv {A : UU} {B C : A -> UU} (f : ∏ (a : A), B a -> C a)
           (d : ∑ (a : A), C a) : hfiber (sumfun f) d ≃ hfiber (f (pr1 d)) (pr2 d).
Proof.
  use weq_iso. induction d as [a c].
  - intro sumfib; simpl.
    induction sumfib as [a'b p]; induction a'b as [a' b].
    unfold sumfun in p; apply total2_paths_equiv in p;
      induction p as [p1 p2]; simpl in p1, p2.
    split with (transportf B p1 b).
    assert (BCeq : f a (transportf B p1 b) = transportf C p1 (f a' b)).
    { generalize p1 as e; induction e; use idpath. }
    etrans. apply BCeq. exact p2.
  - induction d as [a c]. intro fib; simpl in fib.
    induction fib as [b p]. split with (a,,b).
    unfold sumfun. apply total2_paths_equiv.
    split with (idpath a);  exact p.
  - intro sumfib; induction sumfib as [ab' p].
    induction p; use idpath.
  - intro fib. induction d as [a c]; induction fib as [b q]; simpl in b, q.
    induction q; use idpath.
Defined.

Definition sumfun_preserves_incl {A : UU} {B C : A -> UU} (f : ∏ (a : A), B a -> C a) :
  (∏ (a : A), isincl (f a)) -> isincl (sumfun f).
Proof.
  intro forallaincl. unfold isincl, isofhlevelf.
  intro d; induction d as [a c].
  eapply isofhlevelweqb.
  - exact (sumfun_fiber_equiv f (a,,c)).
  - use (forallaincl a).
Defined.