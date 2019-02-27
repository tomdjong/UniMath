(**

Tom de Jong

Created: February 2019

Adapted from
[https://github.com/jashug/IWTypes/blob/master/FiberProperties.v]

*******************************************************************************)

(** * A sufficient condition for decidable equality on indexed W-types *)
(** ** Contents
- Some lemmas on decidable (equality of) types ([decidable])
- Definition of and lemmas on Pi-compact types ([picompact])
- Indexed W-types with decidable equality ([deceq_indexedWtypes])
*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PropExt.

(** * Some lemmas on decidable (equality of) types *)
Section decidable.

Definition decidable_iff {X Y : UU} (f : X <-> Y) :
  decidable X -> decidable Y.
Proof.
  intro Xdec.
  induction Xdec as [x | nX].
  - exact (inl (pr1 f x)).
  - apply inr. intro y.
    apply nX. exact (pr2 f y).
Defined.

Definition isdeceq_retract {X Y : UU} (s : X -> Y) (r : Y -> X)
  (retract : ∏ (x : X), (r (s x)) = x) : isdeceq Y -> isdeceq X.
Proof.
  intro Ydeceq.
  intros x x'.
  induction (Ydeceq (s x) (s x')) as [Yeq | nYeq].
  - apply inl.
    etrans.
    + exact (!retract x).
    + rewrite Yeq.
      exact (retract x').
  - apply inr. intro eq.
    apply nYeq.
    exact (maponpaths s eq).
Defined.

End decidable.

(** * Definition of and lemmas on Pi-compact types *)
Section picompact.

Definition picompact (X : UU) := ∏ (Y : X -> UU),
                                 (∏ (x : X), decidable (Y x)) ->
                                 decidable (∏ (x : X), Y x).

Definition picompact_empty : picompact (empty).
Proof.
  intros Y ptdec.
  apply inl.
  intro x.
  induction x.
Defined.

Definition picompact_unit : picompact (unit).
Proof.
  intros Y ptdec.
  induction (ptdec tt) as [pos | neg].
  - apply inl.
    intro t.
    induction t.
    exact pos.
  - apply inr.
    intro hyp.
    apply neg.
    apply hyp.
Defined.

Definition picompact_coprod (X Y : UU) :
  picompact X -> picompact Y -> picompact (X ⨿ Y).
Proof.
  intros Xpc Ypc F ptdec.
  set (FX := λ (x : X), F (inl x)).
  set (FY := λ (y : Y), F (inr y)).
  assert (FXptdec : ∏ (x : X), decidable (FX x)).
  { intro x. exact (ptdec (inl x)). }
  assert (FYptdec : ∏ (y : Y), decidable (FY y)).
  { intro y. exact (ptdec (inr y)). }
  induction (Xpc FX FXptdec) as [posX | negX].
  - induction (Ypc FY FYptdec) as [posY | negY].
    + apply inl. intro z.
      induction z as [x | y].
      * apply posX.
      * apply posY.
    + apply inr.
      intro hyp. apply negY.
      intro y.
      apply hyp.
  - apply inr.
    intro hyp.
    apply negX.
    intro x.
    apply hyp.
Defined.

End picompact.

(** * Indexed W-types with decidable equality *)
Section deceq_indexedWtypes.

Inductive indexedWtype
          {I : UU}
          {A : UU}
          {B : A -> UU}
          (t : A -> I)
          (s : (∑ (a : A), B a) -> I) : I -> UU :=
| indexedsup (a : A) (f : ∏ (b : B a), indexedWtype t s (s (a,,b))) :
    indexedWtype t s (t a).

Context {I : UU}.
Context {A : UU}.
Context {B : A -> UU}.
Context (t : A -> I).
Context (s : (∑ (a : A), B a) -> I).

Definition subtrees_type (a : A) := ∏ (b : B a), indexedWtype t s (s(a,,b)).

Definition subtrees {i : I} : indexedWtype t s i ->
                              ∑ (fib : hfiber t i), subtrees_type (pr1 fib).
Proof.
  intro w.
  induction w as [a f _].
  exists (a,,idpath (t a)).
  exact f.
Defined.

Definition dec_depeq {X : UU} (Y : X -> UU) (x : X) (y y' : Y x) :
  isaset X -> (x,,y) = (x,,y') -> y = y'.
Proof.
  intros Xaset paireq.
  apply total2_paths_equiv in paireq.
  induction paireq as [eq1 eq2].
  cbn in *.
  assert (triveq : eq1 = idpath x).
  { apply Xaset. }
  rewrite triveq in eq2.
  exact eq2.
Defined.

Definition subtrees_eq (a : A) (f g : ∏ (b : B a), indexedWtype t s (s(a,,b)))
           (fibdeceq : ∏ (i : I), isdeceq (hfiber t i)) :
  indexedsup t s a f = indexedsup t s a g -> f = g.
Proof.
  intro supeq.
  set (depeq := maponpaths subtrees supeq).
  cbn in *.
  exact (dec_depeq _ (a,, idpath (t a)) f g
                   (isasetifdeceq _ (fibdeceq (t a))) depeq).
Defined.

Definition getfib {i : I} : indexedWtype t s i -> hfiber t i.
Proof.
  intro w.
  induction w as [a _ _].
  exact (a,,idpath (t a)).
Defined.

Definition getfib_transport {i j : I} (w : indexedWtype t s i) (p : i = j) :
  getfib (transportf (indexedWtype t s) p w) =
  hfiberpair t (pr1 (getfib w)) (pr2 (getfib w) @ p).
Proof.
  induction p.
  rewrite pathscomp0rid.
  apply idpath.
Defined.

Definition indexedWtype_deceq_transport :
  (∏ (i : I), isdeceq (hfiber t i)) ->
  (∏ (a : A), picompact (B a)) ->
  ∏ (i : I)
    (u : indexedWtype t s i)
    (j : I)
    (p : i = j)
    (v : indexedWtype t s j),
    decidable (transportf _ p u = v).
Proof.
  intros fibdeceq Bpicompact.
  intros i u.
  induction u as [a  f IH].
  intros j p v.
  induction v as [a' f' _].
  induction (fibdeceq (t a') (a',,idpath (t a')) (a,,p)) as [eq | neq].
  - apply total2_paths_equiv in eq.
    induction eq as [e1 e2].
    cbn in *.
    induction e1.
    cbn in e2. unfold idfun in e2.
    rewrite <- e2.
    cbn. unfold idfun.
    set (helper := Bpicompact a' _
                              (λ (b : B a'), IH b (s(a',,b))
                              (idpath _)
                              (f' b))).
    cbn in helper. unfold idfun in helper.
    induction helper as [feq | nfeq].
    + apply inl.
      apply maponpaths.
      apply funextsec.
      use feq.
    + apply inr.
      intro hyp.
      apply nfeq.
      apply eqtohomot.
      exact (subtrees_eq _ _ _ fibdeceq hyp).
  - apply inr.
    intro hyp.
    apply neq.
    set (fibeq := maponpaths getfib hyp).
    cbn in fibeq.
    etrans.
    + apply pathsinv0, fibeq.
    + apply getfib_transport.
Defined.

Definition indexedWtype_deceq :
  (∏ (i : I), isdeceq (hfiber t i)) ->
  (∏ (a : A), picompact (B a)) ->
  ∏ (i : I), isdeceq (indexedWtype t s i).
Proof.
  intros fibdeceq Bpicompact.
  intros i u v.
  exact (indexedWtype_deceq_transport fibdeceq Bpicompact i u i (idpath _) v).
Defined.

Definition indexedWtype_deceq' :
  isdeceq A -> isaset I -> (∏ (a : A), picompact (B a)) ->
  ∏ (i : I), isdeceq (indexedWtype t s i).
Proof.
  intros Adeceq Iaset Bpicompact.
  use indexedWtype_deceq.
  - intros i [a p] [a' p'].
    induction (Adeceq a a') as [e | ne].
    + apply inl.
      apply total2_paths_equiv.
      exists e.
      apply Iaset.
    + apply inr.
      intro hyp.
      apply total2_paths_equiv in hyp.
      apply ne, (pr1 hyp).
  - exact Bpicompact.
Defined.

End deceq_indexedWtypes.