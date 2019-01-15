Require Import UniMath.Foundations.All.

Section Wtypes.

Inductive Wtype {A : UU} {B : A -> UU} :=
| sup (a : A) (f : B a -> Wtype) : Wtype.

Context {A : UU}.
Context {B : A -> UU}.
Context (Adec : isdeceq A).

Fixpoint Wtype_code (u v : Wtype) : UU :=
  match u with
  | sup a f =>
    match v with
    | sup a' f' =>
      match (Adec a a') with
      | inr _ => empty
      | inl e => ∏ (b : B a), Wtype_code (f b) (f' (transportf B e b))
      end
    end
  end.

Definition Wtype_r (w : Wtype) : Wtype_code w w.
Proof.
  induction w as [a f c].
  simpl.
  induction (Adec a a) as [eq | neq].
  - assert (triveq : eq = idpath _).
    { apply proofirrelevance, isasetifdeceq, Adec. }
    rewrite triveq. apply c.
  - apply neq, idpath.
Defined.

Definition Wtype_encode (u v : Wtype) : u = v -> Wtype_code u v :=
  λ (p : u = v), transportf (λ w : Wtype, Wtype_code u w) p (Wtype_r u).

Context (B_Pidec : ∏ (a : A) (C : B a -> UU), (∏ (b : B a), decidable (C b)) ->
                                              decidable (∏ (b : B a), C b)).

Definition Wtype_decode : ∏ (u v : Wtype),  Wtype_code u v -> u = v.
Proof.
  induction u as [a f IH].
  induction v as [a' f' _].
  unfold Wtype_code.
  induction (Adec a a') as [eq | neq].
  - intro c.
    assert (feq : ∏ (b : B a), f b = f' (transportf B eq b)).
    { intro b. apply (IH b (f' (transportf B eq b))).
      apply (c b). }
    set (intermed := sup a (f' ∘ transportf B eq)).
    intermediate_path intermed.
    + unfold intermed. apply maponpaths.
      apply funextfun.
      exact feq.
    + unfold intermed. generalize eq as e.
      induction e. apply idpath.
  - apply fromempty.
Defined.

Definition decidable_iff (X Y : UU) (iff : X <-> Y) : decidable X <-> decidable Y.
Proof.
  induction iff as [f g].
  split.
  - intro Xdec. induction Xdec as [x | nx].
    + apply inl. exact (f x).
    + apply inr. intro y. apply nx. exact (g y).
  - intro Ydec. induction Ydec as [y | ny].
    + apply inl. exact (g y).
    + apply inr. intro x. apply ny. exact (f x).
Defined.

Definition Wtype_dec : isdeceq (@Wtype A B).
Proof.
  unfold isdeceq. intros u' v'.
  eapply decidable_iff.
  - split.
    + apply Wtype_decode.
    + apply Wtype_encode.
  - generalize v' as v. generalize u' as u.
    clear u' v'.
    induction u as [a f IH].
    induction v as [a' f' _].
    unfold Wtype_code.
    induction (Adec a a') as [eq | neq].
    + apply (B_Pidec a _). intro b.
      exact (IH b (f' (transportf B eq b))).
    + apply isdecpropempty.
Defined.

End Wtypes.

Section IndexedWTypes.

Inductive indexedWtype {I : UU} {A : UU} {B : A -> UU}
            (t : A -> I) (s : (∑ (a : A), B a) -> I) : I -> UU :=
| indexedsup (a : A) (f : ∏ (b : B a), indexedWtype t s (s (a,,b))) :
    indexedWtype t s (t a).

Context {I : UU}.
Context {A : UU}.
Context {B : A -> UU}.
Context (t : A -> I).
Context (s : (∑ (a : A), B a) -> I).
Context (W := indexedWtype t s).
Context (Adec : isdeceq A).

Definition indexedWtype_s_transport {a a' : A} (e : a = a') (b : B a) :
  s(a,,b) = s(a',,transportf B e b).
Proof.
  induction e. apply idpath.
Defined.

Fixpoint indexedWtype_code {i : I} (u v : W i) : UU :=
  match u with
  | indexedsup _ _ a f =>
    match v with
    | indexedsup _ _ a' f' =>
      match (Adec a a') with
      | inr _ => empty
      | inl e => ∏ (b : B a), @indexedWtype_code (s (a,,b)) (f b)
                                                (transportb W (indexedWtype_s_transport e b)
                                                (f' (transportf B e b)))
      end
    end
  end.

Definition indexedWtype_r {i : I} (w : W i) : indexedWtype_code w w.
Proof.
  induction w as [a f c].
  simpl.
  induction (Adec a a) as [eq | neq].
  - assert (triveq : eq = idpath _).
    { apply proofirrelevance, isasetifdeceq, Adec. }
    rewrite triveq. apply c.
  - apply neq, idpath.
Defined.

Definition indexedWtype_encode (i : I) (u v : W i) : u = v -> indexedWtype_code u v :=
  λ (p : u = v), transportf (λ w : W i, indexedWtype_code u w) p (indexedWtype_r u).


Context (B_Pidec : ∏ (a : A) (C : B a -> UU), (∏ (b : B a), decidable (C b)) ->
                                              decidable (∏ (b : B a), C b)).

Definition indexedWtype_f_transport {a a' : A} (e : a = a')
           (f' : ∏ (b' : B a'), W (s(a',,b'))) : ∏ (b : B a), W (s(a,,b)).
Proof.
  intro b.
  exact (transportb W (indexedWtype_s_transport e b) (f' (transportf B e b))).
Defined.

Definition indexedWtype_a_transport {a a' : A} (e : a = a')
           (f' : ∏ (b' : B a'), W (s(a',,b'))) :
  transportb W (maponpaths t e) (indexedsup t s a' f') =
  indexedsup t s a (indexedWtype_f_transport e f').
Proof.
  induction e. apply idpath.
Defined.

Context (Iaset : isaset I).

Definition indexedWtype_decode : ∏ (i : I) (u : W i) (j : I) (v : W j) (p : i = j),
                                   indexedWtype_code u (transportb W p v) -> u = (transportb W p v).
Proof.
  induction u as [a f IH].
  induction v as [a' f' _].
  intro p. cbn.
  induction (Adec a a') as [e | ne].
  - admit.
  - intro c. inversion c. apply fromempty, ne.

    assert (p = maponpaths
Defined.
