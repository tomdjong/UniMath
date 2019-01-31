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


Context (B_Pidec : ∏ (a : A) (C : B a -> UU), (∏ (b : B a), decidable (C b)) ->
                                              decidable (∏ (b : B a), C b)).

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

(*Inductive indexedWtype {I : UU} {A : UU} {B : A -> UU}
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
  - assert (maponpathseq : p = maponpaths t e).
    { apply proofirrelevance, Iaset. }
    rewrite maponpathseq.
    rewrite indexedWtype_a_transport.
    induction (Adec a a) as [e' | _].
    + assert (e'eq : e' = idpath a).
      { apply proofirrelevance, isasetifdeceq, Adec. }
      rewrite e'eq.
      cbn; unfold idfun.
      intro c.
      apply maponpaths.
      unfold indexedWtype_f_transport.
      apply funextsec.
      intro b.
      apply IH.
      apply c.
    + apply fromempty.
  - (* Stuck *)
Defined.*)

Inductive indexedWtype' {I : UU} {A : UU} {B : A -> UU}
            (t : A -> I) (s : (∑ (a : A), B a) -> I) : I -> UU :=
| indexedsup' (i : I) (a : A) (p : t a = i) (f : ∏ (b : B a), indexedWtype' t s (s (a,,b))) :
    indexedWtype' t s i.

Context {I : UU}.
Context {A : UU}.
Context {B : A -> UU}.
Context (t : A -> I).
Context (s : (∑ (a : A), B a) -> I).
Context (W := indexedWtype' t s).
Context (Adec : isdeceq A).

Definition indexedWtype_s_transport {a a' : A} (e : a = a') (b : B a) :
  s(a,,b) = s(a',,transportf B e b).
Proof.
  induction e. apply idpath.
Defined.

Definition indexedWtype_code {i : I} (u v : W i) : UU.
Proof.
  induction u as [i a p _ IH].
  induction v as [i' a' p' f' _].
  induction (Adec a a') as [e | ne].
  - exact (∏ (b : B a), IH b (transportb W (indexedWtype_s_transport e b) (f' (transportf B e b)))).
  - exact empty.
Defined.
(*Fixpoint indexedWtype_code {i : I} (u v : W i) : UU :=
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
  end. *)

Definition indexedWtype_r {i : I} (w : W i) : indexedWtype_code w w.
Proof.
  induction w as [i a p f c].
  simpl.
  induction (Adec a a) as [eq | neq].
  - assert (triveq : eq = idpath _).
    { apply proofirrelevance, isasetifdeceq, Adec. }
    rewrite triveq. simpl. apply c.
  - apply neq, idpath.
Defined.

Definition indexedWtype_encode (i : I) (u v : W i) : u = v -> indexedWtype_code u v :=
  λ (p : u = v), transportf (λ w : W i, indexedWtype_code u w) p (indexedWtype_r u).



Definition indexedWtype_f_transport {a a' : A} (e : a = a')
           (f' : ∏ (b' : B a'), W (s(a',,b'))) : ∏ (b : B a), W (s(a,,b)).
Proof.
  intro b.
  exact (transportb W (indexedWtype_s_transport e b) (f' (transportf B e b))).
Defined.

Context (Iaset : isaset I).

Definition indexedWtype_index_transport {a : A} {i j : I} (p : t a = j) (q : i = j)
           (f : ∏ (b : B a), W (s(a,,b))) :
  transportb W q (indexedsup' t s j a p f) = indexedsup' t s i a (p @ !q) f.
Proof.
  induction q. cbn. unfold idfun. rewrite pathscomp0rid. apply idpath.
Defined.

Definition indexedWtype_decode_transport : ∏ (i : I) (u : W i) (j : I) (v : W j) (p : i = j),
                                   indexedWtype_code u (transportb W p v) -> u = (transportb W p v).
Proof.
  intro i.
  induction u as [i a p f IH].
  intro j.
  induction v as [i' a' p' f' _].
  intro q.
  rewrite (indexedWtype_index_transport p' q f').
  simpl. unfold coprod_rect.
  induction (Adec a a') as [e | ne].
  - assert (pathseq : p' @ ! q = (maponpaths t (!e)) @ p).
    { apply proofirrelevance, Iaset. }
    rewrite pathseq.
    generalize e as e'.
    induction e'. simpl.
    intro c.
    apply maponpaths.
    apply funextsec. (* Strong function extensionality *)
    intro b.
    set (IH' := IH b _ (f' b) (idpath _)).
    unfold transportb in IH'. simpl in IH'.
    rewrite idpath_transportf in IH'.
    apply IH'.
    apply c.
  - apply fromempty.
Defined.

Definition indexedWtype_decode (i : I) (u v : W i) : indexedWtype_code u v -> u = v.
Proof.
  set (helper := indexedWtype_decode_transport i u i v (idpath i)).
  unfold transportb in helper; simpl in helper.
  rewrite idpath_transportf in helper.
  exact helper.
Defined.

Context (B_Pidec : ∏ (a : A) (C : B a -> UU), (∏ (b : B a), decidable (C b)) ->
                                              decidable (∏ (b : B a), C b)).


Definition indexedWtype_dec (i : I) : isdeceq (W i).
Proof.
  unfold isdeceq. intros u' v'.
  eapply decidable_iff.
  - split.
    + apply indexedWtype_decode.
    + apply indexedWtype_encode.
  - generalize v' as v. generalize u' as u.
    clear u' v'.
    induction u as [i a p f IH].
    induction v as [i' a' p' f' _].
    simpl. unfold coprod_rect.
    induction (Adec a a') as [eq | neq].
    + apply (B_Pidec a _). intro b.
      apply IH.
    + apply isdecpropempty.
Defined.

Inductive indexedWtype {I : UU} {A : UU} {B : A -> UU}
            (t : A -> I) (s : (∑ (a : A), B a) -> I) : I -> UU :=
| indexedsup (a : A) (f : ∏ (b : B a), indexedWtype t s (s (a,,b))) :
    indexedWtype t s (t a).

Definition indexed_into_indexed' (i : I) : indexedWtype t s i -> indexedWtype' t s i.
Proof.
  intro w.
  induction w as [a f IH].
  eapply indexedsup'.
  - apply idpath.
  - exact IH.
Defined.

Definition indexed'_to_indexed (i : I) : indexedWtype' t s i -> indexedWtype t s i.
Proof.
  intro w'.
  induction w' as [i a p f IH].
  apply (transportf (indexedWtype t s) p).
  apply indexedsup.
  exact IH.
Defined.

Definition left_cancellable_indexed (i : I) :
  (indexed'_to_indexed i) ∘ (indexed_into_indexed' i) ~ idfun _.
Proof.
  intro w.
  induction w as [a f IH].
  unfold idfun.
  cbn.
  unfold idfun.
  apply maponpaths.
  apply funextsec.
  intro b.
  apply IH.
Defined.
