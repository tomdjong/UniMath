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

Definition Wtype_canonical_data {i : I} (w : W i) : ∑ (a : A),
                                                    (∏ (b : B a), W (s(a,,b))) × (i = t a).
Proof.
  induction w as [a f _].
  exists a.
  split.
  - exact f.
  - exact (idpath (t a)).
Defined.

Definition mk_Wtype_canonical {i : I} (w : W i) : W i.
Proof.
  induction w as [a f _].
  exact (transportb W (idpath (t a)) (indexedsup t s a f)).
Defined.

Definition Wtype_canonical_eq {i : I} (w : W i) : w = mk_Wtype_canonical w.
Proof.
  induction w. apply idpath.
Defined.

Fixpoint indexedWtype_code {i : I} (u v : W i) : UU :=
  match u with
  | indexedsup _ _ a f =>
    let a' := pr1 (Wtype_canonical_data v) in
    let f' := pr1 (pr2 (Wtype_canonical_data v)) in
      match (Adec a a') with
      | inr _ => empty
      | inl e => ∏ (b : B a), @indexedWtype_code (s (a,,b)) (f b)
                                                (transportb W (indexedWtype_s_transport e b)
                                                (f' (transportf B e b)))
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

(* Definition Wtype_canonical_indexedsup {i : I} (a' : A) (p : i = t a')
           (f' : ∏ (b' : B a'), W (s(a',,b'))) :
  mk_Wtype_canonical (transportb W p (indexedsup t s a' f')) =
  transportb W p (indexedsup t s a' f').
Proof.
  unfold mk_Wtype_canonical. cbn. unfold idfun.
  unfold indexedWtype_rect. *)

Definition indexedWtype_decode : ∏ (i : I) (u : W i) (j : I) (v : W j) (p : i = j),
                                   indexedWtype_code u (transportb W p v) -> u = (transportb W p v).
Proof.
  induction u as [a f IH].
  intros j v p.
  cbn.
  induction ( Adec a (pr1 (Wtype_canonical_data (transportb W p v)))) as [e | ne].
  - intro c.
    induction v.


  induction v as [a' f' _].
  cbn. intro p.
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
      apply funextsec. (* Stronger than function extensionality *)
      intro b.
      apply IH.
      apply c.
    + apply fromempty.
  - admit.
Admitted.*)

  Context (B_Pidec : ∏ (a : A) (C : B a -> UU), (∏ (b : B a), decidable (C b)) ->
                                              decidable (∏ (b : B a), C b)).

Definition indexedWtype_s_transport {a a' : A} (e : a = a') (b : B a) :
  s(a,,b) = s(a',,transportf B e b).
Proof.
  induction e. apply idpath.
Defined.


Definition indexedWtype_code {i : I} (u v : W i) : UU.
Proof.
  induction u as [a f IH].
  induction (Wtype_canonical (t a) v) as [a' rest].
  induction rest as [f' rest'].
  induction rest' as [p veq].
  induction (Adec a a') as [e | ne].
  - exact (∏ (b : B a), IH b (transportb W (indexedWtype_s_transport e b) (f' (transportf B e b)))).
  - exact empty.
Defined.

Definition indexedWtype_r {i : I} (w : W i) : indexedWtype_code w w.
Proof.
  induction w as [a f c].
  simpl.
  induction (Adec a a) as [eq | neq].
  - assert (triveq : eq = idpath _).
    { apply proofirrelevance, isasetifdeceq, Adec. }
    rewrite triveq. cbn. apply c.
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

(*Context (indexeq_function : ∏ (a a' : A) (f' : ∏ (b' : B a'), W (s(a',,b'))) (p : t a = t a'),
           ∑ (a'' : A) (e : a' = a'') (g : ∏ (b'' : B a''), W (s(a'',,b''))),
           transportb W p (indexedsup t s a' f') =
           transportb W (maponpaths t e) (indexedsup t s a'' g)).*)

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
    cbn.
    induction (Adec a a) as [e' | ne'].
    + cbn.
      assert (e'eq : e' = idpath a).
      { apply proofirrelevance, isasetifdeceq, Adec. }
      rewrite e'eq.
      cbn; unfold idfun.
      intro c.
      apply maponpaths.
      apply funextsec. (* Stronger than function extensionality *)
      intro b.
      apply IH.
      apply c.
    + apply fromempty.
  - assert (pr1 (Wtype_canonical (t a) (transportb W p (indexedsup t s a' f'))) = a').
    { admit. }
    set (a'' := pr1 (Wtype_canonical (t a) (transportb W p (indexedsup t s a' f')))).
    induction (Adec a (pr1 (Wtype_canonical (t a) (transportb W p (indexedsup t s a' f'))))).
    + rewrite X in a0. apply fromempty. apply ne. exact a0.
    + admit.
Admitted.

Definition Wtypecode_deceq (i : I) (u v : W i) : decidable (indexedWtype_code u v).
Proof.
  induction u as [a f IH].
  simpl. unfold coprod_rect.
  induction (Adec a (pr1 (Wtype_canonical (t a) v))) as [e | ne].
  - admit.
  - apply inr. unfold neg.
    induction (Adec a (pr1 (Wtype_canonical (t a) v))) as [e' | ne'].
    + admit.
    +
    intro c.
    set (ne' := @ii2 (a = pr1 (Wtype_canonical (t a) v)) (a != pr1 (Wtype_canonical (t a) v)) ne).
    unfold coprod_rect in c.

    set (c' := c ne').