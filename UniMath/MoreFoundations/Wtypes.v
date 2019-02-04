Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PropExt.

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

Section picompact.
Definition picompact (X : UU) := ∏ (Y : X -> UU),
                                 (∏ (x : X), decidable (Y x)) ->
                                 decidable (∏ (x : X), Y x).
End picompact.

Section Wtypes.

Inductive Wtype {A : UU} (B : A -> UU) :=
| sup (a : A) (f : B a -> Wtype B) : Wtype B.

Context {A : UU}.
Context (B : A -> UU).

Context (Adeceq : isdeceq A).

Fixpoint Wtype_code (u v : Wtype B) : UU :=
  match u with
  | sup _ a f =>
    match v with
    | sup _ a' f' =>
      match (Adeceq a a') with
      | inr _ => empty
      | inl e => ∏ (b : B a), Wtype_code (f b) (f' (transportf B e b))
      end
    end
  end.

Definition Wtype_r (w : Wtype B) : Wtype_code w w.
Proof.
  induction w as [a f c].
  unfold Wtype_code.
  induction (Adeceq a a) as [eq | neq].
  - assert (triveq : eq = idpath _).
    { apply proofirrelevance, isasetifdeceq, Adeceq. }
    rewrite triveq. fold Wtype_code. exact c.
  - apply neq, idpath.
Defined.

Definition Wtype_encode (u v : Wtype B) : u = v -> Wtype_code u v :=
  λ (p : u = v), transportf (λ w : Wtype B, Wtype_code u w) p (Wtype_r u).

Definition Wtype_decode : ∏ (u v : Wtype B), Wtype_code u v -> u = v.
Proof.
  induction u as [a f IH].
  induction v as [a' f' _].
  unfold Wtype_code.
  induction (Adeceq a a') as [eq | neq].
  - fold Wtype_code. intro c.
    assert (feq : ∏ (b : B a), f b = f' (transportf B eq b)).
    { intro b. apply (IH b (f' (transportf B eq b))).
      apply (c b). }
    intermediate_path (sup B a (f' ∘ transportf B eq)).
    + apply maponpaths.
      apply funextfun.
      exact feq.
    + induction eq. apply idpath.
  - apply fromempty.
Defined.

Context (B_PiCompact : ∏ (a : A), picompact (B a)).

Definition Wtype_code_decidable : ∏ (u v : Wtype B), decidable (Wtype_code u v).
Proof.
  induction u as [a f IH].
  induction v as [a' f' _].
  unfold Wtype_code.
  induction (Adeceq a a') as [eq | neq].
  - fold Wtype_code.
    apply B_PiCompact.
    intro b.
    apply IH.
  - apply (isdecpropempty).
Defined.

Definition Wtype_deceq : isdeceq (Wtype B).
Proof.
  unfold isdeceq. intros u' v'.
  eapply decidable_iff.
  - split.
    + apply Wtype_decode.
    + apply Wtype_encode.
  - apply Wtype_code_decidable.
Defined.

End Wtypes.

Section indexedWtypes'.

Inductive indexedWtype'
          {I : UU}
          {A : UU}
          {B : A -> UU}
          (t : A -> I)
          (s : (∑ (a : A), B a) -> I) : I -> UU :=
| indexedsup'
    (i : I)
    (a : A)
    (p : t a = i)
    (f : ∏ (b : B a), indexedWtype' t s (s (a,,b))) : indexedWtype' t s i.

Context {I : UU}.
Context {A : UU}.
Context {B : A -> UU}.
Context (t : A -> I).
Context (s : (∑ (a : A), B a) -> I).

(** This is the intuitive reason why indexedWtypes' sometimes behave better
    than indexedWtypes: we can express transports of indexedsup' as another
    indexedsup'. *)
Definition indexedWtype'_index_transport {a : A} {i j : I}
           (p : t a = j) (q : i = j)
           (f : ∏ (b : B a), indexedWtype' t s (s(a,,b))) :
  transportb (indexedWtype' t s) q (indexedsup' t s j a p f) =
  indexedsup' t s i a (p @ !q) f.
Proof.
  induction q. cbn. unfold idfun.
  rewrite pathscomp0rid. apply idpath.
Defined.

Definition indexedWtype'_s_transport {a a' : A} (e : a = a') (b : B a) :
  s(a,,b) = s(a',,transportf B e b).
Proof.
  induction e. apply idpath.
Defined.

Context (Adec : isdeceq A).

Fixpoint indexedWtype'_code {i : I} (u v : indexedWtype' t s i) : UU :=
  match u with
  | indexedsup' _ _ _ a _ f =>
    match v with
    | indexedsup' _ _ _ a' _ f' =>
      match (Adec a a') with
      | inr _ => empty
      | inl e => ∏ (b : B a), @indexedWtype'_code
                                (s (a,,b))
                                (f b)
                                (transportb (indexedWtype' t s)
                                            (indexedWtype'_s_transport e b)
                                            (f' (transportf B e b)))
      end
    end
  end.


Definition indexedWtype'_r {i : I} (w : indexedWtype' t s i) :
  indexedWtype'_code w w.
Proof.
  induction w as [i a p f c].
  unfold indexedWtype'_code.
  induction (Adec a a) as [eq | neq].
  - intro b.
    fold (@indexedWtype'_code (s (a,,b))).
    assert (triveq : eq = idpath _).
    { apply proofirrelevance, isasetifdeceq, Adec. }
    rewrite triveq. apply c.
  - apply neq, idpath.
Defined.

Definition indexedWtype'_encode (i : I) (u v : indexedWtype' t s i) :
  u = v -> indexedWtype'_code u v :=
  λ (p : u = v), transportf
                   (λ w : indexedWtype' t s i, indexedWtype'_code u w)
                   p (indexedWtype'_r u).

Context (Iaset : isaset I).

Definition indexedWtype'_decode_transport :
  ∏ (i : I) (u : indexedWtype' t s i)
    (j : I) (v : indexedWtype' t s j) (p : i = j),
  indexedWtype'_code u (transportb (indexedWtype' t s) p v) ->
  u = (transportb (indexedWtype' t s) p v).
Proof.
  intro i.
  induction u as [i a p f IH].
  intro j.
  induction v as [i' a' p' f' _].
  intro q.
  rewrite (indexedWtype'_index_transport p' q f').
  unfold indexedWtype'_code.
  induction (Adec a a') as [e | ne].
  - intro c.
    assert (pathseq : p' @ ! q = (maponpaths t (!e)) @ p).
    { apply proofirrelevance, Iaset. }
    rewrite pathseq.
    induction e. cbn in *. unfold idfun in c.
    apply maponpaths.
    apply funextsec.
    intro b.
    set (IH' := IH b _ (f' b) (idpath _)).
    cbn in IH'. unfold idfun in IH'.
    apply IH'.
    apply c.
  - apply fromempty.
Defined.

Definition indexedWtype'_decode (i : I) (u v : indexedWtype' t s i) :
  indexedWtype'_code u v -> u = v.
Proof.
  set (helper := indexedWtype'_decode_transport i u i v (idpath i)).
  cbn in helper. unfold idfun in helper.
  exact helper.
Defined.

Context (B_PiCompact : ∏ (a : A), picompact (B a)).

Definition indexedWtype'_code_decidable {i : I} (u v : indexedWtype' t s i) :
  decidable (indexedWtype'_code u v).
Proof.
  induction u as [i a p f IH].
  induction v as [i' a' p' f' _].
  unfold indexedWtype'_code.
  induction (Adec a a') as [eq | neq].
  + apply B_PiCompact. intro b.
    fold (@indexedWtype'_code (s(a,,b))).
    apply IH.
  + apply isdecpropempty.
Defined.

Definition indexedWtype'_deceq (i : I) : isdeceq (indexedWtype' t s i).
Proof.
  unfold isdeceq. intros u' v'.
  eapply decidable_iff.
  - split.
    + apply indexedWtype'_decode.
    + apply indexedWtype'_encode.
  - apply indexedWtype'_code_decidable.
Defined.

End indexedWtypes'.

Section indexedWtypes.

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

Definition indexed_to_indexed' (i : I) :
  indexedWtype t s i -> indexedWtype' t s i.
Proof.
  intro w.
  induction w as [a f IH].
  eapply indexedsup'.
  - apply idpath.
  - exact IH.
Defined.

Definition indexed'_to_indexed (i : I) :
  indexedWtype' t s i -> indexedWtype t s i.
Proof.
  intro w'.
  induction w' as [i a p f IH].
  rewrite <- p.
  apply indexedsup.
  exact IH.
Defined.

Definition indexed_retractof_indexed' (i : I) :
  (indexed'_to_indexed i) ∘ (indexed_to_indexed' i) ~ idfun _.
Proof.
  intro w.
  induction w as [a f IH].
  unfold funcomp, idfun.
  simpl.
  apply maponpaths.
  apply funextsec.
  intro b.
  apply IH.
Defined.

Context (Adeceq : isdeceq A).
Context (Iaset : isaset I).
Context (B_PiCompact : ∏ (a : A), picompact (B a)).

Definition indexedWtype_deceq (i : I) : isdeceq (indexedWtype t s i).
Proof.
  eapply (isdeceq_retract (indexed_to_indexed' i)).
  - apply indexed_retractof_indexed'.
  - exact (indexedWtype'_deceq t s Adeceq Iaset B_PiCompact i).
Defined.

End indexedWtypes.

Section WtypesAlternativeProof.

Context {A : UU}.
Context (B : A -> UU).

Definition Wtype_to_indexedWtype :
  Wtype B -> indexedWtype (@tounit A) (@tounit (∑ (a : A), B a)) tt.
Proof.
  intro w. induction w as [a _ IH].
  use indexedsup.
  - exact a.
  - exact IH.
Defined.

Definition indexedWtype_to_Wtype :
  indexedWtype (@tounit A) (@tounit (∑ (a : A), B a)) tt -> Wtype B.
Proof.
  intro w. induction w as [a _ IH].
  eapply sup.
  exact IH.
Defined.

Definition Wtype_retractof_indexedWtype :
  (indexedWtype_to_Wtype) ∘ (Wtype_to_indexedWtype) ~ idfun _.
Proof.
  intro w. unfold idfun.
  induction w as [a f IH].
  cbn.
  apply maponpaths.
  apply funextsec.
  use IH.
Defined.

Context (Adeceq : isdeceq A).
Context (B_PiCompact : ∏ (a : A), picompact (B a)).

Definition Wtype_deceq' : isdeceq (Wtype B).
Proof.
  eapply (isdeceq_retract Wtype_to_indexedWtype).
  - apply Wtype_retractof_indexedWtype.
  - apply indexedWtype_deceq.
    + exact Adeceq.
    + apply isasetaprop. exact isapropunit.
    + exact B_PiCompact.
Defined.

End WtypesAlternativeProof.