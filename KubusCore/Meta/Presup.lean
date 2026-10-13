import KubusCore.Meta.KanU

/-!
# Metatheory: presupposition

`pre_eq`: both sides of a derivable equation are typed, and its type is a type, provided the
contracta of the computation rules listed in `ContractaTyped` are typed whenever the redex is.
These are the rules whose contractum's typing would have to be read off the redex's typing
through conversions, which needs injectivity of type formers (`docs/metatheory.md`), or which
are not yet done (boundaries of constructors). All other rules are proven here:
structural rules, congruences, η-rules, the face rules and the boundary rules of systems,
`transp` and `hcomp`, `hcomp` in `Π`, `(i : I) → A` (`HcompTyped.lean`), `PathP` (`KanPath.lean`), `Σ` (`KanSigma.lean`) Glue types (`KanGlue.lean`) and `U` (`KanU.lean`), and the Glue face
and η rules.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- The contracta of these computation rules are typed whenever their redexes are. -/
structure ContractaTyped (S : Sig) : Prop where
  piBeta : ∀ {Ψ Φ Γ A t a T}, HasTy0 S Ψ Φ Γ (app (lam A t) a) T → HasTy0 S Ψ Φ Γ (t.inst a) T
  fstBeta : ∀ {Ψ Φ Γ a b T}, HasTy0 S Ψ Φ Γ (fst (pair a b)) T → HasTy0 S Ψ Φ Γ a T
  sndBeta : ∀ {Ψ Φ Γ a b T}, HasTy0 S Ψ Φ Γ (snd (pair a b)) T → HasTy0 S Ψ Φ Γ b T
  pathBeta : ∀ {Ψ Φ Γ t r T}, HasTy0 S Ψ Φ Γ (papp (plam t) r) T → HasTy0 S Ψ Φ Γ (t.dinst r) T
  transpPi : ∀ {Ψ Φ Γ A B φ u0 T}, HasTy0 S Ψ Φ Γ (transp (pi A B) φ u0) T →
    HasTy0 S Ψ Φ Γ (transpPi A B φ u0) T
  transpSigma : ∀ {Ψ Φ Γ A B φ u0 T}, HasTy0 S Ψ Φ Γ (transp (sigma A B) φ u0) T →
    HasTy0 S Ψ Φ Γ (transpSigma A B φ u0) T
  transpPath : ∀ {Ψ Φ Γ A a b φ p0 T}, HasTy0 S Ψ Φ Γ (transp (path A a b) φ p0) T →
    HasTy0 S Ψ Φ Γ (transpPath A a b φ p0) T
  transpIPi : ∀ {Ψ Φ Γ A φ u0 T}, HasTy0 S Ψ Φ Γ (transp (ipi A) φ u0) T →
    HasTy0 S Ψ Φ Γ (transpIPi A φ u0) T
  transpGlue : ∀ {Ψ Φ Γ A φ T' e ψ u0 T l δ}, HasTy0 S Ψ Φ Γ (transp (glue A φ T' e) ψ u0) T →
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l) →
    HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift e (equiv T' A) →
    I.Entails δ φ.forall0 → I.Entails φ.forall0 δ → HasTy0 S Ψ Φ Γ (transpGlueWith δ A φ T' e ψ u0) T
  conBnd : ∀ {Ψ Φ Γ d D c C ps args rs} {k : Nat} {ψ : I} {b T : Tm}, S[d]? = some (.data D) →
    D.ctors[c]? = some C →
    C.bnd[k]? = some (ψ, b) → I.Entails Φ (Ctor.cofAt ψ rs) →
    ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    HasTy0 S Ψ Φ Γ (con d c ps args rs) T →
    HasTy0 S Ψ Φ Γ (Ctor.bndAt b ps.toList args.toList rs) T
  elimCon : ∀ {Ψ Φ Γ d D c C ps P bs b qs args rs T}, S[d]? = some (.data D) →
    D.ctors[c]? = some C → bs.toList[c]? = some b →
    args = Tm.ofList args.toList → bs = Tm.ofList bs.toList →
    HasTy0 S Ψ Φ Γ (elim d ps P bs (con d c qs args rs)) T →
    HasTy0 S Ψ Φ Γ (Tm.papps (Tm.apps b (args.toList ++
      C.recPos.map fun k => elim d ps P bs (args.toList.getD k .abort))) rs) T
  elimHcomp : ∀ {Ψ Φ Γ d D ps P bs qs φ u a T}, S[d]? = some (.data D) →
    HasTy0 S Ψ Φ Γ (elim d ps P bs (hcomp (data d qs) φ u a)) T →
    HasTy0 S Ψ Φ Γ (comp (P.subst (consSub (hfill (data d ps) φ u a)) (fun i => .var (i + 1))) φ
      (elim d ps.dshift P.dshift bs.dshift u) (elim d ps P bs a)) T
  transpCon : ∀ {Ψ Φ Γ d D c C ps φ qs args rs T}, S[d]? = some (.data D) → D.params ≠ [] →
    D.ctors[c]? = some C → ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    HasTy0 S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs)) T →
    HasTy0 S Ψ Φ Γ (con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T
  transpHcomp : ∀ {Ψ Φ Γ d D ps φ qs ψ u a T}, S[d]? = some (.data D) → D.params ≠ [] →
    HasTy0 S Ψ Φ Γ (transp (data d ps) φ (hcomp (data d qs) ψ u a)) T →
    HasTy0 S Ψ Φ Γ (hcomp (data d (ps.dinst .one)) ψ
      (transp ((data d ps).dsubst skip1I) φ.shift u) (transp (data d ps) φ a)) T

section
variable (hS : SigClosed S) (hT : SigTyped0 S) (hC : ContractaTyped S)
include hS hT hC

mutual

theorem pre_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → IsTyp S Ψ Φ Γ A
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 =>
    .inl (lookup_typed hS h0 h1)
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 =>
    .inl ⟨_, (pre_eq h1).2.1⟩
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 =>
    (pre_ty h2).restrict h0 h1
  | @HasTy0.const _ Ψ Φ Γ k t A h0 h1 =>
    .inl ((hT _ _ _ h1).1.elim fun l h => ⟨l, HasTy0.ofEmpty hS h h0⟩)
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 =>
    .inl ⟨_, h0⟩
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
      · exact .inl ⟨l, HasTy0.subst hS (HasTy0.piCod hS h) h1⟩
      · cases h
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 =>
    .inl ⟨_, h0⟩
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
      · exact .inl ⟨l, HasTy0.sigmaDom hS h⟩
      · cases h
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
      · exact .inl ⟨l, HasTy0.subst hS (HasTy0.sigmaCod hS h) (HasTy0.fst h0)⟩
      · cases h
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 =>
    .inl ⟨_, h0⟩
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
      · exact .inl ⟨l, HasTy0.dsubst hS (HasTy0.pathLine hS h) h1⟩
      · cases h
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 =>
    .inl ⟨_, h0⟩
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h⟩
      · exact .inl ⟨l, HasTy0.dsubst hS (HasTy0.ipiLine hS h) h1⟩
      · cases h
  | @HasTy0.split _ Ψ Φ Γ A φ ψ t u l h0 h1 h2 h3 h4 h5 h6 =>
    .inl ⟨_, h3⟩
  | @HasTy0.abort _ Ψ Φ Γ A l h0 h1 =>
    .inl ⟨_, h1⟩
  | @HasTy0.transp _ Ψ Φ Γ A φ a l h0 h1 h2 h3 =>
    .inl ⟨_, HasTy0.dsubst hS h0 trivial⟩
  | @HasTy0.hcomp _ Ψ Φ Γ A φ u a l h0 h1 h2 h3 h4 =>
    .inl ⟨_, h0⟩
  | @HasTy0.glue _ Ψ Φ Γ A φ T e l h0 h1 h2 h3 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 =>
    .inl ⟨_, h0⟩
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 =>
    .inl ⟨_, h1⟩
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 =>
    .inr ⟨_, rfl⟩
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 =>
    .inl ⟨_, h3⟩
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    .inl ⟨_, HasTy0.subst hS h4 h9⟩

theorem pre_eq {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A →
    HasTy0 S Ψ Φ Γ t A ∧ HasTy0 S Ψ Φ Γ u A ∧ IsTyp S Ψ Φ Γ A
  | @EqTm0.refl _ Ψ Φ Γ t A h0 =>
    ⟨h0, h0, pre_ty h0⟩
  | @EqTm0.symm _ Ψ Φ Γ t u A h0 =>
    ⟨(pre_eq h0).2.1, (pre_eq h0).1, (pre_eq h0).2.2⟩
  | @EqTm0.trans _ Ψ Φ Γ t u v A h0 h1 =>
    ⟨(pre_eq h0).1, (pre_eq h1).2.1, (pre_eq h0).2.2⟩
  | @EqTm0.conv _ Ψ Φ Γ t u A B l h0 h1 =>
    ⟨HasTy0.conv (pre_eq h0).1 h1, HasTy0.conv (pre_eq h0).2.1 h1, .inl ⟨_, (pre_eq h1).2.1⟩⟩
  | @EqTm0.restrict _ Ψ Φ Φ' Γ t u A h0 h1 h2 =>
    ⟨HasTy0.restrict h0 h1 (pre_eq h2).1, HasTy0.restrict h0 h1 (pre_eq h2).2.1, (pre_eq h2).2.2.restrict h0 h1⟩
  | @EqTm0.cumul _ Ψ Φ Γ A B l h0 h1 =>
    ⟨HasTy0.cumul h0 (pre_eq h1).1, HasTy0.cumul h0 (pre_eq h1).2.1, .inr ⟨_, rfl⟩⟩
  | @EqTm0.delta _ Ψ Φ Γ k t A h0 h1 =>
    ⟨h0, HasTy0.ofEmpty hS (hT _ _ _ h1).2 (wf_of_ty h0), pre_ty h0⟩
  | @EqTm0.absurd _ Ψ Φ Γ t u A h0 h1 h2 =>
    ⟨h1, h2, pre_ty h1⟩
  | @EqTm0.local _ Ψ Φ Γ φ ψ t u A h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h3, h4, pre_ty h3⟩
  | @EqTm0.face _ Ψ Φ Γ t A i d l h0 h1 h2 h3 =>
    ⟨h3, HasTy0.face_typed hS h0 h1 (.inl ⟨_, h2⟩) h3, .inl ⟨_, h2⟩⟩
  | @EqTm0.faceU _ Ψ Φ Γ t i d l h0 h1 h2 =>
    ⟨h2, HasTy0.face_typed hS h0 h1 (.inr ⟨_, rfl⟩) h2, .inr ⟨_, rfl⟩⟩
  | @EqTm0.pi _ Ψ Φ Γ A A' B B' l h0 h1 =>
    by
      obtain ⟨a, a', _⟩ := pre_eq h0
      obtain ⟨b, b', _⟩ := pre_eq h1
      exact ⟨HasTy0.pi a b, HasTy0.pi a' (HasTy0.ctxConv hS b' a' (EqTm0.symm h0)), .inr ⟨_, rfl⟩⟩
  | @EqTm0.lam _ Ψ Φ Γ A B t t' l h0 h1 =>
    ⟨HasTy0.lam h0 (pre_eq h1).1, HasTy0.lam h0 (pre_eq h1).2.1, .inl ⟨_, h0⟩⟩
  | @EqTm0.app _ Ψ Φ Γ A B f f' a a' h0 h1 =>
    by
      obtain ⟨f, f', hpi⟩ := pre_eq h0
      obtain ⟨a, a', _⟩ := pre_eq h1
      rcases hpi with ⟨l, hpi⟩ | ⟨l, hpi⟩
      · have hB := HasTy0.piCod hS hpi
        exact ⟨HasTy0.app f a, HasTy0.conv (HasTy0.app f' a')
          (EqTm0.symm (HasTy0.inst_congr hS hB a a' h1)), .inl ⟨_, HasTy0.subst hS hB a⟩⟩
      · cases hpi
  | @EqTm0.sigma _ Ψ Φ Γ A A' B B' l h0 h1 =>
    by
      obtain ⟨a, a', _⟩ := pre_eq h0
      obtain ⟨b, b', _⟩ := pre_eq h1
      exact ⟨HasTy0.sigma a b, HasTy0.sigma a' (HasTy0.ctxConv hS b' a' (EqTm0.symm h0)), .inr ⟨_, rfl⟩⟩
  | @EqTm0.pair _ Ψ Φ Γ A B a a' b b' l h0 h1 h2 =>
    by
      obtain ⟨a, a', _⟩ := pre_eq h1
      obtain ⟨b, b', _⟩ := pre_eq h2
      have hB := HasTy0.sigmaCod hS h0
      exact ⟨HasTy0.pair h0 a b, HasTy0.pair h0 a' (HasTy0.conv b' (HasTy0.inst_congr hS hB a a' h1)),
        .inl ⟨_, h0⟩⟩
  | @EqTm0.fst _ Ψ Φ Γ A B p p' h0 =>
    by
      obtain ⟨p, p', hs⟩ := pre_eq h0
      rcases hs with ⟨l, hs⟩ | ⟨l, hs⟩
      · exact ⟨HasTy0.fst p, HasTy0.fst p', .inl ⟨_, HasTy0.sigmaDom hS hs⟩⟩
      · cases hs
  | @EqTm0.snd _ Ψ Φ Γ A B p p' h0 =>
    by
      obtain ⟨p, p', hs⟩ := pre_eq h0
      rcases hs with ⟨l, hs⟩ | ⟨l, hs⟩
      · have hB := HasTy0.sigmaCod hS hs
        exact ⟨HasTy0.snd p, HasTy0.conv (HasTy0.snd p')
          (EqTm0.symm (HasTy0.inst_congr hS hB (HasTy0.fst p) (HasTy0.fst p') (EqTm0.fst h0))),
          .inl ⟨_, HasTy0.subst hS hB (HasTy0.fst p)⟩⟩
      · cases hs
  | @EqTm0.path _ Ψ Φ Γ A A' a a' b b' l h0 h1 h2 =>
    by
      obtain ⟨A, A', _⟩ := pre_eq h0
      obtain ⟨a, a', _⟩ := pre_eq h1
      obtain ⟨b, b', _⟩ := pre_eq h2
      exact ⟨HasTy0.path A a b, HasTy0.path A' (HasTy0.conv a' (EqTm0.dsubst hS h0 trivial))
        (HasTy0.conv b' (EqTm0.dsubst hS h0 trivial)), .inr ⟨_, rfl⟩⟩
  | @EqTm0.plam _ Ψ Φ Γ A a b t t' l h0 h1 h2 h3 =>
    ⟨h1, h2, .inl ⟨_, h0⟩⟩
  | @EqTm0.papp _ Ψ Φ Γ A a b p p' r r' h0 h1 h2 h3 =>
    by
      obtain ⟨p, p', hP⟩ := pre_eq h0
      rcases hP with ⟨l, hP⟩ | ⟨l, hP⟩
      · have hA := HasTy0.pathLine hS hP
        exact ⟨HasTy0.papp p h1, HasTy0.conv (HasTy0.papp p' h2)
          (EqTm0.symm (HasTy0.dinst_congr hS hA h1 h2 h3)), .inl ⟨_, HasTy0.dsubst hS hA h1⟩⟩
      · cases hP
  | @EqTm0.split _ Ψ Φ Γ A φ ψ t t' u u' h0 h1 h2 h3 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.transp _ Ψ Φ Γ A A' φ φ' a a' l h0 h1 h2 h3 h4 h5 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.hcomp _ Ψ Φ Γ A A' φ φ' u u' a a' l h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.glue _ Ψ Φ Γ A A' φ φ' T T' e e' l h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h0, h1, .inr ⟨_, rfl⟩⟩
  | @EqTm0.glueEl _ Ψ Φ Γ φ φ' t t' a a' A T e e' h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.unglue _ Ψ Φ Γ A φ φ' T e e' g g' h0 h1 h2 h3 h4 h5 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.ipi _ Ψ Φ Γ A A' l h0 h1 =>
    ⟨HasTy0.ipi h0 (pre_eq h1).1, HasTy0.ipi h0 (pre_eq h1).2.1, .inr ⟨_, rfl⟩⟩
  | @EqTm0.ilam _ Ψ Φ Γ A t t' l h0 h1 =>
    ⟨HasTy0.ilam h0 (pre_eq h1).1, HasTy0.ilam h0 (pre_eq h1).2.1, .inl ⟨_, h0⟩⟩
  | @EqTm0.iapp _ Ψ Φ Γ A p p' r r' h0 h1 h2 h3 =>
    by
      obtain ⟨p, p', hP⟩ := pre_eq h0
      rcases hP with ⟨l, hP⟩ | ⟨l, hP⟩
      · have hA := HasTy0.ipiLine hS hP
        exact ⟨HasTy0.iapp p h1, HasTy0.conv (HasTy0.iapp p' h2)
          (EqTm0.symm (HasTy0.dinst_congr hS hA h1 h2 h3)), .inl ⟨_, HasTy0.dsubst hS hA h1⟩⟩
      · cases hP
  | @EqTm0.piInjDom _ Ψ Φ Γ A A' B B' l h0 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.piDom hS p, HasTy0.piDom hS p', .inr ⟨_, rfl⟩⟩
  | @EqTm0.piInjCod _ Ψ Φ Γ A A' B B' a l h0 h1 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.subst hS (HasTy0.piCod hS p) h1,
        HasTy0.subst hS (HasTy0.piCod hS p') (HasTy0.conv h1 (EqTm0.piInjDom h0)), .inr ⟨_, rfl⟩⟩
  | @EqTm0.sigmaInjDom _ Ψ Φ Γ A A' B B' l h0 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.sigmaDom hS p, HasTy0.sigmaDom hS p', .inr ⟨_, rfl⟩⟩
  | @EqTm0.sigmaInjCod _ Ψ Φ Γ A A' B B' a l h0 h1 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.subst hS (HasTy0.sigmaCod hS p) h1,
        HasTy0.subst hS (HasTy0.sigmaCod hS p') (HasTy0.conv h1 (EqTm0.sigmaInjDom h0)), .inr ⟨_, rfl⟩⟩
  | @EqTm0.pathInjLine _ Ψ Φ Γ A A' a a' b b' r l h0 h1 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.dsubst hS (HasTy0.pathLine hS p) h1, HasTy0.dsubst hS (HasTy0.pathLine hS p') h1, .inr ⟨_, rfl⟩⟩
  | @EqTm0.pathInjLeft _ Ψ Φ Γ A A' a a' b b' l h0 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.pathLeft hS p, HasTy0.conv (HasTy0.pathLeft hS p')
        (EqTm0.symm (EqTm0.pathInjLine h0 (r := .zero) trivial)),
        .inl ⟨_, HasTy0.dsubst hS (HasTy0.pathLine hS p) trivial⟩⟩
  | @EqTm0.pathInjRight _ Ψ Φ Γ A A' a a' b b' l h0 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.pathRight hS p, HasTy0.conv (HasTy0.pathRight hS p')
        (EqTm0.symm (EqTm0.pathInjLine h0 (r := .one) trivial)),
        .inl ⟨_, HasTy0.dsubst hS (HasTy0.pathLine hS p) trivial⟩⟩
  | @EqTm0.ipiInj _ Ψ Φ Γ A A' r l h0 h1 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.dsubst hS (HasTy0.ipiLine hS p) h1, HasTy0.dsubst hS (HasTy0.ipiLine hS p') h1, .inr ⟨_, rfl⟩⟩
  | @EqTm0.noConf _ Ψ Φ Γ X Y l t u T h0 h1 h2 h3 =>
    ⟨h2, h3, pre_ty h2⟩
  | @EqTm0.piBeta _ Ψ Φ Γ A t a T h0 =>
    ⟨h0, hC.piBeta h0, pre_ty h0⟩
  | @EqTm0.piEta _ Ψ Φ Γ A B f h0 =>
    by
      rcases pre_ty h0 with ⟨l, hpi⟩ | ⟨l, hpi⟩
      · have hA := HasTy0.piDom hS hpi
        have hw := HasTy0.wk hS hA h0
        have hv : HasTy0 S Ψ Φ (A :: Γ) (var 0) A.shift := HasTy0.var (Wf0.cons hA) rfl
        simp only [Tm.shift, Tm.ren] at hw
        have happ := HasTy0.app hw hv
        rw [upShift_inst0] at happ
        exact ⟨h0, HasTy0.lam hpi happ, .inl ⟨_, hpi⟩⟩
      · cases hpi
  | @EqTm0.fstBeta _ Ψ Φ Γ a b T h0 =>
    ⟨h0, hC.fstBeta h0, pre_ty h0⟩
  | @EqTm0.sndBeta _ Ψ Φ Γ a b T h0 =>
    ⟨h0, hC.sndBeta h0, pre_ty h0⟩
  | @EqTm0.sigmaEta _ Ψ Φ Γ A B p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hs⟩ | ⟨l, hs⟩
      · exact ⟨h0, HasTy0.pair hs (HasTy0.fst h0) (HasTy0.snd h0), .inl ⟨_, hs⟩⟩
      · cases hs
  | @EqTm0.pathBeta _ Ψ Φ Γ t r T h0 =>
    ⟨h0, hC.pathBeta h0, pre_ty h0⟩
  | @EqTm0.pathEta _ Ψ Φ Γ A a b p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP⟩
      · have hw := HasTy0.dwk hS h0
        simp only [Tm.dshift, Tm.ren] at hw
        have hb := HasTy0.papp hw (r := .var 0) (show (0 : Nat) < Ψ + 1 by omega)
        rw [upDShift_dinst0] at hb
        have e0 : (papp p.dshift (.var 0)).dinst .zero = papp p .zero := by
          change Tm.papp (p.dshift.dinst .zero) ((I.var 0).subst (I.inst0 .zero)) = _
          rw [dshift_dinst]; rfl
        have e1 : (papp p.dshift (.var 0)).dinst .one = papp p .one := by
          change Tm.papp (p.dshift.dinst .one) ((I.var 0).subst (I.inst0 .one)) = _
          rw [dshift_dinst]; rfl
        refine ⟨h0, HasTy0.plam hP hb ?_ ?_, .inl ⟨_, hP⟩⟩
        · rw [e0]; exact EqTm0.pathZero h0
        · rw [e1]; exact EqTm0.pathOne h0
      · cases hP
  | @EqTm0.ipiEta _ Ψ Φ Γ A p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP⟩
      · have hw := HasTy0.dwk hS h0
        simp only [Tm.dshift, Tm.ren] at hw
        have hb := HasTy0.iapp hw (r := .var 0) (show (0 : Nat) < Ψ + 1 by omega)
        rw [upDShift_dinst0] at hb
        exact ⟨h0, HasTy0.ilam hP hb, .inl ⟨_, hP⟩⟩
      · cases hP
  | @EqTm0.pathZero _ Ψ Φ Γ A a b p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP⟩
      · exact ⟨HasTy0.papp h0 trivial, HasTy0.pathLeft hS hP, .inl ⟨_, HasTy0.dsubst hS (HasTy0.pathLine hS hP) trivial⟩⟩
      · cases hP
  | @EqTm0.pathOne _ Ψ Φ Γ A a b p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP⟩
      · exact ⟨HasTy0.papp h0 trivial, HasTy0.pathRight hS hP, .inl ⟨_, HasTy0.dsubst hS (HasTy0.pathLine hS hP) trivial⟩⟩
      · cases hP
  | @EqTm0.splitL _ Ψ Φ Γ φ ψ t u T h0 h1 =>
    by
      obtain ⟨A', ⟨hφ, _, _, ht, _⟩, ch⟩ := gen_split h1 rfl
      have hs := scoped_of_ty h1
      exact ⟨h1, ch.transport (HasTy0.restrict hs (ent_and_intro (ent_refl _) h0) ht), pre_ty h1⟩
  | @EqTm0.splitR _ Ψ Φ Γ φ ψ t u T h0 h1 =>
    by
      obtain ⟨A', ⟨_, hψ, _, _, hu⟩, ch⟩ := gen_split h1 rfl
      have hs := scoped_of_ty h1
      exact ⟨h1, ch.transport (HasTy0.restrict hs (ent_and_intro (ent_refl _) h0) hu), pre_ty h1⟩
  | @EqTm0.transpFace _ Ψ Φ Γ A φ a T h0 h1 =>
    by
      obtain ⟨l, ⟨hA, hφ, hc, ha⟩, ch⟩ := gen_transpF h1 rfl
      have hs := scoped_of_ty h1
      have hc' := EqTm0.restrict (scoped_shift hs) (ent_shift (ent_and_intro (ent_refl _) h0)) hc
      have hc1 := EqTm0.dsubst hS hc' (r := .one) trivial
      rw [dshift_dinst] at hc1
      exact ⟨h1, ch.transport (HasTy0.conv ha (EqTm0.symm hc1)), pre_ty h1⟩
  | @EqTm0.hcompFace _ Ψ Φ Γ A φ u a T h0 h1 =>
    by
      obtain ⟨l, ⟨hA, hφ, hu, ha, _⟩, ch⟩ := gen_hcomp h1 rfl
      have hs := scoped_of_ty h1
      have hu1 := HasTy0.dsubst hS hu (r := .one) trivial
      rw [dshift_dinst] at hu1
      exact ⟨h1, ch.transport (HasTy0.restrict hs (ent_and_intro (ent_refl _) h0) hu1), pre_ty h1⟩
  | @EqTm0.transpU _ Ψ Φ Γ l φ a T h0 =>
    by
      obtain ⟨l, ⟨_, _, _, ha⟩, ch⟩ := gen_transpF h0 rfl
      exact ⟨h0, ch.transport ha, pre_ty h0⟩
  | @EqTm0.transpPi _ Ψ Φ Γ A B φ u0 T h0 =>
    ⟨h0, hC.transpPi h0, pre_ty h0⟩
  | @EqTm0.transpSigma _ Ψ Φ Γ A B φ u0 T h0 =>
    ⟨h0, hC.transpSigma h0, pre_ty h0⟩
  | @EqTm0.transpPath _ Ψ Φ Γ A a b φ p0 T h0 =>
    ⟨h0, hC.transpPath h0, pre_ty h0⟩
  | @EqTm0.transpGlue _ Ψ Φ Γ A φ T' e ψ u0 T l δ h0 h1 h2 h3 h4 =>
    ⟨h0, hC.transpGlue h0 h1 h2 h3 h4, pre_ty h0⟩
  | @EqTm0.transpIPi _ Ψ Φ Γ A φ u0 T h0 =>
    ⟨h0, hC.transpIPi h0, pre_ty h0⟩
  | @EqTm0.hcompIPi _ Ψ Φ Γ A φ u u0 T h0 =>
    ⟨h0, hcompIPi_typed hS h0, pre_ty h0⟩
  | @EqTm0.hcompPi _ Ψ Φ Γ A B φ u u0 T h0 =>
    ⟨h0, hcompPi_typed hS h0, pre_ty h0⟩
  | @EqTm0.hcompSigma _ Ψ Φ Γ A B φ u u0 T h0 =>
    ⟨h0, hcompSigma_typed hS h0, pre_ty h0⟩
  | @EqTm0.hcompPath _ Ψ Φ Γ A a b φ u p0 T h0 =>
    ⟨h0, hcompPath_typed hS h0, pre_ty h0⟩
  | @EqTm0.hcompGlue _ Ψ Φ Γ A φ T' e ψ u u0 T l h0 h1 h2 =>
    ⟨h0, hcompGlue_typed hS h0, pre_ty h0⟩
  | @EqTm0.hcompU _ Ψ Φ Γ φ u u0 T l h0 =>
    ⟨h0, hcompU_typed hS h0, pre_ty h0⟩
  | @EqTm0.glueFace _ Ψ Φ Γ A φ T e G h0 h1 =>
    by
      obtain ⟨l, ⟨_, hφ, hT', _⟩, ch⟩ := gen_glue hS h1 rfl
      have hs := scoped_of_ty h1
      exact ⟨h1, ch.transport (HasTy0.restrict hs (ent_and_intro (ent_refl _) h0) hT'), pre_ty h1⟩
  | @EqTm0.glueElFace _ Ψ Φ Γ φ e t a G h0 h1 =>
    by
      obtain ⟨A', T', l, ⟨hg, _, ht, _⟩, ch⟩ := gen_glueEl h1 rfl
      have hs := scoped_of_ty h1
      have ht' := HasTy0.restrict hs (ent_and_intro (ent_refl _) h0) ht
      exact ⟨h1, ch.transport (HasTy0.conv ht' (EqTm0.symm (EqTm0.glueFace h0 hg))), pre_ty h1⟩
  | @EqTm0.unglueFace _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 =>
    by
      rcases pre_ty h1 with ⟨l', hG⟩ | ⟨l', hG⟩
      · have hs := scoped_of_ty h1
        obtain ⟨l0, ⟨hA0, hφ, _, _⟩, chg⟩ := gen_glue hS hG rfl
        have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
        have hu := HasTy0.unglue hG (chg.transport hA0) (HasTy0.restrict hs' (ent_and_left _ _) h3) h1
        have hgT := HasTy0.conv h1 (EqTm0.glueFace h0 hG)
        have hf := HasTy0.fst h3
        simp only [equiv, arrow] at hf
        have happ := HasTy0.app hf hgT
        rw [shift_inst] at happ
        exact ⟨hu, happ, .inl ⟨_, h2⟩⟩
      · cases hG
  | @EqTm0.glueBeta _ Ψ Φ Γ φ e t a G h0 h1 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.glueEta _ Ψ Φ Γ A φ T e g h0 =>
    by
      rcases pre_ty h0 with ⟨l, hG⟩ | ⟨l, hG⟩
      · obtain ⟨l0, ⟨hA, hφ, hT', he⟩, ch⟩ := gen_glue hS hG rfl
        have hs := scoped_of_ty h0
        have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
        have hA' := ch.transport hA
        have hgc := HasTy0.restrict hs' (ent_and_left _ _) h0
        have hGc := HasTy0.restrict hs' (ent_and_left _ _) hG
        have hgT := HasTy0.conv hgc (EqTm0.glueFace (ent_and_right _ _) hGc)
        have hu := HasTy0.unglue hG hA' he h0
        have hAc := HasTy0.restrict hs' (ent_and_left _ _) hA'
        have heq := EqTm0.unglueFace (ent_and_right _ _) hgc hAc he
        have hu' := HasTy0.restrict hs' (ent_and_left _ _) hu
        exact ⟨h0, HasTy0.glueEl hG he hgT hu (EqTm0.symm heq), .inl ⟨_, hG⟩⟩
      · cases hG
  | @EqTm0.data _ Ψ Φ Γ d D ps ps' h0 h1 h2 h3 =>
    ⟨h1, h2, .inr ⟨_, rfl⟩⟩
  | @EqTm0.con _ Ψ Φ Γ d D c C ps ps' args args' rs rs' h0 h1 h2 h3 h4 h5 h6 h7 =>
    ⟨h2, h3, pre_ty h2⟩
  | @EqTm0.elim _ Ψ Φ Γ d D ps ps' P P' bs bs' t t' m h0 h1 h2 h3 h4 h5 h6 h7 =>
    ⟨h1, h2, pre_ty h1⟩
  | @EqTm0.conBnd _ Ψ Φ Γ d D c C ps args rs k ψ b T h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h6, hC.conBnd h0 h1 h2 h3 h4 h5 h6, pre_ty h6⟩
  | @EqTm0.elimCon _ Ψ Φ Γ d D c C ps P bs b qs args rs T h0 h1 h2 h3 h4 h5 =>
    ⟨h5, hC.elimCon h0 h1 h2 h3 h4 h5, pre_ty h5⟩
  | @EqTm0.elimHcomp _ Ψ Φ Γ d D ps P bs qs φ u a T h0 h1 =>
    ⟨h1, hC.elimHcomp h0 h1, pre_ty h1⟩
  | @EqTm0.transpData0 _ Ψ Φ Γ d D ps φ a T h0 h1 h2 =>
    by
      have hv := pre_ty h2
      obtain ⟨l, ⟨hL, _, _, ha⟩, ch⟩ := gen_transpF h2 rfl
      obtain ⟨D', hD', htele⟩ := gen_data_tele hL rfl
      rw [h0] at hD'; cases hD'
      rw [h1] at htele
      cases htele
      exact ⟨h2, ch.transport ha, hv⟩
  | @EqTm0.transpCon _ Ψ Φ Γ d D c C ps φ qs args rs T h0 h1 h2 h3 h4 h5 =>
    ⟨h5, hC.transpCon h0 h1 h2 h3 h4 h5, pre_ty h5⟩
  | @EqTm0.transpHcomp _ Ψ Φ Γ d D ps φ qs ψ u a T h0 h1 h2 =>
    ⟨h2, hC.transpHcomp h0 h1 h2, pre_ty h2⟩
end

/-- Presupposition for the minimal judgments, given `ContractaTyped`. -/
theorem presup0 : Presup0 S := fun h => ⟨(pre_eq hS hT hC h).1, (pre_eq hS hT hC h).2.1⟩

end

end KubusCore.Meta
