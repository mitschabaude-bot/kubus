import KubusCore.Meta.BetaTyped
import KubusCore.Meta.KanTransp
import KubusCore.Meta.KanTranspGlue
import KubusCore.Meta.DataContracta

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
  conBnd : ∀ {Ψ Φ Γ d D c C ps args rs} {k : Nat} {ψ : I} {b T : Tm}, S[d]? = some (.data D) →
    D.ctors[c]? = some C →
    C.bnd[k]? = some (ψ, b) → I.Entails Φ (Ctor.cofAt ψ rs) →
    ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    HasTy0 S Ψ Φ Γ (con d c ps args rs) T →
    HasTy0 S Ψ Φ Γ (Ctor.bndAt b ps.toList args.toList rs) T
  hcompCon : ∀ {Ψ Φ Γ d D c C ps φ u qs uargs args T}, S[d]? = some (.data D) → D.isHIT = false →
    D.ctors[c]? = some C → ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    uargs = Tm.ofList uargs.toList →
    HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse →
    HasTele0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse →
    EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (con d c ps.dshift uargs []) (data d ps.dshift) →
    EqTele0 S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse →
    HasTy0 S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args [])) T →
    HasTy0 S Ψ Φ Γ (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d ps)
      ps.dshift.toList φ 0 [] uargs.toList args.toList)) []) T
  transpCon : ∀ {Ψ Φ Γ d D c C ps φ qs args rs l0 X l T}, S[d]? = some (.data D) → D.params ≠ [] →
    D.ctors[c]? = some C → ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
    HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse →
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (data d ps) (univ l0) → φ.Scoped Ψ →
    EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (data d ps) ((data d ps).dinst .zero).dshift (univ l0) →
    IntroTy S Ψ Φ Γ (con d c qs args rs) X → HasTy0 S Ψ Φ Γ X (univ l) → l ≤ maxLevel →
    Rel S Ψ Φ Γ X ((data d ps).dinst .zero) → TB S Ψ Φ Γ ((data d ps).dinst .zero) →
    TyChainC S Ψ Φ Γ ((data d ps).dinst .one) T →
    HasTy0 S Ψ Φ Γ (con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T

section
variable (hS : SigClosed S) (hT : SigTyped0 S) (hC : ContractaTyped S)
include hS hT hC

set_option maxHeartbeats 4000000

mutual

theorem pre_ty {Ψ Φ Γ t A} : HasTy0 S Ψ Φ Γ t A → IsTypB S Ψ Φ Γ A
  | @HasTy0.var _ Ψ Φ Γ x A h0 h1 =>
    .inl (lookup_typed hS h0 h1)
  | @HasTy0.conv _ Ψ Φ Γ t A B l h0 h1 =>
    .inl ⟨_, (pre_eq h1).2.1⟩
  | @HasTy0.restrict _ Ψ Φ Φ' Γ t A h0 h1 h2 =>
    (pre_ty h2).restrict h0 h1
  | @HasTy0.const _ Ψ Φ Γ k t A h0 h1 =>
    .inl ((hT _ _ _ h1).1.elim fun l h => ⟨l, HasTy0.ofEmpty hS h h0⟩)
  | @HasTy0.univ _ Ψ Φ Γ l h0 h1 =>
    .inr ⟨_, rfl, h0⟩
  | @HasTy0.cumul _ Ψ Φ Γ A l h0 h1 =>
    .inr ⟨_, rfl, h0⟩
  | @HasTy0.pi _ Ψ Φ Γ A B l h0 h1 =>
    .inr ⟨_, rfl, (pre_ty h0).lvl⟩
  | @HasTy0.lam _ Ψ Φ Γ A B t l h0 h1 =>
    .inl ⟨_, h0⟩
  | @HasTy0.app _ Ψ Φ Γ A B f a h0 h1 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h, -⟩
      · exact .inl ⟨l, HasTy0.subst hS (HasTy0.piCod hS h) h1⟩
      · cases h
  | @HasTy0.sigma _ Ψ Φ Γ A B l h0 h1 =>
    .inr ⟨_, rfl, (pre_ty h0).lvl⟩
  | @HasTy0.pair _ Ψ Φ Γ A B a b l h0 h1 h2 =>
    .inl ⟨_, h0⟩
  | @HasTy0.fst _ Ψ Φ Γ A B p h0 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h, -⟩
      · exact .inl ⟨l, HasTy0.sigmaDom hS h⟩
      · cases h
  | @HasTy0.snd _ Ψ Φ Γ A B p h0 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h, -⟩
      · exact .inl ⟨l, HasTy0.subst hS (HasTy0.sigmaCod hS h) (HasTy0.fst h0)⟩
      · cases h
  | @HasTy0.path _ Ψ Φ Γ A a b l h0 h1 h2 =>
    .inr ⟨_, rfl, (pre_ty h0).lvl⟩
  | @HasTy0.plam _ Ψ Φ Γ A a b t l h0 h1 h2 h3 =>
    .inl ⟨_, h0⟩
  | @HasTy0.papp _ Ψ Φ Γ A a b p r h0 h1 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h, -⟩
      · exact .inl ⟨l, HasTy0.dsubst hS (HasTy0.pathLine hS h) h1⟩
      · cases h
  | @HasTy0.ipi _ Ψ Φ Γ A l h0 h1 =>
    .inr ⟨_, rfl, (pre_ty h1).lvl⟩
  | @HasTy0.ilam _ Ψ Φ Γ A t l h0 h1 =>
    .inl ⟨_, h0⟩
  | @HasTy0.iapp _ Ψ Φ Γ A p r h0 h1 =>
    by
      rcases pre_ty h0 with ⟨l, h⟩ | ⟨l, h, -⟩
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
    .inr ⟨_, rfl, (pre_ty h0).lvl⟩
  | @HasTy0.glueEl _ Ψ Φ Γ A φ T e t a l h0 h1 h2 h3 h4 =>
    .inl ⟨_, h0⟩
  | @HasTy0.unglue _ Ψ Φ Γ A φ T e g l h0 h1 h2 h3 =>
    .inl ⟨_, h1⟩
  | @HasTy0.data _ Ψ Φ Γ d D ps h0 h1 h2 =>
    .inr ⟨_, rfl, Nat.le_of_succ_le h1⟩
  | @HasTy0.con _ Ψ Φ Γ d D c C ps args rs h0 h1 h2 h3 h4 h5 h6 h7 =>
    .inl ⟨_, h3⟩
  | @HasTy0.elim _ Ψ Φ Γ d D ps P bs t m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    .inl ⟨_, HasTy0.subst hS h4 h9⟩

theorem pre_eq {Ψ Φ Γ t u A} : EqTm0 S Ψ Φ Γ t u A →
    HasTy0 S Ψ Φ Γ t A ∧ HasTy0 S Ψ Φ Γ u A ∧ IsTypB S Ψ Φ Γ A
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
    ⟨HasTy0.cumul h0 (pre_eq h1).1, HasTy0.cumul h0 (pre_eq h1).2.1, .inr ⟨_, rfl, h0⟩⟩
  | @EqTm0.delta _ Ψ Φ Γ k t A h0 h1 =>
    ⟨h0, HasTy0.ofEmpty hS (hT _ _ _ h1).2 (wf_of_ty h0), pre_ty h0⟩
  | @EqTm0.absurd _ Ψ Φ Γ t u A h0 h1 h2 =>
    ⟨h1, h2, pre_ty h1⟩
  | @EqTm0.local _ Ψ Φ Γ φ ψ t u A h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h3, h4, pre_ty h3⟩
  | @EqTm0.face _ Ψ Φ Γ t A i d l h0 h1 h2 h3 =>
    ⟨h3, HasTy0.face_typed hS h0 h1 (.inl ⟨_, h2⟩) h3, .inl ⟨_, h2⟩⟩
  | @EqTm0.faceU _ Ψ Φ Γ t i d l h0 h1 h2 =>
    ⟨h2, HasTy0.face_typed hS h0 h1 (.inr ⟨_, rfl⟩) h2, pre_ty h2⟩
  | @EqTm0.pi _ Ψ Φ Γ A A' B B' l h0 h1 =>
    by
      obtain ⟨a, a', _⟩ := pre_eq h0
      obtain ⟨b, b', _⟩ := pre_eq h1
      exact ⟨HasTy0.pi a b, HasTy0.pi a' (HasTy0.ctxConv hS b' a' (EqTm0.symm h0)), (pre_eq h0).2.2⟩
  | @EqTm0.lam _ Ψ Φ Γ A B t t' l h0 h1 =>
    ⟨HasTy0.lam h0 (pre_eq h1).1, HasTy0.lam h0 (pre_eq h1).2.1, .inl ⟨_, h0⟩⟩
  | @EqTm0.app _ Ψ Φ Γ A B f f' a a' h0 h1 =>
    by
      obtain ⟨f, f', hpi⟩ := pre_eq h0
      obtain ⟨a, a', _⟩ := pre_eq h1
      rcases hpi with ⟨l, hpi⟩ | ⟨l, hpi, -⟩
      · have hB := HasTy0.piCod hS hpi
        exact ⟨HasTy0.app f a, HasTy0.conv (HasTy0.app f' a')
          (EqTm0.symm (HasTy0.inst_congr hS hB a a' h1)), .inl ⟨_, HasTy0.subst hS hB a⟩⟩
      · cases hpi
  | @EqTm0.sigma _ Ψ Φ Γ A A' B B' l h0 h1 =>
    by
      obtain ⟨a, a', _⟩ := pre_eq h0
      obtain ⟨b, b', _⟩ := pre_eq h1
      exact ⟨HasTy0.sigma a b, HasTy0.sigma a' (HasTy0.ctxConv hS b' a' (EqTm0.symm h0)), (pre_eq h0).2.2⟩
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
      rcases hs with ⟨l, hs⟩ | ⟨l, hs, -⟩
      · exact ⟨HasTy0.fst p, HasTy0.fst p', .inl ⟨_, HasTy0.sigmaDom hS hs⟩⟩
      · cases hs
  | @EqTm0.snd _ Ψ Φ Γ A B p p' h0 =>
    by
      obtain ⟨p, p', hs⟩ := pre_eq h0
      rcases hs with ⟨l, hs⟩ | ⟨l, hs, -⟩
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
        (HasTy0.conv b' (EqTm0.dsubst hS h0 trivial)), .inr ⟨_, rfl, (pre_eq h0).2.2.lvl⟩⟩
  | @EqTm0.plam _ Ψ Φ Γ A a b t t' l h0 h1 h2 h3 =>
    ⟨h1, h2, .inl ⟨_, h0⟩⟩
  | @EqTm0.papp _ Ψ Φ Γ A a b p p' r r' h0 h1 h2 h3 =>
    by
      obtain ⟨p, p', hP⟩ := pre_eq h0
      rcases hP with ⟨l, hP⟩ | ⟨l, hP, -⟩
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
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.glueEl _ Ψ Φ Γ φ φ' t t' a a' A T e e' h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.unglue _ Ψ Φ Γ A φ φ' T e e' g g' h0 h1 h2 h3 h4 h5 =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.ipi _ Ψ Φ Γ A A' l h0 h1 =>
    ⟨HasTy0.ipi h0 (pre_eq h1).1, HasTy0.ipi h0 (pre_eq h1).2.1, .inr ⟨_, rfl, (pre_eq h1).2.2.lvl⟩⟩
  | @EqTm0.ilam _ Ψ Φ Γ A t t' l h0 h1 =>
    ⟨HasTy0.ilam h0 (pre_eq h1).1, HasTy0.ilam h0 (pre_eq h1).2.1, .inl ⟨_, h0⟩⟩
  | @EqTm0.iapp _ Ψ Φ Γ A p p' r r' h0 h1 h2 h3 =>
    by
      obtain ⟨p, p', hP⟩ := pre_eq h0
      rcases hP with ⟨l, hP⟩ | ⟨l, hP, -⟩
      · have hA := HasTy0.ipiLine hS hP
        exact ⟨HasTy0.iapp p h1, HasTy0.conv (HasTy0.iapp p' h2)
          (EqTm0.symm (HasTy0.dinst_congr hS hA h1 h2 h3)), .inl ⟨_, HasTy0.dsubst hS hA h1⟩⟩
      · cases hP
  | @EqTm0.piInjDom _ Ψ Φ Γ A A' B B' l h0 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.piDom hS p, HasTy0.piDom hS p', (pre_eq h0).2.2⟩
  | @EqTm0.piInjCod _ Ψ Φ Γ A A' B B' a l h0 h1 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.subst hS (HasTy0.piCod hS p) h1,
        HasTy0.subst hS (HasTy0.piCod hS p') (HasTy0.conv h1 (EqTm0.piInjDom h0)), (pre_eq h0).2.2⟩
  | @EqTm0.sigmaInjDom _ Ψ Φ Γ A A' B B' l h0 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.sigmaDom hS p, HasTy0.sigmaDom hS p', (pre_eq h0).2.2⟩
  | @EqTm0.sigmaInjCod _ Ψ Φ Γ A A' B B' a l h0 h1 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.subst hS (HasTy0.sigmaCod hS p) h1,
        HasTy0.subst hS (HasTy0.sigmaCod hS p') (HasTy0.conv h1 (EqTm0.sigmaInjDom h0)), (pre_eq h0).2.2⟩
  | @EqTm0.pathInjLine _ Ψ Φ Γ A A' a a' b b' r l h0 h1 =>
    by
      obtain ⟨p, p', _⟩ := pre_eq h0
      exact ⟨HasTy0.dsubst hS (HasTy0.pathLine hS p) h1, HasTy0.dsubst hS (HasTy0.pathLine hS p') h1, (pre_eq h0).2.2⟩
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
      exact ⟨HasTy0.dsubst hS (HasTy0.ipiLine hS p) h1, HasTy0.dsubst hS (HasTy0.ipiLine hS p') h1, (pre_eq h0).2.2⟩
  | @EqTm0.dataInjAt _ Ψ Φ Γ d D ps ps' l k p p' A h0 h1 h2 h3 h4 h5 h6 h7 h8 =>
    ⟨h7, h8, pre_ty h7⟩
  | @EqTm0.noConf _ Ψ Φ Γ X Y l t u T h0 h1 h2 h3 =>
    ⟨h2, h3, pre_ty h2⟩
  | @EqTm0.piBeta _ Ψ Φ Γ A t a T h0 =>
    by
      obtain ⟨A1, B1, X, l, ha, hI, hX, hl, r, tb, ch⟩ := genApp h0 rfl rfl
      exact ⟨h0, piBeta_of hS hI hX hl r tb ha ch, pre_ty h0⟩
  | @EqTm0.piEta _ Ψ Φ Γ A B f h0 =>
    by
      rcases pre_ty h0 with ⟨l, hpi⟩ | ⟨l, hpi, -⟩
      · have hA := HasTy0.piDom hS hpi
        have hw := HasTy0.wk hS hA h0
        have hv : HasTy0 S Ψ Φ (A :: Γ) (var 0) A.shift := HasTy0.var (Wf0.cons hA) rfl
        simp only [Tm.shift, Tm.ren] at hw
        have happ := HasTy0.app hw hv
        rw [upShift_inst0] at happ
        exact ⟨h0, HasTy0.lam hpi happ, .inl ⟨_, hpi⟩⟩
      · cases hpi
  | @EqTm0.fstBeta _ Ψ Φ Γ a b T h0 =>
    by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genFst h0 rfl rfl
      exact ⟨h0, fstBeta_of hI hX hl r tb ch, pre_ty h0⟩
  | @EqTm0.sndBeta _ Ψ Φ Γ a b T h0 =>
    by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genSnd h0 rfl rfl
      exact ⟨h0, sndBeta_of hS hI hX hl r tb ch, pre_ty h0⟩
  | @EqTm0.sigmaEta _ Ψ Φ Γ A B p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hs⟩ | ⟨l, hs, -⟩
      · exact ⟨h0, HasTy0.pair hs (HasTy0.fst h0) (HasTy0.snd h0), .inl ⟨_, hs⟩⟩
      · cases hs
  | @EqTm0.pathBeta _ Ψ Φ Γ t r T h0 =>
    by
      obtain ⟨Y, A1, X, l, hY, hr, hI, hX, hl, r, tb, ch⟩ := genPapp h0 rfl rfl
      exact ⟨h0, pathBeta_of hS hI hX hl hY hr r tb ch, pre_ty h0⟩
  | @EqTm0.pathEta _ Ψ Φ Γ A a b p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP, -⟩
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
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP, -⟩
      · have hw := HasTy0.dwk hS h0
        simp only [Tm.dshift, Tm.ren] at hw
        have hb := HasTy0.iapp hw (r := .var 0) (show (0 : Nat) < Ψ + 1 by omega)
        rw [upDShift_dinst0] at hb
        exact ⟨h0, HasTy0.ilam hP hb, .inl ⟨_, hP⟩⟩
      · cases hP
  | @EqTm0.pathZero _ Ψ Φ Γ A a b p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP, -⟩
      · exact ⟨HasTy0.papp h0 trivial, HasTy0.pathLeft hS hP, .inl ⟨_, HasTy0.dsubst hS (HasTy0.pathLine hS hP) trivial⟩⟩
      · cases hP
  | @EqTm0.pathOne _ Ψ Φ Γ A a b p h0 =>
    by
      rcases pre_ty h0 with ⟨l, hP⟩ | ⟨l, hP, -⟩
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
    ⟨h0, transpPi_typed hS h0, pre_ty h0⟩
  | @EqTm0.transpSigma _ Ψ Φ Γ A B φ u0 T h0 =>
    ⟨h0, transpSigma_typed hS h0, pre_ty h0⟩
  | @EqTm0.transpPath _ Ψ Φ Γ A a b φ p0 T h0 =>
    ⟨h0, transpPath_typed hS h0, pre_ty h0⟩
  | @EqTm0.transpGlue _ Ψ Φ Γ A φ T' e ψ u0 T l δ h0 h1 h2 h3 h4 h5 =>
    ⟨h0, transpGlue_typed hS h0 h4 h3, pre_ty h0⟩
  | @EqTm0.transpIPi _ Ψ Φ Γ A φ u0 T h0 =>
    ⟨h0, transpIPi_typed hS h0, pre_ty h0⟩
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
      rcases pre_ty h1 with ⟨l', hG⟩ | ⟨l', hG, -⟩
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
  | @EqTm0.glueBeta _ Ψ Φ Γ φ e t a G h0 h1 _ =>
    ⟨h0, h1, pre_ty h0⟩
  | @EqTm0.glueEta _ Ψ Φ Γ A φ T e g h0 =>
    by
      rcases pre_ty h0 with ⟨l, hG⟩ | ⟨l, hG, -⟩
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
    ⟨h1, h2, pre_ty h1⟩
  | @EqTm0.con _ Ψ Φ Γ d D c C ps ps' args args' rs rs' h0 h1 h2 h3 h4 h5 h6 h7 =>
    ⟨h2, h3, pre_ty h2⟩
  | @EqTm0.elim _ Ψ Φ Γ d D ps ps' P P' bs bs' t t' m h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    ⟨h1, h2, pre_ty h1⟩
  | @EqTm0.conBnd _ Ψ Φ Γ d D c C ps args rs k ψ b T h0 h1 h2 h3 h4 h5 h6 =>
    ⟨h6, hC.conBnd h0 h1 h2 h3 h4 h5 h6, pre_ty h6⟩
  | @EqTm0.elimCon _ Ψ Φ Γ d D c C ps P bs b qs args rs T h0 h1 h2 h3 h4 h5 h6 h7 =>
    by
      obtain ⟨D', m, X, l, hE, hI, hX, hl, r, tb, ch⟩ := genElim h7 rfl rfl
      exact ⟨h7, elimCon_of hS h0 h1 h2 h3 h4 h5 h6 hE hI hX hl r tb ch, pre_ty h7⟩
  | @EqTm0.elimHcomp _ Ψ Φ Γ d D ps P bs qs φ u a T h0 h1 h2 h3 =>
    by
      obtain ⟨D', m, X, l, hE, hI, hX, hl, r, tb, ch⟩ := genElim h3 rfl rfl
      exact ⟨h3, elimHcomp_of hS h0 h2 hE hI hX hl r tb ch, pre_ty h3⟩
  | @EqTm0.hcompCon _ Ψ Φ Γ d D c C ps φ u qs uargs args T h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    ⟨h10, hC.hcompCon h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, pre_ty h10⟩
  | @EqTm0.transpData0 _ Ψ Φ Γ d D ps φ a T h0 h1 h2 =>
    by
      have hv := pre_ty h2
      obtain ⟨l, ⟨hL, _, _, ha⟩, ch⟩ := gen_transpF h2 rfl
      obtain ⟨D', hD', htele⟩ := gen_data_tele hL rfl
      rw [h0] at hD'; cases hD'
      rw [h1] at htele
      cases htele
      exact ⟨h2, ch.transport ha, hv⟩
  | @EqTm0.transpCon _ Ψ Φ Γ d D c C ps φ qs args rs T h0 h1 h2 h3 h4 h5 h6 =>
    by
      obtain ⟨l0, X, l, hL, hφ, hc, hI, hX, hl, r, tb, ch⟩ := genTransp h6 rfl rfl
      exact ⟨h6, hC.transpCon h0 h1 h2 h3 h4 h5 hL hφ hc hI hX hl r tb ch, pre_ty h6⟩
  | @EqTm0.transpHcomp _ Ψ Φ Γ d D ps φ qs ψ u a T h0 h1 h2 h3 h4 =>
    by
      obtain ⟨l0, X, l, hL, hφ, hc, hI, hX, hl, r, tb, ch⟩ := genTransp h4 rfl rfl
      exact ⟨h4, transpHcomp_of hS h0 h1 h3 hL hφ hc hI hX hl r tb ch, pre_ty h4⟩

theorem genI {Ψ Φ Γ s T} : HasTy0 S Ψ Φ Γ s T → isIntro s = true →
    ∃ X l, IntroTy S Ψ Φ Γ s X ∧ HasTy0 S Ψ Φ Γ X (univ l) ∧ l ≤ maxLevel ∧ Rel S Ψ Φ Γ X T ∧
      TB S Ψ Φ Γ T
  | .var h0 h1, hs => by simp [isIntro] at hs
  | .conv h0 h1, hs => by
      obtain ⟨X, l', hI, hX, hl, r, _⟩ := genI h0 hs
      exact ⟨X, l', hI, hX, hl, r.conv h1 (pre_eq h1).2.2.lvl, .inl ⟨_, (pre_eq h1).2.2.lvl, (pre_eq h1).2.1⟩⟩
  | .restrict h0 h1 h2, hs => by
      obtain ⟨X, l, hI, hX, hl, r, tb⟩ := genI h2 hs
      exact ⟨X, l, hI.restrict h0 h1, HasTy0.restrict h0 h1 hX, hl, r.restrict h0 h1, tb.restrict h0 h1⟩
  | .const h0 h1, hs => by simp [isIntro] at hs
  | .univ h0 h1, hs => by simp [isIntro] at hs
  | .cumul h0 h1, hs => by
      obtain ⟨X, l', hI, hX, hl, r, _⟩ := genI h1 hs
      exact ⟨X, l', hI, hX, hl, r.up, .inr ⟨_, rfl, h0⟩⟩
  | .pi h0 h1, hs => by simp [isIntro] at hs
  | .lam h0 h1, hs => ⟨_, _, ⟨_, _, rfl, h0, h1⟩, h0, (pre_ty h0).lvl, Rel.refl h0 (pre_ty h0).lvl, .inl ⟨_, (pre_ty h0).lvl, h0⟩⟩
  | .app h0 h1, hs => by simp [isIntro] at hs
  | .sigma h0 h1, hs => by simp [isIntro] at hs
  | .pair h0 h1 h2, hs => ⟨_, _, ⟨_, _, _, rfl, h0, h1, h2⟩, h0, (pre_ty h0).lvl, Rel.refl h0 (pre_ty h0).lvl, .inl ⟨_, (pre_ty h0).lvl, h0⟩⟩
  | .fst h0, hs => by simp [isIntro] at hs
  | .snd h0, hs => by simp [isIntro] at hs
  | .path h0 h1 h2, hs => by simp [isIntro] at hs
  | .plam h0 h1 h2 h3, hs => ⟨_, _, .inl ⟨_, _, _, _, rfl, h0, h1, h2, h3⟩, h0, (pre_ty h0).lvl, Rel.refl h0 (pre_ty h0).lvl, .inl ⟨_, (pre_ty h0).lvl, h0⟩⟩
  | .papp h0 h1, hs => by simp [isIntro] at hs
  | .ipi h0 h1, hs => by simp [isIntro] at hs
  | .ilam h0 h1, hs => ⟨_, _, .inr ⟨_, _, rfl, h0, h1⟩, h0, (pre_ty h0).lvl, Rel.refl h0 (pre_ty h0).lvl, .inl ⟨_, (pre_ty h0).lvl, h0⟩⟩
  | .iapp h0 h1, hs => by simp [isIntro] at hs
  | .split h0 h1 h2 h3 h4 h5 h6, hs => by simp [isIntro] at hs
  | .abort h0 h1, hs => by simp [isIntro] at hs
  | .transp h0 h1 h2 h3, hs => by simp [isIntro] at hs
  | .hcomp h0 h1 h2 h3 h4, hs => ⟨_, _, ⟨rfl, _, h0, h1, h2, h3, h4⟩, h0, (pre_ty h0).lvl, Rel.refl h0 (pre_ty h0).lvl, .inl ⟨_, (pre_ty h0).lvl, h0⟩⟩
  | .glue h0 h1 h2 h3, hs => by simp [isIntro] at hs
  | .glueEl h0 h1 h2 h3 h4, hs => by simp [isIntro] at hs
  | .unglue h0 h1 h2 h3, hs => by simp [isIntro] at hs
  | .data h0 h1 h2, hs => by simp [isIntro] at hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7, hs => ⟨_, _, ⟨rfl, _, _, h0, h1, h2, h3, h4, h5, h6, h7⟩, h3, (pre_ty h3).lvl, Rel.refl h3 (pre_ty h3).lvl, .inl ⟨_, (pre_ty h3).lvl, h3⟩⟩
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, hs => by simp [isIntro] at hs

theorem genApp {Ψ Φ Γ s T f a} : HasTy0 S Ψ Φ Γ s T → s = .app f a → isIntro f = true →
    ∃ A1 B1 X l, HasTy0 S Ψ Φ Γ a A1 ∧ IntroTy S Ψ Φ Γ f X ∧ HasTy0 S Ψ Φ Γ X (univ l) ∧ l ≤ maxLevel ∧
      Rel S Ψ Φ Γ X (pi A1 B1) ∧ TB S Ψ Φ Γ (pi A1 B1) ∧ TyChainC S Ψ Φ Γ (B1.inst a) T
  | .var h0 h1, hs, hf => by cases hs
  | .conv h0 h1, hs, hf => by
      obtain ⟨A1, B1, X, l, ha, hI, hX, hl, r, tb, ch⟩ := genApp h0 hs hf
      exact ⟨A1, B1, X, l, ha, hI, hX, hl, r, tb, ch.snoc h1⟩
  | .restrict h0 h1 h2, hs, hf => by
      obtain ⟨A1, B1, X, l, ha, hI, hX, hl, r, tb, ch⟩ := genApp h2 hs hf
      exact ⟨A1, B1, X, l, HasTy0.restrict h0 h1 ha, hI.restrict h0 h1, HasTy0.restrict h0 h1 hX, hl, r.restrict h0 h1, tb.restrict h0 h1, ch.restrict h0 h1⟩
  | .const h0 h1, hs, hf => by cases hs
  | .univ h0 h1, hs, hf => by cases hs
  | .cumul h0 h1, hs, hf => by
      obtain ⟨A1, B1, X, l, ha, hI, hX, hl, r, tb, ch⟩ := genApp h1 hs hf
      exact ⟨A1, B1, X, l, ha, hI, hX, hl, r, tb, ch.cumul h0⟩
  | .pi h0 h1, hs, hf => by cases hs
  | .lam h0 h1, hs, hf => by cases hs
  | .app h0 h1, hs, hf => by
      obtain ⟨X, l, hI, hX, hl, r, tb⟩ := genI h0 (by injection hs with h; rw [h]; exact hf)
      cases hs
      exact ⟨_, _, X, l, h1, hI, hX, hl, r, tb, .refl _⟩
  | .sigma h0 h1, hs, hf => by cases hs
  | .pair h0 h1 h2, hs, hf => by cases hs
  | .fst h0, hs, hf => by cases hs
  | .snd h0, hs, hf => by cases hs
  | .path h0 h1 h2, hs, hf => by cases hs
  | .plam h0 h1 h2 h3, hs, hf => by cases hs
  | .papp h0 h1, hs, hf => by cases hs
  | .ipi h0 h1, hs, hf => by cases hs
  | .ilam h0 h1, hs, hf => by cases hs
  | .iapp h0 h1, hs, hf => by cases hs
  | .split h0 h1 h2 h3 h4 h5 h6, hs, hf => by cases hs
  | .abort h0 h1, hs, hf => by cases hs
  | .transp h0 h1 h2 h3, hs, hf => by cases hs
  | .hcomp h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .glue h0 h1 h2 h3, hs, hf => by cases hs
  | .glueEl h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .unglue h0 h1 h2 h3, hs, hf => by cases hs
  | .data h0 h1 h2, hs, hf => by cases hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7, hs, hf => by cases hs
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, hs, hf => by cases hs

theorem genFst {Ψ Φ Γ s T p} : HasTy0 S Ψ Φ Γ s T → s = .fst p → isIntro p = true →
    ∃ A1 B1 X l, IntroTy S Ψ Φ Γ p X ∧ HasTy0 S Ψ Φ Γ X (univ l) ∧ l ≤ maxLevel ∧
      Rel S Ψ Φ Γ X (sigma A1 B1) ∧ TB S Ψ Φ Γ (sigma A1 B1) ∧ TyChainC S Ψ Φ Γ A1 T
  | .var h0 h1, hs, hf => by cases hs
  | .conv h0 h1, hs, hf => by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genFst h0 hs hf
      exact ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch.snoc h1⟩
  | .restrict h0 h1 h2, hs, hf => by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genFst h2 hs hf
      exact ⟨A1, B1, X, l, hI.restrict h0 h1, HasTy0.restrict h0 h1 hX, hl, r.restrict h0 h1, tb.restrict h0 h1, ch.restrict h0 h1⟩
  | .const h0 h1, hs, hf => by cases hs
  | .univ h0 h1, hs, hf => by cases hs
  | .cumul h0 h1, hs, hf => by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genFst h1 hs hf
      exact ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch.cumul h0⟩
  | .pi h0 h1, hs, hf => by cases hs
  | .lam h0 h1, hs, hf => by cases hs
  | .app h0 h1, hs, hf => by cases hs
  | .sigma h0 h1, hs, hf => by cases hs
  | .pair h0 h1 h2, hs, hf => by cases hs
  | .fst h0, hs, hf => by
      obtain ⟨X, l, hI, hX, hl, r, tb⟩ := genI h0 (by injection hs with h; rw [h]; exact hf)
      cases hs
      exact ⟨_, _, X, l, hI, hX, hl, r, tb, .refl _⟩
  | .snd h0, hs, hf => by cases hs
  | .path h0 h1 h2, hs, hf => by cases hs
  | .plam h0 h1 h2 h3, hs, hf => by cases hs
  | .papp h0 h1, hs, hf => by cases hs
  | .ipi h0 h1, hs, hf => by cases hs
  | .ilam h0 h1, hs, hf => by cases hs
  | .iapp h0 h1, hs, hf => by cases hs
  | .split h0 h1 h2 h3 h4 h5 h6, hs, hf => by cases hs
  | .abort h0 h1, hs, hf => by cases hs
  | .transp h0 h1 h2 h3, hs, hf => by cases hs
  | .hcomp h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .glue h0 h1 h2 h3, hs, hf => by cases hs
  | .glueEl h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .unglue h0 h1 h2 h3, hs, hf => by cases hs
  | .data h0 h1 h2, hs, hf => by cases hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7, hs, hf => by cases hs
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, hs, hf => by cases hs

theorem genSnd {Ψ Φ Γ s T p} : HasTy0 S Ψ Φ Γ s T → s = .snd p → isIntro p = true →
    ∃ A1 B1 X l, IntroTy S Ψ Φ Γ p X ∧ HasTy0 S Ψ Φ Γ X (univ l) ∧ l ≤ maxLevel ∧
      Rel S Ψ Φ Γ X (sigma A1 B1) ∧ TB S Ψ Φ Γ (sigma A1 B1) ∧ TyChainC S Ψ Φ Γ (B1.inst (fst p)) T
  | .var h0 h1, hs, hf => by cases hs
  | .conv h0 h1, hs, hf => by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genSnd h0 hs hf
      exact ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch.snoc h1⟩
  | .restrict h0 h1 h2, hs, hf => by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genSnd h2 hs hf
      exact ⟨A1, B1, X, l, hI.restrict h0 h1, HasTy0.restrict h0 h1 hX, hl, r.restrict h0 h1, tb.restrict h0 h1, ch.restrict h0 h1⟩
  | .const h0 h1, hs, hf => by cases hs
  | .univ h0 h1, hs, hf => by cases hs
  | .cumul h0 h1, hs, hf => by
      obtain ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch⟩ := genSnd h1 hs hf
      exact ⟨A1, B1, X, l, hI, hX, hl, r, tb, ch.cumul h0⟩
  | .pi h0 h1, hs, hf => by cases hs
  | .lam h0 h1, hs, hf => by cases hs
  | .app h0 h1, hs, hf => by cases hs
  | .sigma h0 h1, hs, hf => by cases hs
  | .pair h0 h1 h2, hs, hf => by cases hs
  | .fst h0, hs, hf => by cases hs
  | .snd h0, hs, hf => by
      obtain ⟨X, l, hI, hX, hl, r, tb⟩ := genI h0 (by injection hs with h; rw [h]; exact hf)
      cases hs
      exact ⟨_, _, X, l, hI, hX, hl, r, tb, .refl _⟩
  | .path h0 h1 h2, hs, hf => by cases hs
  | .plam h0 h1 h2 h3, hs, hf => by cases hs
  | .papp h0 h1, hs, hf => by cases hs
  | .ipi h0 h1, hs, hf => by cases hs
  | .ilam h0 h1, hs, hf => by cases hs
  | .iapp h0 h1, hs, hf => by cases hs
  | .split h0 h1 h2 h3 h4 h5 h6, hs, hf => by cases hs
  | .abort h0 h1, hs, hf => by cases hs
  | .transp h0 h1 h2 h3, hs, hf => by cases hs
  | .hcomp h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .glue h0 h1 h2 h3, hs, hf => by cases hs
  | .glueEl h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .unglue h0 h1 h2 h3, hs, hf => by cases hs
  | .data h0 h1 h2, hs, hf => by cases hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7, hs, hf => by cases hs
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, hs, hf => by cases hs

theorem genPapp {Ψ Φ Γ s T p r} : HasTy0 S Ψ Φ Γ s T → s = .papp p r → isIntro p = true →
    ∃ Y A1 X l, ((∃ a1 b1, Y = path A1 a1 b1) ∨ Y = ipi A1) ∧ r.Scoped Ψ ∧ IntroTy S Ψ Φ Γ p X ∧
      HasTy0 S Ψ Φ Γ X (univ l) ∧ l ≤ maxLevel ∧ Rel S Ψ Φ Γ X Y ∧ TB S Ψ Φ Γ Y ∧
      TyChainC S Ψ Φ Γ (A1.dinst r) T
  | .var h0 h1, hs, hf => by cases hs
  | .conv h0 h1, hs, hf => by
      obtain ⟨Y, A1, X, l, hY, hr, hI, hX, hl, rl, tb, ch⟩ := genPapp h0 hs hf
      exact ⟨Y, A1, X, l, hY, hr, hI, hX, hl, rl, tb, ch.snoc h1⟩
  | .restrict h0 h1 h2, hs, hf => by
      obtain ⟨Y, A1, X, l, hY, hr, hI, hX, hl, rl, tb, ch⟩ := genPapp h2 hs hf
      exact ⟨Y, A1, X, l, hY, hr, hI.restrict h0 h1, HasTy0.restrict h0 h1 hX, hl, rl.restrict h0 h1, tb.restrict h0 h1, ch.restrict h0 h1⟩
  | .const h0 h1, hs, hf => by cases hs
  | .univ h0 h1, hs, hf => by cases hs
  | .cumul h0 h1, hs, hf => by
      obtain ⟨Y, A1, X, l, hY, hr, hI, hX, hl, rl, tb, ch⟩ := genPapp h1 hs hf
      exact ⟨Y, A1, X, l, hY, hr, hI, hX, hl, rl, tb, ch.cumul h0⟩
  | .pi h0 h1, hs, hf => by cases hs
  | .lam h0 h1, hs, hf => by cases hs
  | .app h0 h1, hs, hf => by cases hs
  | .sigma h0 h1, hs, hf => by cases hs
  | .pair h0 h1 h2, hs, hf => by cases hs
  | .fst h0, hs, hf => by cases hs
  | .snd h0, hs, hf => by cases hs
  | .path h0 h1 h2, hs, hf => by cases hs
  | .plam h0 h1 h2 h3, hs, hf => by cases hs
  | .papp h0 h1, hs, hf => by
      obtain ⟨X, l, hI, hX, hl, rl, tb⟩ := genI h0 (by injection hs with h; rw [h]; exact hf)
      cases hs
      exact ⟨_, _, X, l, .inl ⟨_, _, rfl⟩, h1, hI, hX, hl, rl, tb, .refl _⟩
  | .ipi h0 h1, hs, hf => by cases hs
  | .ilam h0 h1, hs, hf => by cases hs
  | .iapp h0 h1, hs, hf => by
      obtain ⟨X, l, hI, hX, hl, rl, tb⟩ := genI h0 (by injection hs with h; rw [h]; exact hf)
      cases hs
      exact ⟨_, _, X, l, .inr rfl, h1, hI, hX, hl, rl, tb, .refl _⟩
  | .split h0 h1 h2 h3 h4 h5 h6, hs, hf => by cases hs
  | .abort h0 h1, hs, hf => by cases hs
  | .transp h0 h1 h2 h3, hs, hf => by cases hs
  | .hcomp h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .glue h0 h1 h2 h3, hs, hf => by cases hs
  | .glueEl h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .unglue h0 h1 h2 h3, hs, hf => by cases hs
  | .data h0 h1 h2, hs, hf => by cases hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7, hs, hf => by cases hs
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, hs, hf => by cases hs

theorem genElim {Ψ Φ Γ s T d ps P bs t} : HasTy0 S Ψ Φ Γ s T → s = .elim d ps P bs t →
    isIntro t = true →
    ∃ D m X l, ElimPrem S Ψ Φ Γ d D ps P bs m ∧ IntroTy S Ψ Φ Γ t X ∧ HasTy0 S Ψ Φ Γ X (univ l) ∧
      l ≤ maxLevel ∧ Rel S Ψ Φ Γ X (data d ps) ∧ TB S Ψ Φ Γ (data d ps) ∧ TyChainC S Ψ Φ Γ (P.inst t) T
  | .var h0 h1, hs, hf => by cases hs
  | .conv h0 h1, hs, hf => by
      obtain ⟨D, m, X, l, hE, hI, hX, hl, r, tb, ch⟩ := genElim h0 hs hf
      exact ⟨D, m, X, l, hE, hI, hX, hl, r, tb, ch.snoc h1⟩
  | .restrict h0 h1 h2, hs, hf => by
      obtain ⟨D, m, X, l, hE, hI, hX, hl, r, tb, ch⟩ := genElim h2 hs hf
      exact ⟨D, m, X, l, hE.restrict h0 h1, hI.restrict h0 h1, HasTy0.restrict h0 h1 hX, hl, r.restrict h0 h1, tb.restrict h0 h1, ch.restrict h0 h1⟩
  | .const h0 h1, hs, hf => by cases hs
  | .univ h0 h1, hs, hf => by cases hs
  | .cumul h0 h1, hs, hf => by
      obtain ⟨D, m, X, l, hE, hI, hX, hl, r, tb, ch⟩ := genElim h1 hs hf
      exact ⟨D, m, X, l, hE, hI, hX, hl, r, tb, ch.cumul h0⟩
  | .pi h0 h1, hs, hf => by cases hs
  | .lam h0 h1, hs, hf => by cases hs
  | .app h0 h1, hs, hf => by cases hs
  | .sigma h0 h1, hs, hf => by cases hs
  | .pair h0 h1 h2, hs, hf => by cases hs
  | .fst h0, hs, hf => by cases hs
  | .snd h0, hs, hf => by cases hs
  | .path h0 h1 h2, hs, hf => by cases hs
  | .plam h0 h1 h2 h3, hs, hf => by cases hs
  | .papp h0 h1, hs, hf => by cases hs
  | .ipi h0 h1, hs, hf => by cases hs
  | .ilam h0 h1, hs, hf => by cases hs
  | .iapp h0 h1, hs, hf => by cases hs
  | .split h0 h1 h2 h3 h4 h5 h6, hs, hf => by cases hs
  | .abort h0 h1, hs, hf => by cases hs
  | .transp h0 h1 h2 h3, hs, hf => by cases hs
  | .hcomp h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .glue h0 h1 h2 h3, hs, hf => by cases hs
  | .glueEl h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .unglue h0 h1 h2 h3, hs, hf => by cases hs
  | .data h0 h1 h2, hs, hf => by cases hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7, hs, hf => by cases hs
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, hs, hf => by
      obtain ⟨X, l, hI, hX, hl, r, tb⟩ := genI h9 (by injection hs with _ _ _ _ h; rw [h]; exact hf)
      cases hs
      exact ⟨_, _, X, l, ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, hI, hX, hl, r, tb, .refl _⟩

theorem genTransp {Ψ Φ Γ s T A φ a} : HasTy0 S Ψ Φ Γ s T → s = .transp A φ a → isIntro a = true →
    ∃ l0 X l, HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l0) ∧ φ.Scoped Ψ ∧
      EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (univ l0) ∧
      IntroTy S Ψ Φ Γ a X ∧ HasTy0 S Ψ Φ Γ X (univ l) ∧ l ≤ maxLevel ∧ Rel S Ψ Φ Γ X (A.dinst .zero) ∧
      TB S Ψ Φ Γ (A.dinst .zero) ∧ TyChainC S Ψ Φ Γ (A.dinst .one) T
  | .var h0 h1, hs, hf => by cases hs
  | .conv h0 h1, hs, hf => by
      obtain ⟨l0, X, l, hL, hφ, hc, hI, hX', hl, r, tb, ch⟩ := genTransp h0 hs hf
      exact ⟨l0, X, l, hL, hφ, hc, hI, hX', hl, r, tb, ch.snoc h1⟩
  | .restrict h0 h1 h2, hs, hf => by
      obtain ⟨l0, X, l, hL, hφ, hc, hI, hX', hl, r, tb, ch⟩ := genTransp h2 hs hf
      exact by
        have hs1 := scoped_shift h0
        have hX : (cof _ φ).Scoped _ := ⟨h0, hφ⟩
        exact ⟨l0, X, l, HasTy0.restrict hs1 (ent_shift h1) hL, hφ,
          EqTm0.restrict (scoped_shift hX) (ent_shift (ent_and_mono h1 (ent_refl _))) hc,
          hI.restrict h0 h1, HasTy0.restrict h0 h1 hX', hl, r.restrict h0 h1, tb.restrict h0 h1, ch.restrict h0 h1⟩
  | .const h0 h1, hs, hf => by cases hs
  | .univ h0 h1, hs, hf => by cases hs
  | .cumul h0 h1, hs, hf => by
      obtain ⟨l0, X, l, hL, hφ, hc, hI, hX', hl, r, tb, ch⟩ := genTransp h1 hs hf
      exact ⟨l0, X, l, hL, hφ, hc, hI, hX', hl, r, tb, ch.cumul h0⟩
  | .pi h0 h1, hs, hf => by cases hs
  | .lam h0 h1, hs, hf => by cases hs
  | .app h0 h1, hs, hf => by cases hs
  | .sigma h0 h1, hs, hf => by cases hs
  | .pair h0 h1 h2, hs, hf => by cases hs
  | .fst h0, hs, hf => by cases hs
  | .snd h0, hs, hf => by cases hs
  | .path h0 h1 h2, hs, hf => by cases hs
  | .plam h0 h1 h2 h3, hs, hf => by cases hs
  | .papp h0 h1, hs, hf => by cases hs
  | .ipi h0 h1, hs, hf => by cases hs
  | .ilam h0 h1, hs, hf => by cases hs
  | .iapp h0 h1, hs, hf => by cases hs
  | .split h0 h1 h2 h3 h4 h5 h6, hs, hf => by cases hs
  | .abort h0 h1, hs, hf => by cases hs
  | .transp h0 h1 h2 h3, hs, hf => by
      obtain ⟨X, l, hI, hX, hl, r, tb⟩ := genI h3 (by injection hs with _ _ h; rw [h]; exact hf)
      cases hs
      exact ⟨_, X, l, h0, h1, h2, hI, hX, hl, r, tb, .refl _⟩
  | .hcomp h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .glue h0 h1 h2 h3, hs, hf => by cases hs
  | .glueEl h0 h1 h2 h3 h4, hs, hf => by cases hs
  | .unglue h0 h1 h2 h3, hs, hf => by cases hs
  | .data h0 h1 h2, hs, hf => by cases hs
  | .con h0 h1 h2 h3 h4 h5 h6 h7, hs, hf => by cases hs
  | .elim h0 h1 h2 h3 h4 h5 h6 h7 h8 h9, hs, hf => by cases hs
end

/-- Presupposition for the minimal judgments, given `ContractaTyped`. -/
theorem presup0 : Presup0 S := fun h => ⟨(pre_eq hS hT hC h).1, (pre_eq hS hT hC h).2.1⟩

end

end KubusCore.Meta
