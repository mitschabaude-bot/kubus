import Model.Whnf.Boundary2Eval

/-! # Boundary typing and constructor induction hypotheses -/
set_option autoImplicit false
namespace Model.Whnf.Boundary2
open KubusCore KubusCore.Meta Model.Canon Model.Whnf
noncomputable section

/-- Boundary argument typing for one data declaration, supplied by validity at its preceding prefix. -/
def BndTyping (S : Sig) (d : ℕ) : Prop := ∀ {k : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {P1 : Tm} {Y : List Tm} {rs : List I}
    {kb : ℕ} {ψ : I} {b : Tm},
    S[d]? = some (.data D) → D.isHIT = true → D.ctors[c]? = some C → C.bnd[kb]? = some (ψ, b) →
    I.Entails .one (Ctor.cofAt ψ rs) →
    HasTy S k .one [] (.data d P1) (.univ D.level) → RT2 S k (.data d P1) (.data d P1) →
    Y.length = C.args.length →
    HasTy S k .one [] (.con d c P1 (Tm.ofList Y) rs) (.data d P1) →
    (∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ P1.toList.reverse)) (Y.getD i .abort) (Y.getD i .abort)) →
    bndRel S k d D.params.length C.args.length C D.ctors P1 P1 Y Y rs b

/-- Boundary expansion for one constructor, uniformly in closed instances. -/
def CBRSt (S : Sig) (d : ℕ) (D : DataDecl) (c : ℕ) : Prop := ∀ {k : ℕ} {C : Ctor} {P1 : Tm} {Y : List Tm} {rs : List I} {kb : ℕ}
    {ψ : I} {b : Tm},
    D.ctors[c]? = some C → C.bnd[kb]? = some (ψ, b) →
    I.Entails .one (Ctor.cofAt ψ rs) →
    HasTy S k .one [] (.data d P1) (.univ D.level) → RT2 S k (.data d P1) (.data d P1) →
    Y.length = C.args.length →
    HasTy S k .one [] (.con d c P1 (Tm.ofList Y) rs) (.data d P1) →
    (∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ P1.toList.reverse)) (Y.getD i .abort) (Y.getD i .abort)) →
    RE2 S k (.data d P1) (.con d c P1 (Tm.ofList Y) rs) (Ctor.bndAt b P1.toList Y rs)

/-- Constructor relatedness may be based at any restriction. -/
theorem crst_restr {S : Sig} {d K k c : ℕ} {D : DataDecl} {P : Tm}
    (h : CRSt S d D K P c) (σ : ISub k K) : CRSt S d D k (P.isub σ) c := by
  intro k3 ρ C q q' X X' rs rs' hC ht ht' hrs hargs
  simpa only [Tm.isub_isub] using h (σ.comp ρ) hC (by simpa only [Tm.isub_isub] using ht)
    (by simpa only [Tm.isub_isub] using ht') hrs (by simpa only [Tm.isub_isub] using hargs)

end
end Model.Whnf.Boundary2
