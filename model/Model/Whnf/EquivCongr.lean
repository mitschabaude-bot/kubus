import Model.Canon.Proj

/-!
# Congruence of the types of equivalences
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta

variable {S : Sig} (hS : SigClosed S) (hT0 : SigTyped0 S) (hC0 : ContractaTyped S)
include hS hT0 hC0

omit hT0 hC0 in
theorem pathC_congr {Ψ Φ Γ A A' a a' b b' l} (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) (ha : EqTm0 S Ψ Φ Γ a a' A)
    (hb : EqTm0 S Ψ Φ Γ b b' A) : EqTm0 S Ψ Φ Γ (Tm.pathC A a b) (Tm.pathC A' a' b') (Tm.univ l) := by
  have hAd := EqTm0.dwk hS hA
  exact EqTm0.path hAd (by rw [Meta.dshift_dinst]; exact ha) (by rw [Meta.dshift_dinst]; exact hb)

theorem isContr_congr {Ψ Φ Γ X X' l} (hX : EqTm0 S Ψ Φ Γ X X' (Tm.univ l)) :
    EqTm0 S Ψ Φ Γ (Tm.isContr X) (Tm.isContr X') (Tm.univ l) := by
  have hXt := (pre_eq hS hT0 hC0 hX).1
  have hX1t := HasTy0.wk hS hXt hXt
  have hX1 := EqTm0.wk hS hXt hX
  have hX2 := EqTm0.wk hS hX1t hX1
  have hv1 : HasTy0 S Ψ Φ (X.shift :: X :: Γ) (Tm.var 1) X.shift.shift := HasTy0.var (Wf0.cons hX1t) rfl
  have hv0 : HasTy0 S Ψ Φ (X.shift :: X :: Γ) (Tm.var 0) X.shift.shift := HasTy0.var (Wf0.cons hX1t) rfl
  exact EqTm0.sigma hX (EqTm0.pi hX1 (pathC_congr hS hX2 (EqTm0.refl hv1) (EqTm0.refl hv0)))

theorem fiber_congr {Ψ Φ Γ T T' A A' f f' y y' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l))
    (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) (hf : EqTm0 S Ψ Φ Γ f f' (Tm.arrow T A)) (hy : EqTm0 S Ψ Φ Γ y y' A) :
    EqTm0 S Ψ Φ Γ (Tm.fiber T A f y) (Tm.fiber T' A' f' y') (Tm.univ l) := by
  have hTt := (pre_eq hS hT0 hC0 hT).1
  have hA1 := EqTm0.wk hS hTt hA
  have hf1 := EqTm0.wk hS hTt hf
  rw [Meta.arrow_shift] at hf1
  have hv : HasTy0 S Ψ Φ (T :: Γ) (Tm.var 0) T.shift := HasTy0.var (Wf0.cons hTt) rfl
  have happ := EqTm0.app hf1 (EqTm0.refl hv)
  rw [Meta.shift_inst] at happ
  exact EqTm0.sigma hT (pathC_congr hS hA1 happ (EqTm0.wk hS hTt hy))

theorem isEquiv_congr {Ψ Φ Γ T T' A A' f f' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l))
    (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) (hf : EqTm0 S Ψ Φ Γ f f' (Tm.arrow T A)) :
    EqTm0 S Ψ Φ Γ (Tm.isEquiv T A f) (Tm.isEquiv T' A' f') (Tm.univ l) := by
  have hAt := (pre_eq hS hT0 hC0 hA).1
  have hT1 := EqTm0.wk hS hAt hT
  have hA1 := EqTm0.wk hS hAt hA
  have hf1 := EqTm0.wk hS hAt hf
  rw [Meta.arrow_shift] at hf1
  have hv : HasTy0 S Ψ Φ (A :: Γ) (Tm.var 0) A.shift := HasTy0.var (Wf0.cons hAt) rfl
  exact EqTm0.pi hA (isContr_congr hS hT0 hC0 (fiber_congr hS hT0 hC0 hT1 hA1 hf1 (EqTm0.refl hv)))

theorem arrow_congr {Ψ Φ Γ T T' A A' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l)) (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) :
    EqTm0 S Ψ Φ Γ (Tm.arrow T A) (Tm.arrow T' A') (Tm.univ l) :=
  EqTm0.pi hT (EqTm0.wk hS (pre_eq hS hT0 hC0 hT).1 hA)

theorem equiv_congr {Ψ Φ Γ T T' A A' l} (hT : EqTm0 S Ψ Φ Γ T T' (Tm.univ l)) (hA : EqTm0 S Ψ Φ Γ A A' (Tm.univ l)) :
    EqTm0 S Ψ Φ Γ (Tm.equiv T A) (Tm.equiv T' A') (Tm.univ l) := by
  have hTA := arrow_congr hS hT0 hC0 hT hA
  have hTAt := (pre_eq hS hT0 hC0 hTA).1
  have hv : HasTy0 S Ψ Φ (Tm.arrow T A :: Γ) (Tm.var 0) (Tm.arrow T A).shift := HasTy0.var (Wf0.cons hTAt) rfl
  rw [Meta.arrow_shift] at hv
  exact EqTm0.sigma hTA (isEquiv_congr hS hT0 hC0 (EqTm0.wk hS hTAt hT) (EqTm0.wk hS hTAt hA) (EqTm0.refl hv))

theorem piPath_congr {Ψ Φ Γ X X' c c' l} (hX : EqTm0 S Ψ Φ Γ X X' (Tm.univ l)) (hc : EqTm0 S Ψ Φ Γ c c' X) :
    EqTm0 S Ψ Φ Γ (.pi X (Tm.pathC X.shift c.shift (.var 0))) (.pi X' (Tm.pathC X'.shift c'.shift (.var 0))) (Tm.univ l) := by
  have hXt := (pre_eq hS hT0 hC0 hX).1
  have hv : HasTy0 S Ψ Φ (X :: Γ) (Tm.var 0) X.shift := HasTy0.var (Wf0.cons hXt) rfl
  exact EqTm0.pi hX (pathC_congr hS (EqTm0.wk hS hXt hX) (EqTm0.wk hS hXt hc) (EqTm0.refl hv))

end Model.Whnf
