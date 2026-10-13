import KubusCore.Meta.KanU

/-!
# Metatheory: typing the contracta of `transp` in `Π`, `Σ`, path types and `(i : I) → A`

The line's constancy on `φ` gives, by injectivity of the type former, the constancy of its
components, which the contracta need.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem transpIPi_typed (hS : SigClosed S) {Ψ Φ Γ A φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (ipi A) φ u0) T) : HasTy0 S Ψ Φ Γ (transpIPi A φ u0) T := by
  sorry

theorem transpPi_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (pi A B) φ u0) T) : HasTy0 S Ψ Φ Γ (transpPi A B φ u0) T := by
  sorry

theorem transpSigma_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (sigma A B) φ u0) T) : HasTy0 S Ψ Φ Γ (transpSigma A B φ u0) T := by
  sorry

theorem transpPath_typed (hS : SigClosed S) {Ψ Φ Γ A a b φ p0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (path A a b) φ p0) T) : HasTy0 S Ψ Φ Γ (transpPath A a b φ p0) T := by
  sorry

end KubusCore.Meta
