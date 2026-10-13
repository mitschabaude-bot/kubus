import Model.Canon.Formers

/-!
# Canonicity: the Kan operations preserve computability
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

variable (hW : WfSig S)
include hW

/-- Composition in a computable type of a computable tube and base is computable. -/
theorem kan_hcomp {A u a : Tm} {φ : I} (hA : RT S k A)
    (hty : HasTy S k .one [] (.hcomp A φ u a) A)
    (hu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE S k' (A.isub σ) ((u.isub σ.up).dinst r))
    (ha : RE S k A a) : RE S k A (.hcomp A φ u a) := by
  sorry

/-- Transport along a computable line of a computable element is computable. -/
theorem kan_transp {A a : Tm} {φ : I} {l : ℕ} (hA : RT S (k + 1) A)
    (hty : HasTy S k .one [] (.transp A φ a) (A.dinst .one))
    (ha : RE S k (A.dinst .zero) a) : RE S k (A.dinst .one) (.transp A φ a) := by
  sorry

end

end Model.Canon
