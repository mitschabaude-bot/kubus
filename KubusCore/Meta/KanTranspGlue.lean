import KubusCore.Meta.KanU

/-!
# Metatheory: typing the contractum of `transp` in Glue types
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem transpGlue_typed (hS : SigClosed S) {Ψ Φ Γ A φ T' e ψ u0 T l δ}
    (h : HasTy0 S Ψ Φ Γ (transp (glue A φ T' e) ψ u0) T)
    (hA : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l))
    (he : HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift e (equiv T' A))
    (hδ1 : I.Entails δ φ.forall0) (hδ2 : I.Entails φ.forall0 δ) :
    HasTy0 S Ψ Φ Γ (transpGlueWith δ A φ T' e ψ u0) T := by
  sorry

end KubusCore.Meta
