import Model.Whnf.Valid2ElimH7

/-!
# Composition in the higher inductive eliminator motive

The motive line's own code supplies transport and composition at every restriction used by the
binary composition lemma.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

/-- Binary heterogeneous composition using the Kan evidence of its line code. -/
theorem comp2r_code {C C' u u' u0 u0' : Tm} {ψ ψ' : I} {l : ℕ}
    (hC : HasTy S (k + 1) .one [] C (.univ l)) (hK : KanP2 S (k + 1) (semK S (k + 1) C))
    (hLR : LineRob S k C C') (hLRL : LineRob S k C C)
    (hty : HasTy S k .one [] (Tm.comp C ψ u u0) (C.dinst .one))
    (hty' : HasTy S k .one [] (Tm.comp C' ψ' u' u0') (C.dinst .one))
    (h12 : I.Entails ψ ψ') (h21 : I.Entails ψ' ψ)
    (htube : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r'))
    (hu0 : RE2 S k (C.dinst .zero) u0 u0')
    (hbd : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) ((u.isub σ.up).dinst .zero) (u0'.isub σ))
    (hbd' : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) (u0.isub σ) ((u'.isub σ.up).dinst .zero)) :
    RE2 S k (C.dinst .one) (Tm.comp C ψ u u0) (Tm.comp C' ψ' u' u0') := by
  refine comp2r hW hLR hLRL (fun k3 Θ X' hR => ?_) (fun X' hR => ?_) hty hty' h12 h21 htube hu0 hbd hbd'
  · exact (hK.isub hW hC Θ).2 k3 (Hom.id (k3 + 1)) _ _ hR
  · have hK1 := hK.isub hW hC (ISub.cons .one trivial (ISub.id k))
    rw [isub_cons_id_of_closed (closed_of_ty hW hC) .one trivial] at hK1
    exact hK1.1 k (Hom.id k) _ _ hR

end

end Model.Whnf
