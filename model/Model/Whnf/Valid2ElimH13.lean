import Model.Whnf.Valid2ElimH12

/-!
# The computable filler line of a higher inductive eliminator

Pointwise tube relatedness supplies its judgmental equality under the face. The data universe
premise supplies Kan for the filler, and the motive universe premise supplies Kan for its image.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ} (hW : WfSig S)
include hW

/-- The pointwise tube relation gives judgmental equality in the face context. -/
theorem TubeD.eq {A u u' : Tm} {φ : I} {l : ℕ} (hs : φ.Scoped k)
    (hA : HasTy S k .one [] A (.univ l))
    (ht : HasTy S (k + 1) (cof .one φ).shift [] u A.dshift)
    (ht' : HasTy S (k + 1) (cof .one φ).shift [] u' A.dshift)
    (hu : TubeD S k A φ u u') :
    EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift := by
  have hφ : (cof .one φ).shift = cof .one φ.shift := rfl
  rw [hφ] at ht ht' ⊢
  refine eq_of_restr hW (l := l) (KubusCore.I.scoped_shift hs) (.inl ?_) ht ht' ?_
  · exact HasTy.restrict ⟨trivial, KubusCore.I.scoped_shift hs⟩ (ent_one _)
      (minimal_to_spec (HasTy0.dwk (sigClosed_of_wfSig hW) (spec_to_minimal hW hA)))
  · intro k' σ hh
    have hh' : (ival (idEnv k') (φ.subst σ.tail.τ)).holds := by
      rwa [shift_subst_tail] at hh
    have h := hu k' σ.tail (σ.τ 0) (σ.sc 0 (by omega)) hh'
    have he := (RE2.typed h).2.2
    rw [isub_up_dinst _ _ _ (σ.sc 0 (by omega)), isub_up_dinst _ _ _ (σ.sc 0 (by omega)),
      ISub.cons_tail] at he
    simpa only [dshift_isub_tail] using he

/-- Related formal compositions have related filler points using the data code's Kan evidence. -/
theorem ElimRelH.fillerRel {d : ℕ} {D : DataDecl} {K : ℕ} {P M bs Q M' bs' : Tm}
    (H : ElimRelH S d D K P M bs Q M' bs')
    (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (ρ : ISub k K)
    {φ φ' : I} {u u' a a' : Tm} (hs : φ.Scoped k) (hs' : φ'.Scoped k)
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' (Tm.data d (P.isub ρ)).dshift)
    (ht : HasTy S (k + 1) .one [] (Tm.hfill (.data d (P.isub ρ)) φ u a) (Tm.data d (P.isub ρ)).dshift)
    (ht' : HasTy S (k + 1) .one [] (Tm.hfill (.data d (Q.isub ρ)) φ' u' a') (Tm.data d (P.isub ρ)).dshift)
    (he : EqTm S (k + 1) .one [] (Tm.hfill (.data d (P.isub ρ)) φ u a)
      (Tm.hfill (.data d (Q.isub ρ)) φ' u' a') (Tm.data d (P.isub ρ)).dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hu : Tube2 S k (.data d (P.isub ρ)) φ u u') (ha : RE2 S k (.data d (P.isub ρ)) a a')
    (hb : HcompBnd2 S k (.data d (P.isub ρ)) φ u a) (hb' : HcompBnd2 S k (.data d (P.isub ρ)) φ' u' a') :
    ∀ k' (σ σ' : ISub k' (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k' (.data d (P.isub (ρ.comp σ.tail)))
        ((Tm.hfill (.data d (P.isub ρ)) φ u a).isub σ)
        ((Tm.hfill (.data d (Q.isub ρ)) φ' u' a').isub σ') := by
  intro k' σ σ' et e0
  have h := hfill_rel_code hW (HasTy.isubS hW hP ρ) (H.dat k ρ) (H.dataKan.isub hW hP ρ)
    hs hs' hteq ht ht' he h12 h21 hu ha hb hb' σ σ' et e0
  rw [dshift_isub_tail] at h
  change RE2 S k' (.data d ((P.isub ρ).isub σ.tail)) _ _ at h
  rwa [Tm.isub_isub] at h

end

end Model.Whnf
