import Model.Whnf.Valid2ElimH29

/-! # Coherence of eliminator contracta across restrictions -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' K : ℕ} (hW : WfSig S) {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (HL : ElimRelH S d D K P M bs P M bs)
include hW hD hH hyp hP hPP HL

/-- A restricted head's contractum agrees with the contractum of the new head after restriction. -/
theorem elimRedH_coh (ρ : ISub k K) {x x' W : Tm}
    (hx : RE2 S k (.data d (P.isub ρ)) x x') (hw : RedE S k (.data d (P.isub ρ)) x W)
    (N : ElimNormH S d D K P M bs k ρ W) (σ : ISub k' k) {Y : Tm}
    (hy : RedE S k' (.data d (P.isub (ρ.comp σ))) (x.isub σ) Y)
    (C : EMStageH S d D K P M bs k' (ρ.hom.comp σ.hom) ((Tm.data d (P.isub ρ)).isub σ)
      (W.isub σ) (x.isub σ)) :
    RE2 S k' ((M.isub (ρ.comp σ)).inst (x.isub σ))
      ((elimRedH d D (P.isub ρ) (M.isub ρ) (bs.isub ρ) W).isub σ)
      (elimRedH d D (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) Y) := by
  obtain ⟨W0, hw0, -, -, hWx⟩ := whnf_data hW hD hH hyp hP hPP ρ hx
  obtain rfl := RedW.unique hw.1 hw0.1
  have hc := closed_of_ty hW (HasTy.eqR hw.2)
  have N0 := N k (ISub.id k) W
    (by rw [ISub.comp_id, isub_id_of_closed hc]; exact ⟨redW_self hw.1.2, EqTm.refl (HasTy.eqR hw.2)⟩)
  rw [ISub.comp_id, isub_id_of_closed hc] at N0
  have NS := RE2.isub hW N0 σ
  simp only [isub_inst, isub_elim, Tm.isub_isub] at NS
  have R0 := RE2.isub hW hWx σ
  rw [data_isub_comp] at R0
  obtain ⟨V, hv, -, -, hVW⟩ := whnf_data hW hD hH hyp hP hPP (ρ.comp σ) R0
  have NV := N k' σ V hv
  have hA := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp σ)
  have Wself := RE2.trans hW hA R0 (RE2.symm hW hA R0)
  have TW := HL.mot k' (ρ.comp σ) _ _ Wself
  have R1 := RE2.trans hW TW (RE2.symm hW TW NS) NV
  rw [data_isub_comp] at C
  have R2 := C (ρ.comp σ) (by rw [ISub.hom_comp]) rfl P M bs HL V Y hv hy
  have Vx := RE2.trans hW hA hVW R0
  have xself := RE2.trans hW hA (RE2.symm hW hA R0) R0
  have TX := HL.mot k' (ρ.comp σ) _ _ xself
  exact RE2.trans hW TX (RE2.conv hW (HL.mot k' (ρ.comp σ) _ _ R0) R1)
    (RE2.conv hW (HL.mot k' (ρ.comp σ) _ _ Vx) R2)

end

end Model.Whnf
