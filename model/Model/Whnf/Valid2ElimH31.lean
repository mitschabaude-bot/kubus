import Model.Whnf.Valid2ElimH30

/-! # Head expansion for the higher inductive eliminator -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k K : ℕ} (hW : WfSig S) {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (HL : ElimRelH S d D K P M bs P M bs)
include hW hD hH hyp hP hPP HL

variable {ρ : ISub k K} {x x' : Tm} (hx : RE2 S k (.data d (P.isub ρ)) x x')
    (ih : ∀ k' (σ : ISub k' k), ElimStageH S d D K P M bs k' (ρ.comp σ).hom
      (.data d (P.isub (ρ.comp σ))) (x.isub σ) (x'.isub σ))
    (ihc : ∀ k' (σ : ISub k' k) W, RedW S (x.isub σ) W → ∀ k'' (τ : ISub k'' k'),
      ElimStageH S d D K P M bs k'' ((ρ.comp σ).comp τ).hom
        (.data d (P.isub ((ρ.comp σ).comp τ))) (W.isub τ) (x.isub (σ.comp τ)))
include hx ih ihc

/-- Head stages and their coherence supply normalization of the original scrutinee's elimination. -/
theorem elimNorm_introH : ElimNormH S d D K P M bs k ρ x := by
  intro k3 σ W hw
  have hxσ := RE2.isub hW hx σ
  rw [data_isub_comp] at hxσ
  have NW := (ih k3 σ).2 (ρ.comp σ) rfl rfl W hw
  obtain ⟨W0, hw0, -, -, hWx⟩ := whnf_data hW hD hH hyp hP hPP (ρ.comp σ) hxσ
  obtain rfl := RedW.unique hw.1 hw0.1
  have hWc := closed_of_ty hW (HasTy.eqR hw.2)
  have N0 := NW k3 (ISub.id k3) W (by
    rw [ISub.comp_id, isub_id_of_closed hWc]
    exact ⟨redW_self hw.1.2, EqTm.refl (HasTy.eqR hw.2)⟩)
  rw [ISub.comp_id, isub_id_of_closed hWc] at N0
  have target := RE2.conv hW (HL.mot k3 (ρ.comp σ) _ _ hWx) N0
  have hA := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp σ)
  have selfx := RE2.trans hW hA hxσ (RE2.symm hW hA hxσ)
  have TX := HL.mot k3 (ρ.comp σ) _ _ selfx
  obtain ⟨m, E⟩ := HL.tyL k3 (ρ.comp σ)
  have hElim := minimal_to_spec (E.elim_ty (spec_to_minimal hW (RE2.typed hxσ).1))
  refine RE2.expandH hW TX hElim (RE2.typed target).2.1 ?_
  intro k4 τ
  have hxτ := RE2.isub hW hxσ τ
  rw [data_isub_comp] at hxτ
  obtain ⟨Y, hy, hYF, -, -⟩ := whnf_data hW hD hH hyp hP hPP ((ρ.comp σ).comp τ) hxτ
  obtain ⟨m4, E4⟩ := HL.tyL k4 ((ρ.comp σ).comp τ)
  obtain ⟨rr, ee⟩ := elimRedH_reduct hW hD E4 (RE2.typed hxτ).1 hy hYF hH
  have CC : EMStageH S d D K P M bs k4 ((ρ.comp σ).hom.comp τ.hom)
      ((Tm.data d (P.isub (ρ.comp σ))).isub τ) (W.isub τ) ((x.isub σ).isub τ) := by
    simpa only [ISub.hom_comp, data_isub_comp, Tm.isub_isub] using (ihc k3 σ W hw.1 k4 τ).1
  have R := elimRedH_coh hW hD hH hyp hP hPP HL (ρ.comp σ) hxσ hw NW τ hy CC
  simp only [Tm.isub_isub] at R
  have TT := RT2.isub hW (RE2.tyCode hW target) TX τ
  simp only [isub_inst, Tm.isub_isub] at TT
  refine ⟨elimRedH d D (P.isub ((ρ.comp σ).comp τ)) (M.isub ((ρ.comp σ).comp τ))
    (bs.isub ((ρ.comp σ).comp τ)) Y, ?_, ?_, ?_⟩
  · simpa only [isub_elim, Tm.isub_isub] using rr
  · simpa only [isub_elim, isub_inst, Tm.isub_isub] using ee
  · simpa only [isub_inst, Tm.isub_isub] using RE2.symm hW TT R

/-- Related eliminations follow by expansion on the right from the paired head contracta. -/
theorem elimPair_introH {Q M' bs' : Tm} (H : ElimRelH S d D K P M bs Q M' bs') :
    RE2 S k ((M.isub ρ).inst x) (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x)
      (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) x') := by
  have NL := elimNorm_introH hW hD hH hyp hP hPP HL hx ih ihc
  have left := ElimNormH.computable hW hD hH hyp hP hPP HL ρ hx NL
  have hA := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
  have xself := RE2.trans hW hA hx (RE2.symm hW hA hx)
  have TX := HL.mot k ρ _ _ xself
  obtain ⟨mR, ER⟩ := H.tyR k ρ
  have right := minimal_to_spec (ER.elim_ty (spec_to_minimal hW ((RE2.typed hx).2.1.tyConv
    (Comp2_ty_base (H.dat k ρ)).2.2.2.2.2)))
  have rightT := right.tyConv (Comp2_ty_base (H.mot k ρ _ _ hx)).2.2.2.2.2.symm
  apply RE2.symm hW TX
  refine RE2.expandH hW TX rightT (RE2.typed left).1 ?_
  intro k' σ
  have hxσ := RE2.isub hW hx σ
  rw [data_isub_comp] at hxσ
  have hAσ := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp σ)
  obtain ⟨W, hw, -, -, hWx⟩ := whnf_data hW hD hH hyp hP hPP (ρ.comp σ) hxσ
  obtain ⟨W', hw', hWF', -, -⟩ := whnf_data hW hD hH hyp hP hPP (ρ.comp σ) (RE2.symm hW hAσ hxσ)
  obtain ⟨mR', ER'⟩ := H.tyR k' (ρ.comp σ)
  have eDat := (Comp2_ty_base (H.dat k' (ρ.comp σ))).2.2.2.2.2
  have hwQ : RedE S k' (.data d (Q.isub (ρ.comp σ))) (x'.isub σ) W' := ⟨hw'.1, hw'.2.tyConv eDat⟩
  obtain ⟨rr, ee⟩ := elimRedH_reduct hW hD ER'
    ((RE2.typed hxσ).2.1.tyConv eDat) hwQ hWF' hH
  have ee' := ee.tyConv (Comp2_ty_base (H.mot k' (ρ.comp σ) _ _ hxσ)).2.2.2.2.2.symm
  have N := NL k' σ W hw
  have C := (ih k' σ).1 (ρ.comp σ) rfl rfl Q M' bs' H W W' hw hw'
  have R := RE2.trans hW (HL.mot k' (ρ.comp σ) _ _ (RE2.trans hW hAσ hxσ (RE2.symm hW hAσ hxσ))) N
    (RE2.conv hW (HL.mot k' (ρ.comp σ) _ _ hWx) C)
  have TT := RT2.isub hW (RE2.tyCode hW left) TX σ
  simp only [isub_inst, Tm.isub_isub] at TT
  refine ⟨elimRedH d D (Q.isub (ρ.comp σ)) (M'.isub (ρ.comp σ)) (bs'.isub (ρ.comp σ)) W', ?_, ?_, ?_⟩
  · simpa only [isub_elim, Tm.isub_isub] using rr
  · simpa only [isub_elim, isub_inst, Tm.isub_isub] using ee'
  · simpa only [isub_elim, isub_inst, Tm.isub_isub] using RE2.symm hW TT R

end

end Model.Whnf
