import Model.Whnf.Valid2ElimH28

/-! # Formal composition stages of the eliminator normalization induction -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k K : ℕ} (hW : WfSig S) {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) {P : Tm}
    (hP : HasTy S K .one [] (.data d P) (.univ D.level))
include hW hD hP

theorem DR2_lit_toRE2 (ρ : ISub k K) {x x' : Tm}
    (h : DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k ρ.hom (.data d (P.isub ρ)) x x') :
    RE2 S k (.data d (P.isub ρ)) x x' := by
  have he : EqTm S k .one [] x x' (.data d (P.isub ρ)) := by cases h with | intro he => exact he
  exact (RE2_dataLit_iff hW hD hP ρ).2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, h⟩

variable (hH : D.isHIT = true) (hPP : RT2 S K (.data d P) (.data d P)) {M bs : Tm}
    (HL : ElimRelH S d D K P M bs P M bs)
include hH hPP HL

/-- The composition stage gives paired contracta and normalization of the left head. -/
theorem elimStage_hcompH {g : Hom k K} {A t t' ps qs qs' u u' a a' : Tm} {φ φ' : I}
    (hA : RedT S k A (.data d ps))
    (ht : RedE S k A t (.hcomp (.data d qs) φ u a))
    (ht' : RedE S k A t' (.hcomp (.data d qs') φ' u' a'))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ha : DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k g (.data d ps) a a')
    (hu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
        (dataP2 S (ΘK S D d K P) (Hom.id K)) k' (g.comp σ.hom) ((Tm.data d ps).isub σ)
        ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r))
    (hb : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
        (dataP2 S (ΘK S D d K P) (Hom.id K)) k' (g.comp σ.hom) ((Tm.data d ps).isub σ)
        ((u.isub σ.up).dinst .zero) (a.isub σ))
    (hb' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ'.subst σ.τ)).holds →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
        (dataP2 S (ΘK S D d K P) (Hom.id K)) k' (g.comp σ.hom) ((Tm.data d ps).isub σ)
        ((u'.isub σ.up).dinst .zero) (a'.isub σ))
    (iha : ElimMotiveH S d D K P M bs k g (.data d ps) a a')
    (ihu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      ElimMotiveH S d D K P M bs k' (g.comp σ.hom) ((Tm.data d ps).isub σ)
        ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r))
    (ihb : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      ElimMotiveH S d D K P M bs k' (g.comp σ.hom) ((Tm.data d ps).isub σ)
        ((u.isub σ.up).dinst .zero) (a.isub σ)) :
    ElimStageH S d D K P M bs k g A t t' := by
  refine ⟨?_, ?_⟩
  all_goals
    intro ρ hg hAe
    subst hg hAe
    obtain rfl : ps = P.isub ρ := redT_data_eq (Θ := ΘK S D d K P) hA
    have hAρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
    have aR := DR2_lit_toRE2 hW hD hP ρ ha
    have aL := RE2.trans hW hAρ aR (RE2.symm hW hAρ aR)
    have uR : TubeD S k (.data d (P.isub ρ)) φ u u' := by
      intro k' σ r hr hh
      have I := hu k' σ r hr hh
      rw [data_isub_comp, ← ISub.hom_comp] at I
      simpa only [data_isub_comp] using DR2_lit_toRE2 hW hD hP (ρ.comp σ) I
    have uL : TubeD S k (.data d (P.isub ρ)) φ u u := by
      intro k' σ r hr hh
      have T := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp σ)
      change RT2 S k' (.data d (P.isub (ρ.comp σ))) (.data d (P.isub (ρ.comp σ))) at T
      rw [← data_isub_comp] at T
      exact RE2.trans hW T (uR k' σ r hr hh) (RE2.symm hW T (uR k' σ r hr hh))
    have bL : HcompBnd2 S k (.data d (P.isub ρ)) φ u a := by
      intro k' σ hh
      have I := hb k' σ hh
      rw [data_isub_comp, ← ISub.hom_comp] at I
      simpa only [data_isub_comp] using DR2_lit_toRE2 hW hD hP (ρ.comp σ) I
    have bR : HcompBnd2 S k (.data d (P.isub ρ)) φ' u' a' := by
      intro k' σ hh
      have I := hb' k' σ hh
      rw [data_isub_comp, ← ISub.hom_comp] at I
      simpa only [data_isub_comp] using DR2_lit_toRE2 hW hD hP (ρ.comp σ) I
    have bE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
        RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst .zero))
          (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst .zero))
          (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) (a.isub σ)) := by
      intro k' σ hh
      have I := (ihb k' σ hh).1
      rw [data_isub_comp] at I
      exact I (ρ.comp σ) (by rw [ISub.hom_comp]) rfl P M bs HL
  · intro Q M' bs' H W W' hw hw'
    obtain rfl := RedW.unique hw.1 ht.1
    obtain rfl := RedW.unique hw'.1 ht'.1
    apply em2_hcompH hW hD hH hP hPP HL H ρ (HasTy.eqR ht.2) (HasTy.eqR ht'.2) h12 h21 uR aR bL bR
      (iha.1 ρ rfl rfl Q M' bs' H) ?_ bE
    intro k' σ r hr hh
    have I := (ihu k' σ r hr hh).1
    rw [data_isub_comp] at I
    exact I (ρ.comp σ) (by rw [ISub.hom_comp]) rfl Q M' bs' H
  · intro W hw
    obtain rfl := RedW.unique hw.1 ht.1
    have ae := iha.1 ρ rfl rfl P M bs HL
    have aeL := RE2.trans hW (HL.mot k ρ _ _ aL) ae (RE2.symm hW (HL.mot k ρ _ _ aL) ae)
    apply elimNorm_hcompH hW hD hH hP hPP HL ρ (HasTy.eqR ht.2) uL aL bL aeL ?_ bE ?_
    · intro k' σ r hr hh
      have I := (ihu k' σ r hr hh).1
      rw [data_isub_comp] at I
      have R := I (ρ.comp σ) (by rw [ISub.hom_comp]) rfl P M bs HL
      have T := HL.mot k' (ρ.comp σ) _ _ (by simpa only [data_isub_comp] using uL k' σ r hr hh)
      exact RE2.trans hW T R (RE2.symm hW T R)
    · intro k' σ r hr hh
      have I := (ihu k' σ r hr hh).2
      rw [data_isub_comp] at I
      exact I (ρ.comp σ) (by rw [ISub.hom_comp]) rfl

end

end Model.Whnf
