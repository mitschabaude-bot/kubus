import Model.Canon.DataKripke

/-!
# Canonicity: computability is Kripke, for every code
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

variable (hW : WfSig S)
include hW

theorem kr_glueC {l : ℕ} {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTw : ∀ k (f : Hom k m), (φ.restr f).holds → WF l k (dat Tp k f)) (hl : l ≤ maxLevel)
    (hX : Fib (glueC m A φ Tp ep) m)
    (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KR S k (dat Tp k f)) :
    KR S m (glueC m A φ Tp ep) := by
  have hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f) := fun k f hh => (hTw k f hh).fib.kv
  intro k f k' σ T t
  rw [Comp_glueC_at hφ hTp hTkv f, Comp_glueC_at hφ hTp hTkv (f.comp σ.hom)]
  by_cases hf : (φ.restr f).holds
  · have hfσ : (φ.restr (f.comp σ.hom)).holds := by
      rw [← Cof.restr_restr]; exact (hφ.restr f).holds_restr hf _
    rw [if_pos hf, if_pos hfσ, ← hTp k f hf k' σ.hom, ← Comp_eq_res (IsKV.ne_empty (hTkv k f hf))]
    have := ihT k f hf k (Hom.id k) k' σ T t
    rwa [Hom.id_comp] at this
  rw [if_neg hf, Comp_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr f) hf]
  simp only [Comp_res (IsKV.ne_empty hA), dat_res, Cof.restr_restr]
  by_cases hfσ : (φ.restr (f.comp σ.hom)).holds
  · rw [if_pos hfσ]
    have hcv := cv_wf hW l hl k' _ (hTw k' _ hfσ) k' (Hom.id k')
    constructor
    · rintro ⟨⟨hT, hsem⟩, A1, φ1, T1, e1, hE, hs, hfc, hdata, hall1, hall2⟩
      obtain ⟨hTT, -⟩ := hall2 k' σ hfσ
      have hG := hT.of_tyEq hE
      have hface := glue_face_tyEq hW (by rw [← isub_glue]; exact hG.isub hW σ)
        (entails_of_face hs hfc σ (by rwa [Cof.restr_restr]))
      have hTσ : TyEq S k' (T1.isub σ) (T.isub σ) := hface.symm.trans hW (by
        rw [← isub_glue]; exact (hE.isub hW σ).symm)
      have := (hcv _ _ t t).1 hTT hTσ
      exact this
    · rintro ⟨ht, hmem, -, A1, φ1, T1, e1, hE, hs, hfc, hdata, hun, hT⟩
      have hG := (isTyK_of_ty hW ht).of_tyEq hE
      have hface := glue_face_tyEq hW (by rw [← isub_glue]; exact hG.isub hW σ)
        (entails_of_face hs hfc σ (by rwa [Cof.restr_restr]))
      have hTσ : TyEq S k' (T1.isub σ) (T.isub σ) := hface.symm.trans hW (by
        rw [← isub_glue]; exact (hE.isub hW σ).symm)
      have htσ := HasTy.isubS hW ht σ
      exact (hcv _ _ _ _).2 (hT k' σ hfσ) hTσ (EqTm.refl htσ)
  · rw [if_neg hfσ, Comp_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr _) hfσ]
    simp only [Comp_res (IsKV.ne_empty hA), dat_res, Cof.restr_restr]
    constructor
    · rintro ⟨⟨hT, hsem⟩, A1, φ1, T1, e1, hE, hs, hfc, hdata, hall1, hall2⟩
      refine ⟨⟨hT.isub hW σ, ?_⟩, A1.isub σ, φ1.subst σ.τ, T1.isub σ, e1.isub σ, ?_, I.scoped_subst hs σ.sc,
        ?_, glueData_isub hW hs hdata σ, fun k'' σ' => ?_, fun k'' σ' hh => ?_⟩
      · have hG : glueC k (res f A) (φ.restr f) (res f Tp) (res f ep) = res f (glueC m A φ Tp ep) := by
          rw [res_glueC hTp hTkv hφ f, if_neg hf]
        have hG' : glueC k' (res (f.comp σ.hom) A) (φ.restr (f.comp σ.hom)) (res (f.comp σ.hom) Tp)
            (res (f.comp σ.hom) ep) = res (f.comp σ.hom) (glueC m A φ Tp ep) := by
          rw [res_glueC hTp hTkv hφ _, if_neg hfσ]
        rw [semK_isubTy hW hT σ, hsem, hG, hG']; simp only [res_res, Hom.comp_id, Hom.id_comp]
      · rw [← isub_glue]; exact hE.isub hW σ
      · rw [face_isub hfc σ, Cof.restr_restr]
      · have := hall1 k'' (σ.comp σ'); rwa [ISub.comp_hom, Tm.isub_isub]
      · rw [ISub.comp_hom] at hh
        obtain ⟨h1, h2⟩ := hall2 k'' (σ.comp σ') hh
        rw [ISub.comp_hom, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
        refine ⟨h1, ?_⟩
        have e : (fun k3 (σ3 : ISub k3 k'') => (Comp S A m k3 ((f.comp σ.hom).comp (σ'.comp σ3).hom)).el) =
            fun k3 σ3 => (Comp S A m k3 (f.comp ((σ.comp σ').comp σ3).hom)).el := by
          funext k3 σ3; rw [ISub.comp_hom, ISub.comp_assoc]
        rw [e]; exact h2
    · rintro ⟨ht, hmem, -, A1, φ1, T1, e1, hE, hs, hfc, hdata, hun, hT⟩
      have hG : glueC k (res f A) (φ.restr f) (res f Tp) (res f ep) = res f (glueC m A φ Tp ep) := by
        rw [res_glueC hTp hTkv hφ f, if_neg hf]
      have hG' : glueC k' (res (f.comp σ.hom) A) (φ.restr (f.comp σ.hom)) (res (f.comp σ.hom) Tp)
          (res (f.comp σ.hom) ep) = res (f.comp σ.hom) (glueC m A φ Tp ep) := by
        rw [res_glueC hTp hTkv hφ _, if_neg hfσ]
      have hmem' : semK S k' (t.isub σ) ∈ El (res (Hom.id k') (res (f.comp σ.hom) (glueC m A φ Tp ep))) (Hom.id k') := by
        rw [hG, res_res, Hom.comp_id] at hmem
        have := mem_isub hW hX ht hmem σ
        rwa [res_res, Hom.comp_id]
      refine ⟨HasTy.isubS hW ht σ, by rw [hG']; exact hmem', HasTy.isubS hW ht σ, A1.isub σ, φ1.subst σ.τ,
        T1.isub σ, e1.isub σ, ?_, I.scoped_subst hs σ.sc, ?_, glueData_isub hW hs hdata σ,
        fun k'' σ' => ?_, fun k'' σ' hh => ?_⟩
      · rw [← isub_glue]; exact hE.isub hW σ
      · rw [face_isub hfc σ, Cof.restr_restr]
      · have := hun k'' (σ.comp σ')
        rw [ISub.comp_hom, Tm.isub_isub, Tm.isub_isub, I_subst_subst, Tm.isub_isub]
        exact this
      · rw [ISub.comp_hom] at hh
        have := hT k'' (σ.comp σ') hh
        rw [ISub.comp_hom, Tm.isub_isub, Tm.isub_isub]; exact this

/-- Computability is Kripke, for every well-formed code. -/
theorem kr_wf : ∀ l, l ≤ maxLevel → ∀ m X, WF l m X → KR S m X := by
  intro l hl
  refine code_ind _ (fun m => kr_emptyC hW) ?_ ?_ ?_ ?_ ?_ ?_ ?_ l hl
  · intro l m A B hA hB hBf hBw hBn _ _
    exact kr_piC hW (WF.fib (show WF l m (piC m A B) from WFI.pi hA hB hBf hBw hBn)) (IsKV.ne_empty hA.fib.kv)
  · intro l m A B hA hB hBf hBw hBn _ _
    exact kr_sigmaC hW (WF.fib (show WF l m (sigmaC m A B) from WFI.sigma hA hB hBf hBw hBn)) (IsKV.ne_empty hA.fib.kv)
  · intro l m L a0 a1 hL h0 h1 _
    exact kr_pathC hW (WF.fib (show WF l m (pathC m L a0 a1) from WFI.path hL h0 h1)) (IsKV.ne_empty hL.fib.kv)
  · intro l m L hL _
    exact kr_ipiC hW (WF.fib (show WF l m (ipiC m L) from WFI.ipi hL)) (IsKV.ne_empty hL.fib.kv)
  · intro m l _ ih; exact kr_univC hW ih
  · intro l m A φ Tp ep hl hA hφ hn hTp hep hTw hTn hem hen _ ihT
    exact kr_glueC hW hA.fib.kv hφ hTn hTw hl
      (WF.fib (show WF l m (glueC m A φ Tp ep) from WFI.glue hA hφ hn hTp hep hTw hTn hem hen)) ihT
  · intro l m Θ hc hw hpw ih _
    have hΘ : Θ.Good := { hc with fib := fun c j n g pre hp => (hw c j n g pre hp).fib }
    exact kr_dataC hW hΘ (WF.fib (show WF l m (dataC Θ) from WFI.data Θ hc hw hpw)) ih

theorem kr_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : KR S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact kr_wf hW l hl m X hX
  · exact kr_univC hW fun m' X hX => kr_wf hW l hl m' X hX

end

end Model.Canon
