import Model.Whnf.Unfold2
import Model.Canon.KripkeAll

/-!
# The binary relation is stable under restriction
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-- The binary relations are Kripke: stable under every interval substitution. -/
def KR2 (S : Sig) (m : ℕ) (X : V) : Prop :=
  ∀ k (f : Hom k m) k' (σ : ISub k' k) (A A' t t' : Tm),
    ((Comp2 S X m k f).ty A A' → (Comp2 S X m k' (f.comp σ.hom)).ty (A.isub σ) (A'.isub σ)) ∧
    ((Comp2 S X m k f).el A t t' → (Comp2 S X m k' (f.comp σ.hom)).el (A.isub σ) (t.isub σ) (t'.isub σ))

variable (hW : WfSig S)
include hW

theorem EB.isub {A t t' : Tm} (h : EB S k A t t') (σ : ISub k' k) : EB S k' (A.isub σ) (t.isub σ) (t'.isub σ) :=
  ⟨HasTy.isubS hW h.1 σ, HasTy.isubS hW h.2.1 σ, EqTm.isubS hW h.2.2 σ⟩

theorem base_isub {X : V} {A A' : Tm}
    (h : IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = X ∧ semK S k A' = X ∧ TyEq S k A A') (σ : ISub k' k) :
    IsTyK S k' (A.isub σ) ∧ IsTyK S k' (A'.isub σ) ∧ semK S k' (A.isub σ) = res σ.hom X ∧
      semK S k' (A'.isub σ) = res σ.hom X ∧ TyEq S k' (A.isub σ) (A'.isub σ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.isub hW σ, h2.isub hW σ, by rw [semK_isubTy hW h1 σ, h3], by rw [semK_isubTy hW h2 σ, h4],
    h5.isub hW σ⟩

omit hW in
theorem cohPi_isub {A B : V} {f : Hom k m} {T : Tm} (h : cohPi S A B f T) (σ0 : ISub k' k) :
    cohPi S A B (f.comp σ0.hom) (T.isub σ0) := by
  intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
  rw [Tm.isub_isub] at h1 h2
  have := h k1 (σ0.comp σ) k2 σ' A1 B1 A2 B2 h1 (by rwa [ISub.comp_assoc])
  rw [ISub.comp_assoc] at this; rwa [ISub.comp_hom]

omit hW in
theorem cohSigma_isub {A B : V} {f : Hom k m} {T : Tm} (h : cohSigma S A B f T) (σ0 : ISub k' k) :
    cohSigma S A B (f.comp σ0.hom) (T.isub σ0) := by
  intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
  rw [Tm.isub_isub] at h1 h2
  have := h k1 (σ0.comp σ) k2 σ' A1 B1 A2 B2 h1 (by rwa [ISub.comp_assoc])
  rw [ISub.comp_assoc] at this; rwa [ISub.comp_hom]

omit hW in
theorem cohPath_isub {L : V} {f : Hom k m} {T : Tm} (h : cohPath S L f T) (σ0 : ISub k' k) :
    cohPath S L (f.comp σ0.hom) (T.isub σ0) := by
  intro k1 σ k2 σ' L1 b0 b1 L2 c0 c1 h1 h2
  rw [Tm.isub_isub] at h1 h2
  have := h k1 (σ0.comp σ) k2 σ' L1 b0 b1 L2 c0 c1 h1 (by rwa [ISub.comp_assoc])
  rw [ISub.comp_assoc] at this; rwa [lift_hom_comp]

omit hW in
theorem cohIPi_isub {L : V} {f : Hom k m} {T : Tm} (h : cohIPi S L f T) (σ0 : ISub k' k) :
    cohIPi S L (f.comp σ0.hom) (T.isub σ0) := by
  intro k1 σ k2 σ' L1 L2 h1 h2
  rw [Tm.isub_isub] at h1 h2
  have := h k1 (σ0.comp σ) k2 σ' L1 L2 h1 (by rwa [ISub.comp_assoc])
  rw [ISub.comp_assoc] at this; rwa [lift_hom_comp]

theorem kr2_piC {A B : V} (hX : Fib (piC m A B) m) (hA : A ≠ ∅) : KR2 S m (piC m A B) := by
  intro k f k' σ T T' t t'
  rw [Comp2_piC A B hA, Comp2_piC A B hA]
  constructor
  · rintro ⟨hb, hall, hc, hc'⟩
    refine ⟨?_, fun k'' σ' => ?_, cohPi_isub hc σ, cohPi_isub hc' σ⟩
    · have := base_isub hW hb σ; rwa [res_res] at this
    · obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k'' (σ.comp σ')
      refine ⟨A1, B1, A1', B1', by rw [Tm.isub_isub]; exact h1, by rw [Tm.isub_isub]; exact h2, ?_, ?_⟩
      · rw [ISub.comp_hom]; exact h3
      · intro a a' ha; rw [ISub.comp_hom] at ha ⊢; exact h4 a a' ha
  · rintro ⟨he, hmem, -, hall⟩
    refine ⟨he.isub hW σ, mem_isub hW hX he.1 hmem σ, he.isub hW σ, fun k'' σ' => ?_⟩
    obtain ⟨A1, B1, h1, h2⟩ := hall k'' (σ.comp σ')
    refine ⟨A1, B1, by rw [Tm.isub_isub]; exact h1, fun a a' ha => ?_⟩
    simp only [ISub.id_comp, ISub.comp_hom] at ha h2 ⊢
    rw [Tm.isub_isub, Tm.isub_isub]
    exact h2 a a' ha

theorem kr2_sigmaC {A B : V} (hX : Fib (sigmaC m A B) m) (hA : A ≠ ∅) : KR2 S m (sigmaC m A B) := by
  intro k f k' σ T T' t t'
  rw [Comp2_sigmaC A B hA, Comp2_sigmaC A B hA]
  constructor
  · rintro ⟨hb, hall, hc, hc'⟩
    refine ⟨?_, fun k'' σ' => ?_, cohSigma_isub hc σ, cohSigma_isub hc' σ⟩
    · have := base_isub hW hb σ; rwa [res_res] at this
    · obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k'' (σ.comp σ')
      refine ⟨A1, B1, A1', B1', by rw [Tm.isub_isub]; exact h1, by rw [Tm.isub_isub]; exact h2, ?_, ?_⟩
      · rw [ISub.comp_hom]; exact h3
      · intro a a' ha; rw [ISub.comp_hom] at ha ⊢; exact h4 a a' ha
  · rintro ⟨he, hmem, -, hall⟩
    refine ⟨he.isub hW σ, mem_isub hW hX he.1 hmem σ, he.isub hW σ, fun k'' σ' => ?_⟩
    obtain ⟨A1, B1, h1, h2, h3⟩ := hall k'' (σ.comp σ')
    refine ⟨A1, B1, by rw [Tm.isub_isub]; exact h1, ?_, ?_⟩
    · simp only [ISub.id_comp, ISub.comp_hom] at h2 ⊢; rw [Tm.isub_isub, Tm.isub_isub]; exact h2
    · simp only [ISub.id_comp, ISub.comp_hom] at h3 ⊢; rw [Tm.isub_isub, Tm.isub_isub]; exact h3

theorem kr2_pathC {L a0 a1 : V} (hX : Fib (pathC m L a0 a1) m) (hL : L ≠ ∅) : KR2 S m (pathC m L a0 a1) := by
  intro k f k' σ T T' t t'
  rw [Comp2_pathC L a0 a1 hL, Comp2_pathC L a0 a1 hL]
  constructor
  · rintro ⟨hb, hall, hc, hc'⟩
    refine ⟨?_, fun k'' σ' => ?_, cohPath_isub hc σ, cohPath_isub hc' σ⟩
    · have := base_isub hW hb σ; rwa [res_res] at this
    · obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, hrr, h4, h5⟩ := hall k'' (σ.comp σ')
      refine ⟨L1, b0, b1, L1', b0', b1', by rw [Tm.isub_isub]; exact h1, by rw [Tm.isub_isub]; exact h2, ?_, ?_, ?_, ?_⟩
      · rw [lift_hom_comp]; exact h3
      · intro r r' hr hr' he; rw [lift_cons]; exact hrr r r' hr hr' he
      · rw [lift_cons]; exact h4
      · rw [lift_cons]; exact h5
  · rintro ⟨he, hmem, -, hall⟩
    refine ⟨he.isub hW σ, mem_isub hW hX he.1 hmem σ, he.isub hW σ, fun k'' σ' => ?_⟩
    obtain ⟨L1, b0, b1, h1, h2, h3, h4⟩ := hall k'' (σ.comp σ')
    simp only [ISub.id_comp] at h2 h3 h4 ⊢
    refine ⟨L1, b0, b1, by rw [Tm.isub_isub]; exact h1, fun r r' hr hr' he => ?_, ?_, ?_⟩
    · rw [lift_cons, Tm.isub_isub, Tm.isub_isub]; exact h2 r r' hr hr' he
    · rw [lift_cons, Tm.isub_isub]; exact h3
    · rw [lift_cons, Tm.isub_isub]; exact h4

theorem kr2_ipiC {L : V} (hX : Fib (ipiC m L) m) (hL : L ≠ ∅) : KR2 S m (ipiC m L) := by
  intro k f k' σ T T' t t'
  rw [Comp2_ipiC L hL, Comp2_ipiC L hL]
  constructor
  · rintro ⟨hb, hall, hc, hc'⟩
    refine ⟨?_, fun k'' σ' => ?_, cohIPi_isub hc σ, cohIPi_isub hc' σ⟩
    · have := base_isub hW hb σ; rwa [res_res] at this
    · obtain ⟨L1, L1', h1, h2, h3, hrr⟩ := hall k'' (σ.comp σ')
      refine ⟨L1, L1', by rw [Tm.isub_isub]; exact h1, by rw [Tm.isub_isub]; exact h2, ?_, ?_⟩
      · rw [lift_hom_comp]; exact h3
      · intro r r' hr hr' he; rw [lift_cons]; exact hrr r r' hr hr' he
  · rintro ⟨he, hmem, -, hall⟩
    refine ⟨he.isub hW σ, mem_isub hW hX he.1 hmem σ, he.isub hW σ, fun k'' σ' => ?_⟩
    obtain ⟨L1, h1, h2⟩ := hall k'' (σ.comp σ')
    refine ⟨L1, by rw [Tm.isub_isub]; exact h1, fun r r' hr hr' he => ?_⟩
    have := h2 r r' hr hr' he
    simp only [ISub.id_comp] at this ⊢
    rw [lift_cons, Tm.isub_isub, Tm.isub_isub]; exact this

theorem kr2_emptyC : KR2 S m (emptyC m) := by
  intro k f k' σ T T' t t'
  rw [Comp2_emptyC, Comp2_emptyC]
  refine ⟨fun hb => ?_, fun h => h⟩
  have := base_isub hW hb σ; rwa [res_res] at this

theorem kr2_univC {l : ℕ} (ih : ∀ m' X, WF l m' X → KR2 S m' X) : KR2 S m (univC m l) := by
  intro k f k' σ T T' t t'
  rw [Comp2_univC, Comp2_univC]
  constructor
  · rintro ⟨hb, hall⟩
    refine ⟨?_, fun k'' σ' => ?_⟩
    · have := base_isub hW hb σ; rwa [res_res] at this
    · rw [Tm.isub_isub, Tm.isub_isub]; exact hall k'' (σ.comp σ')
  · rintro ⟨he, hmem, hm, hty⟩
    have ht := he.1
    have hm' : semK S k' (t.isub σ) ∈ ZFSet.sep (WF l k') (Vt l) := by
      rw [ZFSet.mem_sep] at hm ⊢
      rw [semK_isubS hW ht]
      exact ⟨res_mem_Vt hm.1 _, hm.2.res _⟩
    refine ⟨he.isub hW σ, ?_, hm', ?_⟩
    · rw [semK_isubS hW ht, El_res, Hom.comp_id]
      rw [El_res, Hom.comp_id] at hmem
      exact (WF.fib (show WF (l + 1) m (univC m l) from wf_univC)).elRes _ _ _ hmem _ _
    · have hY : WF l k (semK S k t) := (ZFSet.mem_sep.1 hm).2
      have := ((ih k _ hY) k (Hom.id k) k' σ t t' t t).1 hty
      rw [Hom.id_comp] at this
      rw [semK_isubS hW ht, ← Comp2_eq_res (IsKV.ne_empty hY.fib.kv) σ.hom]
      exact this

theorem kr2_glueC {l : ℕ} {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTw : ∀ k (f : Hom k m), (φ.restr f).holds → WF l k (dat Tp k f))
    (hX : Fib (glueC m A φ Tp ep) m)
    (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KR2 S k (dat Tp k f)) :
    KR2 S m (glueC m A φ Tp ep) := by
  have hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f) := fun k f hh => (hTw k f hh).fib.kv
  intro k f k' σ T T' t t'
  rw [Comp2_glueC_at hφ hTp hTkv f, Comp2_glueC_at hφ hTp hTkv (f.comp σ.hom)]
  by_cases hf : (φ.restr f).holds
  · have hfσ : (φ.restr (f.comp σ.hom)).holds := by
      rw [← Cof.restr_restr]; exact (hφ.restr f).holds_restr hf _
    rw [if_pos hf, if_pos hfσ, ← hTp k f hf k' σ.hom, ← Comp2_eq_res (IsKV.ne_empty (hTkv k f hf))]
    have := ihT k f hf k (Hom.id k) k' σ T T' t t'
    rwa [Hom.id_comp] at this
  rw [if_neg hf, Comp2_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr f) hf]
  simp only [Comp2_res (IsKV.ne_empty hA), dat_res, Cof.restr_restr]
  have hG : glueC k (res f A) (φ.restr f) (res f Tp) (res f ep) = res f (glueC m A φ Tp ep) := by
    rw [res_glueC hTp hTkv hφ f, if_neg hf]
  by_cases hfσ : (φ.restr (f.comp σ.hom)).holds
  · rw [if_pos hfσ]
    constructor
    · rintro ⟨-, hall⟩
      have := hall k' σ
      rwa [if_pos hfσ] at this
    · rintro ⟨-, -, -, hall⟩
      have := hall k' σ
      rwa [if_pos hfσ] at this
  · rw [if_neg hfσ, Comp2_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr _) hfσ]
    simp only [Comp2_res (IsKV.ne_empty hA), dat_res, Cof.restr_restr]
    have hG' : glueC k' (res (f.comp σ.hom) A) (φ.restr (f.comp σ.hom)) (res (f.comp σ.hom) Tp)
        (res (f.comp σ.hom) ep) = res (f.comp σ.hom) (glueC m A φ Tp ep) := by
      rw [res_glueC hTp hTkv hφ _, if_neg hfσ]
    constructor
    · rintro ⟨hb, hall⟩
      refine ⟨?_, fun k'' σ' => ?_⟩
      · have := base_isub hW hb σ
        simp only [hG, res_res, Hom.comp_id] at this
        simp only [hG', res_res, Hom.comp_id]; exact this
      · have := hall k'' (σ.comp σ')
        simp only [ISub.comp_hom, Tm.isub_isub, ISub.comp_assoc] at this ⊢
        exact this
    · rintro ⟨he, hmem, -, hall⟩
      have hmem' : semK S k' (t.isub σ) ∈ El (res (Hom.id k') (res (f.comp σ.hom) (glueC m A φ Tp ep))) (Hom.id k') := by
        rw [hG, res_res, Hom.comp_id] at hmem
        have := mem_isub hW hX he.1 hmem σ
        rwa [res_res, Hom.comp_id]
      refine ⟨he.isub hW σ, by rw [hG']; exact hmem', he.isub hW σ, fun k'' σ' => ?_⟩
      have := hall k'' (σ.comp σ')
      simp only [ISub.comp_hom, Tm.isub_isub] at this ⊢
      exact this

end

end Model.Whnf
