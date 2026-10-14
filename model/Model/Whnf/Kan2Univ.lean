import Model.Whnf.Kan2PathT

/-!
# The binary Kan operations at universes
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem step_transp_univ {l : ℕ} {φ : I} {a : Tm} (hn : ¬ I.Entails .one φ) :
    step S (.transp (.univ l) φ a) = some a := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

variable (hW : WfSig S)
include hW

/-- The universe clause of a type related to a type whose normal form is a universe. -/
theorem univ_clause {T T' : Tm} {l : ℕ} (hTT : RT2 S k T T') (hR : RedT S k T (.univ l)) :
    ∀ k' (σ : ISub k' k), RedT S k' (T.isub σ) (.univ l) ∧ RedT S k' (T'.isub σ) (.univ l) := by
  have hX : semK S k T = univC k l := (semK_tyEq hW hR.2).trans rfl
  have h := hTT
  unfold RT2 at h
  rw [hX, Comp2_univC] at h
  intro k' σ
  exact h.2 k' σ

/-- A type whose normal form at every restriction is a universe is related to the universe. -/
theorem RT2_toUniv {X : Tm} {l : ℕ} (hX : IsTyK S k X) (h : ∀ k' (σ : ISub k' k), RedT S k' (X.isub σ) (.univ l)) :
    RT2 S k X (.univ l) := by
  have hXc := closed_of_isTyK hW hX
  have h0 := h k (ISub.id k)
  rw [isub_id_of_closed hXc] at h0
  have hsem : semK S k X = univC k l := (semK_tyEq hW h0.2).trans rfl
  unfold RT2
  rw [hsem, Comp2_univC]
  refine ⟨⟨hX, ⟨l, .inr rfl⟩, ?_, ?_, h0.2⟩, fun k' σ => ⟨h k' σ, ⟨redW_self rfl, TyEq.refl _⟩⟩⟩
  · rw [res_id (isKV_univC _), hsem]
  · rw [res_id (isKV_univC _)]; rfl

/-- Transport along related lines whose normal forms are universes. -/
theorem kanT2_univ {T T' : Tm} {l : ℕ} (hTT : RT2 S (k + 1) T T') (hR : RedT S (k + 1) T (.univ l)) :
    KanT2 S k T T' := by
  have hcl := univ_clause hW hTT hR
  intro hLR φ φ' a0 a0' hC hty hty' heq h12 h21 ha0
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hTK : ∀ k3 (σ : ISub k3 (k + 1)), IsTyK S k3 (T.isub σ) := fun k3 σ => ⟨l0, .inl (HasTy.isubS hW hTl' σ)⟩
  have hT0 : ∀ k3 (τ : ISub k3 k), (T.dinst .zero).isub τ = T.isub (ISub.cons .zero trivial τ) := fun k3 τ => by
    rw [isub_dinst]; exact isub_up_dinst T τ .zero trivial
  have hT1 : ∀ k3 (τ : ISub k3 k), (T.dinst .one).isub τ = T.isub (ISub.cons .one trivial τ) := fun k3 τ => by
    rw [isub_dinst]; exact isub_up_dinst T τ .one trivial
  have toU : ∀ k3 (σ : ISub k3 (k + 1)), RT2 S k3 (T.isub σ) (.univ l) := fun k3 σ =>
    RT2_toUniv hW (hTK k3 σ) (fun k4 σ4 => by have := (hcl k4 (σ.comp σ4)).1; rwa [← Tm.isub_isub] at this)
  have hXT : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (T.isub σ)) := fun k3 σ =>
    tyCode_of_univ hW (HasTy.isubS hW hTl' σ)
  have hY : ∀ k3 (τ : ISub k3 k), RT2 S k3 ((T.dinst .zero).isub τ) ((T.dinst .one).isub τ) := by
    intro k3 τ
    rw [hT0, hT1]
    have a := toU k3 (ISub.cons .zero trivial τ)
    have b := toU k3 (ISub.cons .one trivial τ)
    exact RT2.trans hW (hXT _ _) a (RT2.symm hW (hXT _ _) b)
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hX : TyCode k (semK S k (T.dinst .one)) := by
    have := hXT k (ISub.cons .one trivial (ISub.id k)); rwa [isub_cons_id_of_closed hTc] at this
  have hYY : RT2 S k (T.dinst .one) (T.dinst .one) := by
    have := hY k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW hty))] at this
    exact RT2.refl' hW (RT2.tyCode_l hW this hX) this
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty ρ; rwa [isub_dinst] at this
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty' ρ; rwa [isub_dinst] at this
  have eT1 : ∀ k' (ρ : ISub k' k), TyEq S k' ((T.isub ρ.up).dinst .one) ((T'.isub ρ.up).dinst .one) := fun k' ρ => by
    have := (tyEq_dinst hW (Comp2_ty_base hTT).2.2.2.2.2 (r := .one) trivial).isub hW ρ
    rwa [isub_dinst, isub_dinst] at this
  refine RE2.expandBoth hW hX hYY hty hty' (fun k' ρ => a0.isub ρ) (fun k' ρ => a0'.isub ρ)
    (fun k' ρ => ?_) (fun k' ρ => ?_) (fun k' ρ k'' ρ' => ?_)
  · show Red S (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ)) _ ∧ EqTm S k' .one [] _ _ _
    rw [isub_dinst]
    by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (hρT k' ρ)⟩
    · have e1 := eq_transp_ty hW (hρT k' ρ) (hcl (k' + 1) ρ.up).1.2
      exact ⟨(red_transp_ty hf (hcl (k' + 1) ρ.up).1.1.1).trans (.step (step_transp_univ hf) (.refl _)),
        e1.trans (EqTm.transpU (HasTy.eqR e1))⟩
  · show Red S (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ)) _ ∧ EqTm S k' .one [] _ _ _
    rw [isub_dinst]
    by_cases hf : I.Entails .one (φ'.subst ρ.τ)
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (hρT' k' ρ)⟩
    · have e1 := eq_transp_ty hW ((hρT' k' ρ).tyConv (eT1 k' ρ)) (hcl (k' + 1) ρ.up).2.2
      exact ⟨(red_transp_ty hf (hcl (k' + 1) ρ.up).2.1.1).trans (.step (step_transp_univ hf) (.refl _)),
        (e1.trans (EqTm.transpU (HasTy.eqR e1))).tyConv (TyEq.symm (eT1 k' ρ))⟩
  · show RE2 S k'' _ ((a0.isub ρ).isub ρ') (a0'.isub (ρ.comp ρ'))
    rw [Tm.isub_isub]
    exact RE2.conv hW (hY k'' (ρ.comp ρ')) (RE2.isub hW ha0 (ρ.comp ρ'))

end

end Model.Whnf
