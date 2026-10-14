import Model.Whnf.Kan2DataHIT

/-!
# The binary transport at inductive types without parameters

Transport along a line whose normal forms are an inductive type without parameters is the identity
(`transpData0`), and the line is constant: its normal forms are all `data d []`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem step_transp_data0 {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (h0 : D.params = [])
    {ps a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) : step S (.transp (.data d ps) φ a) = some a := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn', hD, h0]

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (h0 : D.params = [])
include hW hD h0

/-- The parameters of a typed inductive type without parameters are empty. -/
theorem params_nil {ps : Tm} {l : ℕ} (h : HasTy S k .one [] (.data d ps) (.univ l)) : ps = Tm.ofList [] := by
  obtain ⟨D', hD', hPt⟩ := gen_data_tele (spec_to_minimal hW h) rfl
  rw [hD] at hD'; cases hD'
  have hl := data_len_of hW (⟨_, .inl h⟩ : IsTyK S k (.data d ps))
  rw [dataD_eq hW hD, h0] at hl
  rw [tele_isList hPt, List.eq_nil_of_length_eq_zero hl]

/-- A type related to itself whose normal form is an inductive type without parameters is related to
`data d []`. -/
theorem RT2_data0 {T ps : Tm} (hTT : RT2 S k T T) (hR : RedT S k T (.data d ps)) :
    RT2 S k T (.data d (Tm.ofList [])) := by
  have h := RT2_data_whnf hW hD hTT hR
  rwa [params_nil hW hD h0 (data_whnf_ty hW hD (Comp2_ty_base hTT).2.1 hR)] at h

/-- Transport along related lines whose normal forms are an inductive type without parameters. -/
theorem kanT2_data0 {T T' ps : Tm} (hTT : RT2 S (k + 1) T T') (hR : RedT S (k + 1) T (.data d ps)) :
    KanT2 S k T T' := by
  intro hLR φ φ' a0 a0' hC hty hty' heq h12 h21 ha0
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hXT0 : TyCode (k + 1) (semK S (k + 1) T) := tyCode_of_univ hW hTl'
  have hTTd : RT2 S (k + 1) T T := RT2.refl hW hXT0 hTT
  have hw := fun k3 (σ : ISub k3 (k + 1)) => data_whnf_pair hW hD hTT hR σ
  choose P1 P1' hw using hw
  have hT0 : ∀ k3 (τ : ISub k3 k), (T.dinst .zero).isub τ = T.isub (ISub.cons .zero trivial τ) := fun k3 τ => by
    rw [isub_dinst]; exact isub_up_dinst T τ .zero trivial
  have hT1 : ∀ k3 (τ : ISub k3 k), (T.dinst .one).isub τ = T.isub (ISub.cons .one trivial τ) := fun k3 τ => by
    rw [isub_dinst]; exact isub_up_dinst T τ .one trivial
  have hXT : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (T.isub σ)) := fun k3 σ =>
    tyCode_of_univ hW (HasTy.isubS hW hTl' σ)
  have toU : ∀ k3 (σ : ISub k3 (k + 1)), RT2 S k3 (T.isub σ) (.data d (Tm.ofList [])) := fun k3 σ =>
    RT2_data0 hW hD h0 (RT2.isub hW hXT0 hTTd σ) (hw k3 σ).1
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
    · have e1 := eq_transp_ty hW (hρT k' ρ) (hw (k' + 1) ρ.up).1.2
      exact ⟨(red_transp_ty hf (hw (k' + 1) ρ.up).1.1.1).trans (.step (step_transp_data0 hD h0 hf) (.refl _)),
        e1.trans (EqTm.transpData0 hD h0 (HasTy.eqR e1))⟩
  · show Red S (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ)) _ ∧ EqTm S k' .one [] _ _ _
    rw [isub_dinst]
    by_cases hf : I.Entails .one (φ'.subst ρ.τ)
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (hρT' k' ρ)⟩
    · have e1 := eq_transp_ty hW ((hρT' k' ρ).tyConv (eT1 k' ρ)) (hw (k' + 1) ρ.up).2.2
      exact ⟨(red_transp_ty hf (hw (k' + 1) ρ.up).2.1.1).trans (.step (step_transp_data0 hD h0 hf) (.refl _)),
        (e1.trans (EqTm.transpData0 hD h0 (HasTy.eqR e1))).tyConv (TyEq.symm (eT1 k' ρ))⟩
  · show RE2 S k'' _ ((a0.isub ρ).isub ρ') (a0'.isub (ρ.comp ρ'))
    rw [Tm.isub_isub]
    exact RE2.conv hW (hY k'' (ρ.comp ρ')) (RE2.isub hW ha0 (ρ.comp ρ'))

end

end Model.Whnf
