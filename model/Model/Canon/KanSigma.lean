import Model.Canon.KanDerived
import Model.Canon.KanPi

/-!
# Canonicity: the Kan operations at Σ-types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem sigma_dinst (A B : Tm) (r : I) : (Tm.sigma A B).dinst r = .sigma (A.dinst r) (B.dinst r) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, up_var]

variable (hW : WfSig S)
include hW

theorem kanT_sigma {A B : Tm} {l : ℕ} (hsig : HasTy S (k + 1) .one [] (.sigma A B) (.univ l))
    (hA : ∀ k' (ρ : ISub (k' + 1) (k + 1)), KanT S k' (A.isub ρ))
    (hB : ∀ k' (ρ : ISub (k' + 1) (k + 1)) a, RE S (k' + 1) (A.isub ρ) a → KanT S k' ((B.isub ρ).inst a)) :
    KanT S k (.sigma A B) := by
  have hS := sigClosed_of_wfSig hW
  intro φ u0 hty hu0
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hL, hφ, hc, hu0t⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) h0 rfl
  have hAt := HasTy0.sigmaDom hS hL
  have hAc : A.closedB 0 (k + 1) = true := closed_ty hAt
  have hBc : B.closedB 1 (k + 1) = true := closed_ty (HasTy0.sigmaCod hS hL)
  have hcD := EqTm0.sigmaInjDom (A' := (A.dinst .zero).dshift) hc
  rw [sigma_dinst] at hu0t
  have hf0 := HasTy0.fst hu0t
  obtain ⟨htF, eF0, eF1, -⟩ := transpFill_typed hS hAt hφ hcD hf0
  have e := EqTm.transpSigma hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  have hp := HasTy.eqR e
  rw [transpSigma_eq] at hp ⊢
  rw [sigma_dinst] at hp hu0 ⊢
  have hL1 := HasTy0.dsubst hS (Φ := .one) (Γ := []) hL (r := .one) trivial
  have hL0 := HasTy0.dsubst hS (Φ := .one) (Γ := []) hL (r := .zero) trivial
  rw [sigma_dinst] at hL1 hL0
  have hB1 := minimal_to_spec (HasTy0.sigmaCod hS hL1)
  have hB0 := minimal_to_spec (HasTy0.sigmaCod hS hL0)
  have fβ := EqTm.fstBeta (HasTy.fst hp)
  have sβ := EqTm.sndBeta (HasTy.snd hp)
  obtain ⟨hr0, hr1⟩ := RE_sigma_elim hW hu0
  -- the first component
  have KA := hA k (ISub.id (k + 1))
  rw [isub_id_of_closed hAc] at KA
  have hfst := KA φ _ (HasTy.eqR fβ) hr0
  -- the second component
  have hF := RE_transpFill hW hA (minimal_to_spec (HasTy0.transp hAt hφ hcD hf0)) hr0
  have KB := hB k (ISub.id (k + 1)) _ (by rw [isub_id_of_closed hAc]; exact hF)
  rw [isub_id_of_closed hBc] at KB
  have eB1 : EqTm S k .one [] ((B.dinst .one).inst (.fst (.pair (.transp A φ (.fst u0))
      (.transp (B.inst (Tm.transpFill A φ (.fst u0))) φ (.snd u0)))))
      ((B.inst (Tm.transpFill A φ (.fst u0))).dinst .one) (.univ l0) := by
    rw [dinst_inst]
    exact EqTm.subst (EqTm.refl hB1) (EqTm.trans fβ (EqTm.symm (minimal_to_spec_eq eF1)))
  have eB0 : EqTm S k .one [] ((B.dinst .zero).inst (.fst u0)) ((B.inst (Tm.transpFill A φ (.fst u0))).dinst .zero)
      (.univ l0) := by
    rw [dinst_inst]
    exact EqTm.subst (EqTm.refl hB0) (EqTm.symm (minimal_to_spec_eq eF0))
  have hsnd := KB φ _ (HasTy.tyConv (HasTy.eqR sβ) (.inr ⟨l0, eB1⟩)) (hr1.conv_ty hW (.inr ⟨l0, eB0⟩))
  refine RE_sigma_intro hW (minimal_to_spec hL1) hp (hfst.conv hW (TyEq.refl _) (EqTm.symm fβ)) ?_
  exact hsnd.conv hW (.inr ⟨l0, EqTm.symm eB1⟩) (EqTm.symm sβ)

omit hW in
/-- `(B.dshift.inst H).isub ρ` as an instance of the restricted family. -/
theorem dshift_inst_isub (B H : Tm) (ρ : ISub k' (k + 1)) :
    (B.dshift.inst H).isub ρ = (B.isub ρ.tail).inst (H.isub ρ) := by
  rw [isub_inst]
  congr 1
  simp only [Tm.isub, dshift_subst]; rfl

theorem kanH_sigma {A B : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A B) (.univ l))
    (hA : ∀ k' (ρ : ISub k' k), KanH S k' (A.isub ρ))
    (hB : ∀ k' (σ : ISub k' k) a, RE S k' (A.isub σ) a → KanAll S k' ((B.isub σ).inst a)) :
    KanH S k (.sigma A B) := by
  have hS := sigClosed_of_wfSig hW
  intro φ u u0 hty hu hu0
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hSig, hφ, hut, hu0t, hside⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) h0 rfl
  rw [sigma_dshift] at hut
  have hAt := HasTy0.sigmaDom hS hSig
  have hBt := HasTy0.sigmaCod hS hSig
  have hAc : A.closedB 0 k = true := closed_ty hAt
  obtain ⟨hH, hH0, hH1, hHu⟩ := hfill_typed hS hAt hφ (HasTy0.fst hut) (HasTy0.fst hu0t) (EqTm0.fst hside)
  have hfc := HasTy0.hcomp hAt hφ (HasTy0.fst hut) (HasTy0.fst hu0t) (EqTm0.fst hside)
  have e := EqTm.hcompSigma hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  have hp := HasTy.eqR e
  rw [hcompSigma_eq] at hp ⊢
  have fβ := EqTm.fstBeta (HasTy.fst hp)
  have sβ := EqTm.sndBeta (HasTy.snd hp)
  -- the first component
  have hfu : TubeC S k A φ (.fst u) := fun k' σ r hr hh => by
    have := hu k' σ r hr hh
    rw [isub_sigma] at this
    exact (RE_sigma_elim hW this).1
  have KA := hA k (ISub.id k)
  rw [isub_id_of_closed hAc] at KA
  have hfst := KA φ _ _ (minimal_to_spec hfc) hfu (RE_sigma_elim hW hu0).1
  -- the second component: composition along `B[hfill]`
  have hRH := RE_hfill hW hA (minimal_to_spec hfc) hfu (RE_sigma_elim hW hu0).1
  have hCt := minimal_to_spec (HasTy0.subst hS (HasTy0.dwk hS hBt) hH)
  have hBs := minimal_to_spec hBt
  have hCall : KanAll S (k + 1) (B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))) := by
    have key : ∀ k' (ρ : ISub k' (k + 1)), KanAll S k' ((B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))).isub ρ) ∧
        ((B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))).isub ρ).closedB 0 k' = true := by
      intro k' ρ
      have hc := closed_of_ty hW (HasTy.isubS hW hCt ρ)
      rw [dshift_inst_isub] at hc ⊢
      have hRρ : RE S k' (A.isub ρ.tail) ((Tm.hfill A φ (.fst u) (.fst u0)).isub ρ) := by
        have := hRH.isub hW ρ; rwa [dshift_isub_tail] at this
      exact ⟨hB k' ρ.tail _ hRρ, hc⟩
    refine ⟨fun k' ρ => ?_, fun k' ρ => ?_⟩
    · have := ((key k' ρ).1).1 k' (ISub.id k')
      rwa [isub_id_of_closed (key k' ρ).2] at this
    · have := ((key (k' + 1) ρ).1).2 k' (ISub.id (k' + 1))
      rwa [isub_id_of_closed (key (k' + 1) ρ).2] at this
  have eC1 : EqTm S k .one [] (B.inst (.fst (.pair (.hcomp A φ (.fst u) (.fst u0))
      (Tm.comp (B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))) φ (.snd u) (.snd u0)))))
      ((B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))).dinst .one) (.univ l0) := by
    rw [inst_dshift_dinst]
    exact EqTm.subst (EqTm.refl hBs) (EqTm.trans fβ (EqTm.symm (minimal_to_spec_eq hH1)))
  have hcomp := RE_comp hW hCall (HasTy.tyConv (HasTy.eqR sβ) (.inr ⟨l0, eC1⟩)) (fun k' σ r hr hh => ?_) ?_
  · refine RE_sigma_intro hW hsig hp (hfst.conv hW (TyEq.refl _) (EqTm.symm fβ)) ?_
    exact hcomp.conv hW (.inr ⟨l0, EqTm.symm eC1⟩) (EqTm.symm sβ)
  · rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r hr, dshift_inst_isub]
    have h1 := hu k' σ r hr hh
    rw [isub_sigma, isub_up_dinst _ σ r hr] at h1
    have h2 := (RE_sigma_elim hW h1).2
    have hAσ := HasTy0.isub hS (Ψ' := k') (Φ' := .one) (τ := σ.τ) hAt (fun i hi => σ.sc i hi) (ent_refl _)
      (Wf0.nil trivial)
    have hBσ := HasTy0.isub hS (Ψ' := k') (Φ' := .one) (τ := σ.τ) hBt (fun i hi => σ.sc i hi) (ent_refl _)
      (Wf0.cons hAσ)
    have eH := EqTm0.isub hS (Ψ' := k') (Φ' := .one) (τ := (ISub.cons r hr σ).τ) hHu
      (fun i hi => (ISub.cons r hr σ).sc i hi)
      (by show I.Entails .one (I.and I.one.shift (φ.shift.subst (ISub.cons r hr σ).τ))
          rw [I_shift_cons]; exact ent_cof_one hW (entails_of_holds (I.scoped_subst hφ σ.sc) hh))
      (Wf0.nil trivial)
    have eH' := minimal_to_spec_eq eH
    rw [← isub_eq_subst, ← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons] at eH'
    have eT := EqTm.subst (EqTm.refl (minimal_to_spec hBσ)) (EqTm.symm eH')
    exact h2.conv_ty hW (.inr ⟨l0, eT⟩)
  · rw [inst_dshift_dinst]
    exact (RE_sigma_elim hW hu0).2.conv_ty hW
      (.inr ⟨l0, EqTm.subst (EqTm.refl hBs) (EqTm.symm (minimal_to_spec_eq hH0))⟩)

end

end Model.Canon
