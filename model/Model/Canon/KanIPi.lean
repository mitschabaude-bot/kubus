import Model.Canon.KanPi

/-!
# Canonicity: the Kan operations at interval Π-types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem hcompIPi_body (A u u0 : Tm) (φ : I) (r : I) : ∃ t, Tm.hcompIPi A φ u u0 = .plam t ∧
    t.dinst r = .hcomp (A.dinst r) φ (.papp u r.shift) (.papp u0 r) := by
  refine ⟨_, rfl, ?_⟩
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, subst_subst]
  have hφ : φ.shift.subst (I.inst0 r) = φ := by simp only [I.shift, I_ren_subst]; exact I_subst_var φ
  rw [hφ]
  congr 2
  · exact subst_id_of (fun n => rfl) (fun i => by rcases i with _ | i <;> rfl) u
  · exact dshift_dinst u0 r

theorem isub_hcompIPi (A u u0 : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.hcompIPi A φ u u0).isub σ = Tm.hcompIPi (A.isub σ.up) (φ.subst σ.τ) (u.isub σ.up) (u0.isub σ) := by
  show (Tm.hcompIPi A φ u u0).subst .var σ.τ = _
  rw [hcompIPi_subst, show dupS Tm.var = Tm.var from funext fun n => rfl]; rfl

theorem shift_up_inst0 (r : I) (τ : ℕ → I) (r' : I) : (r.shift.subst (I.up τ)).subst (I.inst0 r') = r.subst τ := by
  rw [I_shift_subst_up]; simp only [I.shift, I_ren_subst]; exact I_subst_var _


theorem transpIPi_body (A u0 : Tm) (φ : I) (r : I) : ∃ t, Tm.transpIPi A φ u0 = .plam t ∧
    t.dinst r = .transp (A.subst .var (fun i => (swapI i).subst (I.up (I.inst0 r)))) φ (.papp u0 r) := by
  refine ⟨_, rfl, ?_⟩
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, subst_subst]
  have hφ : φ.shift.subst (I.inst0 r) = φ := by simp only [I.shift, I_ren_subst]; exact I_subst_var φ
  rw [hφ]
  congr 2
  · exact dshift_dinst u0 r

theorem isub_transpIPi (A u0 : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.transpIPi A φ u0).isub σ = Tm.transpIPi (A.isub σ.up.up) (φ.subst σ.τ) (u0.isub σ) := by
  show (Tm.transpIPi A φ u0).subst .var σ.τ = _
  rw [transpIPi_subst, show dupS (dupS Tm.var) = Tm.var from funext fun n => rfl]; rfl

variable (hW : WfSig S)
include hW

theorem kanH_ipi {A : Tm} {l : ℕ} (hipi : HasTy S k .one [] (.ipi A) (.univ l))
    (hA : ∀ k' (ρ : ISub k' (k + 1)), KanH S k' (A.isub ρ)) : KanH S k (.ipi A) := by
  intro φ u u0 hty hu hu0
  have e := EqTm.hcompIPi hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  refine RE_ipi_intro hW hipi (HasTy.eqR e) fun k' σ r hr => ?_
  rw [isub_hcompIPi]
  have hf := HasTy.isubS hW (HasTy.eqR e) σ
  rw [isub_hcompIPi, isub_ipi] at hf
  obtain ⟨t, ht, htr⟩ := hcompIPi_body (A.isub σ.up) (u.isub σ.up) (u0.isub σ) (φ.subst σ.τ) r
  rw [ht] at hf ⊢
  have hβ := EqTm.pathBeta (HasTy.iapp hf hr)
  rw [htr] at hβ
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm hβ)
  have KH := hA k' (ISub.cons r hr σ)
  rw [← isub_up_dinst _ σ r hr] at KH
  refine KH _ _ _ (HasTy.eqR hβ) (fun k'' σ' r' hr' hh => ?_) ?_
  · have h1 := hu k'' (σ.comp σ') r' hr' (by rw [I_subst_comp]; exact hh)
    rw [isub_ipi] at h1
    have h2 := RE_ipi_elim hW h1 (r.subst σ'.τ) (I.scoped_subst hr σ'.sc)
    rw [isub_dinst, Tm.isub_isub, ← ISub.up_comp]
    show RE S k'' _ (Tm.papp ((u.isub σ.up).isub σ'.up |>.dinst r') ((r.shift.subst σ'.up.τ).subst (I.inst0 r')))
    rw [show (r.shift.subst σ'.up.τ).subst (I.inst0 r') = r.subst σ'.τ from shift_up_inst0 r σ'.τ r',
      Tm.isub_isub, ← ISub.up_comp]
    exact h2
  · have h1 := hu0.isub hW σ
    rw [isub_ipi] at h1
    exact RE_ipi_elim hW h1 r hr

theorem kanT_ipi {A : Tm} {l : ℕ} (hipi : HasTy S (k + 1) .one [] (.ipi A) (.univ l))
    (hA : ∀ k' (ρ : ISub (k' + 1) (k + 2)), KanT S k' (A.isub ρ)) : KanT S k (.ipi A) := by
  have hS := sigClosed_of_wfSig hW
  intro φ u0 hty hu0
  have e := EqTm.transpIPi hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  have hAl := HasTy.ipiLine hipi
  have hipi1 := minimal_to_spec (HasTy0.dsubst hS (Φ := .one) (Γ := []) (spec_to_minimal hW hipi) (r := .one) trivial)
  refine RE_ipi_intro hW hipi1 (HasTy.eqR e) fun k' σ r hr => ?_
  obtain ⟨t, ht, htr⟩ := transpIPi_body (A.isub σ.up.up) (u0.isub σ) (φ.subst σ.τ) r
  have hf := HasTy.isubS hW (HasTy.eqR e) σ
  rw [isub_transpIPi, ht] at hf
  rw [isub_transpIPi, ht]
  have hβ := EqTm.pathBeta (HasTy.iapp hf hr)
  rw [htr] at hβ
  -- the line at the interval argument `r`
  let τr : ℕ → I := fun i => (swapI i).subst (I.up (I.inst0 r))
  have hsc : ∀ i < k' + 2, (τr i).Scoped (k' + 1) := fun i hi => by
    rcases i with _ | _ | i
    · exact I.scoped_shift hr
    · show 0 < k' + 1; omega
    · show i + 1 < k' + 1; omega
  have hAσ : (A.isub σ.up.up).closedB 0 (k' + 2) = true := closed_of_ty hW (HasTy.isubS hW hAl σ.up.up)
  have KT := hA k' (σ.up.up.comp (ISub.ofFun (k' + 2) τr hsc))
  rw [← Tm.isub_isub, isub_ofFun hAσ] at KT
  have E : ∀ b : I, b = .zero ∨ b = .one → ((A.isub σ.up.up).subst .var τr).dinst b =
      ((A.subst .var (I.up (I.inst0 b))).isub σ.up).dinst r := by
    intro b hb
    simp only [Tm.dinst, Tm.dsubst, Tm.isub, subst_subst]
    refine subst_congr (fun _ => rfl) (fun i => ?_) A
    rcases i with _ | _ | i
    · show (r.shift.subst (I.inst0 b)) = r
      simp only [I.shift, I_ren_subst]; exact I_subst_var r
    · rcases hb with rfl | rfl <;> rfl
    · show (((σ.τ i).shift.shift).subst τr).subst (I.inst0 b) = ((σ.τ i).shift).subst (I.inst0 r)
      simp only [I.shift, I_ren_subst, I_subst_subst]
      exact I_subst_congr (fun j => by simp [τr, swapI, I.up, I.inst0, I.subst, I.shift, I.ren]) _
  have h1 := hu0.isub hW σ
  have h2 := RE_ipi_elim hW (L := (A.subst .var (I.up (I.inst0 .zero))).isub σ.up) h1 r hr
  have htyT : HasTy S k' .one [] (.transp ((A.isub σ.up.up).subst .var τr) (φ.subst σ.τ) (.papp (u0.isub σ) r))
      (((A.isub σ.up.up).subst .var τr).dinst .one) := by
    rw [E .one (.inr rfl)]; exact HasTy.eqR hβ
  have res := KT (φ.subst σ.τ) _ htyT (by rw [E .zero (.inl rfl)]; exact h2)
  rw [E .one (.inr rfl)] at res
  exact res.conv hW (TyEq.refl _) (EqTm.symm hβ)

end

end Model.Canon
