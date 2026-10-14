import Model.Whnf.Kan2GlueTF

/-!
# Binary transport in Glue types: the Glue elements

The contracta `transpGlueWith` at a pair of related Glue lines are related (`TGD2.final`), from the
related pieces of `Kan2GlueTP` and `Kan2GlueTF`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

section
variable {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
  (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ')
include D

/-- Where `φ(1)` holds, the composition in the base at the end is the equivalence applied to the extension. -/
theorem TGD2.a1E (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) :
    RE2 S k (A.dinst .one) (tgA1 A φ T e ψ u0 δ) (.app (.fst (e.dinst .one)) (.fst (tgExt A φ T e ψ u0 δ))) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφe := entails_of_holds hφs hφ1
  have hAA := D.hAA1 hW
  have hA1c : (A.dinst .one).closedB 0 k = true := closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))
  have hh : (ival (idEnv k) ((I.or (φ.subst (I.inst0 .one)) ψ).subst (ISub.id k).τ)).holds := by
    rw [I_subst_id (show (I.or (φ.subst (I.inst0 .one)) ψ).Scoped k from ⟨hφs, H.hψ⟩),
      holds_iff_entails (show (I.or (φ.subst (I.inst0 .one)) ψ).Scoped k from ⟨hφs, H.hψ⟩)]
    exact ent_trans hφe (ent_or_left _ _)
  have hsp := asysTy hW H (ISub.id k) hh (r := .one) trivial
  rw [I_subst_id hφs, I_subst_id H.hψ, isub_id_of_closed hA1c, isub_id_of_closed (closed_ty H.ha1'),
    isub_id_of_closed (show (Tm.snd (tgExt A φ T e ψ u0 δ)).closedB 0 k = true by
      simpa [Tm.closedB] using closed_ty H.hext)] at hsp
  have w := D.extSnd hW hφ1
  have x : RE2 S k (A.dinst .one) (.papp (.snd (tgExt A φ T e ψ u0 δ)) (.neg .one))
      (.app (.fst (e.dinst .one)) (.fst (tgExt A φ T e ψ u0 δ))) :=
    RE2.trans hW hAA (pathC_elim2 hW w (s := .neg .one) (s' := .zero) trivial trivial I_eq_neg_one)
      (RE2.trans hW hAA (RE2.symm hW hAA (pathC_elim2 hW w (s := .zero) (s' := .zero) trivial trivial (I_eq_refl _)))
        (pathC_elim0 hW w))
  have hty := minimal_to_spec H.ha1
  rw [tgA1_eq] at hty ⊢
  have st := stable_hcompFace hW (ent_trans hφe (ent_or_left _ _)) hty
  rw [asys_dinst] at st
  exact RE2.expandL hW hAA hty (RE2.typed x).2.1 st
    (RE2.expandL hW hAA hsp (RE2.typed x).2.1 (stable_splitL hW hφe hsp) x)


/-- The contracta of the transports along the Glue lines. -/
theorem TGD2.final : RE2 S k ((Tm.glue A φ T e).dinst .one) (Tm.transpGlueWith δ A φ T e ψ u0)
    (Tm.transpGlueWith δ' A' φ' T' e' ψ' u0') := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  obtain ⟨hφs', lA', hA0', he0'⟩ := glue_data hW hG'
  have eqL := EqTm.transpGlue D.hty hA0 he0 D.hδs D.hδ1 D.hδ2
  have eqR := EqTm.transpGlue D.hty' hA0' he0' D.hδs' D.hδ1' D.hδ2'
  have hEB : EB S k ((Tm.glue A φ T e).dinst .one) (Tm.transpGlueWith δ A φ T e ψ u0)
      (Tm.transpGlueWith δ' A' φ' T' e' ψ' u0') := ⟨HasTy.eqR eqL, HasTy.eqR eqR, eqL.symm.trans (D.heq.trans eqR)⟩
  have hφ1s : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφ1s' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have f12 : I.Entails (φ.subst (I.inst0 .one)) (φ'.subst (I.inst0 .one)) := ent_subst D.f12 _
  have f21 : I.Entails (φ'.subst (I.inst0 .one)) (φ.subst (I.inst0 .one)) := ent_subst D.f21 _
  have hG1 := minimal_to_spec (H.hGr (r := .one) trivial)
  have hG1' := minimal_to_spec (H'.hGr (r := .one) trivial)
  have hGc := closed_of_ty hW hG
  have hGG : RT2 S k ((Tm.glue A φ T e).dinst .one) ((Tm.glue A φ T e).dinst .one) := by
    have := D.rGG k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed hGc] at this
  rw [transpGlueWith_eq, transpGlueWith_eq] at hEB ⊢
  rw [glue_dinst] at hEB hGG ⊢
  by_cases hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds
  · -- the face holds at the end: the fibres
    have hφe := entails_of_holds hφ1s hφ1
    have z := D.ext hW hφ1
    rw [tgFib_eq] at z
    obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
    have hTT1 := RT2.refl hW (tyCode_of_univ hW hT1) (by
      have := D.rT1 hW hφ1 (ISub.id k); rwa [isub_id_of_closed (closed_of_ty hW hT1)] at this)
    have y := RE2_glue_of_fiber hW hG1 hφe hTT1 (RE2_sigma_elim hW z).1
    exact RE2.expand2 hW hGG hEB.1 hEB.2.1 (stable_glueEl hW hEB.1 hφe)
      (stable_glueEl hW hEB.2.1 (ent_trans hφe f12)) y
  -- the face does not hold at the end: the components
  have hφc : ∀ {k3} (σ : ISub k3 k), (ival (idEnv k3) ((φ.subst (I.inst0 .one)).subst σ.τ)).holds →
      (ival (idEnv k3) (φ.subst (ISub.cons .one trivial σ).τ)).holds := fun σ hh => by rwa [I_inst1_isub] at hh
  have hφu : ∀ {k3} (σ : ISub k3 k), (ival (idEnv k3) ((φ.subst (I.inst0 .one)).subst σ.τ)).holds →
      (ival (idEnv k3) ((φ.subst σ.up.τ).subst (I.inst0 .one))).holds := fun σ hh => by rwa [I_phi1_isub] at hh
  have rAσ : ∀ {k3} (σ : ISub k3 k), RT2 S k3 ((A.dinst .one).isub σ) ((A'.dinst .one).isub σ) := fun σ => by
    rw [dinst1_isub, dinst1_isub]; exact D.rA _ σ .one .one trivial trivial (I_eq_refl _)
  have hAAσ : ∀ {k3} (σ : ISub k3 k), RT2 S k3 ((A.dinst .one).isub σ) ((A.dinst .one).isub σ) := fun σ => by
    rw [dinst1_isub]; exact D.rAA _ σ .one .one trivial trivial (I_eq_refl _)
  have hT : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) ((φ.subst (I.inst0 .one)).subst σ.τ)).holds →
      RT2 S k3 ((T.dinst .one).isub σ) ((T'.dinst .one).isub σ) := fun k3 σ hh => by
    rw [dinst1_isub, dinst1_isub]; exact D.rT _ _ (hφc σ hh)
  have hE : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) ((φ.subst (I.inst0 .one)).subst σ.τ)).holds →
      RE2 S k3 (Tm.equiv ((T.dinst .one).isub σ) ((A.dinst .one).isub σ)) ((e.dinst .one).isub σ)
        ((e'.dinst .one).isub σ) := fun k3 σ hh => by
    rw [dinst1_isub, dinst1_isub, dinst1_isub, dinst1_isub]; exact D.rE _ _ (hφc σ hh)
  have hA1c : (A.dinst .one).closedB 0 k = true := closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))
  have rA1 := rAσ (ISub.id k)
  rw [isub_id_of_closed hA1c, isub_id_of_closed (closed_of_ty hW (minimal_to_spec (H'.hAr (r := .one) trivial)))] at rA1
  have ee' := glue_ee hW hG1 hG1' f12 rA1 hT hE
  refine RE2_glueEl_intro hW hG1 hφ1 hEB f12 f21 ee' hGG (fun k3 σ => hAAσ σ)
    (fun k3 σ hh => by rw [dinst1_isub]; exact D.rTT _ _ (hφc σ hh)) (fun k3 σ => ?_) (fun k3 σ hh => ?_)
    (fun k3 σ hh => ?_) (fun k3 σ hh => ?_)
  · rw [(tg_isub A φ T e ψ u0 δ σ).2.2.2.2.2, (tg_isub A' φ' T' e' ψ' u0' δ' σ).2.2.2.2.2, dinst_isub_end _ (.inr rfl)]
    exact (D.isub hW σ).a1 hW
  · have z := (D.isub hW σ).ext hW (hφu σ hh)
    rw [tgFib_eq] at z
    rw [isub_fst, isub_fst, (tg_isub A φ T e ψ u0 δ σ).2.2.2.2.1, (tg_isub A' φ' T' e' ψ' u0' δ' σ).2.2.2.2.1,
      dinst_isub_end _ (.inr rfl)]
    exact (RE2_sigma_elim hW z).1
  · rw [isub_fst, (tg_isub A φ T e ψ u0 δ σ).2.2.2.2.2, (tg_isub A φ T e ψ u0 δ σ).2.2.2.2.1,
      dinst_isub_end _ (.inr rfl), dinst_isub_end _ (.inr rfl)]
    exact (D.isub hW σ).a1E hW (hφu σ hh)
  · have D' := D.isub hW σ
    have h1 := hφu σ hh
    have a1r := D'.a1 hW
    have a1e := D'.a1E hW h1
    have z := D'.ext hW h1
    rw [tgFib_eq] at z
    have hEL := D.rEL k3 (ISub.cons .one trivial σ) (hφc σ hh)
    rw [← isub_up_dinst T σ .one trivial, ← isub_up_dinst A σ .one trivial, ← isub_up_dinst e σ .one trivial] at hEL
    have hAA' : RT2 S k3 ((A.isub σ.up).dinst .one) ((A.isub σ.up).dinst .one) := by
      rw [← dinst_isub_end _ (.inr rfl)]; exact hAAσ σ
    rw [isub_fst, (tg_isub A' φ' T' e' ψ' u0' δ' σ).2.2.2.2.2,
      (tg_isub A' φ' T' e' ψ' u0' δ' σ).2.2.2.2.1, dinst_isub_end _ (.inr rfl), dinst_isub_end _ (.inr rfl)]
    exact RE2.trans hW hAA' (RE2.symm hW hAA' a1r)
      (RE2.trans hW hAA' a1e (RE2_equiv_app hW hEL (RE2_sigma_elim hW z).1))

end

end

end Model.Whnf
