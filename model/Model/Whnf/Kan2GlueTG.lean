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

theorem pairP_isub (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (τ : ISub k' k) :
    (Tm.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)).isub τ =
      .pair (tgT1 (T.isub τ.up) (ψ.subst τ.τ) (u0.isub τ))
        (tgOmega (A.isub τ.up) (φ.subst τ.up.τ) (T.isub τ.up) (e.isub τ.up) (ψ.subst τ.τ) (u0.isub τ)) := by
  have h := (tg_subst_low A φ T e ψ u0 Tm.var τ.τ).1
  rw [dupS_var] at h
  show Tm.pair ((tgT1 T ψ u0).isub τ) ((tgOmega A φ T e ψ u0).isub τ) = _
  rw [tgOmega_isub]
  exact congrArg (Tm.pair · _) h

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


/-- `φ(1)` holds on `δ`. -/
theorem TGD2.φ1ofδ (hδ : (ival (idEnv k) δ).holds) : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds := by
  obtain ⟨l1, H⟩ := D.tgL hW
  rw [holds_iff_entails (H.hφr (r := .one) trivial)]
  exact ent_trans (entails_of_holds D.hδs hδ) (ent_forall_inst D.hδ1 .one)

theorem TGD2.Pd1P (τ : ISub k' k) (hδτ : (ival (idEnv k') (δ.subst τ.τ)).holds) :
    RE2 S k' ((tgFib A φ T e ψ u0).isub τ) (.papp ((tgPd A φ T e ψ u0).isub τ) .one)
      ((Tm.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)).isub τ) := by
  have D' := D.isub hW τ
  have y := pathC_elim1 hW (D'.Pd hW (D'.φ1ofδ hW hδτ) hδτ)
  obtain ⟨eF, -, eP, -, -, -⟩ := tg_isub A φ T e ψ u0 δ τ
  rw [eF, eP, pairP_isub]
  exact y

/-- On `δ`, the extension to the left fibre is the pair `(t1', ω)`. -/
theorem TGD2.extP (hδ : (ival (idEnv k) δ).holds) :
    RE2 S k (tgFib A φ T e ψ u0) (tgExt A φ T e ψ u0 δ) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφ1 := D.φ1ofδ hW hδ
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hent1 := ent_cof_one hW (entails_of_holds hφs hφ1)
  have hext := HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hext)
  have hP := HasTy.restrict (Φ' := .one) trivial (ent_and_intro hent1 (entails_of_holds D.hδs hδ))
    (minimal_to_spec H.hpd)
  have hfib := D.hfib hW hφ1
  have hX := tyCode_of_univ hW hfib
  have hFF := RT2.refl hW hX (D.rFib hW hφ1)
  have hor : I.Entails .one (I.or δ ψ) := ent_trans (entails_of_holds D.hδs hδ) (ent_or_left _ _)
  have hh : (ival (idEnv k) ((I.or δ ψ).subst (ISub.id k).τ)).holds := by
    rw [I_subst_id (show (I.or δ ψ).Scoped k from ⟨D.hδs, H.hψ⟩),
      holds_iff_entails (show (I.or δ ψ).Scoped k from ⟨D.hδs, H.hψ⟩)]
    exact hor
  have hsp := psysTy hW H hφ1 (ISub.id k) hh (r := .one) trivial
  have hFc := closed_of_ty hW hfib
  have hPc := closed_of_ty hW hP
  rw [isub_id_of_closed hFc] at hsp
  rw [tgExt_eq] at hext ⊢
  refine RE2.expandL hW hFF hext hP (stable_hcompFace hW hor hext) ?_
  rw [← isub_up_id_of_closed (closed_ty H.hpsys), psys_isub]
  rw [← isub_id_of_closed hPc] at hP ⊢
  rw [← isub_id_of_closed hFc] at hFF hsp hP ⊢
  refine RE2_split_l hW (I.scoped_subst D.hδs (ISub.id k).sc) (I.scoped_subst H.hψ (ISub.id k).sc)
    (entails_of_holds (I.scoped_subst (show (I.or δ ψ).Scoped k from ⟨D.hδs, H.hψ⟩) (ISub.id k).sc) hh) hFF hsp hP
    (fun k2 σ2 h => ?_) (fun k2 σ2 h => ?_) <;>
  simp only [isub_papp, Tm.isub_isub, I.subst]
  · exact D.Pd1P hW ((ISub.id k).comp σ2)
      ((holds_iff_entails (I.scoped_subst D.hδs ((ISub.id k).comp σ2).sc)).2 (by rw [I_subst_comp]; exact h))
  · have hδτ := holds_isub hW D.hδs hδ ((ISub.id k).comp σ2)
    have hψτ : (ival (idEnv k2) (ψ.subst ((ISub.id k).comp σ2).τ)).holds :=
      (holds_iff_entails (I.scoped_subst H.hψ ((ISub.id k).comp σ2).sc)).2 (by rw [I_subst_comp]; exact h)
    have D' := D.isub hW ((ISub.id k).comp σ2)
    have h1 := D'.φ1ofδ hW hδτ
    have hF' := D'.hfib hW h1
    have hFF' := RT2.refl hW (tyCode_of_univ hW hF') (D'.rFib hW h1)
    have x := D.Ppsi1Pt hW hφ1 ((ISub.id k).comp σ2) hψτ
    have z := D'.pairPQ hW h1 hδτ hψτ
    obtain ⟨eF, -, -, -, -, -⟩ := tg_isub A φ T e ψ u0 δ ((ISub.id k).comp σ2)
    rw [eF, pairQ_isub] at x
    rw [eF, pairP_isub]
    exact RE2.trans hW hFF' x (RE2.symm hW hFF' z)


/-- On `δ`, the contractum of the left transport is the transport in the fibre. -/
theorem TGD2.bdryδ (hδ : (ival (idEnv k) δ).holds) :
    RE2 S k ((Tm.glue A φ T e).dinst .one) (Tm.transpGlueWith δ A φ T e ψ u0) (tgT1 T ψ u0) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hφ1 := D.φ1ofδ hW hδ
  have hφ1s : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφe := entails_of_holds hφ1s hφ1
  have eqL := EqTm.transpGlue D.hty hA0 he0 D.hδs D.hδ1 D.hδ2
  have hL := HasTy.eqR eqL
  have hG1 := minimal_to_spec (H.hGr (r := .one) trivial)
  obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
  have hTT1 := RT2.refl hW (tyCode_of_univ hW hT1) (by
    have := D.rT1 hW hφ1 (ISub.id k); rwa [isub_id_of_closed (closed_of_ty hW hT1)] at this)
  have x := D.extP hW hδ
  rw [tgFib_eq] at x
  have y := (RE2_sigma_elim hW x).1
  have hfP := (RE2.typed y).2.1
  have ht1 := HasTy.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds D.hδs hδ)) (minimal_to_spec H.ht1)
  have z := RE2.reduceR hW hTT1 y (stable_fstBeta hW hfP) ht1
  have g := RE2_glue_of_fiber hW hG1 hφe hTT1 z
  have hGG : RT2 S k ((Tm.glue A φ T e).dinst .one) ((Tm.glue A φ T e).dinst .one) := by
    have := D.rGG k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed (closed_of_ty hW hG)] at this
  rw [transpGlueWith_eq] at hL ⊢
  rw [glue_dinst] at hL hGG ⊢
  exact RE2.expandL hW hGG hL (RE2.typed g).2.1 (stable_glueEl hW hL hφe) g


/-- The equivalences at the end, left against left, under restrictions. -/
theorem TGD2.e1L {k3 : ℕ} (σ : ISub k3 k) (hh : (ival (idEnv k3) ((φ.subst (I.inst0 .one)).subst σ.τ)).holds) :
    RE2 S k3 (Tm.equiv ((T.dinst .one).isub σ) ((A.dinst .one).isub σ)) ((e.dinst .one).isub σ)
      ((e.dinst .one).isub σ) := by
  rw [dinst1_isub, dinst1_isub, dinst1_isub]
  exact D.rEL k3 _ (by rwa [I_inst1_isub] at hh)

theorem TGD2.T1L {k3 : ℕ} (σ : ISub k3 k) (hh : (ival (idEnv k3) ((φ.subst (I.inst0 .one)).subst σ.τ)).holds) :
    RT2 S k3 ((T.dinst .one).isub σ) ((T.dinst .one).isub σ) := by
  rw [dinst1_isub]; exact D.rTT k3 _ (by rwa [I_inst1_isub] at hh)

theorem TGD2.A1L {k3 : ℕ} (σ : ISub k3 k) : RT2 S k3 ((A.dinst .one).isub σ) ((A.dinst .one).isub σ) := by
  rw [dinst1_isub]; exact D.rAA k3 σ .one .one trivial trivial (I_eq_refl _)

section
variable (hψk : (ival (idEnv k) ψ).holds)
include hψk

/-- On `ψ`, the starts at the end of the Glue line. -/
theorem TGD2.u0G1 : RE2 S k ((Tm.glue A φ T e).dinst .one) u0 u0' := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l1, H⟩ := D.tgL hW
  have hGc := closed_of_ty hW hG
  have c := D.cG k (ISub.id k) .one trivial (by rw [I_subst_id H.hψ]; exact hψk)
  rw [isub_cons_id_of_closed hGc, isub_cons_id_of_closed hGc] at c
  have hG1 := HasTy.isubS hW hG (ISub.cons .one trivial (ISub.id k))
  rw [isub_cons_id_of_closed hGc] at hG1
  exact RE2.conv hW (RT2.symm hW (tyCode_of_univ hW hG1) c) D.ha0

/-- On `ψ`, the composition in the base at the end is the composition `a1'`. -/
theorem TGD2.a1ψ : RE2 S k (A.dinst .one) (tgA1 A φ T e ψ u0 δ) (tgA1' A φ e ψ u0) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hψe := entails_of_holds H.hψ hψk
  have hAA := D.hAA1 hW
  have hA1c : (A.dinst .one).closedB 0 k = true := closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))
  have hsc : (I.or (φ.subst (I.inst0 .one)) ψ).Scoped k := ⟨hφs, H.hψ⟩
  have hh : (ival (idEnv k) ((I.or (φ.subst (I.inst0 .one)) ψ).subst (ISub.id k).τ)).holds := by
    rw [I_subst_id hsc, holds_iff_entails hsc]; exact ent_trans hψe (ent_or_right _ _)
  have hsp := asysTy hW H (ISub.id k) hh (r := .one) trivial
  rw [I_subst_id hφs, I_subst_id H.hψ, isub_id_of_closed hA1c, isub_id_of_closed (closed_ty H.ha1'),
    isub_id_of_closed (show (Tm.snd (tgExt A φ T e ψ u0 δ)).closedB 0 k = true by
      simpa [Tm.closedB] using closed_ty H.hext)] at hsp
  have ha1 := D.a1' hW
  have hty := minimal_to_spec H.ha1
  rw [tgA1_eq] at hty ⊢
  have st := stable_hcompFace hW (ent_trans hψe (ent_or_right _ _)) hty
  rw [asys_dinst] at st
  refine RE2.expandL hW hAA hty (RE2.typed ha1).1 st ?_
  refine RE2_split_l hW hφs H.hψ (ent_trans hψe (ent_or_right _ _)) hAA hsp (RE2.typed ha1).1
    (fun k2 σ2 h => ?_) (fun k2 σ2 h => ?_) <;>
  (try simp only [isub_papp, isub_snd, I.subst]) <;>
  (try simp only [(tg_isub A φ T e ψ u0 δ σ2).2.2.2.2.1, tgA1'_isub, dinst_isub_end _ (Or.inr rfl)])
  · have D' := D.isub hW σ2
    have h1 : (ival (idEnv k2) ((φ.subst σ2.up.τ).subst (I.inst0 .one))).holds := by
      rw [← I_phi1_isub, holds_iff_entails (I.scoped_subst hφs σ2.sc)]; exact h
    have hψτ := holds_isub hW H.hψ hψk σ2
    have hAA2 := D'.hAA1 hW
    exact RE2.trans hW hAA2 (D'.extR hW h1 hψτ (s := .neg .one) trivial) (RE2.symm hW hAA2 (D'.a1' hW))
  · have D' := D.isub hW σ2
    exact RE2.reflL hW (D'.hAA1 hW) (D'.a1' hW)


/-- On `ψ`, the composition in the base is the right start unglued. -/
theorem TGD2.a1'U : RE2 S k (A.dinst .one) (tgA1' A φ e ψ u0)
    (.unglue (φ.subst (I.inst0 .one)) (e.dinst .one) u0') := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hψe := entails_of_holds H.hψ hψk
  have hAA := D.hAA1 hW
  have hG1 := minimal_to_spec (H.hGr (r := .one) trivial)
  have hA1 := minimal_to_spec (H.hAr (r := .one) trivial)
  have he1 : HasTy S k (cof .one (φ.subst (I.inst0 .one))) [] (e.dinst .one) (Tm.equiv (T.dinst .one) (A.dinst .one)) :=
    minimal_to_spec (H.her (r := .one) trivial (X := cof .one (φ.subst (I.inst0 .one))) ⟨trivial, hφs⟩
      (ent_and_left _ _) (ent_and_right _ _))
  have hu := D.u0G1 hW hψk
  rw [glue_dinst] at hu
  have hGK : IsTyK S k (.glue (A.dinst .one) (φ.subst (I.inst0 .one)) (T.dinst .one) (e.dinst .one)) := ⟨_, .inl hG1⟩
  have x := RE2_unglue_gen hW hG1 hu (unglue_ty hW hGK ⟨_, hA1, he1⟩ (RE2.typed hu).1)
    (unglue_ty hW hGK ⟨_, hA1, he1⟩ (RE2.typed hu).2.1) hφs (ent_refl _) (ent_refl _) (EqTm.refl he1)
    (fun k3 σ => D.A1L hW σ) (fun k3 σ hh => D.T1L hW σ hh) (fun k3 σ hh => D.e1L hW σ hh)
  have hty := minimal_to_spec H.ha1'
  have st := stable_compFace hW hψe hty
  rw [tgTube_dinst] at st
  exact RE2.expandL hW hAA hty (RE2.typed x).2.1 st x

/-- On `ψ` and `φ(1)`, the first component of the extension is the right start. -/
theorem TGD2.extU (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) :
    RE2 S k (T.dinst .one) (.fst (tgExt A φ T e ψ u0 δ)) u0' := by
  obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
  have hTT1 := RT2.refl hW (tyCode_of_univ hW hT1) (by
    have := D.rT1 hW hφ1 (ISub.id k); rwa [isub_id_of_closed (closed_of_ty hW hT1)] at this)
  have x := D.extQ hW hφ1 hψk
  rw [tgFib_eq] at x
  have y := (RE2_sigma_elim hW x).1
  have u := D.u0T1 hW hφ1 hψk
  have z := RE2.reduceR hW hTT1 y (stable_fstBeta hW (RE2.typed y).2.1) (RE2.typed u).1
  exact RE2.trans hW hTT1 z u

end

end

end

end Model.Whnf
