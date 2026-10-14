import Model.Whnf.Kan2GlueTP

/-!
# Binary transport in Glue types: the fibres of the equivalence at the end of the line

Where `φ(1)` holds, the fibres `tgFib` of `e(1)` over the compositions `a1'` are related, contractible
(`TGD2.c`) and have compositions (`TGD2.fibK`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' : ℕ}

theorem dinst1_isub (X : Tm) (σ : ISub k' k) : (X.dinst .one).isub σ = X.isub (ISub.cons .one trivial σ) := by
  rw [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial]

theorem I_inst1_isub (φ : I) (σ : ISub k' k) :
    (φ.subst (I.inst0 .one)).subst σ.τ = φ.subst (ISub.cons .one trivial σ).τ := by
  rw [I_subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl

theorem fibB_isub_inst (X f y a : Tm) (σ : ISub k' k) :
    ((Tm.pathC X.shift (.app f.shift (.var 0)) y.shift).isub σ).inst a =
      Tm.pathC (X.isub σ) (.app (f.isub σ) a) (y.isub σ) := by
  rw [pathC_isub, isub_shift, isub_shift]
  have eapp : (Tm.app f.shift (.var 0)).isub σ = .app (f.isub σ).shift (.var 0) := by
    show Tm.app (f.shift.isub σ) (Tm.var 0) = _; rw [isub_shift]
  rw [eapp, P_inst]

variable (hW : WfSig S)
include hW

theorem HasTy.top {X : Tm} {l : ℕ} (h : HasTy S k .one [] X (.univ l)) : HasTy S k .one [] X (.univ maxLevel) :=
  h.cumulTo (lvl_of_ty hW h) le_rfl

section
variable {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
  (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ')
  (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds)
include D hφ1

/-- Where `φ(1)` holds, the face holds at the end of the line, under every restriction. -/
theorem TGD2.φ1At (σ : ISub k' k) : (ival (idEnv k') (φ.subst (ISub.cons .one trivial σ).τ)).holds := by
  obtain ⟨-, -, -, hφs⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  have hs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have := holds_isub hW hs hφ1 σ
  rwa [I_inst1_isub] at this

theorem TGD2.φ1R : (ival (idEnv k) (φ'.subst (I.inst0 .one))).holds := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  rw [holds_iff_entails (H'.hφr (r := .one) trivial)]
  exact ent_trans (entails_of_holds (H.hφr (r := .one) trivial) hφ1) (ent_subst D.f12 _)

/-- The fibres at the end of the line. -/
theorem TGD2.rT1 (σ : ISub k' k) : RT2 S k' ((T.dinst .one).isub σ) ((T'.dinst .one).isub σ) := by
  rw [dinst1_isub, dinst1_isub]; exact D.rT k' _ (D.φ1At hW hφ1 σ)

/-- The equivalences at the end of the line. -/
theorem TGD2.e1 (σ : ISub k' k) :
    RE2 S k' (Tm.equiv ((T.dinst .one).isub σ) ((A.dinst .one).isub σ)) ((e.dinst .one).isub σ)
      ((e'.dinst .one).isub σ) := by
  rw [dinst1_isub, dinst1_isub, dinst1_isub, dinst1_isub]; exact D.rE k' _ (D.φ1At hW hφ1 σ)

theorem TGD2.hT1 : ∃ l, HasTy S k .one [] (T.dinst .one) (.univ l) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  exact ⟨l1, minimal_to_spec (H.hTr (r := .one) trivial (X := .one) trivial (ent_refl _)
    (entails_of_holds hφs hφ1))⟩

/-- The fibres of the equivalences over the compositions in the bases are related types. -/
theorem TGD2.rFib : RT2 S k (tgFib A φ T e ψ u0) (tgFib A' φ' T' e' ψ' u0') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφs' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) := ent_cof_one hW (entails_of_holds hφs hφ1)
  have hent1' : I.Entails .one (cof .one (φ'.subst (I.inst0 .one))) :=
    ent_cof_one hW (entails_of_holds hφs' (D.φ1R hW hφ1))
  have hfib := HasTy.top hW (HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hfib))
  have hfib' := HasTy.top hW (HasTy.restrict (Φ' := .one) trivial hent1' (minimal_to_spec H'.hfib))
  obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
  have hA1 := minimal_to_spec (H.hAr (r := .one) trivial)
  have rT := D.rT1 hW hφ1 (ISub.id k)
  have he1 := D.e1 hW hφ1 (ISub.id k)
  have hAc := closed_of_ty hW hA1
  have hTc := closed_of_ty hW hT1
  have hec := closed_ty (H.her (r := .one) trivial (X := cof .one (φ.subst (I.inst0 .one))) ⟨trivial, hφs⟩
    (ent_and_left _ _) (ent_and_right _ _))
  have hec' := closed_ty (H'.her (r := .one) trivial (X := cof .one (φ'.subst (I.inst0 .one))) ⟨trivial, hφs'⟩
    (ent_and_left _ _) (ent_and_right _ _))
  have hTc' := closed_ty (H'.hTr (r := .one) trivial (X := .one) trivial (ent_refl _)
    (entails_of_holds hφs' (D.φ1R hW hφ1)))
  rw [isub_id_of_closed hTc, isub_id_of_closed hTc'] at rT
  rw [isub_id_of_closed hTc, isub_id_of_closed hAc, isub_id_of_closed hec, isub_id_of_closed hec'] at he1
  have rA : RT2 S k (A.dinst .one) (A'.dinst .one) := by
    have := D.rA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed (D.closedL hW).1, isub_cons_id_of_closed (D.closedR hW).1] at this
  have eT := tyEq_top hW hT1 (Comp2_ty_base rT).2.2.2.2.2
  have eA := tyEq_top hW hA1 (Comp2_ty_base rA).2.2.2.2.2
  have ee := (RE2.typed he1).2.2
  unfold Tm.equiv at ee
  have he := fiber_congrS hW eT eA (EqTm.fst ee) (RE2.typed (D.a1' hW)).2.2
  rw [tgFib_eq] at hfib hfib' ⊢
  rw [tgFib_eq]
  refine RT2_sigma_intro hW hfib hfib' he (fun k' σ => D.rT1 hW hφ1 σ) fun k' σ a a' ha => ?_
  rw [fibB_isub_inst, fibB_isub_inst]
  have eσ := D.e1 hW hφ1 σ
  have rAσ : ∀ {k3} (τ : ISub k3 k), RT2 S k3 ((A.dinst .one).isub τ) ((A'.dinst .one).isub τ) := fun τ => by
    rw [dinst1_isub, dinst1_isub]; exact D.rA _ τ .one .one trivial trivial (I_eq_refl _)
  have happ : RE2 S k' ((A.dinst .one).isub σ) (.app (.fst ((e.dinst .one).isub σ)) a)
      (.app (.fst ((e'.dinst .one).isub σ)) a') := by
    rw [dinst1_isub, dinst1_isub, dinst1_isub]
    rw [dinst1_isub] at ha
    exact D.eApp hW σ (r := .one) (r' := .one) trivial trivial (I_eq_refl _) (D.φ1At hW hφ1 σ) ha
  have ha1 := RE2.isub hW (D.a1' hW) σ
  have hAσ := HasTy.isubS hW hA1 σ
  have hAσ' := HasTy.isubS hW (minimal_to_spec (H'.hAr (r := .one) trivial)) σ
  have hp := HasTy.top hW (minimal_to_spec (pathC_typed hS (spec_to_minimal hW hAσ)
    (spec_to_minimal hW (RE2.typed happ).1) (spec_to_minimal hW (RE2.typed ha1).1)))
  have eAσ := tyEq_top hW hAσ (Comp2_ty_base (rAσ σ)).2.2.2.2.2
  have hp' := HasTy.top hW (minimal_to_spec (pathC_typed hS (spec_to_minimal hW hAσ')
    (spec_to_minimal hW ((RE2.typed happ).2.1.conv eAσ)) (spec_to_minimal hW ((RE2.typed ha1).2.1.conv eAσ))))
  have hpe := pathC_congrS hW eAσ (RE2.typed happ).2.2 (RE2.typed ha1).2.2
  unfold Tm.pathC at hp hp' hpe ⊢
  refine RT2_path_intro hW hp hp' hpe (fun k3 σ3 => ?_) (fun k3 σ3 r r' hr hr' he => ?_) ?_ ?_
  · rw [isub_dshift, isub_dshift, Tm.isub_isub, Tm.isub_isub]
    have x := RT2.isub hW (tyCode_of_univ hW (HasTy.isubS hW hA1 _)) (rAσ (σ.comp σ3)) (ISub.wk k3)
    rwa [isub_wk_of_closed (closed_of_ty hW (HasTy.isubS hW hA1 (σ.comp σ3))),
      isub_wk_of_closed (closed_of_ty hW (HasTy.isubS hW (minimal_to_spec (H'.hAr (r := .one) trivial)) (σ.comp σ3)))]
      at x
  · rw [isub_dshift, isub_dshift, dshift_dinst, dshift_dinst, Tm.isub_isub, Tm.isub_isub]
    exact rAσ (σ.comp σ3)
  · rw [dshift_dinst]; exact happ
  · rw [dshift_dinst]; exact ha1


/-- The equivalences at the end of the line, unrestricted. -/
theorem TGD2.e1id : RE2 S k (Tm.equiv (T.dinst .one) (A.dinst .one)) (e.dinst .one) (e'.dinst .one) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφs' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have hec := closed_ty (H.her (r := .one) trivial (X := cof .one (φ.subst (I.inst0 .one))) ⟨trivial, hφs⟩
    (ent_and_left _ _) (ent_and_right _ _))
  have hec' := closed_ty (H'.her (r := .one) trivial (X := cof .one (φ'.subst (I.inst0 .one))) ⟨trivial, hφs'⟩
    (ent_and_left _ _) (ent_and_right _ _))
  obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
  have he1 := D.e1 hW hφ1 (ISub.id k)
  rwa [isub_id_of_closed (closed_of_ty hW hT1),
    isub_id_of_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))), isub_id_of_closed hec,
    isub_id_of_closed hec'] at he1

/-- The fibres are contractible. -/
theorem TGD2.c : RE2 S k (Tm.isContr (tgFib A φ T e ψ u0)) (tgC A φ e ψ u0) (tgC A' φ' e' ψ' u0') := by
  have he1 := D.e1id hW hφ1
  unfold Tm.equiv at he1
  have h2 := (RE2_sigma_elim hW he1).2
  rw [isEquiv_inst, isEquiv_eq] at h2
  have h3 := RE2_pi_elim hW h2 (D.a1' hW)
  rwa [isContr_fiber_inst] at h3

/-- The paths in the fibres, typed. -/
theorem TGD2.fibPath (ρ : ISub k' k) {b : Tm} (hb : RE2 S k' ((T.dinst .one).isub ρ) b b) :
    ∃ l, HasTy S k' .one [] (Tm.pathC ((A.dinst .one).isub ρ) (.app (.fst ((e.dinst .one).isub ρ)) b)
      ((tgA1' A φ e ψ u0).isub ρ)) (.univ l) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have happ : RE2 S k' ((A.dinst .one).isub ρ) (.app (.fst ((e.dinst .one).isub ρ)) b)
      (.app (.fst ((e'.dinst .one).isub ρ)) b) := by
    rw [dinst1_isub, dinst1_isub, dinst1_isub]
    rw [dinst1_isub] at hb
    exact D.eApp hW ρ (r := .one) (r' := .one) trivial trivial (I_eq_refl _) (D.φ1At hW hφ1 ρ) hb
  exact ⟨l1, minimal_to_spec (pathC_typed (sigClosed_of_wfSig hW)
    (spec_to_minimal hW (HasTy.isubS hW (minimal_to_spec (H.hAr (r := .one) trivial)) ρ))
    (spec_to_minimal hW (RE2.typed happ).1) (spec_to_minimal hW (RE2.typed (RE2.isub hW (D.a1' hW) ρ)).1))⟩

/-- The fibres have compositions. -/
theorem TGD2.fibK : KanH2 S k (tgFib A φ T e ψ u0) (tgFib A' φ' T' e' ψ' u0') := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) := ent_cof_one hW (entails_of_holds hφs hφ1)
  have hfib := HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hfib)
  have rF := D.rFib hW hφ1
  have KH : ∀ {k1} (ρ : ISub k1 k), KHRel S k1 ((A.dinst .one).isub ρ) := fun ρ k3 σ X X' h h' =>
    D.kAR k3 (ISub.cons .one trivial (ρ.comp σ)) X X' (by rwa [Tm.isub_isub, dinst1_isub] at h) h'
  have KT : ∀ {k1} (ρ : ISub k1 k), KTRel S k1 ((A.dinst .one).isub ρ) := fun ρ k3 Θ X X' h h' =>
    D.kATR k3 (ISub.cons .one trivial (ρ.comp Θ)) X X' (by rwa [Tm.isub_isub, dinst1_isub] at h) h'
  rw [tgFib_eq] at hfib rF ⊢
  refine kanH2_sigma hW rF ⟨redW_self rfl, TyEq.refl _⟩ hfib (fun k1 ρ1 A1 B1 h1 k2 ρ2 X X' hX hXX' => ?_)
    (fun k1 ρ1 A1 B1 h1 b hb k2 ρ2 X X' hX hXX' => ?_) (fun k1 ρ1 A1 B1 h1 b hb k2 ρ2 X X' hX hXX' => ?_) <;>
  · rw [isub_sigma] at h1
    obtain ⟨rfl, rfl⟩ : _ = A1 ∧ _ = B1 := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
    first
    | (rw [Tm.isub_isub, dinst1_isub] at hX
       exact D.kTR k2 _ (D.φ1At hW hφ1 _) X X' hX hXX')
    | (rw [fibB_isub_inst] at hX
       obtain ⟨lp, hp⟩ := D.fibPath hW hφ1 ρ1 hb
       first
       | exact khRel_pathC hW hp (KH ρ1) k2 ρ2 X X' hX hXX'
       | exact ktRel_pathC hW hp (KH ρ1) (KT ρ1) k2 ρ2 X X' hX hXX')

end

end

end Model.Whnf
