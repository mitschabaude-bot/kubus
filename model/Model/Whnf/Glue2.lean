import Model.Whnf.Stable
import Model.Canon.GlueRT

/-!
# The binary relation at Glue types: formation
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- A Glue type whose face holds reduces to its fiber, at every further restriction. -/
theorem stable_glue {A1 T1 e1 : Tm} {φ1 : I} (hY : IsTyK S k (.glue A1 φ1 T1 e1)) (h : I.Entails .one φ1) :
    StableT S k (.glue A1 φ1 T1 e1) T1 := by
  intro k' σ
  have hσ : I.Entails .one (φ1.subst σ.τ) := by
    have := ent_subst h σ.τ; simpa [I.subst] using this
  rw [isub_glue]
  refine ⟨.step (by simp [step, show I.entails .one (φ1.subst σ.τ) = true from hσ]) (.refl _),
    glue_face_tyEq hW ?_ hσ⟩
  rw [← isub_glue]; exact hY.isub hW σ

omit hW in
/-- A Glue type whose face does not hold is a weak-head normal form. -/
theorem redT_glue_self {A1 T1 e1 : Tm} {φ1 : I} (h : ¬ I.Entails .one φ1) :
    RedT S k (.glue A1 φ1 T1 e1) (.glue A1 φ1 T1 e1) :=
  ⟨redW_self (by simp [step, show I.entails .one φ1 = false by simpa [I.Entails] using h]), TyEq.refl _⟩

/-- The relation at one stage of a Glue code, between two Glue types whose components are related. -/
theorem glue_loc {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (σ : ISub k' k) {A1 T1 e1 A2 T2 e2 : Tm} {φ1 φ2 : I} {l1 l2 : ℕ}
    (hY : HasTy S k' .one [] (.glue A1 φ1 T1 e1) (.univ l1)) (hZ : HasTy S k' .one [] (.glue A2 φ2 T2 e2) (.univ l2))
    (f1 : (ival (idEnv k') φ1).face = Cof.restr (ival (idEnv k) φ).face σ.hom)
    (f2 : (ival (idEnv k') φ2).face = Cof.restr (ival (idEnv k) φ).face σ.hom)
    (eA : semK S k' A1 = semK S k' (A.isub σ))
    (eT : ∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      semK S k'' (T1.isub σ') = semK S k'' (T.isub (σ.comp σ')))
    (hA12 : RT2 S k' A1 A2)
    (hT12 : ∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      RT2 S k'' (T1.isub σ') (T2.isub σ'))
    (hE12 : ∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      RE2 S k'' (Tm.equiv (T1.isub σ') (A1.isub σ')) (e1.isub σ') (e2.isub σ')) :
    glueLocT S (semK S k A) (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k)))
      (ival (idEnv k) φ).face (Hom.id k) k' σ (.glue A1 φ1 T1 e1) (.glue A2 φ2 T2 e2) := by
  obtain ⟨hφs, lA, hA0, -⟩ := glue_data hW hG
  obtain ⟨hφ1, -⟩ := glue_data hW hY
  obtain ⟨hφ2, -⟩ := glue_data hW hZ
  have hYK : IsTyK S k' (.glue A1 φ1 T1 e1) := ⟨l1, .inl hY⟩
  have hZK : IsTyK S k' (.glue A2 φ2 T2 e2) := ⟨l2, .inl hZ⟩
  have ent : ∀ {ψ : I}, ψ.Scoped k' → (ival (idEnv k') ψ).face = Cof.restr (ival (idEnv k) φ).face σ.hom →
      (I.Entails .one ψ ↔ (Cof.restr (ival (idEnv k) φ).face σ.hom).holds) := fun hs hf => by
    rw [← holds_iff_entails hs, DM.holds_iff_face_holds, hf]
  unfold glueLocT
  simp only [Hom.id_comp]
  split_ifs with hh
  · -- the face holds: both sides reduce to their fibers
    rw [dat_glue_fiber σ hh]
    have hh' := (face_holds_iff hφs σ).1 hh
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh'
    have hX := tyCode_of_univ hW hTσ
    have h0 := hT12 k' (ISub.id k') (by rwa [ISub.comp_id])
    have e0 := eT k' (ISub.id k') (by rwa [ISub.comp_id])
    have hc1 := closed_of_ty hW hY
    have hc2 := closed_of_ty hW hZ
    simp only [Tm.closedB, Bool.and_eq_true] at hc1 hc2
    rw [isub_id_of_closed hc1.1.2, isub_id_of_closed hc2.1.2] at h0
    rw [isub_id_of_closed hc1.1.2, ISub.comp_id] at e0
    have hent1 := (ent hφ1 f1).2 hh
    have hent2 := (ent hφ2 f2).2 hh
    have hT1K : IsTyK S k' T1 := hYK.of_tyEq (glue_face_tyEq hW hYK hent1)
    unfold RT2 at h0
    rw [e0] at h0
    exact ty_expandS2 hW hX hYK hZK hT1K (stable_glue hW hYK hent1) (stable_glue hW hZK hent2) h0
  · -- the face does not hold: both sides are their own normal forms
    have hn1 : ¬ I.Entails .one φ1 := fun h => hh ((ent hφ1 f1).1 h)
    have hn2 : ¬ I.Entails .one φ2 := fun h => hh ((ent hφ2 f2).1 h)
    obtain ⟨-, lA1, hA1, he1⟩ := glue_data hW hY
    refine ⟨A1, φ1, T1, e1, A2, φ2, T2, e2, redT_glue_self hn1, redT_glue_self hn2, hφ1, hφ2, f1, f2, ?_,
      fun k'' σ' hh' => ⟨?_, ?_⟩⟩
    · rw [Comp2_res_el hW hA0, ← eA]; exact hA12
    · have hh2 := (face_holds_iff hφs (σ.comp σ')).1 hh'
      rw [dat_glue_fiber (σ.comp σ') hh', ← eT k'' σ' hh2]
      exact hT12 k'' σ' hh2
    · have hh2 := (face_holds_iff hφs (σ.comp σ')).1 hh'
      -- the fiber and base of the left side at this restriction
      have hY1 : (ival (idEnv k'') (φ1.subst σ'.τ)).holds := by
        rw [DM.holds_iff_face_holds, face_isub f1 σ', Cof.restr_restr, ← ISub.hom_comp]; exact hh'
      obtain ⟨lT, hTσ, heσ⟩ := glue_fiber_ty hW hY σ' hY1
      obtain ⟨lE, hE⟩ := ty_of_tyEq hW (isTyK_of_ty hW heσ) (TyEq.refl _) (fun l h => by cases h)
      have hA1σ := HasTy.isubS hW hA1 σ'
      have gT : GoodP S k'' (fun k3 σ3 => Comp2 S (dat (partialKV k (ival (idEnv k) φ).face
          (faceVals S T (idEnv k) (γ0 k))) k'' (σ.comp σ').hom) k'' k3 σ3.hom) (T1.isub σ') := by
        rw [dat_glue_fiber (σ.comp σ') hh', ← eT k'' σ' hh2]; exact goodP_comp hW hTσ
      have gA : GoodP S k'' (fun k3 σ3 => Comp2 S (semK S k A) k k3 ((σ.comp σ').comp σ3).hom) (A1.isub σ') := by
        intro k3 σ3 t t'
        have eA' : semK S k'' (A1.isub σ') = semK S k'' (A.isub (σ.comp σ')) := by
          rw [semK_isubS hW hA1, eA, ← semK_isubS hW (HasTy.isubS hW hA0 σ), Tm.isub_isub]
        have := goodP_comp hW hA1σ k3 σ3 t t'
        simp only at this ⊢
        rw [eA', semK_isubS hW hA0, Comp2_res (semK_ne hW hA0), ← ISub.hom_comp] at this
        exact this
      exact (goodP_id hW (goodP_equivF hW hE gT gA) (closed_of_ty hW hE) _ _).2 (hE12 k'' σ' hh2)


/-- A Glue type whose face does not hold, related to another one with the same face, through related
components. -/
theorem RT2_glue_intro {A T e A' T' e' : Tm} {φ φ' : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hG' : HasTy S k .one [] (.glue A' φ' T' e') (.univ l))
    (he : EqTm S k .one [] (.glue A φ T e) (.glue A' φ' T' e') (.univ l))
    (hn : ¬ (ival (idEnv k) φ).holds) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A'.isub σ))
    (hT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T'.isub σ))
    (hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ))
    (hEL : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e.isub σ))
    (hER : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T'.isub σ) (A'.isub σ)) (e'.isub σ) (e'.isub σ)) :
    RT2 S k (.glue A φ T e) (.glue A' φ' T' e') := by
  obtain ⟨hφs, lA, hA0, -⟩ := glue_data hW hG
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hf' : (ival (idEnv k) φ').face = (ival (idEnv k) φ).face := face_eq_of_entails h21 h12 _
  have hXA : ∀ k' (σ : ISub k' k), TyCode k' (semK S k' (A.isub σ)) := fun k' σ =>
    tyCode_of_univ hW (HasTy.isubS hW hA0 σ)
  have hXT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → TyCode k' (semK S k' (T.isub σ)) :=
    fun k' σ hh => tyCode_of_univ hW (glue_fiber_ty hW hG σ hh).choose_spec.1
  have hhc : ∀ {k' k'' : ℕ} (σ : ISub k' k) (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      (ival (idEnv k'') ((φ.subst σ.τ).subst σ'.τ)).holds := fun σ σ' h => by rwa [← I_subst_comp]
  have hGσ : ∀ k' (σ : ISub k' k), HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) :=
    fun k' σ => by have := HasTy.isubS hW hG σ; rwa [isub_glue] at this
  have hGσ' : ∀ k' (σ : ISub k' k),
      HasTy S k' .one [] (.glue (A'.isub σ) (φ'.subst σ.τ) (T'.isub σ) (e'.isub σ)) (.univ l) :=
    fun k' σ => by have := HasTy.isubS hW hG' σ; rwa [isub_glue] at this
  have fL : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).face = Cof.restr (ival (idEnv k) φ).face σ.hom :=
    fun k' σ => face_isub rfl σ
  have fR : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ'.subst σ.τ)).face = Cof.restr (ival (idEnv k) φ).face σ.hom :=
    fun k' σ => face_isub hf' σ
  have hsemG' : semK S k (.glue A' φ' T' e') = semK S k (.glue A φ T e) := (semK_eq hW he).symm
  unfold RT2
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
  refine ⟨⟨⟨l, .inl hG⟩, ⟨l, .inl hG'⟩, ?_, ?_, .inr ⟨l, he⟩⟩, fun k' σ => ?_, ?_, ?_⟩
  · rw [← semK_glueT hW hG, res_id (kv_semK_of_univ hW hG)]
  · rw [hsemG', ← semK_glueT hW hG, res_id (kv_semK_of_univ hW hG)]
  · rw [isub_glue, isub_glue]
    refine glue_loc hW hG σ (hGσ k' σ) (hGσ' k' σ) (fL k' σ) (fR k' σ) rfl (fun k'' σ' _ => by rw [Tm.isub_isub])
      (hA k' σ) (fun k'' σ' hh => ?_) (fun k'' σ' hh => ?_)
    · rw [Tm.isub_isub, Tm.isub_isub]; exact hT k'' (σ.comp σ') hh
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact hE k'' (σ.comp σ') hh
  · intro k' σ hnσ W hW' k'' ρ
    have hne : ¬ I.Entails .one (φ.subst σ.τ) := by
      rw [← holds_iff_entails (I.scoped_subst hφs σ.sc), DM.holds_iff_face_holds, fL k' σ]
      simpa only [Hom.id_comp] using hnσ
    rw [isub_glue] at hW'
    obtain rfl := RedW.unique hW' (redT_glue_self (S := S) (k := k') hne).1
    rw [← isub_glue, Tm.isub_isub, isub_glue]
    refine glue_loc hW hG (σ.comp ρ) (hGσ k'' _) (hGσ k'' _) (fL k'' _) (fL k'' _) rfl
      (fun k3 σ3 _ => by rw [Tm.isub_isub]) (RT2.refl hW (hXA _ _) (hA k'' _)) (fun k3 σ3 hh => ?_)
      (fun k3 σ3 hh => ?_)
    · rw [Tm.isub_isub]; exact RT2.refl hW (hXT _ _ hh) (hT k3 _ hh)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact hEL k3 _ hh
  · intro k' σ hnσ W hW' k'' ρ
    have hne : ¬ I.Entails .one (φ'.subst σ.τ) := by
      rw [← holds_iff_entails (I.scoped_subst (glue_data hW hG').1 σ.sc), DM.holds_iff_face_holds, fR k' σ]
      simpa only [Hom.id_comp] using hnσ
    rw [isub_glue] at hW'
    obtain rfl := RedW.unique hW' (redT_glue_self (S := S) (k := k') hne).1
    rw [← isub_glue, Tm.isub_isub, isub_glue]
    refine glue_loc hW hG (σ.comp ρ) (hGσ' k'' _) (hGσ' k'' _) (fR k'' _) (fR k'' _)
      (RT2.semK_eq hW (hA k'' _)) (fun k3 σ3 hh => by rw [Tm.isub_isub]; exact RT2.semK_eq hW (hT k3 _ hh))
      (RT2.refl' hW (hXA _ _) (hA k'' _)) (fun k3 σ3 hh => ?_) (fun k3 σ3 hh => ?_)
    · rw [Tm.isub_isub]; exact RT2.refl' hW (hXT _ _ hh) (hT k3 _ hh)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact hER k3 _ hh

end

end Model.Whnf
