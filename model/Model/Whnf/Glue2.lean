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


omit hW in
theorem isub_glueEl (ψ : I) (e t a : Tm) (σ : ISub k' k) :
    (Tm.glueEl ψ e t a).isub σ = .glueEl (ψ.subst σ.τ) (e.isub σ) (t.isub σ) (a.isub σ) := rfl

omit hW in
/-- A Glue element whose face does not hold is a weak-head normal form. -/
theorem redE_glueEl_self {X e t a : Tm} {ψ : I} (h : ¬ I.Entails .one ψ) (ht : HasTy S k .one [] (.glueEl ψ e t a) X) :
    RedE S k X (.glueEl ψ e t a) (.glueEl ψ e t a) :=
  ⟨redW_self (by simp [step, show I.entails .one ψ = false by simpa [I.Entails] using h]), EqTm.refl ht⟩

/-- A Glue element whose face holds reduces to its fiber, at every further restriction. -/
theorem stable_glueEl {X e t a : Tm} {ψ : I} (hy : HasTy S k .one [] (.glueEl ψ e t a) X) (h : I.Entails .one ψ) :
    StableE S k X (.glueEl ψ e t a) t := by
  intro k' σ
  have hσ : I.Entails .one (ψ.subst σ.τ) := by
    have := ent_subst h σ.τ; simpa [I.subst] using this
  have hyσ := HasTy.isubS hW hy σ
  refine ⟨.step (by simp [Tm.isub, Tm.subst, step, show I.entails .one (ψ.subst σ.τ) = true from hσ]) (.refl _), ?_⟩
  exact EqTm.glueElFace hσ hyσ

/-- The relation at one stage of a Glue code, between two Glue elements whose components are related. -/
theorem glueE_loc {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (σ : ISub k' k) {ψ1 ψ2 : I} {e1 t1 a1 e2 t2 a2 : Tm}
    (hy : HasTy S k' .one [] (.glueEl ψ1 e1 t1 a1) ((Tm.glue A φ T e).isub σ))
    (hz : HasTy S k' .one [] (.glueEl ψ2 e2 t2 a2) ((Tm.glue A φ T e).isub σ))
    (q1 : I.Entails ψ1 (φ.subst σ.τ)) (q1' : I.Entails (φ.subst σ.τ) ψ1)
    (q2 : I.Entails ψ2 (φ.subst σ.τ)) (q2' : I.Entails (φ.subst σ.τ) ψ2)
    (ee1 : EqTm S k' (cof .one (φ.subst σ.τ)) [] e1 (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)))
    (ee2 : EqTm S k' (cof .one (φ.subst σ.τ)) [] e2 (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)))
    (hGG : RT2 S k' ((Tm.glue A φ T e).isub σ) ((Tm.glue A φ T e).isub σ))
    (ha : RE2 S k' (A.isub σ) a1 a2)
    (hTT : ∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      RT2 S k'' (T.isub (σ.comp σ')) (T.isub (σ.comp σ')))
    (ht : ∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      RE2 S k'' (T.isub (σ.comp σ')) (t1.isub σ') (t2.isub σ'))
    (hat1 : ∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      RE2 S k'' (A.isub (σ.comp σ')) (a1.isub σ') (.app (.fst (e.isub (σ.comp σ'))) (t1.isub σ')))
    (hat2 : ∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
      RE2 S k'' (A.isub (σ.comp σ')) (a2.isub σ') (.app (.fst (e.isub (σ.comp σ'))) (t2.isub σ'))) :
    glueLocE S (semK S k A) (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k)))
      (ival (idEnv k) φ).face (Hom.id k) k' σ ((Tm.glue A φ T e).isub σ) (.glueEl ψ1 e1 t1 a1)
      (.glueEl ψ2 e2 t2 a2) := by
  obtain ⟨hφs, lA, hA0, -⟩ := glue_data hW hG
  have hφσ := I.scoped_subst hφs σ.sc
  have hGσ : IsTyK S k' ((Tm.glue A φ T e).isub σ) := ⟨l, .inl (HasTy.isubS hW hG σ)⟩
  unfold glueLocE
  simp only [Hom.id_comp]
  split_ifs with hh
  · rw [dat_glue_fiber σ hh]
    have hh' := (face_holds_iff hφs σ).1 hh
    have hent : I.Entails .one (φ.subst σ.τ) := (holds_iff_entails hφσ).1 hh'
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh'
    have hX := tyCode_of_univ hW hTσ
    have hface : TyEq S k' ((Tm.glue A φ T e).isub σ) (T.isub σ) := by
      rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ hent
    have hT0 := hTT k' (ISub.id k') (by rwa [ISub.comp_id])
    have h0 := ht k' (ISub.id k') (by rwa [ISub.comp_id])
    rw [ISub.comp_id] at hT0 h0
    have hc1 := closed_of_ty hW hy
    have hc2 := closed_of_ty hW hz
    simp only [Tm.closedB, Bool.and_eq_true] at hc1 hc2
    rw [isub_id_of_closed hc1.1.2, isub_id_of_closed hc2.1.2] at h0
    -- the fiber relation, as a relation at the Glue type
    have hTG : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
      refine ty_expandSR hW hX (hGσ.of_tyEq hface) hGσ ?_ hT0
      rw [isub_glue] at hGσ ⊢
      exact stable_glue hW hGσ hent
    have P := per2_tyCode hW hX k' (Hom.id k')
    have hGGT : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty ((Tm.glue A φ T e).isub σ)
        ((Tm.glue A φ T e).isub σ) := P.reflTy' hTG
    have ent1 : I.Entails .one ψ1 := ent_trans hent q1'
    have ent2 : I.Entails .one ψ2 := ent_trans hent q2'
    exact el_expandS2 hW hX hGGT hy hz ((RE2.typed h0).1.tyConv hface.symm) (stable_glueEl hW hy ent1)
      (stable_glueEl hW hz ent2) (P.conv hTG h0)
  · have hne : ¬ I.Entails .one (φ.subst σ.τ) := by
      rw [← holds_iff_entails hφσ, DM.holds_iff_face_holds, face_isub rfl σ]; exact hh
    have hn1 : ¬ I.Entails .one ψ1 := fun h => hne (ent_trans h q1)
    have hn2 : ¬ I.Entails .one ψ2 := fun h => hne (ent_trans h q2)
    refine ⟨A.isub σ, φ.subst σ.τ, T.isub σ, e.isub σ, ψ1, e1, t1, a1, ψ2, e2, t2, a2, ?_,
      redE_glueEl_self hn1 hy, redE_glueEl_self hn2 hz, q1, q1', q2, q2', ee1, ee2, ?_, fun k'' σ' hh' => ?_⟩
    · rw [isub_glue]; exact redT_glue_self hne
    · rw [Comp2_res_el hW hA0]; exact ha
    · have hh2 := (face_holds_iff hφs (σ.comp σ')).1 hh'
      rw [dat_glue_fiber (σ.comp σ') hh', Comp2_res_el hW hA0, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact ⟨ht k'' σ' hh2, hat1 k'' σ' hh2, hat2 k'' σ' hh2⟩


/-- The fiber relation of a Glue type at a restriction where its face holds, as a relation at the Glue
type itself. -/
theorem glue_fiber_conv {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) (hTT : RT2 S k' (T.isub σ) (T.isub σ))
    {x y : Tm} (hxy : RE2 S k' (T.isub σ) x y) :
    (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).el ((Tm.glue A φ T e).isub σ) x y := by
  obtain ⟨hφs, -⟩ := glue_data hW hG
  have hent : I.Entails .one (φ.subst σ.τ) := (holds_iff_entails (I.scoped_subst hφs σ.sc)).1 hh
  obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh
  have hX := tyCode_of_univ hW hTσ
  have hGσ : IsTyK S k' ((Tm.glue A φ T e).isub σ) := ⟨l, .inl (HasTy.isubS hW hG σ)⟩
  have hface : TyEq S k' ((Tm.glue A φ T e).isub σ) (T.isub σ) := by
    rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ hent
  have hTG : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
    refine ty_expandSR hW hX (hGσ.of_tyEq hface) hGσ ?_ hTT
    rw [isub_glue] at hGσ ⊢
    exact stable_glue hW hGσ hent
  exact (per2_tyCode hW hX k' (Hom.id k')).conv hTG hxy

/-- Related Glue introductions, at a Glue type whose face does not hold. -/
theorem RE2_glueEl_intro {A T e e' t a t' a' : Tm} {φ φ' : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hn : ¬ (ival (idEnv k) φ).holds)
    (hg : EB S k (.glue A φ T e) (.glueEl φ e t a) (.glueEl φ' e' t' a'))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ee' : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A))
    (hGG : RT2 S k (.glue A φ T e) (.glue A φ T e))
    (hAA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A.isub σ))
    (hTT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ))
    (ha : ∀ k' (σ : ISub k' k), RE2 S k' (A.isub σ) (a.isub σ) (a'.isub σ))
    (ht : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RE2 S k' (T.isub σ) (t.isub σ) (t'.isub σ))
    (hat : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a.isub σ) (.app (.fst (e.isub σ)) (t.isub σ)))
    (hat' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a'.isub σ) (.app (.fst (e.isub σ)) (t'.isub σ))) :
    RE2 S k (.glue A φ T e) (.glueEl φ e t a) (.glueEl φ' e' t' a') := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hXA : ∀ k' (σ : ISub k' k), TyCode k' (semK S k' (A.isub σ)) := fun k' σ =>
    tyCode_of_univ hW (HasTy.isubS hW hA0 σ)
  have hXT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → TyCode k' (semK S k' (T.isub σ)) :=
    fun k' σ hh => tyCode_of_univ hW (glue_fiber_ty hW hG σ hh).choose_spec.1
  have hXG := tyCode_of_univ hW hG
  have hΦ : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  have eeσ : ∀ k' (σ : ISub k' k), EqTm S k' (cof .one (φ.subst σ.τ)) [] (e.isub σ) (e.isub σ)
      (Tm.equiv (T.isub σ) (A.isub σ)) := fun k' σ => by
    have := EqTm.isubF hW hΦ (EqTm.refl he0) σ; rwa [isub_equiv] at this
  have ee'σ : ∀ k' (σ : ISub k' k), EqTm S k' (cof .one (φ.subst σ.τ)) [] (e'.isub σ) (e.isub σ)
      (Tm.equiv (T.isub σ) (A.isub σ)) := fun k' σ => by
    have := EqTm.isubF hW hΦ ee' σ; rwa [isub_equiv] at this
  have hgσ : ∀ k' (σ : ISub k' k), HasTy S k' .one [] (.glueEl (φ.subst σ.τ) (e.isub σ) (t.isub σ) (a.isub σ))
      ((Tm.glue A φ T e).isub σ) := fun k' σ => HasTy.isubS hW hg.1 σ
  have hgσ' : ∀ k' (σ : ISub k' k), HasTy S k' .one [] (.glueEl (φ'.subst σ.τ) (e'.isub σ) (t'.isub σ) (a'.isub σ))
      ((Tm.glue A φ T e).isub σ) := fun k' σ => HasTy.isubS hW hg.2.1 σ
  have q12 : ∀ k' (σ : ISub k' k), I.Entails (φ'.subst σ.τ) (φ.subst σ.τ) := fun k' σ => ent_subst h21 σ.τ
  have q21 : ∀ k' (σ : ISub k' k), I.Entails (φ.subst σ.τ) (φ'.subst σ.τ) := fun k' σ => ent_subst h12 σ.τ
  have er : ∀ k' (σ : ISub k' k), I.Entails (φ.subst σ.τ) (φ.subst σ.τ) := fun k' σ => ent_refl _
  have hcomp : ∀ {k' k'' : ℕ} (σ : ISub k' k) (σ' : ISub k'' k'),
      (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds → (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds :=
    fun _ _ h => h
  have PA := fun k' (σ : ISub k' k) => perK hW (hXA k' σ)
  -- self-relations of the components
  have haL : ∀ k' (σ : ISub k' k), RE2 S k' (A.isub σ) (a.isub σ) (a.isub σ) := fun k' σ =>
    (PA k' σ).reflEl (hAA k' σ) (ha k' σ)
  have haR : ∀ k' (σ : ISub k' k), RE2 S k' (A.isub σ) (a'.isub σ) (a'.isub σ) := fun k' σ =>
    (PA k' σ).reflEl' (hAA k' σ) (ha k' σ)
  have htL : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RE2 S k' (T.isub σ) (t.isub σ) (t.isub σ) :=
    fun k' σ hh => (perK hW (hXT k' σ hh)).reflEl (hTT k' σ hh) (ht k' σ hh)
  have htR : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (t'.isub σ) (t'.isub σ) :=
    fun k' σ hh => (perK hW (hXT k' σ hh)).reflEl' (hTT k' σ hh) (ht k' σ hh)
  have hGGσ : ∀ k' (σ : ISub k' k), RT2 S k' ((Tm.glue A φ T e).isub σ) ((Tm.glue A φ T e).isub σ) :=
    fun k' σ => RT2.isub hW hXG hGG σ
  -- the clause at one stage, between two Glue elements built from these components
  have loc : ∀ k' (σ : ISub k' k) {ψ1 ψ2 : I} {e1 t1 a1 e2 t2 a2 : Tm},
      HasTy S k' .one [] (.glueEl ψ1 e1 t1 a1) ((Tm.glue A φ T e).isub σ) →
      HasTy S k' .one [] (.glueEl ψ2 e2 t2 a2) ((Tm.glue A φ T e).isub σ) →
      I.Entails ψ1 (φ.subst σ.τ) → I.Entails (φ.subst σ.τ) ψ1 →
      I.Entails ψ2 (φ.subst σ.τ) → I.Entails (φ.subst σ.τ) ψ2 →
      EqTm S k' (cof .one (φ.subst σ.τ)) [] e1 (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) →
      EqTm S k' (cof .one (φ.subst σ.τ)) [] e2 (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) →
      RE2 S k' (A.isub σ) a1 a2 →
      (∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
        RE2 S k'' (T.isub (σ.comp σ')) (t1.isub σ') (t2.isub σ')) →
      (∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
        RE2 S k'' (A.isub (σ.comp σ')) (a1.isub σ') (.app (.fst (e.isub (σ.comp σ'))) (t1.isub σ'))) →
      (∀ k'' (σ' : ISub k'' k'), (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds →
        RE2 S k'' (A.isub (σ.comp σ')) (a2.isub σ') (.app (.fst (e.isub (σ.comp σ'))) (t2.isub σ'))) →
      glueLocE S (semK S k A) (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k)))
        (ival (idEnv k) φ).face (Hom.id k) k' σ ((Tm.glue A φ T e).isub σ) (.glueEl ψ1 e1 t1 a1)
        (.glueEl ψ2 e2 t2 a2) :=
    by
      intro k' σ ψ1 ψ2 e1 t1 a1 e2 t2 a2 hy hz q1 q1' q2 q2' ee1 ee2 hA12 hT12 hb1 hb2
      exact glueE_loc hW hG σ hy hz q1 q1' q2 q2' ee1 ee2 (hGGσ k' σ) hA12 (fun k'' σ' hh => hTT k'' _ hh) hT12 hb1 hb2
  -- the instances at further restrictions
  have rew : ∀ {k' k'' : ℕ} (σ : ISub k' k) (σ' : ISub k'' k') (x : Tm), (x.isub σ).isub σ' = x.isub (σ.comp σ') :=
    fun σ σ' x => Tm.isub_isub x σ σ'
  -- coherence of one side, a Glue element whose face does not hold at a restriction
  have coh : ∀ {ψ : I} {e1 t1 a1 : Tm}, (∀ k' (σ : ISub k' k), I.Entails (ψ.subst σ.τ) (φ.subst σ.τ) ∧
        I.Entails (φ.subst σ.τ) (ψ.subst σ.τ)) →
      (∀ k' (σ : ISub k' k), HasTy S k' .one [] (.glueEl (ψ.subst σ.τ) (e1.isub σ) (t1.isub σ) (a1.isub σ))
        ((Tm.glue A φ T e).isub σ)) →
      (∀ k' (σ : ISub k' k), EqTm S k' (cof .one (φ.subst σ.τ)) [] (e1.isub σ) (e.isub σ)
        (Tm.equiv (T.isub σ) (A.isub σ))) →
      (∀ k' (σ : ISub k' k), RE2 S k' (A.isub σ) (a1.isub σ) (a1.isub σ)) →
      (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RE2 S k' (T.isub σ) (t1.isub σ) (t1.isub σ)) →
      (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
        RE2 S k' (A.isub σ) (a1.isub σ) (.app (.fst (e.isub σ)) (t1.isub σ))) →
      cohGE S (semK S k A) (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k)))
        (ival (idEnv k) φ).face (Hom.id k) (.glue A φ T e) (.glueEl ψ e1 t1 a1) := by
    intro ψ e1 t1 a1 hq hty hee haa htt hb k' σ hnσ w hw k'' ρ
    have hne : ¬ I.Entails .one (φ.subst σ.τ) := by
      rw [← holds_iff_entails (I.scoped_subst hφs σ.sc), DM.holds_iff_face_holds, face_isub rfl σ]
      simpa only [Hom.id_comp] using hnσ
    have hneψ : ¬ I.Entails .one (ψ.subst σ.τ) := fun h => hne (ent_trans h (hq k' σ).1)
    obtain rfl := RedW.unique hw (redE_glueEl_self hneψ (hty k' σ)).1
    refine ⟨fun hh ψ0 e0 t0 a0 hwe => ?_, fun hh => ?_⟩
    · simp only [Tm.glueEl.injEq] at hwe
      obtain ⟨-, -, rfl, -⟩ := hwe
      simp only [Hom.id_comp] at hh ⊢
      rw [dat_glue_fiber (σ.comp ρ) hh]
      have hh' := (face_holds_iff hφs (σ.comp ρ)).1 hh
      have hent : I.Entails .one (φ.subst (σ.comp ρ).τ) := (holds_iff_entails (I.scoped_subst hφs (σ.comp ρ).sc)).1 hh'
      have hyτ := hty k'' (σ.comp ρ)
      have hX := hXT k'' (σ.comp ρ) hh'
      rw [rew]
      refine el_expandSR hW hX ((perK hW hX).reflTy' (?_ : (Comp2 S _ k'' k'' (Hom.id k'')).ty (T.isub (σ.comp ρ))
        ((Tm.glue A φ T e).isub (σ.comp ρ))))
        ((RE2.typed (htt k'' _ hh')).1.tyConv ?_) hyτ (stable_glueEl hW hyτ (ent_trans hent (hq k'' _).2))
        (glue_fiber_conv hW hG (σ.comp ρ) hh' (hTT k'' _ hh') (htt k'' _ hh'))
      · have hGσ : IsTyK S k'' ((Tm.glue A φ T e).isub (σ.comp ρ)) := ⟨l, .inl (HasTy.isubS hW hG _)⟩
        have hface : TyEq S k'' ((Tm.glue A φ T e).isub (σ.comp ρ)) (T.isub (σ.comp ρ)) := by
          rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ hent
        refine ty_expandSR hW hX (hGσ.of_tyEq hface) hGσ ?_ (hTT k'' _ hh')
        rw [isub_glue] at hGσ ⊢
        exact stable_glue hW hGσ hent
      · have hGσ : IsTyK S k'' ((Tm.glue A φ T e).isub (σ.comp ρ)) := ⟨l, .inl (HasTy.isubS hW hG _)⟩
        rw [isub_glue] at hGσ ⊢; exact (glue_face_tyEq hW hGσ hent).symm
    · simp only [Hom.id_comp] at hh
      have hτ := hty k'' (σ.comp ρ)
      rw [show (Tm.glueEl (ψ.subst σ.τ) (e1.isub σ) (t1.isub σ) (a1.isub σ)).isub ρ =
        Tm.glueEl (ψ.subst (σ.comp ρ).τ) (e1.isub (σ.comp ρ)) (t1.isub (σ.comp ρ)) (a1.isub (σ.comp ρ)) by
          show Tm.glueEl ((ψ.subst σ.τ).subst ρ.τ) ((e1.isub σ).isub ρ) ((t1.isub σ).isub ρ) ((a1.isub σ).isub ρ) = _
          rw [← I_subst_comp, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]]
      rw [isub_glueEl]
      exact loc k'' (σ.comp ρ) hτ hτ (hq _ _).1 (hq _ _).2 (hq _ _).1 (hq _ _).2 (hee _ _) (hee _ _) (haa _ _)
        (fun k3 σ3 hh3 => by simp only [rew]; exact htt _ _ hh3) (fun k3 σ3 hh3 => by simp only [rew]; exact hb _ _ hh3)
        (fun k3 σ3 hh3 => by simp only [rew]; exact hb _ _ hh3)
  unfold RE2
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
  have hmem := mem_of_ty hW hg.1
  rw [semK_glueT hW hG] at hmem
  refine ⟨hg, by rw [res_id (isKV_glueC _ _ _ _)]; exact hmem, hg, fun k' σ => ?_, ?_, ?_⟩
  · rw [isub_glueEl, isub_glueEl]
    exact loc k' σ (hgσ k' σ) (hgσ' k' σ) (er k' σ) (er k' σ) (q12 k' σ) (q21 k' σ) (eeσ k' σ) (ee'σ k' σ) (ha k' σ)
      (fun k'' σ' hh => by simp only [rew]; exact ht _ _ hh) (fun k'' σ' hh => by simp only [rew]; exact hat _ _ hh)
      (fun k'' σ' hh => by simp only [rew]; exact hat' _ _ hh)
  · exact coh (fun k' σ => ⟨er k' σ, er k' σ⟩) hgσ eeσ haL htL hat
  · exact coh (fun k' σ => ⟨q12 k' σ, q21 k' σ⟩) hgσ' ee'σ haR htR hat'


omit hW in
theorem red_unglue {φ : I} {e g w : Tm} (hn : ¬ I.Entails .one φ) (h : Red S g w) :
    Red S (.unglue φ e g) (.unglue φ e w) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih => exact .step (by simp [step, hn', hs]) ih

omit hW in
/-- `unglue` of a Glue type whose face does not hold reduces to the base of the normal form. -/
theorem red_unglue_base {φ ψ : I} {e g e0 t0 a0 : Tm} (hn : ¬ I.Entails .one φ)
    (h : RedW S g (.glueEl ψ e0 t0 a0)) : Red S (.unglue φ e g) a0 := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  have hw : step S (.glueEl ψ e0 t0 a0) = none := h.2
  have hs : step S (.unglue φ e (.glueEl ψ e0 t0 a0)) = some a0 := by
    rw [step]; simp only [hn', Bool.false_eq_true, ↓reduceIte, hw]
  exact (red_unglue hn h.1).trans (.step hs (.refl _))

/-- The coherence of the normal forms of elements of closed Glue types whose face does not hold, at
the base of the Glue type (spec change C4: `glueBeta` takes this coherence as a premise). It holds
given the compatibility of Glue annotations (`glueCohW_of_glueCompat`); the canonicity relation
records the coherence only pointwise, where the face holds, so it is an explicit hypothesis here. -/
def GlueCohW (S : Sig) : Prop :=
  ∀ (k : ℕ) (A1 T1 e1 g e0 t0 a0 : Tm) (φ1 ψ : I) (l : ℕ),
    HasTy S k .one [] (.glue A1 φ1 T1 e1) (.univ l) →
    EqTm S k .one [] g (.glueEl ψ e0 t0 a0) (.glue A1 φ1 T1 e1) → I.Entails ψ φ1 → I.Entails φ1 ψ →
    EqTm S k (cof .one φ1) [] e0 e1 (Tm.equiv T1 A1) → ¬ I.Entails .one φ1 →
    EqTm S k (cof .one ψ) [] a0 (.app (.fst e0) t0) A1

/-- `unglue` of an element of a Glue type whose face does not hold, by the base of a normal form with
agreeing annotations. -/
theorem unglue_base_eq {A1 T1 e1 g e0 t0 a0 : Tm} {φ1 ψ : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A1 φ1 T1 e1) (.univ l))
    (hg : EqTm S k .one [] g (.glueEl ψ e0 t0 a0) (.glue A1 φ1 T1 e1))
    (q12 : I.Entails ψ φ1) (q21 : I.Entails φ1 ψ)
    (ee : EqTm S k (cof .one φ1) [] e0 e1 (Tm.equiv T1 A1)) (ha0 : HasTy S k .one [] a0 A1)
    (hCW : GlueCohW S) (hn : ¬ I.Entails .one φ1) :
    EqTm S k .one [] (.unglue φ1 e1 g) a0 A1 := by
  obtain ⟨l', ⟨hA1, hφ1, hT1, he1⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  have hw := HasTy.eqR hg
  obtain ⟨A', T', lw, ⟨hGw, -, -, -⟩, -⟩ := gen_glueEl (spec_to_minimal hW hw) rfl
  obtain ⟨-, ⟨-, hψ, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) hGw rfl
  have c21 : I.Entails (cof .one ψ) (cof .one φ1) :=
    ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) q12)
  have hψs : (cof .one ψ).Scoped k := ⟨trivial, hψ⟩
  have hGK : IsTyK S k (.glue A1 φ1 T1 e1) := ⟨l, .inl hG⟩
  have hdata : ∃ l, HasTy S k .one [] A1 (.univ l) ∧ HasTy S k (cof .one φ1) [] e1 (Tm.equiv T1 A1) :=
    ⟨l', minimal_to_spec hA1, minimal_to_spec he1⟩
  -- the Glue type with the annotations of the normal form
  have hG2 : HasTy S k .one [] (.glue A1 ψ T1 e0) (.univ l') :=
    HasTy.glue (minimal_to_spec hA1) hψ (HasTy.restrict hψs c21 (minimal_to_spec hT1))
      (HasTy.restrict hψs c21 (HasTy.eqL ee))
  have hlv := lvl_of_ty hW hG
  have hlv' := lvl_of_ty hW hG2
  have eG : EqTm S k .one [] (.glue A1 φ1 T1 e1) (.glue A1 ψ T1 e0) (.univ (max l l')) :=
    EqTm.glue (hG.cumulTo (le_max_left _ _) (max_le hlv hlv')) (hG2.cumulTo (le_max_right _ _) (max_le hlv hlv'))
      (EqTm.refl ((minimal_to_spec hA1).cumulTo (le_max_right _ _) (max_le hlv hlv'))) q21 q12
      (EqTm.refl (minimal_to_spec (HasTy0.cumulTo hT1 (le_max_right _ _) (max_le hlv hlv')))) ee.symm
  have hG2K : IsTyK S k (.glue A1 ψ T1 e0) := ⟨l', .inl hG2⟩
  have hdata2 : ∃ l, HasTy S k .one [] A1 (.univ l) ∧ HasTy S k (cof .one ψ) [] e0 (Tm.equiv T1 A1) :=
    ⟨l', minimal_to_spec hA1, HasTy.restrict hψs c21 (HasTy.eqL ee)⟩
  have hw2 : HasTy S k .one [] (.glueEl ψ e0 t0 a0) (.glue A1 ψ T1 e0) := hw.conv eG
  have e1' := unglue_eq hW hGK hdata hg
  have e2 : EqTm S k .one [] (.unglue φ1 e1 (.glueEl ψ e0 t0 a0)) (.unglue ψ e0 (.glueEl ψ e0 t0 a0)) A1 :=
    EqTm.unglue (unglue_ty hW hGK hdata hw) (unglue_ty hW hG2K hdata2 hw2) q21 q12 ee.symm (EqTm.refl hw)
  have e3 := EqTm.glueBeta (unglue_ty hW hG2K hdata2 hw2) ha0 (hCW k A1 T1 e1 g e0 t0 a0 φ1 ψ l hG hg q12 q21 ee hn)
  exact e1'.trans (e2.trans e3)


/-- `GlueCohW` holds given the compatibility of Glue annotations (`Canon.glueEl_coh`). -/
theorem glueCohW_of_glueCompat (hGC : GlueCompat S) : GlueCohW S := by
  intro k A1 T1 e1 g e0 t0 a0 φ1 ψ l hG hg q12 q21 ee hn
  obtain ⟨l', ⟨hA1, -, hT1, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  have hw := HasTy.eqR hg
  obtain ⟨A', T', lw, ⟨hGw, -, -, -⟩, -⟩ := gen_glueEl (spec_to_minimal hW hw) rfl
  obtain ⟨-, ⟨-, hψ, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) hGw rfl
  have c21 : I.Entails (cof .one ψ) (cof .one φ1) :=
    ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) q12)
  have hψs : (cof .one ψ).Scoped k := ⟨trivial, hψ⟩
  have hG2 : HasTy S k .one [] (.glue A1 ψ T1 e0) (.univ l') :=
    HasTy.glue (minimal_to_spec hA1) hψ (HasTy.restrict hψs c21 (minimal_to_spec hT1))
      (HasTy.restrict hψs c21 (HasTy.eqL ee))
  have hlv := lvl_of_ty hW hG
  have hlv' := lvl_of_ty hW hG2
  have eG : EqTm S k .one [] (.glue A1 φ1 T1 e1) (.glue A1 ψ T1 e0) (.univ (max l l')) :=
    EqTm.glue (hG.cumulTo (le_max_left _ _) (max_le hlv hlv')) (hG2.cumulTo (le_max_right _ _) (max_le hlv hlv'))
      (EqTm.refl ((minimal_to_spec hA1).cumulTo (le_max_right _ _) (max_le hlv hlv'))) q21 q12
      (EqTm.refl (minimal_to_spec (HasTy0.cumulTo hT1 (le_max_right _ _) (max_le hlv hlv')))) ee.symm
  have hw2 : HasTy S k .one [] (.glueEl ψ e0 t0 a0) (.glue A1 ψ T1 e0) := hw.conv eG
  exact glueEl_coh hW hGC hG2 (fun h => hn (ent_trans ((holds_iff_entails hψ).1 h) q12)) hw2

/-- Related equivalences, applied to related elements. -/
theorem RE2_equiv_app {T A e e' x x' : Tm} (he : RE2 S k (Tm.equiv T A) e e') (hx : RE2 S k T x x') :
    RE2 S k A (.app (.fst e) x) (.app (.fst e') x') := by
  have h1 := (RE2_sigma_elim hW (show RE2 S k (.sigma (Tm.arrow T A) _) e e' from he)).1
  have h2 := RE2_pi_elim hW (show RE2 S k (.pi T A.shift) _ _ from h1) hx
  rwa [shift_inst] at h2

/-- A Glue type with equivalent face and agreeing equivalence. -/
theorem glue_annot_eq {A T e e' : Tm} {φ φ' : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hφ' : φ'.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ee' : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A)) :
    ∃ l2, HasTy S k .one [] (.glue A φ' T e') (.univ l2) ∧
      EqTm S k .one [] (.glue A φ T e) (.glue A φ' T e') (.univ l2) := by
  obtain ⟨l', ⟨hA1, hφ1, hT1, he1⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  have c21 : I.Entails (cof .one φ') (cof .one φ) :=
    ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) h21)
  have hs : (cof .one φ').Scoped k := ⟨trivial, hφ'⟩
  have hG2 : HasTy S k .one [] (.glue A φ' T e') (.univ l') :=
    HasTy.glue (minimal_to_spec hA1) hφ' (HasTy.restrict hs c21 (minimal_to_spec hT1))
      (HasTy.restrict hs c21 (HasTy.eqL ee'))
  have hlv := lvl_of_ty hW hG
  have hlv' := lvl_of_ty hW hG2
  refine ⟨max l l', hG2.cumulTo (le_max_right _ _) (max_le hlv hlv'), ?_⟩
  exact EqTm.glue (hG.cumulTo (le_max_left _ _) (max_le hlv hlv')) (hG2.cumulTo (le_max_right _ _) (max_le hlv hlv'))
    (EqTm.refl ((minimal_to_spec hA1).cumulTo (le_max_right _ _) (max_le hlv hlv'))) h12 h21
    (EqTm.refl (minimal_to_spec (HasTy0.cumulTo hT1 (le_max_right _ _) (max_le hlv hlv')))) ee'.symm


/-- `unglue` of related elements of a Glue type whose face does not hold, and the base of a normal form of the left element related to the right `unglue`. -/
theorem RE2_unglue_and {A T e e' g g' : Tm} {φ φ' : I} {l : ℕ} (hCW : GlueCohW S)
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hn : ¬ (ival (idEnv k) φ).holds)
    (hgg : RE2 S k (.glue A φ T e) g g')
    (hu : HasTy S k .one [] (.unglue φ e g) A) (hu' : HasTy S k .one [] (.unglue φ' e' g') A)
    (hφ' : φ'.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ee' : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A))
    (hAA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A.isub σ))
    (hTT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ))
    (hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)) :
    RE2 S k A (.unglue φ e g) (.unglue φ' e' g') ∧
      ∀ k' (σ : ISub k' k), ¬ (ival (idEnv k') (φ.subst σ.τ)).holds → ∀ ψ0 e00 t00 a00,
        RedW S (g.isub σ) (.glueEl ψ0 e00 t00 a00) → RE2 S k' (A.isub σ) a00 ((Tm.unglue φ' e' g').isub σ) := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hXA : ∀ k' (σ : ISub k' k), TyCode k' (semK S k' (A.isub σ)) := fun k' σ =>
    tyCode_of_univ hW (HasTy.isubS hW hA0 σ)
  have hgE := RE2.typed hgg
  unfold RE2 at hgg
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn'] at hgg
  obtain ⟨-, -, -, hmain, hcoh, -⟩ := hgg
  obtain ⟨l2, hG2, eG2⟩ := glue_annot_eq hW hG hφ' h12 h21 ee'
  have hg' : HasTy S k .one [] g' (.glue A φ' T e') := hgE.2.1.conv eG2
  have hΦ : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  have hΦ' : (cof .one φ').Scoped k := ⟨trivial, hφ'⟩
  -- facts at a restriction where the face holds
  have hent : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → I.Entails .one (φ.subst σ.τ) :=
    fun σ hh => (holds_iff_entails (I.scoped_subst hφs σ.sc)).1 hh
  have hent' : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → I.Entails .one (φ'.subst σ.τ) :=
    fun σ hh => ent_trans (hent σ hh) (ent_subst h12 σ.τ)
  have hface : ∀ {k'} (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds),
      (Cof.restr (ival (idEnv k) φ).face ((Hom.id k).comp σ.hom)).holds := fun σ hh => by
    rw [Hom.id_comp]; exact (face_holds_iff hφs σ).2 hh
  -- the fibers of related elements where the face holds
  have fib : ∀ {k'} (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) {x y : Tm},
      (Comp2 S (dat (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k))) k' ((Hom.id k).comp σ.hom))
        k' k' (Hom.id k')).el ((Tm.glue A φ T e).isub σ) x y → RE2 S k' (T.isub σ) x y := by
    intro k' σ hh x y h
    rw [Hom.id_comp, dat_glue_fiber σ ((face_holds_iff hφs σ).2 hh)] at h
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh
    have hX := tyCode_of_univ hW hTσ
    have hGσ : IsTyK S k' ((Tm.glue A φ T e).isub σ) := ⟨l, .inl (HasTy.isubS hW hG σ)⟩
    have hfc : TyEq S k' ((Tm.glue A φ T e).isub σ) (T.isub σ) := by
      rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ (hent σ hh)
    have hTG : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
      refine ty_expandSR hW hX (hGσ.of_tyEq hfc) hGσ ?_ (hTT k' σ hh)
      rw [isub_glue] at hGσ ⊢
      exact stable_glue hW hGσ (hent σ hh)
    have P := per2_tyCode hW hX k' (Hom.id k')
    exact P.conv (P.symTy hTG) h
  -- typings at a restriction
  have hgσ : ∀ {k'} (σ : ISub k' k), HasTy S k' .one [] (g.isub σ) (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) :=
    fun σ => by have := HasTy.isubS hW hgE.1 σ; rwa [isub_glue] at this
  have hgσ' : ∀ {k'} (σ : ISub k' k), HasTy S k' .one [] (g'.isub σ)
      (.glue (A.isub σ) (φ'.subst σ.τ) (T.isub σ) (e'.isub σ)) :=
    fun σ => by have := HasTy.isubS hW hg' σ; rwa [isub_glue] at this
  have heσ : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      HasTy S k' .one [] (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := fun σ hh => by
    have := face_ty hW hφs he0 σ hh; rwa [isub_equiv] at this
  have heσ' : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      HasTy S k' .one [] (e'.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := fun σ hh => by
    have := face_ty hW hφs (HasTy.eqL ee') σ hh; rwa [isub_equiv] at this
  have hAσ : ∀ {k'} (σ : ISub k' k), HasTy S k' .one [] (A.isub σ) (.univ lA) := fun σ => HasTy.isubS hW hA0 σ
  -- `unglue` where the face holds is the application of the equivalence
  have stepF : ∀ {k'} (σ : ISub k' k) {ψ : I} {e1 g1 : Tm}, I.Entails .one ψ →
      step S (.unglue ψ e1 g1) = some (.app (.fst e1) g1) := fun σ ψ e1 g1 h => by
    simp [step, show I.entails .one ψ = true from h]
  have stabF : ∀ {k'} (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds),
      StableE S k' (A.isub σ) ((Tm.unglue φ' e' g').isub σ) (.app (.fst (e'.isub σ)) (g'.isub σ)) := by
    intro k' σ hh k'' ρ
    have hh' : (ival (idEnv k'') (φ.subst (σ.comp ρ).τ)).holds := by
      have := ent_subst (hent σ hh) ρ.τ
      rw [holds_iff_entails (I.scoped_subst hφs (σ.comp ρ).sc), I_subst_comp]; simpa [I.subst] using this
    simp only [isub_unglue, isub_app, isub_fst, Tm.isub_isub, ← I_subst_comp]
    exact ⟨.step (stepF (σ.comp ρ) (hent' _ hh')) (.refl _),
      EqTm.unglueFace (hent' _ hh') (hgσ' (σ.comp ρ)) (hAσ _) (heσ' _ hh')⟩
  -- the base of a normal form of `g`, related to the other side by head expansion of the other side
  have base : ∀ k' (σ : ISub k' k), ¬ (ival (idEnv k') (φ.subst σ.τ)).holds → ∀ ψ0 e00 t00 a00,
      RedW S (g.isub σ) (.glueEl ψ0 e00 t00 a00) → RE2 S k' (A.isub σ) a00 ((Tm.unglue φ' e' g').isub σ) := by
    intro k' σ hh ψ0 e00 t00 a00 hw
    have hne : ¬ I.Entails .one (φ.subst σ.τ) := fun h => hh ((holds_iff_entails (I.scoped_subst hφs σ.sc)).2 h)
    have hnf : ¬ (Cof.restr (ival (idEnv k) φ).face ((Hom.id k).comp σ.hom)).holds := by
      rw [Hom.id_comp, face_holds_iff hφs σ]; exact hh
    have hm := hmain k' σ
    unfold glueLocE at hm; rw [if_neg hnf] at hm
    obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', q1, q1', q2, q2', ee0, ee0', ha0, hfibs⟩ := hm
    have eq1 := RedW.unique r1.1 (by rw [isub_glue]; exact (redT_glue_self (S := S) (k := k') hne).1)
    simp only [Tm.glue.injEq] at eq1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := eq1
    rw [Hom.id_comp, Comp2_res_el hW hA0] at ha0
    have hGσ := HasTy.isubS hW hG σ
    rw [isub_glue] at hGσ
    have rgσ := rg.2
    rw [isub_glue] at rgσ
    have ew0 := RedW.unique rg.1 hw
    simp only [Tm.glueEl.injEq] at ew0
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ew0
    have hXσ := hXA k' σ
    refine (perK hW hXσ).symEl (hAA k' σ) ((he2_tyCode hW hXσ k' (Hom.id k') (A.isub σ) (A.isub σ)
      ((Tm.unglue φ' e' g').isub σ) a0).2 (hAA k' σ) (HasTy.isubS hW hu' σ) (RE2.typed ha0).1 fun k'' ρ => ?_)
    rw [Hom.id_comp, Comp2_res_el hW (hAσ σ), Tm.isub_isub]
    simp only [isub_unglue, Tm.isub_isub, ← I_subst_comp]
    have hcohσ := hcoh k' σ hnf _ rg.1 k'' ρ
    have hcf : ∀ (hτ : (ival (idEnv k'') (φ.subst (σ.comp ρ).τ)).holds),
        (Cof.restr (ival (idEnv k) φ).face ((Hom.id k).comp (σ.comp ρ).hom)).holds := fun hτ => hface _ hτ
    by_cases hh2 : (ival (idEnv k'') (φ.subst (σ.comp ρ).τ)).holds
    · refine ⟨.app (.fst (e'.isub (σ.comp ρ))) (g'.isub (σ.comp ρ)), .step (stepF (σ.comp ρ) (hent' _ hh2)) (.refl _),
        EqTm.unglueFace (hent' _ hh2) (hgσ' _) (hAσ _) (heσ' _ hh2), ?_⟩
      have hb := (hfibs k'' ρ (by rw [Hom.id_comp] at *; exact (face_holds_iff hφs (σ.comp ρ)).2 hh2)).2.1
      rw [Hom.id_comp, Comp2_res_el hW hA0] at hb
      simp only [Tm.isub_isub] at hb
      have hc := fib (σ.comp ρ) hh2 (hcohσ.1 (hcf hh2) ψ e0 t0 a0 rfl)
      have hgτ := fib (σ.comp ρ) hh2 (by have := hmain k'' (σ.comp ρ); unfold glueLocE at this
                                         rwa [if_pos (hcf hh2)] at this)
      have ht0 := RE2.trans hW (hTT _ _ hh2) hc hgτ
      have happ := RE2_equiv_app hW (hE _ _ hh2) ht0
      exact RE2.symm hW (hAA _ _) (RE2.trans hW (hAA _ _) hb happ)
    · have hne2 : ¬ I.Entails .one (φ.subst (σ.comp ρ).τ) :=
        fun h => hh2 ((holds_iff_entails (I.scoped_subst hφs (σ.comp ρ).sc)).2 h)
      have hne2' : ¬ I.Entails .one (φ'.subst (σ.comp ρ).τ) :=
        fun h => hne2 (ent_trans h (ent_subst h21 _))
      have hnf2 : ¬ (Cof.restr (ival (idEnv k) φ).face ((Hom.id k).comp (σ.comp ρ).hom)).holds := by
        rw [Hom.id_comp, face_holds_iff hφs]; exact hh2
      have hm2 := hmain k'' (σ.comp ρ)
      unfold glueLocE at hm2; rw [if_neg hnf2] at hm2
      obtain ⟨A2, φ2, T2, e2, χ, f0, s0, b0, χ', f0', s0', b0', r2, rh, rh', p1, p1', p2, p2', ff0, ff0', hb0, -⟩ := hm2
      have e2' := RedW.unique r2.1 (by rw [isub_glue]; exact (redT_glue_self (S := S) (k := k'') hne2).1)
      simp only [Tm.glue.injEq] at e2'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e2'
      rw [Hom.id_comp, Comp2_res_el hW hA0] at hb0
      -- the other side's base, with the other side's annotations
      have hG2τ := HasTy.isubS hW hG2 (σ.comp ρ)
      rw [isub_glue] at hG2τ
      have eG2τ := EqTm.isubS hW eG2 (σ.comp ρ)
      rw [isub_glue, isub_glue] at eG2τ
      have rh'2 : EqTm S k'' .one [] (g'.isub (σ.comp ρ)) (.glueEl χ' f0' s0' b0')
          (.glue (A.isub (σ.comp ρ)) (φ'.subst (σ.comp ρ).τ) (T.isub (σ.comp ρ)) (e'.isub (σ.comp ρ))) := by
        have := rh'.2; rw [isub_glue] at this; exact this.conv eG2τ
      have q21' : I.Entails (φ.subst (σ.comp ρ).τ) (φ'.subst (σ.comp ρ).τ) := ent_subst h12 _
      have q12' : I.Entails (φ'.subst (σ.comp ρ).τ) (φ.subst (σ.comp ρ).τ) := ent_subst h21 _
      have c' : I.Entails (cof .one (φ'.subst (σ.comp ρ).τ)) (cof .one (φ.subst (σ.comp ρ).τ)) :=
        ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) q12')
      have hs' : (cof .one (φ'.subst (σ.comp ρ).τ)).Scoped k'' := ⟨trivial, I.scoped_subst hφ' (σ.comp ρ).sc⟩
      have ee'τ : EqTm S k'' (cof .one (φ.subst (σ.comp ρ).τ)) [] (e'.isub (σ.comp ρ)) (e.isub (σ.comp ρ))
          (Tm.equiv (T.isub (σ.comp ρ)) (A.isub (σ.comp ρ))) := by
        have := EqTm.isubF hW hΦ ee' (σ.comp ρ); rwa [isub_equiv] at this
      have ff1 : EqTm S k'' (cof .one (φ'.subst (σ.comp ρ).τ)) [] f0' (e'.isub (σ.comp ρ))
          (Tm.equiv (T.isub (σ.comp ρ)) (A.isub (σ.comp ρ))) :=
        EqTm.restrict hs' c' (ff0'.trans ee'τ.symm)
      refine ⟨b0', red_unglue_base hne2' rh'.1,
        unglue_base_eq hW hG2τ rh'2 (ent_trans p2 q21') (ent_trans q12' p2') ff1 (RE2.typed hb0).2.1 hCW hne2', ?_⟩
      -- the coherence of the left side and the relation at this stage
      have hcl := hcohσ.2 hnf2
      unfold glueLocE at hcl; rw [if_neg hnf2] at hcl
      obtain ⟨A3, φ3, T3, e3, χ3, f3, s3, b3, χ3', f3', s3', b3', r3, rw3, rw3', -, -, -, -, -, -, hb3, -⟩ := hcl
      have hneψ : ¬ I.Entails .one (ψ.subst ρ.τ) := fun h => hne2 (by
        have := ent_trans h (ent_subst q1 ρ.τ); rwa [← I_subst_comp] at this)
      have ew := RedW.unique rw3.1 (redE_glueEl_self (S := S) (k := k'') (X := (Tm.glue A φ T e).isub (σ.comp ρ))
        hneψ (by have := HasTy.isubS hW (HasTy.eqR rg.2) ρ; rwa [Tm.isub_isub] at this)).1
      simp only [Tm.glueEl.injEq] at ew
      obtain ⟨-, -, -, rfl⟩ := ew
      have ew' := RedW.unique rw3'.1 rh.1
      simp only [Tm.glueEl.injEq] at ew'
      obtain ⟨-, -, -, rfl⟩ := ew'
      have et := RedW.unique r3.1 (by rw [isub_glue]; exact (redT_glue_self (S := S) (k := k'') hne2).1)
      simp only [Tm.glue.injEq] at et
      obtain ⟨rfl, -, -, -⟩ := et
      rw [Hom.id_comp, Comp2_res_el hW hA0] at hb3
      exact RE2.symm hW (hAA _ _) (RE2.trans hW (hAA _ _) hb3 hb0)
  -- the relation at `A`, through head expansion
  refine ⟨?_, base⟩
  have hX0 := hXA k (ISub.id k)
  rw [isub_id_of_closed (closed_of_ty hW hA0)] at hX0
  refine (he2_tyCode hW hX0 k (Hom.id k) A A (.unglue φ e g) (.unglue φ' e' g')).2
    (by have := hAA k (ISub.id k); rwa [isub_id_of_closed (closed_of_ty hW hA0)] at this) hu hu' fun k' σ => ?_
  rw [Hom.id_comp, Comp2_res_el hW hA0]
  by_cases hh : (ival (idEnv k') (φ.subst σ.τ)).holds
  · -- the face holds: `unglue` is the application of the equivalences
    refine ⟨.app (.fst (e.isub σ)) (g.isub σ), ?_, ?_, ?_⟩
    · rw [isub_unglue]; exact .step (stepF σ (hent σ hh)) (.refl _)
    · rw [isub_unglue]; exact EqTm.unglueFace (hent σ hh) (hgσ σ) (hAσ σ) (heσ σ hh)
    · have hf := fib σ hh (by have := hmain k' σ; unfold glueLocE at this; rwa [if_pos (hface σ hh)] at this)
      have happ := RE2_equiv_app hW (hE k' σ hh) hf
      exact el_expandSR hW (hXA k' σ) (hAA k' σ) (RE2.typed happ).1 (HasTy.isubS hW hu' σ) (stabF σ hh) happ
  · -- the face does not hold: `unglue` is the base of the normal form
    have hne : ¬ I.Entails .one (φ.subst σ.τ) := fun h => hh ((holds_iff_entails (I.scoped_subst hφs σ.sc)).2 h)
    have hnf : ¬ (Cof.restr (ival (idEnv k) φ).face ((Hom.id k).comp σ.hom)).holds := by
      rw [Hom.id_comp, face_holds_iff hφs σ]; exact hh
    have hm := hmain k' σ
    unfold glueLocE at hm; rw [if_neg hnf] at hm
    obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', q1, q1', q2, q2', ee0, ee0', ha0, hfibs⟩ := hm
    have eq1 := RedW.unique r1.1 (by rw [isub_glue]; exact (redT_glue_self (S := S) (k := k') hne).1)
    simp only [Tm.glue.injEq] at eq1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := eq1
    rw [Hom.id_comp, Comp2_res_el hW hA0] at ha0
    have hGσ := HasTy.isubS hW hG σ
    rw [isub_glue] at hGσ
    have rgσ := rg.2
    rw [isub_glue] at rgσ
    exact ⟨a0, by rw [isub_unglue]; exact red_unglue_base hne rg.1,
      by rw [isub_unglue]; exact unglue_base_eq hW hGσ rgσ q1 q1' ee0 (RE2.typed ha0).1 hCW hne, base k' σ hh _ _ _ _ rg.1⟩

/-- `unglue` of related elements of a Glue type whose face does not hold. -/
theorem RE2_unglue {A T e e' g g' : Tm} {φ φ' : I} {l : ℕ} (hCW : GlueCohW S)
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hn : ¬ (ival (idEnv k) φ).holds)
    (hgg : RE2 S k (.glue A φ T e) g g')
    (hu : HasTy S k .one [] (.unglue φ e g) A) (hu' : HasTy S k .one [] (.unglue φ' e' g') A)
    (hφ' : φ'.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ee' : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A))
    (hAA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A.isub σ))
    (hTT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ))
    (hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)) :
    RE2 S k A (.unglue φ e g) (.unglue φ' e' g') :=
  (RE2_unglue_and hW hCW hG hn hgg hu hu' hφ' h12 h21 ee' hAA hTT hE).1


end

end Model.Whnf
