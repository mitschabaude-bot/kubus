import Model.Canon.Conv

/-!
# Canonicity: Glue codes, conversion and restriction
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-- The computability of a Glue code at a restriction: that of `T` where the face holds. -/
theorem Comp_glueC_at {A Tp ep : V} {φ : Cof m} (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f)) (f : Hom k m) :
    Comp S (glueC m A φ Tp ep) m k f =
      if (φ.restr f).holds then Comp S (dat Tp k f) k k (Hom.id k)
      else Comp S (glueC k (res f A) (φ.restr f) (res f Tp) (res f ep)) k k (Hom.id k) := by
  rw [Comp_eq_res (IsKV.ne_empty (isKV_glueC _ _ _ _)), res_glueC hTp hTkv hφ f]
  split <;> rfl

/-- The face of a Glue type under a substitution. -/
theorem face_isub {φ1 : I} {φ : Cof k} (hf : (ival (idEnv k) φ1).face = φ) (σ : ISub k' k) :
    (ival (idEnv k') (φ1.subst σ.τ)).face = φ.restr σ.hom := by
  rw [← hf, ← DM.face_restr, ival_subst, env_isub, ival.restr]

theorem entails_of_face {φ1 : I} {φ : Cof k} (hs : φ1.Scoped k) (hf : (ival (idEnv k) φ1).face = φ)
    (σ : ISub k' k) (hh : (φ.restr σ.hom).holds) : I.Entails .one (φ1.subst σ.τ) := by
  rw [← holds_iff_entails (I.scoped_subst hs σ.sc), DM.holds_iff_face_holds, face_isub hf]; exact hh

theorem not_entails_of_face {φ1 : I} {φ : Cof k} (hs : φ1.Scoped k) (hf : (ival (idEnv k) φ1).face = φ)
    (σ : ISub k' k) (hh : ¬ (φ.restr σ.hom).holds) : ¬ I.Entails .one (φ1.subst σ.τ) := by
  rw [← holds_iff_entails (I.scoped_subst hs σ.sc), DM.holds_iff_face_holds, face_isub hf]; exact hh

variable (hW : WfSig S)
include hW

/-- A Glue type is its fiber type where the face holds. -/
theorem glue_face_tyEq {A1 T1 e1 : Tm} {φ1 : I} (hG : IsTyK S k (.glue A1 φ1 T1 e1)) (h : I.Entails .one φ1) :
    TyEq S k (.glue A1 φ1 T1 e1) T1 := by
  obtain ⟨l, hG | hG⟩ := hG
  · exact .inr ⟨l, EqTm.glueFace h hG⟩
  · cases hG

/-- Typing of `unglue`, from the data recorded by computability. -/
theorem unglue_ty {A1 T1 e1 g : Tm} {φ1 : I} (hG : IsTyK S k (.glue A1 φ1 T1 e1))
    (hA : ∃ l, HasTy S k .one [] A1 (.univ l) ∧ HasTy S k (cof .one φ1) [] e1 (Tm.equiv T1 A1))
    (hg : HasTy S k .one [] g (.glue A1 φ1 T1 e1)) : HasTy S k .one [] (.unglue φ1 e1 g) A1 := by
  obtain ⟨l, hG | hG⟩ := hG
  · obtain ⟨l', hA, he⟩ := hA
    have hl := lvl_of_ty hW hG
    have hl' := lvl_of_ty hW hA
    exact HasTy.unglue (hG.cumulTo (le_max_left l l') (max_le hl hl')) (hA.cumulTo (le_max_right l l')
      (max_le hl hl')) he hg
  · cases hG

theorem unglue_eq {A1 T1 e1 g g' : Tm} {φ1 : I} (hG : IsTyK S k (.glue A1 φ1 T1 e1))
    (hA : ∃ l, HasTy S k .one [] A1 (.univ l) ∧ HasTy S k (cof .one φ1) [] e1 (Tm.equiv T1 A1))
    (hgg : EqTm S k .one [] g g' (.glue A1 φ1 T1 e1)) :
    EqTm S k .one [] (.unglue φ1 e1 g) (.unglue φ1 e1 g') A1 :=
  EqTm.unglue (unglue_ty hW hG hA (HasTy.eqL hgg)) (unglue_ty hW hG hA (HasTy.eqR hgg))
    (I.entails_refl _) (I.entails_refl _) (EqTm.refl hA.choose_spec.2) hgg

theorem glueData_isub {A1 T1 e1 : Tm} {φ1 : I} (hs : φ1.Scoped k)
    (hA : ∃ l, HasTy S k .one [] A1 (.univ l) ∧ HasTy S k (cof .one φ1) [] e1 (Tm.equiv T1 A1)) (σ : ISub k' k) :
    ∃ l, HasTy S k' .one [] (A1.isub σ) (.univ l) ∧
      HasTy S k' (cof .one (φ1.subst σ.τ)) [] (e1.isub σ) (Tm.equiv (T1.isub σ) (A1.isub σ)) := by
  obtain ⟨l, hA, he⟩ := hA
  refine ⟨l, HasTy.isubS hW hA σ, ?_⟩
  have := HasTy.isubF hW (show (cof .one φ1).Scoped k from ⟨trivial, hs⟩) he σ
  rwa [isub_equiv] at this

omit hW in
theorem isub_glue (A T e : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.glue A φ T e).isub σ = .glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ) := rfl

omit hW in
theorem isub_unglue (e g : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.unglue φ e g).isub σ = .unglue (φ.subst σ.τ) (e.isub σ) (g.isub σ) := rfl

theorem cv_glueC {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
    (ihA : CV S m A) (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → CV S k (dat Tp k f)) :
    CV S m (glueC m A φ Tp ep) := by
  intro k f T T' t t'
  rw [Comp_glueC_at hφ hTp hTkv f]
  split
  · rename_i hh; exact ihT k f hh k (Hom.id k) T T' t t'
  rename_i hh
  rw [Comp_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr f) hh]
  simp only [Comp_res (IsKV.ne_empty hA), dat_res, Cof.restr_restr]
  constructor
  · rintro ⟨⟨hT, hsem⟩, A1, φ1, T1, e1, hE, rest⟩ hTT'
    exact ⟨⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, A1, φ1, T1, e1, hTT'.symm.trans hW hE, rest⟩
  · rintro ⟨ht, hmem, -, A1, φ1, T1, e1, hE, hs, hf, hdata, hun, hT⟩ hTT' htt'
    have ht' := HasTy.eqR htt'
    have hE' := hTT'.symm.trans hW hE
    obtain ⟨lG, hG⟩ := ty_of_tyEq hW (isTyK_of_ty hW ht') hE' (fun l h => by cases h)
    have hGσ : ∀ k' (σ : ISub k' k), IsTyK S k' (.glue (A1.isub σ) (φ1.subst σ.τ) (T1.isub σ) (e1.isub σ)) :=
      fun k' σ => ⟨lG, .inl (by rw [← isub_glue, ← isub_univ lG σ]; exact HasTy.isubS hW hG σ)⟩
    have htσ : ∀ k' (σ : ISub k' k), EqTm S k' .one [] (t.isub σ) (t'.isub σ)
        (.glue (A1.isub σ) (φ1.subst σ.τ) (T1.isub σ) (e1.isub σ)) := fun k' σ => by
      rw [← isub_glue]; exact EqTm.isubS hW (htt'.tyConv hE') σ
    refine ⟨ht', mem_of_eq hW htt' hmem, ht', A1, φ1, T1, e1, hE', hs, hf, hdata, fun k' σ => ?_,
      fun k' σ hh' => ?_⟩
    · exact (ihA k' _ _ _ _ _).2 (hun k' σ) (TyEq.refl _)
        (unglue_eq hW (hGσ k' σ) (glueData_isub hW hs hdata σ) (htσ k' σ))
    · have hface := glue_face_tyEq hW (hGσ k' σ) (entails_of_face hs hf σ (by rwa [Cof.restr_restr]))
      exact (ihT k' _ hh' k' (Hom.id k') _ _ _ _).2 (hT k' σ hh') (TyEq.refl _) ((htσ k' σ).tyConv hface)

end

end Model.Canon
