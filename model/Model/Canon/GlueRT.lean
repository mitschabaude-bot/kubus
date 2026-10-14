import Model.Canon.GlueEquiv
import Model.Canon.GlueBasic
import Model.Canon.Statement
import Model.Whnf.Sound

/-!
# Canonicity: computable Glue types and their elements
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem semK_isub_sem (t : Tm) (σ : ISub k' k) :
    semK S k' (t.isub σ) = sem S t k' ((idEnv k).restr σ.hom) (TEnv.restr (γ0 k) σ.hom) := by
  unfold semK
  rw [show t.isub σ = t.dsubst σ.τ from rfl, sem_dsubst, γ0_restr, ← env_isub]

variable (hW : WfSig S)
include hW

/-- The code of a closed Glue type. -/
theorem semK_glueT {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) :
    semK S k (.glue A φ T e) = glueC k (semK S k A) (ival (idEnv k) φ).face
      (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k)))
      (partialKV k (ival (idEnv k) φ).face (faceVals S e (idEnv k) (γ0 k))) := by
  have hne : semK S k (.glue A φ T e) ≠ ∅ := semK_ne hW hG
  obtain ⟨hT, he⟩ := cond_of_sem_glue hne
  exact sem_glue hT he

omit hW in
/-- The fiber type of a Glue type, where the face holds, has the fiber's code. -/
theorem dat_glue_fiber {T : Tm} {φ : I} (σ : ISub k' k) (hh : (Cof.restr (ival (idEnv k) φ).face σ.hom).holds) :
    dat (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k))) k' σ.hom = semK S k' (T.isub σ) := by
  rw [dat_partialKV_holds hh, semK_isub_sem]; rfl

omit hW in
theorem face_holds_iff {φ : I} (hφ : φ.Scoped k) (σ : ISub k' k) :
    (Cof.restr (ival (idEnv k) φ).face σ.hom).holds ↔ (ival (idEnv k') (φ.subst σ.τ)).holds := by
  rw [DM.holds_iff_face_holds, face_isub rfl σ]

/-- The fiber type of a closed Glue type is typed where the face holds. -/
theorem glue_fiber_ty {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) :
    ∃ l', HasTy S k' .one [] (T.isub σ) (.univ l') ∧ HasTy S k' .one [] (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := by
  obtain ⟨l', ⟨-, hφ, hT, he⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  have hent := entails_of_holds (I.scoped_subst hφ σ.sc) hh
  have hXs : (cof .one φ).Scoped k := ⟨trivial, hφ⟩
  have hT' := HasTy.isubF hW hXs (minimal_to_spec hT) σ
  have he' := HasTy.isubF hW hXs (minimal_to_spec he) σ
  rw [isub_equiv] at he'
  refine ⟨l', HasTy.restrict trivial (ent_cof_one hW hent) hT', HasTy.restrict trivial (ent_cof_one hW hent) he'⟩

/-- A closed Glue type whose face does not hold is computable when its base, its fiber (on the
face) and its equivalence (on the face) are. -/
theorem RT_glue_intro {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hn : ¬ (ival (idEnv k) φ).holds) (hA : ∀ k' (σ : ISub k' k), RT S k' (A.isub σ))
    (hT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT S k' (T.isub σ))
    (he : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ)) : RT S k (.glue A φ T e) := by
  obtain ⟨l', ⟨hA0, hφ, -, he0⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  have hAt := minimal_to_spec hA0
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  unfold RT
  rw [semK_glueT hW hG, Comp_glueC (kv_semK_of_univ hW hAt) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
  refine ⟨⟨⟨l, .inl hG⟩, by rw [← semK_glueT hW hG, res_id (kv_semK_of_univ hW hG)]⟩, A, φ, T, e, TyEq.refl _, hφ, rfl,
    ⟨l', hAt, minimal_to_spec he0⟩, fun k' σ => ?_, fun k' σ hh => ?_⟩
  · rw [Comp_res_el hW hAt]; exact hA k' σ
  · have hh' := (face_holds_iff hφ σ).1 hh
    obtain ⟨lT, hTσ, heσ⟩ := glue_fiber_ty hW hG σ hh'
    rw [dat_glue_fiber σ hh]
    refine ⟨hT k' σ hh', ?_⟩
    obtain ⟨lE, hE⟩ := ty_of_tyEq hW (isTyK_of_ty hW heσ) (TyEq.refl _) (fun l h => by cases h)
    have hGA : GoodR S k' (fun k'' σ' => (Comp S (semK S k A) k k'' (σ.comp σ').hom).el) (A.isub σ) := by
      have := goodR_CR hW hAt |>.restr σ
      exact this
    refine (goodR_equivE hW hE (goodR_CR hW hTσ) hGA k' (ISub.id k') _ _ ?_).2 (he k' σ hh')
    rw [isub_id_of_closed (closed_of_ty hW hE)]; exact TyEq.refl _

/-- Elements of a closed Glue type whose face does not hold. -/
theorem RE_glue_intro {A T e g : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hn : ¬ (ival (idEnv k) φ).holds) (hg : HasTy S k .one [] g (.glue A φ T e))
    (hun : ∀ k' (σ : ISub k' k), RE S k' (A.isub σ) (.unglue (φ.subst σ.τ) (e.isub σ) (g.isub σ)))
    (hgT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RE S k' (T.isub σ) (g.isub σ)) :
    RE S k (.glue A φ T e) g := by
  obtain ⟨l', ⟨hA0, hφ, -, he0⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  have hAt := minimal_to_spec hA0
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hmem := mem_of_ty hW hg
  unfold RE
  rw [semK_glueT hW hG, Comp_glueC (kv_semK_of_univ hW hAt) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
  rw [semK_glueT hW hG] at hmem
  refine ⟨hg, by rw [res_id (isKV_glueC _ _ _ _)]; exact hmem, hg, A, φ, T, e, TyEq.refl _, hφ, rfl,
    ⟨l', hAt, minimal_to_spec he0⟩, fun k' σ => ?_, fun k' σ hh => ?_⟩
  · rw [Comp_res_el hW hAt]; exact hun k' σ
  · rw [dat_glue_fiber σ hh]; exact hgT k' σ ((face_holds_iff hφ σ).1 hh)

/-- The base and equivalence of a typed closed Glue type. -/
theorem glue_data {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) :
    φ.Scoped k ∧ ∃ l', HasTy S k .one [] A (.univ l') ∧ HasTy S k (cof .one φ) [] e (Tm.equiv T A) := by
  obtain ⟨l', ⟨hA0, hφ, -, he0⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  exact ⟨hφ, l', minimal_to_spec hA0, minimal_to_spec he0⟩

/-- A glue element of a closed Glue type whose face does not hold is coherent at the base of that
Glue type: its own coherence premise is at the base of its annotation, which the compatibility of
Glue types (`GlueCompat`) identifies with the base (the annotation cannot be a universe, whose
code differs from a Glue code). -/
theorem glueEl_coh (hGC : GlueCompat S) {A T e t a : Tm} {φ : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hn : ¬ (ival (idEnv k) φ).holds)
    (hg : HasTy S k .one [] (.glueEl φ e t a) (.glue A φ T e)) :
    EqTm S k (cof .one φ) [] a (.app (.fst e) t) A := by
  obtain ⟨A2, T2, l2, ⟨hG2, hcoh⟩, ch⟩ := gen_glueEl_coh (spec_to_minimal hW hg) rfl
  have r := Model.Whnf.chain_rel hW ch (Rel.refl hG2 (Model.Whnf.lvl_bound hW hG2))
  obtain ⟨-, ⟨-, hφs, -, -⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  rcases r with ⟨m, -, eG⟩ | ⟨l0, m, -, eU⟩
  · obtain ⟨l1, hA⟩ := (hGC k A2 A T2 T e e φ φ m (minimal_to_spec_eq eG)
      (fun h => hn ((holds_iff_entails hφs).2 h)) (I.entails_refl _) (I.entails_refl _)).1
    exact (EqTm.conv (minimal_to_spec_eq hcoh) (EqTm.restrict ⟨trivial, hφs⟩ (ent_and_left _ _) hA)).symm
  · exfalso
    have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
    have hs := semK_eq hW (minimal_to_spec_eq eU)
    rw [semK_glueT hW (minimal_to_spec hG2)] at hs
    exact glueC_ne_univC _ _ _ hn' (isCof_ival_face _ _) l0 hs

/-- A Glue introduction is computable when its base and (on the face) fiber components are. -/
theorem RE_glueEl_intro (hGC : GlueCompat S) {A T e t a : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hn : ¬ (ival (idEnv k) φ).holds) (hg : HasTy S k .one [] (.glueEl φ e t a) (.glue A φ T e))
    (ha : ∀ k' (σ : ISub k' k), RE S k' (A.isub σ) (a.isub σ))
    (ht : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RE S k' (T.isub σ) (t.isub σ)) :
    RE S k (.glue A φ T e) (.glueEl φ e t a) := by
  obtain ⟨hφ, hdata⟩ := glue_data hW hG
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  refine RE_glue_intro hW hG hn hg (fun k' σ => ?_) (fun k' σ hh => ?_)
  · have hgσ := HasTy.isubS hW hg σ
    rw [isub_glue] at hgσ
    have hu := unglue_ty hW (by rw [← isub_glue]; exact hGK.isub hW σ) (glueData_isub hW hφ hdata σ) hgσ
    have hc := EqTm.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφ⟩) (glueEl_coh hW hGC hG hn hg) σ
    exact (ha k' σ).conv hW (TyEq.refl _) (EqTm.glueBeta hu (Comp_el_typed (ha k' σ)).1 hc).symm
  · have hgσ := HasTy.isubS hW hg σ
    rw [isub_glue] at hgσ
    have hent := entails_of_holds (I.scoped_subst hφ σ.sc) hh
    have hface := glue_face_tyEq hW (by rw [← isub_glue]; exact hGK.isub hW σ) hent
    exact (ht k' σ hh).conv hW (TyEq.refl _) ((EqTm.glueElFace hent hgσ).tyConv hface).symm

/-- The components of an element of a closed Glue type whose face does not hold (using the
compatibility of Glue annotations to compare with the recorded decomposition). -/
theorem RE_glue_elim (hGC : GlueCompat S) {A T e g : Tm} {φ : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hn : ¬ (ival (idEnv k) φ).holds)
    (hg : RE S k (.glue A φ T e) g) :
    (∀ k' (σ : ISub k' k), RE S k' (A.isub σ) (.unglue (φ.subst σ.τ) (e.isub σ) (g.isub σ))) ∧
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RE S k' (T.isub σ) (g.isub σ)) := by
  obtain ⟨l', ⟨hA0, hφ, hT0, he0⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hG) rfl
  have hAt := minimal_to_spec hA0
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  unfold RE at hg
  rw [semK_glueT hW hG, Comp_glueC (kv_semK_of_univ hW hAt) (isKV_partialKV _ _) (isCof_ival_face _ _) hn'] at hg
  obtain ⟨hgt, -, -, A1, φ1, T1, e1, hE, hφ1, hf1, hdata1, hun1, hT1⟩ := hg
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  have hG1 := hGK.of_tyEq hE
  -- base part: compare the two decompositions
  have hbase : TyEq S k A A1 ∧ EqTm S k .one [] (.unglue φ1 e1 g) (.unglue φ e g) A := by
    have hu : HasTy S k .one [] (.unglue φ e g) A := unglue_ty hW hGK ⟨l', hAt, minimal_to_spec he0⟩ hgt
    rcases hE with hE | ⟨l0, hE⟩
    · injection hE with h1 h2 h3 h4; subst h1 h2 h3 h4
      exact ⟨TyEq.refl _, EqTm.refl hu⟩
    · have h12 := ent_of_face_eq hφ hφ1 hf1.symm
      have h21 := ent_of_face_eq hφ1 hφ hf1
      obtain ⟨⟨l1, hAA⟩, hee⟩ := hGC k A A1 T T1 e e1 φ φ1 l0 hE
        (fun h => hn ((holds_iff_entails hφ).2 h)) h12 h21
      have hu1 : HasTy S k .one [] (.unglue φ1 e1 g) A :=
        (unglue_ty hW hG1 hdata1 (hgt.tyConv (.inr ⟨l0, hE⟩))).tyConv (show TyEq S k A A1 from .inr ⟨l1, hAA⟩).symm
      exact ⟨.inr ⟨l1, hAA⟩, (EqTm.unglue hu hu1 h12 h21 hee (EqTm.refl hgt)).symm⟩
  refine ⟨fun k' σ => ?_, fun k' σ hh => ?_⟩
  · have h1 := (CR_RE hW hAt σ (hbase.1.isub hW σ)).1 (hun1 k' σ)
    have := EqTm.isubS hW hbase.2 σ
    rw [isub_unglue, isub_unglue] at this
    exact h1.conv hW (hbase.1.isub hW σ).symm this
  · have hh' : (Cof.restr (ival (idEnv k) φ).face σ.hom).holds := (face_holds_iff hφ σ).2 hh
    have h1 := hT1 k' σ hh'
    rw [dat_glue_fiber σ hh'] at h1
    have hface := glue_face_tyEq hW (by rw [← isub_glue]; exact hG1.isub hW σ) (entails_of_face hφ1 hf1 σ hh')
    have hface0 := glue_face_tyEq hW (by rw [← isub_glue]; exact hGK.isub hW σ)
      (entails_of_holds (I.scoped_subst hφ σ.sc) hh)
    have hTσ : TyEq S k' (T.isub σ) (T1.isub σ) :=
      hface0.symm.trans hW ((by rw [← isub_glue, ← isub_glue]; exact hE.isub hW σ : TyEq S k' _ _).trans hW hface)
    have h2 : RE S k' (T1.isub σ) (g.isub σ) := by
      unfold RE; rw [← semK_tyEq hW hTσ]; exact h1
    exact h2.conv_ty hW hTσ.symm

end

end Model.Canon
