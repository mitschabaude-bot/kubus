import Model.Whnf.Valid2CompPath

/-!
# Validity of the `hcomp` computation rule in Glue types

The typing derivation of the contractum (`KubusCore/Meta/KanGlue.lean`), with validity.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-! ### Paired Glue rules -/

theorem VTy.glue' {A T e : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ) (hA : VTy S Ψ Φ Γ A (.univ l))
    (hT : VTy S Ψ (cof Φ φ) Γ T (.univ l)) (he : VTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A)) :
    VTy S Ψ Φ Γ (.glue A φ T e) (.univ l) := by
  have h := HasTy0.glue hA.ty hφ hT.ty he.ty
  exact ⟨h, valid_glue hW hφ hA.v hT.v he.v h⟩

theorem VEq.glueFace' {A T e G : Tm} {φ : I} (hφ0 : I.Entails Φ φ) (hG : VTy S Ψ Φ Γ (.glue A φ T e) G) :
    VEq S Ψ Φ Γ (.glue A φ T e) T G := by
  have e := EqTm0.glueFace hφ0 hG.ty
  exact ⟨e, valid_glueFace hW hφ0 hG.v hG.ty (presup hW e).2⟩

theorem VTy.unglue' {A T e g : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : VTy S Ψ Φ Γ (.glue A φ T e) (.univ l)) (hA : VTy S Ψ Φ Γ A (.univ l))
    (he : VTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A)) (hg : VTy S Ψ Φ Γ g (.glue A φ T e)) :
    VTy S Ψ Φ Γ (.unglue φ e g) A := by
  have h := HasTy0.unglue hG.ty hA.ty he.ty hg.ty
  exact ⟨h, valid_unglue hW hφ hA.v he.ty he.v hg.v h⟩

theorem VEq.unglue' {A T e g g' : Tm} {φ : I} (hφ : φ.Scoped Ψ)
    (hu : VTy S Ψ Φ Γ (.unglue φ e g) A) (hu' : VTy S Ψ Φ Γ (.unglue φ e g') A)
    (he : VTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A)) (hg : VEq S Ψ Φ Γ g g' (.glue A φ T e)) :
    VEq S Ψ Φ Γ (.unglue φ e g) (.unglue φ e g') A := by
  have h := EqTm0.unglue hu.ty hu'.ty (ent_refl _) (ent_refl _) (EqTm0.refl he.ty) hg.eq
  exact ⟨h, valid_unglue_eq hW hφ hφ (ent_refl _) (ent_refl _) hu.v (EqTm0.refl he.ty) he.v hg.v hu.ty hu'.ty h⟩

theorem VEq.unglueFace' {A T e g : Tm} {φ : I} {l : ℕ} (hφ0 : I.Entails Φ φ)
    (hu : VTy S Ψ Φ Γ (.unglue φ e g) A) (hg : VTy S Ψ Φ Γ g (.glue A φ T e)) (hA : VTy S Ψ Φ Γ A (.univ l))
    (he : VTy S Ψ Φ Γ e (Tm.equiv T A)) :
    VEq S Ψ Φ Γ (.unglue φ e g) (.app (.fst e) g) A := by
  have h := EqTm0.unglueFace hφ0 hg.ty hA.ty he.ty
  exact ⟨h, valid_unglueFace hW hφ0 hu.v hu.ty hg.ty hA.ty he.ty (presup hW h).2⟩

theorem VTy.glueEl' {A T e t a : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : VTy S Ψ Φ Γ (.glue A φ T e) (.univ l)) (he : VTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (ht : VTy S Ψ (cof Φ φ) Γ t T) (ha : VTy S Ψ Φ Γ a A) (hat : VEq S Ψ (cof Φ φ) Γ (.app (.fst e) t) a A) :
    VTy S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e) := by
  have h := HasTy0.glueEl hG.ty he.ty ht.ty ha.ty hat.eq
  exact ⟨h, valid_glueEl hW hφ hG.v he.ty ht.v ha.v hat.v h⟩

theorem VEq.glueEl' {A T e t t' a a' : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : VTy S Ψ Φ Γ (.glue A φ T e) (.univ l)) (he : VTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (hg : VTy S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e)) (hg' : VTy S Ψ Φ Γ (.glueEl φ e t' a') (.glue A φ T e))
    (ht : VEq S Ψ (cof Φ φ) Γ t t' T) (ha : VEq S Ψ Φ Γ a a' A) :
    VEq S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ e t' a') (.glue A φ T e) := by
  have h := EqTm0.glueEl hg.ty hg'.ty (ent_refl _) (ent_refl _) (EqTm0.refl he.ty) ht.eq ha.eq
  exact ⟨h, valid_glueEl_eq hW hφ (ent_refl _) (ent_refl _) (fun k c => hG.v.ty hW c) (EqTm0.refl he.ty) ht.v ha.v hg.v hg'.v
    hg.ty hg'.ty h⟩

theorem VEq.glueEta' {A T e g : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : VTy S Ψ Φ Γ (.glue A φ T e) (.univ l)) (he : VTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (hg : VTy S Ψ Φ Γ g (.glue A φ T e)) :
    VEq S Ψ Φ Γ g (.glueEl φ e g (.unglue φ e g)) (.glue A φ T e) := by
  have h := EqTm0.glueEta hg.ty
  exact ⟨h, valid_glueEta_ty hW hφ he.ty hg.v hg.ty (presup hW h).2⟩

theorem VTy.appFst' {e T A x : Tm} (he : VTy S Ψ Φ Γ e (Tm.equiv T A)) (hx : VTy S Ψ Φ Γ x T) :
    VTy S Ψ Φ Γ (.app (.fst e) x) A := by
  have := VTy.app' hW (VTy.fst' hW he) hx
  rwa [shift_inst] at this

theorem VEq.appFst' {e T A x x' : Tm} (he : VTy S Ψ Φ Γ e (Tm.equiv T A)) (hx : VEq S Ψ Φ Γ x x' T) :
    VEq S Ψ Φ Γ (.app (.fst e) x) (.app (.fst e) x') A := by
  have := VEq.app' hW (VEq.fst' hW (VEq.refl' he)) hx
  rwa [shift_inst] at this

/-! ### `hcomp` in Glue types -/

/-- The contractum of `hcompGlue`, typed and valid, and its agreement with the tube's end where the
face holds. -/
theorem VTy.hcomp'lue' {A T e u u0 : Tm} {φ ψ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hA : VTy S Ψ Φ Γ A (.univ l)) (hT : VTy S Ψ (cof Φ φ) Γ T (.univ l))
    (he : VTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A)) (hψ : ψ.Scoped Ψ)
    (hu : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u (Tm.glue A φ T e).dshift)
    (hu0 : VTy S Ψ Φ Γ u0 (.glue A φ T e)) (hside : VEq S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (.glue A φ T e)) :
    VTy S Ψ Φ Γ (Tm.hcompGlue A φ T e ψ u u0) (.glue A φ T e) ∧
    VEq S Ψ (cof Φ ψ) Γ (u.dinst .one) (Tm.hcompGlue A φ T e ψ u u0) (.glue A φ T e) := by
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hA.ty
  have hG := VTy.glue' hW hφ hA hT he
  have hXφ : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hXψ : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  -- under `φ` the Glue type is `T`
  have hGφ := VTy.restrict' hW hXφ (ent_and_left _ _) hG
  have eGT : VEq S Ψ (cof Φ φ) Γ (.glue A φ T e) T (.univ l) := VEq.glueFace' hW (ent_and_right _ _) hGφ
  have hXφψ : (cof (cof Φ φ) ψ).Scoped Ψ := ⟨hXφ, hψ⟩
  have eGTψ := VEq.restrict' hW hXφψ (ent_and_left _ _) eGT
  have huT : VTy S (Ψ + 1) (cof (cof Φ φ) ψ).shift Γ.dshift u T.dshift :=
    VTy.conv' hW (VTy.restrict' hW (KubusCore.I.scoped_shift hXφψ)
      (ent_shift (ent_and_mono (ent_and_left _ _) (ent_refl _))) hu) (VEq.dwk' hW eGTψ)
  have hu0T : VTy S Ψ (cof Φ φ) Γ u0 T := VTy.conv' hW (VTy.restrict' hW hXφ (ent_and_left _ _) hu0) eGT
  have hsideT : VEq S Ψ (cof (cof Φ φ) ψ) Γ (u.dinst .zero) u0 T :=
    VEq.conv' hW (VEq.restrict' hW hXφψ (ent_and_mono (ent_and_left _ _) (ent_refl _)) hside) eGTψ
  have htc := VTy.hcomp' hW hT hψ huT hu0T hsideT
  obtain ⟨hfl, hfl0, hfl1, hflψ⟩ := VTy.hfill' hW hT hψ huT hu0T hsideT
  -- the tube of the base
  have hYs : (cof Φ (.or ψ φ)).Scoped Ψ := ⟨hs, ⟨hψ, hφ⟩⟩
  have hRs : (cof Φ (.or ψ φ)).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hYs
  have hRΦ : I.Entails (cof Φ (.or ψ φ)).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hA1 := VTy.restrict' hW hRs hRΦ (VTy.dwk' hW hA)
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hψ
  have hφ1 : φ.shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hφ
  have hX1 : (cof (cof Φ (.or ψ φ)).shift ψ.shift).Scoped (Ψ + 1) := ⟨hRs, hψ1⟩
  have hX2 : (cof (cof Φ (.or ψ φ)).shift φ.shift).Scoped (Ψ + 1) := ⟨hRs, hφ1⟩
  have hX3 : (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift).Scoped (Ψ + 1) := ⟨hX1, hφ1⟩
  have hX1ψ : I.Entails (cof (cof Φ (.or ψ φ)).shift ψ.shift) (cof Φ ψ).shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) hRΦ) (ent_and_right _ _)
  have hX2φ : I.Entails (cof (cof Φ (.or ψ φ)).shift φ.shift) (cof Φ φ).shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) hRΦ) (ent_and_right _ _)
  have hX3φ : I.Entails (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) (cof Φ φ).shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hRΦ)) (ent_and_right _ _)
  have hX3φψ : I.Entails (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) (cof (cof Φ φ) ψ).shift :=
    ent_and_intro hX3φ (ent_trans (ent_and_left _ _) (ent_and_right _ _))
  have heD : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift e.dshift (Tm.equiv T.dshift A.dshift) := by
    have := VTy.dwk' hW he
    rwa [equiv_dshift] at this
  have hGD : VTy S (Ψ + 1) Φ.shift Γ.dshift (.glue A.dshift φ.shift T.dshift e.dshift) (.univ l) :=
    VTy.dwk' hW hG
  have heD1 : VTy S (Ψ + 1) (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) Γ.dshift e.dshift
      (Tm.equiv T.dshift A.dshift) := VTy.restrict' hW hX3 hX3φ heD
  have hb1 : VTy S (Ψ + 1) (cof (cof Φ (.or ψ φ)).shift ψ.shift) Γ.dshift
      (.unglue φ.shift e.dshift u) A.dshift :=
    VTy.unglue' hW hφ1 (VTy.restrict' hW hX1 (ent_trans (ent_and_left _ _) hRΦ) hGD)
      (VTy.restrict' hW hX1 (ent_and_left _ _) hA1) heD1 (VTy.restrict' hW hX1 hX1ψ hu)
  have hb2 : VTy S (Ψ + 1) (cof (cof Φ (.or ψ φ)).shift φ.shift) Γ.dshift
      (.app (.fst e.dshift) (Tm.hfill T ψ u u0)) A.dshift :=
    VTy.appFst' hW (VTy.restrict' hW hX2 hX2φ heD) (VTy.restrict' hW hX2 hX2φ hfl)
  have hover : VEq S (Ψ + 1) (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) Γ.dshift
      (.unglue φ.shift e.dshift u) (.app (.fst e.dshift) (Tm.hfill T ψ u u0)) A.dshift := by
    have e1 := VEq.unglueFace' hW (ent_and_right _ _) (VTy.restrict' hW hX3 (ent_and_left _ _) hb1)
      (VTy.restrict' hW hX3 (ent_trans (ent_and_left _ _) hX1ψ) hu)
      (VTy.restrict' hW hX3 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA1) heD1
    have e2 := VEq.appFst' hW heD1 (VEq.symm' hW (VEq.restrict' hW hX3 hX3φψ hflψ))
    exact VEq.trans' hW e1 e2
  have htube : VTy S (Ψ + 1) (cof Φ (.or ψ φ)).shift Γ.dshift (KubusCore.Meta.glueTube φ T e ψ u u0) A.dshift :=
    VTy.split' hW hψ1 hφ1 (ent_shift (ent_and_right Φ (.or ψ φ))) hA1.ty hb1 hb2 hover
  have hu0g := VTy.unglue' hW hφ hG hA he hu0
  -- the side condition of the base
  have htube0 := VTy.dsubst' hW (Φ := cof Φ (.or ψ φ)) .zero trivial htube
  rw [dshift_dinst, glueTube_d] at htube0
  have hud : VTy S Ψ (cof Φ ψ) Γ (u.dinst .zero) (.glue A φ T e) := by
    have := VTy.dsubst' hW (Φ := cof Φ ψ) .zero trivial hu
    rwa [dshift_dinst] at this
  have hside' : VEq S Ψ (cof Φ (.or ψ φ)) Γ ((KubusCore.Meta.glueTube φ T e ψ u u0).dinst .zero) (.unglue φ e u0) A := by
    rw [glueTube_d]
    refine VEq.local' hW (φ := ψ) (ψ := φ) hψ hφ (ent_and_right _ _) htube0
      (VTy.restrict' hW hYs (ent_and_left _ _) hu0g) ?_ ?_
    · have hZ : (cof (cof Φ (.or ψ φ)) ψ).Scoped Ψ := ⟨hYs, hψ⟩
      have hZψ : I.Entails (cof (cof Φ (.or ψ φ)) ψ) (cof Φ ψ) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have hZΦ : I.Entails (cof (cof Φ (.or ψ φ)) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have e1 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hZ (ent_and_left _ _) htube0)
      have hZφ : (cof (cof (cof Φ (.or ψ φ)) ψ) φ).Scoped Ψ := ⟨hZ, hφ⟩
      have heZ := VTy.restrict' hW hZφ (ent_and_mono hZΦ (ent_refl _)) he
      have hl := VTy.unglue' hW hφ (VTy.restrict' hW hZ hZΦ hG) (VTy.restrict' hW hZ hZΦ hA) heZ
        (VTy.restrict' hW hZ hZψ hud)
      have hr := VTy.restrict' hW hZ hZΦ hu0g
      have e2 := VEq.unglue' hW hφ hl hr heZ (VEq.restrict' hW hZ hZψ hside)
      exact VEq.trans' hW e1 e2
    · have hZ : (cof (cof Φ (.or ψ φ)) φ).Scoped Ψ := ⟨hYs, hφ⟩
      have hZφ : I.Entails (cof (cof Φ (.or ψ φ)) φ) (cof Φ φ) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have hZΦ : I.Entails (cof (cof Φ (.or ψ φ)) φ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have heZ := VTy.restrict' hW hZ hZφ he
      have hWs : (cof (cof (cof Φ (.or ψ φ)) φ) ψ).Scoped Ψ := ⟨hZ, hψ⟩
      have hWΦ : I.Entails (cof (cof (cof Φ (.or ψ φ)) φ) ψ) Φ := ent_trans (ent_and_left _ _) hZΦ
      have hWφ : I.Entails (cof (cof (cof Φ (.or ψ φ)) φ) ψ) (cof Φ φ) := ent_trans (ent_and_left _ _) hZφ
      have hWψ : I.Entails (cof (cof (cof Φ (.or ψ φ)) φ) ψ) (cof Φ ψ) :=
        ent_and_intro hWΦ (ent_and_right _ _)
      have hWφψ : I.Entails (cof (cof (cof Φ (.or ψ φ)) φ) ψ) (cof (cof Φ φ) ψ) :=
        ent_and_intro hWφ (ent_and_right _ _)
      have heW := VTy.restrict' hW hWs hWφ he
      have hudW := VTy.restrict' hW hWs hWψ hud
      have hlW := VTy.unglue' hW hφ (VTy.restrict' hW hWs hWΦ hG) (VTy.restrict' hW hWs hWΦ hA)
        (VTy.restrict' hW (⟨hWs, hφ⟩ : (cof (cof (cof (cof Φ (.or ψ φ)) φ) ψ) φ).Scoped Ψ)
          (ent_and_mono hWΦ (ent_refl _)) he) hudW
      have o1 := VEq.unglueFace' hW (ent_trans (ent_and_left _ _) (ent_and_right _ _)) hlW hudW
        (VTy.restrict' hW hWs hWΦ hA) heW
      have o2 := VEq.appFst' hW heW (VEq.trans' hW (VEq.restrict' hW hWs hWφψ hsideT)
        (VEq.symm' hW (VEq.restrict' hW hWs hWφ hfl0)))
      have e1 := VEq.splitR' hW hψ hφ (ent_and_right _ _) (VTy.restrict' hW hZ (ent_and_left _ _) htube0)
        (VTy.appFst' hW (VTy.restrict' hW (⟨hZ, hφ⟩ : (cof (cof (cof Φ (.or ψ φ)) φ) φ).Scoped Ψ)
          (ent_trans (ent_and_left _ _) hZφ) he) (VEq.lty' hW (VEq.restrict' hW ⟨hZ, hφ⟩
            (ent_trans (ent_and_left _ _) hZφ) hfl0)))
        (VEq.restrict' hW ⟨hWs, hφ⟩ (ent_and_left _ _) (VEq.trans' hW o1 o2))
      have e2 := VEq.appFst' hW heZ (VEq.restrict' hW hZ hZφ hfl0)
      have e3 := VEq.unglueFace' hW (ent_and_right _ _) (VTy.restrict' hW hZ hZΦ hu0g)
        (VTy.restrict' hW hZ hZΦ hu0) (VTy.restrict' hW hZ hZΦ hA) heZ
      exact VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.symm' hW e3))
  have hbase := VTy.hcomp' hW hA (show (I.or ψ φ).Scoped Ψ from ⟨hψ, hφ⟩) htube hu0g hside'
  -- the side condition of the Glue element
  have hYφ : I.Entails (cof Φ φ) (cof Φ (.or ψ φ)) :=
    ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) (ent_or_right _ _))
  have ht1 := VTy.dsubst' hW (Φ := cof Φ (.or ψ φ)) .one trivial htube
  rw [dshift_dinst, glueTube_d] at ht1
  have hgside : VEq S Ψ (cof Φ φ) Γ (.app (.fst e) (.hcomp T ψ u u0))
      (.hcomp A (.or ψ φ) (KubusCore.Meta.glueTube φ T e ψ u u0) (.unglue φ e u0)) A := by
    have b1 := VEq.hcompFace' hW (ent_trans (ent_and_right _ _) (ent_or_right _ _))
      (VTy.restrict' hW hXφ (ent_and_left _ _) hbase)
    rw [glueTube_d] at b1
    have hVs : (cof (cof (cof Φ φ) ψ) φ).Scoped Ψ := ⟨hXφψ, hφ⟩
    have hVφ : I.Entails (cof (cof (cof Φ φ) ψ) φ) (cof Φ φ) := ent_trans (ent_and_left _ _) (ent_and_left _ _)
    have hVΦ : I.Entails (cof (cof (cof Φ φ) ψ) φ) Φ := ent_trans hVφ (ent_and_left _ _)
    have hVψ : I.Entails (cof (cof (cof Φ φ) ψ) φ) (cof Φ ψ) :=
      ent_and_intro hVΦ (ent_trans (ent_and_left _ _) (ent_and_right _ _))
    have heV := VTy.restrict' hW hVs hVφ he
    have hu1 : VTy S Ψ (cof Φ ψ) Γ (u.dinst .one) (.glue A φ T e) := by
      have := VTy.dsubst' hW (Φ := cof Φ ψ) .one trivial hu
      rwa [dshift_dinst] at this
    have hu1V := VTy.restrict' hW hVs hVψ hu1
    have hlV := VTy.unglue' hW hφ (VTy.restrict' hW hVs hVΦ hG) (VTy.restrict' hW hVs hVΦ hA)
      (VTy.restrict' hW (⟨hVs, hφ⟩ : (cof (cof (cof (cof Φ φ) ψ) φ) φ).Scoped Ψ)
        (ent_and_mono hVΦ (ent_refl _)) he) hu1V
    have o1 := VEq.unglueFace' hW (ent_and_right _ _) hlV hu1V (VTy.restrict' hW hVs hVΦ hA) heV
    have hfψ1 := VEq.dsubst' hW (Φ := cof (cof Φ φ) ψ) .one trivial hflψ
    rw [dshift_dinst] at hfψ1
    have o2 := VEq.appFst' hW heV (VEq.symm' hW (VEq.restrict' hW hVs (ent_and_left _ _) hfψ1))
    have b2 := VEq.splitR' hW hψ hφ (ent_and_right _ _) (VTy.restrict' hW hXφ hYφ ht1)
      (VTy.appFst' hW (VTy.restrict' hW (⟨hXφ, hφ⟩ : (cof (cof Φ φ) φ).Scoped Ψ) (ent_and_left _ _) he)
        (VEq.lty' hW (VEq.restrict' hW ⟨hXφ, hφ⟩ (ent_and_left _ _) hfl1)))
      (VEq.trans' hW o1 o2)
    have b3 := VEq.appFst' hW he hfl1
    exact VEq.symm' hW (VEq.trans' hW b1 (VEq.trans' hW b2 b3))
  have hy := VTy.glueEl' hW hφ hG he htc hbase hgside
  refine ⟨hy, ?_⟩
  -- where `ψ` holds: Glue η for the tube's end, and the faces of the components
  have hu1 : VTy S Ψ (cof Φ ψ) Γ (u.dinst .one) (.glue A φ T e) := by
    have := VTy.dsubst' hW (Φ := cof Φ ψ) .one trivial hu
    rwa [dshift_dinst] at this
  have hFs : (cof (cof Φ ψ) φ).Scoped Ψ := ⟨hXψ, hφ⟩
  have hFφ : I.Entails (cof (cof Φ ψ) φ) (cof Φ φ) :=
    ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
  have hGZ := VTy.restrict' hW hXψ (ent_and_left _ _) hG
  have heZ := VTy.restrict' hW hFs hFφ he
  have hη := VEq.glueEta' hW hφ hGZ heZ hu1
  have t1 := VEq.hcompFace' hW (ent_trans (ent_and_left _ _) (ent_and_right _ _)) (VTy.restrict' hW hFs hFφ htc)
  have b1 := VEq.hcompFace' hW (ent_trans (ent_and_right _ _) (ent_or_left _ _))
    (VTy.restrict' hW hXψ (ent_and_left _ _) hbase)
  rw [glueTube_d] at b1
  have b2 := VEq.splitL' hW (ent_and_right _ _) (VEq.rty' hW b1)
  have hcong := VEq.glueEl' hW hφ hGZ heZ (VEq.rty' hW hη) (VTy.restrict' hW hXψ (ent_and_left _ _) hy)
    (VEq.symm' hW t1) (VEq.symm' hW (VEq.trans' hW b1 b2))
  exact VEq.trans' hW hη hcong

/-- A redex whose every instance reduces to something related to the right instance of the contractum. -/
theorem valid_red_rule {t y T : Tm} (ht : Valid2 S Ψ Φ Γ t t T) (hy : Valid2 S Ψ Φ Γ y y T)
    (hred : ∀ k (c : CSub2 S Ψ Φ Γ k), ∃ z, Red S (c.L t) z ∧ EqTm S k .one [] (c.L t) z (c.L T) ∧
      RE2 S k (c.L T) z (c.R y)) :
    Valid2 S Ψ Φ Γ t y T := by
  intro k c
  refine ⟨(ht k c).1, RE2.expandH hW (ht.tyLL hW c) (RE2.typed (ht k c).2).1 (RE2.typed (hy k c).2).2.1
    fun k' σ => ?_⟩
  have hr := hred k' (c.restr hW σ)
  rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at hr

theorem valid_hcompGlue_rule {A T e u u0 T0 : Tm} {φ ψ : I}
    (h : HasTy0 S Ψ Φ Γ (.hcomp (.glue A φ T e) ψ u u0) T0)
    (hv : Valid2 S Ψ Φ Γ (.hcomp (.glue A φ T e) ψ u u0) (.hcomp (.glue A φ T e) ψ u u0) T0)
    (hinv : HcompInv S Ψ Φ Γ (.glue A φ T e) ψ u u0 T0) (hg : GlueTyInv S Ψ Φ Γ A φ T e) :
    Valid2 S Ψ Φ Γ (.hcomp (.glue A φ T e) ψ u u0) (Tm.hcompGlue A φ T e ψ u u0) T0 := by
  obtain ⟨_, hψ, -, huV, hu0V, hsV, htr, -, hu, hu0, hside⟩ := hinv
  obtain ⟨l, hφ, hAV, hTV, heV, hA, hT, he⟩ := hg
  have hs := scoped_of_ty hA
  have hup : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u (Tm.glue A φ T e).dshift := ⟨hu, huV⟩
  have hu0p : VTy S Ψ Φ Γ u0 (.glue A φ T e) := ⟨hu0, hu0V⟩
  have hsidep : VEq S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (.glue A φ T e) := ⟨hside, hsV⟩
  obtain ⟨hy, hface⟩ := VTy.hcomp'lue' hW hφ ⟨hA, hAV⟩ ⟨hT, hTV⟩ ⟨he, heV⟩ hψ hup hu0p hsidep
  have hT0 : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T0) (c.R T0) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hy.v htr hT0
  have hb := valid_conv_tr hface.v (htr.restrict (ent_and_left _ _)) fun k c => hT0 k (c.restrictTo (ent_and_left _ _))
  have hE := EqTm0.hcompGlue h hA he
  have hyT0 := (presup hW hE).2
  have hXφ : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hE1 := EqTm0.glueElFace (ent_and_right _ _) (HasTy0.restrict hXφ (ent_and_left _ _) hyT0)
  have hEφ := EqTm0.trans (EqTm0.restrict hXφ (ent_and_left _ _) hE) hE1
  have hzT0 := (presup hW hE1).2
  refine valid_red_rule hW hv hyT fun k c => ?_
  by_cases hf : I.Entails .one (ψ.subst c.σ.τ)
  · refine ⟨c.L (u.dinst .one), ?_, ?_, (hb k (c.cof hf)).2⟩
    · rw [CSub2.L_dinst hW]; exact .step (step_hcomp_face hf) (.refl _)
    · rw [CSub2.L_dinst hW]; exact EqTm.hcompFace hf (c.ty hW h)
  have hn' : I.entails .one (ψ.subst c.σ.τ) = false := by simpa [I.Entails] using hf
  by_cases hgf : I.Entails .one (φ.subst c.σ.τ)
  · have hg' : I.entails .one (φ.subst c.σ.τ) = true := hgf
    refine ⟨c.L (.hcomp T ψ u u0), ?_, ((c.cof hgf).diagL hW).eq hW hEφ, ?_⟩
    · refine .step ?_ (.refl _)
      simp [CSub2.L, Tm.subst, step, hn', hg']
    · have hs' := stable_glueEl hW (c.ty hW hyT0) hgf
      exact RE2.reduceL hW (hv.tyLL hW c) (hyT k c).2 hs' ((c.cof hgf).ty hW hzT0)
  · have hg' : I.entails .one (φ.subst c.σ.τ) = false := by simpa [I.Entails] using hgf
    refine ⟨c.L (Tm.hcompGlue A φ T e ψ u u0), ?_, (c.diagL hW).eq hW hE, (hyT k c).2⟩
    refine .step ?_ (.refl _)
    rw [show c.L (Tm.hcompGlue A φ T e ψ u u0) = Tm.hcompGlue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)
      (ψ.subst c.σ.τ) (u.subst (dupS c.γ) (I.up c.σ.τ)) (c.L u0) from hcompGlue_subst _ _ A φ T e ψ u u0]
    simp [CSub2.L, Tm.subst, step, hn', hg']

end

end Model.Whnf
