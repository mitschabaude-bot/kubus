import KubusCore.Meta.KanSigma

/-!
# Metatheory: typing the contractum of `hcomp` in Glue types
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem app_fst_equiv {Ψ Φ Γ e T A x} (he : HasTy0 S Ψ Φ Γ e (equiv T A)) (hx : HasTy0 S Ψ Φ Γ x T) :
    HasTy0 S Ψ Φ Γ (app (fst e) x) A := by
  have hf := HasTy0.fst he
  have := HasTy0.app hf hx
  rwa [shift_inst] at this

theorem app_fst_congr {Ψ Φ Γ e T A x x'} (he : HasTy0 S Ψ Φ Γ e (equiv T A)) (hx : EqTm0 S Ψ Φ Γ x x' T) :
    EqTm0 S Ψ Φ Γ (app (fst e) x) (app (fst e) x') A := by
  have := EqTm0.app (EqTm0.fst (EqTm0.refl he)) hx
  rwa [shift_inst] at this

theorem equiv_dshift (T A : Tm) : (equiv T A).dshift = equiv T.dshift A.dshift := by
  rw [dshift_eq, dshift_eq, dshift_eq, equiv_subst]

def glueTube (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm) : Tm :=
  split ψ.shift (unglue φ.shift e.dshift u) φ.shift (app (fst e.dshift) (hfill T ψ u u0))

theorem hcompGlue_eq (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm) :
    hcompGlue A φ T e ψ u u0 = glueEl φ e (hcomp T ψ u u0)
      (hcomp A (.or ψ φ) (glueTube φ T e ψ u u0) (unglue φ e u0)) := rfl

theorem glueTube_d (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm) (r : I) :
    (glueTube φ T e ψ u u0).dinst r =
      split ψ (unglue φ e (u.dinst r)) φ (app (fst e) ((hfill T ψ u u0).dinst r)) := by
  simp only [glueTube, Tm.dinst, Tm.dsubst, Tm.subst]
  have h1 : ∀ t : Tm, t.dshift.subst Tm.var (I.inst0 r) = t := fun t => dshift_dinst t r
  have h2 : ∀ x : I, x.shift.subst (I.inst0 r) = x := fun x => by
    simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var x
  rw [h1, h2, h2]

theorem hcompGlue_typed (hS : SigClosed S) {Ψ Φ Γ A φ T e ψ u u0 T0}
    (h : HasTy0 S Ψ Φ Γ (hcomp (glue A φ T e) ψ u u0) T0) :
    HasTy0 S Ψ Φ Γ (hcompGlue A φ T e ψ u u0) T0 := by
  obtain ⟨l, ⟨hG, hψ, hu, hu0, hside⟩, ch⟩ := gen_hcomp h rfl
  refine ch.transport ?_
  rw [hcompGlue_eq]
  obtain ⟨l0, ⟨hA0, hφ, hT0, he⟩, chg⟩ := gen_glue hS hG rfl
  have hA := chg.transport hA0
  have hs := scoped_of_ty h
  have hXφ : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hXψ : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  have hT := (chg.restrict hXφ (ent_and_left _ _)).transport hT0
  -- under `φ` the Glue type is `T`
  have hGφ := HasTy0.restrict hXφ (ent_and_left _ _) hG
  have eGT : EqTm0 S Ψ (cof Φ φ) Γ (glue A φ T e) T (univ l) := EqTm0.glueFace (ent_and_right _ _) hGφ
  have hXφψ : (cof (cof Φ φ) ψ).Scoped Ψ := ⟨hXφ, hψ⟩
  have eGTψ := EqTm0.restrict hXφψ (ent_and_left _ _) eGT
  have huT : HasTy0 S (Ψ + 1) (cof (cof Φ φ) ψ).shift Γ.dshift u T.dshift :=
    HasTy0.conv (HasTy0.restrict (scoped_shift hXφψ)
      (ent_shift (ent_and_mono (ent_and_left _ _) (ent_refl _))) hu) (EqTm0.dwk hS eGTψ)
  have hu0T : HasTy0 S Ψ (cof Φ φ) Γ u0 T := HasTy0.conv (HasTy0.restrict hXφ (ent_and_left _ _) hu0) eGT
  have hsideT : EqTm0 S Ψ (cof (cof Φ φ) ψ) Γ (u.dinst .zero) u0 T :=
    EqTm0.conv (EqTm0.restrict hXφψ (ent_and_mono (ent_and_left _ _) (ent_refl _)) hside) eGTψ
  have htc := HasTy0.hcomp hT hψ huT hu0T hsideT
  obtain ⟨hfl, hfl0, hfl1, hflψ⟩ := hfill_typed hS hT hψ huT hu0T hsideT
  -- the tube of the base
  have hYs : (cof Φ (.or ψ φ)).Scoped Ψ := ⟨hs, ⟨hψ, hφ⟩⟩
  have hRs : (cof Φ (.or ψ φ)).shift.Scoped (Ψ + 1) := scoped_shift hYs
  have hRΦ : I.Entails (cof Φ (.or ψ φ)).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hA1 := HasTy0.restrict hRs hRΦ (HasTy0.dwk hS hA)
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := scoped_shift hψ
  have hφ1 : φ.shift.Scoped (Ψ + 1) := scoped_shift hφ
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
  have heD : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift e.dshift (equiv T.dshift A.dshift) := by
    have := HasTy0.dwk hS he
    rwa [equiv_dshift] at this
  have hGD : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (glue A.dshift φ.shift T.dshift e.dshift) (univ l) :=
    HasTy0.dwk hS hG
  have hb1 : HasTy0 S (Ψ + 1) (cof (cof Φ (.or ψ φ)).shift ψ.shift) Γ.dshift
      (unglue φ.shift e.dshift u) A.dshift :=
    HasTy0.unglue (HasTy0.restrict hX1 (ent_trans (ent_and_left _ _) hRΦ) hGD)
      (HasTy0.restrict hX1 (ent_and_left _ _) hA1)
      (HasTy0.restrict ⟨hX1, hφ1⟩ (ent_and_intro (ent_trans (ent_and_left _ _)
        (ent_trans (ent_and_left _ _) hRΦ)) (ent_and_right _ _)) heD)
      (HasTy0.restrict hX1 hX1ψ hu)
  have hb2 : HasTy0 S (Ψ + 1) (cof (cof Φ (.or ψ φ)).shift φ.shift) Γ.dshift
      (app (fst e.dshift) (hfill T ψ u u0)) A.dshift :=
    app_fst_equiv (HasTy0.restrict hX2 hX2φ heD) (HasTy0.restrict hX2 hX2φ hfl)
  have hover : EqTm0 S (Ψ + 1) (cof (cof (cof Φ (.or ψ φ)).shift ψ.shift) φ.shift) Γ.dshift
      (unglue φ.shift e.dshift u) (app (fst e.dshift) (hfill T ψ u u0)) A.dshift := by
    have he3 := HasTy0.restrict hX3 hX3φ heD
    have e1 := EqTm0.unglueFace (ent_and_right _ _)
      (HasTy0.restrict hX3 (ent_trans (ent_and_left _ _) hX1ψ) hu)
      (HasTy0.restrict hX3 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA1) he3
    have e2 := app_fst_congr he3 (EqTm0.symm (EqTm0.restrict hX3 hX3φψ hflψ))
    exact EqTm0.trans e1 e2
  have htube : HasTy0 S (Ψ + 1) (cof Φ (.or ψ φ)).shift Γ.dshift (glueTube φ T e ψ u u0) A.dshift :=
    HasTy0.split hψ1 hφ1 (ent_shift (ent_and_right Φ (.or ψ φ))) hA1 hb1 hb2 hover
  have hu0g := HasTy0.unglue hG hA he hu0
  -- the side condition of the base
  have htube0 := HasTy0.dsubst hS (Φ := cof Φ (.or ψ φ)) htube (r := .zero) trivial
  rw [dshift_dinst, glueTube_d] at htube0
  have hud : HasTy0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) (glue A φ T e) := by
    have := HasTy0.dsubst hS (Φ := cof Φ ψ) hu (r := .zero) trivial
    rwa [dshift_dinst] at this
  have hside' : EqTm0 S Ψ (cof Φ (.or ψ φ)) Γ ((glueTube φ T e ψ u u0).dinst .zero) (unglue φ e u0) A := by
    rw [glueTube_d]
    refine EqTm0.local (φ := ψ) (ψ := φ) hψ hφ (ent_and_right _ _) htube0
      (HasTy0.restrict hYs (ent_and_left _ _) hu0g) ?_ ?_
    · have hZ : (cof (cof Φ (.or ψ φ)) ψ).Scoped Ψ := ⟨hYs, hψ⟩
      have hZψ : I.Entails (cof (cof Φ (.or ψ φ)) ψ) (cof Φ ψ) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have hZΦ : I.Entails (cof (cof Φ (.or ψ φ)) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have e1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hZ (ent_and_left _ _) htube0)
      have hZφ : (cof (cof (cof Φ (.or ψ φ)) ψ) φ).Scoped Ψ := ⟨hZ, hφ⟩
      have heZ := HasTy0.restrict hZφ (ent_and_mono hZΦ (ent_refl _)) he
      have hl := HasTy0.unglue (HasTy0.restrict hZ hZΦ hG) (HasTy0.restrict hZ hZΦ hA) heZ
        (HasTy0.restrict hZ hZψ hud)
      have hr := HasTy0.restrict hZ hZΦ hu0g
      have e2 := EqTm0.unglue hl hr (ent_refl _) (ent_refl _) (EqTm0.refl heZ)
        (EqTm0.restrict hZ hZψ hside)
      exact EqTm0.trans e1 e2
    · have hZ : (cof (cof Φ (.or ψ φ)) φ).Scoped Ψ := ⟨hYs, hφ⟩
      have hZφ : I.Entails (cof (cof Φ (.or ψ φ)) φ) (cof Φ φ) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have hZΦ : I.Entails (cof (cof Φ (.or ψ φ)) φ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have e1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hZ (ent_and_left _ _) htube0)
      have heZ := HasTy0.restrict hZ hZφ he
      have e2 := app_fst_congr heZ (EqTm0.restrict hZ hZφ hfl0)
      have e3 := EqTm0.unglueFace (ent_and_right _ _) (HasTy0.restrict hZ hZΦ hu0)
        (HasTy0.restrict hZ hZΦ hA) heZ
      exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.symm e3))
  have hbase := HasTy0.hcomp hA (show (I.or ψ φ).Scoped Ψ from ⟨hψ, hφ⟩) htube hu0g hside'
  -- the side condition of the Glue element
  have hgside : EqTm0 S Ψ (cof Φ φ) Γ (app (fst e) (hcomp T ψ u u0))
      (hcomp A (.or ψ φ) (glueTube φ T e ψ u u0) (unglue φ e u0)) A := by
    have hYφ : I.Entails (cof Φ φ) (cof Φ (.or ψ φ)) :=
      ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) (ent_or_right _ _))
    have b1 := EqTm0.hcompFace (ent_trans (ent_and_right _ _) (ent_or_right _ _))
      (HasTy0.restrict hXφ (ent_and_left _ _) hbase)
    rw [glueTube_d] at b1
    have ht1 := HasTy0.dsubst hS (Φ := cof Φ (.or ψ φ)) htube (r := .one) trivial
    rw [dshift_dinst, glueTube_d] at ht1
    have b2 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hXφ hYφ ht1)
    have b3 := app_fst_congr he hfl1
    exact EqTm0.symm (EqTm0.trans b1 (EqTm0.trans b2 b3))
  exact HasTy0.glueEl hG he htc hbase hgside

end KubusCore.Meta
