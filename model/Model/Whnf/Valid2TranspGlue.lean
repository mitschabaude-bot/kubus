import Model.Whnf.Valid2LineEquiv

/-!
# Validity of the `transp` computation rule in Glue types

The typing derivation of the contractum (`KubusCore/Meta/KanTranspGlue.lean`,
`KubusCore/Meta/KanTranspGlueAux.lean`), with validity.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-! ### Heterogeneous composition: face and congruence -/

/-- On its cofibration, `comp` is the end of its tube. -/
theorem VEq.compFace' {C u u0 T : Tm} {ψ : I} (hc : VTy S Ψ Φ Γ (Tm.comp C ψ u u0) T) (hψ : I.Entails Φ ψ) :
    VEq S Ψ Φ Γ (Tm.comp C ψ u u0) (u.dinst .one) T := by
  rw [comp_eq] at hc ⊢
  have e1a := VEq.hcompFace' hW hψ hc
  have e1b := VEq.transpFace' hW (ent_one _) (VEq.rty' hW e1a)
  exact VEq.trans' hW e1a e1b

/-- Congruence of `comp` (the second composition is only assumed typed). -/
theorem VEq.compCong' (hKH : KHAll S) (hKT : KTAll S) {C C' u u' u0 u0' : Tm} {ψ ψ' : I} {l : ℕ}
    (hC : VTy S (Ψ + 1) Φ.shift Γ.dshift C (.univ l)) (hψ : ψ.Scoped Ψ)
    (hu : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C) (hu0 : VTy S Ψ Φ Γ u0 (C.dinst .zero))
    (hside : VEq S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (C.dinst .zero))
    (hc' : HasTy0 S Ψ Φ Γ (Tm.comp C' ψ' u' u0') (C.dinst .one))
    (hCC : VEq S (Ψ + 1) Φ.shift Γ.dshift C C' (.univ l)) (h1 : I.Entails ψ ψ') (h2 : I.Entails ψ' ψ)
    (huu : VEq S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u u' C) (hu0u : VEq S Ψ Φ Γ u0 u0' (C.dinst .zero)) :
    VEq S Ψ Φ Γ (Tm.comp C ψ u u0) (Tm.comp C' ψ' u' u0') (C.dinst .one) := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hC.ty)
  have hs := scoped_of_wf hw0
  obtain ⟨hC1, htube, hconst, hb, hside'⟩ := VTy.compParts' hW hKT hC hψ hu hu0 hside
  have hc := VTy.hcompG hW hKH hC1 hψ htube hb hside'
  rw [comp_eq] at hc' ⊢
  obtain ⟨_, ⟨_, _, htube', hb', _⟩, _⟩ := gen_hcomp hc' rfl
  have hXs : (cof Φ ψ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, hψ⟩
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left Φ ψ)
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  -- the base
  have htb' := transp_retype hb'
  have eC1 := VEq.dsubst' hW .one trivial hCC
  have eb := VEq.transp' hW (fun k c => hKT k _ _ (hCC.v.ty hW (c.up hW))) (φ := .zero) trivial (ent_refl _)
    (ent_refl _) hb.ty (HasTy0.conv htb' (VEq.symm' hW eC1).eq) hCC
    (valid_absurd (A := .univ l) (ent_shift (ent_and_right Φ .zero))) hu0u
  -- the tube
  have htr' := transp_retype (HasTy0.restrict hXs (ent_shift (ent_and_mono (ent_refl _) h1)) htube')
  have hLL := VEq.bind2' hW (X := (cof Φ ψ).shift.shift) (r := .or (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hs
    (ent_shift hXΦ) ((hw0.dwk2 hS).restrict (KubusCore.I.scoped_shift hXs) (ent_shift hXΦ)) hCC
  rw [univ_dsubst] at hLL
  have eL1 := VEq.dsubst' hW .one trivial hLL
  have hwX : Wf0 S (Ψ + 1) (cof Φ ψ).shift (Ctx.dren 1 Γ) := wf_of_ty hu.ty
  have eL0 : VEq S (Ψ + 1) (cof Φ ψ).shift Γ.dshift C
      ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .zero) (.univ l) := by
    rw [L_d0]
    have e := VTy.lineIeq hW hC (k := 1) (r := .var 0) (r' := .or (.var 0) .zero) hXΦ hv0
      ⟨hv0, trivial⟩ (I_eq_symm (I_eq_or_zero_r _)) hwX
    rwa [sk_var1] at e
  have hLLv := hLL.v
  have et := VEq.transp' hW (fun k c => hKT k _ _ (hLLv.ty hW (c.up hW))) (φ := .var 0) hv0 (ent_refl _)
    (ent_refl _) (transp_retype htube.ty) (HasTy0.conv htr' (VEq.symm' hW eL1).eq) hLL hconst.v
    (VEq.conv' hW huu eL0)
  have eC1' : VEq S (Ψ + 1) (cof Φ ψ).shift Γ.dshift
      ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .one) (C.dinst .one).dshift (.univ l) := by
    rw [L_d1]
    have e := VTy.lineIeq hW hC (k := 1) (r := .or (.var 0) .one) (r' := .one) hXΦ
      ⟨hv0, trivial⟩ trivial (I_eq_or_one_r _) hwX
    rwa [sk_one1] at e
  have etu := VEq.conv' hW et eC1'
  have et0 := VEq.dsubst' hW (Φ := cof Φ ψ) .zero trivial etu
  rw [dshift_dinst] at et0
  have hu0' := valid_trans hW (valid_trans hW (valid_symm hW et0.v) hside'.v)
    (valid_restrict hW (ent_and_left _ _) eb.v)
  exact VEq.hcomp' hW (fun k c => hKH k _ _ (eC1.v.ty hW c)) hψ h1 h2 hc.ty hc' eC1 etu eb hside'.v hu0'

/-! ### The filler of heterogeneous composition -/

theorem VTy.fill' (hKH : KHAll S) (hKT : KTAll S) {C ψ u u0} {l : ℕ}
    (hC : VTy S (Ψ + 1) Φ.shift Γ.dshift C (.univ l)) (hψ : ψ.Scoped Ψ)
    (hu : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C) (hu0 : VTy S Ψ Φ Γ u0 (C.dinst .zero))
    (hside : VEq S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (C.dinst .zero)) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.fill C ψ u u0) C ∧
    VEq S Ψ Φ Γ ((Tm.fill C ψ u u0).dinst .zero) u0 (C.dinst .zero) ∧
    VEq S Ψ Φ Γ ((Tm.fill C ψ u u0).dinst .one) (Tm.comp C ψ u u0) (C.dinst .one) ∧
    VEq S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (Tm.fill C ψ u u0) u C := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hC.ty)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hXψs : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  have hL := VTy.bind2' hW (X := Φ.shift.shift) (r := .and (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hs (ent_refl _)
    (hw0.dwk2 hS) hC
  rw [univ_dsubst] at hL
  let χ : I := .or ψ.shift (.neg (.var 0))
  have hχs : χ.Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hψ, hv0⟩
  have hΞs : (cof Φ.shift χ).Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hs, hχs⟩
  have hRs : (cof Φ.shift χ).shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift hΞs
  have hRΦ : I.Entails (cof Φ.shift χ).shift Φ.shift.shift := ent_shift (ent_and_left _ _)
  have hφ2 : ψ.shift.shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hψ)
  have hLR := VTy.restrict' hW hRs hRΦ hL
  have hΦ2 : I.Entails Φ.shift.shift (Φ.subst (fun n => .var (n + 2))) := by rw [I_add2]; exact ent_refl _
  -- the tube
  have hR1s : (cof (cof Φ.shift χ).shift ψ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hRs, hφ2⟩
  have hR1Φ : I.Entails (cof (cof Φ.shift χ).shift ψ.shift.shift) (cof Φ ψ).shift.shift :=
    ent_and_mono hRΦ (ent_refl _)
  have hT1 := VTy.bind2' hW (Φ := cof Φ ψ) (X := cof (cof Φ.shift χ).shift ψ.shift.shift)
    (r := .and (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hXψs hR1Φ
    ((hw0.dwk2 hS).restrict hR1s (ent_trans (ent_and_left _ _) hRΦ)) hu
  have hR2s : (cof (cof Φ.shift χ).shift (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hRs, hv1⟩
  have hR2Φ : I.Entails (cof (cof Φ.shift χ).shift (.neg (.var 1))) Φ.shift.shift :=
    ent_trans (ent_and_left _ _) hRΦ
  have hw2 : Wf0 S (Ψ + 2) (cof (cof Φ.shift χ).shift (.neg (.var 1))) (Ctx.dren 2 Γ) := by
    rw [Ctx.dren_two]; exact (hw0.dwk2 hS).restrict hR2s hR2Φ
  -- under `i = 0` the line is `C(0)`
  have eC0 : VEq S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift (.neg (.var 1))) Γ.dshift.dshift
      (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (C.dinst .zero).dshift.dshift (.univ l) := by
    have e1 := VEq.faceU' hW (i := 1) (d := false) hv1 (ent_and_right _ _)
      (VTy.restrict' hW hR2s (ent_and_left _ _) hLR)
    rw [tf_L1] at e1
    have e2 := VTy.lineIeq hW hC (k := 2) (r := .and .zero (.var 0)) (r' := .zero)
      (ent_trans hR2Φ hΦ2) ⟨trivial, hv0'⟩ trivial (I_eq_and_zero _) hw2
    rw [Ctx.dren_two, sk_zero2] at e2
    exact VEq.trans' hW e1 e2
  have hT2 : VTy S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift (.neg (.var 1))) Γ.dshift.dshift
      u0.dshift.dshift (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) :=
    VTy.conv' hW (VTy.restrict' hW hR2s hR2Φ (VTy.dwk' hW (VTy.dwk' hW hu0))) (VEq.symm' hW eC0)
  have hR3s : (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
    ⟨hR1s, hv1⟩
  have hover : VEq S (Ψ + 1 + 1) (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1)))
      Γ.dshift.dshift (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) u0.dshift.dshift
      (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) := by
    have hR3e : I.Entails (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1)))
        (cof (cof Φ.shift χ).shift (.neg (.var 1))) :=
      ent_and_mono (ent_and_left _ _) (ent_refl _)
    have hw3 : Wf0 S (Ψ + 2) (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1))) (Ctx.dren 2 Γ) :=
      hw2.restrict hR3s hR3e
    have eC0' := VEq.restrict' hW hR3s hR3e eC0
    have e1 := VEq.face' hW (i := 1) (d := false) hv1 (ent_and_right _ _)
      (VTy.restrict' hW hR3s (ent_trans hR3e (ent_and_left _ _)) hLR).ty
      (VTy.restrict' hW hR3s (ent_and_left _ _) hT1)
    rw [fillTube_dset1 ψ u u0] at e1
    have hR3ψ : I.Entails (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1)))
        ((cof Φ ψ).subst (fun n => .var (n + 2))) := by
      rw [I_add2]; exact ent_trans (ent_and_left _ _) hR1Φ
    have e2 := VTy.lineIeq hW hu (k := 2) (r := .and .zero (.var 0)) (r' := .zero) hR3ψ ⟨trivial, hv0'⟩ trivial
      (I_eq_and_zero _) hw3
    rw [Ctx.dren_two, sk_zero2] at e2
    have eCC := VTy.lineIeq hW hC (k := 2) (r := .and .zero (.var 0)) (r' := .zero)
      (ent_trans (ent_trans hR3e hR2Φ) hΦ2) ⟨trivial, hv0'⟩ trivial (I_eq_and_zero _) hw3
    rw [Ctx.dren_two, sk_zero2] at eCC
    have e3 := VEq.restrict' hW hR3s (ent_trans (ent_and_left _ _) hR1Φ)
      (VEq.dwk' hW (VEq.dwk' hW hside))
    exact VEq.trans' hW e1 (VEq.conv' hW (VEq.trans' hW e2 (VEq.conv' hW e3 (VEq.symm' hW eCC)))
      (VEq.trans' hW eCC (VEq.symm' hW eC0')))
  have htube : VTy S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift (KubusCore.Meta.fillTube ψ u u0)
      (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) :=
    VTy.split' hW (φ := ψ.shift.shift) (ψ := .neg (.var 1)) hφ2 hv1 (ent_shift (ent_and_right Φ.shift χ)) hLR.ty hT1 hT2 hover
  -- the base
  have hwX1 : Wf0 S (Ψ + 1) Φ.shift (Ctx.dren 1 Γ) := wf_of_ty hC.ty
  have eL0 : VEq S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero)
      (C.dinst .zero).dshift (.univ l) := by
    rw [tf_L0]
    have e := VTy.lineIeq hW hC (k := 1) (r := .and (.var 0) .zero) (r' := .zero) (ent_refl _) ⟨hv0, trivial⟩
      trivial (I_eq_and_zero_r _) hwX1
    rwa [sk_zero1] at e
  have hbase : VTy S (Ψ + 1) Φ.shift Γ.dshift u0.dshift
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) :=
    VTy.conv' hW (VTy.dwk' hW hu0) (VEq.symm' hW eL0)
  -- the side condition
  have htube0 := VTy.dsubst' hW (Φ := cof Φ.shift χ) (Γ := Γ.dshift) .zero trivial htube
  rw [fillTube_d0] at htube0
  have hside' : VEq S (Ψ + 1) (cof Φ.shift χ) Γ.dshift
      (.split ψ.shift (u.subst Tm.var (sk (.and (.var 0) .zero) 1)) (.neg (.var 0)) u0.dshift)
      u0.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    have hX : (cof (cof Φ.shift χ) ψ.shift).Scoped (Ψ + 1) := ⟨hΞs, KubusCore.I.scoped_shift hψ⟩
    have hXe : I.Entails (cof (cof Φ.shift χ) ψ.shift) (cof Φ ψ).shift :=
      ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
    have hcore : VEq S (Ψ + 1) (cof (cof Φ.shift χ) ψ.shift) Γ.dshift
        (u.subst Tm.var (sk (.and (.var 0) .zero) 1)) u0.dshift
        ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
      have hXe1 : I.Entails (cof (cof Φ.shift χ) ψ.shift) ((cof Φ ψ).subst (fun n => .var (n + 1))) := by
        rw [I_add1]; exact hXe
      have e2 := VTy.lineIeq hW hu (k := 1) (r := .and (.var 0) .zero) (r' := .zero) hXe1 ⟨hv0, trivial⟩ trivial
        (I_eq_and_zero_r _) ((wf_of_ty hC.ty).restrict hX (ent_trans (ent_and_left _ _) (ent_and_left _ _)))
      rw [sk_zero1] at e2
      have e3 := VEq.restrict' hW hX hXe (VEq.dwk' hW hside)
      have eL0' := VEq.restrict' hW hX (ent_trans (ent_and_left _ _) (ent_and_left _ _)) eL0
      rw [tf_L0] at eL0' ⊢
      exact VEq.trans' hW e2 (VEq.conv' hW e3 (VEq.symm' hW eL0'))
    refine VEq.local' hW (φ := ψ.shift) (ψ := .neg (.var 0)) (KubusCore.I.scoped_shift hψ) hv0 (ent_and_right _ _)
      htube0 (VTy.restrict' hW hΞs (ent_and_left _ _) hbase) ?_ ?_
    · have e1 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hX (ent_and_left _ _) htube0)
      exact VEq.trans' hW e1 hcore
    · have hX2 : (cof (cof Φ.shift χ) (.neg (.var 0))).Scoped (Ψ + 1) := ⟨hΞs, hv0⟩
      exact VEq.splitR' hW (KubusCore.I.scoped_shift hψ) hv0 (ent_and_right _ _)
        (VTy.restrict' hW hX2 (ent_and_left _ _) htube0)
        (VTy.restrict' hW ⟨hX2, hv0⟩ (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _)
          (ent_and_left _ _))) hbase)
        (VEq.restrict' hW ⟨⟨hX2, KubusCore.I.scoped_shift hψ⟩, hv0⟩
          (ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) (ent_and_left _ _)))
            (ent_trans (ent_and_left _ _) (ent_and_right _ _))) hcore)
  have hside'' : VEq S (Ψ + 1) (cof Φ.shift χ) Γ.dshift ((KubusCore.Meta.fillTube ψ u u0).dinst .zero) u0.dshift
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by rw [fillTube_d0]; exact hside'
  have hc := VTy.comp' hW hKH hKT hL hχs htube hbase hside''
  have eC : VEq S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) C (.univ l) := by
    have e := VTy.lineIeq hW hC (k := 1) (r := .and (.var 0) .one) (r' := .var 0) (ent_refl _)
      ⟨hv0, trivial⟩ hv0 (I_eq_and_one_r _) hwX1
    rw [sk_var1] at e
    rw [tf_L1']; exact e
  have hfT : VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.fill C ψ u u0) C := VTy.conv' hW hc eC
  have hw00 : Wf0 S (Ψ + 0) Φ (Ctx.dren 0 Γ) := by rw [Ctx.dren_zero]; exact hw0
  have hΦ0 : I.Entails Φ (Φ.subst (fun n => .var (n + 0))) := by rw [I_add0]; exact ent_refl _
  refine ⟨hfT, ?_, ?_, ?_⟩
  · -- the endpoint 0
    have hd := VTy.dsubst' hW .zero trivial hfT
    rw [fill_dinst] at hd
    have e1 := VEq.compFace' hW hd (ent_trans (ent_negzero Φ) (ent_or_right _ _))
    rw [var_up_end0, fillTube_end] at e1
    have hE := VTy.endS' hW false hRs (ent_and_intro (ent_shift2_endS Φ false)
      (ent_trans (ent_negzero Φ) (ent_or_right _ _))) hw0 htube
    rw [Cfill_endS, fillTube_end] at hE
    have eE := VTy.lineIeq hW hC (k := 0) (r := .and .zero .one) (r' := .zero) hΦ0 ⟨trivial, trivial⟩ trivial
      (I_eq_and_zero _) hw00
    rw [Ctx.dren_zero, sk_zero0] at eE
    have hY : (cof (cof Φ ψ) (.neg .zero)).Scoped Ψ := ⟨hXψs, trivial⟩
    have hYψ : I.Entails (cof (cof Φ ψ) (.neg .zero)) ((cof Φ ψ).subst (fun n => .var (n + 0))) := by
      rw [I_add0]; exact ent_and_left _ _
    have eu := VTy.lineIeq hW hu (k := 0) (r := .and .zero .one) (r' := .zero) hYψ ⟨trivial, trivial⟩ trivial
      (I_eq_and_zero _) (by rw [Ctx.dren_zero]; exact hw0.restrict hY (ent_trans (ent_and_left _ _) (ent_and_left _ _)))
    rw [Ctx.dren_zero, sk_zero0] at eu
    have eEY := VEq.restrict' hW hY (ent_trans (ent_and_left _ _) (ent_and_left _ _)) eE
    have hov := VEq.trans' hW (VEq.conv' hW eu eEY) (VEq.restrict' hW hY (ent_and_left _ _) hside)
    have e2 := VEq.splitR' hW (ψ := .neg .zero) hψ trivial (ent_negzero Φ) (VTy.conv' hW hE eE)
      (VTy.restrict' hW (Φ' := cof Φ (.neg .zero)) ⟨hs, trivial⟩ (ent_and_left _ _) hu0) hov
    rw [fill_dinst]
    exact VEq.trans' hW e1 e2
  · -- the endpoint 1
    have hd := VTy.dsubst' hW .one trivial hfT
    rw [fill_dinst, Cfill_up1, fillTube_up1'] at hd
    have hX : (cof Φ (.or ψ (.neg .one))).Scoped Ψ := ⟨hs, ⟨hψ, trivial⟩⟩
    have hXs : (cof Φ (.or ψ (.neg .one))).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hX
    have eA := VTy.lineIeq hW hC (k := 1) (r := .var 0) (r' := .and .one (.var 0)) (ent_refl _) hv0
      ⟨trivial, hv0⟩ (I_eq_symm (I_eq_and_one_l _)) hwX1
    rw [sk_var1] at eA
    have htyped0 := VTy.isubL hW (n := 2) (m := 1) (Ψ0 := Ψ) (Φs := (cof Φ.shift χ).shift) (Γ0 := Γ)
      (Φ' := (cof Φ (.or ψ (.neg .one))).shift) (I.up (I.inst0 .one))
      (fun i hi => by
        rcases i with _ | _ | i
        · exact show 0 < Ψ + 1 by omega
        · trivial
        · omega)
      (fun i => rfl) hRs (by rw [fillR_up1]; exact ent_refl _)
      ((wf_of_ty hC.ty).restrict hXs (ent_shift (ent_and_left _ _)))
      (by rw [Ctx.dren_two]; exact htube)
    have htyped : VTy S (Ψ + 1) (cof Φ (.or ψ (.neg .one))).shift Γ.dshift
        (.split ψ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift)
        (C.subst Tm.var (sk (.and .one (.var 0)) 1)) := by
      have h : VTy S (Ψ + 1) (cof Φ (.or ψ (.neg .one))).shift Γ.dshift
          ((KubusCore.Meta.fillTube ψ u u0).subst Tm.var (I.up (I.inst0 .one)))
          ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).subst Tm.var (I.up (I.inst0 .one))) := htyped0
      rw [Cfill_up1, fillTube_up1'] at h
      exact h
    have hXψ : I.Entails (cof Φ (.or ψ (.neg .one))).shift ((cof Φ ψ).subst (fun n => .var (n + 1))) := by
      rw [I_add1]; exact ent_shift (ent_and_mono (ent_refl _) (ent_neg_one ψ))
    have htu : VEq S (Ψ + 1) (cof Φ (.or ψ (.neg .one))).shift Γ.dshift
        (.split ψ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift) u
        (C.subst Tm.var (sk (.and .one (.var 0)) 1)) := by
      have e1 := VEq.splitL' hW (ent_trans (ent_and_right _ _) (ent_shift (ent_neg_one ψ))) htyped
      have e2 := VTy.lineIeq hW hu (k := 1) (r := .and .one (.var 0)) (r' := .var 0) hXψ ⟨trivial, hv0⟩ hv0
        (I_eq_and_one_l _) ((wf_of_ty hC.ty).restrict hXs (ent_shift (ent_and_left _ _)))
      rw [sk_var1] at e2
      exact VEq.trans' hW e1 e2
    have hψX : I.Entails (cof Φ ψ).shift (cof Φ (.or ψ (.neg .one))).shift :=
      ent_shift (ent_and_mono (ent_refl _) (ent_or_left _ _))
    have hψs1 : (cof Φ ψ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hXψs
    have eAψ := VEq.restrict' hW hψs1 (ent_shift (ent_and_left _ _)) eA
    have huu := VEq.conv' hW (VEq.symm' hW (VEq.restrict' hW hψs1 hψX htu)) (VEq.symm' hW eAψ)
    have eA0 := VEq.dsubst' hW .zero trivial eA
    have e := VEq.compCong' hW hKH hKT hC hψ hu hu0 hside hd.ty eA (ent_or_left _ _) (ent_neg_one ψ) huu
      (VEq.refl' hu0)
    rw [fill_dinst, Cfill_up1, fillTube_up1']
    exact VEq.symm' hW e
  · -- under `ψ` the filler is the tube
    have hs' : (cof Φ ψ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hXψs
    have hψψ : I.Entails (cof Φ ψ).shift ψ.shift := ent_shift (ent_and_right Φ ψ)
    have hf' := VTy.restrict' hW hs' (ent_shift (ent_and_left Φ ψ)) hfT
    have e1 : VEq S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (Tm.fill C ψ u u0)
        ((KubusCore.Meta.fillTube ψ u u0).dinst .one) C :=
      VEq.compFace' hW hf' (ent_trans hψψ (ent_or_left _ _))
    have ht1 := VTy.dsubst' hW (Φ := cof Φ.shift χ) (Γ := Γ.dshift) .one trivial htube
    have ht1' := VTy.restrict' hW hs'
      (ent_and_intro (ent_shift (ent_and_left Φ ψ)) (ent_trans hψψ (ent_or_left _ _))) ht1
    rw [fillTube_d1] at e1 ht1'
    have e2 := VEq.splitL' hW hψψ ht1'
    have hψ1 : I.Entails (cof Φ ψ).shift ((cof Φ ψ).subst (fun n => .var (n + 1))) := by
      rw [I_add1]; exact ent_refl _
    have e3 := VTy.lineIeq hW hu (k := 1) (r := .and (.var 0) .one) (r' := .var 0) hψ1 ⟨hv0, trivial⟩ hv0
      (I_eq_and_one_r _) (wf_of_ty hu.ty)
    rw [sk_var1] at e3
    have eC' := VEq.restrict' hW hs' (ent_shift (ent_and_left Φ ψ)) eC
    rw [tf_L1'] at e2 eC'
    exact VEq.trans' hW e1 (VEq.conv' hW (VEq.trans' hW e2 e3) eC')

end

end Model.Whnf
