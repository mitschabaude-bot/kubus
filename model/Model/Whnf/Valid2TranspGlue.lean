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

/-! ### Judgments under a cofibration in the line variable -/

theorem VTy.sk2' {t A : Tm} {X r : I} (hr : r.Scoped (Ψ + 2)) (hΦ : Φ.Scoped Ψ) (hX : I.Entails X Φ.shift.shift)
    (hw : Wf0 S (Ψ + 1 + 1) X Γ.dshift.dshift) (h : VTy S (Ψ + 1) Φ.shift Γ.dshift t A) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk r 2)) (A.subst Tm.var (sk r 2)) := by
  have := VTy.bind2' hW hr hΦ hX hw h
  simp only [Tm.dsubst, pw_L] at this; exact this

theorem VTy.cofInst' {t T : Tm} {φ X r : I} (h : VTy S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t T) (hw : Wf0 S Ψ Φ Γ)
    (hr : r.Scoped Ψ) (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ) (hXφ : I.Entails X (φ.subst (I.inst0 r))) :
    VTy S Ψ X Γ (t.dinst r) (T.dinst r) := by
  have hΦs : (cof Φ.shift φ).Scoped (Ψ + 1) := scoped_of_ty h.ty
  have := VTy.isubL hW (n := 1) (m := 0) (Ψ0 := Ψ) (Φs := cof Φ.shift φ) (Γ0 := Γ) (Φ' := X) (I.inst0 r)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr) (fun i => rfl) hΦs
    (ent_and_intro (by rw [I_shift_inst0]; exact hXΦ) hXφ) (by rw [Ctx.dren_zero]; exact hw.restrict hXs hXΦ) h
  rw [Ctx.dren_zero] at this; exact this

theorem VEq.cofInst' {t u T : Tm} {φ X r : I} (h : VEq S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t u T)
    (hw : Wf0 S Ψ Φ Γ) (hr : r.Scoped Ψ) (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ)
    (hXφ : I.Entails X (φ.subst (I.inst0 r))) :
    VEq S Ψ X Γ (t.dinst r) (u.dinst r) (T.dinst r) := by
  have hΦs : (cof Φ.shift φ).Scoped (Ψ + 1) := scoped_of_eq h.eq
  have := VEq.isubL hW (n := 1) (m := 0) (Ψ0 := Ψ) (Φs := cof Φ.shift φ) (Γ0 := Γ) (Φ' := X) (I.inst0 r)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr) (fun i => rfl) hΦs
    (ent_and_intro (by rw [I_shift_inst0]; exact hXΦ) hXφ) (by rw [Ctx.dren_zero]; exact hw.restrict hXs hXΦ) h
  rw [Ctx.dren_zero] at this; exact this

theorem VTy.cofIns' {t T : Tm} {φ X : I} (h : VTy S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t T) (hw : Wf0 S Ψ Φ Γ)
    (hXs : X.Scoped (Ψ + 1 + 1)) (hXΦ : I.Entails X Φ.shift.shift)
    (hXφ : I.Entails X (φ.subst (sk (.var 0) 2))) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk (.var 0) 2)) (T.subst Tm.var (sk (.var 0) 2)) := by
  have hS := sigClosed_of_wfSig hW
  have hΦs : (cof Φ.shift φ).Scoped (Ψ + 1) := scoped_of_ty h.ty
  have := VTy.isubL hW (n := 1) (m := 2) (Ψ0 := Ψ) (Φs := cof Φ.shift φ) (Γ0 := Γ) (Φ' := X) (sk (.var 0) 2)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact show 0 < Ψ + 2 by omega) (fun i => rfl) hΦs
    (ent_and_intro (ent_sk2 _ hXΦ) hXφ) (by rw [Ctx.dren_two]; exact (hw.dwk2 hS).restrict hXs hXΦ) h
  rw [Ctx.dren_two] at this; exact this

/-! ### The inner system of `ω` at its ends -/

omit hW in
theorem tg_inner_d0 (e F G : Tm) :
    (Tm.split (.neg (.var 1)) (.app (.fst (e.dsubst (sk (.var 0) 2))) (F.dsubst (sk (.var 0) 2))) (.var 1)
      (G.dsubst (sk (.var 0) 2))).dinst .zero =
      .split (.neg (.var 0)) (.app (.fst (e.dinst .zero).dshift) (F.dinst .zero).dshift) (.var 0)
        (G.dinst .zero).dshift := by
  have h := sys_d e .zero (Tm.var 0) F G .zero (.inl rfl)
  simp only [tgSys', Tm.dinst, Tm.dsubst, Tm.subst] at h ⊢
  injection h with _ _ _ h1

omit hW in
theorem tg_inner_end (e F G : Tm) (d : Bool) :
    (Tm.split (.neg (.var 1)) (.app (.fst (e.dsubst (sk (.var 0) 2))) (F.dsubst (sk (.var 0) 2))) (.var 1)
      (G.dsubst (sk (.var 0) 2))).subst Tm.var (endS d) =
      .split (.neg (I.ofDir d)) (.app (.fst (e.dinst .one)) (F.dinst .one)) (I.ofDir d) (G.dinst .one) := by
  have h := sys_end e .zero (Tm.var 0) F G d
  simp only [tgSys', Tm.subst] at h ⊢
  injection h with _ _ _ h1

/-! ### More paired rules -/

theorem VEq.sndBeta' {a b T : Tm} (h : VTy S Ψ Φ Γ (.snd (.pair a b)) T) : VEq S Ψ Φ Γ (.snd (.pair a b)) b T := by
  have e := EqTm0.sndBeta h.ty
  exact ⟨e, valid_sndBeta hW h.v h.ty (presup hW e).2⟩

theorem VEq.pathBeta' {t T : Tm} {r : I} (h : VTy S Ψ Φ Γ (.papp (.plam t) r) T) :
    VEq S Ψ Φ Γ (.papp (.plam t) r) (t.dinst r) T := by
  have e := EqTm0.pathBeta h.ty
  exact ⟨e, valid_pathBeta hW h.v h.ty (presup hW e).2⟩

theorem VEq.pathCong' {L L' a a' b b' : Tm} {l : ℕ} (hL : VEq S (Ψ + 1) Φ.shift Γ.dshift L L' (.univ l))
    (ha : VEq S Ψ Φ Γ a a' (L.dinst .zero)) (hb : VEq S Ψ Φ Γ b b' (L.dinst .one)) :
    VEq S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l) := by
  have e := EqTm0.path hL.eq ha.eq hb.eq
  exact ⟨e, valid_path hW hL.v ha.v hb.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.fstBeta' {a b T : Tm} (h : VTy S Ψ Φ Γ (.fst (.pair a b)) T) : VEq S Ψ Φ Γ (.fst (.pair a b)) a T := by
  have e := EqTm0.fstBeta h.ty
  exact ⟨e, valid_fstBeta hW h.v h.ty (presup hW e).2⟩

theorem VEq.glueElFace' {e t a G : Tm} {φ : I} (hφ0 : I.Entails Φ φ) (h : VTy S Ψ Φ Γ (.glueEl φ e t a) G) :
    VEq S Ψ Φ Γ (.glueEl φ e t a) t G := by
  have e' := EqTm0.glueElFace hφ0 h.ty
  exact ⟨e', valid_glueElFace hW hφ0 h.v h.ty (presup hW e').2⟩

/-! ### The premises of the Glue transport -/

structure VTG (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I)
    (l l' : ℕ) : Prop where
  hKH : KHAll S
  hKT : KTAll S
  hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l)
  hφ : φ.Scoped (Ψ + 1)
  hT : VTy S (Ψ + 1) (cof Φ.shift φ) Γ.dshift T (.univ l)
  he : VTy S (Ψ + 1) (cof Φ.shift φ) Γ.dshift e (Tm.equiv T A)
  hψ : ψ.Scoped Ψ
  hδ : δ.Scoped Ψ
  hδφ : I.Entails δ φ.forall0
  hGl : VTy S (Ψ + 1) Φ.shift Γ.dshift (.glue A φ T e) (.univ l')
  hconst : VEq S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (.glue A φ T e) ((Tm.glue A φ T e).dinst .zero).dshift (.univ l')
  hu0 : VTy S Ψ Φ Γ u0 ((Tm.glue A φ T e).dinst .zero)

namespace VTG

variable {A : Tm} {φ : I} {T e : Tm} {ψ : I} {u0 : Tm} {δ : I} {l l' : ℕ}
  (H : VTG S Ψ Φ Γ A φ T e ψ u0 δ l l')
include H

theorem hS : SigClosed S := sigClosed_of_wfSig hW
theorem hw : Wf0 S Ψ Φ Γ := wf_of_ty H.hu0.ty
theorem hs : Φ.Scoped Ψ := scoped_of_ty H.hu0.ty

theorem hφr {r : I} (hr : r.Scoped Ψ) : (φ.subst (I.inst0 r)).Scoped Ψ :=
  scoped_subst H.hφ (fun i hi => by
    rcases i with _ | i
    · exact hr
    · exact show i < Ψ by omega)

theorem hG : VTy S (Ψ + 1) Φ.shift Γ.dshift (.glue A φ T e) (.univ l) := VTy.glue' hW H.hφ H.hA H.hT H.he

theorem hAr {r : I} (hr : r.Scoped Ψ) : VTy S Ψ Φ Γ (A.dinst r) (.univ l) := VTy.dsubst' hW r hr H.hA

theorem hGr {r : I} (hr : r.Scoped Ψ) :
    VTy S Ψ Φ Γ (.glue (A.dinst r) (φ.subst (I.inst0 r)) (T.dinst r) (e.dinst r)) (.univ l) :=
  VTy.dsubst' hW r hr (H.hG hW)

theorem hTr {r : I} (hr : r.Scoped Ψ) {X : I} (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ)
    (hXφ : I.Entails X (φ.subst (I.inst0 r))) : VTy S Ψ X Γ (T.dinst r) (.univ l) :=
  VTy.cofInst' hW H.hT (H.hw hW) hr hXs hXΦ hXφ

theorem her {r : I} (hr : r.Scoped Ψ) {X : I} (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ)
    (hXφ : I.Entails X (φ.subst (I.inst0 r))) : VTy S Ψ X Γ (e.dinst r) (Tm.equiv (T.dinst r) (A.dinst r)) := by
  have := VTy.cofInst' hW H.he (H.hw hW) hr hXs hXΦ hXφ
  rwa [equiv_dinst] at this

theorem ha0 : VTy S Ψ Φ Γ (tgA0 φ e u0) (A.dinst .zero) :=
  VTy.unglue' hW (H.hφr hW (r := .zero) trivial) (H.hGr hW (r := .zero) trivial) (H.hAr hW (r := .zero) trivial)
    (H.her hW (r := .zero) trivial ⟨H.hs hW, H.hφr hW (r := .zero) trivial⟩ (ent_and_left _ _) (ent_and_right _ _))
    H.hu0

theorem hXψs : (cof Φ ψ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨H.hs hW, H.hψ⟩

theorem hu0line : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u0.dshift (.glue A φ T e) :=
  VTy.conv' hW (VTy.restrict' hW (H.hXψs hW) (ent_shift (ent_and_left _ _)) (VTy.dwk' hW H.hu0))
    (VEq.symm' hW H.hconst)

theorem htube : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (tgTube φ e u0) A := by
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left _ _)
  exact VTy.unglue' hW H.hφ (VTy.restrict' hW (H.hXψs hW) hXΦ (H.hG hW)) (VTy.restrict' hW (H.hXψs hW) hXΦ H.hA)
    (VTy.restrict' hW ⟨H.hXψs hW, H.hφ⟩ (ent_and_mono hXΦ (ent_refl _)) H.he) (H.hu0line hW)

theorem htube_side : VEq S Ψ (cof Φ ψ) Γ ((tgTube φ e u0).dinst .zero) (tgA0 φ e u0) (A.dinst .zero) := by
  rw [tgTube_dinst]; exact VEq.refl' (VTy.restrict' hW ⟨H.hs hW, H.hψ⟩ (ent_and_left _ _) (H.ha0 hW))

theorem ha1' : VTy S Ψ Φ Γ (tgA1' A φ e ψ u0) (A.dinst .one) :=
  VTy.comp' hW H.hKH H.hKT H.hA H.hψ (H.htube hW) (H.ha0 hW) (H.htube_side hW)

/-! #### On `δ` (`∀i. φ`) the line is `T` -/

theorem hZs : (cof Φ δ).Scoped Ψ := ⟨H.hs hW, H.hδ⟩
theorem hZΦ : I.Entails (cof Φ δ) Φ := ent_and_left _ _
theorem hZφr (r : I) : I.Entails (cof Φ δ) (φ.subst (I.inst0 r)) :=
  ent_trans (ent_and_right _ _) (ent_forall_inst H.hδφ r)
theorem hZφ : I.Entails (cof Φ δ).shift φ :=
  ent_trans (ent_shift (ent_and_right Φ δ)) (ent_forall_shift H.hδφ)
theorem hZs1 : (cof Φ δ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift (H.hZs hW)

theorem hGT : VEq S (Ψ + 1) (cof Φ δ).shift Γ.dshift (.glue A φ T e) T (.univ l') :=
  VEq.glueFace' hW (H.hZφ hW) (VTy.restrict' hW (H.hZs1 hW) (ent_shift (H.hZΦ hW)) H.hGl)

theorem hGTr {r : I} (hr : r.Scoped Ψ) :
    VEq S Ψ (cof Φ δ) Γ ((Tm.glue A φ T e).dinst r) (T.dinst r) (.univ l') := by
  have hG : VTy S Ψ Φ Γ (.glue (A.dinst r) (φ.subst (I.inst0 r)) (T.dinst r) (e.dinst r)) (.univ l') :=
    VTy.dsubst' hW r hr H.hGl
  exact VEq.glueFace' hW (H.hZφr hW r) (VTy.restrict' hW (H.hZs hW) (H.hZΦ hW) hG)

theorem hTZ : VTy S (Ψ + 1) (cof Φ δ).shift Γ.dshift T (.univ l') := VEq.rty' hW (H.hGT hW)

theorem heZ : VTy S (Ψ + 1) (cof Φ δ).shift Γ.dshift e (Tm.equiv T A) :=
  VTy.restrict' hW (H.hZs1 hW) (ent_and_intro (ent_shift (H.hZΦ hW)) (H.hZφ hW)) H.he

theorem hZψs : (cof (cof Φ δ) ψ).Scoped Ψ := ⟨H.hZs hW, H.hψ⟩
theorem hZψs1 : (cof (cof Φ δ) ψ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift (H.hZψs hW)
theorem hZψΦψ : I.Entails (cof (cof Φ δ) ψ) (cof Φ ψ) := ent_and_mono (H.hZΦ hW) (ent_refl _)
theorem hZψZ : I.Entails (cof (cof Φ δ) ψ) (cof Φ δ) := ent_and_left _ _

theorem hconstT : VEq S (Ψ + 1) (cof (cof Φ δ) ψ).shift Γ.dshift T (T.dinst .zero).dshift (.univ l') := by
  have e1 := VEq.restrict' hW (H.hZψs1 hW) (ent_shift (H.hZψZ hW)) (H.hGT hW)
  have e2 := VEq.restrict' hW (H.hZψs1 hW) (ent_shift (H.hZψΦψ hW)) H.hconst
  have e3 := VEq.restrict' hW (H.hZψs1 hW) (ent_shift (H.hZψZ hW)) (VEq.dwk' hW (H.hGTr hW (r := .zero) trivial))
  exact VEq.trans' hW (VEq.symm' hW e1) (VEq.trans' hW e2 e3)

theorem hu0T : VTy S Ψ (cof Φ δ) Γ u0 (T.dinst .zero) :=
  VTy.conv' hW (VTy.restrict' hW (H.hZs hW) (H.hZΦ hW) H.hu0) (H.hGTr hW (r := .zero) trivial)

theorem ht1 : VTy S Ψ (cof Φ δ) Γ (tgT1 T ψ u0) (T.dinst .one) :=
  VTy.transpG hW H.hKT (H.hTZ hW) H.hψ (H.hconstT hW) (H.hu0T hW)

/-! #### The path `ω` on `δ` -/

theorem hδ2 : I.Entails δ.shift.shift (φ.subst (sk (.var 0) 2)) := by
  have := ent_forall_sk H.hδφ (.var 0) 2; rwa [I_add2] at this

theorem hwX {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X Φ.shift.shift) :
    Wf0 S (Ψ + 1 + 1) X Γ.dshift.dshift := ((H.hw hW).dwk2 (H.hS hW)).restrict hXs hX

theorem heIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof Φ δ).shift.shift) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift (e.dsubst (sk (.var 0) 2))
      (Tm.equiv (T.dsubst (sk (.var 0) 2)) (A.dsubst (sk (.var 0) 2))) := by
  have := VTy.cofIns' hW H.he (H.hw hW) hXs (ent_trans hX (ent_shift (ent_shift (ent_and_left Φ δ))))
    (ent_trans hX (ent_trans (ent_shift (ent_shift (ent_and_right Φ δ))) (H.hδ2 hW)))
  rwa [equiv_subst] at this

theorem hCIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X Φ.shift.shift) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift (A.dsubst (sk (.var 0) 2)) (.univ l) :=
  VTy.sk2' hW (r := .var 0) (show 0 < Ψ + 2 by omega) (H.hs hW) hX (H.hwX hW hXs hX) H.hA

theorem hu0Ins {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof (cof Φ δ) ψ).shift.shift) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift u0.dshift.dshift (T.dsubst (sk (.var 0) 2)) := by
  have hXΦ : I.Entails X Φ.shift.shift :=
    ent_trans hX (ent_shift (ent_shift (ent_trans (H.hZψZ hW) (H.hZΦ hW))))
  have e := VEq.sk2' hW (r := .var 0) (show 0 < Ψ + 2 by omega) (H.hZψs hW) hX (H.hwX hW hXs hXΦ) (H.hconstT hW)
  rw [dshift_sk2] at e
  have hu := VTy.restrict' hW hXs (ent_trans hX (ent_shift (ent_shift (H.hZψZ hW))))
    (VTy.dwk' hW (VTy.dwk' hW (H.hu0T hW)))
  exact VTy.conv' hW hu (VEq.symm' hW e)

theorem htfIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof Φ δ).shift.shift) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift ((Tm.transpFill T ψ u0).dsubst (sk (.var 0) 2)) (T.dsubst (sk (.var 0) 2)) :=
  VTy.sk2' hW (r := .var 0) (show 0 < Ψ + 2 by omega) (H.hZs hW) hX
    (H.hwX hW hXs (ent_trans hX (ent_shift (ent_shift (H.hZΦ hW)))))
    (VTy.transpFill' hW H.hKT (H.hTZ hW) H.hψ (H.hconstT hW) (H.hu0T hW)).1

theorem hfillIns {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X Φ.shift.shift) :
    VTy S (Ψ + 1 + 1) X Γ.dshift.dshift ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dsubst (sk (.var 0) 2))
      (A.dsubst (sk (.var 0) 2)) :=
  VTy.sk2' hW (r := .var 0) (show 0 < Ψ + 2 by omega) (H.hs hW) hX (H.hwX hW hXs hX)
    (VTy.fill' hW H.hKH H.hKT H.hA H.hψ (H.htube hW) (H.ha0 hW) (H.htube_side hW)).1

theorem E1 {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof (cof Φ δ) ψ).shift.shift) :
    VEq S (Ψ + 1 + 1) X Γ.dshift.dshift ((Tm.transpFill T ψ u0).dsubst (sk (.var 0) 2)) u0.dshift.dshift
      (T.dsubst (sk (.var 0) 2)) := by
  have hXΦ : I.Entails X Φ.shift.shift :=
    ent_trans hX (ent_shift (ent_shift (ent_trans (H.hZψZ hW) (H.hZΦ hW))))
  have := VEq.sk2' hW (r := .var 0) (show 0 < Ψ + 2 by omega) (H.hZψs hW) hX (H.hwX hW hXs hXΦ)
    (VTy.transpFill' hW H.hKT (H.hTZ hW) H.hψ (H.hconstT hW) (H.hu0T hW)).2.2.2
  rwa [dshift_sk2] at this

theorem hfillψδ : VEq S (Ψ + 1) (cof (cof Φ δ) ψ).shift Γ.dshift (Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0))
    (.app (.fst e) u0.dshift) A := by
  have e1 := VEq.restrict' hW (H.hZψs1 hW) (ent_shift (H.hZψΦψ hW))
    (VTy.fill' hW H.hKH H.hKT H.hA H.hψ (H.htube hW) (H.ha0 hW) (H.htube_side hW)).2.2.2
  have hu0l := VTy.restrict' hW (H.hZψs1 hW) (ent_shift (H.hZψΦψ hW)) (H.hu0line hW)
  have hAZ := VTy.restrict' hW (H.hZψs1 hW) (ent_shift (ent_trans (H.hZψZ hW) (H.hZΦ hW))) H.hA
  have heZ := VTy.restrict' hW (H.hZψs1 hW) (ent_shift (H.hZψZ hW)) (H.heZ hW)
  have hl := VTy.unglue' hW H.hφ (VTy.restrict' hW (H.hZψs1 hW) (ent_shift (ent_trans (H.hZψZ hW) (H.hZΦ hW)))
    (H.hG hW)) hAZ (VTy.restrict' hW ⟨H.hZψs1 hW, H.hφ⟩ (ent_and_left _ _) heZ) hu0l
  have e2 := VEq.unglueFace' hW (ent_trans (ent_shift (H.hZψZ hW)) (H.hZφ hW)) hl hu0l hAZ heZ
  exact VEq.trans' hW e1 e2

theorem E2 {X : I} (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X (cof (cof Φ δ) ψ).shift.shift) :
    VEq S (Ψ + 1 + 1) X Γ.dshift.dshift ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dsubst (sk (.var 0) 2))
      (.app (.fst (e.dsubst (sk (.var 0) 2))) u0.dshift.dshift) (A.dsubst (sk (.var 0) 2)) := by
  have hXΦ : I.Entails X Φ.shift.shift :=
    ent_trans hX (ent_shift (ent_shift (ent_trans (H.hZψZ hW) (H.hZΦ hW))))
  have := VEq.sk2' hW (r := .var 0) (show 0 < Ψ + 2 by omega) (H.hZψs hW) hX (H.hwX hW hXs hXΦ) (H.hfillψδ hW)
  rwa [app_sk2] at this

/-- The inner system of `ω` (`j = 0 ↦ e.1 tfill, j = 1 ↦ fill`), at any face below `δ`. -/
theorem hinnerG {R : I} (hRs : R.Scoped (Ψ + 1 + 1)) (hRZ : I.Entails R (cof Φ δ).shift.shift) :
    VTy S (Ψ + 1 + 1) (cof R (.or (.neg (.var 1)) (.var 1))) Γ.dshift.dshift
      (.split (.neg (.var 1)) (.app (.fst (e.dsubst (sk (.var 0) 2))) ((Tm.transpFill T ψ u0).dsubst (sk (.var 0) 2)))
        (.var 1) ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dsubst (sk (.var 0) 2))) (A.dsubst (sk (.var 0) 2)) := by
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hZΦ2 : I.Entails (cof Φ δ).shift.shift Φ.shift.shift := ent_shift (ent_shift (ent_and_left Φ δ))
  let j2 : I := .or (.neg (.var 1)) (.var 1)
  have hR2s : (cof R j2).Scoped (Ψ + 1 + 1) := ⟨hRs, ⟨hv1, hv1⟩⟩
  have hR2Z : I.Entails (cof R j2) (cof Φ δ).shift.shift := ent_trans (ent_and_left R j2) hRZ
  have hR21s : (cof (cof R j2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hR2s, hv1⟩
  have hR22s : (cof (cof R j2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hR2s, hv1⟩
  have hR21Z : I.Entails (cof (cof R j2) (.neg (.var 1))) (cof Φ δ).shift.shift :=
    ent_trans (ent_and_left _ (.neg (.var 1))) hR2Z
  have hR22Z : I.Entails (cof (cof R j2) (.var 1)) (cof Φ δ).shift.shift := ent_trans (ent_and_left _ (.var 1)) hR2Z
  have b2 := VTy.appFst' hW (H.heIns hW hR21s hR21Z) (H.htfIns hW hR21s hR21Z)
  have b3 := H.hfillIns hW hR22s (ent_trans hR22Z hZΦ2)
  exact VTy.split' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right R j2)
    (H.hCIns hW hR2s (ent_trans hR2Z hZΦ2)).ty b2 b3
    (VEq.absurd' hW (ent_contra (cof R j2) 1)
      (VTy.restrict' hW (Φ' := cof (cof (cof R j2) (.neg (.var 1))) (.var 1)) ⟨hR21s, hv1⟩
        (ent_and_left _ (.var 1)) b2).ty
      (VTy.restrict' hW (Φ' := cof (cof (cof R j2) (.neg (.var 1))) (.var 1)) ⟨hR21s, hv1⟩
        (ent_and_mono (ent_and_left (cof R j2) (.neg (.var 1))) (ent_refl (.var 1))) b3).ty)

/-- The system of `ω`. -/
theorem hsys : VTy S (Ψ + 1 + 1) (cof (cof Φ δ).shift (tgChi ψ)).shift Γ.dshift.dshift
    (tgSys A φ T e ψ u0) (A.dsubst (sk (.var 0) 2)) := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hRs : (cof (cof Φ δ).shift (tgChi ψ)).shift.Scoped (Ψ + 1 + 1) :=
    KubusCore.I.scoped_shift ⟨H.hZs1 hW, ⟨KubusCore.I.scoped_shift H.hψ, ⟨hv0, hv0⟩⟩⟩
  have hRZ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)).shift (cof Φ δ).shift.shift := ent_shift (ent_and_left _ _)
  have hRχ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)).shift (.or ψ.shift.shift (.or (.neg (.var 1)) (.var 1))) :=
    ent_shift (ent_and_right (cof Φ δ).shift (tgChi ψ))
  have hinner := H.hinnerG hW hRs hRZ
  generalize (cof (cof Φ δ).shift (tgChi ψ)).shift = R at hRs hRZ hRχ hinner ⊢
  have hZΦ2 : I.Entails (cof Φ δ).shift.shift Φ.shift.shift := ent_shift (ent_shift (ent_and_left Φ δ))
  have hZψ2 : ∀ {X : I}, I.Entails X (cof Φ δ).shift.shift → I.Entails X ψ.shift.shift →
      I.Entails X (cof (cof Φ δ) ψ).shift.shift := fun h1 h2 =>
    show I.Entails _ (.and _ _) from ent_and_intro h1 h2
  have hψ2 : ψ.shift.shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift (KubusCore.I.scoped_shift H.hψ)
  -- the branch `ψ`
  have hR1s : (cof R ψ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hRs, hψ2⟩
  have hR1Z : I.Entails (cof R ψ.shift.shift) (cof Φ δ).shift.shift := ent_trans (ent_and_left R _) hRZ
  have hR1W := hZψ2 hR1Z (ent_and_right R _)
  have b1 := VTy.appFst' hW (H.heIns hW hR1s hR1Z) (H.hu0Ins hW hR1s hR1W)
  let j2 : I := .or (.neg (.var 1)) (.var 1)
  have hR2Z : I.Entails (cof R j2) (cof Φ δ).shift.shift := ent_trans (ent_and_left R j2) hRZ
  -- agreement
  have hYs : (cof (cof R ψ.shift.shift) j2).Scoped (Ψ + 1 + 1) := ⟨hR1s, ⟨hv1, hv1⟩⟩
  have hYR2 : I.Entails (cof (cof R ψ.shift.shift) j2) (cof R j2) :=
    ent_and_mono (ent_and_left R ψ.shift.shift) (ent_refl j2)
  have hYW : I.Entails (cof (cof R ψ.shift.shift) j2) (cof (cof Φ δ) ψ).shift.shift :=
    ent_trans (ent_and_left _ j2) hR1W
  have hYZ : I.Entails (cof (cof R ψ.shift.shift) j2) (cof Φ δ).shift.shift := ent_trans hYR2 hR2Z
  have hover := VEq.local' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ j2)
    (VTy.restrict' hW hYs (ent_and_left _ j2) b1) (VTy.restrict' hW hYs hYR2 hinner)
    (by
      have hs1 : (cof (cof (cof R ψ.shift.shift) j2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hl := ent_and_left (cof (cof R ψ.shift.shift) j2) (.neg (.var 1))
      have s1 := VEq.splitL' hW (ent_and_right _ (.neg (.var 1))) (VTy.restrict' hW hs1 (ent_trans hl hYR2) hinner)
      have c1 := VEq.appFst' hW (H.heIns hW hs1 (ent_trans hl hYZ)) (VEq.symm' hW (H.E1 hW hs1 (ent_trans hl hYW)))
      exact VEq.trans' hW c1 (VEq.symm' hW s1))
    (by
      have hs1 : (cof (cof (cof R ψ.shift.shift) j2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hl := ent_and_left (cof (cof R ψ.shift.shift) j2) (.var 1)
      have hs2 : (cof (cof (cof (cof (cof R ψ.shift.shift) j2) (.var 1)) (.neg (.var 1))) (.var 1)).Scoped
          (Ψ + 1 + 1) := ⟨⟨hs1, hv1⟩, hv1⟩
      have hin1 := VTy.restrict' hW hs1 (ent_trans hl hYR2) hinner
      have hb3 := H.hfillIns hW hs1 (ent_trans (ent_trans hl hYZ) hZΦ2)
      have s2 := VEq.splitR' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ (.var 1)) hin1
        (VTy.restrict' hW ⟨hs1, hv1⟩ (ent_and_left _ _) hb3)
        (VEq.absurd' hW (ent_contra _ 1)
          (VTy.restrict' hW hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _))
            (VTy.appFst' hW (H.heIns hW hs1 (ent_trans hl hYZ)) (H.htfIns hW hs1 (ent_trans hl hYZ)))).ty
          (VTy.restrict' hW hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hb3).ty)
      exact VEq.trans' hW (VEq.symm' hW (H.E2 hW hs1 (ent_trans hl hYW))) (VEq.symm' hW s2))
  exact VTy.split' hW (φ := ψ.shift.shift) (ψ := .or (.neg (.var 1)) (.var 1)) hψ2 ⟨hv1, hv1⟩ hRχ
    (H.hCIns hW hRs (ent_trans hRZ hZΦ2)).ty b1 hinner hover

theorem he0Z (r : I) (hr : r.Scoped Ψ) : VTy S Ψ (cof Φ δ) Γ (e.dinst r) (Tm.equiv (T.dinst r) (A.dinst r)) :=
  H.her hW hr (H.hZs hW) (H.hZΦ hW) (H.hZφr hW r)

theorem hbaseω : VTy S (Ψ + 1) (cof Φ δ).shift Γ.dshift (.app (.fst (e.dinst .zero).dshift) u0.dshift)
    ((A.dsubst (sk (.var 0) 2)).dinst .zero) := by
  rw [L_C0]; exact VTy.dwk' hW (VTy.appFst' hW (H.he0Z hW .zero trivial) (H.hu0T hW))

theorem hfill0 : VEq S Ψ (cof Φ δ) Γ ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .zero)
    (.app (.fst (e.dinst .zero)) u0) (A.dinst .zero) := by
  have e1 := VEq.restrict' hW (H.hZs hW) (H.hZΦ hW)
    (VTy.fill' hW H.hKH H.hKT H.hA H.hψ (H.htube hW) (H.ha0 hW) (H.htube_side hW)).2.1
  have hu0Z := VTy.restrict' hW (H.hZs hW) (H.hZΦ hW) H.hu0
  have hA0Z := VTy.restrict' hW (H.hZs hW) (H.hZΦ hW) (H.hAr hW (r := .zero) trivial)
  have hl := VTy.unglue' hW (H.hφr hW (r := .zero) trivial)
    (VTy.restrict' hW (H.hZs hW) (H.hZΦ hW) (H.hGr hW (r := .zero) trivial)) hA0Z
    (VTy.restrict' hW ⟨H.hZs hW, H.hφr hW (r := .zero) trivial⟩ (ent_and_left _ _) (H.he0Z hW .zero trivial)) hu0Z
  have e2 := VEq.unglueFace' hW (H.hZφr hW .zero) hl hu0Z hA0Z (H.he0Z hW .zero trivial)
  exact VEq.trans' hW e1 e2

theorem hsideω : VEq S (Ψ + 1) (cof (cof Φ δ).shift (tgChi ψ)) Γ.dshift ((tgSys A φ T e ψ u0).dinst .zero)
    (.app (.fst (e.dinst .zero).dshift) u0.dshift) ((A.dsubst (sk (.var 0) 2)).dinst .zero) := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hQs : (cof (cof Φ δ).shift (tgChi ψ)).Scoped (Ψ + 1) :=
    ⟨H.hZs1 hW, ⟨KubusCore.I.scoped_shift H.hψ, ⟨hv0, hv0⟩⟩⟩
  have hQZ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)) (cof Φ δ).shift := ent_and_left _ _
  have hQχ : I.Entails (cof (cof Φ δ).shift (tgChi ψ)) (.or ψ.shift (.or (.neg (.var 0)) (.var 0))) :=
    ent_and_right _ _
  have hs0 := VTy.dsubst' hW (Φ := cof (cof Φ δ).shift (tgChi ψ)) (Γ := Γ.dshift) .zero trivial (H.hsys hW)
  have hb := VTy.restrict' hW hQs hQZ (H.hbaseω hW)
  have hin := VTy.dsubst' hW (Φ := cof (cof (cof Φ δ).shift (tgChi ψ)) (.or (.neg (.var 0)) (.var 0)))
    (Γ := Γ.dshift) .zero trivial (H.hinnerG hW (R := (cof (cof Φ δ).shift (tgChi ψ)).shift)
      (KubusCore.I.scoped_shift hQs) (ent_shift hQZ))
  rw [L_C0] at hs0 hb hin ⊢
  rw [tg_inner_d0] at hin
  have tf0 := (VTy.transpFill' hW H.hKT (H.hTZ hW) H.hψ (H.hconstT hW) (H.hu0T hW)).2.1
  generalize (cof (cof Φ δ).shift (tgChi ψ)) = Q at hQs hQZ hQχ hs0 hb hin ⊢
  simp only [tgSys] at hs0 ⊢
  rw [sys_d _ _ _ _ _ _ (.inl rfl)] at hs0 ⊢
  have hQ2s : (cof Q (.or (.neg (.var 0)) (.var 0))).Scoped (Ψ + 1) := ⟨hQs, ⟨hv0, hv0⟩⟩
  have hQ2Z : I.Entails (cof Q (.or (.neg (.var 0)) (.var 0))) (cof Φ δ).shift := ent_trans (ent_and_left _ _) hQZ
  have hi0 : VEq S (Ψ + 1) (cof (cof Q (.or (.neg (.var 0)) (.var 0))) (.neg (.var 0))) Γ.dshift
      (.app (.fst (e.dinst .zero).dshift) (Tm.transpFill T ψ u0 |>.dinst .zero).dshift)
      (.app (.fst (e.dinst .zero).dshift) u0.dshift) (A.dinst .zero).dshift :=
    VEq.restrict' hW ⟨hQ2s, hv0⟩ (ent_trans (ent_and_left _ _) hQ2Z)
      (VEq.dwk' hW (VEq.appFst' hW (H.he0Z hW .zero trivial) tf0))
  have hi1 : VEq S (Ψ + 1) (cof (cof Q (.or (.neg (.var 0)) (.var 0))) (.var 0)) Γ.dshift
      ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .zero).dshift
      (.app (.fst (e.dinst .zero).dshift) u0.dshift) (A.dinst .zero).dshift := by
    exact VEq.restrict' hW (Φ' := cof (cof Q (.or (.neg (.var 0)) (.var 0))) (.var 0)) ⟨hQ2s, hv0⟩
      (ent_trans (ent_and_left _ _) hQ2Z) (VEq.dwk' hW (H.hfill0 hW))
  have hQ3s : (cof (cof (cof (cof Q (.or (.neg (.var 0)) (.var 0))) (.var 0)) (.neg (.var 0))) (.var 0)).Scoped
      (Ψ + 1) := ⟨⟨⟨hQ2s, hv0⟩, hv0⟩, hv0⟩
  have hinEq : VEq S (Ψ + 1) (cof Q (.or (.neg (.var 0)) (.var 0))) Γ.dshift
      (.split (.neg (.var 0)) (.app (.fst (e.dinst .zero).dshift) (Tm.transpFill T ψ u0 |>.dinst .zero).dshift)
        (.var 0) ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .zero).dshift)
      (.app (.fst (e.dinst .zero).dshift) u0.dshift) (A.dinst .zero).dshift := by
    refine VEq.local' hW (φ := .neg (.var 0)) (ψ := .var 0) hv0 hv0 (ent_and_right _ _) hin
      (VTy.restrict' hW hQ2s (ent_and_left _ _) hb) ?_ ?_
    · exact VEq.trans' hW (VEq.splitL' hW (ent_and_right _ _)
        (VTy.restrict' hW ⟨hQ2s, hv0⟩ (ent_and_left _ _) hin)) hi0
    · exact VEq.trans' hW (VEq.splitR' hW hv0 hv0 (ent_and_right _ _)
        (VTy.restrict' hW ⟨hQ2s, hv0⟩ (ent_and_left _ _) hin)
        (VEq.lty' hW (VEq.restrict' hW ⟨⟨hQ2s, hv0⟩, hv0⟩ (ent_and_mono (ent_and_left _ _) (ent_refl _)) hi1))
        (VEq.absurd' hW (ent_contra _ 0)
          (VEq.lty' hW (VEq.restrict' hW hQ3s (ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _)
            (ent_and_left _ _))) (ent_trans (ent_and_left _ _) (ent_and_right _ _))) hi0)).ty
          (VEq.lty' hW (VEq.restrict' hW hQ3s (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hi1)).ty)) hi1
  refine VEq.local' hW (φ := ψ.shift) (ψ := .or (.neg (.var 0)) (.var 0)) (KubusCore.I.scoped_shift H.hψ)
    ⟨hv0, hv0⟩ hQχ hs0 hb ?_ ?_
  · exact VEq.splitL' hW (ent_and_right _ _)
      (VTy.restrict' hW ⟨hQs, KubusCore.I.scoped_shift H.hψ⟩ (ent_and_left _ _) hs0)
  · refine VEq.trans' hW (VEq.splitR' hW (KubusCore.I.scoped_shift H.hψ) ⟨hv0, hv0⟩ (ent_and_right _ _)
      (VTy.restrict' hW hQ2s (ent_and_left _ _) hs0) (VTy.restrict' hW ⟨hQ2s, ⟨hv0, hv0⟩⟩ (ent_and_left _ _) hin)
      (VEq.symm' hW (VEq.restrict' hW ⟨⟨hQ2s, KubusCore.I.scoped_shift H.hψ⟩, ⟨hv0, hv0⟩⟩
        (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hinEq))) hinEq

theorem hbody : VTy S (Ψ + 1) (cof Φ δ).shift Γ.dshift (tgBody A φ T e ψ u0) (A.dinst .one).dshift := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have := VTy.comp' hW H.hKH H.hKT (H.hCIns hW (KubusCore.I.scoped_shift (H.hZs1 hW))
      (ent_shift (ent_shift (ent_and_left Φ δ))))
    (show (tgChi ψ).Scoped (Ψ + 1) from ⟨KubusCore.I.scoped_shift H.hψ, ⟨hv0, hv0⟩⟩) (H.hsys hW) (H.hbaseω hW)
    (H.hsideω hW)
  rwa [L_C1] at this

theorem hA1Z : VTy S Ψ (cof Φ δ) Γ (A.dinst .one) (.univ l) :=
  VTy.restrict' hW (H.hZs hW) (H.hZΦ hW) (H.hAr hW (r := .one) trivial)

theorem hwZ : Wf0 S Ψ (cof Φ δ) Γ := (H.hw hW).restrict (H.hZs hW) (H.hZΦ hW)

/-- The ends of `ω`. -/
theorem hωend (d : Bool) : VEq S Ψ (cof Φ δ) Γ ((tgBody A φ T e ψ u0).dinst (I.ofDir d))
    (.split (.neg (I.ofDir d)) (.app (.fst (e.dinst .one)) ((Tm.transpFill T ψ u0).dinst .one)) (I.ofDir d)
      ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .one)) (A.dinst .one) ∧
    VTy S Ψ (cof Φ δ) Γ (.split (.neg (I.ofDir d)) (.app (.fst (e.dinst .one)) ((Tm.transpFill T ψ u0).dinst .one))
      (I.ofDir d) ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .one)) (A.dinst .one) := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hdd : (I.ofDir d).Scoped Ψ := by cases d <;> trivial
  have hor : I.Entails (cof Φ δ) (.or (.neg (I.ofDir d)) (I.ofDir d)) := by
    cases d
    · exact ent_negzero_or _
    · exact ent_one_or _
  have hb0 := VTy.dsubst' hW (Φ := cof Φ δ) (I.ofDir d) hdd (H.hbody hW)
  rw [dshift_dinst, tgBody_dinst] at hb0
  have e1 := VEq.compFace' hW hb0 (ent_trans hor (ent_or_right _ _))
  have hQs : (cof (cof Φ δ).shift (tgChi ψ)).shift.Scoped (Ψ + 1 + 1) :=
    KubusCore.I.scoped_shift ⟨H.hZs1 hW, ⟨KubusCore.I.scoped_shift H.hψ, ⟨hv0, hv0⟩⟩⟩
  have hent : I.Entails (cof Φ δ) (((cof (cof Φ δ).shift (tgChi ψ)).shift).subst (endS d)) :=
    ent_and_intro (ent_shift2_endS (cof Φ δ) d) (ent_trans hor (ent_or_right _ _))
  have hE := VTy.endS' hW d hQs hent (H.hwZ hW) (H.hsys hW)
  rw [L_CE] at hE
  have hsE : (tgSys A φ T e ψ u0).subst Tm.var (endS d) = .split ψ (.app (.fst (e.dinst .one)) u0)
      (.or (.neg (I.ofDir d)) (I.ofDir d)) (.split (.neg (I.ofDir d)) (.app (.fst (e.dinst .one))
        ((Tm.transpFill T ψ u0).dinst .one)) (I.ofDir d) ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .one)) :=
    sys_end _ _ _ _ _ d
  have hu : ((tgSys A φ T e ψ u0).subst Tm.var (I.up (I.inst0 (I.ofDir d)))).dinst .one =
      (tgSys A φ T e ψ u0).subst Tm.var (endS d) := by cases d <;> ssub
  rw [hu, hsE] at e1
  rw [hsE] at hE
  have hin := VTy.endS' hW d (Φs := cof (cof (cof Φ δ).shift (tgChi ψ)).shift (.or (.neg (.var 1)) (.var 1)))
    ⟨hQs, ⟨hv1, hv1⟩⟩ (ent_and_intro hent hor) (H.hwZ hW)
    (H.hinnerG hW hQs (ent_shift (ent_and_left _ _)))
  rw [L_CE, tg_inner_end] at hin
  -- the overlap on `ψ`
  have hWs : (cof (cof Φ δ) ψ).Scoped Ψ := H.hZψs hW
  have htf1 := VEq.dsubst' hW (Φ := cof (cof Φ δ) ψ) .one trivial
    (VTy.transpFill' hW H.hKT (H.hTZ hW) H.hψ (H.hconstT hW) (H.hu0T hW)).2.2.2
  rw [dshift_dinst] at htf1
  have hfl1 := VEq.dsubst' hW (Φ := cof (cof Φ δ) ψ) .one trivial (H.hfillψδ hW)
  rw [show (Tm.app (.fst e) u0.dshift).dinst .one = .app (.fst (e.dinst .one)) u0 by
    show Tm.app (.fst (e.dinst .one)) (u0.dshift.dinst .one) = _; rw [dshift_dinst]] at hfl1
  have he1ψ := VTy.restrict' hW hWs (H.hZψZ hW) (H.he0Z hW .one trivial)
  have ea := VEq.appFst' hW he1ψ htf1
  have hinψ := VTy.restrict' hW hWs (H.hZψZ hW) hin
  have hov : VEq S Ψ (cof (cof Φ δ) ψ) Γ (.app (.fst (e.dinst .one)) u0)
      (.split (.neg (I.ofDir d)) (.app (.fst (e.dinst .one)) ((Tm.transpFill T ψ u0).dinst .one)) (I.ofDir d)
        ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dinst .one)) (A.dinst .one) := by
    cases d
    · exact VEq.symm' hW (VEq.trans' hW (VEq.splitL' hW (ent_negzero _) hinψ) ea)
    · refine VEq.symm' hW (VEq.trans' hW (VEq.splitR' hW (φ := .neg .one) (ψ := .one) trivial trivial (ent_one _) hinψ
        (VEq.lty' hW (VEq.restrict' hW ⟨hWs, trivial⟩ (ent_and_left _ _) hfl1)) ?_) hfl1)
      have hz : I.Entails (cof (cof (cof (cof Φ δ) ψ) (.neg .one)) .one) .zero :=
        ent_trans (ent_trans (ent_and_left _ _) (ent_and_right _ _))
          (ent_trans (ent_or_right .zero (.neg .one)) (ent_neg_one .zero))
      have hzs : (cof (cof (cof (cof Φ δ) ψ) (.neg .one)) .one).Scoped Ψ := ⟨⟨hWs, trivial⟩, trivial⟩
      exact VEq.absurd' hW hz (VEq.lty' hW (VEq.restrict' hW hzs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) ea)).ty
        (VEq.lty' hW (VEq.restrict' hW hzs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hfl1)).ty
  have e2 := VEq.splitR' hW (φ := ψ) (ψ := .or (.neg (I.ofDir d)) (I.ofDir d)) H.hψ ⟨hdd, hdd⟩ hor hE
    (VTy.restrict' hW ⟨H.hZs hW, ⟨hdd, hdd⟩⟩ (ent_and_left _ _) hin)
    (VEq.restrict' hW ⟨hWs, ⟨hdd, hdd⟩⟩ (ent_and_left _ _) hov)
  rw [tgBody_dinst]
  exact ⟨VEq.trans' hW e1 e2, hin⟩

theorem hω0 : VEq S Ψ (cof Φ δ) Γ ((tgBody A φ T e ψ u0).dinst .zero)
    (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (A.dinst .one) := by
  obtain ⟨e1, hin⟩ := H.hωend hW false
  have e2 := VEq.splitL' hW (ent_negzero _) hin
  have e3 := VEq.appFst' hW (H.he0Z hW .one trivial)
    (VTy.transpFill' hW H.hKT (H.hTZ hW) H.hψ (H.hconstT hW) (H.hu0T hW)).2.2.1
  exact VEq.trans' hW e1 (VEq.trans' hW e2 e3)

theorem hω1 : VEq S Ψ (cof Φ δ) Γ ((tgBody A φ T e ψ u0).dinst .one) (tgA1' A φ e ψ u0) (A.dinst .one) := by
  obtain ⟨e1, hin⟩ := H.hωend hW true
  have hf1 := (VTy.fill' hW H.hKH H.hKT H.hA H.hψ (H.htube hW) (H.ha0 hW) (H.htube_side hW)).2.2.1
  have e3 := VEq.restrict' hW (H.hZs hW) (H.hZΦ hW) hf1
  have hz : I.Entails (cof (cof (cof Φ δ) (.neg .one)) .one) .zero :=
    ent_trans (ent_trans (ent_and_left _ _) (ent_and_right _ _))
      (ent_trans (ent_or_right .zero (.neg .one)) (ent_neg_one .zero))
  have hzs : (cof (cof (cof Φ δ) (.neg .one)) .one).Scoped Ψ := ⟨⟨H.hZs hW, trivial⟩, trivial⟩
  have hb := VEq.lty' hW e3
  have ha := VTy.appFst' hW (H.he0Z hW .one trivial)
    (VEq.lty' hW (VTy.transpFill' hW H.hKT (H.hTZ hW) H.hψ (H.hconstT hW) (H.hu0T hW)).2.2.1)
  have e2 := VEq.splitR' hW (φ := .neg .one) (ψ := .one) trivial trivial (ent_one _) hin
    (VTy.restrict' hW ⟨H.hZs hW, trivial⟩ (ent_and_left _ _) hb)
    (VEq.absurd' hW hz (VTy.restrict' hW hzs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) ha).ty
      (VTy.restrict' hW hzs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hb).ty)
  exact VEq.trans' hW e1 (VEq.trans' hW e2 e3)

theorem ha1'Z : VTy S Ψ (cof Φ δ) Γ (tgA1' A φ e ψ u0) (A.dinst .one) :=
  VTy.restrict' hW (H.hZs hW) (H.hZΦ hW) (H.ha1' hW)

/-- `ω : Path A(1) (e(1).1 t1') a1'` -/
theorem hω : VTy S Ψ (cof Φ δ) Γ (tgOmega A φ T e ψ u0)
    (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0)) :=
  VTy.plam' hW (VTy.pathC' hW (H.hA1Z hW) (VTy.appFst' hW (H.he0Z hW .one trivial) (H.ht1 hW)) (H.ha1'Z hW))
    (H.hbody hW) (by rw [dshift_dinst]; exact H.hω0 hW) (by rw [dshift_dinst]; exact H.hω1 hW)

/-! #### The fibre -/

theorem hWs : (cof Φ (φ.subst (I.inst0 .one))).Scoped Ψ := ⟨H.hs hW, H.hφr hW (r := .one) trivial⟩

theorem he1 : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (e.dinst .one) (Tm.equiv (T.dinst .one) (A.dinst .one)) :=
  H.her hW (r := .one) trivial (H.hWs hW) (ent_and_left _ _) (ent_and_right _ _)

theorem hfe1 : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (.fst (e.dinst .one))
    (Tm.arrow (T.dinst .one) (A.dinst .one)) :=
  VTy.fst' hW (H.he1 hW)

theorem hfib : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (tgFib A φ T e ψ u0) (.univ l) :=
  VTy.fiber' hW (H.hTr hW (r := .one) trivial (H.hWs hW) (ent_and_left _ _) (ent_and_right _ _))
    (VTy.restrict' hW (H.hWs hW) (ent_and_left _ _) (H.hAr hW (r := .one) trivial)) (H.hfe1 hW)
    (VTy.restrict' hW (H.hWs hW) (ent_and_left _ _) (H.ha1' hW))

theorem hc : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (tgC A φ e ψ u0) (Tm.isContr (tgFib A φ T e ψ u0)) := by
  have h1 := VTy.snd' hW (H.he1 hW)
  rw [isEquiv_inst, isEquiv_eq] at h1
  have := VTy.app' hW h1 (VTy.restrict' hW (H.hWs hW) (ent_and_left _ _) (H.ha1' hW))
  rwa [isContr_fiber_inst] at this

theorem hfc : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (.fst (tgC A φ e ψ u0)) (tgFib A φ T e ψ u0) :=
  VTy.fst' hW (H.hc hW)

theorem hcp {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X (cof Φ (φ.subst (I.inst0 .one)))) {p : Tm}
    (hp : VTy S Ψ X Γ p (tgFib A φ T e ψ u0)) :
    VTy S Ψ X Γ (.app (.snd (tgC A φ e ψ u0)) p) (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) p) := by
  have h1 := VTy.snd' hW (VTy.restrict' hW hXs hX (H.hc hW))
  rw [K_inst] at h1
  have := VTy.app' hW h1 hp
  rwa [pathC_var0_inst] at this

theorem hcpEq {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X (cof Φ (φ.subst (I.inst0 .one)))) {p p' : Tm}
    (hp : VEq S Ψ X Γ p p' (tgFib A φ T e ψ u0)) :
    VEq S Ψ X Γ (.app (.snd (tgC A φ e ψ u0)) p) (.app (.snd (tgC A φ e ψ u0)) p')
      (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) p) := by
  have h1 := VTy.snd' hW (VTy.restrict' hW hXs hX (H.hc hW))
  rw [K_inst] at h1
  have := VEq.app' hW (VEq.refl' h1) hp
  rwa [pathC_var0_inst] at this

theorem hWδs : (cof (cof Φ (φ.subst (I.inst0 .one))) δ).Scoped Ψ := ⟨H.hWs hW, H.hδ⟩
theorem hWψs : (cof (cof Φ (φ.subst (I.inst0 .one))) ψ).Scoped Ψ := ⟨H.hWs hW, H.hψ⟩
theorem hWδZ : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) δ) (cof Φ δ) :=
  ent_and_mono (ent_and_left _ _) (ent_refl _)

theorem hpd : VTy S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) δ) Γ
    (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)) (tgFib A φ T e ψ u0) := by
  have hf := VTy.restrict' hW (H.hWδs hW) (ent_and_left _ _) (H.hfib hW)
  rw [tgFib_eq] at hf ⊢
  exact VTy.pair' hW hf (VTy.restrict' hW (H.hWδs hW) (H.hWδZ hW) (H.ht1 hW))
    (by rw [P_inst]; exact VTy.restrict' hW (H.hWδs hW) (H.hWδZ hW) (H.hω hW))

theorem hGψ1 : VEq S Ψ (cof Φ ψ) Γ ((Tm.glue A φ T e).dinst .one) ((Tm.glue A φ T e).dinst .zero) (.univ l') := by
  have := VEq.dsubst' hW .one trivial H.hconst
  rwa [dshift_dinst] at this

theorem hu0G1 : VTy S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ u0 ((Tm.glue A φ T e).dinst .one) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) (cof Φ ψ) := ent_and_mono (ent_and_left _ _) (ent_refl _)
  exact VTy.conv' hW (VTy.restrict' hW (H.hWψs hW) (ent_trans hX (ent_and_left _ _)) H.hu0)
    (VEq.symm' hW (VEq.restrict' hW (H.hWψs hW) hX (H.hGψ1 hW)))

theorem hu0T1 : VTy S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ u0 (T.dinst .one) := by
  have hG1T1 := VEq.glueFace' hW (ent_trans (ent_and_left _ _) (ent_and_right _ _))
    (VTy.restrict' hW (H.hWψs hW) (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (H.hGr hW (r := .one) trivial))
  exact VTy.conv' hW (H.hu0G1 hW) hG1T1

theorem he1W {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X (cof Φ (φ.subst (I.inst0 .one)))) :
    VTy S Ψ X Γ (e.dinst .one) (Tm.equiv (T.dinst .one) (A.dinst .one)) := VTy.restrict' hW hXs hX (H.he1 hW)

theorem hA1X {X : I} (hXs : X.Scoped Ψ) (hX : I.Entails X Φ) : VTy S Ψ X Γ (A.dinst .one) (.univ l) :=
  VTy.restrict' hW hXs hX (H.hAr hW (r := .one) trivial)

theorem ha1'eq : VEq S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (tgA1' A φ e ψ u0)
    (.app (.fst (e.dinst .one)) u0) (A.dinst .one) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have e1 := VEq.compFace' hW (VTy.restrict' hW (H.hWψs hW) hX (H.ha1' hW)) (ent_and_right _ _)
  rw [tgTube_dinst] at e1
  have hφ1 : (φ.subst (I.inst0 .one)).Scoped Ψ := H.hφr hW (r := .one) trivial
  have hl := VTy.unglue' hW hφ1 (VTy.restrict' hW (H.hWψs hW) hX (H.hGr hW (r := .one) trivial))
    (H.hA1X hW (H.hWψs hW) hX)
    (H.he1W hW ⟨H.hWψs hW, hφ1⟩ (ent_and_intro (ent_trans (ent_and_left _ _) hX) (ent_and_right _ _))) (H.hu0G1 hW)
  have e2 := VEq.unglueFace' hW (ent_trans (ent_and_left _ _) (ent_and_right _ _)) hl (H.hu0G1 hW)
    (H.hA1X hW (H.hWψs hW) hX) (H.he1W hW (H.hWψs hW) (ent_and_left _ _))
  exact VEq.trans' hW e1 e2

theorem hpl : VTy S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (.plam (tgA1' A φ e ψ u0).dshift)
    (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) u0) (tgA1' A φ e ψ u0)) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  exact VTy.plamConst' hW (H.hA1X hW (H.hWψs hW) hX)
    (VTy.appFst' hW (H.he1W hW (H.hWψs hW) (ent_and_left _ _)) (H.hu0T1 hW))
    (VTy.restrict' hW (H.hWψs hW) hX (H.ha1' hW)) (H.ha1'eq hW)

theorem hpψ : VTy S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ
    (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift)) (tgFib A φ T e ψ u0) := by
  have hf := VTy.restrict' hW (H.hWψs hW) (ent_and_left _ _) (H.hfib hW)
  rw [tgFib_eq] at hf ⊢
  exact VTy.pair' hW hf (H.hu0T1 hW) (by rw [P_inst]; exact H.hpl hW)

theorem hpEq : VEq S Ψ (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) Γ
    (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)) (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift))
    (tgFib A φ T e ψ u0) := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hVs : (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).Scoped Ψ := ⟨H.hWδs hW, H.hψ⟩
  have hVW : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) (cof Φ (φ.subst (I.inst0 .one))) :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hVWψ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) :=
    ent_and_mono (ent_and_left _ _) (ent_refl _)
  have hVZ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) (cof Φ δ) :=
    ent_trans (ent_and_left _ _) (H.hWδZ hW)
  have hVΦ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) Φ := ent_trans hVW (ent_and_left _ _)
  have ht1V : VTy S Ψ (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) Γ (.transp T ψ u0) (T.dinst .one) :=
    VTy.restrict' hW hVs hVZ (H.ht1 hW)
  have et := VEq.transpFace' hW (ent_and_right _ _) ht1V
  have he1V := H.he1W hW hVs hVW
  have hA1V := H.hA1X hW hVs hVΦ
  have ha1V := VTy.restrict' hW hVs hVΦ (H.ha1' hW)
  have ea := VEq.trans' hW (VEq.restrict' hW hVs hVWψ (H.ha1'eq hW)) (VEq.appFst' hW he1V (VEq.symm' hW et))
  have hpl' := VTy.plamConst' hW hA1V (VTy.appFst' hW he1V ht1V) ha1V ea
  have hωV := VTy.restrict' hW hVs hVZ (H.hω hW)
  -- the bodies
  have hVs1 := KubusCore.I.scoped_shift hVs
  have hbV := VTy.restrict' hW hVs1 (ent_shift hVZ) (H.hbody hW)
  have hVχ : I.Entails (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).shift (tgChi ψ) :=
    ent_trans (ent_shift (ent_and_right _ _)) (ent_or_left _ _)
  have e1 := VEq.compFace' hW hbV hVχ
  have hs1 := VTy.dsubst' hW (Φ := cof (cof Φ δ).shift (tgChi ψ)) (Γ := Γ.dshift) .one trivial (H.hsys hW)
  rw [L_C1] at hs1
  have hs1V := VTy.restrict' hW hVs1 (ent_and_intro (ent_shift hVZ) hVχ) hs1
  simp only [tgSys] at e1 hs1V
  rw [sys_d _ _ _ _ _ _ (.inr rfl)] at e1 hs1V
  have e2 := VEq.splitL' hW (ent_shift (ent_and_right _ _)) hs1V
  have e3 := VEq.dwk' hW (VEq.symm' hW (VEq.restrict' hW hVs hVWψ (H.ha1'eq hW)))
  have eb : VEq S (Ψ + 1) (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).shift Γ.dshift
      (tgBody A φ T e ψ u0) (tgA1' A φ e ψ u0).dshift (A.dinst .one).dshift :=
    VEq.trans' hW e1 (VEq.trans' hW e2 e3)
  have eω := VEq.plam' hW (VTy.pathC' hW hA1V (VTy.appFst' hW he1V ht1V) ha1V) hωV hpl'.ty eb
  have hf := VTy.restrict' hW hVs (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (H.hfib hW)
  rw [tgFib_eq] at hf ⊢
  exact VEq.pair' hW hf et (by rw [P_inst]; exact eω)

theorem hPd : VTy S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) δ) Γ (tgPd A φ T e ψ u0)
    (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))) :=
  H.hcp hW (H.hWδs hW) (ent_and_left _ _) (H.hpd hW)

theorem hPψ : VTy S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (tgPpsi A φ e ψ u0)
    (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift))) :=
  H.hcp hW (H.hWψs hW) (ent_and_left _ _) (H.hpψ hW)

theorem hPEq : VEq S Ψ (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ) Γ (tgPd A φ T e ψ u0) (tgPpsi A φ e ψ u0)
    (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))) :=
  H.hcpEq hW (show (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).Scoped Ψ from ⟨H.hWδs hW, H.hψ⟩)
    (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (H.hpEq hW)

theorem hpsys : VTy S (Ψ + 1) (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift Γ.dshift
    (.split δ.shift (.papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift (.papp (tgPpsi A φ e ψ u0).dshift (.var 0)))
    (tgFib A φ T e ψ u0).dshift := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hΞs : (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift.Scoped (Ψ + 1) :=
    KubusCore.I.scoped_shift ⟨H.hWs hW, ⟨H.hδ, H.hψ⟩⟩
  have hΞW : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift (cof Φ (φ.subst (I.inst0 .one))).shift :=
    ent_shift (ent_and_left _ _)
  have hΞχ : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift (.or δ.shift ψ.shift) :=
    ent_shift (ent_and_right _ (.or δ ψ))
  have hd := VTy.dwk' hW (H.hPd hW)
  have hp := VTy.dwk' hW (H.hPψ hW)
  have he := VEq.dwk' hW (H.hPEq hW)
  rw [pathC_dshift] at hd hp he
  have hfibD := VTy.dwk' hW (H.hfib hW)
  generalize (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).shift = Ξ at hΞs hΞW hΞχ ⊢
  have hδ1 : δ.shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift H.hδ
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift H.hψ
  have hX1s : (cof Ξ δ.shift).Scoped (Ψ + 1) := ⟨hΞs, hδ1⟩
  have hX2s : (cof Ξ ψ.shift).Scoped (Ψ + 1) := ⟨hΞs, hψ1⟩
  have hX3s : (cof (cof Ξ δ.shift) ψ.shift).Scoped (Ψ + 1) := ⟨hX1s, hψ1⟩
  have hX1 : I.Entails (cof Ξ δ.shift) (cof (cof Φ (φ.subst (I.inst0 .one))) δ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hΞW (ent_refl _)
  have hX2 : I.Entails (cof Ξ ψ.shift) (cof (cof Φ (φ.subst (I.inst0 .one))) ψ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hΞW (ent_refl _)
  have hX3 : I.Entails (cof (cof Ξ δ.shift) ψ.shift) (cof (cof (cof Φ (φ.subst (I.inst0 .one))) δ) ψ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hX1 (ent_refl _)
  have hb1 := VTy.pappC' hW (VTy.restrict' hW hX1s hX1 hd) hv0
  have hb2 := VTy.pappC' hW (VTy.restrict' hW hX2s hX2 hp) hv0
  have ho := VEq.papp' hW (VEq.restrict' hW hX3s hX3 he) hv0 hv0 (I_eq_refl _)
  rw [dshift_dinst] at ho
  exact VTy.split' hW hδ1 hψ1 hΞχ (VTy.restrict' hW hΞs hΞW hfibD).ty hb1 hb2 ho

theorem hext : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (tgExt A φ T e ψ u0 δ) (tgFib A φ T e ψ u0) := by
  have hΞs : (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)).Scoped Ψ := ⟨H.hWs hW, ⟨H.hδ, H.hψ⟩⟩
  have hs0 := VTy.dsubst' hW (Φ := cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) .zero trivial (H.hpsys hW)
  rw [dshift_dinst, psys_dinst] at hs0
  have hside : VEq S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) Γ
      ((Tm.split δ.shift (.papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift
        (.papp (tgPpsi A φ e ψ u0).dshift (.var 0))).dinst .zero) (.fst (tgC A φ e ψ u0)) (tgFib A φ T e ψ u0) := by
    rw [psys_dinst]
    have hfcΞ := VTy.restrict' hW hΞs (ent_and_left _ _) (H.hfc hW)
    have hX1 : (cof (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) δ).Scoped Ψ := ⟨hΞs, H.hδ⟩
    have hX2 : (cof (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) ψ).Scoped Ψ := ⟨hΞs, H.hψ⟩
    have hPd1 := VTy.restrict' hW hX1 (ent_and_mono (ent_and_left _ _) (ent_refl _)) (H.hPd hW)
    have hPψ1 := VTy.restrict' hW hX2 (ent_and_mono (ent_and_left _ _) (ent_refl _)) (H.hPψ hW)
    have hX3 : (cof (cof (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) δ) ψ).Scoped Ψ := ⟨hX1, H.hψ⟩
    have hov : VEq S Ψ (cof (cof (cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) δ) ψ) Γ
        (.papp (tgPd A φ T e ψ u0) .zero) (.papp (tgPpsi A φ e ψ u0) .zero) (tgFib A φ T e ψ u0) := by
      have := VEq.papp' hW (VEq.restrict' hW hX3 (ent_and_mono (ent_and_mono (ent_and_left _ _) (ent_refl _))
        (ent_refl _)) (H.hPEq hW)) (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _)
      rwa [dshift_dinst] at this
    refine VEq.local' hW (φ := δ) (ψ := ψ) H.hδ H.hψ (ent_and_right _ _) hs0 hfcΞ ?_ ?_
    · refine VEq.trans' hW (VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hX1 (ent_and_left _ _) hs0)) ?_
      exact VEq.pathCZero' hW hPd1
    · refine VEq.trans' hW (VEq.splitR' hW H.hδ H.hψ (ent_and_right _ _)
        (VTy.restrict' hW hX2 (ent_and_left _ _) hs0) (VTy.restrict' hW ⟨hX2, H.hψ⟩ (ent_and_left _ _)
          (VTy.pappC' hW hPψ1 trivial)) (VEq.restrict' hW ⟨⟨hX2, H.hδ⟩, H.hψ⟩
            (ent_and_intro (ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) (ent_and_left _ _)))
              (ent_trans (ent_and_left _ _) (ent_and_right _ _))) (ent_and_right _ _)) hov)) ?_
      exact VEq.pathCZero' hW hPψ1
  rw [tgExt_eq]
  exact VTy.hcompG hW H.hKH (H.hfib hW) ⟨H.hδ, H.hψ⟩ (H.hpsys hW) (H.hfc hW) hside

theorem hextψ : VEq S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (tgExt A φ T e ψ u0 δ)
    (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift)) (tgFib A φ T e ψ u0) := by
  have hX := VTy.restrict' hW (H.hWψs hW) (ent_and_left _ _) (H.hext hW)
  rw [tgExt_eq] at hX ⊢
  have e1 := VEq.hcompFace' hW (ent_trans (ent_and_right _ _) (ent_or_right _ _)) hX
  have hs1 := VTy.dsubst' hW (Φ := cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) .one trivial (H.hpsys hW)
  rw [dshift_dinst] at hs1
  have hs1' := VTy.restrict' hW (H.hWψs hW)
    (ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) (ent_or_right _ _))) hs1
  rw [psys_dinst] at e1 hs1'
  have hWψδ : (cof (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) δ).Scoped Ψ := ⟨H.hWψs hW, H.hδ⟩
  have hov := VEq.papp' hW (VEq.restrict' hW (Φ' := cof (cof (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) δ) ψ)
    ⟨hWψδ, H.hψ⟩ (ent_and_intro (ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _)
      (ent_and_left _ _))) (ent_trans (ent_and_left _ _) (ent_and_right _ _))) (ent_and_right _ _)) (H.hPEq hW))
    (r := .one) (r' := .one) trivial trivial (I_eq_refl _)
  rw [dshift_dinst] at hov
  have e2 := VEq.splitR' hW H.hδ H.hψ (ent_and_right _ _) hs1'
    (VTy.restrict' hW ⟨H.hWψs hW, H.hψ⟩ (ent_and_left _ _) (VTy.pappC' hW (H.hPψ hW) trivial)) hov
  exact VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.pathCOne' hW (H.hPψ hW)))

theorem hfext : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (.fst (tgExt A φ T e ψ u0 δ)) (T.dinst .one) := by
  have := H.hext hW; rw [tgFib_eq] at this; exact VTy.fst' hW this

theorem hsext : VTy S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ (.snd (tgExt A φ T e ψ u0 δ))
    (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (.fst (tgExt A φ T e ψ u0 δ))) (tgA1' A φ e ψ u0)) := by
  have := H.hext hW; rw [tgFib_eq] at this
  have h := VTy.snd' hW this; rwa [P_inst] at h

theorem hsextψ : VEq S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ (.snd (tgExt A φ T e ψ u0 δ))
    (.plam (tgA1' A φ e ψ u0).dshift)
    (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (.fst (tgExt A φ T e ψ u0 δ))) (tgA1' A φ e ψ u0)) := by
  have hX : I.Entails (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have he := H.hextψ hW
  have hp := H.hpψ hW
  rw [tgFib_eq] at he hp
  have e1 := VEq.snd' hW he
  rw [P_inst] at e1
  have hsp := VTy.snd' hW hp
  rw [P_inst] at hsp
  have e2 := VEq.sndBeta' hW hsp
  have hfe := VEq.fst' hW he
  have hA1 := H.hA1X hW (H.hWψs hW) hX
  have ha1 := VTy.restrict' hW (H.hWψs hW) hX (H.ha1' hW)
  have he1 := H.he1W hW (H.hWψs hW) (ent_and_left _ _)
  have eP : VEq S Ψ (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) Γ
      (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (.fst (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift))))
        (tgA1' A φ e ψ u0))
      (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (.fst (tgExt A φ T e ψ u0 δ))) (tgA1' A φ e ψ u0))
      (.univ l) :=
    VEq.pathCong' hW (VEq.refl' (VTy.dwk' hW hA1))
      (by rw [dshift_dinst]; exact VEq.appFst' hW he1 (VEq.symm' hW hfe))
      (by rw [dshift_dinst]; exact VEq.refl' ha1)
  exact VEq.trans' hW e1 (VEq.conv' hW e2 eP)

theorem hasys : VTy S (Ψ + 1) (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift Γ.dshift
    (.split (φ.subst (I.inst0 .one)).shift (.papp (Tm.snd (tgExt A φ T e ψ u0 δ)).dshift (.neg (.var 0)))
      ψ.shift (tgA1' A φ e ψ u0).dshift) (A.dinst .one).dshift := by
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hφ1 : (φ.subst (I.inst0 .one)).Scoped Ψ := H.hφr hW (r := .one) trivial
  have hΞs : (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift.Scoped (Ψ + 1) :=
    KubusCore.I.scoped_shift ⟨H.hs hW, ⟨hφ1, H.hψ⟩⟩
  have hΞΦ : I.Entails (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hΞχ : I.Entails (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift
      (.or (φ.subst (I.inst0 .one)).shift ψ.shift) := ent_shift (ent_and_right _ (.or _ ψ))
  have hd := VTy.dwk' hW (H.hsext hW)
  rw [pathC_dshift] at hd
  have he := VEq.dwk' hW (H.hsextψ hW)
  rw [pathC_dshift, plam_dshift_dshift] at he
  have hpl := VTy.dwk' hW (H.hpl hW)
  rw [pathC_dshift, plam_dshift_dshift] at hpl
  have hA1 := VTy.dwk' hW (H.hAr hW (r := .one) trivial)
  have ha1 := VTy.dwk' hW (H.ha1' hW)
  generalize (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).shift = Ξ at hΞs hΞΦ hΞχ ⊢
  have hφ1s : (φ.subst (I.inst0 .one)).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hφ1
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift H.hψ
  have hX1s : (cof Ξ (φ.subst (I.inst0 .one)).shift).Scoped (Ψ + 1) := ⟨hΞs, hφ1s⟩
  have hX2s : (cof Ξ ψ.shift).Scoped (Ψ + 1) := ⟨hΞs, hψ1⟩
  have hX3s : (cof (cof Ξ (φ.subst (I.inst0 .one)).shift) ψ.shift).Scoped (Ψ + 1) := ⟨hX1s, hψ1⟩
  have hX1 : I.Entails (cof Ξ (φ.subst (I.inst0 .one)).shift) (cof Φ (φ.subst (I.inst0 .one))).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hΞΦ (ent_refl _)
  have hX3 : I.Entails (cof (cof Ξ (φ.subst (I.inst0 .one)).shift) ψ.shift)
      (cof (cof Φ (φ.subst (I.inst0 .one))) ψ).shift :=
    show I.Entails _ (.and _ _) from ent_and_mono hX1 (ent_refl _)
  have hneg : (I.neg (.var 0)).Scoped (Ψ + 1) := hv0
  have hb1 := VTy.pappC' hW (VTy.restrict' hW hX1s hX1 hd) hneg
  have hb2 := VTy.restrict' hW hX2s (ent_trans (ent_and_left _ _) hΞΦ) ha1
  have e1 := VEq.papp' hW (VEq.restrict' hW hX3s hX3 he) hneg hneg (I_eq_refl _)
  rw [dshift_dinst] at e1
  have hpp := VTy.pappC' hW (VTy.restrict' hW hX3s hX3 hpl) hneg
  have e2 := VEq.pathBeta' hW hpp
  rw [dshift_dinst] at e2
  exact VTy.split' hW hφ1s hψ1 hΞχ (VTy.restrict' hW hΞs hΞΦ hA1).ty hb1 hb2 (VEq.trans' hW e1 e2)

theorem ha1 : VTy S Ψ Φ Γ (tgA1 A φ T e ψ u0 δ) (A.dinst .one) := by
  have hφ1 : (φ.subst (I.inst0 .one)).Scoped Ψ := H.hφr hW (r := .one) trivial
  have hΞs : (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)).Scoped Ψ := ⟨H.hs hW, ⟨hφ1, H.hψ⟩⟩
  have hs0 := VTy.dsubst' hW (Φ := cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) .zero trivial (H.hasys hW)
  rw [dshift_dinst, asys_dinst] at hs0
  have hX : (cof (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) (φ.subst (I.inst0 .one))).Scoped Ψ := ⟨hΞs, hφ1⟩
  have hsx := VTy.restrict' hW hX (ent_and_mono (ent_and_left _ _) (ent_refl _)) (H.hsext hW)
  have hb1eq : VEq S Ψ (cof (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) (φ.subst (I.inst0 .one))) Γ
      (.papp (.snd (tgExt A φ T e ψ u0 δ)) (.neg .zero)) (tgA1' A φ e ψ u0) (A.dinst .one) :=
    VEq.trans' hW (VEq.pappC' hW hsx (r := .neg .zero) (r' := .one) trivial trivial I_eq_neg_zero)
      (VEq.pathCOne' hW hsx)
  have hside : VEq S Ψ (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) Γ
      ((Tm.split (φ.subst (I.inst0 .one)).shift (.papp (Tm.snd (tgExt A φ T e ψ u0 δ)).dshift (.neg (.var 0)))
        ψ.shift (tgA1' A φ e ψ u0).dshift).dinst .zero) (tgA1' A φ e ψ u0) (A.dinst .one) := by
    rw [asys_dinst]
    refine VEq.local' hW (φ := φ.subst (I.inst0 .one)) (ψ := ψ) hφ1 H.hψ (ent_and_right _ _) hs0
      (VTy.restrict' hW hΞs (ent_and_left _ _) (H.ha1' hW)) ?_ ?_
    · exact VEq.trans' hW (VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hX (ent_and_left _ _) hs0)) hb1eq
    · have hY : (cof (cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) ψ).Scoped Ψ := ⟨hΞs, H.hψ⟩
      exact VEq.splitR' hW hφ1 H.hψ (ent_and_right _ _) (VTy.restrict' hW hY (ent_and_left _ _) hs0)
        (VTy.restrict' hW ⟨hY, H.hψ⟩ (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) (ent_and_left _ _)))
          (H.ha1' hW))
        (VEq.restrict' hW ⟨⟨hY, hφ1⟩, H.hψ⟩ (ent_trans (ent_and_left _ _)
          (ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _))) hb1eq)
  rw [tgA1_eq]
  exact VTy.hcompG hW H.hKH (H.hAr hW (r := .one) trivial) ⟨hφ1, H.hψ⟩ (H.hasys hW) (H.ha1' hW) hside

theorem hglueSide : VEq S Ψ (cof Φ (φ.subst (I.inst0 .one))) Γ
    (.app (.fst (e.dinst .one)) (.fst (tgExt A φ T e ψ u0 δ))) (tgA1 A φ T e ψ u0 δ) (A.dinst .one) := by
  have hW1 := VTy.restrict' hW (H.hWs hW) (ent_and_left _ _) (H.ha1 hW)
  rw [tgA1_eq] at hW1 ⊢
  have hWχ : I.Entails (cof Φ (φ.subst (I.inst0 .one))) (.or (φ.subst (I.inst0 .one)) ψ) :=
    ent_trans (ent_and_right _ _) (ent_or_left _ _)
  have e1 := VEq.hcompFace' hW hWχ hW1
  have hs1 := VTy.dsubst' hW (Φ := cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) .one trivial (H.hasys hW)
  rw [dshift_dinst] at hs1
  have hs1' := VTy.restrict' hW (H.hWs hW) (ent_and_intro (ent_and_left _ _) hWχ) hs1
  rw [asys_dinst] at e1 hs1'
  have e2 := VEq.splitL' hW (ent_and_right _ _) hs1'
  have e3 := VEq.pappC' hW (H.hsext hW) (r := .neg .one) (r' := .zero) trivial trivial I_eq_neg_one
  exact VEq.symm' hW (VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.trans' hW e3 (VEq.pathCZero' hW (H.hsext hW)))))

/-- The contractum is typed (and valid) at the end of the line. -/
theorem typed : VTy S Ψ Φ Γ (Tm.transpGlueWith δ A φ T e ψ u0) ((Tm.glue A φ T e).dinst .one) := by
  rw [transpGlueWith_eq, glue_dinst]
  exact VTy.glueEl' hW (H.hφr hW (r := .one) trivial) (H.hGr hW (r := .one) trivial) (H.he1 hW) (H.hfext hW)
    (H.ha1 hW) (H.hglueSide hW)

/-! #### The contractum where the faces hold -/

/-- Where `ψ` holds, the contractum is `u0` (Glue η and the faces of its components). -/
theorem faceψ : VEq S Ψ (cof Φ ψ) Γ u0 (Tm.transpGlueWith δ A φ T e ψ u0) ((Tm.glue A φ T e).dinst .one) := by
  have hZs : (cof Φ ψ).Scoped Ψ := ⟨H.hs hW, H.hψ⟩
  have hφ1 : (φ.subst (I.inst0 .one)).Scoped Ψ := H.hφr hW (r := .one) trivial
  have hu0G : VTy S Ψ (cof Φ ψ) Γ u0 (.glue (A.dinst .one) (φ.subst (I.inst0 .one)) (T.dinst .one) (e.dinst .one)) :=
    VTy.conv' hW (VTy.restrict' hW hZs (ent_and_left _ _) H.hu0) (VEq.symm' hW (H.hGψ1 hW))
  have hG1Z := VTy.restrict' hW hZs (ent_and_left _ _) (H.hGr hW (r := .one) trivial)
  have hFs : (cof (cof Φ ψ) (φ.subst (I.inst0 .one))).Scoped Ψ := ⟨hZs, hφ1⟩
  have hFW : I.Entails (cof (cof Φ ψ) (φ.subst (I.inst0 .one))) (cof Φ (φ.subst (I.inst0 .one))) :=
    ent_and_mono (ent_and_left _ _) (ent_refl _)
  have he1Z := H.he1W hW hFs hFW
  have hη := VEq.glueEta' hW hφ1 hG1Z he1Z hu0G
  -- the fibre component
  have hFψ : I.Entails (cof (cof Φ ψ) (φ.subst (I.inst0 .one))) (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) :=
    ent_and_intro hFW (ent_trans (ent_and_left _ _) (ent_and_right _ _))
  have hextψ := VEq.restrict' hW hFs hFψ (H.hextψ hW)
  rw [tgFib_eq] at hextψ
  have hfe := VEq.fst' hW hextψ
  have hfb := VEq.fstBeta' hW (VEq.rty' hW hfe)
  have ht := VEq.symm' hW (VEq.trans' hW hfe hfb)
  -- the base component
  have hcU := VEq.compFace' hW (VTy.restrict' hW hZs (ent_and_left _ _) (H.ha1' hW)) (ent_and_right _ _)
  rw [tgTube_dinst] at hcU
  have ha1Z := VTy.restrict' hW hZs (ent_and_left _ _) (H.ha1 hW)
  rw [tgA1_eq] at ha1Z
  have hZχ : I.Entails (cof Φ ψ) (.or (φ.subst (I.inst0 .one)) ψ) := ent_trans (ent_and_right _ _) (ent_or_right _ _)
  have b1 := VEq.hcompFace' hW hZχ ha1Z
  rw [asys_dinst] at b1
  have hs1 := VTy.dsubst' hW (Φ := cof Φ (.or (φ.subst (I.inst0 .one)) ψ)) .one trivial (H.hasys hW)
  rw [dshift_dinst] at hs1
  have hs1Z := VTy.restrict' hW hZs (ent_and_intro (ent_and_left _ _) hZχ) hs1
  rw [asys_dinst] at hs1Z
  have hWs : (cof (cof (cof Φ ψ) (φ.subst (I.inst0 .one))) ψ).Scoped Ψ := ⟨hFs, H.hψ⟩
  have hWe : I.Entails (cof (cof (cof Φ ψ) (φ.subst (I.inst0 .one))) ψ) (cof (cof Φ (φ.subst (I.inst0 .one))) ψ) :=
    ent_trans (ent_and_left _ _) hFψ
  have hsx := VEq.papp' hW (VEq.restrict' hW hWs hWe (H.hsextψ hW)) (r := .neg .one) (r' := .neg .one) trivial trivial
    (I_eq_refl _)
  rw [dshift_dinst] at hsx
  have hpb := VEq.pathBeta' hW (VEq.rty' hW hsx)
  rw [dshift_dinst] at hpb
  have b2 := VEq.splitR' hW hφ1 H.hψ (ent_and_right _ _) hs1Z
    (VTy.restrict' hW ⟨hZs, H.hψ⟩ (ent_and_left _ _) (VTy.restrict' hW hZs (ent_and_left _ _) (H.ha1' hW)))
    (VEq.trans' hW hsx hpb)
  have ha := VEq.symm' hW (VEq.trans' hW b1 (VEq.trans' hW b2 hcU))
  have hy := VTy.restrict' hW hZs (ent_and_left _ _) (H.typed hW)
  rw [transpGlueWith_eq, glue_dinst] at hy ⊢
  have hcong := VEq.glueEl' hW hφ1 hG1Z he1Z (VEq.rty' hW hη) hy ht ha
  exact VEq.trans' hW hη hcong

/-- Where `δ` holds, the contractum is the transport in `T`. -/
theorem faceδ : VEq S Ψ (cof Φ δ) Γ (tgT1 T ψ u0) (Tm.transpGlueWith δ A φ T e ψ u0) ((Tm.glue A φ T e).dinst .one) := by
  have hφ1 : (φ.subst (I.inst0 .one)).Scoped Ψ := H.hφr hW (r := .one) trivial
  have hDφ1 : I.Entails (cof Φ δ) (φ.subst (I.inst0 .one)) := H.hZφr hW .one
  have hDW : I.Entails (cof Φ δ) (cof Φ (φ.subst (I.inst0 .one))) := ent_and_intro (ent_and_left _ _) hDφ1
  have hy := VTy.restrict' hW (H.hZs hW) (ent_and_left _ _) (H.typed hW)
  rw [transpGlueWith_eq, glue_dinst] at hy
  have g1 := VEq.glueElFace' hW hDφ1 hy
  have hextD := VTy.restrict' hW (H.hZs hW) hDW (H.hext hW)
  rw [tgExt_eq] at hextD
  have hDχ : I.Entails (cof Φ δ) (.or δ ψ) := ent_trans (ent_and_right _ _) (ent_or_left _ _)
  have f1 := VEq.hcompFace' hW hDχ hextD
  rw [psys_dinst] at f1
  have hs1 := VTy.dsubst' hW (Φ := cof (cof Φ (φ.subst (I.inst0 .one))) (.or δ ψ)) .one trivial (H.hpsys hW)
  rw [dshift_dinst] at hs1
  have hs1D := VTy.restrict' hW (H.hZs hW) (ent_and_intro hDW hDχ) hs1
  rw [psys_dinst] at hs1D
  have f2 := VEq.splitL' hW (ent_and_right _ _) hs1D
  have f3 := VEq.pathCOne' hW (VTy.restrict' hW (H.hZs hW) (ent_and_intro hDW (ent_and_right _ _)) (H.hPd hW))
  have f123 := VEq.trans' hW f1 (VEq.trans' hW f2 f3)
  rw [tgFib_eq] at f123
  have hfe := VEq.fst' hW f123
  have hfb := VEq.fstBeta' hW (VEq.rty' hW hfe)
  have hG1 := VEq.glueFace' hW hDφ1 (VTy.restrict' hW (H.hZs hW) (ent_and_left _ _) (H.hGr hW (r := .one) trivial))
  have hfst := VEq.conv' hW (VEq.trans' hW hfe hfb) (VEq.symm' hW hG1)
  rw [transpGlueWith_eq, glue_dinst]
  exact VEq.symm' hW (VEq.trans' hW g1 hfst)

end VTG

end

end Model.Whnf
