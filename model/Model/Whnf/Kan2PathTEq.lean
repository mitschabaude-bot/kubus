import Model.Whnf.Kan2PathEq

/-!
# Judgmental equality of the systems of transports in path types
-/

set_option autoImplicit false

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem transpPath_sys (hS : SigClosed S) {Ψ Φ Γ A a b φ p0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (path A a b) φ p0) T) :
    HasTy0 S (Ψ + 1 + 1) (cof Φ.shift (.or φ.shift (.or (.neg (.var 0)) (.var 0)))).shift Γ.dshift.dshift
      (split φ.shift.shift (papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))) (A.dsubst swapI) := by
  obtain ⟨l, ⟨hL, hφ, hc, hu0⟩, ch⟩ := gen_transpF h rfl
  have hs := scoped_of_ty h
  have hw0 := wf_of_ty h
  have hAl := HasTy0.pathLine hS hL
  have ha := HasTy0.pathLeft hS hL
  have hb := HasTy0.pathRight hS hL
  have hCc := HasTy0.swap hS hAl
  rw [univ_dsubst] at hCc
  -- constancy of the swapped line on `φ`
  have hcd := EqTm0.dwk hS hc
  have hci := EqTm0.pathInjLine (A := A.ren id (upRen Nat.succ))
    (A' := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ)).ren id (upRen Nat.succ))
    (r := .var 0) hcd (show 0 < Ψ + 1 + 1 by omega)
  rw [ipi_c1, ipi_c2] at hci
  have hcC := EqTm0.swap hS (Φ := cof Φ φ) hci
  rw [ipi_c3, univ_dsubst] at hcC
  -- the endpoints are constant on `φ`
  have hcl := EqTm0.pathInjLeft hc
  have hcr := EqTm0.pathInjRight hc
  -- contexts
  let ψ : I := .or φ.shift (.or (.neg (.var 0)) (.var 0))
  have hv0' : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hψs : ψ.Scoped (Ψ + 1) := ⟨scoped_shift hφ, ⟨hv0', hv0'⟩⟩
  have hΞs : (cof Φ.shift ψ).Scoped (Ψ + 1) := ⟨scoped_shift hs, hψs⟩
  have hR2s : (cof Φ.shift ψ).shift.Scoped (Ψ + 1 + 1) := scoped_shift hΞs
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hφ)
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  let ψ2 : I := .or (.neg (.var 1)) (.var 1)
  have hψ2s : ψ2.Scoped (Ψ + 1 + 1) := ⟨hv1, hv1⟩
  have hR2Φ : I.Entails (cof Φ.shift ψ).shift Φ.shift.shift := ent_shift (ent_and_left Φ.shift ψ)
  have hCc2 := HasTy0.restrict hR2s hR2Φ hCc
  -- the tube on `φ`: `p0 j`
  have hp0dd := HasTy0.dwk hS (HasTy0.dwk hS hu0)
  have hP := HasTy0.papp (A := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ)).ren id
    (upRen Nat.succ)) hp0dd hv1
  rw [tp_P] at hP
  have hR3 : (cof (cof Φ.shift ψ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hR2s, hφ2⟩
  have hR3e : I.Entails (cof (cof Φ.shift ψ).shift φ.shift.shift) (cof Φ φ).shift.shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) hR2Φ) (ent_and_right _ _)
  have hPr : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift ψ).shift φ.shift.shift) Γ.dshift.dshift
      (papp p0.dshift.dshift (.var 1)) (A.dsubst swapI) :=
    HasTy0.conv (HasTy0.restrict hR3 (ent_trans (ent_and_left _ _) hR2Φ) hP)
      (EqTm0.symm (EqTm0.restrict hR3 hR3e hcC))
  -- the inner system `[j = 0 ↦ a, j = 1 ↦ b]`
  have hΞ2s : (cof (cof Φ.shift ψ).shift ψ2).Scoped (Ψ + 1 + 1) := ⟨hR2s, hψ2s⟩
  have hXa : (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXb : (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXaΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hXbΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have haI : HasTy0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) Γ.dshift.dshift
      (a.dsubst insI) (A.dsubst swapI) := by
    have h1 := HasTy0.restrict hXa (ent_trans hXaΦ hR2Φ) (HasTy0.insI' hS ha)
    rw [tp_end0] at h1
    have hf := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _) (HasTy0.restrict hXa hXaΦ hCc2)
    exact HasTy0.conv h1 (EqTm0.symm hf)
  have hbI : HasTy0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) Γ.dshift.dshift
      (b.dsubst insI) (A.dsubst swapI) := by
    have h1 := HasTy0.restrict hXb (ent_trans hXbΦ hR2Φ) (HasTy0.insI' hS hb)
    rw [tp_end1] at h1
    have hf := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _) (HasTy0.restrict hXb hXbΦ hCc2)
    exact HasTy0.conv h1 (EqTm0.symm hf)
  have hXab : (cof (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (.var 1)).Scoped (Ψ + 1 + 1) :=
    ⟨hXa, hv1⟩
  have hinner : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift ψ).shift ψ2) Γ.dshift.dshift
      (split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI)) (A.dsubst swapI) :=
    HasTy0.split hv1 hv1 (ent_and_right _ _) (HasTy0.restrict hΞ2s (ent_and_left _ _) hCc2) haI hbI
      (EqTm0.absurd (ent_contra _ 1) (HasTy0.restrict hXab (ent_and_left _ _) haI)
        (HasTy0.restrict hXab (ent_and_mono (ent_and_left _ _) (ent_refl _)) hbI))
  -- agreement of the tube with the inner system
  have hC0d : HasTy0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift ((A.dsubst swapI).dinst .zero).dshift (univ l) :=
    HasTy0.dwk hS (HasTy0.dsubst hS hCc (r := .zero) trivial)
  have hcl' := EqTm0.insI' hS (EqTm0.pathInjLeft (a' := (a.dinst .zero).dshift) hc)
  rw [tp_a0, tp_end0] at hcl'
  have hcr' := EqTm0.insI' hS (EqTm0.pathInjRight (b' := (b.dinst .zero).dshift) hc)
  rw [tp_a0, tp_end1] at hcr'
  have hY : (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2).Scoped (Ψ + 1 + 1) := ⟨hR3, hψ2s⟩
  have hover : EqTm0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) Γ.dshift.dshift
      (papp p0.dshift.dshift (.var 1)) (split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))
      (A.dsubst swapI) := by
    have hYU := HasTy0.restrict hY (ent_and_left _ _) hPr
    have hYI := HasTy0.restrict hY (ent_and_mono (ent_and_left _ _) (ent_refl _)) hinner
    have hYΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) Φ.shift.shift :=
      ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hR2Φ)
    have hYc : I.Entails (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (cof Φ φ).shift.shift :=
      ent_trans (ent_and_left _ _) hR3e
    refine EqTm0.local (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _) hYU hYI ?_ ?_
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have hW := ent_and_left (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))
      have hWA := HasTy0.restrict hs1 (ent_trans hW hYΦ) hCc
      have e1 := EqTm0.face (i := 1) (d := false) hv1 (ent_and_right _ _) hWA (HasTy0.restrict hs1 hW hYU)
      rw [tp_Pdset] at e1
      have e2 := EqTm0.pathZero (HasTy0.restrict hs1 (ent_trans hW hYΦ) hp0dd)
      have hz := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _) (HasTy0.restrict hs1 (ent_trans hW hYΦ) hC0d)
      rw [tp_Z] at hz
      have eT := EqTm0.trans (EqTm0.restrict hs1 (ent_trans hW hYc) hcC) hz
      have hf := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _) hWA
      have e3 := EqTm0.conv (EqTm0.restrict hs1 (ent_trans hW hYc) hcl') (EqTm0.symm hf)
      have e4 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs1 hW hYI)
      exact EqTm0.trans e1 (EqTm0.trans (EqTm0.conv e2 (EqTm0.symm eT))
        (EqTm0.trans (EqTm0.symm e3) (EqTm0.symm e4)))
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have hW := ent_and_left (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)
      have hWA := HasTy0.restrict hs1 (ent_trans hW hYΦ) hCc
      have e1 := EqTm0.face (i := 1) (d := true) hv1 (ent_and_right _ _) hWA (HasTy0.restrict hs1 hW hYU)
      rw [tp_Pdset] at e1
      have e2 := EqTm0.pathOne (HasTy0.restrict hs1 (ent_trans hW hYΦ) hp0dd)
      have hz := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _) (HasTy0.restrict hs1 (ent_trans hW hYΦ) hC0d)
      rw [tp_Z] at hz
      have eT := EqTm0.trans (EqTm0.restrict hs1 (ent_trans hW hYc) hcC) hz
      have hf := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _) hWA
      have e3 := EqTm0.conv (EqTm0.restrict hs1 (ent_trans hW hYc) hcr') (EqTm0.symm hf)
      have e4 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs1 hW hYI)
      exact EqTm0.trans e1 (EqTm0.trans (EqTm0.conv e2 (EqTm0.symm eT))
        (EqTm0.trans (EqTm0.symm e3) (EqTm0.symm e4)))
  exact HasTy0.split hφ2 hψ2s (ent_shift (ent_and_right Φ.shift ψ)) hCc2 hPr hinner hover

theorem transpPath_sys_eq (hW : WfSig S) {Ψ : Nat} {A A' a a' b b' p0 p0' T T' : Tm} {φ φ' : I}
    (h : HasTy0 S Ψ .one [] (transp (path A a b) φ p0) T)
    (h' : HasTy0 S Ψ .one [] (transp (path A' a' b') φ' p0') T')
    (hPP : path A a b = path A' a' b' ∨ ∃ l, EqTm0 S (Ψ + 1) .one [] (path A a b) (path A' a' b') (univ l))
    (hp0 : EqTm0 S Ψ .one [] p0 p0' ((path A a b).dinst .zero)) (h12 : I.Entails φ φ') :
    EqTm0 S (Ψ + 1 + 1) (cof I.one.shift (.or φ.shift (.or (.neg (.var 0)) (.var 0)))).shift []
      (split φ.shift.shift (papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI)))
      (split φ'.shift.shift (papp p0'.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) (a'.dsubst insI) (.var 1) (b'.dsubst insI))) (A.dsubst swapI) := by
  have hS := sigClosed_of_wfSig hW
  have hsL := transpPath_sys hS h
  have hsR := transpPath_sys hS h'
  obtain ⟨l1, ⟨hL, hφ, hc, -⟩, -⟩ := gen_transpF h rfl
  have hAl := HasTy0.pathLine hS hL
  have hCc := HasTy0.swap hS hAl
  rw [univ_dsubst] at hCc
  -- the parts of the path types
  have parts : (∃ l, EqTm0 S (Ψ + 1 + 1) I.one.shift.shift [] (A.dsubst swapI) (A'.dsubst swapI) (univ l)) ∧
      EqTm0 S (Ψ + 1) I.one.shift [] a a' (A.dinst .zero) ∧ EqTm0 S (Ψ + 1) I.one.shift [] b b' (A.dinst .one) := by
    rcases hPP with e | ⟨l, e⟩
    · injection e with e1 e2 e3; subst e1 e2 e3
      exact ⟨⟨l1, EqTm0.refl hCc⟩, EqTm0.refl (HasTy0.pathLeft hS hL), EqTm0.refl (HasTy0.pathRight hS hL)⟩
    · have ed := EqTm0.dwk hS e
      have el := EqTm0.pathInjLine (A := A.ren id (upRen Nat.succ)) (A' := A'.ren id (upRen Nat.succ))
        (r := .var 0) ed (show 0 < Ψ + 1 + 1 by omega)
      rw [upDShift_dinst0, upDShift_dinst0] at el
      have el' : EqTm0 S (Ψ + 1 + 1) I.one.shift.shift (Ctx.dshift []).dshift A A' (univ l) := el
      have es := EqTm0.swap hS (Φ := I.one) (Γ := []) el'
      rw [univ_dsubst] at es
      exact ⟨⟨l, es⟩, EqTm0.pathInjLeft e, EqTm0.pathInjRight e⟩
  obtain ⟨⟨lA, eA⟩, ea, eb⟩ := parts
  -- constancy of the swapped line on `φ`
  have hcd := EqTm0.dwk hS hc
  have hci := EqTm0.pathInjLine (A := A.ren id (upRen Nat.succ))
    (A' := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ)).ren id (upRen Nat.succ))
    (r := .var 0) hcd (show 0 < Ψ + 1 + 1 by omega)
  rw [ipi_c1, ipi_c2] at hci
  have hcC := EqTm0.swap hS (Φ := cof I.one φ) hci
  rw [ipi_c3, univ_dsubst] at hcC
  -- contexts
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  let ψ : I := .or φ.shift (.or (.neg (.var 0)) (.var 0))
  let ψ' : I := .or φ'.shift (.or (.neg (.var 0)) (.var 0))
  let ψ2 : I := .or (.neg (.var 1)) (.var 1)
  have hψs : ψ.Scoped (Ψ + 1) := ⟨scoped_shift hφ, ⟨hv0, hv0⟩⟩
  have hC2 : (cof I.one.shift ψ).shift.Scoped (Ψ + 1 + 1) := scoped_shift ⟨trivial, hψs⟩
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hφ)
  have hψ2s : ψ2.Scoped (Ψ + 1 + 1) := ⟨hv1, hv1⟩
  have hCC : I.Entails (cof I.one.shift ψ).shift (cof I.one.shift ψ').shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _))
      (ent_or_right _ _)))
  have eA2 := EqTm0.restrict hC2 (ent_one _) eA
  have hsR' := HasTy0.conv (HasTy0.restrict hC2 hCC hsR) (EqTm0.symm eA2)
  refine EqTm0.local (φ := φ.shift.shift) (ψ := ψ2) hφ2 hψ2s (ent_trans (ent_and_right _ _) (ent_refl _))
    hsL hsR' ?_ ?_
  · -- the bases
    have hc2 : (cof (cof I.one.shift ψ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hC2, hφ2⟩
    have s1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hc2 (ent_and_left _ _) hsL)
    have s2 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_shift h12)))
      (HasTy0.restrict hc2 (ent_and_left _ _) hsR')
    have hpd := EqTm0.dwk hS (EqTm0.dwk hS hp0)
    have m := EqTm0.papp (A := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ)).ren id
      (upRen Nat.succ)) hpd hv1 hv1 (I_eq_refl _)
    rw [tp_P] at m
    have hce : I.Entails (cof (cof I.one.shift ψ).shift φ.shift.shift) (cof I.one φ).shift.shift :=
      ent_and_intro (ent_one _) (ent_and_right _ _)
    have m' := EqTm0.conv (EqTm0.restrict hc2 (ent_one _) m) (EqTm0.symm (EqTm0.restrict hc2 hce hcC))
    exact EqTm0.trans s1 (EqTm0.trans m' (EqTm0.symm s2))
  · -- the endpoints
    have hc2 : (cof (cof I.one.shift ψ).shift ψ2).Scoped (Ψ + 1 + 1) := ⟨hC2, hψ2s⟩
    have t1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc2 (ent_and_left _ _) hsL)
    have t2 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc2 (ent_and_left _ _) hsR')
    have hinL := spec_to_minimal hW (HasTy.eqR (minimal_to_spec_eq t1))
    have hinR := spec_to_minimal hW (HasTy.eqR (minimal_to_spec_eq t2))
    have ee : ∀ (d : Bool) {x x' : Tm}, EqTm0 S (Ψ + 1) I.one.shift [] x x' (A.dinst (I.ofDir d)) →
        EqTm0 S (Ψ + 1 + 1) (cof (cof (cof I.one.shift ψ).shift ψ2) (I.lit 1 d)) [] (x.dsubst insI) (x'.dsubst insI)
          (A.dsubst swapI) := by
      intro d x x' hx
      have hc3 : (cof (cof (cof I.one.shift ψ).shift ψ2) (I.lit 1 d)).Scoped (Ψ + 1 + 1) := ⟨hc2, by cases d <;> exact hv1⟩
      have e0 : EqTm0 S (Ψ + 1 + 1) I.one [] (x.dsubst insI) (x'.dsubst insI) ((A.dinst (I.ofDir d)).dsubst insI) :=
        EqTm0.insI' hS (Φ := I.one) (Γ := []) hx
      have e := EqTm0.restrict hc3 (ent_one _) e0
      rw [tp_end] at e
      have hf := EqTm0.faceU (i := 1) (d := d) (by omega) (ent_and_right _ _)
        (HasTy0.restrict hc3 (ent_one _) hCc)
      exact EqTm0.conv e (EqTm0.symm hf)
    have mm := EqTm0.split hinL hinR (ee false ea) (ee true eb)
    exact EqTm0.trans t1 (EqTm0.trans mm (EqTm0.symm t2))

theorem sysJT_inst (p0 a b : Tm) (φ r : I) :
    (split φ.shift.shift (papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))).subst Tm.var (I.up (I.inst0 r)) =
      split φ.shift (papp p0.dshift r.shift) (.or (.neg r.shift) r.shift) (split (.neg r.shift) a r.shift b) := by
  have hφ : φ.shift.shift.subst (I.up (I.inst0 r)) = φ.shift := by
    rw [I_shift_subst_up, Model.Canon.I_shift_inst0]
  have hd : ∀ x : Tm, x.dshift.dshift.subst Tm.var (I.up (I.inst0 r)) = x.dshift := by
    intro x; simp only [dshift_eq, subst_subst]
    exact subst_congr (fun _ => rfl) (fun i => rfl) x
  have hu : ∀ x : Tm, (x.dsubst insI).subst Tm.var (I.up (I.inst0 r)) = x := by
    intro x
    simp only [Tm.dsubst, subst_subst]
    exact subst_id_of (fun _ => rfl) (fun i => by rcases i with _ | i <;> rfl) x
  simp only [Tm.subst, I.subst]
  rw [hφ, hd p0, hu a, hu b]
  rfl

theorem swap_up_inst0 (A : Tm) (r : I) : (A.dsubst swapI).subst Tm.var (I.up (I.inst0 r)) = A.dinst r.shift := by
  simp only [Tm.dsubst, Tm.dinst, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · rfl
  · rfl
  · rfl

/-- The systems of the points of transports in path types are judgmentally equal. -/
theorem transpPath_sysr_eq (hW : WfSig S) {Ψ : Nat} {A A' a a' b b' p0 p0' T T' : Tm} {φ φ' r r' : I}
    (h : HasTy0 S Ψ .one [] (transp (path A a b) φ p0) T)
    (h' : HasTy0 S Ψ .one [] (transp (path A' a' b') φ' p0') T')
    (hPP : path A a b = path A' a' b' ∨ ∃ l, EqTm0 S (Ψ + 1) .one [] (path A a b) (path A' a' b') (univ l))
    (hp0 : EqTm0 S Ψ .one [] p0 p0' ((path A a b).dinst .zero)) (h12 : I.Entails φ φ')
    (hr : r.Scoped Ψ) (hr' : r'.Scoped Ψ) (hE : I.Eq r r') :
    EqTm0 S (Ψ + 1) (cof .one (.or φ (.or (.neg r) r))).shift []
      (split φ.shift (papp p0.dshift r.shift) (.or (.neg r.shift) r.shift) (split (.neg r.shift) a r.shift b))
      (split φ'.shift (papp p0'.dshift r'.shift) (.or (.neg r'.shift) r'.shift)
        (split (.neg r'.shift) a' r'.shift b')) (A.dinst r.shift) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨hL, hφ, -, -⟩, -⟩ := gen_transpF h rfl
  obtain ⟨l2, ⟨-, hφ', -, -⟩, -⟩ := gen_transpF h' rfl
  have E := transpPath_sys_eq hW h h' hPP hp0 h12
  have hsR := transpPath_sys hS h'
  have hΦs : (cof I.one (.or φ (.or (.neg r) r))).shift.Scoped (Ψ + 1) := scoped_shift ⟨trivial, hφ, ⟨hr, hr⟩⟩
  have hb : ∀ (x : I), x.Scoped Ψ → ∀ i < Ψ + 1 + 1, ((I.up (I.inst0 x)) i).Scoped (Ψ + 1) := by
    intro x hx i hi
    rcases i with _ | _ | i
    · show 0 < Ψ + 1; omega
    · exact scoped_shift hx
    · show i + 1 < Ψ + 1; omega
  have hC : ∀ (x : I) (χ : I), ((cof I.one.shift (.or χ.shift (.or (.neg (.var 0)) (.var 0)))).shift.subst
      (I.up (I.inst0 x))) = (cof I.one (.or χ (.or (.neg x) x))).shift := by
    intro x χ
    rw [I_shift_subst_up]
    show I.shift (cof (I.one.shift.subst _) (.or (χ.shift.subst _) (.or (.neg x) x))) = _
    rw [Model.Canon.I_shift_inst0, Model.Canon.I_shift_inst0]
  have L : EqTm0 S (Ψ + 1) (cof I.one (.or φ (.or (.neg r) r))).shift [] _ _ _ :=
    EqTm0.isub hS E (hb r hr) (by rw [hC]; exact ent_refl _) (Wf0.nil hΦs)
  rw [sysJT_inst, sysJT_inst, swap_up_inst0] at L
  have R : EqTm0 S (Ψ + 1) (cof I.one (.or φ (.or (.neg r) r))).shift [] _ _ _ :=
    HasTy0.ieq hS hsR (hb r hr) (hb r' hr')
      (by rw [hC]; exact ent_shift (ent_and_mono (ent_refl _) (ent_or3 h12 (I_eq_refl _))))
      (by rw [hC]; exact ent_shift (ent_and_mono (ent_refl _) (ent_or3 h12 hE)))
      (fun i hi => by
        rcases i with _ | _ | i
        · exact I_eq_refl _
        · exact fun ρ0 => by simp only [I.up, I.inst0, I.shift, eval_ren]; exact hE _
        · exact I_eq_refl _) rfl (Wf0.nil hΦs)
  rw [sysJT_inst, sysJT_inst, swap_up_inst0] at R
  -- the lines at the point
  have hAl := HasTy0.pathLine hS hL
  have hCc := HasTy0.swap hS hAl
  rw [univ_dsubst] at hCc
  obtain ⟨lA, eA⟩ : ∃ l, EqTm0 S (Ψ + 1 + 1) I.one.shift.shift [] (A.dsubst swapI) (A'.dsubst swapI) (univ l) := by
    rcases hPP with e | ⟨l, e⟩
    · injection e with e1 e2 e3; subst e1 e2 e3
      exact ⟨l1, EqTm0.refl hCc⟩
    · have ed := EqTm0.dwk hS e
      have el := EqTm0.pathInjLine (A := A.ren id (upRen Nat.succ)) (A' := A'.ren id (upRen Nat.succ))
        (r := .var 0) ed (show 0 < Ψ + 1 + 1 by omega)
      rw [upDShift_dinst0, upDShift_dinst0] at el
      have el' : EqTm0 S (Ψ + 1 + 1) I.one.shift.shift (Ctx.dshift []).dshift A A' (univ l) := el
      have es := EqTm0.swap hS (Φ := I.one) (Γ := []) el'
      rw [univ_dsubst] at es
      exact ⟨l, es⟩
  have eA1 : EqTm0 S (Ψ + 1) (cof I.one (.or φ (.or (.neg r) r))).shift [] _ _ _ :=
    EqTm0.isub hS eA (hb r hr) (by show I.Entails _ (I.one.shift.shift.subst _); exact ent_one _) (Wf0.nil hΦs)
  rw [swap_up_inst0, swap_up_inst0] at eA1
  exact EqTm0.trans L (EqTm0.conv R (EqTm0.symm eA1))

end KubusCore.Meta
