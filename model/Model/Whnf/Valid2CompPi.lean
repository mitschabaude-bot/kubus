import Model.Whnf.Valid2Fill

/-!
# Validity of the computation rule `transpPi`

The contractum `λ v. transp (i. B[w(i)]) φ (u0 w(0))` (`KubusCore/Meta/KanTransp.lean`), with the
transported arguments `wT`, `w0T` and their typing derivations, with validity.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- A line at `sk r 1`. -/
theorem VEq.sk1' {t u A : Tm} {X r : I} (hr : r.Scoped (Ψ + 1)) (hΦ : Φ.Scoped Ψ) (hX : I.Entails X Φ.shift)
    (hw : Wf0 S (Ψ + 1) X Γ.dshift) (h : VEq S (Ψ + 1) Φ.shift Γ.dshift t u A) :
    VEq S (Ψ + 1) X Γ.dshift (t.subst Tm.var (sk r 1)) (u.subst Tm.var (sk r 1)) (A.subst Tm.var (sk r 1)) :=
  VEq.isubL hW (n := 1) (m := 1) (Ψ0 := Ψ) (Φs := Φ.shift) (Γ0 := Γ) (sk r 1)
    (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hr) (fun i => rfl) (KubusCore.I.scoped_shift hΦ)
    (ent_sk1 r hX) hw h

/-- `wT_typed`, with validity. -/
theorem VTy.wT' {A : Tm} {φ : I} {l : ℕ} (hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l))
    (hφ : φ.Scoped Ψ) (hcD : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l)) :
    VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (wT A φ) A.shift := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hA.ty)
  have hs := scoped_of_wf hw0
  have hA1 := VTy.dsubst' hW .one trivial hA
  have hwΔ : Wf0 S Ψ Φ (A.dinst .one :: Γ) := Wf0.cons hA1.ty
  have hA1d := VTy.dwk' hW hA1
  have hAw : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift (.univ l) := VTy.wk' hW hA1d.ty hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hψ : (I.or φ.shift (.var 0)).Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hφ, hv0⟩
  -- the line
  have hL := VTy.bind2' hW (Γ := A.dinst .one :: Γ) (X := Φ.shift.shift) (r := .or (.var 1) (.neg (.var 0)))
    ⟨hv1, hv0'⟩ hs (ent_refl _) (hwΔ.dwk2 hS) hAw
  rw [univ_dsubst] at hL
  -- constancy
  let Y : I := (cof Φ.shift (.or φ.shift (.var 0))).shift
  have hYs : Y.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift ⟨KubusCore.I.scoped_shift hs, hψ⟩
  have hYΦ : I.Entails Y Φ.shift.shift := ent_and_left _ _
  have hwY : Wf0 S (Ψ + 2) Y (Ctx.dren 2 (A.dinst .one :: Γ)) := by
    rw [Ctx.dren_two]; exact (hwΔ.dwk2 hS).restrict hYs hYΦ
  have hLY := VTy.restrict' hW hYs hYΦ hL
  have hL0Y := VTy.restrict' hW hYs hYΦ (VTy.dwk' hW
    (VTy.dsubst' hW (Φ := Φ.shift) (Γ := Ctx.dshift (A.dinst .one :: Γ)) .zero trivial hL))
  have hconst : VEq S (Ψ + 1 + 1) Y (Ctx.dshift (A.dinst .one :: Γ)).dshift
      (A.shift.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0)))))
      ((A.shift.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).dinst .zero).dshift (.univ l) := by
    refine VEq.local' hW (φ := φ.shift.shift) (ψ := .var 1) (KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hφ))
      hv1 (ent_and_right _ _) hLY hL0Y ?_ ?_
    · -- on φ: the domain is constant
      have hZs : (cof Y φ.shift.shift).Scoped (Ψ + 1 + 1) :=
        ⟨hYs, KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hφ)⟩
      have hZ : I.Entails (cof Y φ.shift.shift) (cof Φ φ).shift.shift :=
        ent_and_intro (ent_trans (ent_and_left _ _) hYΦ) (ent_and_right _ _)
      have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, hφ⟩
      have hcDw := VEq.wk' hW (VTy.restrict' hW hXs (ent_shift (ent_and_left _ _)) hA1d).ty hcD
      have key : ∀ r : I, r.Scoped (Ψ + 1 + 1) →
          VEq S (Ψ + 1 + 1) (cof Y φ.shift.shift) (Ctx.dshift (A.dinst .one :: Γ)).dshift
            (A.shift.subst Tm.var (sk r 2)) (A.dinst .zero).shift.dshift.dshift (.univ l) := by
        intro r hr
        have := VEq.sk2' hW (Γ := A.dinst .one :: Γ) (Φ := cof Φ φ) (X := cof Y φ.shift.shift) hr ⟨hs, hφ⟩ hZ
          ((hwΔ.dwk2 hS).restrict hZs (ent_trans hZ (ent_shift (ent_shift (ent_and_left _ _))))) hcDw
        rwa [pw_shift_sk2] at this
      have e1 := key (.or (.var 1) (.neg (.var 0))) ⟨hv1, hv0'⟩
      have e2 := key (.or (.var 1) (.neg .zero)) ⟨hv1, trivial⟩
      rw [pw_L0s, pw_L]
      exact VEq.trans' hW e1 (VEq.symm' hW e2)
    · -- on i = 1: the line is constant
      have hZs : (cof Y (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hZΦ : I.Entails (cof Y (.var 1)) (Φ.subst (fun n => .var (n + 2))) := by
        rw [I_add2]; exact ent_trans (ent_and_left _ _) hYΦ
      have hwZ : Wf0 S (Ψ + 2) (cof Y (.var 1)) (Ctx.dren 2 (A.dinst .one :: Γ)) :=
        hwY.restrict hZs (ent_and_left _ _)
      have e1 := VEq.faceU' hW (i := 1) (d := true) hv1 (ent_and_right _ _) (VTy.restrict' hW hZs (ent_and_left _ _) hLY)
      rw [pw_dset11] at e1
      have e2 := VTy.lineIeq hW hAw (k := 2) (r := .or .one (.neg (.var 0))) (r' := .one) hZΦ
        ⟨trivial, hv0'⟩ trivial (I_eq_or_one_l _) hwZ
      rw [Ctx.dren_two] at e2
      have hL0Z := VTy.restrict' hW hZs (ent_and_left _ _) hL0Y
      rw [pw_L0s] at hL0Z
      have e3 := VEq.faceU' hW (i := 1) (d := true) hv1 (ent_and_right _ _) hL0Z
      rw [pw_dset11'] at e3
      have e4 := VTy.lineIeq hW hAw (k := 2) (r := .or .one (.neg .zero)) (r' := .one) hZΦ
        ⟨trivial, trivial⟩ trivial (I_eq_or_one_l _) hwZ
      rw [Ctx.dren_two] at e4
      rw [pw_L0s]
      exact VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.symm' hW (VEq.trans' hW e3 e4)))
  -- the base
  have hwX : Wf0 S (Ψ + 1) Φ.shift (Ctx.dren 1 (A.dinst .one :: Γ)) := wf_of_ty hAw.ty
  have hb : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (.var 0)
      ((A.shift.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).dinst .zero) := by
    rw [pw_L0]
    have e := VTy.lineIeq hW hAw (k := 1) (r := .one) (r' := .or (.var 0) (.neg .zero)) (ent_refl _)
      trivial ⟨hv0, trivial⟩ (I_eq_symm (I_eq_or_negzero_r _)) hwX
    have hv := VTy.var' hW (A := (A.dinst .one).dshift.shift) (x := 0) (wf_of_ty hAw.ty) rfl
    rw [pw_A1] at hv
    exact VTy.conv' hW hv e
  have ht := VTy.transp' hW hL hψ hconst hb
  rw [pw_L1] at ht
  have e := VTy.lineIeq hW hAw (k := 1) (r := .or (.var 0) (.neg .one)) (r' := .var 0) (ent_refl _)
    ⟨hv0, trivial⟩ hv0 (I_eq_or_negone_r _) hwX
  rw [sk_var1] at e
  exact VTy.conv' hW ht e

/-- `w0T_typed`, with validity. -/
theorem VTy.w0T' {A : Tm} {φ : I} {l : ℕ} (hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l))
    (hφ : φ.Scoped Ψ) (hcD : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l)) :
    VTy S Ψ Φ (A.dinst .one :: Γ) (w0T A φ) ((A.shift.dsubst negI).dinst .one) ∧
      VEq S Ψ Φ (A.dinst .one :: Γ) ((A.shift.dsubst negI).dinst .one) (A.dinst .zero).shift (.univ l) ∧
      VTy S Ψ Φ (A.dinst .one :: Γ) (.var 0) ((A.shift.dsubst negI).dinst .zero) ∧
      VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (A.shift.dsubst negI) (.univ l) ∧
      VEq S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
        (A.shift.dsubst negI) ((A.shift.dsubst negI).dinst .zero).dshift (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hA.ty)
  have hs := scoped_of_wf hw0
  have hA1 := VTy.dsubst' hW .one trivial hA
  have hwΔ : Wf0 S Ψ Φ (A.dinst .one :: Γ) := Wf0.cons hA1.ty
  have hA1d := VTy.dwk' hW hA1
  have hAw : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift (.univ l) := VTy.wk' hW hA1d.ty hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  -- the line
  have hL : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (A.shift.dsubst negI) (.univ l) :=
    VTy.isubL hW (n := 1) (m := 1) (Ψ0 := Ψ) (Φs := Φ.shift) (Γ0 := A.dinst .one :: Γ) negI
      (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact hv0) (fun i => rfl) (KubusCore.I.scoped_shift hs)
      (by rw [I_shift_subst]; exact ent_refl _) (wf_of_ty hAw.ty) hAw
  -- constancy
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, hφ⟩
  have hcDw := VEq.wk' hW (VTy.restrict' hW hXs (ent_shift (ent_and_left _ _)) hA1d).ty hcD
  have key : ∀ r : I, r.Scoped (Ψ + 1) →
      VEq S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
        (A.shift.subst Tm.var (sk r 1)) (A.dinst .zero).shift.dshift (.univ l) := by
    intro r hr
    have := VEq.sk1' hW (Γ := A.dinst .one :: Γ) (Φ := cof Φ φ) hr ⟨hs, hφ⟩ (ent_refl _) (wf_of_eq hcDw.eq) hcDw
    rwa [p0_shift_sk1] at this
  have hconst : VEq S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
      (A.shift.dsubst negI) ((A.shift.dsubst negI).dinst .zero).dshift (.univ l) := by
    rw [p0_L0s, p0_L]
    exact VEq.trans' hW (key _ hv0) (VEq.symm' hW (key (.neg .zero) trivial))
  -- the base
  have hwX : Wf0 S (Ψ + 0) Φ (Ctx.dren 0 (A.dinst .one :: Γ)) := by rw [Ctx.dren_zero]; exact hwΔ
  have hΦ0 : I.Entails Φ (Φ.subst (fun n => .var (n + 0))) := by rw [I_add0]; exact ent_refl _
  have hb : VTy S Ψ Φ (A.dinst .one :: Γ) (.var 0) ((A.shift.dsubst negI).dinst .zero) := by
    rw [p0_L0]
    have e := VTy.lineIeq hW hAw (k := 0) (r := .one) (r' := .neg .zero) hΦ0 trivial trivial
      (I_eq_symm I_eq_neg_zero) hwX
    rw [Ctx.dren_zero] at e
    have hv := VTy.var' hW (A := (A.dinst .one).shift) (x := 0) hwΔ rfl
    rw [p0_A1] at hv
    exact VTy.conv' hW hv e
  have ht := VTy.transp' hW hL hφ hconst hb
  have e := VTy.lineIeq hW hAw (k := 0) (r := .neg .one) (r' := .zero) hΦ0 trivial trivial I_eq_neg_one hwX
  rw [Ctx.dren_zero, p0_A0] at e
  refine ⟨ht, ?_, hb, hL, hconst⟩
  rw [p0_L1]; exact e

omit hW in
theorem lookup_upRen_succ (B X : Tm) (Γ' : Ctx) : ∀ x A', Ctx.lookup (B :: Γ') x = some A' →
    Ctx.lookup (B.shift :: X :: Γ') (Tm.upRen Nat.succ x) = some (A'.ren (Tm.upRen Nat.succ) id) := by
  intro x A' h
  have e : ∀ t : Tm, t.shift.shift = t.shift.ren (Tm.upRen Nat.succ) id := fun t => by
    simp only [Tm.shift, ren_ren]; rfl
  cases x with
  | zero =>
    simp only [Ctx.lookup, Option.some.injEq] at h; subst h
    simp only [Tm.upRen, Ctx.lookup]; rw [e]
  | succ x =>
    simp only [Ctx.lookup, Option.map_eq_some_iff] at h
    obtain ⟨A'', h1, rfl⟩ := h
    simp only [Tm.upRen, Ctx.lookup, h1, Option.map_some]; rw [e]

/-- The body of the contractum of `transpPi`, typed and valid, with the transported argument. -/
theorem VTy.transpPiBody' {A B u0 : Tm} {φ : I} {l : ℕ}
    (hLp : VTy S (Ψ + 1) Φ.shift Γ.dshift (.pi A B) (.univ l)) (hφ : φ.Scoped Ψ)
    (hcp : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (.pi A B) ((Tm.pi A B).dinst .zero).dshift (.univ l))
    (hu0p : VTy S Ψ Φ Γ u0 ((Tm.pi A B).dinst .zero)) :
    VTy S Ψ Φ (A.dinst .one :: Γ)
      (.transp (B.subst (consT (wT A φ) wkS) I.var) φ (.app u0.shift (w0T A φ))) (B.subst (Tm.up Tm.var) (I.inst0 .one)) ∧
    VTy S Ψ Φ (A.dinst .one :: Γ) (w0T A φ) ((A.shift.dsubst negI).dinst .one) ∧
    VEq S Ψ Φ (A.dinst .one :: Γ) ((A.shift.dsubst negI).dinst .one) (A.dinst .zero).shift (.univ l) ∧
    VTy S Ψ Φ (A.dinst .one :: Γ) u0.shift ((Tm.pi A B).dinst .zero).shift := by
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hu0p.ty
  have hL := hLp.ty
  have hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l) :=
    ⟨HasTy0.piDom hS hL, valid_piDom hW hLp.v (HasTy0.piDom hS hL)⟩
  have hB : VTy S (Ψ + 1) Φ.shift (A :: Γ.dshift) B (.univ l) :=
    ⟨HasTy0.piCod hS hL, valid_piCod hW hLp.v (HasTy0.piCod hS hL)⟩
  have hcD := VEq.piInjDom' hW (A' := (A.dinst .zero).dshift) hcp
  have hw := VTy.wT' hW hA hφ hcD
  obtain ⟨hw0, E0, hv00, hL0, hc0⟩ := VTy.w0T' hW hA hφ hcD
  have hA1 := VTy.dsubst' hW .one trivial hA
  have hwΔ : Wf0 S Ψ Φ (A.dinst .one :: Γ) := Wf0.cons hA1.ty
  have hA1d := VTy.dwk' hW hA1
  have hAw : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift (.univ l) := VTy.wk' hW hA1d.ty hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  -- the line `B[w]`
  have hσ := (tySub_wk hA1d.ty).cons (A := A) (a := wT A φ)
    (by show HasTy0 S (Ψ + 1) Φ.shift _ _ (A.subst (fun n => .var (n + 1)) I.var); rw [← shift_eq]; exact hw.ty)
  have hBw : VTy S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (B.subst (consT (wT A φ) wkS) I.var)
      (.univ l) := by
    refine ⟨(sub_ty hS hB.ty).2.1 hσ, ?_⟩
    rw [Bw_inst]
    exact valid_inst hW (B := .univ l) hAw.v hw.v
      (valid_ren (Tm.upRen Nat.succ) (lookup_upRen_succ A _ Γ.dshift) hB.v)
  -- constancy of `B[w]` on `φ`
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, hφ⟩
  have hXΦ : I.Entails (cof Φ φ).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hA1dX := VTy.restrict' hW hXs hXΦ hA1d
  have hcw := VEq.wk' hW hA1dX.ty hcp
  have hwX := VTy.restrict' hW hXs hXΦ hw
  have e1 := VEq.piInjCod' hW (A := A.shift) (B := B.ren (Tm.upRen Nat.succ) id)
    (A' := (A.dinst .zero).dshift.shift)
    (B' := ((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen id) Nat.succ).ren (Tm.upRen Nat.succ) id)
    (a := wT A φ) hcw hwX
  have hcDw := VEq.wk' hW hA1dX.ty hcD
  have hRz := VTy.wk' hW hA1dX.ty (VTy.restrict' hW hXs hXΦ (VTy.dwk' hW (VTy.dsubst' hW .zero trivial hLp)))
  have hAz : VTy S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) (A.dinst .zero).dshift.shift (.univ l) :=
    ⟨HasTy0.piDom hS hRz.ty, valid_piDom hW hRz.v (HasTy0.piDom hS hRz.ty)⟩
  have hBz : VTy S (Ψ + 1) (cof Φ φ).shift ((A.dinst .zero).dshift.shift :: Ctx.dshift (A.dinst .one :: Γ))
      (((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen id) Nat.succ).ren (Tm.upRen Nat.succ) id) (.univ l) :=
    ⟨HasTy0.piCod hS hRz.ty, valid_piCod hW hRz.v (HasTy0.piCod hS hRz.ty)⟩
  have hwd := VTy.restrict' hW hXs hXΦ (VTy.dwk' hW (VTy.dsubst' hW .zero trivial hw))
  rw [pi_t1] at hwd
  have f1 : VEq S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) (wT A φ) (.var 0) A.shift :=
    VEq.transpFace' hW (ent_trans (ent_shift (ent_and_right Φ φ)) (ent_or_left _ _)) hwX
  have f2 : VEq S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) ((wT A φ).dinst .zero).dshift
      (.var 0) (A.dinst .zero).dshift.shift :=
    VEq.transpFace' hW (φ := ((I.or φ.shift (.var 0)).subst (I.inst0 .zero)).shift)
      (by rw [cofw_inst]; exact ent_trans (ent_shift (ent_and_right Φ φ)) (ent_shift (ent_or_left φ .zero))) hwd
  have he := VEq.trans' hW (VEq.conv' hW f1 hcDw) (VEq.symm' hW f2)
  have e2 := VTy.inst_congr' hW hAz hBz he
  have hBC : VEq S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
      (B.subst (consT (wT A φ) wkS) I.var) ((B.subst (consT (wT A φ) wkS) I.var).dinst .zero).dshift (.univ l) := by
    rw [Bw_dinst_dshift, Bw_inst]
    exact VEq.trans' hW e1 e2
  -- the base
  have hu0w := VTy.wk' hW hA1.ty hu0p
  have happ := VTy.app' hW (A := (A.dinst .zero).shift)
    (B := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen Nat.succ) id) hu0w (VTy.conv' hW hw0 E0)
  have hR0 := VTy.wk' hW hA1.ty (VTy.dsubst' hW .zero trivial hLp)
  have hAz0 : VTy S Ψ Φ (A.dinst .one :: Γ) (A.dinst .zero).shift (.univ l) :=
    ⟨HasTy0.piDom hS hR0.ty, valid_piDom hW hR0.v (HasTy0.piDom hS hR0.ty)⟩
  have hBz0 : VTy S Ψ Φ ((A.dinst .zero).shift :: A.dinst .one :: Γ)
      ((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen Nat.succ) id) (.univ l) :=
    ⟨HasTy0.piCod hS hR0.ty, valid_piCod hW hR0.v (HasTy0.piCod hS hR0.ty)⟩
  have hwd0 : VTy S Ψ Φ (A.dinst .one :: Γ) ((wT A φ).dinst .zero) (A.shift.dinst .zero) :=
    VTy.dsubst' hW .zero trivial hw
  rw [shift_dinst_comm] at hwd0
  have hwX1 : Wf0 S (Ψ + 1) Φ.shift (Ctx.dren 1 (A.dinst .one :: Γ)) := wf_of_ty hAw.ty
  have hline : VEq S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (A.shift.dsubst negI)
      ((A.shift.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).subst (fun n => (Tm.var n).dshift)
        (I.up (I.inst0 .zero))) (.univ l) := by
    have e := VTy.lineIeq hW hAw (k := 1) (r := .neg (.var 0)) (r' := .or .zero (.neg (.var 0)))
      (ent_refl _) hv0 ⟨trivial, hv0⟩ (I_eq_symm (I_eq_or_zero_l _)) hwX1
    rw [p0_L, pw_Lw0]; exact e
  have heq0 : VEq S Ψ Φ (A.dinst .one :: Γ) (w0T A φ) ((wT A φ).dinst .zero) (A.dinst .zero).shift := by
    refine VEq.conv' hW (VEq.transp' hW 
      (A' := (A.shift.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).subst (fun n => (Tm.var n).dshift)
        (I.up (I.inst0 .zero)))
      (φ' := (I.or φ.shift (.var 0)).subst (I.inst0 .zero)) (a' := .var 0) hφ ?_ ?_ hw0.ty
      (HasTy0.conv hwd0.ty (VEq.symm' hW E0).eq) hline hc0.v (VEq.refl' hv00)) E0
    · rw [cofw_inst]; exact ent_or_left _ _
    · rw [cofw_inst]; exact ent_or_elim (ent_refl _) (ent_zero _)
  have hbase : VTy S Ψ Φ (A.dinst .one :: Γ) (.app u0.shift (w0T A φ))
      ((B.subst (consT (wT A φ) wkS) I.var).dinst .zero) := by
    rw [Bw_dinst]
    exact VTy.conv' hW happ (VTy.inst_congr' hW hAz0 hBz0 heq0)
  have ht := VTy.transp' hW hBw hφ hBC hbase
  rw [Bw_dinst] at ht
  -- the endpoint
  have hR1 := VTy.wk' hW hA1.ty (VTy.dsubst' hW .one trivial hLp)
  have hAz1 : VTy S Ψ Φ (A.dinst .one :: Γ) (A.dinst .one).shift (.univ l) :=
    ⟨HasTy0.piDom hS hR1.ty, valid_piDom hW hR1.v (HasTy0.piDom hS hR1.ty)⟩
  have hBz1 : VTy S Ψ Φ ((A.dinst .one).shift :: A.dinst .one :: Γ)
      ((B.subst (Tm.up Tm.var) (I.inst0 .one)).ren (Tm.upRen Nat.succ) id) (.univ l) :=
    ⟨HasTy0.piCod hS hR1.ty, valid_piCod hW hR1.v (HasTy0.piCod hS hR1.ty)⟩
  have hwd1 : VTy S Ψ Φ (A.dinst .one :: Γ) ((wT A φ).dinst .one) (A.shift.dinst .one) :=
    VTy.dsubst' hW .one trivial hw
  rw [shift_dinst_comm] at hwd1
  have heF : VEq S Ψ Φ (A.dinst .one :: Γ) ((wT A φ).dinst .one) (.var 0) (A.dinst .one).shift :=
    VEq.transpFace' hW (φ := (I.or φ.shift (.var 0)).subst (I.inst0 .one))
      (by rw [cofw_inst]; exact ent_trans (ent_one Φ) (ent_or_right _ _)) hwd1
  have eF := VTy.inst_congr' hW hAz1 hBz1 heF
  rw [upShift_inst0] at eF
  exact ⟨VTy.conv' hW ht eF, hw0, E0, hu0w⟩

/-- `transpPi` is valid. -/
theorem valid_transpPi_rule {A B u0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.transp (.pi A B) φ u0) T)
    (hv : Valid2 S Ψ Φ Γ (.transp (.pi A B) φ u0) (.transp (.pi A B) φ u0) T)
    (hinv : TranspInv S Ψ Φ Γ (.pi A B) φ u0 T) :
    Valid2 S Ψ Φ Γ (.transp (.pi A B) φ u0) (Tm.transpPi A B φ u0) T := by
  obtain ⟨l, hφ, hLV, hCV, hu0V, htr, hL, hc, hu0⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hu0
  have hLp : VTy S (Ψ + 1) Φ.shift Γ.dshift (.pi A B) (.univ l) := ⟨hL, hLV⟩
  have hcp : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (.pi A B) ((Tm.pi A B).dinst .zero).dshift (.univ l) :=
    ⟨hc, hCV⟩
  have hu0p : VTy S Ψ Φ Γ u0 ((Tm.pi A B).dinst .zero) := ⟨hu0, hu0V⟩
  obtain ⟨hbody, hw0, E0, hu0w⟩ := VTy.transpPiBody' hW hLp hφ hcp hu0p
  have hL1 := VTy.dsubst' hW .one trivial hLp
  have hy : VTy S Ψ Φ Γ (Tm.transpPi A B φ u0) ((Tm.pi A B).dinst .one) := VTy.lam' hW hL1 hbody
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hy.v htr hT
  -- where the face holds: `u0`, by η and the face of the body
  have hX0 : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hX0Φ : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have hφ0 : I.Entails (cof Φ φ) φ := ent_and_right _ _
  have hk1 := VEq.dsubst' hW .one trivial hcp
  rw [dshift_dinst] at hk1
  have hu0P1 := VTy.conv' hW (VTy.restrict' hW hX0 hX0Φ hu0p) (VEq.symm' hW hk1)
  have hη := VEq.piEta' hW (A := A.dinst .one) (B := B.subst (Tm.up Tm.var) (I.inst0 .one)) hu0P1
  have hA1 := VTy.dsubst' hW .one trivial (⟨HasTy0.piDom hS hL, valid_piDom hW hLV (HasTy0.piDom hS hL)⟩ :
    VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l))
  have hX1 : (cof Φ φ).Scoped Ψ := hX0
  have hbX := VTy.restrict' hW hX1 hX0Φ hbody
  have f1 := VEq.transpFace' hW hφ0 hbX
  have hw0X := VTy.restrict' hW hX1 hX0Φ hw0
  have fw := VEq.conv' hW (VEq.transpFace' hW hφ0 hw0X) (VEq.restrict' hW hX1 hX0Φ E0)
  have hu0wX := VTy.restrict' hW hX1 hX0Φ hu0w
  have f2 := VEq.app' hW (A := (A.dinst .zero).shift)
    (B := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen Nat.succ) id) (VEq.refl' hu0wX) fw
  -- the codomain at `w0T` is the codomain at the variable, which is the codomain at `1`
  have hR0X := VTy.restrict' hW hX1 hX0Φ (VTy.wk' hW hA1.ty (VTy.dsubst' hW .zero trivial hLp))
  have hAz0 : VTy S Ψ (cof Φ φ) (A.dinst .one :: Γ) (A.dinst .zero).shift (.univ l) :=
    ⟨HasTy0.piDom hS hR0X.ty, valid_piDom hW hR0X.v (HasTy0.piDom hS hR0X.ty)⟩
  have hBz0 : VTy S Ψ (cof Φ φ) ((A.dinst .zero).shift :: A.dinst .one :: Γ)
      ((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen Nat.succ) id) (.univ l) :=
    ⟨HasTy0.piCod hS hR0X.ty, valid_piCod hW hR0X.v (HasTy0.piCod hS hR0X.ty)⟩
  have eB1 := VTy.inst_congr' hW hAz0 hBz0 fw
  rw [upShift_inst0] at eB1
  have hk1w := VEq.wk' hW (VTy.restrict' hW hX1 hX0Φ hA1).ty hk1
  have hvA1 : VTy S Ψ (cof Φ φ) (A.dinst .one :: Γ) (.var 0) (A.dinst .one).shift :=
    VTy.var' hW (Wf0.cons (VTy.restrict' hW hX1 hX0Φ hA1).ty) rfl
  have eB2 := VEq.piInjCod' hW (A := (A.dinst .one).shift)
    (B := (B.subst (Tm.up Tm.var) (I.inst0 .one)).ren (Tm.upRen Nat.succ) id)
    (A' := (A.dinst .zero).shift) (B' := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen Nat.succ) id)
    hk1w hvA1
  rw [upShift_inst0, upShift_inst0] at eB2
  have f2' := VEq.conv' hW f2 (VEq.trans' hW eB1 (VEq.symm' hW eB2))
  have hbe := VEq.symm' hW (VEq.trans' hW f1 f2')
  have hlam := VEq.lam' hW (VTy.restrict' hW hX1 hX0Φ hL1) hbe
  have hb := valid_conv_tr (VEq.trans' hW hη hlam).v (htr.restrict hX0Φ) fun k c => hT k (c.restrictTo hX0Φ)
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e3 : c.L (Tm.transpPi A B φ u0) = Tm.transpPi (A.subst (dupS c.γ) (I.up c.σ.τ))
        (B.subst (Tm.up (dupS c.γ)) (I.up c.σ.τ)) (φ.subst c.σ.τ) (c.L u0) := transpPi_subst _ _ A B φ u0
    rw [e3]
    exact ⟨.step (step_transp_pi hn) (.refl _), EqTm.transpPi (c.ty hW h)⟩
  · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (c.ty hW h)⟩

end

end Model.Whnf
