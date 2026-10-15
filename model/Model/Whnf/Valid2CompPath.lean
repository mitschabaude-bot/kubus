import Model.Whnf.Valid2Fill

/-!
# Validity of the computation rules in path types

`hcompPath` and `transpPath`, by the typing derivations of their contracta
(`KubusCore/Meta/KanPath.lean`, `KubusCore/Meta/KanTransp.lean`) with validity.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-! ### Components and eliminations of path types -/

theorem valid_pathLine {L a b : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.path L a b) (.path L a b) (.univ l))
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift L (.univ l)) : Valid2 S (Ψ + 1) Φ.shift Γ.dshift L L (.univ l) := by
  refine valid_univ_of hW hL hL (EqTm0.refl hL) fun k c => ?_
  have hh := (RT2_path_inv hW (h.ty hW c.dtail)).2.1 _ _ (c.σ.sc 0 (by omega)) (c.σ'.sc 0 (by omega)) (c.hσ 0)
  simp only [CSub2.L, CSub2.R, CSub2.dtail] at hh ⊢
  rw [dup_dinst, dup_dinst] at hh
  have e1 : consI (c.σ.τ 0) c.σ.tail.τ = c.σ.τ := consI_tail c.σ
  have e2 : consI (c.σ'.τ 0) c.σ'.tail.τ = c.σ'.τ := consI_tail c.σ'
  rwa [e1, e2] at hh

/-- The line, left and right endpoints of a typed and valid path type. -/
theorem VTy.pathParts {L a b : Tm} {l : ℕ} (h : VTy S Ψ Φ Γ (.path L a b) (.univ l)) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift L (.univ l) ∧ VTy S Ψ Φ Γ a (L.dinst .zero) ∧ VTy S Ψ Φ Γ b (L.dinst .one) := by
  have hS := sigClosed_of_wfSig hW
  have hL := HasTy0.pathLine hS h.ty
  exact ⟨⟨hL, valid_pathLine hW h.v hL⟩, ⟨HasTy0.pathLeft hS h.ty, valid_pathInjLeft hW h.v⟩,
    ⟨HasTy0.pathRight hS h.ty, valid_pathInjRight hW h.v⟩⟩

theorem VEq.pathZero' {L a b p : Tm} (h : VTy S Ψ Φ Γ p (.path L a b)) :
    VEq S Ψ Φ Γ (.papp p .zero) a (L.dinst .zero) :=
  ⟨EqTm0.pathZero h.ty, valid_pathZero hW h.v⟩

theorem VEq.pathOne' {L a b p : Tm} (h : VTy S Ψ Φ Γ p (.path L a b)) :
    VEq S Ψ Φ Γ (.papp p .one) b (L.dinst .one) :=
  ⟨EqTm0.pathOne h.ty, valid_pathOne hW h.v⟩

theorem VEq.plam' {L a b t t' : Tm} {l : ℕ} (hpath : VTy S Ψ Φ Γ (.path L a b) (.univ l))
    (hp : VTy S Ψ Φ Γ (.plam t) (.path L a b)) (hty' : HasTy0 S Ψ Φ Γ (.plam t') (.path L a b))
    (ht : VEq S (Ψ + 1) Φ.shift Γ.dshift t t' L) : VEq S Ψ Φ Γ (.plam t) (.plam t') (.path L a b) := by
  have e := EqTm0.plam hpath.ty hp.ty hty' ht.eq
  exact ⟨e, valid_plam_eq hW hpath.v hp.v ht.v hp.ty hty' e⟩

theorem VEq.pathInjLeft' {L L' a a' b b' : Tm} {l : ℕ} (h : VEq S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l)) :
    VEq S Ψ Φ Γ a a' (L.dinst .zero) :=
  ⟨EqTm0.pathInjLeft h.eq, valid_pathInjLeft hW h.v⟩

theorem VEq.pathInjRight' {L L' a a' b b' : Tm} {l : ℕ} (h : VEq S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l)) :
    VEq S Ψ Φ Γ b b' (L.dinst .one) :=
  ⟨EqTm0.pathInjRight h.eq, valid_pathInjRight hW h.v⟩

theorem VEq.pathInjLine' {L L' a a' b b' : Tm} {r : I} {l : ℕ}
    (h : VEq S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l)) (hr : r.Scoped Ψ) :
    VEq S Ψ Φ Γ (L.dinst r) (L'.dinst r) (.univ l) := by
  have e := EqTm0.pathInjLine h.eq hr
  exact ⟨e, valid_pathInjLine hW h.v hr (presup hW e).1 (presup hW e).2 e⟩

omit hW in
theorem bind2_var0 : Tm.bind2 (.var 0) = insI := by funext n; cases n <;> rfl

omit hW in
theorem path_dshift_insI (A a b : Tm) :
    (Tm.path A a b).dshift.dsubst insI = .path (Xp A) a.dshift.dshift b.dshift.dshift := by
  simp only [Tm.dshift, Tm.dsubst, Tm.ren, Tm.subst]
  congr 1
  · simp only [Xp]; ssub
  · ssub
  · ssub

/-- A tube renamed past a new interval variable 1. -/
theorem VTy.tubeSkip {Φs : I} {u X : Tm} (hΦs : Φs.Scoped Ψ) (hu : VTy S (Ψ + 1) Φs.shift Γ.dshift u X) :
    VTy S (Ψ + 1 + 1) Φs.shift.shift Γ.dshift.dshift (u.dsubst insI) (X.dsubst insI) := by
  have := VTy.bind2' hW (X := Φs.shift.shift) (r := .var 0) (show (0 : ℕ) < Ψ + 2 by omega) hΦs (ent_refl _)
    ((wf_unshift (sigClosed_of_wfSig hW) (wf_of_ty hu.ty)).dwk2 (sigClosed_of_wfSig hW)) hu
  rwa [bind2_var0] at this

/-! ### `hcomp` in path types -/

omit hW in
theorem sys1_eq (φ : I) (u a b : Tm) :
    (Tm.split φ.shift.shift (.papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)).dinst .one =
      .split φ.shift (.papp (u.dinst .one).dshift (.var 0)) (.or (.neg (.var 0)) (.var 0))
        (.split (.neg (.var 0)) a.dshift (.var 0) b.dshift) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; rfl
  · congr 1; ssub
  · congr 1 <;> ssub

omit hW in
theorem papp_endS (u : Tm) (d : Bool) :
    (Tm.papp (u.dsubst insI) (.var 1)).subst Tm.var (endS d) = .papp (u.dinst .one) (I.ofDir d) := by
  have h := sysEnd_eq .zero u (.var 0) (.var 0) d
  simp only [Tm.subst] at h ⊢
  injection h with _ h1

/-- The contractum of `hcompPath`, typed and valid. -/
theorem VTy.hcompPath' {A a b u p0 : Tm} {φ : I} {l : ℕ}
    (hPp : VTy S Ψ Φ Γ (.path A a b) (.univ l)) (hφ : φ.Scoped Ψ)
    (hup : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (Tm.path A a b).dshift)
    (hp0p : VTy S Ψ Φ Γ p0 (.path A a b)) (hsidep : VEq S Ψ (cof Φ φ) Γ (u.dinst .zero) p0 (.path A a b)) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift (.hcomp A (.or φ.shift (.or (.neg (.var 0)) (.var 0)))
      (.split φ.shift.shift (.papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift))
      (.papp p0.dshift (.var 0))) A ∧
    VTy S Ψ Φ Γ (Tm.hcompPath A a b φ u p0) (.path A a b) := by
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hPp.ty
  have hw0 := wf_of_ty hPp.ty
  obtain ⟨hA, ha, hb⟩ := VTy.pathParts hW hPp
  -- contexts
  let ψ : I := .or φ.shift (.or (.neg (.var 0)) (.var 0))
  have hψs : ψ.Scoped (Ψ + 1) :=
    ⟨KubusCore.I.scoped_shift hφ, ⟨show 0 < Ψ + 1 by omega, show 0 < Ψ + 1 by omega⟩⟩
  have hΞs : (cof Φ.shift ψ).Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hs, hψs⟩
  have hR2s : (cof Φ.shift ψ).shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift hΞs
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hφ)
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0 : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  let ψ2 : I := .or (.neg (.var 1)) (.var 1)
  have hψ2s : ψ2.Scoped (Ψ + 1 + 1) := ⟨hv1, hv1⟩
  -- the line in the tube context
  have hA2 : VTy S (Ψ + 1 + 1) (cof Φ.shift ψ).shift Γ.dshift.dshift A.dshift (.univ l) :=
    VTy.restrict' hW hR2s (ent_shift (ent_and_left _ _)) (VTy.dwk' hW hA)
  -- the tube
  have hu2 := VTy.tubeSkip hW (Φs := cof Φ φ) ⟨hs, hφ⟩ hup
  rw [path_dshift_insI] at hu2
  have hU := VTy.papp' hW hu2 hv1
  rw [Xp_var1] at hU
  have hR3 : (cof (cof Φ.shift ψ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hR2s, hφ2⟩
  have hR3e : I.Entails (cof (cof Φ.shift ψ).shift φ.shift.shift) (cof Φ φ).shift.shift :=
    ent_and_mono (ent_shift (ent_and_left Φ.shift ψ)) (ent_refl _)
  have hUr := VTy.restrict' hW hR3 hR3e hU
  -- the inner system `[j = 0 ↦ a, j = 1 ↦ b]`
  have hR2Φ : I.Entails (cof Φ.shift ψ).shift Φ.shift.shift := ent_shift (ent_and_left Φ.shift ψ)
  have hΞ2s : (cof (cof Φ.shift ψ).shift ψ2).Scoped (Ψ + 1 + 1) := ⟨hR2s, hψ2s⟩
  have hXa : (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXb : (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXaΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hXbΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have ha2 : VTy S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) Γ.dshift.dshift
      a.dshift.dshift A.dshift := by
    have h1 := VTy.restrict' hW hXa (ent_trans hXaΦ hR2Φ) (VTy.dwk' hW (VTy.dwk' hW ha))
    have hf := VEq.faceU' hW (i := 1) (d := false) hv1 (ent_and_right _ _) (VTy.restrict' hW hXa hXaΦ hA2)
    rw [dshift_dset1_zero] at hf
    exact VTy.conv' hW h1 (VEq.symm' hW hf)
  have hb2 : VTy S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) Γ.dshift.dshift
      b.dshift.dshift A.dshift := by
    have h1 := VTy.restrict' hW hXb (ent_trans hXbΦ hR2Φ) (VTy.dwk' hW (VTy.dwk' hW hb))
    have hf := VEq.faceU' hW (i := 1) (d := true) hv1 (ent_and_right _ _) (VTy.restrict' hW hXb hXbΦ hA2)
    rw [dshift_dset1_one] at hf
    exact VTy.conv' hW h1 (VEq.symm' hW hf)
  have hXab : (cof (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (.var 1)).Scoped (Ψ + 1 + 1) :=
    ⟨hXa, hv1⟩
  have hinner : VTy S (Ψ + 1 + 1) (cof (cof Φ.shift ψ).shift ψ2) Γ.dshift.dshift
      (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift) A.dshift :=
    VTy.split' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _)
      (VTy.restrict' hW hΞ2s (ent_and_left _ _) hA2).ty ha2 hb2
      (VEq.absurd' hW (ent_contra _ 1) (VTy.restrict' hW hXab (ent_and_left _ _) ha2).ty
        (VTy.restrict' hW hXab (ent_and_mono (ent_and_left _ _) (ent_refl _)) hb2).ty)
  -- agreement of the tube with the inner system
  have hY : (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2).Scoped (Ψ + 1 + 1) := ⟨hR3, hψ2s⟩
  have hover : VEq S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) Γ.dshift.dshift
      (.papp (u.dsubst insI) (.var 1)) (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)
      A.dshift := by
    have hYU := VTy.restrict' hW hY (ent_and_left _ _) hUr
    have hYI := VTy.restrict' hW hY (ent_and_mono (ent_and_left _ _) (ent_refl _)) hinner
    have hYA := VTy.restrict' hW hY (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA2
    have hpu := VTy.restrict' hW hY (ent_trans (ent_and_left _ _) hR3e) hu2
    refine VEq.local' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _) hYU hYI ?_ ?_
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have e1 := VEq.face' hW (i := 1) (d := false) hv1 (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_and_left _ _) hYA).ty (VTy.restrict' hW hs1 (ent_and_left _ _) hYU)
      rw [papp_insI_dset1] at e1
      have e2 := VEq.pathZero' hW (VTy.restrict' hW hs1 (ent_and_left _ _) hpu)
      rw [Xp_zero] at e2
      have hf := VEq.faceU' hW (i := 1) (d := false) hv1 (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_and_left _ _) hYA)
      rw [dshift_dset1_zero] at hf
      have e3 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hs1 (ent_and_left _ _) hYI)
      exact VEq.trans' hW e1 (VEq.trans' hW (VEq.conv' hW e2 (VEq.symm' hW hf)) (VEq.symm' hW e3))
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have hs2 : (cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))) (.var 1)).Scoped
          (Ψ + 1 + 1) := ⟨⟨hY, hv1⟩, hv1⟩
      have e1 := VEq.face' hW (i := 1) (d := true) hv1 (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_and_left _ _) hYA).ty (VTy.restrict' hW hs1 (ent_and_left _ _) hYU)
      rw [papp_insI_dset1] at e1
      have e2 := VEq.pathOne' hW (VTy.restrict' hW hs1 (ent_and_left _ _) hpu)
      rw [Xp_one] at e2
      have hf := VEq.faceU' hW (i := 1) (d := true) hv1 (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_and_left _ _) hYA)
      rw [dshift_dset1_one] at hf
      have hXY : I.Entails (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (cof (cof Φ.shift ψ).shift ψ2) :=
        ent_and_mono (ent_and_left _ _) (ent_refl _)
      have hX1 : I.Entails (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1))
          (cof (cof Φ.shift ψ).shift ψ2) := ent_trans (ent_and_left _ _) hXY
      have hXb' : I.Entails (cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)) (.var 1))
          (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) :=
        ent_and_intro (ent_trans (ent_and_left _ _) hX1) (ent_and_right _ _)
      have hXa' : I.Entails (cof (cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)) (.neg (.var 1)))
          (.var 1)) (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hX1))
          (ent_trans (ent_and_left _ _) (ent_and_right _ _))
      have hXb'' : I.Entails (cof (cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)) (.neg (.var 1)))
          (.var 1)) (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hX1)) (ent_and_right _ _)
      have hs3 : (cof (cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)) (.neg (.var 1)))
          (.var 1)).Scoped (Ψ + 1 + 1) := ⟨⟨hs1, hv1⟩, hv1⟩
      have e3 := VEq.splitR' hW (φ := .neg (.var 1)) hv1 hv1 (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_and_left _ _) hYI)
        (VTy.restrict' hW ⟨hs1, hv1⟩ hXb' hb2)
        (VEq.absurd' hW (ent_contra _ 1) (VTy.restrict' hW hs3 hXa' ha2).ty (VTy.restrict' hW hs3 hXb'' hb2).ty)
      exact VEq.trans' hW e1 (VEq.trans' hW (VEq.conv' hW e2 (VEq.symm' hW hf)) (VEq.symm' hW e3))
  have hsys : VTy S (Ψ + 1 + 1) (cof Φ.shift ψ).shift Γ.dshift.dshift
      (.split φ.shift.shift (.papp (u.dsubst insI) (.var 1)) ψ2
        (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)) A.dshift :=
    VTy.split' hW hφ2 hψ2s (ent_shift (ent_and_right Φ.shift ψ)) hA2.ty hUr hinner hover
  -- the base
  have hv0' : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hp0d : VTy S (Ψ + 1) Φ.shift Γ.dshift p0.dshift (.path (A.ren id (Tm.upRen Nat.succ)) a.dshift b.dshift) :=
    VTy.dwk' hW hp0p
  have hbase := VTy.papp' hW hp0d hv0'
  rw [upDShift_dinst0] at hbase
  -- the side condition of the composition
  have hsys0 : VTy S (Ψ + 1) (cof Φ.shift ψ) Γ.dshift
      ((Tm.split φ.shift.shift (.papp (u.dsubst insI) (.var 1)) ψ2
        (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)).dinst .zero) (A.dshift.dinst .zero) :=
    VTy.dsubst' hW .zero trivial hsys
  rw [dshift_dinst, sys0_eq] at hsys0
  have hinner0 : VTy S (Ψ + 1) (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) Γ.dshift
      ((Tm.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift).dinst .zero) (A.dshift.dinst .zero) :=
    VTy.dsubst' hW (Φ := cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (Γ := Γ.dshift) .zero trivial hinner
  rw [dshift_dinst, inner0_eq] at hinner0
  have hover0 : VEq S (Ψ + 1) (cof (cof (cof Φ.shift ψ) φ.shift) (.or (.neg (.var 0)) (.var 0))) Γ.dshift
      ((Tm.papp (u.dsubst insI) (.var 1)).dinst .zero)
      ((Tm.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift).dinst .zero) (A.dshift.dinst .zero) :=
    VEq.dsubst' hW (Φ := cof (cof (cof Φ.shift ψ) φ.shift) (.or (.neg (.var 0)) (.var 0))) (Γ := Γ.dshift)
      .zero trivial hover
  have epu0 : (Tm.papp (u.dsubst insI) (.var 1)).dinst .zero = .papp (u.dinst .zero).dshift (.var 0) := by
    show Tm.papp ((u.dsubst insI).dinst .zero) ((I.var 1).subst (I.inst0 .zero)) = _
    rw [dsubst_insI_dinst0]; rfl
  rw [dshift_dinst, inner0_eq, epu0] at hover0
  have hside' : VEq S (Ψ + 1) (cof Φ.shift ψ) Γ.dshift
      (.split φ.shift (.papp (u.dinst .zero).dshift (.var 0)) (.or (.neg (.var 0)) (.var 0))
        (.split (.neg (.var 0)) a.dshift (.var 0) b.dshift)) (.papp p0.dshift (.var 0)) A := by
    have hΞA := VTy.restrict' hW hΞs (ent_and_left _ _) hA
    have hΞb := VTy.restrict' hW hΞs (ent_and_left _ _) hbase
    refine VEq.local' hW (φ := φ.shift) (ψ := .or (.neg (.var 0)) (.var 0)) (KubusCore.I.scoped_shift hφ)
      ⟨hv0', hv0'⟩ (ent_and_right _ _) hsys0 hΞb ?_ ?_
    · have hs1 : (cof (cof Φ.shift ψ) φ.shift).Scoped (Ψ + 1) := ⟨hΞs, KubusCore.I.scoped_shift hφ⟩
      have s1 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hs1 (ent_and_left _ _) hsys0)
      have hsd := VEq.dwk' hW hsidep
      have hsd1 := VEq.restrict' hW hs1
        (ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)) hsd
      have s2 := VEq.papp' hW (L := A.ren id (Tm.upRen Nat.succ)) (a := a.dshift) (b := b.dshift) hsd1 hv0' hv0'
        (I_eq_refl _)
      rw [upDShift_dinst0] at s2
      exact VEq.trans' hW s1 s2
    · have hs1 : (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))).Scoped (Ψ + 1) := ⟨hΞs, ⟨hv0', hv0'⟩⟩
      have t1 := VEq.splitR' hW (ψ := .or (.neg (.var 0)) (.var 0)) (KubusCore.I.scoped_shift hφ) ⟨hv0', hv0'⟩ (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_and_left _ _) hsys0)
        (VTy.restrict' hW ⟨hs1, ⟨hv0', hv0'⟩⟩ (ent_and_left _ _) hinner0)
        (VEq.restrict' hW ⟨⟨hs1, KubusCore.I.scoped_shift hφ⟩, ⟨hv0', hv0'⟩⟩
          (ent_and_mono (ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _))
            (ent_refl _)) hover0)
      refine VEq.trans' hW t1 ?_
      have hs2a : (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.neg (.var 0))).Scoped (Ψ + 1) :=
        ⟨hs1, hv0'⟩
      have hs2b : (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)).Scoped (Ψ + 1) := ⟨hs1, hv0'⟩
      refine VEq.local' hW (φ := .neg (.var 0)) (ψ := .var 0) hv0' hv0' (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_refl _) hinner0) (VTy.restrict' hW hs1 (ent_and_left _ _) hΞb) ?_ ?_
      · have e1 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hs2a (ent_and_left _ _) hinner0)
        have hA3 := VTy.restrict' hW hs2a (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞA
        have e2 := VEq.face' hW (i := 0) (d := false) hv0' (ent_and_right _ _) hA3.ty
          (VTy.restrict' hW hs2a (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞb)
        rw [papp_dshift_dset0] at e2
        have e3 := VEq.pathZero' hW (VTy.restrict' hW hs2a
          (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)) hp0d)
        rw [show (A.ren id (Tm.upRen Nat.succ)).dinst .zero = (A.dinst .zero).dshift from upDShift_dinst_dir A false]
          at e3
        have hf := VEq.faceU' hW (i := 0) (d := false) hv0' (ent_and_right _ _) hA3
        rw [dset0_eq] at hf
        exact VEq.trans' hW e1 (VEq.symm' hW (VEq.trans' hW e2 (VEq.conv' hW e3 (VEq.symm' hW hf))))
      · have hs4 : (cof (cof (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)) (.neg (.var 0)))
            (.var 0)).Scoped (Ψ + 1) := ⟨⟨hs2b, hv0'⟩, hv0'⟩
        have hinb := VTy.restrict' hW hs2b (ent_and_left _ _) hinner0
        have hA3 := VTy.restrict' hW hs2b (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞA
        have hf' := VEq.faceU' hW (i := 0) (d := true) hv0' (ent_and_right _ _) hA3
        rw [dset0_eq] at hf'
        have hbI : VTy S (Ψ + 1) (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)) Γ.dshift
            b.dshift A :=
          VTy.conv' hW (VTy.restrict' hW hs2b
            (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)) (VTy.dwk' hW hb))
            (VEq.symm' hW hf')
        have hs4e : I.Entails (cof (cof (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0))
            (.neg (.var 0))) (.var 0)) (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)) :=
          ent_trans (ent_and_left _ _) (ent_and_left _ _)
        have hA4 := VTy.restrict' hW hs4 hs4e hA3
        have hf4 := VEq.faceU' hW (i := 0) (d := false) hv0' (ent_trans (ent_and_left _ _) (ent_and_right _ _)) hA4
        rw [dset0_eq] at hf4
        have haI : VTy S (Ψ + 1) _ Γ.dshift a.dshift A :=
          VTy.conv' hW (VTy.restrict' hW hs4
            (ent_trans hs4e (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)))
            (VTy.dwk' hW ha)) (VEq.symm' hW hf4)
        have e1 := VEq.splitR' hW (φ := .neg (.var 0)) (ψ := .var 0) hv0' hv0' (ent_and_right _ _) hinb
          (VTy.restrict' hW ⟨hs2b, hv0'⟩ (ent_and_left _ _) hbI)
          (VEq.absurd' hW (ent_contra _ 0) haI.ty (VTy.restrict' hW hs4 hs4e hbI).ty)
        have e2 := VEq.face' hW (i := 0) (d := true) hv0' (ent_and_right _ _) hA3.ty
          (VTy.restrict' hW hs2b (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞb)
        rw [papp_dshift_dset0] at e2
        have e3 := VEq.pathOne' hW (VTy.restrict' hW hs2b
          (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)) hp0d)
        rw [show (A.ren id (Tm.upRen Nat.succ)).dinst .one = (A.dinst .one).dshift from upDShift_dinst_dir A true]
          at e3
        exact VEq.trans' hW e1 (VEq.symm' hW (VEq.trans' hW e2 (VEq.conv' hW e3 (VEq.symm' hW hf'))))
  have hside'' : VEq S (Ψ + 1) (cof Φ.shift ψ) Γ.dshift
      ((Tm.split φ.shift.shift (.papp (u.dsubst insI) (.var 1)) ψ2
        (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)).dinst .zero)
      (.papp p0.dshift (.var 0)) A := by rw [sys0_eq]; exact hside'
  have hbody := VTy.hcomp' hW hA hψs hsys hbase hside''
  -- the endpoints
  have key : ∀ d : Bool,
      VEq S Ψ Φ Γ ((Tm.hcomp A ψ (.split φ.shift.shift (.papp (u.dsubst insI) (.var 1)) ψ2
          (.split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift))
          (.papp p0.dshift (.var 0))).dinst (I.ofDir d))
        (.split (.neg (I.ofDir d)) a (I.ofDir d) b) (A.dinst (I.ofDir d)) ∧
      VTy S Ψ Φ Γ (.split (.neg (I.ofDir d)) a (I.ofDir d) b) (A.dinst (I.ofDir d)) := by
    intro d
    have hdd : (I.ofDir d).Scoped Ψ := by cases d <;> trivial
    have hor : I.Entails Φ (.or (.neg (I.ofDir d)) (I.ofDir d)) := by
      cases d
      · exact ent_negzero_or Φ
      · exact ent_one_or Φ
    have hb0 := VTy.dsubst' hW _ hdd hbody
    have e1 := VEq.hcompFace' hW (ent_trans hor (ent_or_right _ _)) hb0
    rw [dsub_end, sysEnd_eq] at e1
    have hΦ2 : I.Entails Φ (Φ.shift.shift.subst (endS d)) := ent_shift2_endS Φ d
    have hψE : I.Entails Φ ((cof Φ.shift ψ).shift.subst (endS d)) :=
      ent_and_intro hΦ2 (ent_trans hor (ent_or_right _ _))
    have hsysE := VTy.endS' hW d hR2s hψE hw0 hsys
    rw [dshift_endS, sysEnd_eq] at hsysE
    have hinE := VTy.endS' hW d hΞ2s (ent_and_intro hψE hor) hw0 hinner
    rw [dshift_endS, inner_endS] at hinE
    have hcφ : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
    have hcφo : (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d))).Scoped Ψ := ⟨hcφ, ⟨hdd, hdd⟩⟩
    have hoE : I.Entails (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d)))
        ((cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2).subst (endS d)) := by
      have h1 : I.Entails (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d))) Φ :=
        ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have h2 : I.Entails (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d))) (φ.shift.shift.subst (endS d)) := by
        rw [shift2_endS]; exact ent_trans (ent_and_left _ _) (ent_and_right _ _)
      exact ent_and_intro (ent_and_intro (ent_trans h1 hψE) h2) (ent_and_right _ _)
    have hwo := Wf0.restrict hw0 hcφo (ent_trans (ent_and_left _ _) (ent_and_left _ _))
    have hovE := VEq.endS' hW d hY hoE hwo hover
    rw [dshift_endS, inner_endS, papp_endS] at hovE
    have e2 := VEq.splitR' hW (φ := φ) (ψ := .or (.neg (I.ofDir d)) (I.ofDir d)) hφ ⟨hdd, hdd⟩ hor hsysE (VTy.restrict' hW ⟨hs, ⟨hdd, hdd⟩⟩ (ent_and_left _ _) hinE)
      hovE
    exact ⟨VEq.trans' hW e1 e2, hinE⟩
  have e0 := VEq.trans' hW (key false).1 (VEq.splitL' hW (ent_negzero Φ) (key false).2)
  have hz1 : I.Entails (cof (cof Φ (.neg .one)) .one) .zero :=
    ent_trans (ent_trans (ent_and_left _ _) (ent_and_right _ _))
      (ent_trans (ent_or_right .zero (.neg .one)) (ent_neg_one .zero))
  have hz1s : (cof (cof Φ (.neg .one)) .one).Scoped Ψ := ⟨⟨hs, trivial⟩, trivial⟩
  have hz1e : I.Entails (cof (cof Φ (.neg .one)) .one) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have e1 := VEq.trans' hW (key true).1
    (VEq.splitR' hW trivial trivial (ent_one Φ) (key true).2
      (VTy.restrict' hW (Φ' := cof Φ .one) ⟨hs, trivial⟩ (ent_and_left _ _) hb)
      (VEq.absurd' hW hz1
        (VTy.conv' hW (VTy.restrict' hW (Φ' := cof (cof Φ (.neg .one)) .one) ⟨⟨hs, trivial⟩, trivial⟩
          (ent_trans (ent_and_left _ _) (ent_and_left _ _)) ha)
          (VEq.absurd' hW hz1 (VTy.restrict' hW hz1s hz1e (VTy.dsubst' hW .zero trivial hA)).ty
            (VTy.restrict' hW hz1s hz1e (VTy.dsubst' hW .one trivial hA)).ty)).ty
        (VTy.restrict' hW (Φ' := cof (cof Φ (.neg .one)) .one) ⟨⟨hs, trivial⟩, trivial⟩
          (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hb).ty))
  exact ⟨hbody, VTy.plam' hW hPp hbody e0 e1⟩

theorem valid_hcompPath_rule {A a b u p0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.hcomp (.path A a b) φ u p0) T)
    (hv : Valid2 S Ψ Φ Γ (.hcomp (.path A a b) φ u p0) (.hcomp (.path A a b) φ u p0) T)
    (hinv : HcompInv S Ψ Φ Γ (.path A a b) φ u p0 T) :
    Valid2 S Ψ Φ Γ (.hcomp (.path A a b) φ u p0) (Tm.hcompPath A a b φ u p0) T := by
  obtain ⟨l, hφ, hPV, huV, hu0V, hsV, htr, hP, hu, hu0, hside⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hP
  have hX : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hPp : VTy S Ψ Φ Γ (.path A a b) (.univ l) := ⟨hP, hPV⟩
  have hup : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (Tm.path A a b).dshift := ⟨hu, huV⟩
  have hu0p : VTy S Ψ Φ Γ p0 (.path A a b) := ⟨hu0, hu0V⟩
  have hsidep : VEq S Ψ (cof Φ φ) Γ (u.dinst .zero) p0 (.path A a b) := ⟨hside, hsV⟩
  obtain ⟨hbody, hy⟩ := VTy.hcompPath' hW hPp hφ hup hu0p hsidep
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hy.v htr hT
  -- where the face holds: η for the tube's end, and the face of the body
  have hX0Φ : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have hu1 : VTy S Ψ (cof Φ φ) Γ (u.dinst .one) (.path A a b) := by
    refine ⟨?_, valid_tube_end hW hφ .one trivial huV hu hP⟩
    have := HasTy0.dsubst hS (Φ := cof Φ φ) hu (r := .one) trivial
    rwa [dshift_dinst] at this
  have hη := VEq.pathEta' hW hu1
  have hpl : VTy S Ψ (cof Φ φ) Γ (.plam (.papp (u.dinst .one).dshift (.var 0))) (.path A a b) :=
    ⟨(presup hW hη.eq).2, valid_trans hW (valid_symm hW hη.v) hη.v⟩
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hX
  have hbX := VTy.restrict' hW hXs (ent_shift hX0Φ) hbody
  have e1 := VEq.hcompFace' hW (ent_trans (ent_shift (ent_and_right Φ φ)) (ent_or_left _ _)) hbX
  rw [sys1_eq] at e1
  have hsysX : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift _ A := ⟨(presup hW e1.eq).2, valid_trans hW (valid_symm hW e1.v) e1.v⟩
  have e2 := VEq.splitL' hW (ent_shift (ent_and_right Φ φ)) hsysX
  have hbe := VEq.plam' hW (VTy.restrict' hW hX hX0Φ hPp) hpl (VTy.restrict' hW hX hX0Φ hy).ty
    (VEq.symm' hW (VEq.trans' hW e1 e2))
  have hb := valid_conv_tr (VEq.trans' hW hη hbe).v (htr.restrict hX0Φ) fun k c => hT k (c.restrictTo hX0Φ)
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e4 : c.L (Tm.hcompPath A a b φ u p0) = Tm.hcompPath (A.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)
        (φ.subst c.σ.τ) (u.subst (dupS c.γ) (I.up c.σ.τ)) (c.L p0) := hcompPath_subst _ _ A a b φ u p0
    rw [e4]
    exact ⟨.step (step_hcomp_path hn) (.refl _), EqTm.hcompPath (c.ty hW h)⟩
  · rw [CSub2.L_dinst hW]
    exact ⟨.step (step_hcomp_face hf) (.refl _), EqTm.hcompFace hf (c.ty hW h)⟩

/-! ### `transp` in path types -/

theorem VEq.lty' {t u A : Tm} (h : VEq S Ψ Φ Γ t u A) : VTy S Ψ Φ Γ t A :=
  ⟨(presup hW h.eq).1, valid_trans hW h.v (valid_symm hW h.v)⟩

theorem VEq.rty' {t u A : Tm} (h : VEq S Ψ Φ Γ t u A) : VTy S Ψ Φ Γ u A :=
  ⟨(presup hW h.eq).2, valid_trans hW (valid_symm hW h.v) h.v⟩

omit hW in
theorem swapI_sc2 (Ψ : ℕ) : ∀ i < 2, (swapI i).Scoped (Ψ + 2) := fun i hi => by
  rcases i with _ | _ | i
  · show 1 < Ψ + 2; omega
  · show 0 < Ψ + 2; omega
  · omega

theorem VTy.swap' {Φs : I} {t A : Tm} (hΦs : Φs.Scoped Ψ)
    (h : VTy S (Ψ + 1 + 1) Φs.shift.shift Γ.dshift.dshift t A) :
    VTy S (Ψ + 1 + 1) Φs.shift.shift Γ.dshift.dshift (t.dsubst swapI) (A.dsubst swapI) := by
  have h' : VTy S (Ψ + 2) Φs.shift.shift (Ctx.dren 2 Γ) t A := by rw [Ctx.dren_two]; exact h
  have := VTy.isubL hW (n := 2) (m := 2) (Ψ0 := Ψ) (Γ0 := Γ) swapI (swapI_sc2 Ψ) (fun i => rfl)
    (KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hΦs)) (by rw [I_shift2_swap]; exact ent_refl _)
    (by rw [Ctx.dren_two]; exact wf_of_ty h.ty) h'
  rwa [Ctx.dren_two] at this

theorem VEq.swap' {Φs : I} {t u A : Tm} (hΦs : Φs.Scoped Ψ)
    (h : VEq S (Ψ + 1 + 1) Φs.shift.shift Γ.dshift.dshift t u A) :
    VEq S (Ψ + 1 + 1) Φs.shift.shift Γ.dshift.dshift (t.dsubst swapI) (u.dsubst swapI) (A.dsubst swapI) := by
  have h' : VEq S (Ψ + 2) Φs.shift.shift (Ctx.dren 2 Γ) t u A := by rw [Ctx.dren_two]; exact h
  have := VEq.isubL hW (n := 2) (m := 2) (Ψ0 := Ψ) (Γ0 := Γ) swapI (swapI_sc2 Ψ) (fun i => rfl)
    (KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hΦs)) (by rw [I_shift2_swap]; exact ent_refl _)
    (by rw [Ctx.dren_two]; exact wf_of_eq h.eq) h'
  rwa [Ctx.dren_two] at this

theorem VEq.tubeSkip {Φs : I} {t u X : Tm} (hΦs : Φs.Scoped Ψ) (h : VEq S (Ψ + 1) Φs.shift Γ.dshift t u X) :
    VEq S (Ψ + 1 + 1) Φs.shift.shift Γ.dshift.dshift (t.dsubst insI) (u.dsubst insI) (X.dsubst insI) := by
  have := VEq.bind2' hW (X := Φs.shift.shift) (r := .var 0) (show (0 : ℕ) < Ψ + 2 by omega) hΦs (ent_refl _)
    ((wf_unshift (sigClosed_of_wfSig hW) (wf_of_eq h.eq)).dwk2 (sigClosed_of_wfSig hW)) h
  rwa [bind2_var0] at this

omit hW in
theorem tp_sys1 (φ : I) (p0 a b : Tm) :
    (Tm.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))).dinst .one =
      .split φ.shift (.papp p0.dshift (.var 0)) (.or (.neg (.var 0)) (.var 0))
        (.split (.neg (.var 0)) (a.dinst .one).dshift (.var 0) (b.dinst .one).dshift) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; rfl
  · congr 1; ssub2
  · congr 1 <;> ssub2

omit hW in
theorem tp_A01 (A : Tm) : (A.dinst .zero).dinst .one = ((A.dsubst swapI).dinst .one).dinst (I.ofDir false) := by
  ssub2

omit hW in
theorem tp_A11 (A : Tm) : (A.dinst .one).dinst .one = ((A.dsubst swapI).dinst .one).dinst (I.ofDir true) := by
  ssub2

omit hW in
theorem tp_pappEnd (p0 : Tm) (d : Bool) :
    (Tm.papp p0.dshift.dshift (.var 1)).subst Tm.var (endS d) = .papp p0 (I.ofDir d) := by
  have h := tp_sysEnd .zero p0 (.var 0) (.var 0) d
  simp only [Tm.subst] at h ⊢
  injection h with _ h1

/-- The contractum of `transpPath`, typed and valid. -/
theorem VTy.transpPath' {A a b p0 : Tm} {φ : I} {l : ℕ}
    (hLp : VTy S (Ψ + 1) Φ.shift Γ.dshift (.path A a b) (.univ l)) (hφ : φ.Scoped Ψ)
    (hcp : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (.path A a b) ((Tm.path A a b).dinst .zero).dshift (.univ l))
    (hu0p : VTy S Ψ Φ Γ p0 ((Tm.path A a b).dinst .zero)) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.comp (A.dsubst swapI) (.or φ.shift (.or (.neg (.var 0)) (.var 0)))
      (.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI)))
      (.papp p0.dshift (.var 0))) ((A.dsubst swapI).dinst .one) ∧
    VTy S Ψ Φ Γ (Tm.transpPath A a b φ p0) ((Tm.path A a b).dinst .one) := by
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hu0p.ty
  have hw0 := wf_of_ty hu0p.ty
  have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  obtain ⟨hAl, ha, hb⟩ := VTy.pathParts hW hLp
  have hCc := VTy.swap' hW hs hAl
  rw [univ_dsubst] at hCc
  -- constancy of the swapped line on `φ`
  have hcd := VEq.dwk' hW hcp
  have hci := VEq.pathInjLine' hW (L := A.ren id (Tm.upRen Nat.succ))
    (L' := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ)).ren id (Tm.upRen Nat.succ))
    (r := .var 0) hcd (show 0 < Ψ + 1 + 1 by omega)
  rw [ipi_c1, ipi_c2] at hci
  have hcC := VEq.swap' hW (Φs := cof Φ φ) hs' hci
  rw [ipi_c3, univ_dsubst] at hcC
  -- contexts
  let ψ : I := .or φ.shift (.or (.neg (.var 0)) (.var 0))
  have hv0' : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hψs : ψ.Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hφ, ⟨hv0', hv0'⟩⟩
  have hΞs : (cof Φ.shift ψ).Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hs, hψs⟩
  have hR2s : (cof Φ.shift ψ).shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift hΞs
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hφ)
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  let ψ2 : I := .or (.neg (.var 1)) (.var 1)
  have hψ2s : ψ2.Scoped (Ψ + 1 + 1) := ⟨hv1, hv1⟩
  have hR2Φ : I.Entails (cof Φ.shift ψ).shift Φ.shift.shift := ent_shift (ent_and_left Φ.shift ψ)
  have hCc2 := VTy.restrict' hW hR2s hR2Φ hCc
  -- the tube on `φ`: `p0 j`
  have hp0dd := VTy.dwk' hW (VTy.dwk' hW hu0p)
  have hP := VTy.papp' hW (L := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ)).ren id
    (Tm.upRen Nat.succ)) hp0dd hv1
  rw [tp_P] at hP
  have hR3 : (cof (cof Φ.shift ψ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hR2s, hφ2⟩
  have hR3e : I.Entails (cof (cof Φ.shift ψ).shift φ.shift.shift) (cof Φ φ).shift.shift :=
    ent_and_intro (ent_trans (ent_and_left _ _) hR2Φ) (ent_and_right _ _)
  have hPr : VTy S (Ψ + 1 + 1) (cof (cof Φ.shift ψ).shift φ.shift.shift) Γ.dshift.dshift
      (.papp p0.dshift.dshift (.var 1)) (A.dsubst swapI) :=
    VTy.conv' hW (VTy.restrict' hW hR3 (ent_trans (ent_and_left _ _) hR2Φ) hP)
      (VEq.symm' hW (VEq.restrict' hW hR3 hR3e hcC))
  -- the inner system `[j = 0 ↦ a, j = 1 ↦ b]`
  have hΞ2s : (cof (cof Φ.shift ψ).shift ψ2).Scoped (Ψ + 1 + 1) := ⟨hR2s, hψ2s⟩
  have hXa : (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXb : (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXaΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hXbΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have haI : VTy S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) Γ.dshift.dshift
      (a.dsubst insI) (A.dsubst swapI) := by
    have h1 := VTy.restrict' hW hXa (ent_trans hXaΦ hR2Φ) (VTy.tubeSkip hW hs ha)
    rw [tp_end0] at h1
    have hf := VEq.faceU' hW (i := 1) (d := false) hv1 (ent_and_right _ _) (VTy.restrict' hW hXa hXaΦ hCc2)
    exact VTy.conv' hW h1 (VEq.symm' hW hf)
  have hbI : VTy S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) Γ.dshift.dshift
      (b.dsubst insI) (A.dsubst swapI) := by
    have h1 := VTy.restrict' hW hXb (ent_trans hXbΦ hR2Φ) (VTy.tubeSkip hW hs hb)
    rw [tp_end1] at h1
    have hf := VEq.faceU' hW (i := 1) (d := true) hv1 (ent_and_right _ _) (VTy.restrict' hW hXb hXbΦ hCc2)
    exact VTy.conv' hW h1 (VEq.symm' hW hf)
  have hXab : (cof (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (.var 1)).Scoped (Ψ + 1 + 1) :=
    ⟨hXa, hv1⟩
  have hinner : VTy S (Ψ + 1 + 1) (cof (cof Φ.shift ψ).shift ψ2) Γ.dshift.dshift
      (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI)) (A.dsubst swapI) :=
    VTy.split' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _)
      (VTy.restrict' hW hΞ2s (ent_and_left _ _) hCc2).ty haI hbI
      (VEq.absurd' hW (ent_contra _ 1) (VTy.restrict' hW hXab (ent_and_left _ _) haI).ty
        (VTy.restrict' hW hXab (ent_and_mono (ent_and_left _ _) (ent_refl _)) hbI).ty)
  -- agreement of the tube with the inner system
  have hC0d : VTy S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift ((A.dsubst swapI).dinst .zero).dshift (.univ l) :=
    VTy.dwk' hW (VTy.dsubst' hW .zero trivial hCc)
  have hcl' := VEq.tubeSkip hW hs' (VEq.pathInjLeft' hW (a' := (a.dinst .zero).dshift) hcp)
  rw [tp_a0, tp_end0] at hcl'
  have hcr' := VEq.tubeSkip hW hs' (VEq.pathInjRight' hW (b' := (b.dinst .zero).dshift) hcp)
  rw [tp_a0, tp_end1] at hcr'
  have hY : (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2).Scoped (Ψ + 1 + 1) := ⟨hR3, hψ2s⟩
  have hover : VEq S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) Γ.dshift.dshift
      (.papp p0.dshift.dshift (.var 1)) (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))
      (A.dsubst swapI) := by
    have hYU := VTy.restrict' hW hY (ent_and_left _ _) hPr
    have hYI := VTy.restrict' hW hY (ent_and_mono (ent_and_left _ _) (ent_refl _)) hinner
    have hYΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) Φ.shift.shift :=
      ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hR2Φ)
    have hYc : I.Entails (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (cof Φ φ).shift.shift :=
      ent_trans (ent_and_left _ _) hR3e
    refine VEq.local' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _) hYU hYI ?_ ?_
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have hWe := ent_and_left (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))
      have hWA := VTy.restrict' hW hs1 (ent_trans hWe hYΦ) hCc
      have e1 := VEq.face' hW (i := 1) (d := false) hv1 (ent_and_right _ _) hWA.ty (VTy.restrict' hW hs1 hWe hYU)
      rw [tp_Pdset] at e1
      have e2 := VEq.pathZero' hW (VTy.restrict' hW hs1 (ent_trans hWe hYΦ) hp0dd)
      have hz := VEq.faceU' hW (i := 1) (d := false) hv1 (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_trans hWe hYΦ) hC0d)
      rw [tp_Z] at hz
      have eT := VEq.trans' hW (VEq.restrict' hW hs1 (ent_trans hWe hYc) hcC) hz
      have hf := VEq.faceU' hW (i := 1) (d := false) hv1 (ent_and_right _ _) hWA
      have e3 := VEq.conv' hW (VEq.restrict' hW hs1 (ent_trans hWe hYc) hcl') (VEq.symm' hW hf)
      have e4 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hs1 hWe hYI)
      exact VEq.trans' hW e1 (VEq.trans' hW (VEq.conv' hW e2 (VEq.symm' hW eT))
        (VEq.trans' hW (VEq.symm' hW e3) (VEq.symm' hW e4)))
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have hWe := ent_and_left (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)
      have hWA := VTy.restrict' hW hs1 (ent_trans hWe hYΦ) hCc
      have e1 := VEq.face' hW (i := 1) (d := true) hv1 (ent_and_right _ _) hWA.ty (VTy.restrict' hW hs1 hWe hYU)
      rw [tp_Pdset] at e1
      have e2 := VEq.pathOne' hW (VTy.restrict' hW hs1 (ent_trans hWe hYΦ) hp0dd)
      have hz := VEq.faceU' hW (i := 1) (d := true) hv1 (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_trans hWe hYΦ) hC0d)
      rw [tp_Z] at hz
      have eT := VEq.trans' hW (VEq.restrict' hW hs1 (ent_trans hWe hYc) hcC) hz
      have hf := VEq.faceU' hW (i := 1) (d := true) hv1 (ent_and_right _ _) hWA
      have e3 := VEq.conv' hW (VEq.restrict' hW hs1 (ent_trans hWe hYc) hcr') (VEq.symm' hW hf)
      have hs2 : (cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)) (.neg (.var 1))).Scoped
          (Ψ + 1 + 1) := ⟨hs1, hv1⟩
      have hYIb := VTy.restrict' hW hs1 hWe hYI
      have hb1 := VTy.restrict' hW (Φ' := cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1))
        (.var 1)) ⟨hs1, hv1⟩ (ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans hWe
          (ent_and_mono (ent_and_left _ _) (ent_refl _)))) (ent_and_right _ _)) hbI
      have hs3 : (cof (cof (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)) (.neg (.var 1)))
          (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hs2, hv1⟩
      have e4 := VEq.splitR' hW (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _) hYIb hb1
        (VEq.absurd' hW (ent_contra _ 1)
          (VTy.restrict' hW hs3 (ent_and_intro (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _)
            (ent_trans hWe (ent_and_mono (ent_and_left _ _) (ent_refl _))))) (ent_trans (ent_and_left _ _)
              (ent_and_right _ _))) haI).ty
          (VTy.restrict' hW hs3 (ent_and_mono (ent_and_left _ _) (ent_refl _)) hb1).ty)
      exact VEq.trans' hW e1 (VEq.trans' hW (VEq.conv' hW e2 (VEq.symm' hW eT))
        (VEq.trans' hW (VEq.symm' hW e3) (VEq.symm' hW e4)))
  have hsys : VTy S (Ψ + 1 + 1) (cof Φ.shift ψ).shift Γ.dshift.dshift
      (.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) ψ2
        (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))) (A.dsubst swapI) :=
    VTy.split' hW hφ2 hψ2s (ent_shift (ent_and_right Φ.shift ψ)) hCc2.ty hPr hinner hover
  -- the base
  have hp0d := VTy.dwk' hW hu0p
  have hbase := VTy.papp' hW (L := (A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ)) hp0d hv0'
  rw [ipi_c4] at hbase
  -- the side condition
  have hC0 := VTy.dsubst' hW .zero trivial hCc
  have hsys0 := VTy.dsubst' hW .zero trivial hsys
  rw [tp_sys0] at hsys0
  have hinner0 := VTy.dsubst' hW (Φ := cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (Γ := Γ.dshift)
    .zero trivial hinner
  rw [tp_inner0] at hinner0
  have hover0 := VEq.dsubst' hW (Φ := cof (cof (cof Φ.shift ψ) φ.shift) (.or (.neg (.var 0)) (.var 0)))
    (Γ := Γ.dshift) .zero trivial hover
  rw [tp_inner0, show (Tm.papp p0.dshift.dshift (.var 1)).dinst .zero = .papp p0.dshift (.var 0) by
    show Tm.papp (p0.dshift.dshift.dinst .zero) _ = _; rw [dshift_dinst]; rfl] at hover0
  have hside' : VEq S (Ψ + 1) (cof Φ.shift ψ) Γ.dshift
      (.split φ.shift (.papp p0.dshift (.var 0)) (.or (.neg (.var 0)) (.var 0))
        (.split (.neg (.var 0)) (a.dinst .zero).dshift (.var 0) (b.dinst .zero).dshift))
      (.papp p0.dshift (.var 0)) ((A.dsubst swapI).dinst .zero) := by
    have hΞA := VTy.restrict' hW hΞs (ent_and_left _ _) hC0
    have hΞb := VTy.restrict' hW hΞs (ent_and_left _ _) hbase
    refine VEq.local' hW (φ := φ.shift) (ψ := .or (.neg (.var 0)) (.var 0)) (KubusCore.I.scoped_shift hφ)
      ⟨hv0', hv0'⟩ (ent_and_right _ _) hsys0 hΞb ?_ ?_
    · have hs1 : (cof (cof Φ.shift ψ) φ.shift).Scoped (Ψ + 1) := ⟨hΞs, KubusCore.I.scoped_shift hφ⟩
      exact VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hs1 (ent_and_left _ _) hsys0)
    · have hs1 : (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))).Scoped (Ψ + 1) := ⟨hΞs, ⟨hv0', hv0'⟩⟩
      have t1 := VEq.splitR' hW (ψ := .or (.neg (.var 0)) (.var 0)) (KubusCore.I.scoped_shift hφ) ⟨hv0', hv0'⟩
        (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_and_left _ _) hsys0)
        (VTy.restrict' hW ⟨hs1, ⟨hv0', hv0'⟩⟩ (ent_and_left _ _) hinner0)
        (VEq.restrict' hW ⟨⟨hs1, KubusCore.I.scoped_shift hφ⟩, ⟨hv0', hv0'⟩⟩
          (ent_and_mono (ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _))
            (ent_refl _)) hover0)
      refine VEq.trans' hW t1 ?_
      refine VEq.local' hW (φ := .neg (.var 0)) (ψ := .var 0) hv0' hv0' (ent_and_right _ _)
        (VTy.restrict' hW hs1 (ent_refl _) hinner0) (VTy.restrict' hW hs1 (ent_and_left _ _) hΞb) ?_ ?_
      · have hs2 : (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.neg (.var 0))).Scoped (Ψ + 1) :=
          ⟨hs1, hv0'⟩
        have e1 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hs2 (ent_and_left _ _) hinner0)
        have hA3 := VTy.restrict' hW hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞA
        have e2 := VEq.face' hW (i := 0) (d := false) hv0' (ent_and_right _ _) hA3.ty
          (VTy.restrict' hW hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞb)
        rw [papp_dshift_dset0] at e2
        have e3 := VEq.pathZero' hW (L := (A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ))
          (a := (a.dinst .zero).dshift) (b := (b.dinst .zero).dshift) (VTy.restrict' hW hs2
          (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)) hp0d)
        have hf := VEq.faceU' hW (i := 0) (d := false) hv0' (ent_and_right _ _) hA3
        rw [tp_Z0] at hf
        exact VEq.trans' hW e1 (VEq.symm' hW (VEq.trans' hW e2 (VEq.conv' hW e3 (VEq.symm' hW hf))))
      · have hs2 : (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)).Scoped (Ψ + 1) :=
          ⟨hs1, hv0'⟩
        have hinb := VTy.restrict' hW hs2 (ent_and_left _ _) hinner0
        have hA3 := VTy.restrict' hW hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞA
        have e2 := VEq.face' hW (i := 0) (d := true) hv0' (ent_and_right _ _) hA3.ty
          (VTy.restrict' hW hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞb)
        rw [papp_dshift_dset0] at e2
        have e3 := VEq.pathOne' hW (L := (A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ))
          (a := (a.dinst .zero).dshift) (b := (b.dinst .zero).dshift) (VTy.restrict' hW hs2
          (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)) hp0d)
        have hf := VEq.faceU' hW (i := 0) (d := true) hv0' (ent_and_right _ _) hA3
        rw [tp_Z0] at hf
        have he3 := VEq.conv' hW e3 (VEq.symm' hW hf)
        have hbI0 := VEq.rty' hW he3
        have hs4 : (cof (cof (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)) (.neg (.var 0)))
            (.var 0)).Scoped (Ψ + 1) := ⟨⟨hs2, hv0'⟩, hv0'⟩
        have hs4e : I.Entails (cof (cof (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0))
            (.neg (.var 0))) (.var 0)) (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)) :=
          ent_trans (ent_and_left _ _) (ent_and_left _ _)
        have haI0 : VTy S (Ψ + 1) (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.neg (.var 0))) Γ.dshift
            (a.dinst .zero).dshift ((A.dsubst swapI).dinst .zero) :=
          VEq.rty' hW (VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW (⟨hs1, hv0'⟩ : (cof (cof (cof Φ.shift ψ)
            (.or (.neg (.var 0)) (.var 0))) (.neg (.var 0))).Scoped (Ψ + 1)) (ent_and_left _ _) hinner0))
        have e1 := VEq.splitR' hW (φ := .neg (.var 0)) (ψ := .var 0) hv0' hv0' (ent_and_right _ _) hinb
          (VTy.restrict' hW ⟨hs2, hv0'⟩ (ent_and_left _ _) hbI0)
          (VEq.absurd' hW (ent_contra _ 0)
            (VTy.restrict' hW hs4 (ent_and_intro (ent_trans hs4e (ent_and_left _ _))
              (ent_trans (ent_and_left _ _) (ent_and_right _ _))) haI0).ty
            (VTy.restrict' hW hs4 hs4e hbI0).ty)
        exact VEq.trans' hW e1 (VEq.symm' hW (VEq.trans' hW e2 (VEq.conv' hW e3 (VEq.symm' hW hf))))
  have hside'' : VEq S (Ψ + 1) (cof Φ.shift ψ) Γ.dshift
      ((Tm.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) ψ2
        (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))).dinst .zero)
      (.papp p0.dshift (.var 0)) ((A.dsubst swapI).dinst .zero) := by rw [tp_sys0]; exact hside'
  have hbody := VTy.comp' hW hCc hψs hsys hbase hside''
  -- the endpoints
  have key : ∀ d : Bool,
      VEq S Ψ Φ Γ ((Tm.comp (A.dsubst swapI) ψ (.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) ψ2
          (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI)))
          (.papp p0.dshift (.var 0))).dinst (I.ofDir d))
        (.split (.neg (I.ofDir d)) (a.dinst .one) (I.ofDir d) (b.dinst .one))
        (((A.dsubst swapI).dinst .one).dinst (I.ofDir d)) ∧
      VTy S Ψ Φ Γ (.split (.neg (I.ofDir d)) (a.dinst .one) (I.ofDir d) (b.dinst .one))
        (((A.dsubst swapI).dinst .one).dinst (I.ofDir d)) := by
    intro d
    have hdd : (I.ofDir d).Scoped Ψ := by cases d <;> trivial
    have hor : I.Entails Φ (.or (.neg (I.ofDir d)) (I.ofDir d)) := by
      cases d
      · exact ent_negzero_or Φ
      · exact ent_one_or Φ
    have hb0 := VTy.dsubst' hW _ hdd hbody
    have e1a := VEq.hcompFace' hW (ent_trans hor (ent_or_right _ _)) hb0
    have e1b := VEq.transpFace' hW (ent_one _) (VEq.rty' hW e1a)
    have e1 : VEq S Ψ Φ Γ ((Tm.comp (A.dsubst swapI) ψ (.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) ψ2
          (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI)))
          (.papp p0.dshift (.var 0))).dinst (I.ofDir d))
        (((Tm.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) ψ2
          (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))).subst (fun n => (Tm.var n).dshift)
            (I.up (I.inst0 (I.ofDir d)))).dinst .one)
        (((A.dsubst swapI).dinst .one).dinst (I.ofDir d)) := VEq.trans' hW e1a e1b
    rw [dsub_end, tp_sysEnd] at e1
    have hΦ2 : I.Entails Φ (Φ.shift.shift.subst (endS d)) := ent_shift2_endS Φ d
    have hψE : I.Entails Φ ((cof Φ.shift ψ).shift.subst (endS d)) :=
      ent_and_intro hΦ2 (ent_trans hor (ent_or_right _ _))
    have hsysE := VTy.endS' hW d hR2s hψE hw0 hsys
    rw [tp_Cend, tp_sysEnd] at hsysE
    have hinE := VTy.endS' hW d hΞ2s (ent_and_intro hψE hor) hw0 hinner
    rw [tp_Cend, tp_innerEnd] at hinE
    have hcφo : (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d))).Scoped Ψ := ⟨hs', ⟨hdd, hdd⟩⟩
    have hoE : I.Entails (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d)))
        ((cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2).subst (endS d)) := by
      have h1 : I.Entails (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d))) Φ :=
        ent_trans (ent_and_left _ _) (ent_and_left _ _)
      have h2 : I.Entails (cof (cof Φ φ) (.or (.neg (I.ofDir d)) (I.ofDir d))) (φ.shift.shift.subst (endS d)) := by
        rw [shift2_endS]; exact ent_trans (ent_and_left _ _) (ent_and_right _ _)
      exact ent_and_intro (ent_and_intro (ent_trans h1 hψE) h2) (ent_and_right _ _)
    have hwo := Wf0.restrict hw0 hcφo (ent_trans (ent_and_left _ _) (ent_and_left _ _))
    have hovE := VEq.endS' hW d hY hoE hwo hover
    rw [tp_Cend, tp_innerEnd, tp_pappEnd] at hovE
    have e2 := VEq.splitR' hW (φ := φ) (ψ := .or (.neg (I.ofDir d)) (I.ofDir d)) hφ ⟨hdd, hdd⟩ hor hsysE
      (VTy.restrict' hW ⟨hs, ⟨hdd, hdd⟩⟩ (ent_and_left _ _) hinE) hovE
    exact ⟨VEq.trans' hW e1 e2, hinE⟩
  have e0 := VEq.trans' hW (key false).1 (VEq.splitL' hW (ent_negzero Φ) (key false).2)
  have hz1 : I.Entails (cof (cof Φ (.neg .one)) .one) .zero :=
    ent_trans (ent_trans (ent_and_left _ _) (ent_and_right _ _))
      (ent_trans (ent_or_right .zero (.neg .one)) (ent_neg_one .zero))
  have hz1s : (cof (cof Φ (.neg .one)) .one).Scoped Ψ := ⟨⟨hs, trivial⟩, trivial⟩
  have hz1e : I.Entails (cof (cof Φ (.neg .one)) .one) Φ := ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hC1 := VTy.dsubst' hW .one trivial hCc
  have ha1 := VTy.dsubst' hW .one trivial ha
  rw [tp_A01] at ha1
  have hb1 := VTy.dsubst' hW .one trivial hb
  rw [tp_A11] at hb1
  have e1 := VEq.trans' hW (key true).1
    (VEq.splitR' hW trivial trivial (ent_one Φ) (key true).2
      (VTy.restrict' hW (Φ' := cof Φ (I.ofDir true)) ⟨hs, trivial⟩ (ent_and_left _ _) hb1)
      (VEq.absurd' hW hz1 (VTy.conv' hW (VTy.restrict' hW hz1s hz1e ha1) (VEq.absurd' hW hz1
          (VTy.restrict' hW hz1s hz1e (VTy.dsubst' hW .zero trivial hC1)).ty
          (VTy.restrict' hW hz1s hz1e (VTy.dsubst' hW .one trivial hC1)).ty)).ty
        (VTy.restrict' hW hz1s hz1e hb1).ty))
  have hbody' := hbody
  rw [ipi_c5] at e0 e1 hbody'
  exact ⟨hbody, VTy.plam' hW (VTy.dsubst' hW .one trivial hLp) hbody' e0 e1⟩

theorem valid_transpPath_rule {A a b p0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.transp (.path A a b) φ p0) T)
    (hv : Valid2 S Ψ Φ Γ (.transp (.path A a b) φ p0) (.transp (.path A a b) φ p0) T)
    (hinv : TranspInv S Ψ Φ Γ (.path A a b) φ p0 T) :
    Valid2 S Ψ Φ Γ (.transp (.path A a b) φ p0) (Tm.transpPath A a b φ p0) T := by
  obtain ⟨l, hφ, hLV, hCV, hu0V, htr, hL, hc, hu0⟩ := hinv
  have hs := scoped_of_ty hu0
  have hLp : VTy S (Ψ + 1) Φ.shift Γ.dshift (.path A a b) (.univ l) := ⟨hL, hLV⟩
  have hcp : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (.path A a b) ((Tm.path A a b).dinst .zero).dshift (.univ l) :=
    ⟨hc, hCV⟩
  have hu0p : VTy S Ψ Φ Γ p0 ((Tm.path A a b).dinst .zero) := ⟨hu0, hu0V⟩
  obtain ⟨hbody, hy⟩ := VTy.transpPath' hW hLp hφ hcp hu0p
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hy.v htr hT
  -- where the face holds: η for `p0`, and the face of the body
  have hX : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hX0Φ : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have hη := VEq.pathEta' hW (L := (A.subst Tm.var (I.up (I.inst0 .zero))))
    (a := a.dinst .zero) (b := b.dinst .zero) (VTy.restrict' hW hX hX0Φ hu0p)
  have hk1 := VEq.dsubst' hW .one trivial hcp
  rw [dshift_dinst] at hk1
  have hη1 := VEq.conv' hW hη (VEq.symm' hW hk1)
  have hpl := VEq.rty' hW hη1
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hX
  have hbX := VTy.restrict' hW hXs (ent_shift hX0Φ) hbody
  have e1a := VEq.hcompFace' hW (ent_trans (ent_shift (ent_and_right Φ φ)) (ent_or_left _ _)) hbX
  have e1b := VEq.transpFace' hW (ent_one _) (VEq.rty' hW e1a)
  have e1 : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift
      (Tm.comp (A.dsubst swapI) (.or φ.shift (.or (.neg (.var 0)) (.var 0)))
        (.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
          (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI)))
        (.papp p0.dshift (.var 0)))
      ((Tm.split φ.shift.shift (.papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
          (.split (.neg (.var 1)) (a.dsubst insI) (.var 1) (b.dsubst insI))).dinst .one)
      ((A.dsubst swapI).dinst .one) := VEq.trans' hW e1a e1b
  rw [tp_sys1] at e1
  have e2 := VEq.splitL' hW (ent_shift (ent_and_right Φ φ)) (VEq.rty' hW e1)
  have ht := VEq.symm' hW (VEq.trans' hW e1 e2)
  rw [ipi_c5] at ht
  have hplam := VEq.plam' hW (VTy.restrict' hW hX hX0Φ (VTy.dsubst' hW .one trivial hLp)) hpl
    (VTy.restrict' hW hX hX0Φ hy).ty ht
  have hb := valid_conv_tr (VEq.trans' hW hη1 hplam).v (htr.restrict hX0Φ) fun k c => hT k (c.restrictTo hX0Φ)
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e3 : c.L (Tm.transpPath A a b φ p0) = Tm.transpPath (A.subst (dupS (dupS c.γ)) (I.up (I.up c.σ.τ)))
        (a.subst (dupS c.γ) (I.up c.σ.τ)) (b.subst (dupS c.γ) (I.up c.σ.τ)) (φ.subst c.σ.τ) (c.L p0) :=
      transpPath_subst _ _ A a b φ p0
    rw [e3]
    exact ⟨.step (step_transp_path hn) (.refl _), EqTm.transpPath (c.ty hW h)⟩
  · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (c.ty hW h)⟩

end

end Model.Whnf
