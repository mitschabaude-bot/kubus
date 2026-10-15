import Model.Whnf.Valid2Pair

/-!
# Fillers and heterogeneous composition, with validity

`hfill_typed` and `comp_typed` (`KubusCore/Meta/KanFill.lean`) with their validity, following the
typing derivations.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-! ### More interval substitutions -/

/-- The endpoint substitution `endS d` of a square. -/
theorem VTy.endS' {Φs Φ' : I} {t A : Tm} (d : Bool) (hΦs : Φs.Scoped (Ψ + 2)) (hent : I.Entails Φ' (Φs.subst (endS d)))
    (hw : Wf0 S Ψ Φ' Γ) (h : VTy S (Ψ + 1 + 1) Φs Γ.dshift.dshift t A) :
    VTy S Ψ Φ' Γ (t.subst Tm.var (endS d)) (A.subst Tm.var (endS d)) := by
  have h' : VTy S (Ψ + 2) Φs (Ctx.dren 2 Γ) t A := by rw [Ctx.dren_two]; exact h
  have := VTy.isubL hW (n := 2) (m := 0) (Ψ0 := Ψ) (Γ0 := Γ) (endS d)
    (fun i hi => by rcases i with _ | _ | i
                    · trivial
                    · cases d <;> trivial
                    · omega)
    (fun i => rfl) hΦs hent (by rw [Ctx.dren_zero]; exact hw) h'
  rw [Ctx.dren_zero] at this; exact this

theorem VEq.endS' {Φs Φ' : I} {t u A : Tm} (d : Bool) (hΦs : Φs.Scoped (Ψ + 2)) (hent : I.Entails Φ' (Φs.subst (endS d)))
    (hw : Wf0 S Ψ Φ' Γ) (h : VEq S (Ψ + 1 + 1) Φs Γ.dshift.dshift t u A) :
    VEq S Ψ Φ' Γ (t.subst Tm.var (endS d)) (u.subst Tm.var (endS d)) (A.subst Tm.var (endS d)) := by
  have h' : VEq S (Ψ + 2) Φs (Ctx.dren 2 Γ) t u A := by rw [Ctx.dren_two]; exact h
  have := VEq.isubL hW (n := 2) (m := 0) (Ψ0 := Ψ) (Γ0 := Γ) (endS d)
    (fun i hi => by rcases i with _ | _ | i
                    · trivial
                    · cases d <;> trivial
                    · omega)
    (fun i => rfl) hΦs hent (by rw [Ctx.dren_zero]; exact hw) h'
  rw [Ctx.dren_zero] at this; exact this

/-- Instantiating the inner of two interval variables. -/
theorem VTy.upInst' {Φs Φ' : I} {t A : Tm} (r : I) (hr : r.Scoped Ψ) (hΦs : Φs.Scoped (Ψ + 2))
    (hent : I.Entails Φ' (Φs.subst (I.up (I.inst0 r)))) (hw : Wf0 S (Ψ + 1) Φ' Γ.dshift)
    (h : VTy S (Ψ + 1 + 1) Φs Γ.dshift.dshift t A) :
    VTy S (Ψ + 1) Φ' Γ.dshift (t.subst Tm.var (I.up (I.inst0 r))) (A.subst Tm.var (I.up (I.inst0 r))) := by
  have h' : VTy S (Ψ + 2) Φs (Ctx.dren 2 Γ) t A := by rw [Ctx.dren_two]; exact h
  exact VTy.isubL hW (n := 2) (m := 1) (Ψ0 := Ψ) (Γ0 := Γ) (I.up (I.inst0 r))
    (fun i hi => by rcases i with _ | _ | i
                    · show 0 < Ψ + 1; omega
                    · exact KubusCore.I.scoped_shift hr
                    · omega)
    (fun i => rfl) hΦs hent hw h'

/-- Composition, congruence. -/
theorem VEq.hcomp' {A A' u u' a a' : Tm} {φ φ' : I} {l : ℕ}
    (hφ : φ.Scoped Ψ) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hty : HasTy0 S Ψ Φ Γ (.hcomp A φ u a) A) (hty' : HasTy0 S Ψ Φ Γ (.hcomp A' φ' u' a') A)
    (hA : VEq S Ψ Φ Γ A A' (.univ l)) (hu : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift u u' A.dshift)
    (ha : VEq S Ψ Φ Γ a a' A) (hu0 : Valid2 S Ψ (cof Φ φ) Γ (u.dinst .zero) a A)
    (hu0' : Valid2 S Ψ (cof Φ φ) Γ (u'.dinst .zero) a' A) :
    VEq S Ψ Φ Γ (.hcomp A φ u a) (.hcomp A' φ' u' a') A := by
  have e := EqTm0.hcomp hty hty' hA.eq h12 h21 hu.eq ha.eq
  exact ⟨e, valid_hcomp hW hφ h12 h21 hA.v hu.v ha.v hu0 hu0' hty hty' e hu.eq⟩

/-! ### The homogeneous filler -/

/-- `hfill_typed`, with validity. -/
theorem VTy.hfill' {A u u0 : Tm} {φ : I} {l : ℕ} (hA : VTy S Ψ Φ Γ A (.univ l))
    (hφ : φ.Scoped Ψ) (hu : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift)
    (hu0 : VTy S Ψ Φ Γ u0 A) (hside : VEq S Ψ (cof Φ φ) Γ (u.dinst .zero) u0 A) :
    VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.hfill A φ u u0) A.dshift ∧
    VEq S Ψ Φ Γ ((Tm.hfill A φ u u0).dinst .zero) u0 A ∧
    VEq S Ψ Φ Γ ((Tm.hfill A φ u u0).dinst .one) (.hcomp A φ u u0) A ∧
    VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (Tm.hfill A φ u u0) u A.dshift := by
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hA.ty
  have hw0 := wf_of_ty hA.ty
  have hA1 := VTy.dwk' hW hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hsφ : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  let χ : I := .or φ.shift (.neg (.var 0))
  have hχs : χ.Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hφ, hv0⟩
  have hΞs : (cof Φ.shift χ).Scoped (Ψ + 1) := ⟨KubusCore.I.scoped_shift hs, hχs⟩
  have hRs : (cof Φ.shift χ).shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift hΞs
  have hRΦ : I.Entails (cof Φ.shift χ).shift Φ.shift.shift := ent_shift (ent_and_left Φ.shift χ)
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hφ)
  have hA2 : VTy S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift A.dshift.dshift (.univ l) :=
    VTy.restrict' hW hRs hRΦ (VTy.dwk' hW hA1)
  -- the tube
  have hR1s : (cof (cof Φ.shift χ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hRs, hφ2⟩
  have hR1Φ : I.Entails (cof (cof Φ.shift χ).shift φ.shift.shift) (cof Φ φ).shift.shift :=
    ent_and_mono hRΦ (ent_refl _)
  have hT1 : VTy S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift φ.shift.shift) Γ.dshift.dshift
      (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) A.dshift.dshift := by
    have := VTy.bind2' hW (Φ := cof Φ φ) (r := .and (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hsφ hR1Φ
      ((hw0.dwk2 hS).restrict hR1s (ent_trans (ent_and_left _ _) hRΦ)) hu
    rwa [show A.dshift.dsubst (Tm.bind2 (.and (.var 1) (.var 0))) = A.dshift.dshift from dshift_bind2 A _] at this
  have hR2s : (cof (cof Φ.shift χ).shift (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hRs, hv1⟩
  have hT2 : VTy S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift (.neg (.var 1))) Γ.dshift.dshift
      u0.dshift.dshift A.dshift.dshift :=
    VTy.restrict' hW hR2s (ent_trans (ent_and_left _ _) hRΦ) (VTy.dwk' hW (VTy.dwk' hW hu0))
  have hR3s : (cof (cof (cof Φ.shift χ).shift φ.shift.shift) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hR1s, hv1⟩
  have hover : VEq S (Ψ + 1 + 1) (cof (cof (cof Φ.shift χ).shift φ.shift.shift) (.neg (.var 1)))
      Γ.dshift.dshift (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) u0.dshift.dshift A.dshift.dshift := by
    have e1 := VEq.face' hW (i := 1) (d := false) hv1 (ent_and_right _ _)
      (VTy.restrict' hW hR3s (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA2).ty
      (VTy.restrict' hW hR3s (ent_and_left _ _) hT1)
    rw [fillTube_dset1 φ u u0] at e1
    have hX : I.Entails (cof (cof (cof Φ.shift χ).shift φ.shift.shift) (.neg (.var 1)))
        ((cof Φ φ).subst (fun n => .var (n + 2))) := by
      rw [I_add2]; exact ent_trans (ent_and_left _ _) hR1Φ
    have e2 := VTy.lineIeq hW hu (k := 2) (r := .and .zero (.var 0)) (r' := .zero) hX ⟨trivial, hv0'⟩ trivial
      (I_eq_and_zero _)
      (by rw [Ctx.dren_two]; exact ((hw0.dwk2 hS).restrict hR3s (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hRΦ))))
    rw [Ctx.dren_two, dshift_sk, subst_add2, sk_zero2] at e2
    have e3 := VEq.restrict' hW hR3s (ent_trans (ent_and_left _ _) hR1Φ) (VEq.dwk' hW (VEq.dwk' hW hside))
    exact VEq.trans' hW e1 (VEq.trans' hW e2 e3)
  have htube : VTy S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift (KubusCore.Meta.fillTube φ u u0) A.dshift.dshift :=
    VTy.split' hW (ψ := .neg (.var 1)) hφ2 hv1 (ent_shift (ent_and_right Φ.shift χ)) hA2.ty hT1 hT2 hover
  -- the base and the side condition
  have hbase := VTy.dwk' hW hu0
  have htube0 : VTy S (Ψ + 1) (cof Φ.shift χ) Γ.dshift
      ((KubusCore.Meta.fillTube φ u u0).dinst .zero) (A.dshift.dshift.dinst .zero) :=
    VTy.dsubst' hW (Φ := cof Φ.shift χ) (Γ := Γ.dshift) .zero trivial htube
  rw [dshift_dinst, fillTube_d0] at htube0
  have hwu := wf_of_ty hu.ty
  have hu1 : ∀ {X : I} {r : I}, X.Scoped (Ψ + 1) → I.Entails X (cof Φ φ).shift → r.Scoped (Ψ + 1) →
      I.Eq r (.var 0) → VEq S (Ψ + 1) X Γ.dshift (u.subst Tm.var (sk r 1)) u A.dshift := by
    intro X r hX hXe hr he
    have := VTy.lineIeq hW hu (k := 1) (r := r) (r' := .var 0) hXe hr hv0 he (hwu.restrict hX hXe)
    rwa [dshift_sk, subst_add1, sk_var1] at this
  have hu1' : ∀ {X : I} {r : I}, X.Scoped (Ψ + 1) → I.Entails X (cof Φ φ).shift → r.Scoped (Ψ + 1) →
      I.Eq r .zero → VEq S (Ψ + 1) X Γ.dshift (u.subst Tm.var (sk r 1)) u0.dshift A.dshift := by
    intro X r hX hXe hr he
    have e2 := VTy.lineIeq hW hu (k := 1) (r := r) (r' := .zero) hXe hr trivial he (hwu.restrict hX hXe)
    rw [dshift_sk, subst_add1, sk_zero1] at e2
    exact VEq.trans' hW e2 (VEq.restrict' hW hX hXe (VEq.dwk' hW hside))
  have hside' : VEq S (Ψ + 1) (cof Φ.shift χ) Γ.dshift
      (.split φ.shift (u.subst Tm.var (sk (.and (.var 0) .zero) 1)) (.neg (.var 0)) u0.dshift)
      u0.dshift A.dshift := by
    have hX1 : (cof (cof Φ.shift χ) φ.shift).Scoped (Ψ + 1) := ⟨hΞs, KubusCore.I.scoped_shift hφ⟩
    have hX1e : I.Entails (cof (cof Φ.shift χ) φ.shift) (cof Φ φ).shift :=
      ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
    have hX2 : (cof (cof Φ.shift χ) (.neg (.var 0))).Scoped (Ψ + 1) := ⟨hΞs, hv0⟩
    have hX3 : (cof (cof (cof Φ.shift χ) φ.shift) (.neg (.var 0))).Scoped (Ψ + 1) := ⟨hX1, hv0⟩
    have hX3e : I.Entails (cof (cof (cof Φ.shift χ) φ.shift) (.neg (.var 0))) (cof Φ φ).shift :=
      ent_trans (ent_and_left _ _) hX1e
    refine VEq.local' hW (φ := φ.shift) (ψ := .neg (.var 0)) (KubusCore.I.scoped_shift hφ) hv0 (ent_and_right _ _)
      htube0 (VTy.restrict' hW hΞs (ent_and_left _ _) hbase) ?_ ?_
    · have e1 := VEq.splitL' hW (ent_and_right _ _) (VTy.restrict' hW hX1 (ent_and_left _ _) htube0)
      exact VEq.trans' hW e1 (hu1' hX1 hX1e ⟨hv0, trivial⟩ (I_eq_and_zero_r _))
    · exact VEq.splitR' hW (KubusCore.I.scoped_shift hφ) hv0 (ent_and_right _ _)
        (VTy.restrict' hW hX2 (ent_and_left _ _) htube0)
        (VTy.restrict' hW ⟨hX2, hv0⟩ (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) (ent_and_left _ _)))
          hbase)
        (hu1' (X := cof (cof (cof (cof Φ.shift χ) (.neg (.var 0))) φ.shift) (.neg (.var 0)))
          ⟨⟨hX2, KubusCore.I.scoped_shift hφ⟩, hv0⟩
          (ent_trans (ent_and_left _ _) (ent_and_intro (ent_trans (ent_and_left _ _)
            (ent_trans (ent_and_left _ _) (ent_and_left _ _))) (ent_and_right _ _)))
          ⟨hv0, trivial⟩ (I_eq_and_zero_r _))
  have hside'' : VEq S (Ψ + 1) (cof Φ.shift χ) Γ.dshift ((KubusCore.Meta.fillTube φ u u0).dinst .zero) u0.dshift
      A.dshift := by rw [fillTube_d0]; exact hside'
  have hfT : VTy S (Ψ + 1) Φ.shift Γ.dshift (Tm.hfill A φ u u0) A.dshift :=
    VTy.hcomp' hW hA1 hχs htube hbase hside''
  refine ⟨hfT, ?_, ?_, ?_⟩
  · -- the endpoint 0
    have hd : VTy S Ψ Φ Γ ((Tm.hcomp A.dshift χ (KubusCore.Meta.fillTube φ u u0) u0.dshift).dinst .zero)
        (A.dshift.dinst .zero) := VTy.dsubst' hW .zero trivial hfT
    have e1 := VEq.hcompFace' hW (ent_trans (ent_negzero Φ) (ent_or_right _ _)) hd
    rw [dsub_end0, fillTube_end] at e1
    have hE := VTy.endS' hW false hRs
      (ent_and_intro (ent_shift2_endS Φ false) (ent_trans (ent_negzero Φ) (ent_or_right _ _))) hw0 htube
    rw [dshift2_endS, fillTube_end] at hE
    have hX0 : (cof Φ (.neg .zero)).Scoped Ψ := ⟨hs, trivial⟩
    have hX1 : (cof (cof Φ φ) (.neg .zero)).Scoped Ψ := ⟨hsφ, trivial⟩
    have htu : VEq S Ψ (cof (cof Φ φ) (.neg .zero)) Γ (u.subst Tm.var (sk (.and .zero .one) 0)) u0 A := by
      have e := VTy.lineIeq hW hu (k := 0) (r := .and .zero .one) (r' := .zero)
        (X := cof (cof Φ φ) (.neg .zero)) (by rw [I_add0]; exact ent_and_left _ _) ⟨trivial, trivial⟩ trivial
        (I_eq_and_zero _) (by rw [Ctx.dren_zero]; exact hw0.restrict hX1 (ent_trans (ent_and_left _ _) (ent_and_left _ _)))
      rw [Ctx.dren_zero, dshift_sk, subst_add0, sk_zero0] at e
      exact VEq.trans' hW e (VEq.restrict' hW hX1 (ent_and_left _ _) hside)
    have e2 := VEq.splitR' hW (ψ := .neg .zero) hφ trivial (ent_negzero Φ) hE (VTy.restrict' hW hX0 (ent_and_left _ _) hu0) htu
    have hAA : VEq S Ψ Φ Γ A (A.dshift.dinst .zero) (.univ l) := by rw [dshift_dinst]; exact VEq.refl' hA
    exact VEq.conv' hW (VEq.trans' hW e1 (VEq.conv' hW e2 hAA)) (VEq.symm' hW hAA)
  · -- the endpoint 1
    have hd : VTy S Ψ Φ Γ ((Tm.hcomp A.dshift χ (KubusCore.Meta.fillTube φ u u0) u0.dshift).dinst .one)
        (A.dshift.dinst .one) := VTy.dsubst' hW .one trivial hfT
    have hc := VTy.hcomp' hW hA hφ hu hu0 hside
    have hX : (cof Φ (.or φ (.neg .one))).Scoped Ψ := ⟨hs, ⟨hφ, trivial⟩⟩
    have hXe0 : I.Entails (cof Φ (.or φ (.neg .one))) (cof Φ φ) := ent_and_mono (ent_refl _) (ent_neg_one φ)
    have hXe : I.Entails (cof Φ (.or φ (.neg .one))).shift (cof Φ φ).shift := ent_shift hXe0
    have hXs : (cof Φ (.or φ (.neg .one))).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hX
    have htyped := VTy.upInst' hW (Φ' := (cof Φ (.or φ (.neg .one))).shift) .one trivial hRs
      (by rw [fillR_up1]; exact ent_refl _)
      ((Wf0.dwk hS hw0).restrict hXs (ent_shift (ent_and_left _ _))) htube
    rw [dshift2_up_inst0, fillTube_up1'] at htyped
    have htu : VEq S (Ψ + 1) (cof Φ (.or φ (.neg .one))).shift Γ.dshift
        (.split φ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift) u A.dshift := by
      have e1 := VEq.splitL' hW (ent_trans (ent_and_right _ _) (ent_shift (ent_neg_one φ))) htyped
      exact VEq.trans' hW e1 (hu1 hXs hXe ⟨trivial, hv0⟩ (I_eq_and_one_l _))
    rw [hfill_d1_eq, dshift_dinst, fillTube_up1'] at hd
    have hu0L : Valid2 S Ψ (cof Φ (.or φ (.neg .one))) Γ
        ((Tm.split φ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift).dinst .zero) u0 A := by
      have e := VEq.dsubst' hW (Φ := cof Φ (.or φ (.neg .one))) .zero trivial htu
      rw [dshift_dinst] at e
      exact (VEq.trans' hW e (VEq.restrict' hW hX hXe0 hside)).v
    have e := VEq.hcomp' hW (φ := .or φ (.neg .one))  ⟨hφ, trivial⟩ (ent_neg_one φ) (ent_or_left _ _)
      hd.ty hc.ty (VEq.refl' hA) htu (VEq.refl' hu0) hu0L (valid_restrict hW hXe0 hside.v)
    rw [show Tm.hfill A φ u u0 = Tm.hcomp A.dshift χ (KubusCore.Meta.fillTube φ u u0) u0.dshift from hfill_eq A φ u u0,
      hfill_d1_eq, fillTube_up1']
    exact e
  · -- under `φ` the filler is the tube
    have hs' : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hsφ
    have hφφ : I.Entails (cof Φ φ).shift φ.shift := ent_shift (ent_and_right Φ φ)
    have hf' := VTy.restrict' hW hs' (ent_shift (ent_and_left Φ φ)) hfT
    have e1 := VEq.hcompFace' hW (A := A.dshift) (φ := χ) (u := KubusCore.Meta.fillTube φ u u0) (a := u0.dshift)
      (ent_trans hφφ (ent_or_left _ _)) hf'
    have ht1 : VTy S (Ψ + 1) (cof Φ.shift χ) Γ.dshift ((KubusCore.Meta.fillTube φ u u0).dinst .one)
        (A.dshift.dshift.dinst .one) := VTy.dsubst' hW (Φ := cof Φ.shift χ) (Γ := Γ.dshift) .one trivial htube
    rw [dshift_dinst] at ht1
    have ht1' := VTy.restrict' hW hs'
      (ent_and_intro (ent_shift (ent_and_left Φ φ)) (ent_trans hφφ (ent_or_left _ _))) ht1
    rw [fillTube_d1] at e1 ht1'
    have e2 := VEq.splitL' hW hφφ ht1'
    exact VEq.trans' hW e1 (VEq.trans' hW e2 (hu1 hs' (ent_refl _) ⟨hv0, trivial⟩ (I_eq_and_one_r _)))

/-! ### Heterogeneous composition -/

/-- The parts of `comp`: the end type, the tube of transports, the transported base and the side condition. -/
theorem VTy.compParts' {C ψ u u0} {l : ℕ}
    (hC : VTy S (Ψ + 1) Φ.shift Γ.dshift C (.univ l)) (hψ : ψ.Scoped Ψ)
    (hu : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C) (hu0 : VTy S Ψ Φ Γ u0 (C.dinst .zero))
    (hside : VEq S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (C.dinst .zero)) :
    VTy S Ψ Φ Γ (C.dinst .one) (.univ l) ∧
    VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift
      (.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u) (C.dinst .one).dshift ∧
    VEq S (Ψ + 1 + 1) (cof (cof Φ ψ).shift (.var 0)).shift Γ.dshift.dshift
      (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0))))
      ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .zero).dshift (.univ l) ∧
    VTy S Ψ Φ Γ (.transp C .zero u0) (C.dinst .one) ∧
    VEq S Ψ (cof Φ ψ) Γ ((Tm.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u).dinst .zero)
      (.transp C .zero u0) (C.dinst .one) := by
  have hS := sigClosed_of_wfSig hW
  have hw0 := wf_unshift hS (wf_of_ty hC.ty)
  have hs := scoped_of_wf hw0
  have hC1 := VTy.dsubst' hW .one trivial hC
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hXs : (cof Φ ψ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, hψ⟩
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left Φ ψ)
  -- the line of the tube's transports
  have hL := VTy.bind2' hW (X := (cof Φ ψ).shift.shift) (r := .or (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hs
    (ent_shift hXΦ) ((hw0.dwk2 hS).restrict (KubusCore.I.scoped_shift hXs) (ent_shift hXΦ)) hC
  rw [univ_dsubst] at hL
  have hYs : (cof (cof Φ ψ).shift (.var 0)).shift.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift ⟨hXs, hv0⟩
  have hYX : I.Entails (cof (cof Φ ψ).shift (.var 0)).shift (cof Φ ψ).shift.shift := ent_shift (ent_and_left _ _)
  have hY1 : I.Entails (cof (cof Φ ψ).shift (.var 0)).shift (I.lit 1 true) := ent_shift (ent_and_right _ (.var 0))
  have hYΦ : I.Entails (cof (cof Φ ψ).shift (.var 0)).shift (Φ.subst (fun n => .var (n + 2))) := by
    rw [I_add2]; exact ent_trans hYX (ent_shift hXΦ)
  have hwY : Wf0 S (Ψ + 2) (cof (cof Φ ψ).shift (.var 0)).shift (Ctx.dren 2 Γ) := by
    rw [Ctx.dren_two]; exact (hw0.dwk2 hS).restrict hYs (by rw [← I_add2]; exact hYΦ)
  have hconst : VEq S (Ψ + 1 + 1) (cof (cof Φ ψ).shift (.var 0)).shift Γ.dshift.dshift
      (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0))))
      ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .zero).dshift (.univ l) := by
    have hLY := VTy.restrict' hW hYs hYX hL
    have e1 := VEq.faceU' hW (i := 1) (d := true) hv1 hY1 hLY
    rw [L_dset11] at e1
    have e2 := VTy.lineIeq hW hC (k := 2) (r := .or .one (.var 0)) (r' := .one) hYΦ ⟨trivial, hv0'⟩ trivial
      (I_eq_or_one_l _) hwY
    rw [Ctx.dren_two] at e2
    have hL0 := VTy.restrict' hW hYs hYX (VTy.dwk' hW (VTy.dsubst' hW (Φ := (cof Φ ψ).shift) (Γ := Γ.dshift)
      .zero trivial hL))
    rw [L_d0_dshift] at hL0
    have e3 := VEq.faceU' hW (i := 1) (d := true) hv1 hY1 hL0
    rw [sk_dset11] at e3
    have e4 := VTy.lineIeq hW hC (k := 2) (r := .or .one .zero) (r' := .one) hYΦ ⟨trivial, trivial⟩ trivial
      (I_eq_or_one_l _) hwY
    rw [Ctx.dren_two] at e4
    rw [L_d0_dshift]
    exact VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.symm' hW (VEq.trans' hW e3 e4)))
  -- the tube
  have hwX : Wf0 S (Ψ + 1) (cof Φ ψ).shift (Ctx.dren 1 Γ) := wf_of_ty hu.ty
  have hu' : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u
      ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .zero) := by
    rw [L_d0]
    have e := VTy.lineIeq hW hC (k := 1) (r := .var 0) (r' := .or (.var 0) .zero) hXΦ hv0
      ⟨hv0, trivial⟩ (I_eq_symm (I_eq_or_zero_r _)) hwX
    rw [sk_var1] at e
    exact VTy.conv' hW hu e
  have ht0 := VTy.transp' hW hL hv0 hconst hu'
  have htube : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift
      (.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u) (C.dinst .one).dshift := by
    have e := VTy.lineIeq hW hC (k := 1) (r := .or (.var 0) .one) (r' := .one) hXΦ
      ⟨hv0, trivial⟩ trivial (I_eq_or_one_r _) hwX
    rw [sk_one1] at e
    rw [L_d1] at ht0
    exact VTy.conv' hW ht0 e
  -- the base
  have hab : I.Entails (cof Φ .zero).shift .zero := ent_shift (ent_and_right Φ .zero)
  have hZs : (cof Φ .zero).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, trivial⟩
  have hb := VTy.transp' hW hC (φ := .zero) trivial
    (VEq.absurd' hW hab (HasTy0.restrict hZs (ent_shift (ent_and_left _ _)) hC.ty)
      (HasTy0.restrict hZs (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS (HasTy0.dsubst hS hC.ty (r := .zero) trivial))))
    hu0
  -- the side condition
  have hψs : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  have hwψ : Wf0 S (Ψ + 0) (cof Φ ψ) (Ctx.dren 0 Γ) := by
    rw [Ctx.dren_zero]; exact hw0.restrict hψs (ent_and_left _ _)
  have hψΦ0 : I.Entails (cof Φ ψ) (Φ.subst (fun n => .var (n + 0))) := by rw [I_add0]; exact ent_and_left _ _
  have hside' : VEq S Ψ (cof Φ ψ) Γ
      ((Tm.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u).dinst .zero)
      (.transp C .zero u0) (C.dinst .one) := by
    rw [tube_d0]
    have h0 : VTy S Ψ (cof Φ ψ) Γ ((Tm.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u).dinst .zero)
        (((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .one).dinst .zero) :=
      VTy.dsubst' hW (Φ := cof Φ ψ) (Γ := Γ) .zero trivial ht0
    rw [tube_d0, L_d1_d0] at h0
    have eA1 := VTy.lineIeq hW hC (k := 0) (r := .or .zero .one) (r' := .one) hψΦ0 ⟨trivial, trivial⟩
      trivial (I_eq_or_one_r _) hwψ
    rw [Ctx.dren_zero, sk_one0] at eA1
    have h0' : VTy S Ψ (cof Φ ψ) Γ (.transp (C.subst Tm.var (sk (.or .zero (.var 0)) 1)) .zero (u.dinst .zero))
        ((C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .one) := by
      rw [sk1_d1z]; exact h0
    have h1 : VTy S Ψ (cof Φ ψ) Γ (.transp C .zero u0) ((C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .one) := by
      rw [sk1_d1z]
      exact VTy.conv' hW (VTy.restrict' hW hψs (ent_and_left _ _) hb) (VEq.symm' hW eA1)
    have h2 := VTy.lineIeq hW hC (k := 1) (r := .or .zero (.var 0)) (r' := .var 0) hXΦ
      ⟨trivial, hv0⟩ hv0 (I_eq_or_zero_l _) hwX
    rw [sk_var1] at h2
    have eA0 := VTy.lineIeq hW hC (k := 0) (r := .zero) (r' := .or .zero .zero) hψΦ0 trivial
      ⟨trivial, trivial⟩ (I_eq_symm (I_eq_or_zero_l _)) hwψ
    rw [Ctx.dren_zero, sk_zero0] at eA0
    have h5 : VEq S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 ((C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .zero) := by
      rw [sk1_d0z]; exact VEq.conv' hW hside eA0
    have e := VEq.transp' hW 
      (φ := .zero) trivial (ent_refl _) (ent_refl _) h0'.ty h1.ty h2
      (valid_absurd (A := .univ l) (ent_shift (ent_and_right (cof Φ ψ) .zero))) h5
    rw [sk1_d1z] at e
    exact VEq.conv' hW e eA1
  exact ⟨hC1, htube, hconst, hb, hside'⟩

/-- `comp_typed`, with validity. -/
theorem VTy.comp' {C ψ u u0} {l : ℕ}
    (hC : VTy S (Ψ + 1) Φ.shift Γ.dshift C (.univ l)) (hψ : ψ.Scoped Ψ)
    (hu : VTy S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C) (hu0 : VTy S Ψ Φ Γ u0 (C.dinst .zero))
    (hside : VEq S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (C.dinst .zero)) :
    VTy S Ψ Φ Γ (Tm.comp C ψ u u0) (C.dinst .one) := by
  obtain ⟨hC1, htube, -, hb, hside'⟩ := VTy.compParts' hW hC hψ hu hu0 hside
  exact VTy.hcomp' hW hC1 hψ htube hb hside'

end

end Model.Whnf
