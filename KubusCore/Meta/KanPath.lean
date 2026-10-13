import KubusCore.Meta.Derived

/-!
# Metatheory: typing the contractum of `hcomp` in path types
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- The substitution `k := 1`, `j := d` of the tube context, lowering the others. -/
def endS (d : Bool) : Nat → I
  | 0 => .one
  | 1 => I.ofDir d
  | n + 2 => .var n

/-- Compare two substitutions of the same term pointwise. -/
macro "ssub" : tactic => `(tactic| (
  simp only [Tm.dinst, Tm.dsubst, Tm.dset, dshift_eq, shift_eq, ren_eq_subst, subst_subst, I_subst_subst];
  first
    | refine subst_congr (fun n => ?_) (fun n => ?_) _
    | refine (subst_congr (fun n => ?_) (fun n => ?_) _).trans (subst_var _)
    | refine (subst_var _).symm.trans (subst_congr (fun n => ?_) (fun n => ?_) _)
  all_goals (rcases n with _ | _ | _ | n <;>
    simp [Tm.subst, I.subst, I.inst0, insI, skip1, skip1I, rS, rI, I.up, Tm.up, upRen, I.ofDir, I.shift,
      I.ren, endS] <;> omega)))

/-- The line of a path type, under the tube variable and renamed past the path variable. -/
def Xp (A : Tm) : Tm := A.subst Tm.var (fun i => match i with | 0 => .var 0 | n + 1 => .var (n + 3))

theorem Xp_var1 (A : Tm) : (Xp A).dinst (.var 1) = A.dshift := by simp only [Xp]; ssub
theorem Xp_zero (A : Tm) : (Xp A).dinst .zero = (A.dinst .zero).dshift.dshift := by simp only [Xp]; ssub
theorem Xp_one (A : Tm) : (Xp A).dinst .one = (A.dinst .one).dshift.dshift := by simp only [Xp]; ssub
theorem dshift_dset1_zero (A : Tm) : A.dshift.dset 1 (I.ofDir false) = (A.dinst .zero).dshift.dshift := by
  ssub
theorem dshift_dset1_one (A : Tm) : A.dshift.dset 1 (I.ofDir true) = (A.dinst .one).dshift.dshift := by
  ssub
theorem insI_dset1 (u : Tm) (d : Bool) : (u.dsubst insI).dset 1 (I.ofDir d) = u.dsubst insI := by
  cases d <;> ssub
theorem path_dshift_skip (A a b : Tm) :
    ((path A a b).dshift).subst (rS id) (rI skip1) = path (Xp A) a.dshift.dshift b.dshift.dshift := by
  simp only [Tm.dshift, Tm.ren, Tm.subst]
  congr 1
  · simp only [Xp]; ssub
  · ssub
  · ssub
theorem insI_eq (u : Tm) : u.subst (rS id) (rI skip1) = u.dsubst insI := by ssub
theorem dset0_eq (A : Tm) (d : Bool) : A.dset 0 (I.ofDir d) = (A.dinst (I.ofDir d)).dshift := by
  cases d <;> ssub
theorem upDShift_dinst_dir (A : Tm) (d : Bool) :
    (A.ren id (upRen Nat.succ)).dinst (I.ofDir d) = (A.dinst (I.ofDir d)).dshift := by
  cases d <;> ssub

theorem Wf0.dwk2 (hS : SigClosed S) {Ψ Φ Γ} (h : Wf0 S Ψ Φ Γ) :
    Wf0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift := Wf0.dwk hS (Wf0.dwk hS h)

/-- A tube renamed past a new interval variable 1. -/
theorem tube_skip (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {u X : Tm} (hu : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift u X) :
    HasTy0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift (u.dsubst insI) (X.subst (rS id) (rI skip1)) := by
  have hw := wf_unshift hS (wf_of_ty hu)
  have hw2 := hw.dwk2 hS
  have hR : TyRen S (Ψ + 1) Φ.shift Γ.dshift (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift id skip1 :=
    { inj := fun i j hij => by
        rcases i with _ | i <;> rcases j with _ | j <;> simp_all [skip1]
      bound := fun i hi => by rcases i with _ | i <;> simp [skip1] <;> omega
      hscoped := scoped_of_wf hw2
      ent := by
        apply eq_ent; intro ρ
        simp only [I.shift, I.ren, I_subst_subst]
        rfl
      look := fun x B hx => by
        rw [lookup_dshift, Option.map_eq_some_iff] at hx
        obtain ⟨B0, hB0, rfl⟩ := hx
        rw [lookup_dshift, lookup_dshift]
        simp only [id, hB0, Option.map_some, Option.some.injEq, dshift_eq, subst_subst]
        exact subst_congr (fun n => rfl) (fun i => rfl) B0
      wf := wfAll_of_wf hS hw2 }
  have := (ren_ty hS hu).2 hR
  rwa [insI_eq] at this

theorem ent_of_sem {Ξ ψ : I} (h : ∀ ρ, K3Asg ρ → Ξ.eval ρ = .one → ψ.eval ρ = .one) : I.Entails Ξ ψ :=
  entails_iff.2 h

theorem ent_contra (X : I) (n : Nat) : I.Entails (.and (.and X (.neg (.var n))) (.var n)) .zero := by
  apply ent_of_sem; intro ρ _ h
  simp only [I.eval, meet_one_iff, neg_one_iff] at h
  rw [h.1.2] at h; cases h.2

theorem ent_negzero (X : I) : I.Entails X (.neg .zero) := ent_of_sem fun _ _ _ => rfl

theorem ent_negzero_or (X : I) : I.Entails X (.or (.neg .zero) .zero) :=
  ent_trans (ent_negzero X) (ent_or_left _ _)

theorem ent_one_or (X : I) : I.Entails X (.or (.neg .one) .one) :=
  ent_trans (ent_one X) (ent_or_right _ _)

theorem hcompPath_eq (A a b : Tm) (φ : I) (u p0 : Tm) :
    hcompPath A a b φ u p0 = plam (hcomp A (.or φ.shift (.or (.neg (.var 0)) (.var 0)))
      (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift))
      (papp p0.dshift (.var 0))) := rfl

theorem sys0_eq (φ : I) (u a b : Tm) :
    (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)).dinst .zero =
      split φ.shift (papp (u.dinst .zero).dshift (.var 0)) (.or (.neg (.var 0)) (.var 0))
        (split (.neg (.var 0)) a.dshift (.var 0) b.dshift) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; rfl
  · congr 1; ssub
  · congr 1 <;> ssub

theorem sysEnd_eq (φ : I) (u a b : Tm) (d : Bool) :
    (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) (.or (.neg (.var 1)) (.var 1))
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)).subst Tm.var (endS d) =
      split φ (papp (u.dinst .one) (I.ofDir d)) (.or (.neg (I.ofDir d)) (I.ofDir d))
        (split (.neg (I.ofDir d)) a (I.ofDir d) b) := by
  simp only [Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var φ
  · congr 1; simp only [Tm.dinst]; ssub
  · congr 1
    · ssub
    · ssub

theorem ctxI_endS (Γ : Ctx) (d : Bool) : ctxI (endS d) Γ.dshift.dshift = Γ := by
  simp only [ctxI, Ctx.dshift, List.map_map]
  conv => rhs; rw [← List.map_id Γ]
  congr 1; funext t; simp only [Function.comp, id]; ssub

theorem papp_insI_dset1 (u : Tm) (d : Bool) :
    (papp (u.dsubst insI) (.var 1)).dset 1 (I.ofDir d) = papp (u.dsubst insI) (I.ofDir d) := by
  show papp ((u.dsubst insI).dset 1 (I.ofDir d)) ((I.var 1).subst _) = _
  rw [insI_dset1]; simp [I.subst]

theorem papp_dshift_dset0 (p : Tm) (d : Bool) :
    (papp p.dshift (.var 0)).dset 0 (I.ofDir d) = papp p.dshift (I.ofDir d) := by
  show papp (p.dshift.dset 0 (I.ofDir d)) ((I.var 0).subst _) = _
  rw [show p.dshift.dset 0 (I.ofDir d) = p.dshift by ssub]; simp [I.subst]

theorem dsub_end (X : Tm) (d : Bool) :
    (X.subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 (I.ofDir d)))).dinst .one = X.subst Tm.var (endS d) := by
  cases d <;> ssub

theorem dshift_endS (A : Tm) (d : Bool) : A.dshift.subst Tm.var (endS d) = A.dinst (I.ofDir d) := by
  cases d <;> ssub

theorem shift2_endS (Φ : I) (d : Bool) : Φ.shift.shift.subst (endS d) = Φ := by
  simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var Φ

theorem ent_shift2_endS (Φ : I) (d : Bool) : I.Entails Φ (Φ.shift.shift.subst (endS d)) := by
  rw [shift2_endS]; exact ent_refl _

theorem inner_endS (a b : Tm) (d : Bool) :
    (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift).subst Tm.var (endS d) =
      split (.neg (I.ofDir d)) a (I.ofDir d) b := by
  simp only [Tm.subst]; congr 1 <;> ssub

theorem inner0_eq (a b : Tm) :
    (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift).dinst .zero =
      split (.neg (.var 0)) a.dshift (.var 0) b.dshift := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst]; congr 1 <;> ssub

theorem endS_scoped (Ψ : Nat) (d : Bool) : ∀ i < Ψ + 1 + 1, (endS d i).Scoped Ψ := by
  intro i hi
  rcases i with _ | _ | i
  · trivial
  · cases d <;> trivial
  · show i < Ψ; omega

theorem hcompPath_typed (hS : SigClosed S) {Ψ Φ Γ A a b φ u p0 T}
    (h : HasTy0 S Ψ Φ Γ (hcomp (path A a b) φ u p0) T) : HasTy0 S Ψ Φ Γ (hcompPath A a b φ u p0) T := by
  obtain ⟨l, ⟨hP, hφ, hu, hp0, hside⟩, ch⟩ := gen_hcomp h rfl
  refine ch.transport ?_
  rw [hcompPath_eq]
  have hs := scoped_of_ty h
  have hw0 := wf_of_ty h
  have hA := HasTy0.pathLine hS hP
  have ha := HasTy0.pathLeft hS hP
  have hb := HasTy0.pathRight hS hP
  -- contexts
  let ψ : I := .or φ.shift (.or (.neg (.var 0)) (.var 0))
  have hψs : ψ.Scoped (Ψ + 1) := ⟨scoped_shift hφ, ⟨show 0 < Ψ + 1 by omega, show 0 < Ψ + 1 by omega⟩⟩
  have hΞs : (cof Φ.shift ψ).Scoped (Ψ + 1) := ⟨scoped_shift hs, hψs⟩
  have hR2s : (cof Φ.shift ψ).shift.Scoped (Ψ + 1 + 1) := scoped_shift hΞs
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hφ)
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0 : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  let ψ2 : I := .or (.neg (.var 1)) (.var 1)
  have hψ2s : ψ2.Scoped (Ψ + 1 + 1) := ⟨hv1, hv1⟩
  -- the line in the tube context
  have hA2 : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift ψ).shift Γ.dshift.dshift A.dshift (univ l) :=
    HasTy0.restrict hR2s (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS hA)
  -- the tube
  have hu2 := tube_skip hS hu
  rw [path_dshift_skip] at hu2
  have hU := HasTy0.papp hu2 hv1
  rw [Xp_var1] at hU
  have hR3 : (cof (cof Φ.shift ψ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hR2s, hφ2⟩
  have hR3e : I.Entails (cof (cof Φ.shift ψ).shift φ.shift.shift) (cof Φ φ).shift.shift :=
    ent_and_mono (ent_shift (ent_and_left Φ.shift ψ)) (ent_refl _)
  have hUr := HasTy0.restrict hR3 hR3e hU
  -- the inner system `[j = 0 ↦ a, j = 1 ↦ b]`
  have hR2Φ : I.Entails (cof Φ.shift ψ).shift Φ.shift.shift := ent_shift (ent_and_left Φ.shift ψ)
  have hΞ2s : (cof (cof Φ.shift ψ).shift ψ2).Scoped (Ψ + 1 + 1) := ⟨hR2s, hψ2s⟩
  have hXa : (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXb : (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hΞ2s, hv1⟩
  have hXaΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have hXbΦ : I.Entails (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) (cof Φ.shift ψ).shift :=
    ent_trans (ent_and_left _ _) (ent_and_left _ _)
  have ha2 : HasTy0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) Γ.dshift.dshift
      a.dshift.dshift A.dshift := by
    have h1 := HasTy0.restrict hXa (ent_trans hXaΦ hR2Φ) (HasTy0.dwk hS (HasTy0.dwk hS ha))
    have hf := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _) (HasTy0.restrict hXa hXaΦ hA2)
    rw [dshift_dset1_zero] at hf
    exact HasTy0.conv h1 (EqTm0.symm hf)
  have hb2 : HasTy0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift ψ2) (.var 1)) Γ.dshift.dshift
      b.dshift.dshift A.dshift := by
    have h1 := HasTy0.restrict hXb (ent_trans hXbΦ hR2Φ) (HasTy0.dwk hS (HasTy0.dwk hS hb))
    have hf := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _) (HasTy0.restrict hXb hXbΦ hA2)
    rw [dshift_dset1_one] at hf
    exact HasTy0.conv h1 (EqTm0.symm hf)
  have hXab : (cof (cof (cof (cof Φ.shift ψ).shift ψ2) (.neg (.var 1))) (.var 1)).Scoped (Ψ + 1 + 1) :=
    ⟨hXa, hv1⟩
  have hinner : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift ψ).shift ψ2) Γ.dshift.dshift
      (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift) A.dshift :=
    HasTy0.split hv1 hv1 (ent_and_right _ _) (HasTy0.restrict hΞ2s (ent_and_left _ _) hA2) ha2 hb2
      (EqTm0.absurd (ent_contra _ 1) (HasTy0.restrict hXab (ent_and_left _ _) ha2)
        (HasTy0.restrict hXab (ent_and_mono (ent_and_left _ _) (ent_refl _)) hb2))
  -- agreement of the tube with the inner system
  have hY : (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2).Scoped (Ψ + 1 + 1) := ⟨hR3, hψ2s⟩
  have hover : EqTm0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) Γ.dshift.dshift
      (papp (u.dsubst insI) (.var 1)) (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)
      A.dshift := by
    have hYU := HasTy0.restrict hY (ent_and_left _ _) hUr
    have hYI := HasTy0.restrict hY (ent_and_mono (ent_and_left _ _) (ent_refl _)) hinner
    have hYA := HasTy0.restrict hY (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA2
    have hpu := HasTy0.restrict hY (ent_trans (ent_and_left _ _) hR3e) hu2
    refine EqTm0.local (φ := .neg (.var 1)) (ψ := .var 1) hv1 hv1 (ent_and_right _ _) hYU hYI ?_ ?_
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have e1 := EqTm0.face (i := 1) (d := false) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA) (HasTy0.restrict hs1 (ent_and_left _ _) hYU)
      rw [papp_insI_dset1] at e1
      have e2 := EqTm0.pathZero (HasTy0.restrict hs1 (ent_and_left _ _) hpu)
      rw [Xp_zero] at e2
      have hf := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA)
      rw [dshift_dset1_zero] at hf
      have e3 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hYI)
      exact EqTm0.trans e1 (EqTm0.trans (EqTm0.conv e2 (EqTm0.symm hf)) (EqTm0.symm e3))
    · have hs1 : (cof (cof (cof (cof Φ.shift ψ).shift φ.shift.shift) ψ2) (.var 1)).Scoped (Ψ + 1 + 1) :=
        ⟨hY, hv1⟩
      have e1 := EqTm0.face (i := 1) (d := true) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA) (HasTy0.restrict hs1 (ent_and_left _ _) hYU)
      rw [papp_insI_dset1] at e1
      have e2 := EqTm0.pathOne (HasTy0.restrict hs1 (ent_and_left _ _) hpu)
      rw [Xp_one] at e2
      have hf := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_and_left _ _) hYA)
      rw [dshift_dset1_one] at hf
      have e3 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hYI)
      exact EqTm0.trans e1 (EqTm0.trans (EqTm0.conv e2 (EqTm0.symm hf)) (EqTm0.symm e3))
  have hsys : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift ψ).shift Γ.dshift.dshift
      (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) ψ2
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)) A.dshift :=
    HasTy0.split hφ2 hψ2s (ent_shift (ent_and_right Φ.shift ψ)) hA2 hUr hinner hover
  -- the base
  have hv0' : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hp0d : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift p0.dshift
      (path (A.ren id (upRen Nat.succ)) a.dshift b.dshift) := HasTy0.dwk hS hp0
  have hbase := HasTy0.papp hp0d hv0'
  rw [upDShift_dinst0] at hbase
  -- the side condition of the composition
  have hsys0 := HasTy0.dsubst hS hsys (r := .zero) trivial
  rw [dshift_dinst, sys0_eq] at hsys0
  have hinner0 := HasTy0.dsubst hS (Φ := cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (Γ := Γ.dshift) hinner (r := .zero) trivial
  rw [dshift_dinst, inner0_eq] at hinner0
  have hside' : EqTm0 S (Ψ + 1) (cof Φ.shift ψ) Γ.dshift
      (split φ.shift (papp (u.dinst .zero).dshift (.var 0)) (.or (.neg (.var 0)) (.var 0))
        (split (.neg (.var 0)) a.dshift (.var 0) b.dshift)) (papp p0.dshift (.var 0)) A := by
    have hΞA := HasTy0.restrict hΞs (ent_and_left _ _) hA
    have hΞb := HasTy0.restrict hΞs (ent_and_left _ _) hbase
    refine EqTm0.local (φ := φ.shift) (ψ := .or (.neg (.var 0)) (.var 0)) (scoped_shift hφ)
      ⟨hv0', hv0'⟩ (ent_and_right _ _) hsys0 hΞb ?_ ?_
    · have hs1 : (cof (cof Φ.shift ψ) φ.shift).Scoped (Ψ + 1) := ⟨hΞs, scoped_shift hφ⟩
      have s1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hsys0)
      have hsd : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (u.dinst .zero).dshift p0.dshift
          (path (A.ren id (upRen Nat.succ)) a.dshift b.dshift) := EqTm0.dwk hS hside
      have hsd1 := EqTm0.restrict hs1
        (ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)) hsd
      have s2 := EqTm0.papp hsd1 hv0' hv0' (I_eq_refl _)
      rw [upDShift_dinst0] at s2
      exact EqTm0.trans s1 s2
    · have hs1 : (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))).Scoped (Ψ + 1) := ⟨hΞs, ⟨hv0', hv0'⟩⟩
      have t1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs1 (ent_and_left _ _) hsys0)
      refine EqTm0.trans t1 ?_
      refine EqTm0.local (φ := .neg (.var 0)) (ψ := .var 0) hv0' hv0' (ent_and_right _ _)
        (HasTy0.restrict hs1 (ent_refl _) hinner0) (HasTy0.restrict hs1 (ent_and_left _ _) hΞb) ?_ ?_
      · have hs2 : (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.neg (.var 0))).Scoped (Ψ + 1) :=
          ⟨hs1, hv0'⟩
        have e1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hs2 (ent_and_left _ _) hinner0)
        have hA3 := HasTy0.restrict hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞA
        have e2 := EqTm0.face (i := 0) (d := false) hv0' (ent_and_right _ _) hA3
          (HasTy0.restrict hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞb)
        rw [papp_dshift_dset0] at e2
        have e3 := EqTm0.pathZero (HasTy0.restrict hs2
          (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)) hp0d)
        rw [show (A.ren id (upRen Nat.succ)).dinst .zero = (A.dinst .zero).dshift from upDShift_dinst_dir A false] at e3
        have hf := EqTm0.faceU (i := 0) (d := false) hv0' (ent_and_right _ _) hA3
        rw [dset0_eq] at hf
        exact EqTm0.trans e1 (EqTm0.symm (EqTm0.trans e2 (EqTm0.conv e3 (EqTm0.symm hf))))
      · have hs2 : (cof (cof (cof Φ.shift ψ) (.or (.neg (.var 0)) (.var 0))) (.var 0)).Scoped (Ψ + 1) :=
          ⟨hs1, hv0'⟩
        have e1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hs2 (ent_and_left _ _) hinner0)
        have hA3 := HasTy0.restrict hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞA
        have e2 := EqTm0.face (i := 0) (d := true) hv0' (ent_and_right _ _) hA3
          (HasTy0.restrict hs2 (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hΞb)
        rw [papp_dshift_dset0] at e2
        have e3 := EqTm0.pathOne (HasTy0.restrict hs2
          (ent_trans (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_left _ _)) hp0d)
        rw [show (A.ren id (upRen Nat.succ)).dinst .one = (A.dinst .one).dshift from upDShift_dinst_dir A true] at e3
        have hf := EqTm0.faceU (i := 0) (d := true) hv0' (ent_and_right _ _) hA3
        rw [dset0_eq] at hf
        exact EqTm0.trans e1 (EqTm0.symm (EqTm0.trans e2 (EqTm0.conv e3 (EqTm0.symm hf))))
  have hside'' : EqTm0 S (Ψ + 1) (cof Φ.shift ψ) Γ.dshift
      ((split φ.shift.shift (papp (u.dsubst insI) (.var 1)) ψ2
        (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)).dinst .zero)
      (papp p0.dshift (.var 0)) A := by rw [sys0_eq]; exact hside'
  have hbody := HasTy0.hcomp hA hψs hsys hbase hside''
  -- the endpoints
  have key : ∀ d : Bool,
      EqTm0 S Ψ Φ Γ ((hcomp A ψ (split φ.shift.shift (papp (u.dsubst insI) (.var 1)) ψ2
          (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift))
          (papp p0.dshift (.var 0))).dinst (I.ofDir d))
        (split (.neg (I.ofDir d)) a (I.ofDir d) b) (A.dinst (I.ofDir d)) ∧
      HasTy0 S Ψ Φ Γ (split (.neg (I.ofDir d)) a (I.ofDir d) b) (A.dinst (I.ofDir d)) := by
    intro d
    have hdd : (I.ofDir d).Scoped Ψ := by cases d <;> trivial
    have hor : I.Entails Φ (.or (.neg (I.ofDir d)) (I.ofDir d)) := by
      cases d
      · exact ent_negzero_or Φ
      · exact ent_one_or Φ
    have hb0 := HasTy0.dsubst hS hbody hdd
    have e1 := EqTm0.hcompFace (ent_trans hor (ent_or_right _ _)) hb0
    rw [dsub_end, sysEnd_eq] at e1
    have hsysE := HasTy0.isub hS (τ := endS d) hsys (endS_scoped Ψ d)
      (ent_and_intro (ent_shift2_endS Φ d) (ent_trans hor (ent_or_right _ _)))
      (by rw [ctxI_endS]; exact hw0)
    rw [ctxI_endS, dshift_endS, sysEnd_eq] at hsysE
    have e2 := EqTm0.splitR hor hsysE
    have hinE := HasTy0.isub hS (τ := endS d) hinner (endS_scoped Ψ d)
      (ent_and_intro (ent_and_intro (ent_shift2_endS Φ d) (ent_trans hor (ent_or_right _ _))) hor)
      (by rw [ctxI_endS]; exact hw0)
    rw [ctxI_endS, dshift_endS, inner_endS] at hinE
    exact ⟨EqTm0.trans e1 e2, hinE⟩
  have e0 := EqTm0.trans (key false).1 (EqTm0.splitL (ent_negzero Φ) (key false).2)
  have e1 := EqTm0.trans (key true).1 (EqTm0.splitR (ent_one Φ) (key true).2)
  exact HasTy0.plam hP hbody e0 e1

end KubusCore.Meta
