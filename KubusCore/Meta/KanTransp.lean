import KubusCore.Meta.KanU

/-!
# Metatheory: typing the contracta of `transp` in `Π`, `Σ`, path types and `(i : I) → A`

The line's constancy on `φ` gives, by injectivity of the type former, the constancy of its
components, which the contracta need.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## Helpers -/

/-- Swap interval variables 0 and 1. -/
def swapI : Nat → I
  | 0 => .var 1
  | 1 => .var 0
  | n + 2 => .var (n + 2)

/-- Interval variable 1 to `0`, others kept. -/
def zero1 : Nat → I
  | 0 => .var 0
  | 1 => .zero
  | n + 2 => .var (n + 2)

def negI : Nat → I
  | 0 => .neg (.var 0)
  | n + 1 => .var (n + 1)

macro "ssub2" : tactic => `(tactic| (
  (try simp only [Tm.dinst, Tm.dsubst, Tm.dset, dshift_eq, shift_eq, ren_eq_subst, subst_subst, I_subst_subst]);
  first
    | refine subst_congr (fun n => ?_) (fun n => ?_) _
    | refine (subst_congr (fun n => ?_) (fun n => ?_) _).trans (subst_var _)
    | refine (subst_var _).symm.trans (subst_congr (fun n => ?_) (fun n => ?_) _)
  all_goals (rcases n with _ | _ | _ | n <;>
    simp [Tm.subst, I.subst, I.inst0, insI, skip1, skip1I, rS, rI, I.up, Tm.up, upRen, I.ofDir, I.shift,
      I.ren, endS, Tm.bind2, sk, swapI, zero1, negI] <;> omega)))

theorem transpIPi_eq (A : Tm) (φ : I) (u0 : Tm) :
    transpIPi A φ u0 = plam (transp (A.dsubst swapI) φ.shift (papp u0.dshift (.var 0))) := rfl

theorem I_shift2_swap (Φ : I) : Φ.shift.shift.subst swapI = Φ.shift.shift := by
  rw [I_shift_subst, I_shift_subst]; exact I_add2 Φ

theorem ctxI_swap2 (Γ : Ctx) : ctxI swapI Γ.dshift.dshift = Γ.dshift.dshift := by
  rw [ctxI_dshift_gen, ctxI_dshift_gen]; exact ctxI_add2 Γ

theorem swapI_scoped (Ψ : Nat) : ∀ i < Ψ + 1 + 1, (swapI i).Scoped (Ψ + 1 + 1) := by
  intro i hi; rcases i with _ | _ | i
  · show 1 < Ψ + 1 + 1; omega
  · show 0 < Ψ + 1 + 1; omega
  · show i + 2 < Ψ + 1 + 1; omega

theorem HasTy0.swap (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift t T) :
    HasTy0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift (t.dsubst swapI) (T.dsubst swapI) := by
  have := HasTy0.isub hS (τ := swapI) h (swapI_scoped Ψ) (by rw [I_shift2_swap]; exact ent_refl _)
    (by rw [ctxI_swap2]; exact wf_of_ty h)
  rwa [ctxI_swap2] at this

theorem EqTm0.swap (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {t u T : Tm} (h : EqTm0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift t u T) :
    EqTm0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift (t.dsubst swapI) (u.dsubst swapI) (T.dsubst swapI) := by
  have := EqTm0.isub hS (τ := swapI) h (swapI_scoped Ψ) (by rw [I_shift2_swap]; exact ent_refl _)
    (by rw [ctxI_swap2]; exact wf_of_eq h)
  rwa [ctxI_swap2] at this

theorem ipi_c1 (A : Tm) : (A.ren id (upRen Nat.succ)).dinst (.var 0) = A := upDShift_dinst0 A
theorem ipi_c2 (A : Tm) :
    (((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ)).ren id (upRen Nat.succ)).dinst (.var 0) = A.dsubst zero1 := by ssub2
theorem ipi_c3 (A : Tm) : (A.dsubst zero1).dsubst swapI = ((A.dsubst swapI).dinst .zero).dshift := by ssub2
theorem ipi_c4 (A : Tm) : ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ)).dinst (.var 0) = (A.dsubst swapI).dinst .zero := by ssub2
theorem ipi_c5 (A : Tm) : (A.dsubst swapI).dinst .one = A.subst Tm.var (I.up (I.inst0 .one)) := by ssub2
theorem univ_dsubst (l : Nat) (τ : Nat → I) : (Tm.univ l).dsubst τ = Tm.univ l := rfl

theorem transpIPi_typed (hS : SigClosed S) {Ψ Φ Γ A φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (ipi A) φ u0) T) : HasTy0 S Ψ Φ Γ (transpIPi A φ u0) T := by
  obtain ⟨l, ⟨hL, hφ, hc, hu0⟩, ch⟩ := gen_transpF h rfl
  refine ch.transport ?_
  rw [transpIPi_eq]
  have hA := HasTy0.ipiLine hS hL
  have hA' := HasTy0.swap hS hA
  rw [univ_dsubst] at hA'
  -- constancy of the swapped line
  have hcd := EqTm0.dwk hS hc
  have hci := EqTm0.ipiInj (A := A.ren id (upRen Nat.succ))
    (A' := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ)).ren id (upRen Nat.succ))
    (r := .var 0) hcd (show 0 < Ψ + 1 + 1 by omega)
  rw [ipi_c1, ipi_c2] at hci
  have hcs := EqTm0.swap hS (Φ := cof Φ φ) hci
  rw [ipi_c3, univ_dsubst] at hcs
  -- the base
  have hu0d := HasTy0.dwk hS hu0
  have hb := HasTy0.iapp (A := (A.subst Tm.var (I.up (I.inst0 .zero))).ren id (upRen Nat.succ))
    (r := .var 0) hu0d (show 0 < Ψ + 1 by omega)
  rw [ipi_c4] at hb
  have ht := HasTy0.transp hA' (scoped_shift hφ) hcs hb
  rw [ipi_c5] at ht
  exact HasTy0.ilam (HasTy0.dsubst hS hL (r := .one) trivial) ht

/-! ## `Π` -/

def wkS : Nat → Tm := fun n => .var (n + 1)


/-- The transported argument in `transpPi`. -/
def wT (A : Tm) (φ : I) : Tm :=
  transp (A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0)) (var 0)
def w0T (A : Tm) (φ : I) : Tm := transp (A.shift.dsubst negI) φ (var 0)

theorem transpPi_eq (A B : Tm) (φ : I) (u0 : Tm) :
    transpPi A B φ u0 = lam (A.dinst .one)
      (transp (B.subst (consT (wT A φ) wkS) I.var) φ (app u0.shift (w0T A φ))) := rfl

theorem bind2_eq_sk (r : I) : bind2 r = sk r 2 := by funext n; cases n <;> rfl

-- B[w] as an instantiation
theorem Bw_inst (B w : Tm) : B.subst (consT w wkS) I.var = (B.ren (upRen Nat.succ) id).inst w := by
  simp only [Tm.inst, ren_eq_subst, subst_subst]
  refine subst_congr (fun n => ?_) (fun n => rfl) _
  cases n <;> rfl

theorem Bw_dinst (B w : Tm) (r : I) :
    (B.subst (consT w wkS) I.var).dinst r =
      ((B.subst (Tm.up Tm.var) (I.inst0 r)).ren (upRen Nat.succ) id).inst (w.dinst r) := by
  simp only [Tm.inst, Tm.dinst, Tm.dsubst, ren_eq_subst, subst_subst]
  refine subst_congr (fun n => ?_) (fun n => ?_) _
  · rcases n with _ | n
    · rfl
    · simp [Tm.subst, Tm.up, consT, wkS, upRen, shift_eq, I.subst]
  · rcases n with _ | n <;> simp [I.subst, I.inst0, I_subst_var]

theorem Bw_dinst_dshift (B w : Tm) :
    ((B.subst (consT w wkS) I.var).dinst .zero).dshift =
      (((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen id) Nat.succ).ren (upRen Nat.succ) id).inst
        (w.dinst .zero).dshift := by
  simp only [Tm.inst, Tm.dinst, Tm.dsubst, dshift_eq, ren_eq_subst, subst_subst]
  refine subst_congr (fun n => ?_) (fun n => ?_) _
  · rcases n with _ | n
    · rfl
    · simp [Tm.subst, Tm.up, consT, wkS, upRen, shift_eq, I.subst]
  · rcases n with _ | n <;> simp [I.subst, I.inst0, I_subst_var]

theorem I_eq_or_negzero_r (r : I) : I.Eq (.or r (.neg .zero)) .one := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_or_negone_r (r : I) : I.Eq (.or r (.neg .one)) r := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl

theorem tySub_wk {Ψ Φ Γ C l} (hC : HasTy0 S Ψ Φ Γ C (univ l)) :
    TySub S Ψ Φ Γ Ψ Φ (C :: Γ) wkS I.var :=
  { bound := fun i hi => hi
    hscoped := scoped_of_wf (wf_of_ty hC)
    ent := by rw [I_subst_var]; exact ent_refl _
    look := fun x A hx => by
      show HasTy0 S Ψ Φ (C :: Γ) (var (x + 1)) (A.subst (fun n => .var (n + 1)) I.var)
      rw [← shift_eq]
      exact HasTy0.var (Wf0.cons hC) (by simp [Ctx.lookup, hx])
    wf := Wf0.cons hC }

theorem pw_L (C : Tm) (r : I) : C.dsubst (bind2 r) = C.subst Tm.var (sk r 2) := by rw [bind2_eq_sk]; rfl
theorem pw_L0s (C : Tm) : ((C.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).dinst .zero).dshift =
    C.subst Tm.var (sk (.or (.var 1) (.neg .zero)) 2) := by ssub2
theorem pw_shift_sk2 (A : Tm) (r : I) : (A.dinst .zero).dshift.shift.subst Tm.var (sk r 2) =
    (A.dinst .zero).shift.dshift.dshift := by ssub2
theorem pw_dset11 (C : Tm) : (C.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).dset 1 (I.ofDir true) =
    C.subst Tm.var (sk (.or .one (.neg (.var 0))) 2) := by ssub2
theorem pw_dset11' (C : Tm) : (C.subst Tm.var (sk (.or (.var 1) (.neg .zero)) 2)).dset 1 (I.ofDir true) =
    C.subst Tm.var (sk (.or .one (.neg .zero)) 2) := by ssub2
theorem pw_L0 (C : Tm) : (C.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).dinst .zero =
    C.subst Tm.var (sk (.or (.var 0) (.neg .zero)) 1) := by ssub2
theorem pw_L1 (C : Tm) : (C.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).dinst .one =
    C.subst Tm.var (sk (.or (.var 0) (.neg .one)) 1) := by ssub2
theorem pw_A1 (A : Tm) : (A.dinst .one).dshift.shift = A.shift.subst Tm.var (sk .one 1) := by ssub2

theorem wT_typed (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {A : Tm} {φ : I} {l : Nat} (hA : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l))
    (hφ : φ.Scoped Ψ)
    (hcD : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (univ l)) :
    HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (wT A φ) A.shift := by
  have hw0 := wf_unshift hS (wf_of_ty hA)
  have hs := scoped_of_wf hw0
  have hA1 : HasTy0 S Ψ Φ Γ (A.dinst .one) (univ l) := HasTy0.dsubst hS hA (r := .one) trivial
  have hwΔ : Wf0 S Ψ Φ (A.dinst .one :: Γ) := Wf0.cons hA1
  have hA1d := HasTy0.dwk hS hA1
  have hAw : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift (univ l) := HasTy0.wk hS hA1d hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hψ : (I.or φ.shift (.var 0)).Scoped (Ψ + 1) := ⟨scoped_shift hφ, hv0⟩
  -- the line
  have hL : HasTy0 S (Ψ + 1 + 1) Φ.shift.shift (Ctx.dshift (A.dinst .one :: Γ)).dshift
      (A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))) (univ l) := by
    have := HasTy0.isub hS (τ := bind2 (.or (.var 1) (.neg (.var 0)))) hAw
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (ent_bind2_shift _ (ent_refl _))
      (by rw [ctxI_bind2]; exact hwΔ.dwk2 hS)
    rwa [ctxI_bind2] at this
  -- constancy
  let Y : I := (cof Φ.shift (.or φ.shift (.var 0))).shift
  have hYs : Y.Scoped (Ψ + 1 + 1) := scoped_shift ⟨scoped_shift hs, hψ⟩
  have hYΦ : I.Entails Y Φ.shift.shift := ent_and_left _ _
  have hwY : Wf0 S (Ψ + 1 + 1) Y (ctxI (fun n => .var (n + 2)) (A.dinst .one :: Γ)) := by
    rw [ctxI_add2]; exact (hwΔ.dwk2 hS).restrict hYs hYΦ
  have hLY := HasTy0.restrict hYs hYΦ hL
  have hL0Y := HasTy0.restrict hYs hYΦ (HasTy0.dwk hS
    (HasTy0.dsubst hS (Φ := Φ.shift) (Γ := (Ctx.dshift (A.dinst .one :: Γ))) hL (r := .zero) trivial))
  have hconst : EqTm0 S (Ψ + 1 + 1) Y (Ctx.dshift (A.dinst .one :: Γ)).dshift
      (A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0)))))
      ((A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).dinst .zero).dshift (univ l) := by
    refine EqTm0.local (φ := φ.shift.shift) (ψ := .var 1) (scoped_shift (scoped_shift hφ)) hv1
      (ent_and_right _ _) hLY hL0Y ?_ ?_
    · -- on φ: the domain is constant
      have hZs : (cof Y φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hYs, scoped_shift (scoped_shift hφ)⟩
      have hZ : I.Entails (cof Y φ.shift.shift) (cof Φ φ).shift.shift :=
        ent_and_intro (ent_trans (ent_and_left _ _) hYΦ) (ent_and_right _ _)
      have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ⟩
      have hcDw : EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift
          (A.dinst .zero).dshift.shift (univ l) :=
        EqTm0.wk hS (HasTy0.restrict hXs (ent_shift (ent_and_left _ _)) hA1d) hcD
      have key : ∀ r : I, r.Scoped (Ψ + 1 + 1) →
          EqTm0 S (Ψ + 1 + 1) (cof Y φ.shift.shift) (Ctx.dshift (A.dinst .one :: Γ)).dshift
            (A.shift.subst Tm.var (sk r 2)) (A.dinst .zero).shift.dshift.dshift (univ l) := by
        intro r hr
        have := EqTm0.isub hS (τ := sk r 2) hcDw (sk_scoped hr (by omega)) (ent_sk2 r hZ)
          (by rw [ctxI_sk2]; exact (hwΔ.dwk2 hS).restrict hZs (ent_trans hZ (ent_shift (ent_shift (ent_and_left _ _)))))
        rwa [ctxI_sk2, pw_shift_sk2] at this
      have e1 := key (.or (.var 1) (.neg (.var 0))) ⟨hv1, hv0'⟩
      have e2 := key (.or (.var 1) (.neg .zero)) ⟨hv1, trivial⟩
      rw [pw_L0s, pw_L]
      exact EqTm0.trans e1 (EqTm0.symm e2)
    · -- on i = 1: the line is constant
      have hZs : (cof Y (.var 1)).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hZΦ : I.Entails (cof Y (.var 1)) (Φ.subst (fun n => .var (n + 2))) := by
        rw [I_add2]; exact ent_trans (ent_and_left _ _) hYΦ
      have hwZ : Wf0 S (Ψ + 1 + 1) (cof Y (.var 1)) (ctxI (fun n => .var (n + 2)) (A.dinst .one :: Γ)) :=
        hwY.restrict hZs (ent_and_left _ _)
      have e1 := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _) (HasTy0.restrict hZs (ent_and_left _ _) hLY)
      rw [pw_dset11] at e1
      have e2 := line_ieq hS hAw (k := 2) (Ψ' := Ψ + 1 + 1) (r := .or .one (.neg (.var 0))) (r' := .one) hZΦ
        ⟨trivial, hv0'⟩ trivial (by omega) (I_eq_or_one_l _) hwZ
      rw [ctxI_add2] at e2
      have hL0Z := HasTy0.restrict hZs (ent_and_left _ _) hL0Y
      rw [pw_L0s] at hL0Z
      have e3 := EqTm0.faceU (i := 1) (d := true) hv1 (ent_and_right _ _) hL0Z
      rw [pw_dset11'] at e3
      have e4 := line_ieq hS hAw (k := 2) (Ψ' := Ψ + 1 + 1) (r := .or .one (.neg .zero)) (r' := .one) hZΦ
        ⟨trivial, trivial⟩ trivial (by omega) (I_eq_or_one_l _) hwZ
      rw [ctxI_add2] at e4
      rw [pw_L0s]
      exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.symm (EqTm0.trans e3 e4)))
  -- the base
  have hwX : Wf0 S (Ψ + 1) Φ.shift (ctxI (fun n => .var (n + 1)) (A.dinst .one :: Γ)) := by
    rw [ctxI_add1]; exact wf_of_ty hAw
  have hb : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (var 0)
      ((A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).dinst .zero) := by
    rw [pw_L0]
    have e := line_ieq hS hAw (k := 1) (Ψ' := Ψ + 1) (r := .one) (r' := .or (.var 0) (.neg .zero)) (ent_refl _)
      trivial ⟨hv0, trivial⟩ (by omega) (I_eq_symm (I_eq_or_negzero_r _)) hwX
    rw [ctxI_add1] at e
    have hv := HasTy0.var (A := (A.dinst .one).dshift.shift) (x := 0) (wf_of_ty hAw) rfl
    rw [pw_A1] at hv
    exact HasTy0.conv hv e
  have ht := HasTy0.transp hL hψ hconst hb
  rw [pw_L1] at ht
  have e := line_ieq hS hAw (k := 1) (Ψ' := Ψ + 1) (r := .or (.var 0) (.neg .one)) (r' := .var 0) (ent_refl _)
    ⟨hv0, trivial⟩ hv0 (by omega) (I_eq_or_negone_r _) hwX
  rw [ctxI_add1, sk_var1] at e
  exact HasTy0.conv ht e

theorem p0_L (C : Tm) : C.dsubst negI = C.subst Tm.var (sk (.neg (.var 0)) 1) := by ssub2
theorem p0_L0s (C : Tm) : ((C.dsubst negI).dinst .zero).dshift = C.subst Tm.var (sk (.neg .zero) 1) := by ssub2
theorem p0_shift_sk1 (A : Tm) (r : I) : (A.dinst .zero).dshift.shift.subst Tm.var (sk r 1) =
    (A.dinst .zero).shift.dshift := by ssub2
theorem p0_L0 (C : Tm) : (C.dsubst negI).dinst .zero = C.subst Tm.var (sk (.neg .zero) 0) := by ssub2
theorem p0_L1 (C : Tm) : (C.dsubst negI).dinst .one = C.subst Tm.var (sk (.neg .one) 0) := by ssub2
theorem p0_A1 (A : Tm) : (A.dinst .one).shift = A.shift.subst Tm.var (sk .one 0) := by ssub2
theorem p0_A0 (A : Tm) : A.shift.subst Tm.var (sk .zero 0) = (A.dinst .zero).shift := by ssub2

theorem w0T_typed (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {A : Tm} {φ : I} {l : Nat}
    (hA : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l)) (hφ : φ.Scoped Ψ)
    (hcD : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (univ l)) :
    HasTy0 S Ψ Φ (A.dinst .one :: Γ) (w0T A φ) ((A.shift.dsubst negI).dinst .one) ∧
      EqTm0 S Ψ Φ (A.dinst .one :: Γ) ((A.shift.dsubst negI).dinst .one) (A.dinst .zero).shift (univ l) ∧
      HasTy0 S Ψ Φ (A.dinst .one :: Γ) (var 0) ((A.shift.dsubst negI).dinst .zero) := by
  have hw0 := wf_unshift hS (wf_of_ty hA)
  have hs := scoped_of_wf hw0
  have hA1 : HasTy0 S Ψ Φ Γ (A.dinst .one) (univ l) := HasTy0.dsubst hS hA (r := .one) trivial
  have hwΔ : Wf0 S Ψ Φ (A.dinst .one :: Γ) := Wf0.cons hA1
  have hA1d := HasTy0.dwk hS hA1
  have hAw : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift (univ l) := HasTy0.wk hS hA1d hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  -- the line
  have hL : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (A.shift.dsubst negI) (univ l) := by
    have := HasTy0.isub hS (τ := negI) hAw
      (fun i hi => by rcases i with _ | i
                      · exact hv0
                      · show i + 1 < Ψ + 1; omega)
      (by rw [I_shift_subst]; exact ent_refl _)
      (by rw [ctxI_dshift negI _ (fun i => rfl)]; exact wf_of_ty hAw)
    rwa [ctxI_dshift negI _ (fun i => rfl)] at this
  -- constancy
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ⟩
  have hcDw : EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift
      (A.dinst .zero).dshift.shift (univ l) :=
    EqTm0.wk hS (HasTy0.restrict hXs (ent_shift (ent_and_left _ _)) hA1d) hcD
  have key : ∀ r : I, r.Scoped (Ψ + 1) →
      EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
        (A.shift.subst Tm.var (sk r 1)) (A.dinst .zero).shift.dshift (univ l) := by
    intro r hr
    have := EqTm0.isub hS (τ := sk r 1) hcDw (sk_scoped hr (by omega)) (ent_sk1 r (ent_refl _))
      (by rw [ctxI_sk1]; exact wf_of_eq hcDw)
    rwa [ctxI_sk1, p0_shift_sk1] at this
  have hconst : EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
      (A.shift.dsubst negI) ((A.shift.dsubst negI).dinst .zero).dshift (univ l) := by
    rw [p0_L0s, p0_L]
    exact EqTm0.trans (key _ hv0) (EqTm0.symm (key (.neg .zero) trivial))
  -- the base
  have hwX : Wf0 S Ψ Φ (ctxI (fun n => .var (n + 0)) (A.dinst .one :: Γ)) := by
    rw [ctxI_add0]; exact hwΔ
  have hΦ0 : I.Entails Φ (Φ.subst (fun n => .var (n + 0))) := by rw [I_add0]; exact ent_refl _
  have hb : HasTy0 S Ψ Φ (A.dinst .one :: Γ) (var 0) ((A.shift.dsubst negI).dinst .zero) := by
    rw [p0_L0]
    have e := line_ieq hS hAw (k := 0) (Ψ' := Ψ) (r := .one) (r' := .neg .zero) hΦ0
      trivial trivial (by omega) (I_eq_symm I_eq_neg_zero) hwX
    rw [ctxI_add0] at e
    have hv := HasTy0.var (A := (A.dinst .one).shift) (x := 0) hwΔ rfl
    rw [p0_A1] at hv
    exact HasTy0.conv hv e
  have ht := HasTy0.transp hL hφ hconst hb
  have e := line_ieq hS hAw (k := 0) (Ψ' := Ψ) (r := .neg .one) (r' := .zero) hΦ0
    trivial trivial (by omega) I_eq_neg_one hwX
  rw [ctxI_add0, p0_A0] at e
  rw [p0_L1]
  exact ⟨by rw [← p0_L1]; exact ht, e, hb⟩

theorem cofw_inst (φ : I) (r : I) : (I.or φ.shift (.var 0)).subst (I.inst0 r) = .or φ r := by
  show I.or (φ.shift.subst (I.inst0 r)) r = _
  rw [I_shift_subst]; congr 1; exact I_subst_var φ

theorem pw_Lw0 (C : Tm) :
    (C.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .zero)) =
      C.subst Tm.var (sk (.or .zero (.neg (.var 0))) 1) := by ssub2
theorem pi_t1 (A : Tm) : (A.shift.dinst .zero).dshift = (A.dinst .zero).dshift.shift := by ssub2

theorem transpPi_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (pi A B) φ u0) T) : HasTy0 S Ψ Φ Γ (transpPi A B φ u0) T := by
  obtain ⟨l, ⟨hL, hφ, hc, hu0⟩, ch⟩ := gen_transpF h rfl
  refine ch.transport ?_
  rw [transpPi_eq]
  have hs := scoped_of_ty h
  have hA := HasTy0.piDom hS hL
  have hB := HasTy0.piCod hS hL
  have hcD := EqTm0.piInjDom (A' := (A.dinst .zero).dshift) hc
  have hw := wT_typed hS hA hφ hcD
  obtain ⟨hw0, E0, hv00⟩ := w0T_typed hS hA hφ hcD
  have hA1 : HasTy0 S Ψ Φ Γ (A.dinst .one) (univ l) := HasTy0.dsubst hS hA (r := .one) trivial
  have hwΔ : Wf0 S Ψ Φ (A.dinst .one :: Γ) := Wf0.cons hA1
  have hA1d := HasTy0.dwk hS hA1
  have hAw : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift (univ l) := HasTy0.wk hS hA1d hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  -- the line `B[w]`
  have hσ := (tySub_wk hA1d).cons (A := A) (a := wT A φ)
    (by show HasTy0 S (Ψ + 1) Φ.shift _ _ (A.subst (fun n => .var (n + 1)) I.var); rw [← shift_eq]; exact hw)
  have hBw : HasTy0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (B.subst (consT (wT A φ) wkS) I.var)
      (univ l) := (sub_ty hS hB).2.1 hσ
  -- constancy of `B[w]` on `φ`
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ⟩
  have hXΦ : I.Entails (cof Φ φ).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hA1dX := HasTy0.restrict hXs hXΦ hA1d
  have hcw := EqTm0.wk hS hA1dX hc
  have hwX := HasTy0.restrict hXs hXΦ hw
  have e1 := EqTm0.piInjCod (A := A.shift) (B := B.ren (upRen Nat.succ) id)
    (A' := (A.dinst .zero).dshift.shift)
    (B' := ((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen id) Nat.succ).ren (upRen Nat.succ) id)
    (a := wT A φ) hcw hwX
  have hcDw : EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) A.shift
      (A.dinst .zero).dshift.shift (univ l) := EqTm0.wk hS hA1dX hcD
  have hRz : HasTy0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
      ((pi A B).dinst .zero).dshift.shift (univ l) :=
    HasTy0.wk hS hA1dX (HasTy0.restrict hXs hXΦ (HasTy0.dwk hS (HasTy0.dsubst hS hL (r := .zero) trivial)))
  have hBz := HasTy0.piCod hS (A := (A.dinst .zero).dshift.shift)
    (B := ((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen id) Nat.succ).ren (upRen Nat.succ) id) hRz
  have hwz := HasTy0.conv hwX hcDw
  have hwd := HasTy0.restrict hXs hXΦ (HasTy0.dwk hS (HasTy0.dsubst hS hw (r := .zero) trivial))
  rw [pi_t1] at hwd
  have f1 : EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) (wT A φ) (var 0) A.shift :=
    EqTm0.transpFace (ent_trans (ent_shift (ent_and_right Φ φ)) (ent_or_left _ _)) hwX
  have f2 : EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ)) ((wT A φ).dinst .zero).dshift
      (var 0) (A.dinst .zero).dshift.shift :=
    EqTm0.transpFace (φ := ((I.or φ.shift (.var 0)).subst (I.inst0 .zero)).shift)
      (by rw [cofw_inst]; exact ent_trans (ent_shift (ent_and_right Φ φ)) (ent_shift (ent_or_left φ .zero))) hwd
  have he := EqTm0.trans (EqTm0.conv f1 hcDw) (EqTm0.symm f2)
  have e2 := HasTy0.inst_congr hS hBz hwz hwd he
  have hBC : EqTm0 S (Ψ + 1) (cof Φ φ).shift (Ctx.dshift (A.dinst .one :: Γ))
      (B.subst (consT (wT A φ) wkS) I.var) ((B.subst (consT (wT A φ) wkS) I.var).dinst .zero).dshift (univ l) := by
    rw [Bw_dinst_dshift, Bw_inst]
    exact EqTm0.trans e1 e2
  -- the base
  have hu0w := HasTy0.wk hS hA1 hu0
  have happ := HasTy0.app (A := (A.dinst .zero).shift)
    (B := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen Nat.succ) id) hu0w (HasTy0.conv hw0 E0)
  have hR0 : HasTy0 S Ψ Φ (A.dinst .one :: Γ) ((pi A B).dinst .zero).shift (univ l) :=
    HasTy0.wk hS hA1 (HasTy0.dsubst hS hL (r := .zero) trivial)
  have hBz0 := HasTy0.piCod hS (A := (A.dinst .zero).shift)
    (B := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen Nat.succ) id) hR0
  have hwd0 := HasTy0.dsubst hS hw (r := .zero) trivial
  rw [shift_dinst_comm] at hwd0
  have hline : EqTm0 S (Ψ + 1) Φ.shift (Ctx.dshift (A.dinst .one :: Γ)) (A.shift.dsubst negI)
      ((A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).subst (fun n => (Tm.var n).dshift)
        (I.up (I.inst0 .zero))) (univ l) := by
    have hwX1 : Wf0 S (Ψ + 1) Φ.shift (ctxI (fun n => .var (n + 1)) (A.dinst .one :: Γ)) := by
      rw [ctxI_add1]; exact wf_of_ty hAw
    have e := line_ieq hS hAw (k := 1) (Ψ' := Ψ + 1) (r := .neg (.var 0)) (r' := .or .zero (.neg (.var 0)))
      (ent_refl _) hv0 ⟨trivial, hv0⟩ (by omega) (I_eq_symm (I_eq_or_zero_l _)) hwX1
    rw [ctxI_add1] at e
    rw [p0_L, pw_Lw0]; exact e
  have heq0 : EqTm0 S Ψ Φ (A.dinst .one :: Γ) (w0T A φ) ((wT A φ).dinst .zero) (A.dinst .zero).shift := by
    refine EqTm0.conv (EqTm0.transp
      (A' := (A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))).subst (fun n => (Tm.var n).dshift)
        (I.up (I.inst0 .zero)))
      (φ' := (I.or φ.shift (.var 0)).subst (I.inst0 .zero)) (a' := var 0) hw0 (HasTy0.conv hwd0 (EqTm0.symm E0))
      hline ?_ ?_ (EqTm0.refl hv00)) E0
    · rw [cofw_inst]; exact ent_or_left _ _
    · rw [cofw_inst]; exact ent_or_elim (ent_refl _) (ent_zero _)
  have hbase : HasTy0 S Ψ Φ (A.dinst .one :: Γ) (app u0.shift (w0T A φ))
      ((B.subst (consT (wT A φ) wkS) I.var).dinst .zero) := by
    rw [Bw_dinst]
    exact HasTy0.conv happ (HasTy0.inst_congr hS hBz0 (HasTy0.conv hw0 E0) hwd0 heq0)
  have ht := HasTy0.transp hBw hφ hBC hbase
  rw [Bw_dinst] at ht
  -- the endpoint
  have hR1 : HasTy0 S Ψ Φ (A.dinst .one :: Γ) ((pi A B).dinst .one).shift (univ l) :=
    HasTy0.wk hS hA1 (HasTy0.dsubst hS hL (r := .one) trivial)
  have hBz1 := HasTy0.piCod hS (A := (A.dinst .one).shift)
    (B := (B.subst (Tm.up Tm.var) (I.inst0 .one)).ren (upRen Nat.succ) id) hR1
  have hwd1 := HasTy0.dsubst hS hw (r := .one) trivial
  rw [shift_dinst_comm] at hwd1
  have hvar : HasTy0 S Ψ Φ (A.dinst .one :: Γ) (var 0) (A.dinst .one).shift := HasTy0.var hwΔ rfl
  have heF : EqTm0 S Ψ Φ (A.dinst .one :: Γ) ((wT A φ).dinst .one) (var 0) (A.dinst .one).shift :=
    EqTm0.transpFace (φ := (I.or φ.shift (.var 0)).subst (I.inst0 .one))
      (by rw [cofw_inst]; exact ent_trans (ent_one Φ) (ent_or_right _ _)) hwd1
  have eF := HasTy0.inst_congr hS hBz1 hwd1 hvar heF
  rw [upShift_inst0] at eF
  exact HasTy0.lam (HasTy0.dsubst hS hL (r := .one) trivial) (HasTy0.conv ht eF)

/-! ## `Σ` -/

theorem cofn_inst (φ : I) (r : I) : (I.or φ.shift (.neg (.var 0))).subst (I.inst0 r) = .or φ (.neg r) := by
  show I.or (φ.shift.subst (I.inst0 r)) (.neg r) = _
  rw [I_shift_subst]; congr 1; exact I_subst_var φ

theorem tsf_A0 (A : Tm) (r : I) : (A.dinst .zero).dshift.subst Tm.var (sk r 2) = (A.dinst .zero).dshift.dshift := by
  ssub2
theorem tsf_Lsub1 (A : Tm) :
    (A.dsubst (bind2 (.and (.var 1) (.var 0)))).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .one)) =
      A.subst Tm.var (sk (.and .one (.var 0)) 1) := by ssub2
theorem tsf_L11 (A : Tm) :
    ((A.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one).dinst .one =
      (A.subst Tm.var (sk (.and .one (.var 0)) 1)).dinst .one := by ssub2

theorem transpFill_eq (A : Tm) (φ : I) (a : Tm) : transpFill A φ a =
    transp (A.dsubst (bind2 (.and (.var 1) (.var 0)))) (.or φ.shift (.neg (.var 0))) a.dshift := rfl

theorem tf_d1_eq (A : Tm) (φ : I) (a : Tm) : (transpFill A φ a).dinst .one =
    transp (A.subst Tm.var (sk (.and .one (.var 0)) 1)) (.or φ (.neg .one)) a := by
  show transp ((A.dsubst (bind2 (.and (.var 1) (.var 0)))).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .one)))
    ((I.or φ.shift (.neg (.var 0))).subst (I.inst0 .one)) (a.dshift.dinst .one) = _
  rw [tsf_Lsub1, cofn_inst, dshift_dinst]

theorem transpFill_typed (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {A : Tm} {φ : I} {a : Tm} {l : Nat}
    (hA : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l)) (hφ : φ.Scoped Ψ)
    (hcD : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (univ l))
    (ha : HasTy0 S Ψ Φ Γ a (A.dinst .zero)) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (transpFill A φ a) A ∧
      EqTm0 S Ψ Φ Γ ((transpFill A φ a).dinst .zero) a (A.dinst .zero) ∧
      EqTm0 S Ψ Φ Γ ((transpFill A φ a).dinst .one) (transp A φ a) (A.dinst .one) ∧
      EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (transpFill A φ a) a.dshift A := by
  have hw0 := wf_unshift hS (wf_of_ty hA)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hψ : (I.or φ.shift (.neg (.var 0))).Scoped (Ψ + 1) := ⟨scoped_shift hφ, hv0⟩
  have hL : HasTy0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift
      (A.dsubst (bind2 (.and (.var 1) (.var 0)))) (univ l) := by
    have := HasTy0.isub hS (τ := bind2 (.and (.var 1) (.var 0))) hA
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (ent_bind2_shift _ (ent_refl _))
      (by rw [ctxI_bind2]; exact hw0.dwk2 hS)
    rwa [ctxI_bind2] at this
  let Y : I := (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift
  have hYs : Y.Scoped (Ψ + 1 + 1) := scoped_shift ⟨scoped_shift hs, hψ⟩
  have hYΦ : I.Entails Y Φ.shift.shift := ent_and_left _ _
  have hwY : Wf0 S (Ψ + 1 + 1) Y (ctxI (fun n => .var (n + 2)) Γ) := by
    rw [ctxI_add2]; exact (hw0.dwk2 hS).restrict hYs hYΦ
  have hLY := HasTy0.restrict hYs hYΦ hL
  have hL0Y := HasTy0.restrict hYs hYΦ (HasTy0.dwk hS
    (HasTy0.dsubst hS (Φ := Φ.shift) (Γ := Γ.dshift) hL (r := .zero) trivial))
  have hconst : EqTm0 S (Ψ + 1 + 1) Y Γ.dshift.dshift
      (A.dsubst (bind2 (.and (.var 1) (.var 0))))
      ((A.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift (univ l) := by
    refine EqTm0.local (φ := φ.shift.shift) (ψ := .neg (.var 1)) (scoped_shift (scoped_shift hφ)) hv1
      (ent_and_right _ _) hLY hL0Y ?_ ?_
    · have hZs : (cof Y φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hYs, scoped_shift (scoped_shift hφ)⟩
      have hZ : I.Entails (cof Y φ.shift.shift) (cof Φ φ).shift.shift :=
        ent_and_intro (ent_trans (ent_and_left _ _) hYΦ) (ent_and_right _ _)
      have key : ∀ r : I, r.Scoped (Ψ + 1 + 1) →
          EqTm0 S (Ψ + 1 + 1) (cof Y φ.shift.shift) Γ.dshift.dshift
            (A.subst Tm.var (sk r 2)) (A.dinst .zero).dshift.dshift (univ l) := by
        intro r hr
        have := EqTm0.isub hS (τ := sk r 2) hcD (sk_scoped hr (by omega)) (ent_sk2 r hZ)
          (by rw [ctxI_sk2]; exact (hw0.dwk2 hS).restrict hZs (ent_trans hZ (ent_shift (ent_shift (ent_and_left _ _)))))
        rwa [ctxI_sk2, tsf_A0] at this
      have e1 := key (.and (.var 1) (.var 0)) ⟨hv1, hv0'⟩
      have e2 := key (.and (.var 1) .zero) ⟨hv1, trivial⟩
      rw [tf_L0s, pw_L]
      exact EqTm0.trans e1 (EqTm0.symm e2)
    · have hZs : (cof Y (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hYs, hv1⟩
      have hZΦ : I.Entails (cof Y (.neg (.var 1))) (Φ.subst (fun n => .var (n + 2))) := by
        rw [I_add2]; exact ent_trans (ent_and_left _ _) hYΦ
      have hwZ : Wf0 S (Ψ + 1 + 1) (cof Y (.neg (.var 1))) (ctxI (fun n => .var (n + 2)) Γ) :=
        hwY.restrict hZs (ent_and_left _ _)
      have hY1 : I.Entails (cof Y (.neg (.var 1))) (I.lit 1 false) := ent_and_right _ (.neg (.var 1))
      have e1 := EqTm0.faceU (i := 1) (d := false) hv1 hY1 (HasTy0.restrict hZs (ent_and_left _ _) hLY)
      rw [tf_L1] at e1
      have e2 := line_ieq hS hA (k := 2) (Ψ' := Ψ + 1 + 1) (r := .and .zero (.var 0)) (r' := .zero) hZΦ
        ⟨trivial, hv0'⟩ trivial (by omega) (I_eq_and_zero _) hwZ
      rw [ctxI_add2] at e2
      have hL0Z := HasTy0.restrict hZs (ent_and_left _ _) hL0Y
      rw [tf_L0s] at hL0Z
      have e3 := EqTm0.faceU (i := 1) (d := false) hv1 hY1 hL0Z
      rw [tf_L0s1] at e3
      have e4 := line_ieq hS hA (k := 2) (Ψ' := Ψ + 1 + 1) (r := .and .zero .zero) (r' := .zero) hZΦ
        ⟨trivial, trivial⟩ trivial (by omega) (I_eq_and_zero _) hwZ
      rw [ctxI_add2] at e4
      rw [tf_L0s]
      exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.symm (EqTm0.trans e3 e4)))
  have hwX : Wf0 S (Ψ + 1) Φ.shift (ctxI (fun n => .var (n + 1)) Γ) := by
    rw [ctxI_add1]; exact wf_of_ty hA
  have ha' : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift a.dshift
      ((A.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    rw [tf_L0]
    have e := line_ieq hS hA (k := 1) (Ψ' := Ψ + 1) (r := .zero) (r' := .and (.var 0) .zero) (ent_refl _) trivial
      ⟨hv0, trivial⟩ (by omega) (I_eq_symm (I_eq_and_zero_r _)) hwX
    rw [ctxI_add1, sk_zero1] at e
    exact HasTy0.conv (HasTy0.dwk hS ha) e
  have ht0 := HasTy0.transp hL hψ hconst ha'
  have eC : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift ((A.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one) A (univ l) := by
    have e := line_ieq hS hA (k := 1) (Ψ' := Ψ + 1) (r := .and (.var 0) .one) (r' := .var 0) (ent_refl _)
      ⟨hv0, trivial⟩ hv0 (by omega) (I_eq_and_one_r _) hwX
    rw [ctxI_add1, sk_var1] at e
    rw [tf_L1']; exact e
  have htf : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (transpFill A φ a) A := HasTy0.conv ht0 eC
  refine ⟨htf, ?_, ?_, ?_⟩
  · have h0 := HasTy0.dsubst hS ht0 (r := .zero) trivial
    have eC0 := EqTm0.dsubst hS eC (r := .zero) trivial
    have hf : EqTm0 S Ψ Φ Γ ((transpFill A φ a).dinst .zero) (a.dshift.dinst .zero) _ :=
      EqTm0.transpFace (φ := (I.or φ.shift (.neg (.var 0))).subst (I.inst0 .zero))
        (by rw [cofn_inst]; exact ent_trans (ent_negzero Φ) (ent_or_right _ _)) h0
    rw [dshift_dinst] at hf
    exact EqTm0.conv hf eC0
  · have h1 : HasTy0 S Ψ Φ Γ ((transpFill A φ a).dinst .one) _ := HasTy0.dsubst hS ht0 (r := .one) trivial
    rw [tf_d1_eq, tsf_L11] at h1
    have hline : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift (A.subst Tm.var (sk (.and .one (.var 0)) 1)) A (univ l) := by
      have e := line_ieq hS hA (k := 1) (Ψ' := Ψ + 1) (r := .and .one (.var 0)) (r' := .var 0) (ent_refl _)
        ⟨trivial, hv0⟩ hv0 (by omega) (I_eq_and_one_l _) hwX
      rwa [ctxI_add1, sk_var1] at e
    have eL1 := EqTm0.dsubst hS hline (r := .one) trivial
    have eL0 := EqTm0.dsubst hS hline (r := .zero) trivial
    have h2 := HasTy0.transp hA hφ hcD ha
    have e := EqTm0.transp h1 (HasTy0.conv h2 (EqTm0.symm eL1)) hline (ent_neg_one φ) (ent_or_left _ _)
      (EqTm0.refl (HasTy0.conv ha (EqTm0.symm eL0)))
    rw [tf_d1_eq]
    exact EqTm0.conv e eL1
  · exact EqTm0.transpFace (ent_trans (ent_shift (ent_and_right Φ φ)) (ent_or_left _ _))
      (HasTy0.restrict (scoped_shift ⟨hs, hφ⟩) (ent_shift (ent_and_left _ _)) htf)


theorem transpSigma_eq (A B : Tm) (φ : I) (u0 : Tm) : transpSigma A B φ u0 =
    pair (transp A φ (fst u0)) (transp (B.inst (transpFill A φ (fst u0))) φ (snd u0)) := rfl

theorem tsg_inst_dinst (B a : Tm) (r : I) :
    (B.inst a).dinst r = (B.subst (Tm.up Tm.var) (I.inst0 r)).inst (a.dinst r) := by
  simp only [Tm.inst, Tm.dinst, Tm.dsubst, subst_subst]
  refine subst_congr (fun n => ?_) (fun n => ?_) _
  · rcases n with _ | n
    · rfl
    · simp [Tm.subst, Tm.up, shift_eq]
  · rcases n with _ | n <;> simp [I.subst, I.inst0, I_subst_var]

theorem tsg_inst_dinst_dshift (B a : Tm) :
    ((B.inst a).dinst .zero).dshift =
      ((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen id) Nat.succ).inst (a.dinst .zero).dshift := by
  simp only [Tm.inst, Tm.dinst, Tm.dsubst, dshift_eq, ren_eq_subst, subst_subst]
  refine subst_congr (fun n => ?_) (fun n => ?_) _
  · rcases n with _ | n
    · rfl
    · simp [Tm.subst, Tm.up, shift_eq, I.subst, upRen]
  · rcases n with _ | n <;> simp [I.subst, I.inst0, I_subst_var]

theorem transpSigma_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (sigma A B) φ u0) T) : HasTy0 S Ψ Φ Γ (transpSigma A B φ u0) T := by
  obtain ⟨l, ⟨hL, hφ, hc, hu0⟩, ch⟩ := gen_transpF h rfl
  refine ch.transport ?_
  rw [transpSigma_eq]
  have hs := scoped_of_ty h
  have hA := HasTy0.sigmaDom hS hL
  have hB := HasTy0.sigmaCod hS hL
  have hcD := EqTm0.sigmaInjDom (A' := (A.dinst .zero).dshift) hc
  have hf0 := HasTy0.fst (A := A.dinst .zero) (B := B.subst (Tm.up Tm.var) (I.inst0 .zero)) hu0
  have hs0 := HasTy0.snd (A := A.dinst .zero) (B := B.subst (Tm.up Tm.var) (I.inst0 .zero)) hu0
  obtain ⟨htf, e0, e1, eX⟩ := transpFill_typed hS hA hφ hcD hf0
  have hBa := HasTy0.subst hS hB htf
  -- constancy of the second line
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ⟩
  have hXΦ : I.Entails (cof Φ φ).shift Φ.shift := ent_shift (ent_and_left _ _)
  have haX := HasTy0.restrict hXs hXΦ htf
  have ec := EqTm0.sigmaInjCod (A := A) (B := B) (A' := (A.dinst .zero).dshift)
    (B' := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen id) Nat.succ) hc haX
  have hRz : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift ((sigma A B).dinst .zero).dshift (univ l) :=
    HasTy0.restrict hXs hXΦ (HasTy0.dwk hS (HasTy0.dsubst hS hL (r := .zero) trivial))
  have hBz := HasTy0.sigmaCod hS (A := (A.dinst .zero).dshift)
    (B := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (upRen id) Nat.succ) hRz
  have haz := HasTy0.conv haX hcD
  have had := HasTy0.restrict hXs hXΦ (HasTy0.dwk hS (HasTy0.dsubst hS htf (r := .zero) trivial))
  have he := EqTm0.trans (EqTm0.conv eX hcD) (EqTm0.symm (EqTm0.restrict hXs hXΦ (EqTm0.dwk hS e0)))
  have e2 := HasTy0.inst_congr hS hBz haz had he
  have hBC : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (B.inst (transpFill A φ (fst u0)))
      ((B.inst (transpFill A φ (fst u0))).dinst .zero).dshift (univ l) := by
    rw [tsg_inst_dinst_dshift]; exact EqTm0.trans ec e2
  -- the base
  have hB0 := HasTy0.sigmaCod hS (HasTy0.dsubst hS hL (r := .zero) trivial)
  have had0 := HasTy0.dsubst hS htf (r := .zero) trivial
  have hbase : HasTy0 S Ψ Φ Γ (snd u0) ((B.inst (transpFill A φ (fst u0))).dinst .zero) := by
    rw [tsg_inst_dinst]
    exact HasTy0.conv hs0 (HasTy0.inst_congr hS hB0 hf0 had0 (EqTm0.symm e0))
  have ht := HasTy0.transp hBa hφ hBC hbase
  rw [tsg_inst_dinst] at ht
  have hB1 := HasTy0.sigmaCod hS (HasTy0.dsubst hS hL (r := .one) trivial)
  have had1 := HasTy0.dsubst hS htf (r := .one) trivial
  have htr := HasTy0.transp hA hφ hcD hf0
  exact HasTy0.pair (A := A.dinst .one) (B := B.subst (Tm.up Tm.var) (I.inst0 .one))
    (HasTy0.dsubst hS hL (r := .one) trivial) htr
    (HasTy0.conv ht (HasTy0.inst_congr hS hB1 had1 htr e1))

/-! ## Path types -/

theorem transpPath_typed (hS : SigClosed S) {Ψ Φ Γ A a b φ p0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (path A a b) φ p0) T) : HasTy0 S Ψ Φ Γ (transpPath A a b φ p0) T := by
  sorry

end KubusCore.Meta
