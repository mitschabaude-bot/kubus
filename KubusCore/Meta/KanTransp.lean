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

macro "ssub2" : tactic => `(tactic| (
  (try simp only [Tm.dinst, Tm.dsubst, Tm.dset, dshift_eq, shift_eq, ren_eq_subst, subst_subst, I_subst_subst]);
  first
    | refine subst_congr (fun n => ?_) (fun n => ?_) _
    | refine (subst_congr (fun n => ?_) (fun n => ?_) _).trans (subst_var _)
    | refine (subst_var _).symm.trans (subst_congr (fun n => ?_) (fun n => ?_) _)
  all_goals (rcases n with _ | _ | _ | n <;>
    simp [Tm.subst, I.subst, I.inst0, insI, skip1, skip1I, rS, rI, I.up, Tm.up, upRen, I.ofDir, I.shift,
      I.ren, endS, Tm.bind2, sk, swapI, zero1] <;> omega)))

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

theorem transpPi_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (pi A B) φ u0) T) : HasTy0 S Ψ Φ Γ (transpPi A B φ u0) T := by
  sorry

theorem transpSigma_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (sigma A B) φ u0) T) : HasTy0 S Ψ Φ Γ (transpSigma A B φ u0) T := by
  sorry

theorem transpPath_typed (hS : SigClosed S) {Ψ Φ Γ A a b φ p0 T}
    (h : HasTy0 S Ψ Φ Γ (transp (path A a b) φ p0) T) : HasTy0 S Ψ Φ Γ (transpPath A a b φ p0) T := by
  sorry

end KubusCore.Meta
