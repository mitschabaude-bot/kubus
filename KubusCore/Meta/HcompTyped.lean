import KubusCore.Meta.PresupLemmas

/-!
# Metatheory: typing the contracta of `hcomp` in `Π` and `(i : I) → A`

These two computation rules need no injectivity: the `hcomp` type is syntactically a `Π` or
`(i : I) → A`, so its components are typed by inversion.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem upRen_id_eq : upRen id = id := by funext n; cases n <;> rfl

theorem pi_dshift (A B : Tm) : (pi A B).dshift = pi A.dshift (B.ren (upRen id) Nat.succ) := rfl

theorem upShift_dshift_inst0 (B : Tm) :
    ((B.ren (upRen id) Nat.succ).ren (upRen Nat.succ) id).inst (.var 0) = B.dshift := by
  rw [upShift_inst0, upRen_id_eq]; rfl

theorem shift_dinst_comm (u : Tm) (r : I) : u.shift.dinst r = (u.dinst r).shift := by
  simp only [Tm.dinst, Tm.dsubst, shift_eq, subst_subst]
  apply subst_congr
  · intro n; rfl
  · intro i; simp [I.subst, I_subst_var]

theorem hcompPi_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u u0 T}
    (h : HasTy0 S Ψ Φ Γ (hcomp (pi A B) φ u u0) T) : HasTy0 S Ψ Φ Γ (hcompPi A B φ u u0) T := by
  obtain ⟨l, ⟨hPi, hφ, hu, hu0, hside⟩, ch⟩ := gen_hcomp h rfl
  refine ch.transport ?_
  have hs := scoped_of_ty h
  have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hA := HasTy0.piDom hS hPi
  have hB := HasTy0.piCod hS hPi
  -- the tube, applied to the bound variable
  have hAd : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A.dshift (univ l) :=
    HasTy0.dwk hS (HasTy0.restrict hs' (ent_and_left _ _) hA)
  have huw := HasTy0.wk hS hAd hu
  rw [pi_dshift] at huw
  simp only [Tm.shift, Tm.ren] at huw
  have hv : HasTy0 S (Ψ + 1) (cof Φ φ).shift (A.dshift :: Γ.dshift) (var 0) A.dshift.shift :=
    HasTy0.var (Wf0.cons hAd) rfl
  have hU := HasTy0.app huw hv
  rw [upShift_dshift_inst0] at hU
  -- the base, applied to the bound variable
  have hu0w := HasTy0.wk hS hA hu0
  simp only [Tm.shift, Tm.ren] at hu0w
  have hv0 : HasTy0 S Ψ Φ (A :: Γ) (var 0) A.shift := HasTy0.var (Wf0.cons hA) rfl
  have hU0 := HasTy0.app hu0w hv0
  rw [upShift_inst0] at hU0
  -- the side condition
  have hAc := HasTy0.restrict hs' (ent_and_left _ _) hA
  have hsw := EqTm0.wk hS hAc hside
  simp only [Tm.shift, Tm.ren] at hsw
  have hv0c : HasTy0 S Ψ (cof Φ φ) (A :: Γ) (var 0) A.shift := HasTy0.var (Wf0.cons hAc) rfl
  have hsd := EqTm0.app hsw (EqTm0.refl hv0c)
  rw [upShift_inst0] at hsd
  have hcomp' : HasTy0 S Ψ Φ (A :: Γ) (hcomp B φ (app u.shift (var 0)) (app u0.shift (var 0))) B := by
    refine HasTy0.hcomp hB hφ ?_ hU0 ?_
    · exact hU
    · have e : (app u.shift (var 0)).dinst .zero = app (u.dinst .zero).shift (var 0) := by
        show app (u.shift.dinst .zero) ((var 0).dinst .zero) = _
        rw [shift_dinst_comm]; rfl
      rw [e]
      exact hsd
  exact HasTy0.lam hPi hcomp'

def insI : Nat → I
  | 0 => .var 0
  | n + 1 => .var (n + 2)

theorem hcompIPi_eq (A : Tm) (φ : I) (u u0 : Tm) :
    hcompIPi A φ u u0 = plam (hcomp A φ.shift (papp (u.dsubst insI) (.var 1)) (papp u0.dshift (.var 0))) := by
  rfl

def skip1 : Nat → Nat
  | 0 => 0
  | n + 1 => n + 2

theorem ipi_dshift_ins_dinst (A : Tm) :
    ((A.ren id (upRen Nat.succ)).subst (fun n => (rS id n).ren id Nat.succ) (I.up (rI skip1))).dinst (.var 1) =
      A.dshift := by
  simp only [Tm.dinst, Tm.dsubst, ren_eq_subst, dshift_eq, subst_subst]
  refine subst_congr (fun n => rfl) (fun i => ?_) A
  rcases i with _ | _ | i <;> rfl

theorem dsubst_insI_dinst0 (u : Tm) : (u.dsubst insI).dinst .zero = (u.dinst .zero).dshift := by
  simp only [Tm.dinst, Tm.dsubst, dshift_eq, subst_subst]
  apply subst_congr
  · intro n; rfl
  · intro i; rcases i with _ | i <;> rfl

theorem hcompIPi_typed (hS : SigClosed S) {Ψ Φ Γ A φ u u0 T}
    (h : HasTy0 S Ψ Φ Γ (hcomp (ipi A) φ u u0) T) : HasTy0 S Ψ Φ Γ (hcompIPi A φ u u0) T := by
  obtain ⟨l, ⟨hI, hφ, hu, hu0, hside⟩, ch⟩ := gen_hcomp h rfl
  refine ch.transport ?_
  rw [hcompIPi_eq]
  have hs := scoped_of_ty h
  have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hA := HasTy0.ipiLine hS hI
  -- the tube, renamed past the new interval variable
  have hw : Wf0 S Ψ (cof Φ φ) Γ := (wf_of_ty h).restrict hs' (ent_and_left _ _)
  have hw2 := Wf0.dwk hS (Wf0.dwk hS hw)
  have hR : TyRen S (Ψ + 1) (cof Φ φ).shift Γ.dshift (Ψ + 2) (cof Φ φ).shift.shift Γ.dshift.dshift id skip1 :=
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
  have hu2 := (ren_ty hS hu).2 hR
  simp only [Tm.dshift, Tm.ren, Tm.subst] at hu2
  have hU := HasTy0.iapp (r := .var 1) hu2 (show (1 : Nat) < Ψ + 1 + 1 by omega)
  rw [ipi_dshift_ins_dinst] at hU
  have hU' : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift φ.shift).shift Γ.dshift.dshift
      (papp (u.dsubst insI) (.var 1)) A.dshift := by
    have e : u.subst (rS id) (rI skip1) = u.dsubst insI := by
      simp only [Tm.dsubst]; apply subst_congr
      · intro n; rfl
      · intro i; rcases i with _ | i <;> rfl
    rw [← e]; exact hU
  -- the base
  have hu0d := HasTy0.dwk hS hu0
  have hU0 := HasTy0.iapp (r := .var 0) (by simpa [Tm.dshift, Tm.ren] using hu0d) (show (0 : Nat) < Ψ + 1 by omega)
  rw [upDShift_dinst0] at hU0
  -- the side condition
  have hsd := EqTm0.dwk hS hside
  have hsd' := EqTm0.iapp (r := .var 0) (r' := .var 0) (by simpa [Tm.dshift, Tm.ren] using hsd)
    (show (0 : Nat) < Ψ + 1 by omega) (show (0 : Nat) < Ψ + 1 by omega) (I_eq_refl _)
  rw [upDShift_dinst0] at hsd'
  have body : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift
      (hcomp A φ.shift (papp (u.dsubst insI) (.var 1)) (papp u0.dshift (.var 0))) A := by
    refine HasTy0.hcomp hA (scoped_shift hφ) hU' hU0 ?_
    have e : (papp (u.dsubst insI) (.var 1)).dinst .zero = papp (u.dinst .zero).dshift (.var 0) := by
      show papp ((u.dsubst insI).dinst .zero) ((I.var 1).subst (I.inst0 .zero)) = _
      rw [dsubst_insI_dinst0]; rfl
    rw [e]; exact hsd'
  exact HasTy0.ilam hI body

end KubusCore.Meta
