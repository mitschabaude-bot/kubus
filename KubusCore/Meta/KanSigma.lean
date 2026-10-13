import KubusCore.Meta.KanFill

/-!
# Metatheory: typing the contractum of `hcomp` in `Σ`
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem hcompSigma_eq (A B : Tm) (φ : I) (u u0 : Tm) :
    hcompSigma A B φ u u0 = pair (hcomp A φ (fst u) (fst u0))
      (comp (B.dshift.inst (hfill A φ (fst u) (fst u0))) φ (snd u) (snd u0)) := rfl

theorem inst_dshift_dinst (B f : Tm) (r : I) : (B.dshift.inst f).dinst r = B.inst (f.dinst r) := by
  simp only [Tm.inst, Tm.dinst, Tm.dsubst, dshift_eq, subst_subst]
  apply subst_congr
  · intro n; cases n <;> rfl
  · intro i; simp [I.subst, I.inst0]

theorem sigma_dshift (A B : Tm) : (sigma A B).dshift = sigma A.dshift B.dshift := by
  show sigma A.dshift (B.ren (upRen id) Nat.succ) = _
  rw [upRen_id_eq]; rfl

theorem hcompSigma_typed (hS : SigClosed S) {Ψ Φ Γ A B φ u u0 T}
    (h : HasTy0 S Ψ Φ Γ (hcomp (sigma A B) φ u u0) T) : HasTy0 S Ψ Φ Γ (hcompSigma A B φ u u0) T := by
  obtain ⟨l, ⟨hSig, hφ, hu, hu0, hside⟩, ch⟩ := gen_hcomp h rfl
  refine ch.transport ?_
  rw [hcompSigma_eq]
  have hs := scoped_of_ty h
  have hX : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift hX
  have hA := HasTy0.sigmaDom hS hSig
  have hB := HasTy0.sigmaCod hS hSig
  rw [sigma_dshift] at hu
  have hfu := HasTy0.fst hu
  have hsu := HasTy0.snd hu
  have hfu0 := HasTy0.fst hu0
  have hsu0 := HasTy0.snd hu0
  have hsf : EqTm0 S Ψ (cof Φ φ) Γ ((fst u).dinst .zero) (fst u0) A := EqTm0.fst hside
  have hss := EqTm0.snd hside
  obtain ⟨hf, hf0, hf1, hfφ⟩ := hfill_typed hS hA hφ hfu hfu0 hsf
  have ha := HasTy0.hcomp hA hφ hfu hfu0 hsf
  -- the line of the second component
  have hBd := HasTy0.dwk hS hB
  have hC : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (B.dshift.inst (hfill A φ (fst u) (fst u0))) (univ l) :=
    HasTy0.subst hS hBd hf
  -- the tube: `snd u : B[fst u] ≡ B[f]` under `φ`
  have hBdX := HasTy0.restrict (Φ' := (cof Φ φ).shift) hXs (ent_shift (ent_and_left Φ φ)) hBd
  have hfX := HasTy0.restrict hXs (ent_shift (ent_and_left Φ φ)) hf
  have hu' : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (snd u) (B.dshift.inst (hfill A φ (fst u) (fst u0))) :=
    HasTy0.conv hsu (HasTy0.inst_congr hS hBdX hfu hfX (EqTm0.symm hfφ))
  -- the base: `snd u0 : B[fst u0] ≡ B[f(0)]`
  have hf0t := HasTy0.dsubst hS hf (r := .zero) trivial
  rw [dshift_dinst] at hf0t
  have hu0' : HasTy0 S Ψ Φ Γ (snd u0) ((B.dshift.inst (hfill A φ (fst u) (fst u0))).dinst .zero) := by
    rw [inst_dshift_dinst]
    exact HasTy0.conv hsu0 (HasTy0.inst_congr hS hB hfu0 hf0t (EqTm0.symm hf0))
  -- the side condition
  have hBX := HasTy0.restrict hX (ent_and_left Φ φ) hB
  have hf0X := HasTy0.restrict hX (ent_and_left Φ φ) hf0t
  have hside' : EqTm0 S Ψ (cof Φ φ) Γ ((snd u).dinst .zero) (snd u0)
      ((B.dshift.inst (hfill A φ (fst u) (fst u0))).dinst .zero) := by
    rw [inst_dshift_dinst]
    have hfud := HasTy0.restrict hX (ent_refl _) (HasTy0.fst (HasTy0.dsubst hS (Φ := cof Φ φ) hu (r := .zero) trivial))
    rw [show A.dshift.subst Tm.var (I.inst0 .zero) = A from dshift_dinst A .zero] at hfud
    exact EqTm0.conv hss (HasTy0.inst_congr hS hBX hfud hf0X
      (EqTm0.trans hsf (EqTm0.symm (EqTm0.restrict hX (ent_and_left Φ φ) hf0))))
  have hcomp' := comp_typed hS hC hφ hu' hu0' hside'
  rw [inst_dshift_dinst] at hcomp'
  have hf1t := HasTy0.dsubst hS hf (r := .one) trivial
  rw [dshift_dinst] at hf1t
  have hb := HasTy0.conv hcomp' (HasTy0.inst_congr hS hB hf1t ha hf1)
  exact HasTy0.pair hSig ha hb

end KubusCore.Meta
