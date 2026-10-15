import Model.Whnf.Kan2DataFillH

/-!
# Congruence of heterogeneous fillers

The judgmental congruence of the fillers `fill C ψ u u0`, the heterogeneous analogue of `hfill_cong`
(`Kan2Comp.lean`): `fill` is a `comp` along the line `C(i ∧ j)`, so this is `comp_cong` with the tubes
related by `fillTubeH_eq`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- Congruence of heterogeneous fillers. -/
theorem fill_cong (hW : WfSig S) {Ψ : Nat} {C C' u u' u0 u0' : Tm} {ψ ψ' : I}
    (hF : HasTy0 S (Ψ + 1) .one [] (Tm.fill C ψ u u0) C) (hF' : HasTy0 S (Ψ + 1) .one [] (Tm.fill C' ψ' u' u0') C)
    (hCC : ∃ l, EqTm0 S (Ψ + 1) .one [] C C' (.univ l))
    (huu : EqTm0 S (Ψ + 1) (cof .one ψ).shift [] u u' C) (hu0 : EqTm0 S Ψ .one [] u0 u0' (C.dinst .zero))
    (h12 : I.Entails ψ ψ') (h21 : I.Entails ψ' ψ) :
    EqTm0 S (Ψ + 1) .one [] (Tm.fill C ψ u u0) (Tm.fill C' ψ' u' u0') C := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hCe⟩ := hCC
  have hCt : HasTy0 S (Ψ + 1) (I.one).shift (Ctx.dshift []) C (.univ l) := (presup hW hCe).1
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hone : (I.one).shift.Scoped (Ψ + 1) := KubusCore.Meta.scoped_shift (show I.one.Scoped Ψ from trivial)
  -- the ends of the line `C(i ∧ j)`
  have eC1 : EqTm0 S (Ψ + 1) (I.one).shift (Ctx.dshift []) C
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) (.univ l) := by
    rw [tf_L1']
    have e := HasTy0.sk1_ieq hS hCt (r := .var 0) (r' := .and (.var 0) .one) hv0 ⟨hv0, trivial⟩
      (I_eq_symm (I_eq_and_one_r _)) hone (ent_refl _)
    rwa [sk_var1] at e
  have eC0 : EqTm0 S (Ψ + 1) (I.one).shift (Ctx.dshift []) ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero)
      (C.dinst .zero).dshift (.univ l) := by
    rw [tf_L0]
    have e := HasTy0.sk1_ieq hS hCt (r := .and (.var 0) .zero) (r' := .zero) ⟨hv0, trivial⟩ trivial
      (I_eq_and_zero_r _) hone (ent_refl _)
    rwa [sk_zero1] at e
  -- the lines
  have hDD : EqTm0 S (Ψ + 1 + 1) .one [] (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.univ l) :=
    EqTm0.isub hS (τ := Tm.bind2 (.and (.var 1) (.var 0))) hCe
      (fun i hi => by
        rcases i with _ | i
        · exact ⟨show 1 < Ψ + 1 + 1 by omega, show 0 < Ψ + 1 + 1 by omega⟩
        · show i + 2 < Ψ + 1 + 1; omega)
      (ent_one _) (Wf0.nil trivial)
  have ht := fillTubeH_eq hS hF hF' (.inl ⟨l, hCt⟩) (.inr ⟨l, hDD⟩) huu hu0 h12
  have hb : EqTm0 S (Ψ + 1) .one [] u0.dshift u0'.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) :=
    EqTm0.conv (EqTm0.dwk hS hu0) (EqTm0.symm eC0)
  have hc : HasTy0 S (Ψ + 1) .one [] (Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      (.or ψ.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ u u0) u0.dshift)
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) := HasTy0.conv hF eC1
  have hc' : HasTy0 S (Ψ + 1) .one [] (Tm.comp (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      (.or ψ'.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ' u' u0') u0'.dshift)
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) := HasTy0.conv hF' eC1
  have e := comp_cong hS hc hc' hDD
    (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _)) (ent_or_right _ _))
    (ent_or_elim (ent_trans (ent_shift h21) (ent_or_left _ _)) (ent_or_right _ _)) ht hb
  exact EqTm0.conv e (EqTm0.symm eC1)

end

end Model.Whnf
