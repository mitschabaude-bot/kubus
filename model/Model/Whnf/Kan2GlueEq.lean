import Model.Whnf.Kan2Comp

/-!
# Judgmental equality of the tubes of compositions in Glue types

Fillers are congruent in any context of a face (`hfill_congΦ`), and the tube of the base composition of
`hcompGlue` (`glueTube`) is congruent in its components (`glueTube_eq`).
-/

set_option autoImplicit false

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem fillTube_eqΦ (hW : WfSig S) {Ψ : Nat} {Φ : I} {A A' u u' u0 u0' T T' : Tm} {φ φ' : I}
    (h : HasTy0 S (Ψ + 1) Φ.shift [] (hcomp A.dshift (.or φ.shift (.neg (.var 0))) (fillTube φ u u0) u0.dshift) T)
    (h' : HasTy0 S (Ψ + 1) Φ.shift [] (hcomp A'.dshift (.or φ'.shift (.neg (.var 0))) (fillTube φ' u' u0') u0'.dshift) T')
    (hAA : A = A' ∨ ∃ l, EqTm0 S Ψ Φ [] A A' (univ l))
    (huu : EqTm0 S (Ψ + 1) (cof Φ φ).shift [] u u' A.dshift) (hu0 : EqTm0 S Ψ Φ [] u0 u0' A)
    (h12 : I.Entails φ φ') :
    EqTm0 S (Ψ + 1 + 1) (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift [] (fillTube φ u u0) (fillTube φ' u' u0')
      A.dshift.dshift := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨-, hψ, hsL, -, -⟩, -⟩ := gen_hcomp h rfl
  obtain ⟨l2, ⟨-, -, hsR, -, -⟩, -⟩ := gen_hcomp h' rfl
  have hΦs : Φ.shift.Scoped (Ψ + 1) := scoped_of_ty h
  have hC : (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift.Scoped (Ψ + 1 + 1) := scoped_shift ⟨hΦs, hψ⟩
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift hψ.1
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hCC : I.Entails (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift
      (cof Φ.shift (.or φ'.shift (.neg (.var 0)))).shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _))
      (ent_or_right _ _)))
  have hCΦ : I.Entails (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift Φ.shift.shift :=
    ent_shift (ent_and_left _ _)
  have hsR' : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift [] (fillTube φ' u' u0')
      A.dshift.dshift := by
    rcases hAA with rfl | ⟨l, e⟩
    · exact HasTy0.restrict hC hCC hsR
    · have eA := EqTm0.restrict hC hCΦ (EqTm0.dwk hS (EqTm0.dwk hS e))
      exact HasTy0.conv (HasTy0.restrict hC hCC hsR) (EqTm0.symm eA)
  refine EqTm0.local (φ := φ.shift.shift) (ψ := .neg (.var 1)) hφ2 hv1 (ent_trans (ent_and_right _ _) (ent_refl _))
    hsL hsR' ?_ ?_
  · have hc : (cof (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hC, hφ2⟩
    have s1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have s2 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_shift h12)))
      (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m : EqTm0 S (Ψ + 1 + 1) (cof (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift φ.shift.shift) [] _ _ _ :=
      EqTm0.isub hS huu (τ := bind2 (.and (.var 1) (.var 0)))
        (fun i hi => by
          rcases i with _ | i
          · exact ⟨show 1 < Ψ + 1 + 1 by omega, show 0 < Ψ + 1 + 1 by omega⟩
          · show i + 2 < Ψ + 1 + 1; omega)
        (ent_bind2_shift _ (ent_and_intro (ent_trans (ent_and_left _ _) hCΦ) (ent_and_right _ _))) (Wf0.nil hc)
    rw [dshift_bind2] at m
    exact EqTm0.trans s1 (EqTm0.trans m (EqTm0.symm s2))
  · have hc : (cof (cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hC, hv1⟩
    have t1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have t2 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m := EqTm0.restrict hc (ent_trans (ent_and_left _ _) hCΦ) (EqTm0.dwk hS (EqTm0.dwk hS hu0))
    exact EqTm0.trans t1 (EqTm0.trans m (EqTm0.symm t2))

/-- Congruence of fillers, in the context of a face. -/
theorem hfill_congΦ (hW : WfSig S) {Ψ : Nat} {Φ : I} {A A' v v' v0 v0' : Tm} {φ φ' : I}
    (h : HasTy0 S (Ψ + 1) Φ.shift [] (hfill A φ v v0) A.dshift)
    (h' : HasTy0 S (Ψ + 1) Φ.shift [] (hfill A' φ' v' v0') A.dshift)
    (hAA : A = A' ∨ ∃ l, EqTm0 S Ψ Φ [] A A' (univ l))
    (huu : EqTm0 S (Ψ + 1) (cof Φ φ).shift [] v v' A.dshift) (hv0 : EqTm0 S Ψ Φ [] v0 v0' A)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) :
    EqTm0 S (Ψ + 1) Φ.shift [] (hfill A φ v v0) (hfill A' φ' v' v0') A.dshift := by
  have hS := sigClosed_of_wfSig hW
  have ht := fillTube_eqΦ hW h h' hAA huu hv0 h12
  obtain ⟨l1, ⟨hA1, -, -, -, -⟩, -⟩ := gen_hcomp h rfl
  have hΦs : Φ.shift.Scoped (Ψ + 1) := scoped_of_ty h
  obtain ⟨l, eA⟩ : ∃ l, EqTm0 S (Ψ + 1) Φ.shift [] A.dshift A'.dshift (univ l) := by
    rcases hAA with rfl | ⟨l, e⟩
    · exact ⟨l1, EqTm0.refl hA1⟩
    · exact ⟨l, EqTm0.dwk hS e⟩
  have hb := EqTm0.dwk hS hv0
  rw [hfill_eq] at h h' ⊢
  exact EqTm0.hcomp h h' eA (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _)) (ent_or_right _ _))
    (ent_or_elim (ent_trans (ent_shift h21) (ent_or_left _ _)) (ent_or_right _ _)) ht hb

/-- Congruence of the tube of the base composition of `hcompGlue`. -/
theorem glueTube_eq (hW : WfSig S) {Ψ : Nat} {A A' T T' e e' u u' a0 a0' : Tm} {φ φ' ψ ψ' : I}
    (hsL : HasTy0 S (Ψ + 1) (cof .one (.or ψ φ)).shift [] (glueTube φ T e ψ u a0) A.dshift)
    (hsR : HasTy0 S (Ψ + 1) (cof .one (.or ψ' φ')).shift [] (glueTube φ' T' e' ψ' u' a0') A'.dshift)
    (hAA : A = A' ∨ ∃ l, EqTm0 S Ψ .one [] A A' (univ l))
    (huu : EqTm0 S (Ψ + 1) (cof .one ψ).shift [] u u' (glue A φ T e).dshift)
    (hee : EqTm0 S Ψ (cof .one φ) [] e e' (equiv T A))
    (hFF : EqTm0 S (Ψ + 1) (cof .one φ).shift [] (hfill T ψ u a0) (hfill T' ψ' u' a0') T.dshift)
    (p12 : I.Entails ψ ψ') (f12 : I.Entails φ φ') (f21 : I.Entails φ' φ) :
    EqTm0 S (Ψ + 1) (cof .one (.or ψ φ)).shift [] (glueTube φ T e ψ u a0) (glueTube φ' T' e' ψ' u' a0') A.dshift := by
  have hS := sigClosed_of_wfSig hW
  have eqR0 : ∀ {Φ0 : I} {x y X : Tm}, EqTm0 S (Ψ + 1) Φ0 [] x y X → HasTy0 S (Ψ + 1) Φ0 [] y X :=
    fun h => spec_to_minimal hW (HasTy.eqR (minimal_to_spec_eq h))
  have hC : (cof .one (.or ψ φ)).shift.Scoped (Ψ + 1) := scoped_of_ty hsL
  have hψ1 : ψ.shift.Scoped (Ψ + 1) := hC.2.1
  have hφ1 : φ.shift.Scoped (Ψ + 1) := hC.2.2
  have hCC : I.Entails (cof .one (.or ψ φ)).shift (cof .one (.or ψ' φ')).shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_or_elim (ent_trans p12 (ent_or_left _ _))
      (ent_trans f12 (ent_or_right _ _))))
  have hsR' : HasTy0 S (Ψ + 1) (cof .one (.or ψ φ)).shift [] (glueTube φ' T' e' ψ' u' a0') A.dshift := by
    rcases hAA with rfl | ⟨l, e⟩
    · exact HasTy0.restrict hC hCC hsR
    · have eA := EqTm0.restrict hC (ent_one _) (EqTm0.dwk hS e)
      exact HasTy0.conv (HasTy0.restrict hC hCC hsR) (EqTm0.symm eA)
  have hee1 := EqTm0.dwk hS hee
  rw [equiv_dshift] at hee1
  refine EqTm0.local (φ := ψ.shift) (ψ := φ.shift) hψ1 hφ1 (ent_and_right _ _) hsL hsR' ?_ ?_
  · have hc : (cof (cof .one (.or ψ φ)).shift ψ.shift).Scoped (Ψ + 1) := ⟨hC, hψ1⟩
    have s1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have s2 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift p12)) (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m := EqTm0.unglue (eqR0 s1) (eqR0 s2) (ent_shift f12) (ent_shift f21)
      (EqTm0.restrict (Φ' := cof (cof (cof .one (.or ψ φ)).shift ψ.shift) φ.shift) ⟨hc, hφ1⟩
        (ent_and_intro (ent_one _) (ent_and_right _ _)) hee1)
      (EqTm0.restrict hc (ent_and_intro (ent_one _) (ent_and_right _ _)) huu)
    exact EqTm0.trans s1 (EqTm0.trans m (EqTm0.symm s2))
  · have hc : (cof (cof .one (.or ψ φ)).shift φ.shift).Scoped (Ψ + 1) := ⟨hC, hφ1⟩
    have t1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have t2 := EqTm0.splitR (ent_trans (ent_and_right _ _) (ent_shift f12)) (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m := EqTm0.app (EqTm0.fst (EqTm0.restrict hc (ent_and_intro (ent_one _) (ent_and_right _ _)) hee1))
      (EqTm0.restrict hc (ent_and_intro (ent_one _) (ent_and_right _ _)) hFF)
    rw [shift_inst] at m
    exact EqTm0.trans t1 (EqTm0.trans m (EqTm0.symm t2))

end KubusCore.Meta
