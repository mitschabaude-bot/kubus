import Model.Whnf.Kan2DataHC4

/-!
# Composition of related constructors

The `hcompCon` contracta of compositions of related constructors along related tubes are related at
one stage (`HCC.hcompCon2`): recursive arguments by the composition of the base's arguments,
point arguments by `comp2` along their related type lines.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

namespace HCC

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {qs qs' : Tm} {X X' : List Tm} {φ φ' : I} {u u' : Tm}
  (H : HCC S d D K P Q Q' k1 ρ c C qs qs' X X' φ φ' u u')
include H

/-- Restricted tubes, from the type at `Q` to the type at `P`. -/
theorem tubeP {v v' : Tm} {ψ : I} (h : Tube2 S k1 (.data d (Q.isub ρ)) ψ v v') :
    Tube2 S k1 (.data d (P.isub ρ)) ψ v v' := by
  intro k3 σ r r' hr hr' hE hh
  have := h k3 σ r r' hr hr' hE hh
  rw [H.eQσ] at this
  rw [H.ePσ]
  exact RE2.conv H.hW (RT2.symm H.hW (H.XPσ σ) (H.PQσ σ)) this

theorem toP {k3 : ℕ} (σ : ISub k3 k1) {x y : Tm} (h : RE2 S k3 ((Tm.data d (Q.isub ρ)).isub σ) x y) :
    RE2 S k3 ((Tm.data d (P.isub ρ)).isub σ) x y := by
  rw [H.eQσ] at h
  rw [H.ePσ]
  exact RE2.conv H.hW (RT2.symm H.hW (H.XPσ σ) (H.PQσ σ)) h

/-- The `hcompCon` contracta of compositions of related constructors along related tubes are related
at one stage. -/
theorem hcompCon2 :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 ρ.hom
      (.data d (P.isub ρ)) (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
      (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') [])) := by
  obtain ⟨⟨e_hc, rL⟩, ⟨e_hc', rR⟩⟩ := H.contracta
  refine DR2At.expandR H.hW (DR2At.expand H.hW ?_ rL e_hc) rR e_hc'
  have B := H.basic
  have eLR := H.eLR
  have hYl : (conOuts d D c C (Q.isub ρ) φ u X).length = C.args.length := by simp [conOuts]
  have hY'l : (conOuts d D c C (Q'.isub ρ) φ' u' X').length = C.args.length := by simp [conOuts]
  have hpl := (dataLit_rel H.hW H.hD H.hP H.hPP ρ).2.2.2.2.2.1
  have hplen : (P.isub ρ).toList.length = D.params.length := by
    have := data_len_of H.hW (⟨_, .inl B.hpT⟩ : IsTyK S k1 (.data d (P.isub ρ))); rwa [dataD_eq H.hW H.hD] at this
  refine DR2At_con_of H.hW H.hD H.hH H.hP H.hPP ρ H.hC hYl hY'l (HasTy.eqL eLR)
    ⟨redW_self (step_con_nonHIT H.hD H.hH H.hC _ _ _), EqTm.refl (HasTy.eqR eLR)⟩ eLR
    (fun i hi hi' => ⟨fun hri => ?_, fun hri hRT => ?_⟩)
  · -- a recursive argument
    have hiC : i < C.args.length := by omega
    rw [← getD_eq_get hi, ← getD_eq_get hi']
    have e := H.eYY' i hiC
    rw [argTy_rec_inst hri hpl hplen (by simp [hYl]; omega)] at e
    have h := H.hrecH i hiC hri Q Q' H.hQ H.hQ' k1 (ISub.id k1)
    have hXc' : (X'.getD i .abort).closedB 0 k1 = true := by
      have := tele_getD B.hXq' (by rw [H.hXl']; exact hiC) (argTys_get hiC); exact closed_ty this
    rw [ISub.comp_id, isub_id_of_closed (H.X_closed hiC), isub_id_of_closed hXc'] at h
    obtain ⟨-, -, -, -, hteq⟩ := H.recFill hiC hri
    rw [outs_get_rec _ _ _ _ hiC hri, outs_get_rec _ _ _ _ hiC hri] at e ⊢
    have eQP : TyEq S k1 (.data d (Q.isub ρ)) (.data d (P.isub ρ)) :=
      (Comp2_ty_base (RT2.symm H.hW (tyCode_of_univ H.hW B.hpT) B.hPQ)).2.2.2.2.2
    exact h φ φ' _ _ (minimal_to_spec (pre_eq (sigClosed_of_wfSig H.hW) (wf_typed _ S rfl H.hW).1
      (wf_typed _ S rfl H.hW).2 e).1) (minimal_to_spec (pre_eq (sigClosed_of_wfSig H.hW) (wf_typed _ S rfl H.hW).1
      (wf_typed _ S rfl H.hW).2 e).2.1) (minimal_to_spec_eq e)
      (EqTm.cofConv B.hφs hteq eQP)
      H.h12 H.h21 (H.tubeP (H.recTube hiC hri)) (H.hrecR i hiC hri)
      (fun k3 σ hh => H.toP σ (H.recBd hiC hri σ hh)) (fun k3 σ hh => H.toP σ (H.recBd' hiC hri σ hh))
  · -- a point argument
    have hiC : i < C.args.length := by omega
    have hV := fun i' (hi' : i' < i) => H.inv i' (by omega)
    obtain ⟨-, -, -, htyC, htyC', heqC, hteq⟩ := H.ptFill hiC hri hV
    rw [outs_get_pt _ _ _ _ hiC hri] at htyC htyC'
    rw [outs_get_pt _ _ _ _ hiC hri, outs_get_pt _ _ _ _ hiC hri] at heqC
    have hlc := H.line_closed hiC hri
    have hKH1 : ∀ X'', RT2 S k1 ((conLine d D c C (Q.isub ρ) φ u X i).dinst .one) X'' →
        KanH2 S k1 ((conLine d D c C (Q.isub ρ) φ u X i).dinst .one) X'' := by
      intro X'' h
      have := H.ptKH hiC hri hV k1 (ISub.cons .one trivial (ISub.id k1)) X''
      rw [isub_cons_id_of_closed hlc] at this
      exact this h
    have r := comp2 H.hW (H.ptLR hiC hV) (H.ptLRL hiC hV) (H.ptKT hiC hri hV) hKH1 htyC htyC' heqC hteq H.h12 H.h21
      (fun k3 σ r r' hr hr' hE hh => H.ptTube hiC hV σ r r' hr hr' hE hh) (H.ptU0 hiC hri hV)
      (fun k3 σ hh => H.ptBd hiC hV σ hh) (fun k3 σ hh => H.ptBd' hiC hV σ hh)
    have hFY := H.relFY hiC hV
    rw [← H.lineσ hiC.le (ISub.id k1) .one trivial, isub_cons_id_of_closed hlc] at hFY
    rw [← getD_eq_get hi, ← getD_eq_get hi', outs_get_pt _ _ _ _ hiC hri, outs_get_pt _ _ _ _ hiC hri]
    exact RE2.conv H.hW hFY r

end HCC

end

end Model.Whnf
