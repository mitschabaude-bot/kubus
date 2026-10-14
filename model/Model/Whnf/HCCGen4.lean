import Model.Whnf.HCCGen3

/-!
# Composition of constructors along arbitrary tube lists: the invariant, and the relation of the contracta
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

namespace HCG

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {X X' : List Tm} {φ φ' : I} {us us' : List Tm}
  (H : HCG S d D K P Q Q' k1 ρ c C X X' φ φ' us us')
include H

theorem hrecQ {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) :
    RE2 S k1 (.data d (Q.isub ρ)) (X.getD j .abort) (X'.getD j .abort) :=
  RE2.conv H.hW H.basic.hPQ (H.hrecR j hj hrj)

theorem QQ : RT2 S k1 (.data d (Q.isub ρ)) (.data d (Q.isub ρ)) :=
  RT2.refl' H.hW (tyCode_of_univ H.hW H.basic.hpT) H.basic.hPQ

theorem XQ : TyCode k1 (semK S k1 (.data d (Q.isub ρ))) := tyCode_of_univ H.hW H.basic.hqT

theorem eQQ' : TyEq S k1 (.data d (Q.isub ρ)) (.data d (Q'.isub ρ)) :=
  (Comp2_ty_base (RT2.trans H.hW (tyCode_of_univ H.hW H.basic.hpT |> fun h => RT2.tyCode_r H.hW H.basic.hPQ h)
    (RT2.symm H.hW (tyCode_of_univ H.hW H.basic.hpT) H.basic.hPQ) H.basic.hPQ')).2.2.2.2.2

theorem dQσ {k3 : ℕ} (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3) :
    (Tm.data d (Q.isub ρ)).dshift.isub (ISub.cons r hr τ) = .data d (Q.isub (ρ.comp τ)) := by
  rw [dshift_isub_cons, H.eQσ]

/-- The invariant at a recursive argument. -/
theorem stepRec {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) :
    GInv S d D Q Q' ρ C X X' φ φ' us us' j := by
  obtain ⟨htyF, htyF', heqF, htyH, hteq⟩ := H.recFill hj hrj
  rw [fills_get_rec _ _ _ _ hj hrj] at htyF htyF'
  rw [fills_get_rec _ _ _ _ hj hrj, fills_get_rec _ _ _ _ hj hrj] at heqF
  have B := H.basic
  have hu0s : RE2 S k1 (.data d (Q.isub ρ)) (X.getD j .abort) (X.getD j .abort) :=
    RE2.trans H.hW H.QQ (H.hrecQ hj hrj) (RE2.symm H.hW H.QQ (H.hrecQ hj hrj))
  have hbds : ∀ k3 (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds →
      RE2 S k3 ((Tm.data d (Q.isub ρ)).isub σ) ((((us).getD j .abort).isub σ.up).dinst .zero)
        ((X.getD j .abort).isub σ) := fun k3 σ hh => H.recBds hj hrj σ hh
  have hrecTy : ∀ {k3 : ℕ} (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3),
      argTyAt d D C (gFills d D C (Q.isub ρ) φ us X) Q ρ j τ r hr = (Tm.data d (Q.isub ρ)).isub τ := by
    intro k3 τ r hr; rw [H.argTyAt_rec hj hrj τ r hr, H.eQσ]
  refine ⟨fun k3 τ r r' hr hr' hE => ?_, fun k3 τ r hr hh => ?_, fun k3 τ => ?_, ?_, fun k3 τ r r' hr hr' hE hh => ?_,
    fun k3 τ r r' hr hr' hE hh => ?_⟩
  · have := hfill_relAt H.hW B.hφs (fun k3 τ => H.recK hj hrj τ) H.QQ H.eQQ' hteq htyF htyF' heqF H.h12 H.h21
      (H.recTube hj hrj) (H.hrecQ hj hrj) (fun k3 σ hh => H.recBd hj hrj σ hh) (fun k3 σ hh => H.recBd' hj hrj σ hh)
      (ISub.cons r hr τ) (ISub.cons r' hr' τ) rfl hE
    rw [H.dQσ] at this
    rw [H.argTyAt_rec hj hrj τ r hr, fills_get_rec _ _ _ _ hj hrj, fills_get_rec _ _ _ _ hj hrj]
    exact this
  · have := hfill_face_pt H.hW B.hφs H.XQ H.QQ htyF (H.recTubes hj hrj) τ r hr hh
    rw [hrecTy, fills_get_rec _ _ _ _ hj hrj]
    rw [isub_up_dinst _ τ r hr] at this
    exact this
  · have := hfill_zero_pt H.hW B.hφs H.XQ H.QQ htyF (H.recTubes hj hrj) hu0s hbds τ
    rw [hrecTy, fills_get_rec _ _ _ _ hj hrj]
    exact this
  · have := hfill_one_ptAt H.hW B.hφs H.XQ H.QQ (fun k3 τ => H.recKs hj hrj τ) htyH htyF (H.recTubes hj hrj) hu0s
      hbds (ISub.id k1)
    rw [hrecTy, fills_get_rec _ _ _ _ hj hrj, outs_get_rec _ _ _ _ hj hrj]
    rwa [isub_id_of_closed (closed_of_ty H.hW htyH)] at this
  · have := H.recTubes hj hrj k3 τ r r' hr hr' hE hh
    rw [isub_up_dinst _ τ r hr, isub_up_dinst _ τ r' hr'] at this
    rw [hrecTy]
    exact this
  · have := H.recTube hj hrj k3 τ r r' hr hr' hE hh
    rw [isub_up_dinst _ τ r hr, isub_up_dinst _ τ r' hr'] at this
    rw [hrecTy]
    exact this

/-- The invariant at a point argument. -/
theorem stepPt {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    GInv S d D Q Q' ρ C X X' φ φ' us us' j := by
  obtain ⟨htyF, htyF', heqF, htyC, -, -, hteq⟩ := H.ptFill hj hrj hV
  rw [fills_get_pt _ _ _ _ hj hrj] at htyF htyF'
  rw [fills_get_pt _ _ _ _ hj hrj, fills_get_pt _ _ _ _ hj hrj] at heqF
  rw [outs_get_pt _ _ _ _ hj hrj] at htyC
  have B := H.basic
  have hLRL := H.ptLRL hj hV
  have hKT := H.ptKT hj hrj hV
  have hKH := H.ptKH hj hrj hV
  have hu0 := H.ptU0 hj hrj hV
  have hX0 : TyCode k1 (semK S k1 ((gLine d D C (Q.isub ρ) φ us X j).dinst .zero)) := RE2.tyCode H.hW hu0
  have hRT0 : RT2 S k1 ((gLine d D C (Q.isub ρ) φ us X j).dinst .zero)
      ((gLine d D C (Q.isub ρ) φ us X j).dinst .zero) := by
    have := hLRL k1 (ISub.id k1) .zero .zero trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed (H.line_closed hj hrj)] at this
  have hu0s := RE2.trans H.hW hRT0 hu0 (RE2.symm H.hW hRT0 hu0)
  have htubes := fun k3 σ r r' hr hr' hE hh => H.ptTubes (k3 := k3) hj hV σ r r' hr hr' hE hh
  have hbds := fun k3 σ hh => H.ptBds (k3 := k3) hj hrj hV σ hh
  refine ⟨fun k3 τ r r' hr hr' hE => ?_, fun k3 τ r hr hh => ?_, fun k3 τ => ?_, ?_, fun k3 τ r r' hr hr' hE hh => ?_,
    fun k3 τ r r' hr hr' hE hh => ?_⟩
  · have := fill_rel H.hW B.hφs (H.ptLR hj hV) hLRL hKT hKH htyF htyF' heqF hteq H.h12 H.h21
      (fun k3 σ r r' hr hr' hE hh => H.ptTube hj hV σ r r' hr hr' hE hh) hu0
      (fun k3 σ hh => H.ptBd hj hV σ hh) (fun k3 σ hh => H.ptBd' hj hV σ hh)
      (ISub.cons r hr τ) (ISub.cons r' hr' τ) rfl hE
    rw [H.lineσ hj.le τ r hr] at this
    rw [fills_get_pt _ _ _ _ hj hrj, fills_get_pt _ _ _ _ hj hrj]
    exact this
  · have := fill_face_pt H.hW B.hφs hLRL htyF htubes τ r hr hh
    rw [H.lineσ hj.le τ r hr, isub_up_dinst _ τ r hr] at this
    rw [fills_get_pt _ _ _ _ hj hrj]
    exact this
  · have := fill_zero_pt H.hW B.hφs hLRL htyF htubes hu0s hbds τ
    rw [H.lineσ hj.le τ .zero trivial] at this
    rw [fills_get_pt _ _ _ _ hj hrj]
    exact this
  · have := fill_one_pt H.hW B.hφs hLRL hKT hKH htyC htyF htubes hu0s hbds (ISub.id k1)
    rw [H.lineσ hj.le (ISub.id k1) .one trivial, isub_id_of_closed (closed_of_ty H.hW htyC)] at this
    rw [fills_get_pt _ _ _ _ hj hrj, outs_get_pt _ _ _ _ hj hrj]
    exact this
  · have := H.ptTubes hj hV τ r r' hr hr' hE hh
    rw [H.lineσ hj.le τ r hr, isub_up_dinst _ τ r hr, isub_up_dinst _ τ r' hr'] at this
    exact this
  · have := H.ptTube hj hV τ r r' hr hr' hE hh
    rw [H.lineσ hj.le τ r hr, isub_up_dinst _ τ r hr, isub_up_dinst _ τ r' hr'] at this
    exact this

/-- The invariant along all arguments. -/
theorem inv : ∀ i, i < C.args.length → GInv S d D Q Q' ρ C X X' φ φ' us us' i := by
  have key : ∀ j, j ≤ C.args.length → ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      by_cases hij : i < j
      · exact ih (by omega) i hij
      obtain rfl : i = j := by omega
      cases hri : C.isRec i
      · exact H.stepPt (by omega) hri (ih (by omega))
      · exact H.stepRec (by omega) hri
  exact key C.args.length (Nat.le_refl _)


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

/-- The `hcompCon` contracta along related tube lists are related at one stage. -/
theorem conRel :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 ρ.hom
      (.data d (P.isub ρ)) (.con d c (Q.isub ρ) (Tm.ofList (gOuts d D C (Q.isub ρ) φ us X)) [])
      (.con d c (Q'.isub ρ) (Tm.ofList (gOuts d D C (Q'.isub ρ) φ' us' X')) []) := by
  have B := H.basic
  have eLR := H.eLR
  have hYl : (gOuts d D C (Q.isub ρ) φ us X).length = C.args.length := by simp [gOuts]
  have hY'l : (gOuts d D C (Q'.isub ρ) φ' us' X').length = C.args.length := by simp [gOuts]
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
    have hKH1 : ∀ X'', RT2 S k1 ((gLine d D C (Q.isub ρ) φ us X i).dinst .one) X'' →
        KanH2 S k1 ((gLine d D C (Q.isub ρ) φ us X i).dinst .one) X'' := by
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

end HCG

end

end Model.Whnf
