import Model.Whnf.Kan2DataHC3

/-!
# Composition of related constructors: the invariant along the arguments
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
    Inv S d D Q Q' ρ c C X X' φ φ' u u' j := by
  obtain ⟨htyF, htyF', heqF, htyH, hteq⟩ := H.recFill hj hrj
  rw [fills_get_rec _ _ _ _ hj hrj] at htyF htyF'
  rw [fills_get_rec _ _ _ _ hj hrj, fills_get_rec _ _ _ _ hj hrj] at heqF
  have B := H.basic
  have hu0s : RE2 S k1 (.data d (Q.isub ρ)) (X.getD j .abort) (X.getD j .abort) :=
    RE2.trans H.hW H.QQ (H.hrecQ hj hrj) (RE2.symm H.hW H.QQ (H.hrecQ hj hrj))
  have hbds : ∀ k3 (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds →
      RE2 S k3 ((Tm.data d (Q.isub ρ)).isub σ) ((((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub σ.up).dinst .zero)
        ((X.getD j .abort).isub σ) := fun k3 σ hh => H.recBds hj hrj σ hh
  have hrecTy : ∀ {k3 : ℕ} (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3),
      argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ r hr = (Tm.data d (Q.isub ρ)).isub τ := by
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
    (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i) :
    Inv S d D Q Q' ρ c C X X' φ φ' u u' j := by
  obtain ⟨htyF, htyF', heqF, htyC, -, -, hteq⟩ := H.ptFill hj hrj hV
  rw [fills_get_pt _ _ _ _ hj hrj] at htyF htyF'
  rw [fills_get_pt _ _ _ _ hj hrj, fills_get_pt _ _ _ _ hj hrj] at heqF
  rw [outs_get_pt _ _ _ _ hj hrj] at htyC
  have B := H.basic
  have hLRL := H.ptLRL hj hV
  have hKT := H.ptKT hj hrj hV
  have hKH := H.ptKH hj hrj hV
  have hu0 := H.ptU0 hj hrj hV
  have hX0 : TyCode k1 (semK S k1 ((conLine d D c C (Q.isub ρ) φ u X j).dinst .zero)) := RE2.tyCode H.hW hu0
  have hRT0 : RT2 S k1 ((conLine d D c C (Q.isub ρ) φ u X j).dinst .zero)
      ((conLine d D c C (Q.isub ρ) φ u X j).dinst .zero) := by
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
theorem inv : ∀ i, i < C.args.length → Inv S d D Q Q' ρ c C X X' φ φ' u u' i := by
  have key : ∀ j, j ≤ C.args.length → ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i := by
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


end HCC

end

end Model.Whnf
