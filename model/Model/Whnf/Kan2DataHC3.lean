import Model.Whnf.Kan2DataHC2

/-!
# Composition of related constructors: the data of each argument

For a recursive argument, the compositions of the projections of the tubes over the base's
arguments; for a point argument, the type lines (related, robust and Kan, at the code of the
inductive type) and the projections of the tubes along them.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

theorem getD_eq_get {L : List Tm} {i : ℕ} (h : i < L.length) : L.getD i .abort = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

namespace HCC

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {qs qs' : Tm} {X X' : List Tm} {φ φ' : I} {u u' : Tm}
  (H : HCC S d D K P Q Q' k1 ρ c C qs qs' X X' φ φ' u u')
include H

/-- The line of a point argument is Kan at all its restrictions. -/
theorem lineKan {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i) {n : ℕ} (τ : ISub n k1) (r : I) (hr : r.Scoped n)
    {X'' : Tm} (hR : RT2 S n (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ r hr) X'') :
    KanH2 S n (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ r hr) X'' ∧
      ∀ {n' : ℕ} (e : n = n' + 1), KanT2 S n' (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ r hr) X'' := by
  have hFl := fills_len (d := d) (D := D) (c := c) (C := C) (Q.isub ρ) φ u X
  have hFl' := fills_len (d := d) (D := D) (c := c) (C := C) (Q'.isub ρ) φ' u' X'
  have hRR' := argRelH_QQ H.hW H.hD H.hP H.hQ H.hQ' (ρ.comp τ)
  have hQT : IsTyK S n (.data d (Q.isub (ρ.comp τ))) := ((Comp2_ty_base H.hQ).2.2.1).isub H.hW (ρ.comp τ)
  have hQ'T : IsTyK S n (.data d (Q'.isub (ρ.comp τ))) := ((Comp2_ty_base H.hQ').2.2.1).isub H.hW (ρ.comp τ)
  have hc1 : (Q.isub (ρ.comp τ)).closedB 0 n = true := by
    have := closed_of_isTyK H.hW hQT; simpa [Tm.closedB] using this
  have hc2 : (Q'.isub (ρ.comp τ)).closedB 0 n = true := by
    have := closed_of_isTyK H.hW hQ'T; simpa [Tm.closedB] using this
  have hcode := argTy_code_rel H.hW H.hD H.hH H.hP (ρ.comp τ) hRR' (semK_dataQ H.hW H.hD H.hP H.hQ (ρ.comp τ)) hc1 hc2
    H.hC (A := ((conFills d D c C (Q.isub ρ) φ u X).map (·.isub (ISub.cons r hr τ))).take j)
    (A' := ((conFills d D c C (Q'.isub ρ) φ' u' X').map (·.isub (ISub.cons r hr τ))).take j)
    (by simp [hFl, hFl'])
    (fun i hi hi' hri => by
      have hij : i < j := by simp [hFl] at hi; omega
      have h1 := (hV i hij).1 n τ r r hr hr (I_eq_refl _)
      rw [H.argTyAt_rec (by omega) hri τ r hr] at h1
      rw [← getD_eq_get hi, ← getD_eq_get hi', getD_take_lt hij,
        getD_take_lt hij, getD_map_isub, getD_map_isub]
      exact h1)
    (fun i hi hi' hri => by
      have hij : i < j := by simp [hFl] at hi; omega
      have h1 := (hV i hij).1 n τ r r hr hr (I_eq_refl _)
      rw [← getD_eq_get hi, ← getD_eq_get hi', getD_take_lt hij,
        getD_take_lt hij, getD_map_isub, getD_map_isub, List.take_take, Nat.min_eq_left hij.le]
      exact h1)
    (by simp [hFl]; omega) (by simp [hFl]; rw [Nat.min_eq_left (by omega)]; exact hrj)
  have hl : (((conFills d D c C (Q.isub ρ) φ u X).map (·.isub (ISub.cons r hr τ))).take j).length = j := by
    simp [hFl]; omega
  rw [hl] at hcode
  have hb := Comp2_ty_base hcode
  have hR' := (Comp2_ty_iff hb.1 hb.2.2.2.1).2 hR
  exact kan_tyLook H.hW H.hD H.hArgK _ c j _ hR'

/-- The type line of a point argument, against the right one. -/
theorem ptLR {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i) :
    LineRob S k1 (conLine d D c C (Q.isub ρ) φ u X j) (conLine d D c C (Q'.isub ρ) φ' u' X' j) := by
  intro k3 τ r r' hr hr' hE
  rw [H.lineσ hj.le τ r hr, H.lineσ' hj.le τ r' hr']
  exact H.relLine hj hV τ r r' hr hr' hE

theorem ptXL {j : ℕ} (hj : j < C.args.length) {k3 : ℕ} (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3) :
    TyCode k3 (semK S k3 ((conLine d D c C (Q.isub ρ) φ u X j).isub (ISub.cons r hr τ))) := by
  have B := H.basic
  obtain ⟨⟨G1, -, G3, -⟩, -⟩ := H.prem
  cases hrj : C.isRec j
  · obtain ⟨A0, hA0⟩ := argTy_point hj hrj
    obtain ⟨hLt, -, -, -⟩ := hcompCon_pt_types H.hW H.hD H.hH H.hC (spec_to_minimal H.hW B.hqT) B.hφs B.hXq G1 G3 hA0
    exact tyCode_of_univ H.hW (HasTy.isubS H.hW (minimal_to_spec hLt) (ISub.cons r hr τ))
  · rw [H.lineσ hj.le τ r hr, H.argTyAt_rec hj hrj τ r hr]
    have h := HasTy.isubS H.hW B.hqT τ
    rw [show (Tm.data d (Q.isub ρ)).isub τ = .data d (Q.isub (ρ.comp τ)) by
      show Tm.data d ((Q.isub ρ).isub τ) = _; rw [Tm.isub_isub]] at h
    exact tyCode_of_univ H.hW h

/-- The type line of a point argument, against itself. -/
theorem ptLRL {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i) :
    LineRob S k1 (conLine d D c C (Q.isub ρ) φ u X j) (conLine d D c C (Q.isub ρ) φ u X j) := by
  intro k3 τ r r' hr hr' hE
  have h1 := H.ptLR hj hV k3 τ r r' hr hr' hE
  have h2 := H.ptLR hj hV k3 τ r' r' hr' hr' (I_eq_refl _)
  exact RT2.trans H.hW (H.ptXL hj τ r hr) h1 (RT2.symm H.hW (H.ptXL hj τ r' hr') h2)

/-- Transport along the restrictions of the type line of a point argument. -/
theorem ptKT {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i) :
    ∀ k3 (Θ : ISub (k3 + 1) (k1 + 1)) X'', RT2 S (k3 + 1) ((conLine d D c C (Q.isub ρ) φ u X j).isub Θ) X'' →
      KanT2 S k3 ((conLine d D c C (Q.isub ρ) φ u X j).isub Θ) X'' := by
  intro k3 Θ X'' hR
  rw [← ISub.cons_tail Θ, H.lineσ hj.le] at hR ⊢
  exact (H.lineKan hj hrj hV Θ.tail _ _ hR).2 rfl

/-- Composition at the restrictions of the type line of a point argument. -/
theorem ptKH {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i) :
    ∀ k3 (Θ : ISub k3 (k1 + 1)) X'', RT2 S k3 ((conLine d D c C (Q.isub ρ) φ u X j).isub Θ) X'' →
      KanH2 S k3 ((conLine d D c C (Q.isub ρ) φ u X j).isub Θ) X'' := by
  intro k3 Θ X'' hR
  rw [← ISub.cons_tail Θ, H.lineσ hj.le] at hR ⊢
  exact (H.lineKan hj hrj hV Θ.tail _ _ hR).1

/-- The projections of the tubes along the type line of a point argument. -/
theorem ptTube {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i)
    {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3) (hE : I.Eq r r')
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((conLine d D c C (Q.isub ρ) φ u X j).isub (ISub.cons r hr σ))
      ((((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub σ.up).dinst r)
      ((((tubeArgs d D c C (Q'.isub ρ) u').getD j .abort).isub σ.up).dinst r') := by
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r' hr', H.lineσ hj.le σ r hr]
  have hF := H.relFU hj hV σ r hr hh
  have hX := H.ptXL hj σ r hr
  rw [H.lineσ hj.le σ r hr] at hX
  exact RE2.conv H.hW (RT2.symm H.hW hX hF) (H.prj σ r r' hr hr' hE hh j hj)

/-- The projections of the left tube along the type line of a point argument, against themselves. -/
theorem ptTubes {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i)
    {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3) (hE : I.Eq r r')
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((conLine d D c C (Q.isub ρ) φ u X j).isub (ISub.cons r hr σ))
      ((((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub σ.up).dinst r)
      ((((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub σ.up).dinst r') := by
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r' hr', H.lineσ hj.le σ r hr]
  have hF := H.relFU hj hV σ r hr hh
  have hX := H.ptXL hj σ r hr
  rw [H.lineσ hj.le σ r hr] at hX
  exact RE2.conv H.hW (RT2.symm H.hW hX hF) (H.prjs σ r r' hr hr' hE hh j hj)


end HCC

end

end Model.Whnf
