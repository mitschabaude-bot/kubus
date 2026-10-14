import Model.Whnf.Kan2Glue

/-!
# Binary Kan lemma: transport along lines of Glue types

`transp (i. Glue A [φ ↦ (T, e)]) ψ u0` computes (`transpGlueWith`) to a Glue element built from a
composition in `A`, a transport in `T` and a contraction in the fibres of `e(1)`. Related lines and
related starts give related results, piece by piece as in the unary `KanGlueT`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- The parts of a heterogeneous composition, typed. -/
theorem comp_parts {C u u0 X : Tm} {ψ : I} (h : HasTy S k .one [] (Tm.comp C ψ u u0) X) :
    ∃ l, HasTy S (k + 1) .one [] C (.univ l) ∧ ψ.Scoped k ∧ HasTy S (k + 1) (cof .one ψ).shift [] u C ∧
      HasTy S k .one [] u0 (C.dinst .zero) := by
  have hS := sigClosed_of_wfSig hW
  have hm := spec_to_minimal hW h
  rw [comp_eq] at hm
  obtain ⟨l1, ⟨-, hψ, htube, hb, -⟩, -⟩ := gen_hcomp hm rfl
  obtain ⟨lC, ⟨hC, -, -, hu0⟩, -⟩ := gen_transpF hb rfl
  obtain ⟨lL, ⟨-, -, -, hu⟩, -⟩ := gen_transpF htube rfl
  have hXs : (cof .one ψ).shift.Scoped (k + 1) := KubusCore.I.scoped_shift ⟨trivial, hψ⟩
  have hv0 : (I.var 0).Scoped (k + 1) := show 0 < k + 1 by omega
  have e := line_ieq hS hC (k := 1) (Ψ' := k + 1) (X := (cof .one ψ).shift) (r := .or (.var 0) .zero) (r' := .var 0)
    (ent_one _) ⟨hv0, trivial⟩ hv0 (by omega) (I_eq_or_zero_r _) (by rw [ctxI_add1]; exact Wf0.nil hXs)
  rw [ctxI_add1, sk_var1] at e
  rw [L_d0] at hu
  exact ⟨lC, minimal_to_spec hC, hψ, minimal_to_spec (HasTy0.conv hu e), minimal_to_spec hu0⟩

/-- Lines related at all their points are judgmentally equal. -/
theorem eqLine_of_rob {C C' : Tm} {l l' : ℕ} (hC : HasTy S (k + 1) .one [] C (.univ l))
    (hC' : HasTy S (k + 1) .one [] C' (.univ l')) (h : LineRob S k C C') :
    EqTm S (k + 1) .one [] C C' (.univ maxLevel) := by
  have hm : HasTy S (k + 1) .one [] C (.univ maxLevel) := hC.cumulTo (lvl_of_ty hW hC) le_rfl
  have hm' : HasTy S (k + 1) .one [] C' (.univ maxLevel) := hC'.cumulTo (lvl_of_ty hW hC') le_rfl
  have hc : (cof .one .one).Scoped (k + 1) := ⟨trivial, trivial⟩
  have e := eq_of_restr hW (φ := .one) trivial (.inr rfl) (HasTy.restrict hc (ent_and_left _ _) hm)
    (HasTy.restrict hc (ent_and_left _ _) hm') fun k' σ _ => by
      have h1 := h k' σ.tail (σ.τ 0) (σ.τ 0) (σ.sc 0 (by omega)) (σ.sc 0 (by omega)) (I_eq_refl _)
      rw [ISub.cons_tail] at h1
      rw [isub_univ]
      exact eqTop hW (Comp2_ty_base h1).2.2.2.2.2 (HasTy.isubS hW hC σ)
  exact EqTm.restrict trivial (ent_and_intro (ent_refl _) (ent_refl _)) e


/-- Heterogeneous composition along related lines, from relations alone. -/
theorem comp2r {C C' u u' u0 u0' : Tm} {ψ ψ' : I} (hLR : LineRob S k C C') (hLRL : LineRob S k C C)
    (hKT : ∀ k3 (Θ : ISub (k3 + 1) (k + 1)) X', RT2 S (k3 + 1) (C.isub Θ) X' → KanT2 S k3 (C.isub Θ) X')
    (hKH : ∀ X', RT2 S k (C.dinst .one) X' → KanH2 S k (C.dinst .one) X')
    (hty : HasTy S k .one [] (Tm.comp C ψ u u0) (C.dinst .one))
    (hty' : HasTy S k .one [] (Tm.comp C' ψ' u' u0') (C.dinst .one))
    (h12 : I.Entails ψ ψ') (h21 : I.Entails ψ' ψ)
    (htube : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r'))
    (hu0 : RE2 S k (C.dinst .zero) u0 u0')
    (hbd : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) ((u.isub σ.up).dinst .zero) (u0'.isub σ))
    (hbd' : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) (u0.isub σ) ((u'.isub σ.up).dinst .zero)) :
    RE2 S k (C.dinst .one) (Tm.comp C ψ u u0) (Tm.comp C' ψ' u' u0') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hC, hψs, hu, -⟩ := comp_parts hW hty
  obtain ⟨l', hC', -, hu', -⟩ := comp_parts hW hty'
  have hCC := eqLine_of_rob hW hC hC' hLR
  have hc : (cof .one ψ).shift.Scoped (k + 1) := KubusCore.I.scoped_shift ⟨trivial, hψs⟩
  have hu'C : HasTy S (k + 1) (cof .one ψ).shift [] u' C :=
    (HasTy.restrict hc (ent_shift (ent_and_mono (ent_refl _) h12)) hu').conv
      (EqTm.restrict hc (ent_trans (ent_shift (ent_and_left _ _)) (ent_refl _)) hCC).symm
  have hteq := eqTube_of_rel hW hψs (HasTy.restrict hc (ent_trans (ent_shift (ent_and_left _ _)) (ent_refl _)) hC)
    hu hu'C fun k3 σ r hr hh => htube k3 σ r r hr hr (I_eq_refl _) hh
  have heq := minimal_to_spec_eq (comp_cong hS (spec_to_minimal hW hty) (spec_to_minimal hW hty')
    (spec_to_minimal_eq hW hCC) h12 h21 (spec_to_minimal_eq hW hteq) (spec_to_minimal_eq hW (RE2.typed hu0).2.2))
  exact comp2 hW hLR hLRL hKT hKH hty hty' heq hteq h12 h21 htube hu0 hbd hbd'

end

end Model.Whnf
