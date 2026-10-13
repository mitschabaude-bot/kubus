import Model.Whnf.Pack2
import Model.Canon.GlueEquiv

/-!
# The binary relation of equivalences

`equivE2 T A` is the relation of `equiv T A` built from the relations of `T` and `A` (as in Glue
types). It is a partial equivalence, transferable along related `T` and `A`, given the PER
properties of `T` and `A` and their Kripke property.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

theorem piE2_rebase (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') (σ : ISub k' k) :
    piE2 S dom cod k' σ = piE2 S (fun k'' σ'' => dom k'' (σ.comp σ'')) (fun k'' σ'' => cod k'' (σ.comp σ''))
      k' (ISub.id k') := by
  funext A t t'; simp only [piE2, ISub.id_comp]

theorem sigmaE2_rebase (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') (σ : ISub k' k) :
    sigmaE2 S dom cod k' σ = sigmaE2 S (fun k'' σ'' => dom k'' (σ.comp σ'')) (fun k'' σ'' => cod k'' (σ.comp σ''))
      k' (ISub.id k') := by
  funext A t t'; simp only [sigmaE2, ISub.id_comp]

theorem pathE2_rebase (line : ElR2 (k + 1)) (σ : ISub k' k) :
    pathE2 S line k' σ = pathE2 S (fun k'' σ'' => line k'' (σ.up.comp σ'')) k' (ISub.id k') := by
  funext A t t'
  simp only [pathE2, ISub.id_comp, ISub.up_comp_cons]

/-- A Kripke family of related types and elements over a base stage. -/
structure FamOK (S : Sig) (n : ℕ) (P : (k' : ℕ) → ISub k' n → Pack2) : Prop where
  per : ∀ k' (σ : ISub k' n), PERP (P k' σ)
  kr : ∀ k' (σ : ISub k' n) k'' (σ' : ISub k'' k') X X', (P k' σ).ty X X' →
    (P k'' (σ.comp σ')).ty (X.isub σ') (X'.isub σ')
  krEl : ∀ k' (σ : ISub k' n) k'' (σ' : ISub k'' k') X t t', (P k' σ).el X t t' →
    (P k'' (σ.comp σ')).el (X.isub σ') (t.isub σ') (t'.isub σ')
  tyEq : ∀ k' (σ : ISub k' n) X X', (P k' σ).ty X X' → TyEq S k' X X'
  isTy : ∀ k' (σ : ISub k' n) X X', (P k' σ).ty X X' → IsTyK S k' X ∧ IsTyK S k' X'

theorem FamOK.rebase {n n' : ℕ} {P : (k' : ℕ) → ISub k' n → Pack2} (h : FamOK S n P) (ρ : ISub n' n) :
    FamOK S n' (fun k' σ => P k' (ρ.comp σ)) where
  per k' σ := h.per k' _
  kr k' σ k'' σ' X X' hX := by have := h.kr k' (ρ.comp σ) k'' σ' X X' hX; rwa [ISub.comp_assoc] at this
  krEl k' σ k'' σ' X t t' hX := by have := h.krEl k' (ρ.comp σ) k'' σ' X t t' hX; rwa [ISub.comp_assoc] at this
  tyEq k' σ X X' hX := h.tyEq k' _ X X' hX
  isTy k' σ X X' hX := h.isTy k' _ X X' hX

theorem ISub.up_tail_comp_cons_id {n : ℕ} (σ : ISub k' n) (r : I) (hr : r.Scoped k') :
    σ.up.tail.comp (ISub.cons r hr (ISub.id k')) = σ := by
  ext i
  show ((σ.τ i).shift).subst (ISub.cons r hr (ISub.id k')).τ = σ.τ i
  rw [I_shift_cons]
  by_cases h : i < n
  · exact ISub.I.subst_scoped_id (σ.sc i h) fun j hj => by simp [ISub.id, hj]
  · rw [σ.hi i (by omega)]; rfl

variable (hW : WfSig S)
include hW

/-- The lines of path types over a constant family satisfy the line condition. -/
theorem constLine_ty {n : ℕ} {AP : (k' : ℕ) → ISub k' n → Pack2} (hA : FamOK S n AP) :
    ∀ k' (σ : ISub k' n) (L1 L1' : Tm), (AP (k' + 1) σ.up.tail).ty L1 L1' → ∀ (r : I) (hr : r.Scoped k'),
      (AP k' (ISub.cons r hr σ).tail).ty (L1.dinst r) (L1'.dinst r) := by
  intro k' σ L1 L1' h r hr
  obtain ⟨h1, h2⟩ := hA.isTy _ _ _ _ h
  have := hA.kr _ _ k' (ISub.cons r hr (ISub.id k')) _ _ h
  rw [ISub.up_tail_comp_cons_id, isub_cons_id_of_closed (closed_of_isTyK hW h1),
    isub_cons_id_of_closed (closed_of_isTyK hW h2)] at this
  exact this

end

end Model.Whnf
