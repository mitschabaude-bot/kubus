import Model.Whnf.Glue2Closed

/-!
# Expansion on both sides with per-restriction reducts

Two terms are related if at every restriction each side takes a step to a reduct, and the restricted
reduct of the left side is related to the reduct of the right side at the further restriction. This
is the form in which the Kan operations and the computation rules are related: their reducts depend
on whether a face holds, which varies with the restriction.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' : ℕ}

theorem I_subst_wk {r : I} (hr : r.Scoped k) : r.subst (ISub.wk k).τ = r.shift :=
  I_subst_congr_scoped (τ := fun i => .var (i + 1)) (fun i hi => by simp [ISub.wk, hi]) hr

/-- Restricting a judgmental equality of tubes. -/
theorem EqTm.cofIsub (hW : WfSig S) {u u' X : Tm} {φ : I} (hφ : φ.Scoped k)
    (h : EqTm S (k + 1) (cof .one φ).shift [] u u' X) (σ : ISub k' k) :
    EqTm S (k' + 1) (cof .one (φ.subst σ.τ)).shift [] (u.isub σ.up) (u'.isub σ.up) (X.isub σ.up) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal_eq hW h
  refine minimal_to_spec_eq (EqTm0.isub hS h0 σ.up.sc ?_ (Wf0.nil ⟨trivial, KubusCore.I.scoped_shift
    (I.scoped_subst hφ σ.sc)⟩))
  show I.Entails (I.and .one (φ.subst σ.τ).shift) (I.and (I.one.shift.subst σ.up.τ) ((φ.shift).subst σ.up.τ))
  rw [show (φ.shift).subst σ.up.τ = (φ.subst σ.τ).shift from I_shift_subst_up _ _]
  exact ent_refl _

/-- A judgmental equality restricted to a face. -/
theorem EqTm.toCof {t t' X : Tm} {φ : I} (hφ : φ.Scoped k) (h : EqTm S (k + 1) .one [] t t' X) :
    EqTm S (k + 1) (cof .one φ).shift [] t t' X :=
  EqTm.restrict ⟨trivial, KubusCore.I.scoped_shift hφ⟩ (ent_trans (ent_and_left _ _) (ent_refl _)) h

/-- Converting the type of a judgmental equality of tubes. -/
theorem EqTm.cofConv {u u' A B : Tm} {φ : I} (hφ : φ.Scoped k)
    (h : EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift) (e : TyEq S k A B) :
    EqTm S (k + 1) (cof .one φ).shift [] u u' B.dshift := by
  rcases e with rfl | ⟨l, e⟩
  · exact h
  · exact EqTm.conv h (EqTm.toCof hφ (EqTm.dwk e))

/-- A composition whose face does not hold reduces its type first. -/
theorem red_hcomp_ty {φ : I} {T W u a : Tm} (hn : ¬ I.Entails .one φ) (h : Red S T W) :
    Red S (.hcomp T φ u a) (.hcomp W φ u a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih => exact .step (by simp [step, hn', hs]) ih

/-- A transport whose face does not hold reduces its line first. -/
theorem red_transp_ty {φ : I} {T W a : Tm} (hn : ¬ I.Entails .one φ) (h : Red S T W) :
    Red S (.transp T φ a) (.transp W φ a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih => exact .step (by simp [step, hn', hs]) ih

theorem step_hcomp_face {φ : I} {T u a : Tm} (h : I.Entails .one φ) :
    step S (.hcomp T φ u a) = some (u.dinst .one) := by
  simp [step, show I.entails .one φ = true from h]

theorem step_transp_face {φ : I} {T a : Tm} (h : I.Entails .one φ) :
    step S (.transp T φ a) = some a := by
  simp [step, show I.entails .one φ = true from h]

variable (hW : WfSig S)
include hW

theorem RE2.expandBoth {A t t' : Tm} (hX : TyCode k (semK S k A)) (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A) (u u' : ∀ k' (_ : ISub k' k), Tm)
    (hu : ∀ k' (σ : ISub k' k), Red S (t.isub σ) (u k' σ) ∧ EqTm S k' .one [] (t.isub σ) (u k' σ) (A.isub σ))
    (hu' : ∀ k' (σ : ISub k' k), Red S (t'.isub σ) (u' k' σ) ∧ EqTm S k' .one [] (t'.isub σ) (u' k' σ) (A.isub σ))
    (h : ∀ k' (σ : ISub k' k) k'' (ρ : ISub k'' k'),
      RE2 S k'' (A.isub (σ.comp ρ)) ((u k' σ).isub ρ) (u' k'' (σ.comp ρ))) :
    RE2 S k A t t' := by
  refine RE2.expandH hW hAA ht ht' fun k' σ => ⟨u k' σ, (hu k' σ).1, (hu k' σ).2, ?_⟩
  have hAσ := RT2.isub hW hX hAA σ
  have hXσ : TyCode k' (semK S k' (A.isub σ)) := by
    rw [semK_isubTy hW (Comp2_ty_base hAA).2.1]; exact hX.res _
  refine RE2.symm hW hAσ (RE2.expandH hW hAσ (HasTy.isubS hW ht' σ) (HasTy.eqR (hu k' σ).2) fun k'' ρ => ?_)
  refine ⟨u' k'' (σ.comp ρ), by rw [Tm.isub_isub]; exact (hu' k'' (σ.comp ρ)).1,
    by rw [Tm.isub_isub, Tm.isub_isub]; exact (hu' k'' (σ.comp ρ)).2, ?_⟩
  have hAσρ := RT2.isub hW hXσ hAσ ρ
  have := h k' σ k'' ρ
  rw [← Tm.isub_isub] at this
  exact RE2.symm hW hAσρ this


/-- A composition whose face holds is its tube's end, at every restriction. -/
theorem stable_hcompFace {X T u a : Tm} {φ : I} (h : I.Entails .one φ)
    (hty : HasTy S k .one [] (.hcomp T φ u a) X) : StableE S k X (.hcomp T φ u a) (u.dinst .one) := by
  intro k' σ
  have hσ : I.Entails .one (φ.subst σ.τ) := by have := ent_subst h σ.τ; simpa [I.subst] using this
  have hty' : HasTy S k' .one [] (.hcomp (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ)) (X.isub σ) :=
    HasTy.isubS hW hty σ
  show Red S (.hcomp (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ)) _ ∧ _
  rw [isub_dinst]
  exact ⟨.step (step_hcomp_face hσ) (.refl _), EqTm.hcompFace hσ hty'⟩

/-- A transport whose face holds is its base, at every restriction. -/
theorem stable_transpFace {X T a : Tm} {φ : I} (h : I.Entails .one φ)
    (hty : HasTy S k .one [] (.transp T φ a) X) : StableE S k X (.transp T φ a) a := by
  intro k' σ
  have hσ : I.Entails .one (φ.subst σ.τ) := by have := ent_subst h σ.τ; simpa [I.subst] using this
  have hty' : HasTy S k' .one [] (.transp (T.isub σ.up) (φ.subst σ.τ) (a.isub σ)) (X.isub σ) :=
    HasTy.isubS hW hty σ
  show Red S (.transp (T.isub σ.up) (φ.subst σ.τ) (a.isub σ)) _ ∧ _
  exact ⟨.step (step_transp_face hσ) (.refl _), EqTm.transpFace hσ hty'⟩

end

end Model.Whnf
