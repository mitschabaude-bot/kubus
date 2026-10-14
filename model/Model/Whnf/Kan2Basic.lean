import Model.Whnf.Valid2Glue

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

/-- Related tubes: related where the face holds, at all restrictions and `I.Eq`-equal points. -/
def Tube2 (S : Sig) (k : ℕ) (A : Tm) (φ : I) (u u' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
    (ival (idEnv k') (φ.subst σ.τ)).holds → RE2 S k' (A.isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r')

/-- Composition in related types relates related tubes and bases. -/
def KanH2 (S : Sig) (k : ℕ) (A A' : Tm) : Prop :=
  ∀ (φ φ' : I) (u u' a a' : Tm), HasTy S k .one [] (.hcomp A φ u a) A → HasTy S k .one [] (.hcomp A' φ' u' a') A →
    EqTm S k .one [] (.hcomp A φ u a) (.hcomp A' φ' u' a') A →
    I.Entails φ φ' → I.Entails φ' φ → Tube2 S k A φ u u' → RE2 S k A a a' →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ)) →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) →
    RE2 S k A (.hcomp A φ u a) (.hcomp A' φ' u' a')

/-- Lines (at stage `k + 1`) related at `I.Eq`-equal points of every restriction. -/
def LineRob (S : Sig) (k : ℕ) (A A' : Tm) : Prop :=
  ∀ k' (τ : ISub k' k) (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
    RT2 S k' (A.isub (ISub.cons r hr τ)) (A'.isub (ISub.cons r' hr' τ))

/-- A line (at stage `k + 1`) is constant where the face `φ` holds. -/
def LineConst (S : Sig) (k : ℕ) (A : Tm) (φ : I) : Prop :=
  ∀ k' (σ : ISub k' k) (r : I) (hr : r.Scoped k'), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RT2 S k' (A.isub (ISub.cons r hr σ)) (A.isub (ISub.cons .zero trivial σ))

/-- Transport along related lines (at stage `k + 1`) relates related elements. -/
def KanT2 (S : Sig) (k : ℕ) (A A' : Tm) : Prop :=
  LineRob S k A A' →
  ∀ (φ φ' : I) (a a' : Tm), LineConst S k A φ → HasTy S k .one [] (.transp A φ a) (A.dinst .one) →
    HasTy S k .one [] (.transp A' φ' a') (A.dinst .one) →
    EqTm S k .one [] (.transp A φ a) (.transp A' φ' a') (A.dinst .one) → I.Entails φ φ' → I.Entails φ' φ →
    RE2 S k (A.dinst .zero) a a' → RE2 S k (A.dinst .one) (.transp A φ a) (.transp A' φ' a')

/-- The Kan properties of all pairs of types related at a restriction of the code `X`. -/
def KanP2 (S : Sig) (m : ℕ) (X : V) : Prop :=
  (∀ k (f : Hom k m) (A A' : Tm), (Comp2 S X m k f).ty A A' → KanH2 S k A A') ∧
  (∀ k (f : Hom (k + 1) m) (A A' : Tm), (Comp2 S X m (k + 1) f).ty A A' → KanT2 S k A A')

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
