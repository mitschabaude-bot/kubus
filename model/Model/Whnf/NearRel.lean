import Model.Whnf.Good
import Model.Whnf.Stable

/-!
# Near terms: reduction and judgmental equality

The hypothesis `NearTy S`: a typed closed term is judgmentally equal to every closed term near it
(`TmNear`: the same shape, interval points equal in the free De Morgan algebra, faces mutually
entailing). It is a theorem of the metatheory (the near-substitution lemma), stated here as a
hypothesis until it lands.

Reduction respects nearness (`red_near`, `redW_near`), and good terms near closed ones are closed
(`closed_of_near_good`), so the weak-head normal forms of near terms are judgmentally equal where the
terms are typed (`RedT.near`, `RedE.near`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

/-- Typed closed terms are judgmentally equal to the closed terms near them. -/
def NearTy (S : Sig) : Prop :=
  ∀ {k : ℕ} {Φ : I} {t t' A : Tm}, HasTy S k Φ [] t A → TmNear t t' → t'.closedB 0 k = true → EqTm S k Φ [] t t' A

variable {S : Sig} {k : ℕ}

theorem TmNear.isub {t t' : Tm} (h : TmNear t t') {k' : ℕ} (σ : ISub k' k) : TmNear (t.isub σ) (t'.isub σ) :=
  h.dsubst fun _ => I_eq_refl _

theorem whnf_near {w w' : Tm} (hw : IsWhnf S w) (h : TmNear w w') : IsWhnf S w' := by
  unfold IsWhnf at hw ⊢
  exact (rel_isNone (step_near S h)).1 hw

theorem red_near {t u : Tm} (h : Red S t u) : ∀ {t'}, TmNear t t' → ∃ u', Red S t' u' ∧ TmNear u u' := by
  induction h with
  | refl t => intro t' ht; exact ⟨t', .refl _, ht⟩
  | step hs _ ih =>
    intro t' ht
    have := step_near S ht
    rw [hs] at this
    revert this
    generalize hs' : step S t' = o
    intro this
    cases this with
    | some hx =>
      obtain ⟨u', hr, hu⟩ := ih hx
      exact ⟨u', .step hs' hr, hu⟩

theorem redW_near {t w t' : Tm} (h : RedW S t w) (ht : TmNear t t') : ∃ w', RedW S t' w' ∧ TmNear w w' := by
  obtain ⟨w', hr, hw⟩ := red_near h.1 ht
  exact ⟨w', ⟨hr, whnf_near h.2 hw⟩, hw⟩

theorem red_good (hW : WfSig S) {t u : Tm} (h : Red S t u) {m : ℕ} (hg : goodB S m t = true) : goodB S m u = true := by
  induction h with
  | refl => exact hg
  | step hs _ ih => exact ih (step_good hW _ hg hs)

/-- A good term near a closed term is closed. -/
theorem closed_of_near_good {t t' : Tm} (h : TmNear t t') : ∀ {n m : ℕ}, t.closedB n m = true → goodB S m t' = true →
    t'.closedB n m = true := by
  induction h with
  | var | const | univ | abort | tnil => intro n m h _; exact h
  | pi _ _ ih1 ih2 | sigma _ _ ih1 ih2 | lam _ _ ih1 ih2 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢; exact ⟨ih1 h.1 hg.1, ih2 h.2 hg.2⟩
  | app _ _ ih1 ih2 | pair _ _ ih1 ih2 | tcons _ _ ih1 ih2 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢; exact ⟨ih1 h.1 hg.1, ih2 h.2 hg.2⟩
  | fst _ ih | snd _ ih | data _ ih | plam _ ih | ipi _ ih =>
    intro n m h hg; simp only [Tm.closedB, goodB] at h hg ⊢; exact ih h hg
  | path _ _ _ ih1 ih2 ih3 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨ih1 h.1.1 hg.1.1, ih2 h.1.2 hg.1.2⟩, ih3 h.2 hg.2⟩
  | papp _ _ ih =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢; exact ⟨ih h.1 hg.1, hg.2⟩
  | split _ _ _ _ ih1 ih2 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨⟨hg.1.1.1, ih1 h.1.1.2 hg.1.1.2⟩, hg.1.2⟩, ih2 h.2 hg.2⟩
  | transp _ _ _ ih1 ih2 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨ih1 h.1.1 hg.1.1, hg.1.2⟩, ih2 h.2 hg.2⟩
  | hcomp _ _ _ _ ih1 ih2 ih3 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨⟨ih1 h.1.1.1 hg.1.1.1, hg.1.1.2⟩, ih2 h.1.2 hg.1.2⟩, ih3 h.2 hg.2⟩
  | glue _ _ _ _ ih1 ih2 ih3 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨⟨ih1 h.1.1.1 hg.1.1.1, hg.1.1.2⟩, ih2 h.1.2 hg.1.2⟩, ih3 h.2 hg.2⟩
  | glueEl _ _ _ _ ih1 ih2 ih3 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨⟨hg.1.1.1, ih1 h.1.1.2 hg.1.1.2⟩, ih2 h.1.2 hg.1.2⟩, ih3 h.2 hg.2⟩
  | unglue _ _ _ ih1 ih2 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨hg.1.1, ih1 h.1.2 hg.1.2⟩, ih2 h.2 hg.2⟩
  | con _ _ _ ih1 ih2 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨ih1 h.1.1 hg.1.1.1, ih2 h.1.2 hg.1.1.2⟩, hg.1.2⟩
  | elim _ _ _ _ ih1 ih2 ih3 ih4 =>
    intro n m h hg; simp only [Tm.closedB, goodB, Bool.and_eq_true] at h hg ⊢
    exact ⟨⟨⟨ih1 h.1.1.1 hg.1.1.1, ih2 h.1.1.2 hg.1.1.2⟩, ih3 h.1.2 hg.1.2⟩, ih4 h.2 hg.2⟩

section
variable (hW : WfSig S) (hN : NearTy S)
include hW hN

/-- A typed closed term and a good term near it are judgmentally equal. -/
theorem eq_near {t t' A : Tm} (ht : HasTy S k .one [] t A) (h : TmNear t t') (hg : goodB S k t' = true) :
    EqTm S k .one [] t t' A :=
  hN ht h (closed_of_near_good h (closed_of_ty hW ht) hg)

/-- A type and a good term near it are equal types. -/
theorem tyEq_near {A A' : Tm} (hA : IsTyK S k A) (h : TmNear A A') (hg : goodB S k A' = true) :
    TyEq S k A A' ∧ IsTyK S k A' := by
  obtain ⟨l, hA | rfl⟩ := hA
  · have e := eq_near hW hN hA h hg
    exact ⟨.inr ⟨l, e⟩, ⟨l, .inl (HasTy.eqR e)⟩⟩
  · cases h; exact ⟨.inl rfl, ⟨l, .inr rfl⟩⟩

/-- The weak-head normal form of a good type near a type with a normal form. -/
theorem RedT.near {T W T' : Tm} (h : RedT S k T W) (hT : IsTyK S k T) (hn : TmNear T T') (hg : goodB S k T' = true) :
    ∃ W', RedT S k T' W' ∧ TmNear W W' := by
  obtain ⟨W', hr, hw⟩ := redW_near h.1 hn
  have hgW : goodB S k W' = true := red_good hW hr.1 hg
  have hWt : IsTyK S k W := by
    rcases h.2 with e | ⟨l, e⟩
    · exact e ▸ hT
    · exact ⟨l, .inl (HasTy.eqR e)⟩
  obtain ⟨e1, -⟩ := tyEq_near hW hN hT hn hg
  obtain ⟨e2, -⟩ := tyEq_near hW hN hWt hw hgW
  exact ⟨W', ⟨hr, (e1.symm.trans hW h.2).trans hW e2⟩, hw⟩

/-- The weak-head normal form of a good term near a term with a normal form, at a typed type. -/
theorem RedE.near {A t w t' : Tm} (h : RedE S k A t w) (ht : HasTy S k .one [] t A) (hn : TmNear t t')
    (hg : goodB S k t' = true) : ∃ w', RedE S k A t' w' ∧ TmNear w w' := by
  obtain ⟨w', hr, hw⟩ := redW_near h.1 hn
  have hgw : goodB S k w' = true := red_good hW hr.1 hg
  have e1 := eq_near hW hN ht hn hg
  have e2 := eq_near hW hN (HasTy.eqR h.2) hw hgw
  exact ⟨w', ⟨hr, (e1.symm.trans h.2).trans e2⟩, hw⟩

end

end Model.Whnf
