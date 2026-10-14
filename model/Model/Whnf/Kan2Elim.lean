import Model.Whnf.Kan2Pi

/-!
# Composition, observed through an elimination

A composition `hcomp T φ u a0` at a type whose elements are observed through an elimination `E`
(application, path application, ...) is related to `hcomp T' φ' u' a0'` once the eliminated
compositions are: at each restriction, an eliminated composition reduces to its tube's end where the
face holds, and otherwise to a composition at the eliminated type, with eliminated tube and base.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- The generic core of composition through an elimination: `E` (resp. `E'`) applied to a restricted
composition reduces to the tube's end where the face holds, and otherwise to a composition at `C`
(resp. `C'`) with face `Ψ` (resp. `Ψ'`), tube `U` (resp. `U'`) and base `A0` (resp. `A0'`). -/
theorem kanH2_elim_core {T T' Y u u' a0 a0' : Tm} {φ φ' : I} (hφs : φ.Scoped k)
    (E E' : ∀ k' (_ : ISub k' k), Tm → Tm)
    (C C' U U' A0 A0' : ∀ k' (_ : ISub k' k), Tm) (Ψ Ψ' : ∀ k' (_ : ISub k' k), I)
    (hΨsc : ∀ k' (ρ : ISub k' k), (Ψ k' ρ).Scoped k')
    (hX : TyCode k (semK S k Y)) (hYY : RT2 S k Y Y)
    (ht : HasTy S k .one [] (E k (ISub.id k) (.hcomp T φ u a0)) Y)
    (ht' : HasTy S k .one [] (E' k (ISub.id k) (.hcomp T' φ' u' a0')) Y)
    (hE0 : EqTm S k .one [] (E k (ISub.id k) (.hcomp T φ u a0)) (E' k (ISub.id k) (.hcomp T' φ' u' a0')) Y)
    (hEnat : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') x, (E k' ρ x).isub ρ' = E k'' (ρ.comp ρ') (x.isub ρ'))
    (hEnat' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') x, (E' k' ρ x).isub ρ' = E' k'' (ρ.comp ρ') (x.isub ρ'))
    (hred : ∀ k' (ρ : ISub k' k),
      (I.Entails .one (φ.subst ρ.τ) → Red S (E k' ρ ((Tm.hcomp T φ u a0).isub ρ)) (E k' ρ ((u.isub ρ.up).dinst .one)) ∧
        EqTm S k' .one [] (E k' ρ ((Tm.hcomp T φ u a0).isub ρ)) (E k' ρ ((u.isub ρ.up).dinst .one)) (Y.isub ρ)) ∧
      (¬ I.Entails .one (φ.subst ρ.τ) → Red S (E k' ρ ((Tm.hcomp T φ u a0).isub ρ))
          (.hcomp (C k' ρ) (Ψ k' ρ) (U k' ρ) (A0 k' ρ)) ∧
        EqTm S k' .one [] (E k' ρ ((Tm.hcomp T φ u a0).isub ρ)) (.hcomp (C k' ρ) (Ψ k' ρ) (U k' ρ) (A0 k' ρ))
          (Y.isub ρ)))
    (hred' : ∀ k' (ρ : ISub k' k),
      (I.Entails .one (φ'.subst ρ.τ) → Red S (E' k' ρ ((Tm.hcomp T' φ' u' a0').isub ρ))
          (E' k' ρ ((u'.isub ρ.up).dinst .one)) ∧
        EqTm S k' .one [] (E' k' ρ ((Tm.hcomp T' φ' u' a0').isub ρ)) (E' k' ρ ((u'.isub ρ.up).dinst .one)) (Y.isub ρ)) ∧
      (¬ I.Entails .one (φ'.subst ρ.τ) → Red S (E' k' ρ ((Tm.hcomp T' φ' u' a0').isub ρ))
          (.hcomp (C' k' ρ) (Ψ' k' ρ) (U' k' ρ) (A0' k' ρ)) ∧
        EqTm S k' .one [] (E' k' ρ ((Tm.hcomp T' φ' u' a0').isub ρ))
          (.hcomp (C' k' ρ) (Ψ' k' ρ) (U' k' ρ) (A0' k' ρ)) (Y.isub ρ)))
    -- the eliminations of related elements
    (hfinU : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst ρ.τ) →
      RE2 S k' (Y.isub ρ) (E k' ρ ((u.isub ρ.up).dinst .one)) (E' k' ρ ((u'.isub ρ.up).dinst .one)))
    -- the eliminated faces
    (hΨ : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      I.Entails .one ((Ψ k' ρ).subst ρ'.τ))
    (hΨΨ : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      I.Entails ((Ψ k' ρ).subst ρ'.τ) (Ψ' k'' (ρ.comp ρ')) ∧ I.Entails (Ψ' k'' (ρ.comp ρ')) ((Ψ k' ρ).subst ρ'.τ))
    -- the eliminated tubes and bases
    (hU1 : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst ρ.τ) →
      I.Entails .one (φ.subst (ρ.comp ρ').τ) → RE2 S k'' (Y.isub (ρ.comp ρ')) (((U k' ρ).isub ρ'.up).dinst .one)
        (E' k'' (ρ.comp ρ') ((u'.isub (ρ.comp ρ').up).dinst .one)))
    (hTU : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      Tube2 S k'' (Y.isub (ρ.comp ρ')) ((Ψ k' ρ).subst ρ'.τ) ((U k' ρ).isub ρ'.up) (U' k'' (ρ.comp ρ')))
    (hA0r : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RE2 S k'' (Y.isub (ρ.comp ρ')) ((A0 k' ρ).isub ρ') (A0' k'' (ρ.comp ρ')))
    (hUEq : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      EqTm S (k'' + 1) (cof .one ((Ψ k' ρ).subst ρ'.τ)).shift [] ((U k' ρ).isub ρ'.up) (U' k'' (ρ.comp ρ'))
        (Y.isub (ρ.comp ρ')).dshift)
    (hUb : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      ∀ k3 (σ3 : ISub k3 k''), (ival (idEnv k3) (((Ψ k' ρ).subst ρ'.τ).subst σ3.τ)).holds →
      RE2 S k3 ((Y.isub (ρ.comp ρ')).isub σ3) ((((U k' ρ).isub ρ'.up).isub σ3.up).dinst .zero)
        ((A0' k'' (ρ.comp ρ')).isub σ3))
    (hUb' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      ∀ k3 (σ3 : ISub k3 k''), (ival (idEnv k3) (((Ψ k' ρ).subst ρ'.τ).subst σ3.τ)).holds →
      RE2 S k3 ((Y.isub (ρ.comp ρ')).isub σ3) (((A0 k' ρ).isub ρ').isub σ3)
        (((U' k'' (ρ.comp ρ')).isub σ3.up).dinst .zero))
    -- the eliminated types
    (hCY : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RT2 S k'' ((C k' ρ).isub ρ') (Y.isub (ρ.comp ρ')))
    (hIH : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      KanH2 S k'' ((C k' ρ).isub ρ') (C' k'' (ρ.comp ρ')))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) :
    RE2 S k Y (E k (ISub.id k) (.hcomp T φ u a0)) (E' k (ISub.id k) (.hcomp T' φ' u' a0')) := by
  have hnat0 : ∀ k' (ρ : ISub k' k), (E k (ISub.id k) (.hcomp T φ u a0)).isub ρ = E k' ρ ((Tm.hcomp T φ u a0).isub ρ) := by
    intro k' ρ; rw [hEnat, ISub.id_comp]
  have hnat0' : ∀ k' (ρ : ISub k' k), (E' k (ISub.id k) (.hcomp T' φ' u' a0')).isub ρ =
      E' k' ρ ((Tm.hcomp T' φ' u' a0').isub ρ) := by
    intro k' ρ; rw [hEnat', ISub.id_comp]
  let L : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    if I.Entails .one (φ.subst ρ.τ) then E k' ρ ((u.isub ρ.up).dinst .one)
    else .hcomp (C k' ρ) (Ψ k' ρ) (U k' ρ) (A0 k' ρ)
  let R : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    if I.Entails .one (φ'.subst ρ.τ) then E' k' ρ ((u'.isub ρ.up).dinst .one)
    else .hcomp (C' k' ρ) (Ψ' k' ρ) (U' k' ρ) (A0' k' ρ)
  have hu : ∀ k' (ρ : ISub k' k), Red S ((E k (ISub.id k) (.hcomp T φ u a0)).isub ρ) (L k' ρ) ∧
      EqTm S k' .one [] ((E k (ISub.id k) (.hcomp T φ u a0)).isub ρ) (L k' ρ) (Y.isub ρ) := by
    intro k' ρ
    rw [hnat0]
    by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · simp only [L, if_pos hf]; exact (hred k' ρ).1 hf
    · simp only [L, if_neg hf]; exact (hred k' ρ).2 hf
  have hu' : ∀ k' (ρ : ISub k' k), Red S ((E' k (ISub.id k) (.hcomp T' φ' u' a0')).isub ρ) (R k' ρ) ∧
      EqTm S k' .one [] ((E' k (ISub.id k) (.hcomp T' φ' u' a0')).isub ρ) (R k' ρ) (Y.isub ρ) := by
    intro k' ρ
    rw [hnat0']
    by_cases hf : I.Entails .one (φ'.subst ρ.τ)
    · simp only [R, if_pos hf]; exact (hred' k' ρ).1 hf
    · simp only [R, if_neg hf]; exact (hred' k' ρ).2 hf
  refine RE2.expandBoth hW hX hYY ht ht' L R hu hu' fun k' ρ k'' ρ' => ?_
  have hholds : ∀ {k3 : ℕ} (τ : ISub k3 k), I.Entails .one (φ.subst τ.τ) → (ival (idEnv k3) (φ.subst τ.τ)).holds :=
    fun τ h => (holds_iff_entails (I.scoped_subst hφs τ.sc)).2 h
  have hRpos : I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      R k'' (ρ.comp ρ') = E' k'' (ρ.comp ρ') ((u'.isub (ρ.comp ρ').up).dinst .one) := by
    intro hf2
    have hf2' : I.Entails .one (φ'.subst (ρ.comp ρ').τ) := ent_trans hf2 (ent_subst h12 _)
    simp only [R, if_pos hf2']
  have htyL : HasTy S k'' .one [] ((L k' ρ).isub ρ') (Y.isub (ρ.comp ρ')) := by
    have := HasTy.isubS hW (HasTy.eqR (hu k' ρ).2) ρ'
    rwa [Tm.isub_isub] at this
  have htyR : HasTy S k'' .one [] (R k'' (ρ.comp ρ')) (Y.isub (ρ.comp ρ')) := HasTy.eqR (hu' k'' (ρ.comp ρ')).2
  have hYτ : RT2 S k'' (Y.isub (ρ.comp ρ')) (Y.isub (ρ.comp ρ')) := RT2.isub hW hX hYY _
  by_cases hf : I.Entails .one (φ.subst ρ.τ)
  · have hL : (L k' ρ).isub ρ' = E k'' (ρ.comp ρ') ((u.isub (ρ.comp ρ').up).dinst .one) := by
      simp only [L, if_pos hf]
      rw [hEnat, up_dinst_one_isub]
    rw [hL, hRpos (ent_comp hf)]
    exact hfinU k'' (ρ.comp ρ') (ent_comp hf)
  have hL : (L k' ρ).isub ρ' = .hcomp ((C k' ρ).isub ρ') ((Ψ k' ρ).subst ρ'.τ)
      ((U k' ρ).isub ρ'.up) ((A0 k' ρ).isub ρ') := by
    simp only [L, if_neg hf]; rfl
  by_cases hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ)
  · have hst := stable_hcompFace hW (hΨ k' ρ k'' ρ' hf2) (hL ▸ htyL)
    rw [hL] at htyL ⊢
    refine RE2.expandL hW hYτ htyL htyR hst ?_
    rw [hRpos hf2]
    exact hU1 k' ρ k'' ρ' hf hf2
  · have hf2' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hf2 (ent_trans h (ent_subst h21 _))
    have hR' : R k'' (ρ.comp ρ') = .hcomp (C' k'' (ρ.comp ρ')) (Ψ' k'' (ρ.comp ρ')) (U' k'' (ρ.comp ρ'))
        (A0' k'' (ρ.comp ρ')) := by
      simp only [R, if_neg hf2']
    have hXY := hCY k' ρ k'' ρ' hf2
    have hXc : TyCode k'' (semK S k'' (Y.isub (ρ.comp ρ'))) := tyCode_of_ty hW htyR
    have hXcode : TyCode k'' (semK S k'' ((C k' ρ).isub ρ')) := RT2.tyCode_l hW hXY hXc
    have hTyXY := (Comp2_ty_base hXY).2.2.2.2.2
    have EL := EqTm.isubS hW (hu k' ρ).2 ρ'
    rw [Tm.isub_isub, Tm.isub_isub] at EL
    have Eall := (EL.symm.trans (EqTm.isubS hW hE0 (ρ.comp ρ'))).trans (hu' k'' (ρ.comp ρ')).2
    rw [hL, hR'] at Eall
    rw [hL] at htyL
    rw [hR'] at htyR
    rw [hL, hR']
    obtain ⟨e12, e21⟩ := hΨΨ k' ρ k'' ρ' hf2
    refine RE2.conv hW hXY (hIH k' ρ k'' ρ' hf2 _ _ _ _ _ _ (htyL.tyConv (TyEq.symm hTyXY))
      (htyR.tyConv (TyEq.symm hTyXY)) (Eall.tyConv (TyEq.symm hTyXY))
      (EqTm.cofConv (I.scoped_subst (hΨsc k' ρ) ρ'.sc) (hUEq k' ρ k'' ρ' hf2) (TyEq.symm hTyXY)) e12 e21
      (fun k3 σ3 r r' hr hr' hE hh => ?_) ?_ (fun k3 σ3 hh => ?_) (fun k3 σ3 hh => ?_))
    · have h1 := hTU k' ρ k'' ρ' hf2 k3 σ3 r r' hr hr' hE hh
      have hXY3 := RT2.isub hW hXcode hXY σ3
      exact RE2.conv' hW hXY3 h1 (RT2.tyCode_l hW hXY3 (RE2.tyCode hW h1))
    · exact RE2.conv' hW hXY (hA0r k' ρ k'' ρ' hf2) hXcode
    · have h1 := hUb k' ρ k'' ρ' hf2 k3 σ3 hh
      have hXY3 := RT2.isub hW hXcode hXY σ3
      exact RE2.conv' hW hXY3 h1 (RT2.tyCode_l hW hXY3 (RE2.tyCode hW h1))
    · have h1 := hUb' k' ρ k'' ρ' hf2 k3 σ3 hh
      have hXY3 := RT2.isub hW hXcode hXY σ3
      exact RE2.conv' hW hXY3 h1 (RT2.tyCode_l hW hXY3 (RE2.tyCode hW h1))

end

end Model.Whnf
