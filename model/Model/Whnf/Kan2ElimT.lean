import Model.Whnf.Kan2Elim

/-!
# Transport, observed through an elimination

A transport `transp T φ a0` whose elements are observed through an elimination `E` is related to
`transp T' φ' a0'` once the eliminated transports are: at each restriction, an eliminated transport
reduces to its eliminated base where the face holds, and otherwise to a transport along an eliminated
line `C` with an eliminated base `A0`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- The generic core of transport through an elimination. -/
theorem kanT2_elim_core {T T' Y a0 a0' : Tm} {φ φ' : I}
    (E E' : ∀ k' (_ : ISub k' k), Tm → Tm)
    (C C' : ∀ k' (_ : ISub k' k), Tm) (A0 A0' : ∀ k' (_ : ISub k' k), Tm)
    (hX : TyCode k (semK S k Y)) (hYY : RT2 S k Y Y)
    (ht : HasTy S k .one [] (E k (ISub.id k) (.transp T φ a0)) Y)
    (ht' : HasTy S k .one [] (E' k (ISub.id k) (.transp T' φ' a0')) Y)
    (hE0 : EqTm S k .one [] (E k (ISub.id k) (.transp T φ a0)) (E' k (ISub.id k) (.transp T' φ' a0')) Y)
    (hEnat : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') x, (E k' ρ x).isub ρ' = E k'' (ρ.comp ρ') (x.isub ρ'))
    (hEnat' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') x, (E' k' ρ x).isub ρ' = E' k'' (ρ.comp ρ') (x.isub ρ'))
    (hred : ∀ k' (ρ : ISub k' k),
      (I.Entails .one (φ.subst ρ.τ) → Red S (E k' ρ ((Tm.transp T φ a0).isub ρ)) (E k' ρ (a0.isub ρ)) ∧
        EqTm S k' .one [] (E k' ρ ((Tm.transp T φ a0).isub ρ)) (E k' ρ (a0.isub ρ)) (Y.isub ρ)) ∧
      (¬ I.Entails .one (φ.subst ρ.τ) → Red S (E k' ρ ((Tm.transp T φ a0).isub ρ))
          (.transp (C k' ρ) (φ.subst ρ.τ) (A0 k' ρ)) ∧
        EqTm S k' .one [] (E k' ρ ((Tm.transp T φ a0).isub ρ)) (.transp (C k' ρ) (φ.subst ρ.τ) (A0 k' ρ))
          (Y.isub ρ)))
    (hred' : ∀ k' (ρ : ISub k' k),
      (I.Entails .one (φ'.subst ρ.τ) → Red S (E' k' ρ ((Tm.transp T' φ' a0').isub ρ)) (E' k' ρ (a0'.isub ρ)) ∧
        EqTm S k' .one [] (E' k' ρ ((Tm.transp T' φ' a0').isub ρ)) (E' k' ρ (a0'.isub ρ)) (Y.isub ρ)) ∧
      (¬ I.Entails .one (φ'.subst ρ.τ) → Red S (E' k' ρ ((Tm.transp T' φ' a0').isub ρ))
          (.transp (C' k' ρ) (φ'.subst ρ.τ) (A0' k' ρ)) ∧
        EqTm S k' .one [] (E' k' ρ ((Tm.transp T' φ' a0').isub ρ)) (.transp (C' k' ρ) (φ'.subst ρ.τ) (A0' k' ρ))
          (Y.isub ρ)))
    -- the eliminated bases where the face holds
    (hfin : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst ρ.τ) →
      RE2 S k' (Y.isub ρ) (E k' ρ (a0.isub ρ)) (E' k' ρ (a0'.isub ρ)))
    (hA1 : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst ρ.τ) →
      I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RE2 S k'' (Y.isub (ρ.comp ρ')) ((A0 k' ρ).isub ρ') (E' k'' (ρ.comp ρ') (a0'.isub (ρ.comp ρ'))))
    -- the eliminated lines and bases where the face does not hold
    (hCY : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RT2 S k'' (((C k' ρ).isub ρ'.up).dinst .one) (Y.isub (ρ.comp ρ')))
    (hLR : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      LineRob S k'' ((C k' ρ).isub ρ'.up) (C' k'' (ρ.comp ρ')))
    (hLC : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      LineConst S k'' ((C k' ρ).isub ρ'.up) ((φ.subst ρ.τ).subst ρ'.τ))
    (hA0r : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RE2 S k'' (((C k' ρ).isub ρ'.up).dinst .zero) ((A0 k' ρ).isub ρ') (A0' k'' (ρ.comp ρ')))
    (hIH : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      KanT2 S k'' ((C k' ρ).isub ρ'.up) (C' k'' (ρ.comp ρ')))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) :
    RE2 S k Y (E k (ISub.id k) (.transp T φ a0)) (E' k (ISub.id k) (.transp T' φ' a0')) := by
  have hnat0 : ∀ k' (ρ : ISub k' k), (E k (ISub.id k) (.transp T φ a0)).isub ρ =
      E k' ρ ((Tm.transp T φ a0).isub ρ) := by
    intro k' ρ; rw [hEnat, ISub.id_comp]
  have hnat0' : ∀ k' (ρ : ISub k' k), (E' k (ISub.id k) (.transp T' φ' a0')).isub ρ =
      E' k' ρ ((Tm.transp T' φ' a0').isub ρ) := by
    intro k' ρ; rw [hEnat', ISub.id_comp]
  let L : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    if I.Entails .one (φ.subst ρ.τ) then E k' ρ (a0.isub ρ) else .transp (C k' ρ) (φ.subst ρ.τ) (A0 k' ρ)
  let R : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    if I.Entails .one (φ'.subst ρ.τ) then E' k' ρ (a0'.isub ρ) else .transp (C' k' ρ) (φ'.subst ρ.τ) (A0' k' ρ)
  have hu : ∀ k' (ρ : ISub k' k), Red S ((E k (ISub.id k) (.transp T φ a0)).isub ρ) (L k' ρ) ∧
      EqTm S k' .one [] ((E k (ISub.id k) (.transp T φ a0)).isub ρ) (L k' ρ) (Y.isub ρ) := by
    intro k' ρ
    rw [hnat0]
    by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · simp only [L, if_pos hf]; exact (hred k' ρ).1 hf
    · simp only [L, if_neg hf]; exact (hred k' ρ).2 hf
  have hu' : ∀ k' (ρ : ISub k' k), Red S ((E' k (ISub.id k) (.transp T' φ' a0')).isub ρ) (R k' ρ) ∧
      EqTm S k' .one [] ((E' k (ISub.id k) (.transp T' φ' a0')).isub ρ) (R k' ρ) (Y.isub ρ) := by
    intro k' ρ
    rw [hnat0']
    by_cases hf : I.Entails .one (φ'.subst ρ.τ)
    · simp only [R, if_pos hf]; exact (hred' k' ρ).1 hf
    · simp only [R, if_neg hf]; exact (hred' k' ρ).2 hf
  refine RE2.expandBoth hW hX hYY ht ht' L R hu hu' fun k' ρ k'' ρ' => ?_
  have hRpos : I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      R k'' (ρ.comp ρ') = E' k'' (ρ.comp ρ') (a0'.isub (ρ.comp ρ')) := by
    intro hf2
    have hf2' : I.Entails .one (φ'.subst (ρ.comp ρ').τ) := ent_trans hf2 (ent_subst h12 _)
    simp only [R, if_pos hf2']
  have htyL : HasTy S k'' .one [] ((L k' ρ).isub ρ') (Y.isub (ρ.comp ρ')) := by
    have := HasTy.isubS hW (HasTy.eqR (hu k' ρ).2) ρ'
    rwa [Tm.isub_isub] at this
  have htyR : HasTy S k'' .one [] (R k'' (ρ.comp ρ')) (Y.isub (ρ.comp ρ')) := HasTy.eqR (hu' k'' (ρ.comp ρ')).2
  have hYτ : RT2 S k'' (Y.isub (ρ.comp ρ')) (Y.isub (ρ.comp ρ')) := RT2.isub hW hX hYY _
  by_cases hf : I.Entails .one (φ.subst ρ.τ)
  · have hL : (L k' ρ).isub ρ' = E k'' (ρ.comp ρ') (a0.isub (ρ.comp ρ')) := by
      simp only [L, if_pos hf]
      rw [hEnat, Tm.isub_isub]
    rw [hL, hRpos (ent_comp hf)]
    exact hfin k'' (ρ.comp ρ') (ent_comp hf)
  have hL : (L k' ρ).isub ρ' = .transp ((C k' ρ).isub ρ'.up) ((φ.subst ρ.τ).subst ρ'.τ) ((A0 k' ρ).isub ρ') := by
    simp only [L, if_neg hf]; rfl
  by_cases hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ)
  · have hface : I.Entails .one ((φ.subst ρ.τ).subst ρ'.τ) := by rw [← I_subst_comp]; exact hf2
    have hst := stable_transpFace hW hface (hL ▸ htyL)
    rw [hL] at htyL ⊢
    refine RE2.expandL hW hYτ htyL htyR hst ?_
    rw [hRpos hf2]
    exact hA1 k' ρ k'' ρ' hf hf2
  · have hf2' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hf2 (ent_trans h (ent_subst h21 _))
    have hR' : R k'' (ρ.comp ρ') = .transp (C' k'' (ρ.comp ρ')) (φ'.subst (ρ.comp ρ').τ) (A0' k'' (ρ.comp ρ')) := by
      simp only [R, if_neg hf2']
    have hXY := hCY k' ρ k'' ρ' hf2
    have hXc : TyCode k'' (semK S k'' (Y.isub (ρ.comp ρ'))) := tyCode_of_ty hW htyR
    have hTyXY := (Comp2_ty_base hXY).2.2.2.2.2
    have EL := EqTm.isubS hW (hu k' ρ).2 ρ'
    rw [Tm.isub_isub, Tm.isub_isub] at EL
    have Eall := (EL.symm.trans (EqTm.isubS hW hE0 (ρ.comp ρ'))).trans (hu' k'' (ρ.comp ρ')).2
    rw [hL, hR'] at Eall
    rw [hL] at htyL
    rw [hR'] at htyR
    rw [hL, hR']
    have e12 : I.Entails ((φ.subst ρ.τ).subst ρ'.τ) (φ'.subst (ρ.comp ρ').τ) := by
      rw [← I_subst_comp]; exact ent_subst h12 _
    have e21 : I.Entails (φ'.subst (ρ.comp ρ').τ) ((φ.subst ρ.τ).subst ρ'.τ) := by
      rw [← I_subst_comp]; exact ent_subst h21 _
    exact RE2.conv hW hXY (hIH k' ρ k'' ρ' hf2 (hLR k' ρ k'' ρ' hf2) _ _ _ _ (hLC k' ρ k'' ρ' hf2)
      (htyL.tyConv (TyEq.symm hTyXY)) (htyR.tyConv (TyEq.symm hTyXY)) (Eall.tyConv (TyEq.symm hTyXY)) e12 e21
      (hA0r k' ρ k'' ρ' hf2))

end

end Model.Whnf
