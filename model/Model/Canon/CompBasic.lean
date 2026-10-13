import Model.Canon.Sub

/-!
# Canonicity: unfolding computability

`Comp X` at `f` only depends on the data of `X` at the restrictions of `f` (and on `res f X`).
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore ZFSet

noncomputable section

variable {S : Sig} {k k' m m' : ℕ}

theorem Comp_unfold {X : V} (hX : X ≠ ∅) (f : Hom k m) :
    Comp S X m k f = body S k (fun k' g => dat X k' (f.comp g)) (res f X) (rank X)
      (fun k' g => rank_dat_lt hX _) (fun Y _ => Comp S Y) := by
  rw [Comp_eq]; unfold compF; rw [dif_pos hX]

theorem body_irrel (Dt : (k' : ℕ) → Hom k' k → V) (self : V) {ρ ρ' : Ordinal}
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ) (hD' : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ') :
    body S k Dt self ρ hD (fun Y _ => Comp S Y) = body S k Dt self ρ' hD' (fun Y _ => Comp S Y) := rfl

theorem body_congr {Dt Dt' : (k' : ℕ) → Hom k' k → V} (hDt : Dt = Dt') (self : V) {ρ ρ' : Ordinal}
    (hD : ∀ k' (h : Hom k' k), rank (Dt k' h) < ρ) (hD' : ∀ k' (h : Hom k' k), rank (Dt' k' h) < ρ') :
    body S k Dt self ρ hD (fun Y _ => Comp S Y) = body S k Dt' self ρ' hD' (fun Y _ => Comp S Y) := by
  subst hDt; rfl

theorem Comp_congr {X Y : V} (hX : X ≠ ∅) (hY : Y ≠ ∅) (f : Hom k m) (g : Hom k m')
    (hd : ∀ k' (h : Hom k' k), dat X k' (f.comp h) = dat Y k' (g.comp h)) (hr : res f X = res g Y) :
    Comp S X m k f = Comp S Y m' k g := by
  rw [Comp_unfold hX, Comp_unfold hY, hr]
  exact body_congr (funext fun k' => funext fun h => hd k' h) _ _ _

theorem Comp_res {X : V} (hX : X ≠ ∅) (g : Hom k m) (h : Hom k' k) :
    Comp S (res g X) k k' h = Comp S X m k' (g.comp h) := by
  refine Comp_congr (mkKV_ne_empty _) hX h (g.comp h) (fun n h' => ?_) ?_
  · show dat (res g X) n (h.comp h') = _
    rw [dat_res, Hom.comp_assoc]
  · show res h (res g X) = _
    rw [res_res]

/-- Computable elements are typed and in the code's element set. -/
theorem Comp_el_typed {X : V} {f : Hom k m} {A t : Tm} (h : (Comp S X m k f).el A t) :
    HasTy S k .one [] t A ∧ semK S k t ∈ El (res f X) (Hom.id k) := by
  by_cases hX : X = ∅
  · subst hX; rw [Comp_eq] at h; unfold compF at h; rw [dif_neg (by simp)] at h; exact h.elim
  · rw [Comp_unfold hX] at h; exact ⟨h.1, h.2.1⟩

end

end Model.Canon
