import Model.Canon.DataBasic

/-!
# Canonicity: the argument types recorded in an inductive type's code

`tyLook` finds an argument type in the code's table: a genuine entry exactly for the valid
argument prefixes, where it is the argument type.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' n m : ℕ}

theorem Comp_empty (m k : ℕ) (f : Hom k m) : Comp S ∅ m k f = Pack.bot := by
  rw [Comp_eq]; unfold compF; rw [dif_neg (by simp)]

/-- The prefixes of argument lists the table of `Λ` records. -/
def ValidPre (Λ : SData n) (c j : ℕ) (pre : List V) : Prop :=
  ∃ hc : c < Λ.ctors.length, j ≤ (Λ.ctors[c]).args.length ∧ pre.length = j ∧
    ∀ i (hi : i < pre.length), pre[i] ∈ argSet Λ (delemSet Λ) n (Hom.id n) c Λ.ctors[c] (pre.take i) i

theorem tyLook_eq {Λ : SData n} {c j : ℕ} {pre : List V} (h : ValidPre Λ c j pre) :
    tyLook (shapeV Λ) c j pre = Λ.ty c j n (Hom.id n) pre := by
  obtain ⟨hc, hj, hl, hp⟩ := h
  let p : VPref Λ (delemSet Λ) n (Hom.id n) c Λ.ctors[c] j := ⟨pre, hl, hp⟩
  have hmem : ZFSet.pair (natZ c) (ZFSet.pair (natZ j) (ZFSet.pair (vlist pre) (Λ.ty c j n (Hom.id n) pre)))
      ∈ shapeV Λ := by
    simp only [shapeV, ZFSet.mem_iUnion, ZFSet.mem_range]
    exact ⟨⟨c, hc⟩, ⟨j, Nat.lt_succ_of_le hj⟩, p, rfl⟩
  have hex : ∃ T, ZFSet.pair (natZ c) (ZFSet.pair (natZ j) (ZFSet.pair (vlist pre) T)) ∈ shapeV Λ := ⟨_, hmem⟩
  rw [tyLook, dif_pos hex]
  have hs := Classical.choose_spec hex
  generalize Classical.choose hex = T0 at hs ⊢
  simp only [shapeV, ZFSet.mem_iUnion, ZFSet.mem_range, pair_inj', natZ_inj] at hs
  obtain ⟨c', j', p', h1, h2, h3, h4⟩ := hs
  have e3 : p'.1 = pre := vlist_injective h3
  rw [← h4, e3, h1, h2]

theorem tyLook_cases (Λ : SData n) (c j : ℕ) (pre : List V) :
    tyLook (shapeV Λ) c j pre = ∅ ∨ ValidPre Λ c j pre := by
  by_cases hex : ∃ T, ZFSet.pair (natZ c) (ZFSet.pair (natZ j) (ZFSet.pair (vlist pre) T)) ∈ shapeV Λ
  · right
    obtain ⟨T, hs⟩ := hex
    simp only [shapeV, ZFSet.mem_iUnion, ZFSet.mem_range, pair_inj', natZ_inj] at hs
    obtain ⟨⟨c', hc'⟩, ⟨j', hj'⟩, p', h1, h2, h3, -⟩ := hs
    simp only at h1 h2; subst h1; subst h2
    have e3 : p'.1 = pre := vlist_injective h3
    exact ⟨hc', Nat.le_of_lt_succ hj', e3 ▸ p'.2.1, e3 ▸ p'.2.2⟩
  · left; rw [tyLook, dif_neg hex]

/-- A computable element of a looked-up argument type: the prefix is valid. -/
theorem validPre_of_el {Λ : SData n} {c j : ℕ} {pre : List V} {k : ℕ} {A t : Tm}
    (h : (Comp S (tyLook (shapeV Λ) c j pre) k k (Hom.id k)).el A t) : ValidPre Λ c j pre := by
  rcases tyLook_cases Λ c j pre with h0 | h0
  · rw [h0, Comp_empty] at h; exact h.elim
  · exact h0

theorem validPre_of_ty {Λ : SData n} {c j : ℕ} {pre : List V} {k : ℕ} {A : Tm}
    (h : (Comp S (tyLook (shapeV Λ) c j pre) k k (Hom.id k)).ty A) : ValidPre Λ c j pre := by
  rcases tyLook_cases Λ c j pre with h0 | h0
  · rw [h0, Comp_empty] at h; exact h.elim
  · exact h0

end

end Model.Canon
