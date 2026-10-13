import Model.Canon.Basic
import Mathlib.SetTheory.ZFC.Rank

/-!
# Canonicity: ranks of the parts of values

Projections, application and data lookup never increase the rank, and the datum of a nonempty
value is below it. This is the measure of the recursion defining computability.
-/

set_option autoImplicit false

namespace Model.Canon

open ZFSet

noncomputable section

variable {k m : ℕ}

theorem rank_pair_left (a b : V) : rank a < rank (ZFSet.pair a b) :=
  (rank_lt_of_mem (show a ∈ ({a} : V) by simp)).trans
    (rank_lt_of_mem (show ({a} : V) ∈ ZFSet.pair a b by simp [ZFSet.pair]))

theorem rank_pair_right (a b : V) : rank b < rank (ZFSet.pair a b) :=
  (rank_lt_of_mem (show b ∈ ({a, b} : V) by simp)).trans
    (rank_lt_of_mem (show ({a, b} : V) ∈ ZFSet.pair a b by simp [ZFSet.pair]))

theorem rank_π1_le (z : V) : rank (π1 z) ≤ rank z := by
  unfold π1; split
  · rename_i h
    obtain ⟨b, hb⟩ := h.choose_spec
    conv_rhs => rw [hb]
    exact (rank_pair_left _ _).le
  · rw [rank_empty]; exact bot_le

theorem rank_π2_le (z : V) : rank (π2 z) ≤ rank z := by
  unfold π2; split
  · rename_i h
    conv_rhs => rw [h.choose_spec.choose_spec]
    exact (rank_pair_right _ _).le
  · rw [rank_empty]; exact bot_le

theorem rank_apZ_le (g x : V) : rank (apZ g x) ≤ rank g := by
  unfold apZ; split
  · rename_i h
    exact ((rank_pair_right _ _).trans (rank_lt_of_mem h.choose_spec)).le
  · rw [rank_empty]; exact bot_le

theorem rank_pos_of_ne {X : V} (h : X ≠ ∅) : 0 < rank X := by
  have : ∃ y, y ∈ X := by
    by_contra hn; push Not at hn; exact h (ZFSet.eq_empty X |>.2 hn)
  obtain ⟨y, hy⟩ := this
  exact (bot_le).trans_lt (rank_lt_of_mem hy)

theorem rank_apZ_lt {g x : V} (h : g ≠ ∅) : rank (apZ g x) < rank g := by
  unfold apZ; split
  · rename_i h'
    exact (rank_pair_right _ _).trans (rank_lt_of_mem h'.choose_spec)
  · rw [rank_empty]; exact rank_pos_of_ne h

theorem mkKV_ne_empty (F : (k : ℕ) → Hom k m → V) : mkKV m F ≠ ∅ := by
  intro h
  have : ZFSet.pair (enc (⟨m, Hom.id m⟩ : Dom m)) (F m (Hom.id m)) ∈ mkKV m F := by
    simp only [mkKV, fnC, mem_range]; exact ⟨⟨m, Hom.id m⟩, rfl⟩
  rw [h] at this; exact ZFSet.notMem_empty _ this

theorem IsKV.ne_empty {X : V} (h : IsKV m X) : X ≠ ∅ := by
  obtain ⟨F, rfl⟩ := h; exact mkKV_ne_empty F

theorem rank_dat_lt {X : V} (hX : X ≠ ∅) (f : Hom k m) : rank (dat X k f) < rank X := by
  unfold dat apC; exact rank_apZ_lt hX

theorem rank_dat_le (X : V) (f : Hom k m) : rank (dat X k f) ≤ rank X := by
  unfold dat apC; exact rank_apZ_le _ _

end

end Model.Canon
