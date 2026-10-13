import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Small.Basic
import Mathlib.Logic.Relation

/-!
# Encoding data as ZFC sets

The model's values are ZFC sets (`V := ZFSet.{0}`), so that raw terms can be interpreted
uniformly (application is graph lookup, no type information needed). This file provides:

* von Neumann naturals `natZ` and an injective encoding `enc` of countable Lean data;
* graphs `fnC F` of functions on a countable Lean type, with lookup `apC`;
* graphs `fnZ D F` of functions on a set `D`, with lookup `apZ`;
* tagged values `tagZ n x`;
* the `∈`-closure relation `Below` used for well-founded recursion on values.
-/

set_option autoImplicit false

namespace Model

/-- The universe of values. -/
abbrev V := ZFSet.{5}

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Naturals -/

def natZ : ℕ → V
  | 0 => ∅
  | n + 1 => insert (natZ n) (natZ n)

theorem natZ_mem_succ (n : ℕ) : natZ n ∈ natZ (n + 1) := mem_insert _ _

theorem natZ_mem_of_lt {m n : ℕ} (h : m < n) : natZ m ∈ natZ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact mem_insert_of_mem _ (ih h)
    · exact natZ_mem_succ _

theorem natZ_injective : Function.Injective natZ := by
  intro m n h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := natZ_mem_of_lt hlt; rw [h] at this; exact mem_irrefl _ this
  · have := natZ_mem_of_lt hlt; rw [h] at this; exact mem_irrefl _ this

@[simp] theorem natZ_inj {m n : ℕ} : natZ m = natZ n ↔ m = n := natZ_injective.eq_iff

/-! ### Countable data -/

/-- Injective encoding of countable data. -/
def enc {α : Type} [Countable α] (x : α) : V :=
  natZ (@Encodable.encode α (Encodable.ofCountable α) x)

theorem enc_injective {α : Type} [Countable α] : Function.Injective (enc : α → V) := by
  intro x y h
  exact @Encodable.encode_injective α (Encodable.ofCountable α) _ _ (natZ_injective h)

@[simp] theorem enc_inj {α : Type} [Countable α] {x y : α} : enc x = enc y ↔ x = y :=
  enc_injective.eq_iff

/-! ### Pairs and tags -/

@[simp] theorem pair_inj' {x y x' y' : V} : pair x y = pair x' y' ↔ x = x' ∧ y = y' := pair_inj

def tagZ (n : ℕ) (x : V) : V := pair (natZ n) x

@[simp] theorem tagZ_inj {n n' : ℕ} {x x' : V} : tagZ n x = tagZ n' x' ↔ n = n' ∧ x = x' := by
  simp [tagZ]

/-! ### `∈`-closure, for well-founded recursion on values -/

/-- `Below x y`: `x` is in the transitive closure of `y`. -/
def Below (x y : V) : Prop := Relation.TransGen (· ∈ ·) x y

theorem below_wf : WellFounded Below := ZFSet.mem_wf.transGen

theorem Below.of_mem {x y : V} (h : x ∈ y) : Below x y := Relation.TransGen.single h

theorem Below.trans {x y z : V} (h₁ : Below x y) (h₂ : Below y z) : Below x z :=
  Relation.TransGen.trans h₁ h₂

theorem Below.mem_trans {x y z : V} (h₁ : Below x y) (h₂ : y ∈ z) : Below x z :=
  h₁.trans (Below.of_mem h₂)

theorem below_pair_left (x y : V) : Below x (pair x y) :=
  (Below.of_mem (mem_singleton.2 rfl)).mem_trans (by simp [pair])

theorem below_pair_right (x y : V) : Below y (pair x y) :=
  (Below.of_mem (by simp : y ∈ ({x, y} : V))).mem_trans (by simp [pair])

theorem below_tagZ (n : ℕ) (x : V) : Below x (tagZ n x) := below_pair_right _ _

/-! ### Application of a graph -/

/-- Look up `x` in the graph `g` (junk `∅` if absent). -/
def apZ (g x : V) : V := if h : ∃ y, pair x y ∈ g then h.choose else ∅

/-- `g` is a functional relation (as a set of pairs). -/
def Functional (g : V) : Prop := ∀ x y y', pair x y ∈ g → pair x y' ∈ g → y = y'

theorem apZ_eq {g x y : V} (hg : Functional g) (h : pair x y ∈ g) : apZ g x = y := by
  have he : ∃ y, pair x y ∈ g := ⟨y, h⟩
  rw [apZ, dif_pos he]; exact hg _ _ _ he.choose_spec h

theorem below_apZ {g x : V} (h : ∃ y, pair x y ∈ g) : Below (apZ g x) g := by
  rw [apZ, dif_pos h]; exact (below_pair_right _ _).mem_trans h.choose_spec

/-! ### Graphs over countable types -/

/-- The graph of a function on a countable type. -/
def fnC {α : Type} [Countable α] (F : α → V) : V := range fun x => pair (enc x) (F x)

def apC {α : Type} [Countable α] (g : V) (x : α) : V := apZ g (enc x)

theorem mem_fnC {α : Type} [Countable α] {F : α → V} {z : V} :
    z ∈ fnC F ↔ ∃ x, z = pair (enc x) (F x) := by
  simp [fnC, eq_comm]

theorem fnC_functional {α : Type} [Countable α] (F : α → V) : Functional (fnC F) := by
  intro x y y' h h'
  obtain ⟨a, ha⟩ := mem_fnC.1 h
  obtain ⟨a', ha'⟩ := mem_fnC.1 h'
  rw [pair_inj'] at ha ha'
  rw [ha.1] at ha'
  rw [ha.2, ha'.2, enc_injective ha'.1.symm]

@[simp] theorem apC_fnC {α : Type} [Countable α] (F : α → V) (x : α) : apC (fnC F) x = F x :=
  apZ_eq (fnC_functional F) (mem_fnC.2 ⟨x, rfl⟩)

theorem fnC_injective {α : Type} [Countable α] : Function.Injective (fnC : (α → V) → V) := by
  intro F G h; funext x; rw [← apC_fnC F x, h, apC_fnC]

@[simp] theorem fnC_inj {α : Type} [Countable α] {F G : α → V} : fnC F = fnC G ↔ F = G :=
  fnC_injective.eq_iff

theorem below_fnC {α : Type} [Countable α] (F : α → V) (x : α) : Below (F x) (fnC F) :=
  (below_pair_right _ _).mem_trans (mem_fnC.2 ⟨x, rfl⟩)

theorem below_apC_fnC {α : Type} [Countable α] (F : α → V) (x : α) :
    Below (apC (fnC F) x) (fnC F) := by
  rw [apC_fnC]; exact below_fnC F x

/-! ### Graphs over sets -/

/-- The graph of a function on the set `D`. -/
def fnZ (D : V) (F : V → V) : V := range fun x : D => pair x.1 (F x.1)

theorem mem_fnZ {D : V} {F : V → V} {z : V} : z ∈ fnZ D F ↔ ∃ x ∈ D, z = pair x (F x) := by
  simp only [fnZ, mem_range, Subtype.exists]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem fnZ_functional (D : V) (F : V → V) : Functional (fnZ D F) := by
  intro x y y' h h'
  obtain ⟨a, -, ha⟩ := mem_fnZ.1 h
  obtain ⟨a', -, ha'⟩ := mem_fnZ.1 h'
  rw [pair_inj'] at ha ha'
  rw [ha.2, ha'.2, ← ha.1, ← ha'.1]

theorem apZ_fnZ {D : V} (F : V → V) {x : V} (hx : x ∈ D) : apZ (fnZ D F) x = F x :=
  apZ_eq (fnZ_functional D F) (mem_fnZ.2 ⟨x, hx, rfl⟩)

theorem fnZ_congr {D : V} {F G : V → V} (h : ∀ x ∈ D, F x = G x) : fnZ D F = fnZ D G := by
  ext z; simp only [mem_fnZ]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [h x hx]⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [h x hx]⟩

theorem fnZ_eq_iff {D : V} {F G : V → V} : fnZ D F = fnZ D G ↔ ∀ x ∈ D, F x = G x :=
  ⟨fun h x hx => by rw [← apZ_fnZ F hx, h, apZ_fnZ G hx], fnZ_congr⟩

theorem below_apZ_fnZ {D : V} (F : V → V) {x : V} (hx : x ∈ D) : Below (F x) (fnZ D F) := by
  rw [← apZ_fnZ F hx]; exact below_apZ ⟨_, mem_fnZ.2 ⟨x, hx, rfl⟩⟩

theorem fnZ_mem_funs {D R : V} {F : V → V} (h : ∀ x ∈ D, F x ∈ R) : fnZ D F ∈ funs D R := by
  rw [mem_funs]
  refine ⟨fun z hz => ?_, fun x hx => ⟨F x, ?_, fun y hy => ?_⟩⟩
  · obtain ⟨x, hx, rfl⟩ := mem_fnZ.1 hz
    exact pair_mem_prod.2 ⟨hx, h x hx⟩
  · exact mem_fnZ.2 ⟨x, hx, rfl⟩
  · exact (apZ_eq (fnZ_functional D F) hy).symm.trans (apZ_fnZ F hx)

/-- Every function graph in `funs D R` is an `fnZ`. -/
theorem eq_fnZ_of_mem_funs {D R g : V} (hg : g ∈ funs D R) : g = fnZ D (apZ g) := by
  rw [mem_funs] at hg
  obtain ⟨hsub, hfun⟩ := hg
  have hfn : Functional g := by
    intro x y y' h h'
    have hx : x ∈ D := (pair_mem_prod.1 (hsub h)).1
    obtain ⟨z, -, hz⟩ := hfun x hx
    rw [hz y h, hz y' h']
  ext z
  rw [mem_fnZ]
  constructor
  · intro hz
    obtain ⟨x, hx, y, -, rfl⟩ := mem_prod.1 (hsub hz)
    exact ⟨x, hx, by rw [apZ_eq hfn hz]⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, -⟩ := hfun x hx
    rwa [apZ_eq hfn hy]

end

end Model
