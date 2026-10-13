import Model.Cube
import Model.Enc
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Powerset

/-!
# Kripke values

A value at stage `m` is the graph of a function on `Dom m = Σ k, Hom k m`: its datum at
`(k, f)` describes the restriction of the value along `f`, as an object at stage `k`. With this
representation restriction is uniform reindexing (`res`), independent of types, and strictly
functorial. Glue types and Glue elements reduce on faces automatically: their data at maps into
the face are simply the data of the reduct.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

instance (m : ℕ) : Finite (DM m) := Finite.of_injective DM.fn fun _ _ h => DM.ext h
instance (m : ℕ) : Countable (DM m) := Finite.to_countable
instance (k m : ℕ) : Finite (Hom k m) := by unfold Hom; infer_instance
instance (k m : ℕ) : Countable (Hom k m) := Finite.to_countable
instance (m : ℕ) : Finite (Pt m) := by unfold Pt; infer_instance
instance (m : ℕ) : Countable (Set (Pt m)) := Finite.to_countable

/-- Stages below `m`. -/
abbrev Dom (m : ℕ) := Σ k : ℕ, Hom k m

/-! ### Pairs -/

def π1 (z : V) : V := if h : ∃ a b, z = pair a b then h.choose else ∅
def π2 (z : V) : V := if h : ∃ a b, z = pair a b then h.choose_spec.choose else ∅

@[simp] theorem π1_pair (a b : V) : π1 (pair a b) = a := by
  have h : ∃ a' b', pair a b = pair a' b' := ⟨a, b, rfl⟩
  rw [π1, dif_pos h]
  exact ((pair_inj'.1 h.choose_spec.choose_spec).1).symm

@[simp] theorem π2_pair (a b : V) : π2 (pair a b) = b := by
  have h : ∃ a' b', pair a b = pair a' b' := ⟨a, b, rfl⟩
  rw [π2, dif_pos h]
  exact ((pair_inj'.1 h.choose_spec.choose_spec).2).symm

/-! ### Kripke values -/

variable {k m n : ℕ}

/-- The datum of `v` at `(k, f)`. -/
def dat (v : V) (k : ℕ) (f : Hom k m) : V := apC v (⟨k, f⟩ : Dom m)

/-- The datum at the identity: the value "itself" at its own stage. -/
def here (m : ℕ) (v : V) : V := dat v m (Hom.id m)

/-- A Kripke value from its data. -/
def mkKV (m : ℕ) (F : (k : ℕ) → Hom k m → V) : V := fnC fun x : Dom m => F x.1 x.2

@[simp] theorem dat_mkKV (F : (k : ℕ) → Hom k m → V) (f : Hom k m) : dat (mkKV m F) k f = F k f :=
  apC_fnC _ _

theorem mkKV_inj {F G : (k : ℕ) → Hom k m → V} : mkKV m F = mkKV m G ↔ F = G := by
  constructor
  · intro h; funext k f; rw [← dat_mkKV F f, h, dat_mkKV]
  · rintro rfl; rfl

/-- `v` is a Kripke value at stage `m`. -/
def IsKV (m : ℕ) (v : V) : Prop := ∃ F : (k : ℕ) → Hom k m → V, v = mkKV m F

theorem IsKV.eq {v : V} (h : IsKV m v) : v = mkKV m fun k f => dat v k f := by
  obtain ⟨F, rfl⟩ := h; simp

theorem IsKV.ext {v w : V} (hv : IsKV m v) (hw : IsKV m w)
    (h : ∀ k (f : Hom k m), dat v k f = dat w k f) : v = w := by
  rw [hv.eq, hw.eq]; congr; funext k f; exact h k f

/-- Restriction along a cube map: reindexing. -/
def res (f : Hom k m) (v : V) : V := mkKV k fun n g => dat v n (f.comp g)

@[simp] theorem dat_res (f : Hom k m) (v : V) (g : Hom n k) : dat (res f v) n g = dat v n (f.comp g) :=
  dat_mkKV _ _

theorem isKV_res (f : Hom k m) (v : V) : IsKV k (res f v) := ⟨_, rfl⟩

theorem isKV_mkKV (F : (k : ℕ) → Hom k m → V) : IsKV m (mkKV m F) := ⟨_, rfl⟩

theorem res_res (f : Hom k m) (g : Hom n k) (v : V) : res g (res f v) = res (f.comp g) v := by
  simp [res, Hom.comp_assoc]

theorem res_id {v : V} (h : IsKV m v) : res (Hom.id m) v = v := by
  rw [h.eq]; simp [res]

@[simp] theorem res_mkKV (f : Hom k m) (F : (k : ℕ) → Hom k m → V) :
    res f (mkKV m F) = mkKV k fun n g => F n (f.comp g) := by
  simp [res]

theorem here_res (f : Hom k m) (v : V) : here k (res f v) = dat v k f := by
  simp [here]

@[simp] theorem here_mkKV (F : (k : ℕ) → Hom k m → V) : here m (mkKV m F) = F m (Hom.id m) :=
  dat_mkKV _ _

/-- Data are below the value. -/
theorem below_dat_mkKV (F : (k : ℕ) → Hom k m → V) (f : Hom k m) : Below (F k f) (mkKV m F) :=
  below_fnC (fun x : Dom m => F x.1 x.2) ⟨k, f⟩

theorem below_dat {v : V} (hv : IsKV m v) (f : Hom k m) : Below (dat v k f) v := by
  rw [hv.eq]; simp only [dat_mkKV]; exact below_dat_mkKV _ f

end

end Model
