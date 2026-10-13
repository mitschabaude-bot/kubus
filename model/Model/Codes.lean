import Model.Val

/-!
# Type codes

A type code at stage `m` is a Kripke value whose datum at `(k, f)` describes the type
restricted along `f`, as a type at stage `k`. The datum stores

* the *shape*: a tag and the components (themselves values at stage `k`), so codes are
  intensional (a Π-code records its domain and codomain family; this validates the spec's
  inversion rules for Π, Σ and paths);
* the set of elements at stage `k`;
* the graph of `transp` along the last interval variable (if `k = n + 1`);
* the graph of `hcomp` at stage `k`.

Everything is computed by the constructors from the data of the components, without recursion
on codes, so derived codes (fiber types in Glue, the isEquiv types in the universe's `hcomp`)
can be built freely.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Data layout -/

def quad (s e t h : V) : V := pair s (pair e (pair t h))

variable {k m n : ℕ}

/-- The shape of the code `c` restricted along `f`. -/
def shapeOf (c : V) (f : Hom k m) : V := π1 (dat c k f)
/-- The elements of the code `c` restricted along `f`, at stage `k`. -/
def El (c : V) (f : Hom k m) : V := π1 (π2 (dat c k f))
/-- The graph of `transp` of `c` restricted along `f`, along the last variable. -/
def trG (c : V) (f : Hom k m) : V := π1 (π2 (π2 (dat c k f)))
/-- The graph of `hcomp` of `c` restricted along `f`. -/
def hcG (c : V) (f : Hom k m) : V := π2 (π2 (π2 (dat c k f)))

@[simp] theorem π1_quad (s e t h : V) : π1 (quad s e t h) = s := by simp [quad]
@[simp] theorem π1π2_quad (s e t h : V) : π1 (π2 (quad s e t h)) = e := by simp [quad]
@[simp] theorem π1π2π2_quad (s e t h : V) : π1 (π2 (π2 (quad s e t h))) = t := by simp [quad]
@[simp] theorem π2π2π2_quad (s e t h : V) : π2 (π2 (π2 (quad s e t h))) = h := by simp [quad]

/-! ### Shapes -/

def tEmpty : ℕ := 1
def tPi : ℕ := 2
def tSigma : ℕ := 3
def tPath : ℕ := 4
def tIPi : ℕ := 5
def tUniv : ℕ := 6
def tGlue : ℕ := 7
def tHcompU : ℕ := 8

/-! ### Tubes -/

/-- A tube at stage `k`: values at `(n, h, r)` for `h : Hom n k` and `r : DM n` (the path
direction). Only the values on the face matter. -/
abbrev Tube (k : ℕ) := (n : ℕ) → Hom n k → DM n → V

abbrev TubeDom (k : ℕ) := Σ n : ℕ, Hom n k × DM n

namespace Tube

/-- Forget the values off the face `φ`. -/
def canon (φ : Cof k) (u : Tube k) : Tube k := fun n h r => if (φ.restr h).holds then u n h r else ∅

def restr (u : Tube k) (h : Hom n k) : Tube n := fun n' g r => u n' (h.comp g) r

theorem canon_canon (φ : Cof k) (u : Tube k) : canon φ (canon φ u) = canon φ u := by
  funext n h r; simp only [canon]; split <;> simp_all

end Tube

def tubeZ (φ : Cof k) (u : Tube k) : V :=
  fnC fun x : TubeDom k => Tube.canon φ u x.1 x.2.1 x.2.2

theorem tubeZ_eq_iff {φ : Cof k} {u u' : Tube k} : tubeZ φ u = tubeZ φ u' ↔ Tube.canon φ u = Tube.canon φ u' := by
  constructor
  · intro h; have := fnC_injective h; funext n g r; exact congrFun this ⟨n, g, r⟩
  · intro h; simp only [tubeZ, h]

/-! ### Keys and lookups -/

def hcKey (φ : Cof k) (u : Tube k) (u0 : V) : V := pair (enc φ) (pair (tubeZ φ u) u0)
def trKey (φ : Cof n) (a0 : V) : V := pair (enc φ) a0

/-- `hcomp` in the code `c` restricted along `f`. -/
def hcompAt (c : V) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) : V :=
  apZ (hcG c f) (hcKey φ u u0)

/-- `transp` in the code `c` along the line `f` (direction: the last variable of `n + 1`). -/
def transpAt (c : V) (f : Hom (n + 1) m) (φ : Cof n) (a0 : V) : V :=
  apZ (trG c f) (trKey φ a0)

/-! ### Graph builders -/

/-- Inputs of `hcomp` at stage `k` for element sets `E`: a face, a tube (values in `E` or `∅`),
and a base. -/
abbrev HcIn (k : ℕ) (E : (n : ℕ) → Hom n k → V) :=
  (_ : Cof k) × ((y : TubeDom k) → ↥(insert ∅ (E y.1 y.2.1))) × ↥(E k (Hom.id k))

def HcIn.tube {E : (n : ℕ) → Hom n k → V} (x : HcIn k E) : Tube k := fun n h r => (x.2.1 ⟨n, h, r⟩).1

/-- The graph of an `hcomp` operation `F`, on inputs with tube values in `E`. -/
def hcGraph (k : ℕ) (E : (n : ℕ) → Hom n k → V) (F : Cof k → Tube k → V → V) : V :=
  range fun x : HcIn k E => pair (hcKey x.1 x.tube x.2.2.1) (F x.1 (Tube.canon x.1 x.tube) x.2.2.1)

/-- The graph of a `transp` operation `F`, on bases in `E0`. -/
def trGraph (n : ℕ) (E0 : V) (F : Cof n → V → V) : V :=
  range fun x : Cof n × ↥E0 => pair (trKey x.1 x.2.1) (F x.1 x.2.1)

theorem hcGraph_functional (E : (n : ℕ) → Hom n k → V) (F : Cof k → Tube k → V → V) :
    Functional (hcGraph k E F) := by
  intro z y y' h h'
  simp only [hcGraph, mem_range] at h h'
  obtain ⟨x, hx⟩ := h; obtain ⟨x', hx'⟩ := h'
  rw [pair_inj'] at hx hx'
  obtain ⟨hk, rfl⟩ := hx; obtain ⟨hk', rfl⟩ := hx'
  rw [← hk'] at hk
  simp only [hcKey, pair_inj', enc_inj] at hk
  obtain ⟨h1, h2, h3⟩ := hk
  obtain ⟨φ, t, b⟩ := x; obtain ⟨φ', t', b'⟩ := x'
  simp only at h1 h2 h3; subst h1
  rw [tubeZ_eq_iff] at h2
  simp only [h2, h3]

theorem apZ_hcGraph {E : (n : ℕ) → Hom n k → V} (F : Cof k → Tube k → V → V) {φ : Cof k}
    {u : Tube k} {u0 : V} (hu : ∀ n (h : Hom n k) r, (φ.restr h).holds → u n h r ∈ E n h)
    (hu0 : u0 ∈ E k (Hom.id k)) :
    apZ (hcGraph k E F) (hcKey φ u u0) = F φ (Tube.canon φ u) u0 := by
  apply apZ_eq (hcGraph_functional E F)
  simp only [hcGraph, mem_range]
  let t : (y : TubeDom k) → ↥(insert ∅ (E y.1 y.2.1)) := fun y =>
    ⟨Tube.canon φ u y.1 y.2.1 y.2.2, by
      simp only [Tube.canon]; split
      · exact mem_insert_of_mem _ (hu _ _ _ ‹_›)
      · exact mem_insert _ _⟩
  refine ⟨⟨φ, t, ⟨u0, hu0⟩⟩, ?_⟩
  have ht : HcIn.tube ⟨φ, t, ⟨u0, hu0⟩⟩ = Tube.canon φ u := rfl
  rw [ht, Tube.canon_canon]
  simp only [hcKey, pair_inj', true_and, and_true]
  rw [tubeZ_eq_iff, Tube.canon_canon]

theorem trGraph_functional (E0 : V) (F : Cof n → V → V) : Functional (trGraph n E0 F) := by
  intro z y y' h h'
  simp only [trGraph, mem_range] at h h'
  obtain ⟨x, hx⟩ := h; obtain ⟨x', hx'⟩ := h'
  rw [pair_inj'] at hx hx'
  obtain ⟨hk, rfl⟩ := hx; obtain ⟨hk', rfl⟩ := hx'
  rw [← hk'] at hk
  simp only [trKey, pair_inj', enc_inj] at hk
  rw [hk.1, hk.2]

theorem apZ_trGraph {E0 : V} (F : Cof n → V → V) {φ : Cof n} {a0 : V} (ha : a0 ∈ E0) :
    apZ (trGraph n E0 F) (trKey φ a0) = F φ a0 :=
  apZ_eq (trGraph_functional E0 F) (by simp only [trGraph, mem_range]; exact ⟨⟨φ, a0, ha⟩, rfl⟩)

/-! ### Codes from stage-local data -/

/-- A code from its datum at each stage, given as a function of the restricted components. -/
def mkCode (m : ℕ) (D : (k : ℕ) → Hom k m → V) : V := mkKV m D

@[simp] theorem El_mkKV (D : (k : ℕ) → Hom k m → V) (f : Hom k m) :
    El (mkKV m D) f = π1 (π2 (D k f)) := by simp [El]

@[simp] theorem shapeOf_mkKV (D : (k : ℕ) → Hom k m → V) (f : Hom k m) :
    shapeOf (mkKV m D) f = π1 (D k f) := by simp [shapeOf]

@[simp] theorem trG_mkKV (D : (k : ℕ) → Hom k m → V) (f : Hom k m) :
    trG (mkKV m D) f = π1 (π2 (π2 (D k f))) := by simp [trG]

@[simp] theorem hcG_mkKV (D : (k : ℕ) → Hom k m → V) (f : Hom k m) :
    hcG (mkKV m D) f = π2 (π2 (π2 (D k f))) := by simp [hcG]

theorem El_res (c : V) (f : Hom k m) (g : Hom n k) : El (res f c) g = El c (f.comp g) := by
  simp [El]

theorem trG_res (c : V) (f : Hom k m) (g : Hom n k) : trG (res f c) g = trG c (f.comp g) := by
  simp [trG]

theorem hcG_res (c : V) (f : Hom k m) (g : Hom n k) : hcG (res f c) g = hcG c (f.comp g) := by
  simp [hcG]

theorem shapeOf_res (c : V) (f : Hom k m) (g : Hom n k) :
    shapeOf (res f c) g = shapeOf c (f.comp g) := by
  simp [shapeOf]

end

end Model
