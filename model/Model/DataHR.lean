import Model.DataTrFib

/-!
# Inductive types without path constructors: componentwise composition

`hcD` composes componentwise (`HR`) when the type has no path constructors. Here: existence,
uniqueness and the Kan laws of `HR`, i.e. the composition fields of `fib_dataC`.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

section

variable {Θ : SData m} (hΘ : Θ.Good) (hH : Θ.hit = false)
include hΘ hH

variable {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V}

theorem dataC_hcMem_nonHIT (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f) (hu : TubeOK (dataC Θ) f φ u u0) :
    hcompAt (dataC Θ) f φ u u0 ∈ El (dataC Θ) f := by
  sorry

theorem dataC_hcFace_nonHIT (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f) (hu : TubeOK (dataC Θ) f φ u u0)
    (hh : φ.holds) : hcompAt (dataC Θ) f φ u u0 = u k (Hom.id k) (DM.one k) := by
  sorry

theorem dataC_hcRes_nonHIT (hφ : φ.IsCof) (hu0 : u0 ∈ El (dataC Θ) f)
    (hu : TubeOK (dataC Θ) f φ u u0) (n : ℕ) (h : Hom n k) :
    res h (hcompAt (dataC Θ) f φ u u0) =
      hcompAt (dataC Θ) (f.comp h) (φ.restr h) (u.restr h) (res h u0) := by
  sorry

end

end

end Model
