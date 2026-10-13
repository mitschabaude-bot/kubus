import Model.DataFibFull

/-!
# Inductive types: well-formedness is stable under restriction
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem shapeOf_dataC (Θ : SData m) : shapeOf (dataC Θ) (Hom.id m) =
    tagZ tData (ZFSet.pair (natZ Θ.idx) (ZFSet.pair (Θ.pv m (Hom.id m)) (shapeV (Θ.restr (Hom.id m))))) := by
  rw [dataC, shapeOf_mkKV, dataDatum, π1_quad]
  simp [SData.restr]

end

end Model
