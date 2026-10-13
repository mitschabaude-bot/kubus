import Model.GlueFib
import Model.EquivCode
import Model.CofForall
import Model.CompFill

/-!
# Transport in Glue types

The model's transport along a line of Glue types `i ↦ Glue A(i) [φ(i) ↦ (T(i), e(i))]` (at stage
`n + 1`, `i` the last variable) is the semantic reading of the spec's `Tm.transpGlue` (after
Coquand–Huber–Mörtberg):

* `a0 = unglue φ(0) e(0) u0`, and the tube `i ↦ unglue φ(i) e(i) u0` on `ψ`;
* `a1' = comp (i. A) [ψ ↦ unglue u0] a0`;
* on `δ = ∀ i. φ`: `t1' = transp (i. T) ψ u0` and a path `ω` in `A(1)` from `e(1).1 t1'` to `a1'`;
* on `φ(1)`: `ext`, the extension of the partial element `[δ ↦ (t1', ω), ψ ↦ (u0, refl)]` of the
  fiber of `e(1).1` over `a1'`, by contractibility (`hcomp` in the fiber from the center);
* `a1 = hcomp A(1) [φ(1) ↦ (snd ext)(~j), ψ ↦ a1'] a1'`, and the result `glue [φ(1) ↦ fst ext] a1`.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}


end

end Model
