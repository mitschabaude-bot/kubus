import Model.Consistency
import KubusCore

/-!
# End to end: whatever the kernel certifies lives in a consistent theory

`checkSig` returns a derivation of `WfSig S` by construction, and `Model.consistent`
validates every rule of the spec in the cubical-sets model.
-/

namespace Model

open KubusCore

/-- If the kernel accepts a signature, no closed term has type `(A : U₀) → A`. -/
theorem kernel_consistent {S : Sig} {h : PLift (WfSig S)} (hk : Kernel.checkSig S = .ok h) (t : Tm) :
    ¬ HasTy S 0 .one [] t (.pi (.univ 0) (.var 0)) :=
  consistent S t (Kernel.checkSig_sound hk)

end Model
