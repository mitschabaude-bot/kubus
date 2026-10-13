import Model.EndToEnd
import KubusCore.Meta

/-!
# Consistency of the minimal (textbook) judgments

The trusted statement: the minimal judgments `HasTy0` (`KubusCore/Meta/Minimal.lean`, the spec
without primitive structural, presupposition and inversion rules) derive no closed term of
`(A : U₀) → A` over a signature well-formed in their own sense (`WfSig0`), nor over any
signature the kernel accepts.
-/

namespace Model

open KubusCore KubusCore.Meta

theorem consistent0 : Consistent0 := consistent0_of consistent

/-- If the kernel accepts a signature, the minimal judgments derive no closed term of
`(A : U₀) → A` over it. -/
theorem kernel_consistent0 {S : Sig} {h : PLift (WfSig S)} (hk : Kernel.checkSig S = .ok h) (t : Tm) :
    ¬ HasTy0 S 0 .one [] t (.pi (.univ 0) (.var 0)) :=
  no_bot0_of consistent (Kernel.checkSig_sound hk) t

end Model
