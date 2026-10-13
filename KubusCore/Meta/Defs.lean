import KubusCore.Meta.Cof

/-!
# Metatheory: definitions

Named substitutions used in the rules `elimHcomp` and `transpHcomp`.
-/

namespace KubusCore.Meta

open Tm

/-- `[h/0]` with the other variables lowered (the substitution in `elimHcomp`). -/
def consSub (h : Tm) : Nat → Tm
  | 0 => h
  | j + 1 => var j

/-- Skip interval variable 1 (the substitution in `transpHcomp`). -/
def skip1I : Nat → I
  | 0 => .var 0
  | n + 1 => .var (n + 2)

end KubusCore.Meta
