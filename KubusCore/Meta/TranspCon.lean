import KubusCore.Meta.DataTele
import KubusCore.Meta.ConBnd
import KubusCore.Meta.KanTransp

/-!
# Metatheory: the contractum of `transpCon` is typed

The argument types along the parameter line are instances of the point argument types over
`D.pointCtx` (typed in the prefix signature by `DataDecl.Wf`), under the substitution sending
the parameters to the line and the earlier point arguments to their transport fillers.
Functionality of substitution relates the instances at the ends of the line and on `φ`
(parameters: `EqTm0.dataInjAt`).
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## The fillers of `transpTele` -/

/-- The transport fillers of the first `k` arguments (in order). -/
def tFills (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) : Nat → List Tm
  | 0 => []
  | k + 1 => tFills A psL φ as k ++
      [transpFill ((A k).substList ((tFills A psL φ as k).reverse ++ psL.reverse)) φ (as.getD k .abort)]

/-- The type line of argument `k`. -/
def tLine (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) (k : Nat) : Tm :=
  (A k).substList ((tFills A psL φ as k).reverse ++ psL.reverse)

theorem tFills_succ (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) (k : Nat) :
    tFills A psL φ as (k + 1) = tFills A psL φ as k ++ [transpFill (tLine A psL φ as k) φ (as.getD k .abort)] :=
  rfl

theorem tFills_length (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) :
    ∀ k, (tFills A psL φ as k).length = k
  | 0 => rfl
  | k + 1 => by rw [tFills_succ, List.length_append, tFills_length A psL φ as k]; rfl

theorem tFills_take (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) (k : Nat) :
    ∀ m, (tFills A psL φ as (k + m)).take k = tFills A psL φ as k
  | 0 => by rw [Nat.add_zero, List.take_of_length_le (by rw [tFills_length]; exact Nat.le_refl _)]
  | m + 1 => by
    rw [← Nat.add_assoc, tFills_succ, List.take_append_of_le_length (by rw [tFills_length]; omega)]
    exact tFills_take A psL φ as k m

theorem tFills_get (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) {k n : Nat} (h : k < n) :
    (tFills A psL φ as n).getD k .abort = transpFill (tLine A psL φ as k) φ (as.getD k .abort) := by
  have := tFills_take A psL φ as (k + 1) (n - (k + 1))
  rw [show k + 1 + (n - (k + 1)) = n by omega, tFills_succ] at this
  have hl := tFills_length A psL φ as n
  rw [List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt (j := k + 1) (by omega), this,
    List.getElem?_append_right (by rw [tFills_length]; exact Nat.le_refl _), tFills_length]
  simp

theorem transpTele_eq (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) :
    ∀ (rest : List Tm) (k : Nat), as.drop k = rest →
    Tm.transpTele A psL φ k (tFills A psL φ as k).reverse rest =
      (List.range' k rest.length).map fun j => transp (tLine A psL φ as j) φ (as.getD j .abort)
  | [], _, _ => rfl
  | a :: rest, k, h => by
    have ha : as.getD k .abort = a := by
      have := congrArg (fun l => l[0]?) h
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      rw [List.getD_eq_getElem?_getD, this]; rfl
    have h1 : as.drop (k + 1) = rest := by
      rw [← List.drop_drop, h]; rfl
    simp only [Tm.transpTele, List.length_cons, List.range'_succ, List.map_cons]
    rw [ha]
    congr 1
    have := transpTele_eq A psL φ as rest (k + 1) h1
    rw [tFills_succ, List.reverse_append, ha] at this
    exact this

end KubusCore.Meta
