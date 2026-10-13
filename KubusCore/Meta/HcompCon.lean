import KubusCore.Meta.TranspCon

/-!
# Metatheory: typing the contractum of `hcompCon`

Composition in an inductive type without path constructors, componentwise (`Tm.hcompTele`):
recursive arguments by `hcomp`/`hfill` in the inductive type, point arguments by `comp`/`fill`
along their type lines, which are typed by the point argument clause of `DataDecl.Wf` over the
prefix signature (P11), carried to `S` by `htr`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## The fillers of `hcompTele` -/

/-- The fillers of the first `k` arguments (in order). -/
def hFills (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) : Nat → List Tm
  | 0 => []
  | k + 1 => hFills C A dT psL φ us as k ++
      [if C.isRec k then hfill dT φ (us.getD k .abort) (as.getD k .abort)
       else fill ((A k).substList ((hFills C A dT psL φ us as k).reverse ++ psL.reverse)) φ
         (us.getD k .abort) (as.getD k .abort)]

/-- The type line of (point) argument `k`. -/
def hLine (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) (k : Nat) : Tm :=
  (A k).substList ((hFills C A dT psL φ us as k).reverse ++ psL.reverse)

/-- The filler of argument `k`. -/
def hFill (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) (k : Nat) : Tm :=
  if C.isRec k then hfill dT φ (us.getD k .abort) (as.getD k .abort)
  else fill (hLine C A dT psL φ us as k) φ (us.getD k .abort) (as.getD k .abort)

/-- The composite of argument `k`. -/
def hOut (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) (k : Nat) : Tm :=
  if C.isRec k then hcomp dT φ (us.getD k .abort) (as.getD k .abort)
  else comp (hLine C A dT psL φ us as k) φ (us.getD k .abort) (as.getD k .abort)

section
variable (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm)

theorem hFills_succ (k : Nat) :
    hFills C A dT psL φ us as (k + 1) = hFills C A dT psL φ us as k ++ [hFill C A dT psL φ us as k] :=
  rfl

theorem hFills_length : ∀ k, (hFills C A dT psL φ us as k).length = k
  | 0 => rfl
  | k + 1 => by rw [hFills_succ, List.length_append, hFills_length k]; rfl

theorem hFills_take (k : Nat) :
    ∀ m, (hFills C A dT psL φ us as (k + m)).take k = hFills C A dT psL φ us as k
  | 0 => by rw [Nat.add_zero, List.take_of_length_le (by rw [hFills_length]; exact Nat.le_refl _)]
  | m + 1 => by
    rw [← Nat.add_assoc, hFills_succ, List.take_append_of_le_length (by rw [hFills_length]; omega)]
    exact hFills_take k m

theorem hFills_get {k n : Nat} (h : k < n) :
    (hFills C A dT psL φ us as n).getD k .abort = hFill C A dT psL φ us as k := by
  have := hFills_take C A dT psL φ us as (k + 1) (n - (k + 1))
  rw [show k + 1 + (n - (k + 1)) = n by omega, hFills_succ] at this
  have hl := hFills_length C A dT psL φ us as n
  rw [List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt (j := k + 1) (by omega), this,
    List.getElem?_append_right (by rw [hFills_length]; exact Nat.le_refl _), hFills_length]
  simp

theorem hcompTele_eq :
    ∀ (us' as' : List Tm) (k : Nat), us.drop k = us' → as.drop k = as' → us'.length = as'.length →
    Tm.hcompTele C A dT psL φ k (hFills C A dT psL φ us as k).reverse us' as' =
      (List.range' k as'.length).map (hOut C A dT psL φ us as)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hl | _ :: _, [], _, _, _, hl => by simp at hl
  | u :: us', a :: as', k, hu, ha, hl => by
    have hu0 : us.getD k .abort = u := by
      have := congrArg (fun l => l[0]?) hu
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      rw [List.getD_eq_getElem?_getD, this]; rfl
    have ha0 : as.getD k .abort = a := by
      have := congrArg (fun l => l[0]?) ha
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      rw [List.getD_eq_getElem?_getD, this]; rfl
    have hu1 : us.drop (k + 1) = us' := by rw [← List.drop_drop, hu]; rfl
    have ha1 : as.drop (k + 1) = as' := by rw [← List.drop_drop, ha]; rfl
    have ih := hcompTele_eq us' as' (k + 1) hu1 ha1 (by simpa using hl)
    rw [hFills_succ, List.reverse_append] at ih
    simp only [List.length_cons, List.range'_succ, List.map_cons]
    unfold hFill hOut hLine at *
    rw [hu0, ha0] at ih ⊢
    cases hr : C.isRec k <;> simp only [Tm.hcompTele, hr, if_true, if_false, Bool.false_eq_true] <;>
      simp only [hr, if_true, if_false, Bool.false_eq_true, List.reverse_cons, List.reverse_nil, List.nil_append] at ih <;>
      exact congrArg _ ih

end
end KubusCore.Meta
