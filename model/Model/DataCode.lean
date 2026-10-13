import Model.Kan

/-!
# Inductive types: elements

The elements of an inductive type are Kripke values of two kinds:

* constructor values `conV ctors n c args rs`: at the maps into a boundary face of `c` their
  datum is the datum of the boundary element (evaluated from the arguments, `evalBnd`), so they
  reduce on their boundary automatically (like Glue elements); elsewhere the datum records the
  constructor, the restricted arguments and the restricted interval arguments;
* formal compositions `hcV n φ u a`: on `φ` their datum is the datum of the tube's end, elsewhere
  it records the face, the tube and the base.

Both are defined without reference to types; the arguments' types enter only the element
predicate. Constructor values do not record the parameters (parameters may be large).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

def tCon : ℕ := 9
def tHc : ℕ := 10
def tData : ℕ := 11

/-- The junk Kripke value. -/
def junkV (n : ℕ) : V := mkKV n fun _ _ => ∅

/-- Lists of values as nested pairs. -/
def vlist : List V → V
  | [] => ∅
  | a :: as => ZFSet.pair a (vlist as)

/-- The interval environment of a constructor's interval arguments (the last one is variable 0). -/
def renv (rs : List (DM n)) : IEnv n := fun i => rs.reverse.getD i (DM.zero n)

mutual
/-- The value of a simple boundary element, given the constructors before it (`conF`), the
arguments (oldest first) and the interval arguments. -/
def evalBnd (conF : ℕ → List V → List (DM n) → V) (args : List V) (rs : List (DM n)) : Tm → V
  | .var j => res (Hom.id n) (args.reverse.getD j ∅)
  | .con _ c' _ as rs' => conF c' (evalBndList conF args rs as) (rs'.map (ival (renv rs)))
  | _ => junkV n
def evalBndList (conF : ℕ → List V → List (DM n) → V) (args : List V) (rs : List (DM n)) : Tm → List V
  | .tcons a as => evalBnd conF args rs a :: evalBndList conF args rs as
  | _ => []
end

/-- The first boundary clause of `C` that holds at `f`, for interval arguments `rs`. -/
def bndAtMap (C : Ctor) (rs : List (DM n)) (f : Hom k n) : Option (I × Tm) :=
  C.bnd.find? fun cl => decide ((ival (renv rs) cl.1).restr f).holds

/-- Constructor values. -/
def conV (ctors : List Ctor) (n : ℕ) (c : ℕ) (args : List V) (rs : List (DM n)) : V :=
  mkKV n fun k f =>
    match bndAtMap (ctors.getD c default) rs f with
    | some (_, b) => dat (evalBnd (fun c' as rs' => if _ : c' < c then conV ctors n c' as rs' else junkV n) args rs b) k f
    | none => tagZ tCon (ZFSet.pair (natZ c) (ZFSet.pair (vlist (args.map (res f))) (vlist (rs.map fun r => enc (r.restr f)))))
termination_by c
decreasing_by assumption

/-- Formal compositions. -/
def hcV (n : ℕ) (φ : Cof n) (u : Tube n) (a : V) : V :=
  mkKV n fun k f =>
    if (φ.restr f).holds then here k (u k f (DM.one k))
    else tagZ tHc (ZFSet.pair (enc (φ.restr f)) (ZFSet.pair (tubeZ (φ.restr f) (u.restr f)) (res f a)))

/-! ### Basic properties -/

theorem isKV_junkV : IsKV n (junkV n) := isKV_mkKV _

theorem res_junkV (h : Hom k n) : res h (junkV n) = junkV k := by
  simp [junkV]

theorem isKV_conV (ctors : List Ctor) (c : ℕ) (args : List V) (rs : List (DM n)) :
    IsKV n (conV ctors n c args rs) := by
  rw [conV]; exact isKV_mkKV _

theorem isKV_hcV (φ : Cof n) (u : Tube n) (a : V) : IsKV n (hcV n φ u a) := isKV_mkKV _

theorem renv_restr (rs : List (DM n)) (h : Hom k n) : renv (rs.map (·.restr h)) = (renv rs).restr h := by
  funext i
  simp only [renv, IEnv.restr, ← List.map_reverse, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases rs.reverse[i]? <;> simp [DM.zero_restr]

theorem bndAtMap_restr (C : Ctor) (rs : List (DM n)) (h : Hom k n) (g : Hom m k) :
    bndAtMap C (rs.map (·.restr h)) g = bndAtMap C rs (h.comp g) := by
  simp only [bndAtMap, renv_restr, ival.restr, DM.restr_restr]

theorem dat_empty0 (f : Hom k n) : dat (∅ : V) k f = ∅ := by
  simp only [dat, apC, apZ]; rw [dif_neg]; rintro ⟨y, hy⟩; exact ZFSet.notMem_empty _ hy

theorem ival_renv_restr (rs : List (DM n)) (h : Hom k n) (r : I) :
    (ival (renv rs) r).restr h = ival (renv (rs.map (·.restr h))) r := by
  rw [renv_restr, ival.restr]

theorem res_id_res (h : Hom k n) (x : V) : res h (res (Hom.id n) x) = res (Hom.id k) (res h x) := by
  rw [res_res, res_res, Hom.id_comp, Hom.comp_id]

theorem res_evalBnd {conF : ℕ → List V → List (DM n) → V} {conF' : ℕ → List V → List (DM k) → V} (h : Hom k n)
    (hc : ∀ c as rs', res h (conF c as rs') = conF' c (as.map (res h)) (rs'.map (·.restr h)))
    (args : List V) (rs : List (DM n)) : ∀ b : Tm,
    res h (evalBnd conF args rs b) = evalBnd conF' (args.map (res h)) (rs.map (·.restr h)) b ∧
      (evalBndList conF args rs b).map (res h) = evalBndList conF' (args.map (res h)) (rs.map (·.restr h)) b := by
  intro b
  induction b with
  | var j =>
    refine ⟨?_, by simp [evalBndList]⟩
    simp only [evalBnd]
    rw [res_id_res, ← List.map_reverse, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases args.reverse[j]? with
    | none => simp [res, dat_empty0]
    | some x => rfl
  | con d c ps as rs' _ ihas =>
    refine ⟨?_, by simp [evalBndList]⟩
    simp only [evalBnd]
    rw [hc, ihas.2, List.map_map]
    congr 1
    exact List.map_congr_left fun r _ => ival_renv_restr rs h r
  | tcons a as iha ihas =>
    refine ⟨by simp [evalBnd, res_junkV], ?_⟩
    simp only [evalBndList, List.map_cons, iha.1, ihas.2]
  | _ => exact ⟨by simp [evalBnd, res_junkV], by simp [evalBndList]⟩

theorem conV_eq (ctors : List Ctor) (c : ℕ) (args : List V) (rs : List (DM n)) :
    conV ctors n c args rs = mkKV n fun k f =>
      match bndAtMap (ctors.getD c default) rs f with
      | some (_, b) => dat (evalBnd (fun c' as rs' => if _ : c' < c then conV ctors n c' as rs' else junkV n)
          args rs b) k f
      | none => tagZ tCon (ZFSet.pair (natZ c) (ZFSet.pair (vlist (args.map (res f)))
          (vlist (rs.map fun r => enc (r.restr f))))) := by
  rw [conV]

theorem res_conV (ctors : List Ctor) : ∀ (c : ℕ) {n k : ℕ} (args : List V) (rs : List (DM n)) (h : Hom k n),
    res h (conV ctors n c args rs) = conV ctors k c (args.map (res h)) (rs.map (·.restr h)) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro n k args rs h
    rw [conV_eq, conV_eq, res_mkKV]
    congr 1; funext k' g
    rw [bndAtMap_restr]
    split
    · rename_i ψ b _
      have := (res_evalBnd h (conF := fun c' as rs' => if _ : c' < c then conV ctors n c' as rs' else junkV n)
        (conF' := fun c' as rs' => if _ : c' < c then conV ctors k c' as rs' else junkV k)
        (fun c' as rs' => by
          by_cases hc' : c' < c
          · simp only [dif_pos hc']; exact ih c' hc' as rs' h
          · simp only [dif_neg hc']; exact res_junkV h) args rs b).1
      rw [← this, dat_res]
    · simp only [List.map_map, Function.comp_def, res_res, DM.restr_restr]

theorem res_hcV (φ : Cof n) (u : Tube n) (a : V) (h : Hom k n) :
    res h (hcV n φ u a) = hcV k (φ.restr h) (u.restr h) (res h a) := by
  simp only [hcV, res_mkKV, Cof.restr_restr, res_res]
  rfl

end

end Model
