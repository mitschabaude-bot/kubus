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

theorem hcV_congr {φ : Cof n} {u u' : Tube n} (a : V)
    (h : ∀ n' (h : Hom n' n) r, (φ.restr h).holds → u n' h r = u' n' h r) : hcV n φ u a = hcV n φ u' a := by
  unfold hcV
  congr 1; funext k f
  split
  · rw [h k f _ ‹_›]
  · congr 3
    rw [tubeZ_eq_iff]
    funext n' g r
    simp only [Tube.canon, Tube.restr]
    split
    · rw [Cof.restr_restr] at *; rw [h _ _ _ ‹_›]
    · rfl

/-! ### Semantic inductive types -/

/-- An inductive type at stage `m` (at some parameters): the constructors (from the declaration)
and the types of the point arguments, given at all restrictions and as functions of the earlier
arguments (oldest first). -/
structure SData (m : ℕ) where
  ctors : List Ctor
  params : Bool
  ty : ℕ → ℕ → (n : ℕ) → Hom n m → List V → V
  /-- The index of the inductive type in the signature (recorded in its code). -/
  idx : ℕ
  /-- The parameter values, at all restrictions (recorded in its code). -/
  pv : (n : ℕ) → Hom n m → V
  /-- For each parameter, the code of its type, or its value if its type is a universe (tagged), at
  all restrictions (recorded in its code). -/
  pt : (n : ℕ) → Hom n m → V
  /-- Whether it is a higher inductive type (only these have formal compositions). -/
  hit : Bool

/-- Restriction of a semantic inductive type. -/
def SData.restr (Θ : SData m) (h : Hom k m) : SData k :=
  { Θ with
    ty := fun c j n g pre => Θ.ty c j n (h.comp g) pre
    pv := fun n g => Θ.pv n (h.comp g)
    pt := fun n g => Θ.pt n (h.comp g) }

/-- The elements of an inductive type, at the restriction `g` of its stage: the least set of
Kripke values closed under the constructors (with typed arguments) and formal composition.
Closure under restriction is a lemma (`DElem.res`), for argument types that are natural. -/
inductive DElem (Θ : SData m) : (n : ℕ) → Hom n m → V → Prop
  | con {n : ℕ} {g : Hom n m} {c : ℕ} {C : Ctor} {args : List V} {rs : List (DM n)} :
      Θ.ctors[c]? = some C → args.length = C.args.length → rs.length = C.dims →
      (∀ j a, args[j]? = some a → C.isRec j = true → DElem Θ n g a) →
      (∀ j a, args[j]? = some a → C.isRec j = false → a ∈ El (Θ.ty c j n g (args.take j)) (Hom.id n)) →
      DElem Θ n g (conV Θ.ctors n c args rs)
  | hcomp {n : ℕ} {g : Hom n m} {φ : Cof n} {u : Tube n} {a : V} : Θ.hit = true → φ.IsCof → DElem Θ n g a →
      (∀ n' (h : Hom n' n) r, (φ.restr h).holds → DElem Θ n' (g.comp h) (u n' h r)) →
      (∀ n' (h : Hom n' n) r, (φ.restr h).holds → ∀ n'' (h' : Hom n'' n'),
        res h' (u n' h r) = u n'' (h.comp h') (r.restr h')) →
      (∀ n' (h : Hom n' n), (φ.restr h).holds → u n' h (DM.zero n') = res h a) →
      DElem Θ n g (hcV n φ u a)

theorem DElem.kv {Θ : SData m} {n : ℕ} {g : Hom n m} {v : V} (h : DElem Θ n g v) : IsKV n v := by
  cases h with
  | con => exact isKV_conV _ _ _ _
  | hcomp => exact isKV_hcV _ _ _

/-- The point arguments in `pre` (earlier arguments of constructor `c`, oldest first) have
their types. -/
def SData.PtValid (Θ : SData m) (c n : ℕ) (g : Hom n m) (pre : List V) : Prop :=
  ∀ i (hi : i < pre.length), (Θ.ctors.getD c default).isRec i = false →
    pre[i] ∈ El (Θ.ty c i n g (pre.take i)) (Hom.id n)

/-- The argument types are natural: their elements restrict to elements of the restricted
types at the restricted earlier arguments. -/
def SData.ResClosed (Θ : SData m) : Prop :=
  ∀ c j n (g : Hom n m) pre a, Θ.PtValid c n g pre → a ∈ El (Θ.ty c j n g pre) (Hom.id n) →
    ∀ n' (h : Hom n' n), res h a ∈ El (Θ.ty c j n' (g.comp h) (pre.map (res h))) (Hom.id n')

theorem SData.ptValid_take {Θ : SData m} {c : ℕ} {C : Ctor} (hC : Θ.ctors[c]? = some C) {n : ℕ}
    {g : Hom n m} {args : List V}
    (hpt : ∀ j a, args[j]? = some a → C.isRec j = false → a ∈ El (Θ.ty c j n g (args.take j)) (Hom.id n))
    (j : ℕ) : Θ.PtValid c n g (args.take j) := by
  intro i hi hr
  have hC' : Θ.ctors.getD c default = C := by rw [List.getD_eq_getElem?_getD, hC]; rfl
  rw [hC'] at hr
  simp only [List.length_take] at hi
  rw [List.getElem_take, List.take_take, Nat.min_eq_left (by omega)]
  exact hpt i _ (List.getElem?_eq_getElem _) hr

theorem DElem.res {Θ : SData m} (hΘ : Θ.ResClosed) {n : ℕ} {g : Hom n m} {v : V} (hv : DElem Θ n g v) :
    ∀ n' (h : Hom n' n), DElem Θ n' (g.comp h) (res h v) := by
  induction hv with
  | @con n g c C args rs hC hlen hrs hrec hpt ih =>
    intro n' h
    rw [res_conV]
    refine DElem.con hC (by simp [hlen]) (by simp [hrs]) (fun j a ha hj => ?_) (fun j a ha hj => ?_)
    · rw [List.getElem?_map] at ha
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
      exact ih j a0 ha0 hj n' h
    · rw [List.getElem?_map] at ha
      obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.1 ha
      rw [← List.map_take]
      exact hΘ c j n g _ a0 (SData.ptValid_take hC hpt j) (hpt j a0 ha0 hj) n' h
  | @hcomp n g φ u a hH hφ ha hu hcoh hbase iha ihu =>
    intro n' h
    rw [res_hcV]
    refine DElem.hcomp hH (hφ.restr h) (iha n' h) (fun n₁ h₁ r hh => ?_) (fun n₁ h₁ r hh n₂ h₂ => ?_)
      (fun n₁ h₁ hh => ?_)
    · rw [Cof.restr_restr] at hh; exact hu n₁ (h.comp h₁) r hh
    · rw [Cof.restr_restr] at hh; exact hcoh n₁ (h.comp h₁) r hh n₂ h₂
    · rw [Cof.restr_restr] at hh; show u n₁ (h.comp h₁) _ = _
      rw [hbase n₁ (h.comp h₁) hh, res_res]

theorem delem_restr_iff (Θ : SData m) (h : Hom k m) {n : ℕ} (g : Hom n k) (v : V) :
    DElem (Θ.restr h) n g v ↔ DElem Θ n (h.comp g) v := by
  constructor
  · intro hv
    induction hv with
    | con hC hlen hrs _ hpt ih => exact DElem.con hC hlen hrs ih hpt
    | hcomp hH hφ _ _ hcoh hbase iha ihu => exact DElem.hcomp hH hφ iha ihu hcoh hbase
  · intro hv
    suffices ∀ g', DElem Θ n g' v → ∀ g, g' = h.comp g → DElem (Θ.restr h) n g v from this _ hv g rfl
    clear hv g
    intro g' hv'
    induction hv' with
    | con hC hlen hrs _ hpt ih =>
      intro g e; subst e
      exact DElem.con hC hlen hrs (fun j a ha hj => ih j a ha hj g rfl) hpt
    | hcomp hH hφ _ _ hcoh hbase iha ihu =>
      intro g e; subst e
      exact DElem.hcomp hH hφ (iha g rfl) (fun n₁ h₁ r hh => ihu n₁ h₁ r hh (g.comp h₁) rfl) hcoh hbase

end

end Model
