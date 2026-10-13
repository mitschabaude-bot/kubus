import Model.DataRep

/-!
# Inductive types: well-formed semantic data

The conditions on a semantic inductive type `Θ` (provided by the declaration's well-formedness)
under which its code is fibrant: the argument types are fibrant and natural, they do not depend
on recursive arguments, and the boundaries are simple with point arguments of the right types
(the semantic counterpart of `Ctor.simpleB` and `Ctor.bndTyped`).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem evalBndList_eq {conF : ℕ → List V → List (DM n) → V} (args : List V) (rs : List (DM n)) (as : Tm) :
    evalBndList conF args rs as = as.toList.map (evalBnd conF args rs) := by
  induction as <;> simp_all [evalBndList, Tm.toList]

/-- The earlier arguments of a nested constructor, with the values of point variables from `pre`
(the arguments of the outer constructor, oldest first) and junk for the rest. `prev` lists the
nested argument terms, most recent first. -/
def nestVal (pre : List V) : Tm → V
  | .var y => pre.reverse.getD y ∅
  | _ => ∅

def nestPre (pre : List V) (prev : List Tm) : List V := prev.reverse.map (nestVal pre)

mutual
/-- The boundary term `t` of constructor `c` (with declaration `C`) is simple and its nested
constructors get point arguments of their argument types. -/
def BTy (Θ : SData m) (c : ℕ) (C : Ctor) : Tm → Prop
  | .var x => x < C.args.length ∧ C.isRec (C.args.length - 1 - x) = true
  | .con _ c' _ as rs' => c' < c ∧ ∃ C', Θ.ctors[c']? = some C' ∧ as.toList.length = C'.args.length ∧
      rs'.length = C'.dims ∧ BTyArgs Θ c C C' c' 0 [] as
  | _ => False
/-- The arguments `as` of the nested constructor `c'` from position `k` on (earlier ones `prev`,
most recent first). -/
def BTyArgs (Θ : SData m) (c : ℕ) (C C' : Ctor) (c' : ℕ) (k : ℕ) (prev : List Tm) : Tm → Prop
  | .tcons a as => (C'.isRec k = true → BTy Θ c C a) ∧
      (C'.isRec k = false → ∃ x, a = .var x ∧ x < C.args.length ∧ C.isRec (C.args.length - 1 - x) = false ∧
        ∀ n (g : Hom n m) (pre : List V), pre.length = C.args.length → Θ.PtValid c n g pre →
          Θ.ty c' k n g (nestPre pre prev) =
            Θ.ty c (C.args.length - 1 - x) n g (pre.take (C.args.length - 1 - x))) ∧
      BTyArgs Θ c C C' c' (k + 1) (a :: prev) as
  | _ => True
end

/-- The constructors before `c`, for evaluating the boundary of `c`. -/
def conBefore (ctors : List Ctor) (c n : ℕ) : ℕ → List V → List (DM n) → V :=
  fun c' as rs' => if _ : c' < c then conV ctors n c' as rs' else junkV n

/-- Arguments of constructor `c` (declaration `C`) at the restriction `g`: the right number,
recursive ones elements, point ones of their types. -/
def SData.ArgsTyped (Θ : SData m) (c : ℕ) (C : Ctor) (n : ℕ) (g : Hom n m) (args : List V) : Prop :=
  args.length = C.args.length ∧ (∀ j a, args[j]? = some a → C.isRec j = true → DElem Θ n g a) ∧
    (∀ j a, args[j]? = some a → C.isRec j = false → a ∈ El (Θ.ty c j n g (args.take j)) (Hom.id n))

/-- A well-formed semantic inductive type, apart from the fibrancy of its argument types. -/
structure SData.GoodCore (Θ : SData m) : Prop where
  nat : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → ∀ n' (h : Hom n' n),
    res h (Θ.ty c j n g pre) = Θ.ty c j n' (g.comp h) (pre.map (res h))
  recIrr : ∀ c j n (g : Hom n m) pre pre', pre.length = pre'.length →
    (∀ i (hi : i < pre.length) (hi' : i < pre'.length), (Θ.ctors.getD c default).isRec i = false →
      pre[i] = pre'[i]) → Θ.ty c j n g pre = Θ.ty c j n g pre'
  bnd : ∀ c C, Θ.ctors[c]? = some C → ∀ ψ b, (ψ, b) ∈ C.bnd → ∀ n (rs : List (DM n)),
    (ival (renv rs) ψ).holds → BTy Θ c C b
  const : Θ.params = false → ∀ c j n (g g' : Hom n m) pre, Θ.ty c j n g pre = Θ.ty c j n g' pre
  nonhit : Θ.hit = false → ∀ (c : ℕ) (C : Ctor), Θ.ctors[c]? = some C → C.dims = 0 ∧ C.bnd = []
  ovl : ∀ c C, Θ.ctors[c]? = some C → ∀ ψ b ψ' b', (ψ, b) ∈ C.bnd → (ψ', b') ∈ C.bnd →
    ∀ n (g : Hom n m) args (rs : List (DM n)), Θ.ArgsTyped c C n g args → rs.length = C.dims →
      (ival (renv rs) ψ).holds → (ival (renv rs) ψ').holds →
      evalBnd (conBefore Θ.ctors c n) args rs b = evalBnd (conBefore Θ.ctors c n) args rs b'

/-- A well-formed semantic inductive type. -/
structure SData.Good (Θ : SData m) : Prop extends Θ.GoodCore where
  fib : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → Fib (Θ.ty c j n g pre) n

namespace SData.Good

variable {Θ : SData m} (hΘ : Θ.Good)
include hΘ

theorem ptValid_res {c n : ℕ} {g : Hom n m} {pre : List V} (hp : Θ.PtValid c n g pre) (n' : ℕ) (h : Hom n' n) :
    Θ.PtValid c n' (g.comp h) (pre.map (res h)) := by
  intro i hi hr
  simp only [List.length_map] at hi
  have hpi : Θ.PtValid c n g (pre.take i) := fun i' hi' hr' => by
    simp only [List.length_take] at hi'
    have := hp i' (by omega) hr'
    rw [List.getElem_take, List.take_take, Nat.min_eq_left (by omega)]; exact this
  have := (hΘ.fib c i n g _ hpi).elRes n (Hom.id n) _ (hp i hi hr) n' h
  rw [El_eq_res_id, Hom.id_comp, hΘ.nat c i n g _ hpi n' h] at this
  simpa [List.getElem_map, List.map_take] using this

theorem resClosed : Θ.ResClosed := by
  intro c j n g pre a hp ha n' h
  have := (hΘ.fib c j n g pre hp).elRes n (Hom.id n) a ha n' h
  rwa [El_eq_res_id, Hom.id_comp, hΘ.nat c j n g pre hp n' h] at this

theorem pt_kv {c n : ℕ} {g : Hom n m} {pre : List V} (hp : Θ.PtValid c n g pre) {i : ℕ} (hi : i < pre.length)
    (hr : (Θ.ctors.getD c default).isRec i = false) : IsKV n pre[i] := by
  have hpi : Θ.PtValid c n g (pre.take i) := fun i' hi' hr' => by
    simp only [List.length_take] at hi'
    have := hp i' (by omega) hr'
    rw [List.getElem_take, List.take_take, Nat.min_eq_left (by omega)]; exact this
  exact (hΘ.fib c i n g _ hpi).elKV n (Hom.id n) _ (hp i hi hr)

end SData.Good


/-- The fibrancy and recursive-argument irrelevance of the argument types. -/
structure SData.Basic (Θ : SData m) : Prop where
  recIrr : ∀ c j n (g : Hom n m) pre pre', pre.length = pre'.length →
    (∀ i (hi : i < pre.length) (hi' : i < pre'.length), (Θ.ctors.getD c default).isRec i = false →
      pre[i] = pre'[i]) → Θ.ty c j n g pre = Θ.ty c j n g pre'
  fib : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → Fib (Θ.ty c j n g pre) n

theorem SData.Good.basic {Θ : SData m} (h : Θ.Good) : Θ.Basic := ⟨h.recIrr, h.fib⟩

theorem SData.Basic.pt_kv {Θ : SData m} (hΘ : Θ.Basic) {c n : ℕ} {g : Hom n m} {pre : List V}
    (hp : Θ.PtValid c n g pre) {i : ℕ} (hi : i < pre.length)
    (hr : (Θ.ctors.getD c default).isRec i = false) : IsKV n pre[i] := by
  have hpi : Θ.PtValid c n g (pre.take i) := fun i' hi' hr' => by
    simp only [List.length_take] at hi'
    have := hp i' (by omega) hr'
    rw [List.getElem_take, List.take_take, Nat.min_eq_left (by omega)]; exact this
  exact (hΘ.fib c i n g _ hpi).elKV n (Hom.id n) _ (hp i hi hr)

end

end Model
