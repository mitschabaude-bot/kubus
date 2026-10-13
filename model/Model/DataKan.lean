import Model.DataSmall
import Mathlib.SetTheory.ZFC.Rank

/-!
# Inductive types: transport and the eliminator

Both read off the representation of an element as a constructor value (with no boundary at the
stage itself) or a formal composition (whose face does not hold). The eliminator is defined by
well-founded recursion on the rank of the element.

* Transport (with parameters) is componentwise on constructors: the arguments are transported
  along their type lines, in which the earlier arguments are their transport fillers (the
  spec's `Tm.transpTele`); recursive arguments are transported in the inductive type itself. A
  formal composition is transported by transporting its tube and base (`transpHcomp`). Without
  parameters, transport is the identity (`transpData0`).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

section repr

variable (Θ : SData m)

/-- `v` is a constructor value with no boundary at its own stage (with Kripke-value arguments,
so the representation is unique). -/
def RepCon (k : ℕ) (v : V) : Prop :=
  ∃ c : ℕ, ∃ args : List V, ∃ rs : List (DM k),
    v = conV Θ.ctors k c args rs ∧ bndAtMap (Θ.ctors.getD c default) rs (Hom.id k) = none ∧ ∀ a ∈ args, IsKV k a

/-- `v` is a formal composition whose face does not hold (with a Kripke-value base). -/
def RepHc (k : ℕ) (v : V) : Prop :=
  ∃ ψ : Cof k, ∃ u : Tube k, ∃ a : V, v = hcV k ψ u a ∧ ψ.IsCof ∧ ¬ ψ.holds ∧ IsKV k a

end repr

/-- Transport in an inductive type with parameters, as a relation: `TR Θ k f φ v w` says that
`v` is transported along the line `f` (direction: the last variable) with face `φ` to `w`.
Constructors are transported componentwise: point argument `j` along its type line, in which
the earlier arguments are their transport fillers (the spec's `Tm.transpTele`); recursive
arguments in the inductive type itself, with the filler given by transport along the squeezed
line `tfLine` (as `transpFillF`). Formal compositions are transported by transporting tube and
base. -/
inductive TR (Θ : SData m) : (k : ℕ) → Hom (k + 1) m → Cof k → V → V → Prop
  | con {k : ℕ} {f : Hom (k + 1) m} {φ : Cof k} {c : ℕ} {args : List V} {rs : List (DM k)}
      {outs fills : List V} :
      bndAtMap (Θ.ctors.getD c default) rs (Hom.id k) = none → (∀ a ∈ args, IsKV k a) →
      outs.length = args.length → fills.length = args.length →
      (∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true →
        TR Θ k f φ args[j] (outs.getD j ∅)) →
      (∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = true →
        TR Θ (k + 1) (f.comp (tfLine k)) (fillFace φ) (res (Hom.wk k) args[j]) (fills.getD j ∅)) →
      (∀ j (hj : j < args.length), (Θ.ctors.getD c default).isRec j = false →
        outs.getD j ∅ = transpAt (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ args[j] ∧
        fills.getD j ∅ = transpFillF (Θ.ty c j (k + 1) f (fills.take j)) (Hom.id (k + 1)) φ args[j]) →
      TR Θ k f φ (conV Θ.ctors k c args rs) (conV Θ.ctors k c outs rs)
  | hc {k : ℕ} {f : Hom (k + 1) m} {φ : Cof k} {ψ : Cof k} {u u' : Tube k} {a a' : V} :
      ψ.IsCof → ¬ ψ.holds → IsKV k a → TR Θ k f φ a a' →
      (∀ n (g : Hom n k) r, (ψ.restr g).holds → TR Θ n (f.comp (Hom.lift g)) (φ.restr g) (u n g r) (u' n g r)) →
      TR Θ k f φ (hcV k ψ u a) (hcV k ψ u' a')

/-- Transport in an inductive type along the line `f`: the identity without parameters
(`transpData0`), otherwise given by `TR`. -/
def transpD (Θ : SData m) (k : ℕ) (f : Hom (k + 1) m) (φ : Cof k) (v : V) : V :=
  if ¬ Θ.params then v
  else if h : ∃ w, TR Θ k f φ v w then Classical.choose h else v

/-- The element `c` of a list encoded by nested pairs. -/
def vnth : V → ℕ → V
  | v, 0 => π1 v
  | v, c + 1 => vnth (π2 v) c

/-- Application to a list of arguments. -/
def appsV (k : ℕ) : V → List V → V
  | f, [] => f
  | f, a :: as => appsV k (appV k f a) as

/-- Interval application to a list of interval arguments. -/
def pappsV (k : ℕ) : V → List (DM k) → V
  | f, [] => f
  | f, r :: rs => pappsV k (pappV k f r) rs

/-- The eliminator, with motive `P` (a code at every restriction and element) and branches
`bs` (a list, at every restriction), at the restriction `g`. -/
def elimD (Θ : SData m) (P : (n : ℕ) → Hom n m → V → V) (bs : (k : ℕ) → Hom k m → V) (k : ℕ) (g : Hom k m) (v : V) : V :=
  if h : RepCon Θ k v then
    pappsV k (appsV k (vnth (bs k g) (Classical.choose h))
      (Classical.choose (Classical.choose_spec h) ++
        ((List.range (Classical.choose (Classical.choose_spec h)).length).filter
          (Θ.ctors.getD (Classical.choose h) default).isRec).map fun j =>
          if _ : ZFSet.rank ((Classical.choose (Classical.choose_spec h)).getD j ∅) < ZFSet.rank v then
            elimD Θ P bs k g ((Classical.choose (Classical.choose_spec h)).getD j ∅) else ∅))
      (Classical.choose (Classical.choose_spec (Classical.choose_spec h)))
  else if h : RepHc k v then
    compF (P (k + 1) (g.comp (Hom.wk k))
        (hcV (k + 1) (fillFace (Classical.choose h))
          (fillTube (Classical.choose h) (Classical.choose (Classical.choose_spec h))
            (Classical.choose (Classical.choose_spec (Classical.choose_spec h))))
          (res (Hom.wk k) (Classical.choose (Classical.choose_spec (Classical.choose_spec h))))))
      (Hom.id (k + 1)) (Classical.choose h)
      (fun n' g' r => if _ : ZFSet.rank ((Classical.choose (Classical.choose_spec h)) n' g' r) < ZFSet.rank v then
        elimD Θ P bs n' (g.comp g') ((Classical.choose (Classical.choose_spec h)) n' g' r) else ∅)
      (if _ : ZFSet.rank (Classical.choose (Classical.choose_spec (Classical.choose_spec h))) < ZFSet.rank v then
        elimD Θ P bs k g (Classical.choose (Classical.choose_spec (Classical.choose_spec h))) else ∅)
  else ∅
termination_by ZFSet.rank v
decreasing_by all_goals first | assumption | (simp_wf; assumption) | simp_all

/-! ### The code of an inductive type -/

section code

/-- The elements of `Λ` at the restriction `g`, as a set. -/
def delemSet (Λ : SData m) (n : ℕ) (g : Hom n m) : V := ZFSet.sep (DElem Λ n g) (dataBound Λ n g)

/-- The argument types of `Λ` at stage `m` on the valid argument lists: this makes the code
determine its argument types (needed for transport), without recording the parameters. -/
def shapeV (Λ : SData m) : V :=
  ⋃ c : Fin Λ.ctors.length, ⋃ j : Fin (Λ.ctors[c].args.length + 1),
    ZFSet.range fun p : VPref Λ (delemSet Λ) m (Hom.id m) c Λ.ctors[c] j =>
      ZFSet.pair (natZ c) (ZFSet.pair (natZ j) (ZFSet.pair (vlist p.1) (Λ.ty c j m (Hom.id m) p.1)))

/-- The transport graph of `Λ` along its last variable. -/
def dataTr : (k : ℕ) → SData k → V
  | 0, _ => ∅
  | n + 1, Λ => trGraph n (delemSet Λ n (Hom.endpt n (DM.zero n))) fun φ a => transpD Λ n (Hom.id (n + 1)) φ a

/-- The datum of the inductive type `Λ` at its own stage. -/
def dataDatum (Λ : SData k) : V :=
  quad (tagZ tData (shapeV Λ)) (delemSet Λ k (Hom.id k)) (dataTr k Λ)
    (hcGraph k (fun n g => delemSet Λ n g) fun φ u a => hcV k φ u a)

/-- The code of the inductive type `Θ` at stage `m`. -/
def dataC (Θ : SData m) : V := mkKV m fun k f => dataDatum (Θ.restr f)

theorem SData.restr_restr (Θ : SData m) (h : Hom k m) (g : Hom n k) : (Θ.restr h).restr g = Θ.restr (h.comp g) := rfl

theorem res_dataC (Θ : SData m) (h : Hom k m) : res h (dataC Θ) = dataC (Θ.restr h) := by
  simp only [dataC, res_mkKV]; rfl

theorem isKV_dataC (Θ : SData m) : IsKV m (dataC Θ) := isKV_mkKV _

end code

end

end Model
