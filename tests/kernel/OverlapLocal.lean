import KubusCore
import KubusCore.Meta.Near

/-!
A single boundary normal form over a disjunctive overlap is stricter than `EqTm`. The two paths below have different constructor heads and no boundary that holds throughout the overlap, but they agree by `EqTm.local`. A syntactic overlap check must split the overlap into consistent DNF faces before substituting endpoints and normalizing.

Run with `lake env lean tests/kernel/OverlapLocal.lean`.
-/

namespace OverlapLocal

open KubusCore KubusCore.Kernel Tm

def a : Tm := .con 0 0 .tnil .tnil []
def b : Tm := .con 0 1 .tnil .tnil []

def pathCtor : Ctor :=
  { args := [], dims := 1, bnd := [(.neg (.var 0), a), (.var 0, b)] }

def left : Tm := .con 0 2 .tnil .tnil [.var 1]
def right : Tm := .con 0 3 .tnil .tnil [.var 1]

def square : Ctor :=
  { args := [], dims := 2,
    bnd := [(.or (.neg (.var 1)) (.var 1), left), (.neg (.var 0), right)] }

def D : DataDecl :=
  { level := 0, params := [], ctors :=
      [{ args := [], dims := 0, bnd := [] },
       { args := [], dims := 0, bnd := [] }, pathCtor, pathCtor, square] }

-- This is the exact signature used by Wf to check square's boundaries and overlaps.
def Sc : Sig := [.data (D.truncate 4)]
def ty : Tm := .data 0 .tnil
def overlap : I := .and (.or (.neg (.var 1)) (.var 1)) (.neg (.var 0))

#guard (checkSig [.data D]).toBool

theorem simple_left : Ctor.simpleB D.ctors 0 0 4 0 square left = true := rfl
theorem simple_right : Ctor.simpleB D.ctors 0 0 4 0 square right = true := rfl

theorem path_typed {Φ : I} (hΦ : Φ.Scoped 2) {c : Nat}
    (hc : (D.truncate 4).ctors[c]? = some pathCtor) :
    HasTy Sc 2 Φ [] (.con 0 c .tnil .tnil [.var 1]) ty := by
  have hw : Wf Sc 2 Φ [] := .nil hΦ
  exact .con rfl hc rfl (.data rfl (by decide) (.nil hw)) (.nil hw) rfl
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)

theorem endpoints_agree {Φ : I} (hΦ : Φ.Scoped 2)
    (he : I.Entails Φ (.or (.neg (.var 1)) (.var 1))) :
    EqTm Sc 2 Φ [] left right ty := by
  have hl : HasTy Sc 2 Φ [] left ty := path_typed hΦ rfl
  have hr : HasTy Sc 2 Φ [] right ty := path_typed hΦ rfl
  refine .local (by decide) (by decide) he hl hr ?_ ?_
  · have hΦ0 : (cof Φ (.neg (.var 1))).Scoped 2 := ⟨hΦ, by decide⟩
    have hl0 := HasTy.restrict hΦ0 (KubusCore.Meta.ent_and_left _ _) hl
    have hr0 := HasTy.restrict hΦ0 (KubusCore.Meta.ent_and_left _ _) hr
    have he0 : I.Entails (cof Φ (.neg (.var 1)))
        (Ctor.cofAt (.neg (.var 0)) [.var 1]) := KubusCore.Meta.ent_and_right _ _
    have el : EqTm Sc 2 (cof Φ (.neg (.var 1))) [] left a ty :=
      .conBnd (D := D.truncate 4) (C := pathCtor) (k := 0) rfl rfl rfl he0 rfl rfl hl0
    have er : EqTm Sc 2 (cof Φ (.neg (.var 1))) [] right a ty :=
      .conBnd (D := D.truncate 4) (C := pathCtor) (k := 0) rfl rfl rfl he0 rfl rfl hr0
    exact .trans el (.symm er)
  · have hΦ1 : (cof Φ (.var 1)).Scoped 2 := ⟨hΦ, by decide⟩
    have hl1 := HasTy.restrict hΦ1 (KubusCore.Meta.ent_and_left _ _) hl
    have hr1 := HasTy.restrict hΦ1 (KubusCore.Meta.ent_and_left _ _) hr
    have he1 : I.Entails (cof Φ (.var 1))
        (Ctor.cofAt (.var 0) [.var 1]) := KubusCore.Meta.ent_and_right _ _
    have el : EqTm Sc 2 (cof Φ (.var 1)) [] left b ty :=
      .conBnd (D := D.truncate 4) (C := pathCtor) (k := 1) rfl rfl rfl he1 rfl rfl hl1
    have er : EqTm Sc 2 (cof Φ (.var 1)) [] right b ty :=
      .conBnd (D := D.truncate 4) (C := pathCtor) (k := 1) rfl rfl rfl he1 rfl rfl hr1
    exact .trans el (.symm er)

theorem overlap_eq : EqTm Sc 2 overlap [] left right ty :=
  endpoints_agree (by decide) (KubusCore.Meta.ent_and_left _ _)

theorem overlap_consistent : ¬ I.Entails overlap .zero := by decide

theorem no_uniform_boundary : ∀ ψ t, (ψ, t) ∈ pathCtor.bnd →
    ¬ I.Entails overlap (Ctor.cofAt ψ [.var 1]) := by
  intro ψ t ht
  simp [pathCtor] at ht
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem different_heads : ¬ TmNear left right := by
  intro h
  cases h

#print axioms overlap_eq

-- P12 accepts the unsplit overlap by comparing its two DNF faces separately.
#guard decide (Boundary.Agree D.ctors 0 0 0 4 overlap left right)

/-- Normalization substitutes already normalized recursive arguments when unfolding a boundary. -/
def WrapD : DataDecl :=
  { level := 0, params := [], ctors :=
      [{ args := [], dims := 0, bnd := [] },
       { args := [.recur], dims := 1, bnd := [(.one, .var 0)] },
       { args := [.recur], dims := 2,
         bnd := [(.neg (.var 1), .con 0 1 .tnil
           (Tm.ofList [.con 0 1 .tnil (Tm.ofList [.var 0]) [.var 1]]) [.var 0]),
           (.neg (.var 0), .var 0)] }] }

#guard (checkSig [.data WrapD]).toBool

end OverlapLocal
