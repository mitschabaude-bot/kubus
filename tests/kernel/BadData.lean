import KubusCore
/-! Regression tests for the kernel's check of data declarations (`lake env lean` must succeed). -/
open KubusCore KubusCore.Kernel Tm

def accepts (S : Sig) : Bool := (checkSig S).toBool

/-- `data D (X Y : U₀) := c0 (x : X) | c1 (y : Y) (i : I) [i = 1 ↦ c0 y]`: the boundary is
ill-typed. Checked against the full declaration it passed (via `conBnd`), and gave `false ≡ true`. -/
def D : DataDecl := { level := 0, params := [.univ 0, .univ 0], ctors := [
  { args := [.point (.var 1)], dims := 0, bnd := [] },
  { args := [.point (.var 0)], dims := 1,
    bnd := [(.var 0, .con 0 0 (Ctor.paramVars 2 1) (ofList [.var 0]) [])] }] }

/-- `data Bad := tt | ff | seg (i : I) [i = 1 ↦ tt, i = 1 ↦ ff]`: the boundary disagrees on its
overlap. -/
def Bad : DataDecl := { level := 0, params := [], ctors := [
  { args := [], dims := 0, bnd := [] }, { args := [], dims := 0, bnd := [] },
  { args := [], dims := 1, bnd := [(.var 0, .con 0 0 .tnil .tnil []), (.var 0, .con 0 1 .tnil .tnil [])] }] }

def Nat' : DataDecl := { level := 0, params := [], ctors := [
  { args := [], dims := 0, bnd := [] }, { args := [.recur], dims := 0, bnd := [] }] }

def S1 : DataDecl := { level := 0, params := [], ctors := [
  { args := [], dims := 0, bnd := [] },
  { args := [], dims := 1, bnd := [(.neg (.var 0), .con 0 0 .tnil .tnil []), (.var 0, .con 0 0 .tnil .tnil [])] }] }

#guard !accepts [.data D]
#guard !accepts [.data Bad]
#guard accepts [.data Nat']
#guard accepts [.data S1]
