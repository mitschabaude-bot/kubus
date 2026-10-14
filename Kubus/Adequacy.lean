import Kubus.Bridge
import Kubus.SelfCheck

/-!
# Translation adequacy (run by `kubus` on every certified definition)

The kernel certifies the translated statement. To show that it is the statement the user
wrote, the kernel's type is read back into a Kubus core term (independently of the
translation: a syntactic inverse of the kernel's term formers), evaluated by Kubus, and
compared with the elaborated type by Kubus's conversion check. A mismatch is an error.

Read-back covers the kernel's term formers that arise from types: Π, Σ, λ, application,
pairs and projections, universes, constants, path types, path abstraction and application,
`(i : I) → A`, `transp`, `hcomp`, Glue types and `glue`, inductive types and constructors.
Kernel terms without a Kubus counterpart (`unglue`, whose Kubus form records the Glue type;
eliminators, which Kubus represents by named pattern-matching definitions; bare systems) make
the statement "not covered"; this is reported, not an error.
-/

namespace Kubus.Adequacy

open Bridge (KTm KI)

inductive Kind | tm | dim

/-- The Kubus index of the `x`-th term (or interval) variable of the stack. -/
def rbIdx (st : List Kind) (dim : Bool) (x : Nat) : Except String Nat := do
  let mut n := 0
  let mut i := 0
  for k in st do
    let isDim := match k with | .dim => true | .tm => false
    if isDim == dim then
      if n == x then return i
      n := n + 1
    i := i + 1
  throw s!"variable {x} out of scope"

def rbI (st : List Kind) : KI → Except String ITm
  | .zero => pure .zero
  | .one => pure .one
  | .var i => return .var (← rbIdx st true i)
  | .neg r => return .neg (← rbI st r)
  | .and r s => return .and (← rbI st r) (← rbI st s)
  | .or r s => return .or (← rbI st r) (← rbI st s)

/-- An interval term under one more (interval) binder, moved out of it. -/
def lowerI : ITm → Except String ITm
  | .var 0 => throw "a system key mentions its bound variable"
  | .var (i + 1) => pure (.var i)
  | .neg r => return .neg (← lowerI r)
  | .and r s => return .and (← lowerI r) (← lowerI s)
  | .or r s => return .or (← lowerI r) (← lowerI s)
  | r => pure r

/-- The branches of a system (nested `split`s, `[]`), the last one with key `key`. -/
def branches (key : KI) : KTm → List (KI × KTm)
  | .split φ t ψ u => (φ, t) :: branches ψ u
  | .abort => []
  -- the tube of a heterogeneous composition (`Tm.comp`) transports the system's branches
  | .transp _ _ .abort => []
  | .transp A r s@(.split ..) => (branches key s).map fun (φ, t) => (φ, .transp A r t)
  | t => [(key, t)]

/-- The names of the kernel signature's constants and inductive types. -/
structure Names where
  consts : Std.HashMap Nat (String × Nat) := {}
  datas : Std.HashMap Nat (String × Nat) := {}
  globals : Globals := {}

def Names.of (env : Bridge.Env) (g : Globals) : Names :=
  { consts := env.consts.fold (fun m key c => m.insert c key) {}
    datas := env.datas.fold (fun m key d => m.insert d key) {}
    globals := g }

/-- Read a kernel term back into a Kubus core term. -/
partial def rb (nm : Names) (st : List Kind) : KTm → Except String Tm
  | .var x => return .var (← rbIdx st false x)
  | .const c =>
    match nm.consts[c]? with
    | some (n, k) => pure (.glob n k)
    | none => throw s!"unknown constant c{c}"
  | .univ l => pure (.univ l)
  | .pi A B => return .pi "x" (← rb nm st A) (← rb nm (.tm :: st) B)
  | .lam _ t => return .lam "x" (← rb nm (.tm :: st) t)
  | .app f a => return .app (← rb nm st f) (← rb nm st a)
  | .sigma A B => return .sigma "x" (← rb nm st A) (← rb nm (.tm :: st) B)
  | .pair a b => return .pair (← rb nm st a) (← rb nm st b)
  | .fst p => return .fst (← rb nm st p)
  | .snd p => return .snd (← rb nm st p)
  | .path A a b => return .pathP (.plam "i" (← rb nm (.dim :: st) A)) (← rb nm st a) (← rb nm st b)
  | .plam t => return .plam "i" (← rb nm (.dim :: st) t)
  | .papp p r => return .papp (← rb nm st p) (← rbI st r)
  | .ipi A => return .piI "i" (← rb nm (.dim :: st) A)
  | .transp A φ a => return .transp "i" (← rb nm (.dim :: st) A) (← rbI st φ) (← rb nm st a)
  | .hcomp A φ u a => do
    let sys ← (branches φ.shift u).mapM fun (r, t) => do
      return (← lowerI (← rbI (.dim :: st) r), ← rb nm (.dim :: st) t)
    return .hcomp "i" (← rb nm st A) sys (← rb nm st a)
  | .glue A φ T e => do
    let Ts := branches φ T
    let es := branches φ e
    if Ts.length != es.length then throw "a Glue type whose fibres and equivalences differ in shape"
    let sys ← (Ts.zip es).mapM fun ((r, T), (_, e)) => do
      return (← rbI st r, Tm.pair (← rb nm st T) (← rb nm st e))
    return .glueTy (← rb nm st A) sys
  | .glueEl φ _ t a => do
    let sys ← (branches φ t).mapM fun (r, t) => do return (← rbI st r, ← rb nm st t)
    return .glue sys (← rb nm st a)
  | .data d ps =>
    match nm.datas[d]? with
    | some (dn, k) => return .data dn k (← ps.toList.mapM (rb nm st))
    | none => throw s!"unknown inductive type D{d}"
  | .con d c _ args rs =>
    match nm.datas[d]? with
    | some (dn, _) =>
      match nm.globals.datas[dn]? with
      | some di =>
        match di.ctors[c]? with
        | some ci => return .con ci.name (← args.toList.mapM (rb nm st)) (← rs.mapM (rbI st))
        | none => throw s!"unknown constructor {c} of {dn}"
      | none => throw s!"unknown inductive type {dn}"
    | none => throw s!"unknown inductive type D{d}"
  | .unglue .. => throw "not covered: unglue"
  | .elim .. => throw "not covered: an eliminator"
  | .split .. | .abort => throw "not covered: a system outside a composition or Glue type"
  | .tnil | .tcons .. => throw "not covered: a list outside an inductive type"

/-- A deliberately wrong statement (for the self-test of the check, `KUBUS_ADEQUACY_SELFTEST`):
the endpoints of the first path type swapped, or else one more Π. -/
partial def corrupt (t : KTm) : KTm :=
  let rec swap : KTm → Option KTm
    | .path A a b => if a == b then none else some (.path A b a)
    | .pi A B => (swap B).map (.pi A ·) <|> (swap A).map (.pi · B)
    | .sigma A B => (swap B).map (.sigma A ·) <|> (swap A).map (.sigma · B)
    | .ipi A => (swap A).map .ipi
    | _ => none
  (swap t).getD (.pi (.univ 0) t.shift)

/-- The outcome for one definition. -/
inductive Result
  | adequate
  | notCovered (why : String)
  | mismatch (why : String)

/-- Compare the kernel's statement of `n` (displaced by `k`) with the elaborated type. -/
def check (nm : Names) (n : String) (k : Nat) (kty : KTm) (selftest : Bool := false) : M Result := do
  let kty := if selftest then corrupt kty else kty
  let some info := nm.globals.defs[n]? | return .mismatch "not an elaborated definition"
  match rb nm [] kty with
  | .error e => return .notCovered e
  | .ok ty =>
    let v1 ← eval [] ty
    let v2 ← eval [] (info.tyTm.lift k)
    if (← convTy 0 v1 v2) && (← convTy 0 v2 v1) then return .adequate
    return .mismatch s!"the kernel's type reads back as {← ppVal {} v1}, the elaborated type is {← ppVal {} v2}"

end Kubus.Adequacy
