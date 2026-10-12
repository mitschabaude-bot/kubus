import Std.Data.HashMap
import Kubus.Syntax

namespace Kubus

/-! ## Semantic values

Interval variables in values are nominal atoms (`plam i v` binds the atom `i`).
Term closures are `env + body`. Neutral variables carry their types, so that
`p @ 0` of a neutral path reduces to its endpoint.
-/

mutual
inductive Val
  | univ (l : Nat)
  | pi (x : String) (a : Val) (env : List EnvE) (b : Tm)
  | lam (x : String) (env : List EnvE) (b : Tm)
  | sigma (x : String) (a : Val) (env : List EnvE) (b : Tm)
  | pair (a b : Val)
  /-- `(i : I) → A`, given as a line of types -/
  | piI (line : Val)
  | pathP (line : Val) (u v : Val)
  | plam (i : Atom) (b : Val)
  | data (d : String) (k : Nat) (ps : List Val)
  | con (c : String) (args : List Val)
  | pcon (c : String) (args : List Val) (dims : List Formula)
  /-- formal homogeneous composition in a higher inductive type; `sys` holds lines -/
  | hcompF (ty : Val) (u0 : Val) (sys : List (Face × Val))
  /-- `Glue A [φ ↦ (T, e)]` -/
  | glueTy (base : Val) (sys : List (Face × Val))
  /-- `glue [φ ↦ t] a` -/
  | glue (a : Val) (sys : List (Face × Val))
  /-- composition in the universe; `sys` holds lines of types -/
  | compU (base : Val) (sys : List (Face × Val))
  /-- pattern-matching function `f` with parameters `env` -/
  | split (f : String) (k : Nat) (env : List EnvE)
  -- neutrals
  | var (lvl : Nat) (ty : Val)
  | gvar (n : String) (ty : Val)
  | app (f a : Val)
  | fst (p : Val)
  | snd (p : Val)
  | papp (p : Val) (r : Formula)
  | splitApp (f : String) (k : Nat) (env : List EnvE) (arg : Val)
  /-- stuck composition; `line` and `sys` hold lines -/
  | comp (line : Val) (u0 : Val) (sys : List (Face × Val))
  | unglue (u : Val) (base : Val) (sys : List (Face × Val))
  | unglueU (u : Val) (base : Val) (sys : List (Face × Val))

inductive EnvE
  | v (v : Val)
  | d (r : Formula)
end

instance : Inhabited Val := ⟨.univ 0⟩
instance : Inhabited EnvE := ⟨.d Formula.zero⟩

abbrev Env := List EnvE

def Val.isNeutral : Val → Bool
  | .var .. | .gvar .. | .app .. | .fst _ | .snd _ | .papp .. | .splitApp .. | .comp .. | .unglue ..
  | .unglueU .. => true
  | _ => false

/-! ## Global declarations -/

structure CtorInfo where
  name : String
  data : String
  /-- argument types, each in context `params, previous args` -/
  tele : List (String × Tm)
  /-- which arguments are recursive (for the termination checker) -/
  recArgs : List Bool
  dims : List String
  /-- boundary system, in context `params, args, dims` -/
  boundary : TSys Tm
  deriving Inhabited

structure DataInfo where
  name : String
  params : List (String × Tm)
  level : Nat
  ctors : List CtorInfo
  isHIT : Bool
  /-- closed, no path constructors, and all fields are again closed first-order data:
  then transport along a constant line is the identity (regularity) -/
  firstOrder : Bool
  /-- the declaration mentions no universes, so displacing it changes nothing -/
  liftInvariant : Bool
  deriving Inhabited

structure Branch where
  ctor : String
  nArgs : Nat
  nDims : Nat
  body : Tm
  deriving Inhabited

structure DefInfo where
  name : String
  ty : Val
  tyTm : Tm
  /-- `none` while the definition is being checked: then it is an opaque constant -/
  body : Option Tm
  value : Option Val
  /-- values of displaced copies -/
  lifted : List (Nat × Val) := []
  nParams : Nat
  branches : List Branch
  deriving Inhabited

structure Globals where
  defs : Std.HashMap String DefInfo := {}
  datas : Std.HashMap String DataInfo := {}
  ctors : Std.HashMap String CtorInfo := {}
  deriving Inhabited

structure St where
  globals : Globals := {}
  fresh : Nat := 0

abbrev M := StateT St (Except String)

def freshAtom : M Atom := modifyGet fun s => (s.fresh, { s with fresh := s.fresh + 1 })

def getGlobals : M Globals := return (← get).globals

def lookupData (d : String) : M DataInfo := do
  match (← getGlobals).datas[d]? with
  | some i => pure i
  | none => throw s!"internal: unknown data type {d}"

def lookupCtor (c : String) : M CtorInfo := do
  match (← getGlobals).ctors[c]? with
  | some i => pure i
  | none => throw s!"internal: unknown constructor {c}"

def lookupDef (f : String) : M DefInfo := do
  match (← getGlobals).defs[f]? with
  | some i => pure i
  | none => throw s!"internal: unknown definition {f}"

end Kubus
