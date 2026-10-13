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
  /-- `v`, the value of the global `g^k` applied to the spine `sp` (innermost argument first).
  Kept for printing definitions folded, and for comparing applications of the same global
  without unfolding them. -/
  | glued (g : String) (k : Nat) (sp : List EnvE) (v : Val)
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

/-- The value behind glued globals. -/
def Val.unfold : Val → Val
  | .glued _ _ _ v => v.unfold
  | v => v

mutual
/-- Whether the atom `i` occurs free in a value (if not, substituting for it is the identity). -/
partial def Val.hasAtom (i : Atom) : Val → Bool
  | .univ _ => false
  | .pi _ a env _ | .sigma _ a env _ => a.hasAtom i || envHasAtom i env
  | .lam _ env _ | .split _ _ env => envHasAtom i env
  | .pair a b => a.hasAtom i || b.hasAtom i
  | .piI l => l.hasAtom i
  | .pathP l a b => l.hasAtom i || a.hasAtom i || b.hasAtom i
  | .plam j b => j != i && b.hasAtom i
  | .data _ _ ps | .con _ ps => ps.any (·.hasAtom i)
  | .pcon _ as ds => as.any (·.hasAtom i) || ds.any (·.mentions i)
  | .hcompF ty u sys => ty.hasAtom i || u.hasAtom i || sysHasAtom i sys
  | .glueTy b sys | .glue b sys | .compU b sys => b.hasAtom i || sysHasAtom i sys
  | .glued _ _ sp v => envHasAtom i sp || v.hasAtom i
  | .var _ ty | .gvar _ ty => ty.hasAtom i
  | .app f a => f.hasAtom i || a.hasAtom i
  | .fst p | .snd p => p.hasAtom i
  | .papp p r => p.hasAtom i || r.mentions i
  | .splitApp _ _ env a => envHasAtom i env || a.hasAtom i
  | .comp l u sys | .unglue u l sys | .unglueU u l sys => l.hasAtom i || u.hasAtom i || sysHasAtom i sys

partial def envHasAtom (i : Atom) : Env → Bool
  | [] => false
  | .v v :: env => v.hasAtom i || envHasAtom i env
  | .d r :: env => r.mentions i || envHasAtom i env

partial def sysHasAtom (i : Atom) : List (Face × Val) → Bool
  | [] => false
  | (α, v) :: sys => α.mentions i || v.hasAtom i || sysHasAtom i sys
end

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

/-! ## Elaboration contexts -/

structure CEntry where
  name : String
  /-- `none` for interval variables -/
  ty : Option Val
  val : EnvE

structure Ctx where
  entries : List CEntry := []
  pos : Pos := { line := 0, col := 0 }

/-- A term recorded by the elaborator for self-checking (`--selfcheck`): context, core term,
its type, and a description. -/
structure SCItem where
  ctx : Ctx
  tm : Tm
  ty : Val
  label : String

/-- A metavariable: a closed term of type `ty`, a Π-type over the variables of the context it was
created in (interval variables become `(i : I) →`). Its solution is a closed term too. -/
structure MetaInfo where
  ty : Val
  /-- the context of creation and the type there, for error messages -/
  ctx : Ctx
  ctxTy : Val
  desc : String
  /-- printed as `?short` -/
  short : String
  sol : Option Tm := none
  solV : Option Val := none
  /-- a `?` hole (in editor mode): stays unsolved without an error -/
  hole : Bool := false

structure St where
  globals : Globals := {}
  metas : Array MetaInfo := #[]
  /-- editor mode (`kubus --lsp`): record types of subterms, holes are not errors -/
  lsp : Bool := false
  /-- recorded subterms with their context and type, and their printed types -/
  pendingHovers : Array (Pos × Ctx × Val) := #[]
  hovers : Array (Pos × String) := #[]
  /-- goals of `?` holes, printed at the end of the declaration -/
  pendingGoals : Array (Pos × Ctx × Val) := #[]
  goals : Array (Pos × String) := #[]
  fresh : Nat := 0
  /-- self-check mode: the elaborator records terms in `pending` and checks conversions both ways -/
  selfcheck : Bool := false
  pending : Array SCItem := #[]
  violations : Array String := #[]
  /-- self-checks skipped for running out of budget -/
  skips : Array String := #[]
  /-- evaluation steps, and the step limit of the running self-check (0: no limit) -/
  steps : Nat := 0
  limit : Nat := 0
  budget : Nat := 1000000
  nChecks : Nat := 0
  nSkipped : Nat := 0
  nGaps : Nat := 0

abbrev M := StateT St (Except String)

def freshAtom : M Atom := modifyGet fun s => (s.fresh, { s with fresh := s.fresh + 1 })

def budgetExceeded : String := "selfcheck: budget exceeded"

/-- Count an evaluation step against the budget of the running self-check. -/
@[inline] def tick : M Unit := do
  let s ← get
  if s.limit != 0 then
    if s.steps ≥ s.limit then throw budgetExceeded
    set { s with steps := s.steps + 1 }

def recordViolation (msg : String) : M Unit :=
  modify fun s => { s with violations := s.violations.push msg }

/-- Record a term for self-checking, if enabled. -/
def scPush (ctx : Ctx) (tm : Tm) (ty : Val) (label : String) : M Unit :=
  modify fun s => if s.selfcheck then { s with pending := s.pending.push ⟨ctx, tm, ty, label⟩ } else s

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
