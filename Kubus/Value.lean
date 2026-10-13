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
  /-- pattern-matching function `f` with parameters `env` -/
  | split (f : String) (k : Nat) (env : List EnvE)
  /-- The global `g^k` applied to the spine `sp` (innermost argument first), unfolded only on
  demand (`unfoldM`): definitions are printed folded, applications of the same global are
  compared without unfolding them, and unfolding a body does not unfold the globals in it. -/
  | glued (g : String) (k : Nat) (sp : List EnvE)
  -- neutrals
  | var (lvl : Nat) (ty : Val)
  | gvar (n : String) (ty : Val)
  | app (f a : Val)
  | fst (p : Val)
  | snd (p : Val)
  | papp (p : Val) (r : Formula)
  | splitApp (f : String) (k : Nat) (env : List EnvE) (arg : Val)
  /-- stuck transport along `line` (a line of types), constant where `φ` holds; in a Π-type
  it computes when applied -/
  | transp (line : Val) (φ : Formula) (u0 : Val)
  /-- stuck homogeneous composition (not in a higher inductive type); `sys` holds lines; in a
  Π-type it computes when applied -/
  | hcomp (ty : Val) (u0 : Val) (sys : List (Face × Val))
  | unglue (u : Val) (base : Val) (sys : List (Face × Val))

inductive EnvE
  | v (v : Val)
  | d (r : Formula)
end

instance : Inhabited Val := ⟨.univ 0⟩
instance : Inhabited EnvE := ⟨.d Formula.zero⟩

abbrev Env := List EnvE

mutual
/-- Whether the atom `i` occurs free in a value (if not, substituting for it is the identity). -/
partial def Val.hasAtomRef (i : Atom) : Val → Bool
  | .univ _ => false
  | .pi _ a env _ | .sigma _ a env _ => a.hasAtomRef i || envHasAtom i env
  | .lam _ env _ | .split _ _ env => envHasAtom i env
  | .pair a b => a.hasAtomRef i || b.hasAtomRef i
  | .piI l => l.hasAtomRef i
  | .pathP l a b => l.hasAtomRef i || a.hasAtomRef i || b.hasAtomRef i
  | .plam j b => j != i && b.hasAtomRef i
  | .data _ _ ps | .con _ ps => ps.any (·.hasAtomRef i)
  | .pcon _ as ds => as.any (·.hasAtomRef i) || ds.any (·.mentions i)
  | .hcompF ty u sys => ty.hasAtomRef i || u.hasAtomRef i || sysHasAtom i sys
  | .glueTy b sys | .glue b sys => b.hasAtomRef i || sysHasAtom i sys
  | .glued _ _ sp => envHasAtom i sp
  | .var _ ty | .gvar _ ty => ty.hasAtomRef i
  | .app f a => f.hasAtomRef i || a.hasAtomRef i
  | .fst p | .snd p => p.hasAtomRef i
  | .papp p r => p.hasAtomRef i || r.mentions i
  | .splitApp _ _ env a => envHasAtom i env || a.hasAtomRef i
  | .hcomp l u sys | .unglue u l sys => l.hasAtomRef i || u.hasAtomRef i || sysHasAtom i sys
  | .transp l φ u => l.hasAtomRef i || φ.mentions i || u.hasAtomRef i

partial def envHasAtom (i : Atom) : Env → Bool
  | [] => false
  | .v v :: env => v.hasAtomRef i || envHasAtom i env
  | .d r :: env => r.mentions i || envHasAtom i env

partial def sysHasAtom (i : Atom) : List (Face × Val) → Bool
  | [] => false
  | (α, v) :: sys => α.mentions i || v.hasAtomRef i || sysHasAtom i sys
end

/-- `Val.hasAtomRef`, exploring each shared node only once (values are DAGs: closures share
their environments). -/
unsafe def Val.hasAtomUnsafe (i : Atom) (v : Val) : Bool :=
  -- small values: a plain traversal (no table); large ones: each shared node once
  match small v 256 with
  | some (b, _) => b
  | none => (go v).run' {}
where
  /-- `some (occurs, remaining budget)`, or `none` when the budget runs out. -/
  small (v : Val) (n : Nat) : Option (Bool × Nat) :=
    if n == 0 then none else
    let n := n - 1
    let rec many : List Val → Nat → Option (Bool × Nat)
      | [], n => some (false, n)
      | x :: xs, n => do
        let (b, n) ← small x n
        if b then some (true, n) else many xs n
    let rec env : Env → Nat → Option (Bool × Nat)
      | [], n => some (false, n)
      | .d r :: rest, n => if r.mentions i then some (true, n) else env rest n
      | .v x :: rest, n => do
        let (b, n) ← small x n
        if b then some (true, n) else env rest n
    let rec sys : List (Face × Val) → Nat → Option (Bool × Nat)
      | [], n => some (false, n)
      | (α, x) :: rest, n =>
        if α.mentions i then some (true, n) else do
        let (b, n) ← small x n
        if b then some (true, n) else sys rest n
    match v with
    | .univ _ => some (false, n)
    | .pi _ a e _ | .sigma _ a e _ => do
      let (b, n) ← small a n
      if b then some (true, n) else env e n
    | .lam _ e _ | .split _ _ e | .glued _ _ e => env e n
    | .pair a b | .app a b => many [a, b] n
    | .piI l | .fst l | .snd l | .var _ l | .gvar _ l => small l n
    | .pathP l a b => many [l, a, b] n
    | .plam j b => if j == i then some (false, n) else small b n
    | .data _ _ ps | .con _ ps => many ps n
    | .pcon _ as ds => if ds.any (·.mentions i) then some (true, n) else many as n
    | .hcompF ty u s | .hcomp ty u s | .unglue u ty s => do
      let (b, n) ← many [ty, u] n
      if b then some (true, n) else sys s n
    | .glueTy b s | .glue b s => do
      let (x, n) ← small b n
      if x then some (true, n) else sys s n
    | .papp p r => if r.mentions i then some (true, n) else small p n
    | .splitApp _ _ e a => do
      let (b, n) ← small a n
      if b then some (true, n) else env e n
    | .transp l φ u => if φ.mentions i then some (true, n) else many [l, u] n
  seen {α : Type} (x : α) : StateM (Std.HashSet USize) Bool := do
    let p := ptrAddrUnsafe x
    if (← get).contains p then return true
    modify (·.insert p)
    return false
  go (v : Val) : StateM (Std.HashSet USize) Bool := do
    if ← seen v then return false
    match v with
    | .univ _ => return false
    | .pi _ a env _ | .sigma _ a env _ => return (← go a) || (← goEnv env)
    | .lam _ env _ | .split _ _ env => goEnv env
    | .pair a b => return (← go a) || (← go b)
    | .piI l => go l
    | .pathP l a b => return (← go l) || (← go a) || (← go b)
    | .plam j b => return j != i && (← go b)
    | .data _ _ ps | .con _ ps => ps.anyM go
    | .pcon _ as ds => return (← as.anyM go) || ds.any (·.mentions i)
    | .hcompF ty u sys => return (← go ty) || (← go u) || (← goSys sys)
    | .glueTy b sys | .glue b sys => return (← go b) || (← goSys sys)
    | .glued _ _ sp => goEnv sp
    | .var _ ty | .gvar _ ty => go ty
    | .app f a => return (← go f) || (← go a)
    | .fst p | .snd p => go p
    | .papp p r => return r.mentions i || (← go p)
    | .splitApp _ _ env a => return (← goEnv env) || (← go a)
    | .hcomp l u sys | .unglue u l sys => return (← go l) || (← go u) || (← goSys sys)
    | .transp l φ u => return φ.mentions i || (← go l) || (← go u)
  goEnv (env : Env) : StateM (Std.HashSet USize) Bool := do
    match env with
    | [] => return false
    | e :: rest =>
      if ← seen env then return false
      let here ← match e with
        | .v v => go v
        | .d r => pure (r.mentions i)
      return here || (← goEnv rest)
  goSys (sys : List (Face × Val)) : StateM (Std.HashSet USize) Bool :=
    sys.anyM fun (α, v) => do return α.mentions i || (← go v)

/-- Whether the atom `i` occurs free in a value (if not, substituting for it is the identity). -/
@[implemented_by Val.hasAtomUnsafe]
def Val.hasAtom (i : Atom) (v : Val) : Bool := v.hasAtomRef i

def Val.isNeutral : Val → Bool
  | .var .. | .gvar .. | .app .. | .fst _ | .snd _ | .papp .. | .splitApp .. | .transp .. | .hcomp ..
  | .unglue .. => true
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
  /-- pairs of values found convertible (by address; the values are kept so that addresses are
  not reused); cleared when metavariable solutions are undone or a declaration starts -/
  convCache : Std.HashMap (USize × USize) (Val × Val) := {}

abbrev M := StateT St (Except String)

unsafe def addrUnsafe {α : Type} (x : α) : USize := ptrAddrUnsafe x

/-- The address of a value, for caches that keep the value alive (the reference
implementation returns 0; caches keyed by it are only used through `sameAddr`). -/
@[implemented_by addrUnsafe]
def addr {α : Type} (_x : α) : USize := 0

unsafe def sameAddrUnsafe {α : Type} (x y : α) : Bool := ptrAddrUnsafe x == ptrAddrUnsafe y

/-- Whether two values are the same object (the reference implementation: never). -/
@[implemented_by sameAddrUnsafe]
def sameAddr {α : Type} (_x _y : α) : Bool := false

/-- Undo metavariable solutions (and the conversions that may have used them). -/
def restoreMetas (saved : Array MetaInfo) : M Unit :=
  modify fun s => { s with metas := saved, convCache := {} }

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
