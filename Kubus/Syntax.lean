import Kubus.Interval

namespace Kubus

/-! ## Core syntax (de Bruijn indices; term and interval variables share one context) -/

inductive ITm
  | zero | one
  | var (i : Nat)
  | neg (r : ITm)
  | and (r s : ITm)
  | or (r s : ITm)
  deriving Inhabited, Repr, BEq

/-- Systems in core terms: interval formula keys (`φ` means `φ = 1`). -/
abbrev TSys (α : Type) := List (ITm × α)

inductive Tm
  | var (i : Nat)
  /-- a global definition, with all universe levels displaced by `k` -/
  | glob (n : String) (k : Nat)
  | univ (l : Nat)
  | pi (x : String) (a b : Tm)
  | lam (x : String) (b : Tm)
  | app (f a : Tm)
  | sigma (x : String) (a b : Tm)
  | pair (a b : Tm)
  | fst (t : Tm)
  | snd (t : Tm)
  /-- `(i : I) → A`, binds a dimension -/
  | piI (i : String) (a : Tm)
  /-- `PathP a u v`, where `a` is a line of types -/
  | pathP (a u v : Tm)
  | plam (i : String) (b : Tm)
  | papp (t : Tm) (r : ITm)
  /-- `comp i A [φ ↦ u] u0`: `A` and the `u`s bind `i`. -/
  | comp (i : String) (a : Tm) (sys : List (ITm × Tm)) (u0 : Tm)
  /-- `hcomp i A [φ ↦ u] u0`: only the `u`s bind `i`. -/
  | hcomp (i : String) (a : Tm) (sys : List (ITm × Tm)) (u0 : Tm)
  /-- `fill i A [φ ↦ u] u0`: a path; `A` and the `u`s bind `i`. -/
  | fill (i : String) (a : Tm) (sys : List (ITm × Tm)) (u0 : Tm)
  | glueTy (a : Tm) (sys : List (ITm × Tm))
  | glue (sys : List (ITm × Tm)) (a : Tm)
  | unglue (u : Tm) (base : Tm) (sys : List (ITm × Tm))
  /-- Composition in the universe; only produced by read-back. -/
  | compU (a : Tm) (sys : List (ITm × Tm))
  | unglueU (u : Tm) (base : Tm) (sys : List (ITm × Tm))
  | data (d : String) (k : Nat) (ps : List Tm)
  | con (c : String) (args : List Tm) (dims : List ITm)
  /-- The pattern-matching function body of the global `f`; its environment holds `f`'s parameters. -/
  | split (f : String) (k : Nat)
  | letE (x : String) (t b : Tm)
  deriving Inhabited, Repr, BEq

def ITm.occurs (k : Nat) : ITm → Bool
  | .var i => i == k
  | .neg r => r.occurs k
  | .and r s | .or r s => r.occurs k || s.occurs k
  | _ => false

mutual
partial def Tm.occurs (k : Nat) : Tm → Bool
  | .var i => i == k
  | .pi _ a b | .sigma _ a b => a.occurs k || b.occurs (k + 1)
  | .lam _ b | .piI _ b | .plam _ b => b.occurs (k + 1)
  | .app f a | .pair f a => f.occurs k || a.occurs k
  | .fst t | .snd t => t.occurs k
  | .pathP a u v => a.occurs k || u.occurs k || v.occurs k
  | .papp t r => t.occurs k || r.occurs k
  | .comp _ a sys u0 | .fill _ a sys u0 => a.occurs (k + 1) || sysOccurs (k + 1) k sys || u0.occurs k
  | .hcomp _ a sys u0 => a.occurs k || sysOccurs (k + 1) k sys || u0.occurs k
  | .glueTy a sys | .glue sys a | .compU a sys => a.occurs k || sysOccurs k k sys
  | .unglue u b sys | .unglueU u b sys => u.occurs k || b.occurs k || sysOccurs k k sys
  | .data _ _ ps => ps.any (·.occurs k)
  | .con _ as ds => as.any (·.occurs k) || ds.any (·.occurs k)
  | .letE _ t b => t.occurs k || b.occurs (k + 1)
  | _ => false

partial def sysOccurs (kElem kKey : Nat) (sys : List (ITm × Tm)) : Bool :=
  sys.any fun (r, t) => r.occurs kKey || t.occurs kElem
end

/-- Displace all universe levels by `k`. -/
partial def Tm.lift (k : Nat) (t : Tm) : Tm :=
  if k == 0 then t else
  let l := Tm.lift k
  let ls := fun (sys : List (ITm × Tm)) => sys.map fun (r, t) => (r, l t)
  match t with
  | .univ n => .univ (n + k)
  | .glob n j => .glob n (j + k)
  | .data d j ps => .data d (j + k) (ps.map l)
  | .split f j => .split f (j + k)
  | .var i => .var i
  | .pi x a b => .pi x (l a) (l b)
  | .lam x b => .lam x (l b)
  | .app f a => .app (l f) (l a)
  | .sigma x a b => .sigma x (l a) (l b)
  | .pair a b => .pair (l a) (l b)
  | .fst t => .fst (l t)
  | .snd t => .snd (l t)
  | .piI i a => .piI i (l a)
  | .pathP a u v => .pathP (l a) (l u) (l v)
  | .plam i b => .plam i (l b)
  | .papp t r => .papp (l t) r
  | .comp i a sys u0 => .comp i (l a) (ls sys) (l u0)
  | .hcomp i a sys u0 => .hcomp i (l a) (ls sys) (l u0)
  | .fill i a sys u0 => .fill i (l a) (ls sys) (l u0)
  | .glueTy a sys => .glueTy (l a) (ls sys)
  | .glue sys a => .glue (ls sys) (l a)
  | .unglue u b sys => .unglue (l u) (l b) (ls sys)
  | .compU a sys => .compU (l a) (ls sys)
  | .unglueU u b sys => .unglueU (l u) (l b) (ls sys)
  | .con c as ds => .con c (as.map l) ds
  | .letE x t b => .letE x (l t) (l b)

/-! ## Implicit binders and metavariables

A binder name of the form `{x}` marks an implicit binder (in `pi`, `lam`, surface binders and
values). Implicitness only guides elaboration; conversion ignores binder names.

Metavariables only exist during the elaboration of one declaration and are zonked away before
it is added. In core terms a metavariable is the global `?mN`, applied to the variables of the
context it was created in. -/

def implName (x : String) : String := "{" ++ x ++ "}"
def isImplName (x : String) : Bool := x.startsWith "{" && x.endsWith "}" && x.length ≥ 2
def plainName (x : String) : String := if isImplName x then ((x.drop 1).dropEnd 1).toString else x

def metaName (m : Nat) : String := s!"?m{m}"
def metaId? (n : String) : Option Nat := if n.startsWith "?m" then (n.drop 2).toString.toNat? else none

def ITm.mapVars (f : Nat → Nat → ITm) (c : Nat) : ITm → ITm
  | .var i => f c i
  | .neg r => .neg (r.mapVars f c)
  | .and r s => .and (r.mapVars f c) (s.mapVars f c)
  | .or r s => .or (r.mapVars f c) (s.mapVars f c)
  | r => r

/-- Map the free variables (term and interval variables share one index space); `c` counts
the binders crossed. -/
partial def Tm.mapVars (f : Nat → Nat → Tm) (g : Nat → Nat → ITm) (c : Nat) : Tm → Tm
  | .var i => f c i
  | .pi x a b => .pi x (a.mapVars f g c) (b.mapVars f g (c + 1))
  | .sigma x a b => .sigma x (a.mapVars f g c) (b.mapVars f g (c + 1))
  | .lam x b => .lam x (b.mapVars f g (c + 1))
  | .app a b => .app (a.mapVars f g c) (b.mapVars f g c)
  | .pair a b => .pair (a.mapVars f g c) (b.mapVars f g c)
  | .fst t => .fst (t.mapVars f g c)
  | .snd t => .snd (t.mapVars f g c)
  | .piI i a => .piI i (a.mapVars f g (c + 1))
  | .pathP a u v => .pathP (a.mapVars f g c) (u.mapVars f g c) (v.mapVars f g c)
  | .plam i b => .plam i (b.mapVars f g (c + 1))
  | .papp t r => .papp (t.mapVars f g c) (r.mapVars g c)
  | .comp i a sys u0 => .comp i (a.mapVars f g (c + 1)) (sysUnder sys) (u0.mapVars f g c)
  | .hcomp i a sys u0 => .hcomp i (a.mapVars f g c) (sysUnder sys) (u0.mapVars f g c)
  | .fill i a sys u0 => .fill i (a.mapVars f g (c + 1)) (sysUnder sys) (u0.mapVars f g c)
  | .glueTy a sys => .glueTy (a.mapVars f g c) (sys0 sys)
  | .glue sys a => .glue (sys0 sys) (a.mapVars f g c)
  | .unglue u b sys => .unglue (u.mapVars f g c) (b.mapVars f g c) (sys0 sys)
  | .compU a sys => .compU (a.mapVars f g c) (sys0 sys)
  | .unglueU u b sys => .unglueU (u.mapVars f g c) (b.mapVars f g c) (sys0 sys)
  | .data d k ps => .data d k (ps.map (·.mapVars f g c))
  | .con n as ds => .con n (as.map (·.mapVars f g c)) (ds.map (·.mapVars g c))
  | .letE x t b => .letE x (t.mapVars f g c) (b.mapVars f g (c + 1))
  | t => t
where
  sysUnder (sys : List (ITm × Tm)) := sys.map fun (r, t) => (r.mapVars g c, t.mapVars f g (c + 1))
  sys0 (sys : List (ITm × Tm)) := sys.map fun (r, t) => (r.mapVars g c, t.mapVars f g c)

def Tm.shift (n : Nat) (t : Tm) : Tm :=
  if n == 0 then t else
  t.mapVars (fun c i => .var (if i ≥ c then i + n else i)) (fun c i => .var (if i ≥ c then i + n else i)) 0

def ITm.shift (n : Nat) (r : ITm) : ITm :=
  r.mapVars (fun c i => .var (if i ≥ c then i + n else i)) 0

/-- Apply `f` to the immediate subterms; `f` also gets the number of binders crossed. -/
def Tm.mapChildrenM {m : Type → Type} [Monad m] (f : Nat → Tm → m Tm) : Tm → m Tm
  | .pi x a b => return .pi x (← f 0 a) (← f 1 b)
  | .sigma x a b => return .sigma x (← f 0 a) (← f 1 b)
  | .lam x b => return .lam x (← f 1 b)
  | .app a b => return .app (← f 0 a) (← f 0 b)
  | .pair a b => return .pair (← f 0 a) (← f 0 b)
  | .fst t => return .fst (← f 0 t)
  | .snd t => return .snd (← f 0 t)
  | .piI i a => return .piI i (← f 1 a)
  | .pathP a u v => return .pathP (← f 0 a) (← f 0 u) (← f 0 v)
  | .plam i b => return .plam i (← f 1 b)
  | .papp t r => return .papp (← f 0 t) r
  | .comp i a sys u0 => return .comp i (← f 1 a) (← sysM 1 sys) (← f 0 u0)
  | .hcomp i a sys u0 => return .hcomp i (← f 0 a) (← sysM 1 sys) (← f 0 u0)
  | .fill i a sys u0 => return .fill i (← f 1 a) (← sysM 1 sys) (← f 0 u0)
  | .glueTy a sys => return .glueTy (← f 0 a) (← sysM 0 sys)
  | .glue sys a => return .glue (← sysM 0 sys) (← f 0 a)
  | .unglue u b sys => return .unglue (← f 0 u) (← f 0 b) (← sysM 0 sys)
  | .compU a sys => return .compU (← f 0 a) (← sysM 0 sys)
  | .unglueU u b sys => return .unglueU (← f 0 u) (← f 0 b) (← sysM 0 sys)
  | .data d k ps => return .data d k (← ps.mapM (f 0))
  | .con n as ds => return .con n (← as.mapM (f 0)) ds
  | .letE x t b => return .letE x (← f 0 t) (← f 1 b)
  | t => pure t
where
  sysM (n : Nat) (sys : List (ITm × Tm)) : m (List (ITm × Tm)) := sys.mapM fun (r, t) => return (r, ← f n t)

/-- An argument of an application spine. -/
inductive SArg
  | tm (t : Tm)
  | dim (r : ITm)
  deriving Inhabited

/-- Application spine of a core term. -/
def Tm.sargs : Tm → Tm × Array SArg
  | .app f a => let (h, as) := f.sargs; (h, as.push (.tm a))
  | .papp f r => let (h, as) := f.sargs; (h, as.push (.dim r))
  | t => (t, #[])

def SArg.apply (t : Tm) : SArg → Tm
  | .tm a => .app t a
  | .dim r => .papp t r

/-- Substitute `args` for the outermost `args.length` binders' variables: index `j < n` of `t`
becomes `args[n - 1 - j]`, and free indices `j ≥ n` become `j - n`. -/
def Tm.substArgs (t : Tm) (args : Array SArg) : Tm :=
  let n := args.size
  t.mapVars
    (fun c i => if i < c then .var i else
      let j := i - c
      if h : j < n then (match args[n - 1 - j] with | .tm a => a.shift c | .dim _ => .var i)
      else .var (i - n))
    (fun c i => if i < c then .var i else
      let j := i - c
      if h : j < n then (match args[n - 1 - j] with | .dim r => r.shift c | .tm _ => .var i)
      else .var (i - n)) 0

/-! ## Surface syntax -/

structure Pos where
  line : Nat
  col : Nat
  /-- end of the source range (exclusive), if known (`eline = 0` otherwise) -/
  eline : Nat := 0
  ecol : Nat := 0
  deriving Inhabited, Repr

inductive Raw
  | var (x : String)
  /-- `x^k`: a global with universe levels displaced by `k` -/
  | lift (x : String) (k : Nat)
  | univ (l : Nat)
  | intervalTy
  | pi (x : String) (a b : Raw)
  | sigma (x : String) (a b : Raw)
  | lam (x : String) (ty : Option Raw) (b : Raw)
  | app (f a : Raw)
  | pair (a b : Raw)
  | fst (t : Raw)
  | snd (t : Raw)
  | path (a u v : Raw)
  | pathP (a u v : Raw)
  | izero | ione
  | ineg (r : Raw)
  | iand (r s : Raw)
  | ior (r s : Raw)
  | ieq (r : Raw) (d : Bool)
  | comp (i : String) (a : Raw) (sys : List (Raw × Raw)) (u0 : Raw)
  | hcomp (i : String) (a : Raw) (sys : List (Raw × Raw)) (u0 : Raw)
  | fill (i : String) (a : Raw) (sys : List (Raw × Raw)) (u0 : Raw)
  | glueTy (a : Raw) (sys : List (Raw × Raw))
  | glue (sys : List (Raw × Raw)) (a : Raw)
  | unglue (u : Raw)
  | ann (t a : Raw)
  | hole
  | letE (x : String) (ty : Option Raw) (t b : Raw)
  | loc (p : Pos) (t : Raw)
  /-- `f {a}` (`name = none`) or `f {x := a}` -/
  | iapp (f : Raw) (name : Option String) (a : Raw)
  /-- `@f`: no implicit arguments are inserted; implicit binders take explicit arguments -/
  | explicit (x : String)
  deriving Inhabited, Repr

structure Binder where
  name : String
  ty : Raw
  deriving Inhabited, Repr

/-- Patterns. A variable pattern whose name is a constructor is that constructor. -/
inductive Pat
  | var (x : String) (pos : Pos)
  | con (c : String) (args : List Pat) (pos : Pos)
  deriving Inhabited, Repr

def Pat.pos : Pat → Pos
  | .var _ p | .con _ _ p => p

/-- A clause `| p1, ..., pn => body`. -/
structure Clause' where
  pats : List Pat
  body : Raw
  pos : Pos
  deriving Inhabited, Repr

structure CtorDecl where
  name : String
  args : List Binder
  boundary : List (Raw × Raw)
  pos : Pos
  deriving Inhabited, Repr

inductive Decl
  | defn (name : String) (params : List Binder) (ty : Raw) (body : Raw) (pos : Pos)
  | defSplit (name : String) (params : List Binder) (ty : Raw) (clauses : List Clause') (pos : Pos)
  | data (name : String) (params : List Binder) (level : Nat) (ctors : List CtorDecl) (pos : Pos)
  | eval (t : Raw) (pos : Pos)
  | check (t : Raw) (pos : Pos)
  | importFile (name : String) (pos : Pos)
  deriving Inhabited, Repr

end Kubus
