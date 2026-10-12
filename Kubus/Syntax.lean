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
  | glob (n : String)
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
  | data (d : String) (ps : List Tm)
  | con (c : String) (args : List Tm) (dims : List ITm)
  /-- The pattern-matching function body of the global `f`; its environment holds `f`'s parameters. -/
  | split (f : String)
  | letE (x : String) (t b : Tm)
  deriving Inhabited, Repr

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
  | .data _ ps => ps.any (·.occurs k)
  | .con _ as ds => as.any (·.occurs k) || ds.any (·.occurs k)
  | .letE _ t b => t.occurs k || b.occurs (k + 1)
  | _ => false

partial def sysOccurs (kElem kKey : Nat) (sys : List (ITm × Tm)) : Bool :=
  sys.any fun (r, t) => r.occurs kKey || t.occurs kElem
end

/-! ## Surface syntax -/

structure Pos where
  line : Nat
  col : Nat
  deriving Inhabited, Repr

inductive Raw
  | var (x : String)
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
  deriving Inhabited, Repr

structure Binder where
  name : String
  ty : Raw
  deriving Inhabited, Repr

structure Clause' where
  ctor : String
  vars : List String
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
