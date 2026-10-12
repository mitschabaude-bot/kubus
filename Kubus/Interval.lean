/-!
# The De Morgan interval, faces and systems

Formulas are kept in a canonical disjunctive normal form, so that equality of
formulas in the free De Morgan algebra is structural equality.
-/

namespace Kubus

abbrev Atom := Nat

inductive Dir | zero | one
  deriving BEq, DecidableEq, Repr, Inhabited

def Dir.neg : Dir → Dir
  | .zero => .one
  | .one => .zero

/-- A literal `i` (pos = true) or `~i` (pos = false). -/
structure Lit where
  atom : Atom
  pos : Bool
  deriving BEq, DecidableEq, Repr, Inhabited

def Lit.key (l : Lit) : Nat := 2 * l.atom + (if l.pos then 1 else 0)

/-- A conjunction of literals, sorted by `Lit.key`, without duplicates. -/
abbrev Clause := List Lit

/-- Sorted union of two clauses. -/
def Clause.union : Clause → Clause → Clause
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x.key < y.key then x :: Clause.union xs (y :: ys)
    else if y.key < x.key then y :: Clause.union (x :: xs) ys
    else x :: Clause.union xs ys

def Clause.subset (c d : Clause) : Bool := c.all (d.contains ·)

def Clause.lt : Clause → Clause → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => x.key < y.key || (x.key == y.key && Clause.lt xs ys)

/-- A formula in canonical DNF: `[]` is 0, `[[]]` is 1. -/
structure Formula where
  dnf : List Clause
  deriving BEq, Inhabited, Repr

namespace Formula

def zero : Formula := ⟨[]⟩
def one : Formula := ⟨[[]]⟩
def ofDir : Dir → Formula
  | .zero => zero
  | .one => one
def atom (i : Atom) : Formula := ⟨[[⟨i, true⟩]]⟩
def natom (i : Atom) : Formula := ⟨[[⟨i, false⟩]]⟩

private def insertSorted (c : Clause) : List Clause → List Clause
  | [] => [c]
  | d :: ds => if Clause.lt c d then c :: d :: ds else if c == d then d :: ds else d :: insertSorted c ds

/-- Sort, dedupe and apply absorption. -/
def normalize (cs : List Clause) : Formula :=
  let sorted := cs.foldl (fun acc c => insertSorted c acc) []
  let absorbed := sorted.filter fun c => !(sorted.any fun d => d != c && d.subset c)
  ⟨absorbed⟩

def or (a b : Formula) : Formula := normalize (a.dnf ++ b.dnf)

def and (a b : Formula) : Formula :=
  normalize (a.dnf.flatMap fun c => b.dnf.map fun d => c.union d)

def neg (a : Formula) : Formula :=
  a.dnf.foldl (fun acc c => acc.and ⟨c.map fun l => [{ l with pos := !l.pos }]⟩) one

def isZero (a : Formula) : Bool := a.dnf.isEmpty
def isOne (a : Formula) : Bool := a.dnf == [[]]

def toDir? (a : Formula) : Option Dir :=
  if a.isZero then some .zero else if a.isOne then some .one else none

def support (a : Formula) : List Atom :=
  a.dnf.foldl (fun acc c => c.foldl (fun acc l => if acc.contains l.atom then acc else l.atom :: acc) acc) []

def mentions (a : Formula) (i : Atom) : Bool := a.dnf.any (·.any (·.atom == i))

/-- Substitute the formula `r` for the atom `i`. -/
def subst (a : Formula) (i : Atom) (r : Formula) : Formula :=
  if !a.mentions i then a else
  let litF (l : Lit) : Formula :=
    if l.atom == i then (if l.pos then r else r.neg) else ⟨[[l]]⟩
  a.dnf.foldl (fun acc c => acc.or (c.foldl (fun acc' l => acc'.and (litF l)) one)) zero

end Formula

/-- A face: a consistent assignment of directions to atoms, sorted by atom. -/
abbrev Face := List (Atom × Dir)

namespace Face

def eps : Face := []

def lookup (α : Face) (i : Atom) : Option Dir := (α.find? (·.1 == i)).map (·.2)

def erase (α : Face) (i : Atom) : Face := α.filter (·.1 != i)

def mentions (α : Face) (i : Atom) : Bool := α.any (·.1 == i)

/-- Union of two faces, if compatible. -/
def meet? : Face → Face → Option Face
  | [], β => some β
  | α, [] => some α
  | (i, d) :: α, (j, e) :: β =>
    if i < j then ((i, d) :: ·) <$> meet? α ((j, e) :: β)
    else if j < i then ((j, e) :: ·) <$> meet? ((i, d) :: α) β
    else if d == e then ((i, d) :: ·) <$> meet? α β
    else none

def compatible (α β : Face) : Bool := (meet? α β).isSome

/-- `α ≤ β`: `α` is a sub-face of `β` (it contains all constraints of `β`). -/
def leq (α β : Face) : Bool := β.all fun (i, d) => α.lookup i == some d

/-- Constraints of `δ` on atoms not constrained by `β`. -/
def minus (δ β : Face) : Face := δ.filter fun (i, _) => !β.mentions i

def single (i : Atom) (d : Dir) : Face := [(i, d)]

/-- Formula restricted to a face. -/
def applyF (α : Face) (r : Formula) : Formula :=
  α.foldl (fun r (i, d) => r.subst i (Formula.ofDir d)) r

end Face

/-- The faces on which a formula is 1, as an antichain. -/
def Formula.faces (r : Formula) : List Face :=
  let fs := r.dnf.filterMap fun c =>
    c.foldl (fun acc l => acc.bind fun α =>
      let d := if l.pos then Dir.one else Dir.zero
      match α.lookup l.atom with
      | some d' => if d == d' then some α else none
      | none => some (α ++ [(l.atom, d)])) (some [])
  let fs := fs.map fun α => α.mergeSort (fun a b => a.1 ≤ b.1)
  fs.filter fun α => !(fs.any fun β => β != α && α.leq β)

/-- Faces on which `r` equals `d`. -/
def Formula.inv (r : Formula) : Dir → List Face
  | .one => r.faces
  | .zero => r.neg.faces

/-- Partial elements: a list of faces with values. -/
abbrev System (α : Type) := List (Face × α)

namespace System

def insert {α} (f : Face) (v : α) (s : System α) : System α :=
  if s.any (fun (g, _) => f.leq g) then s
  else (f, v) :: s.filter fun (g, _) => !g.leq f

def ofList {α} (l : List (Face × α)) : System α := l.foldr (fun (f, v) s => insert f v s) []

def union {α} (s t : System α) : System α := s.foldr (fun (f, v) acc => insert f v acc) t

def eps? {α} (s : System α) : Option α := (s.find? (·.1.isEmpty)).map (·.2)

def faces {α} (s : System α) : List Face := s.map (·.1)

end System

end Kubus
