/-!
# Kubus Core: syntax

Two sorts of de Bruijn indices: term variables and interval variables.
See `docs/core-theory.md`.
-/

namespace KubusCore

/-! ## The interval -/

inductive I where
  | zero
  | one
  | var (i : Nat)
  | neg (r : I)
  | and (r s : I)
  | or (r s : I)
  deriving DecidableEq, Repr, Inhabited

namespace I

def subst (σ : Nat → I) : I → I
  | zero => zero
  | one => one
  | var i => σ i
  | neg r => neg (r.subst σ)
  | and r s => and (r.subst σ) (s.subst σ)
  | or r s => or (r.subst σ) (s.subst σ)

def ren (ρ : Nat → Nat) (r : I) : I := r.subst fun i => var (ρ i)

def shift (r : I) : I := r.ren Nat.succ

/-- Lift a substitution under an interval binder. -/
def up (σ : Nat → I) : Nat → I
  | 0 => var 0
  | n + 1 => (σ n).shift

/-- Instantiate interval variable 0. -/
def inst0 (s : I) : Nat → I
  | 0 => s
  | n + 1 => var n

/-- All variables are below `n`. -/
def Scoped (n : Nat) : I → Prop
  | zero | one => True
  | var i => i < n
  | neg r => r.Scoped n
  | and r s | or r s => r.Scoped n ∧ s.Scoped n

def scopedB (n : Nat) : I → Bool
  | zero | one => true
  | var i => decide (i < n)
  | neg r => r.scopedB n
  | and r s | or r s => r.scopedB n && s.scopedB n

theorem scopedB_iff (n : Nat) (r : I) : r.scopedB n = true ↔ r.Scoped n := by
  induction r <;> simp_all [scopedB, Scoped]

instance (n : Nat) (r : I) : Decidable (r.Scoped n) := decidable_of_iff _ (scopedB_iff n r)

/-! ### Equality: the free De Morgan algebra, via the four-element De Morgan algebra -/

/-- The four-element De Morgan algebra `{0, a, b, 1}` with `~a = a`, `~b = b`. -/
inductive M4 where
  | zero | a | b | one
  deriving DecidableEq, Repr, Inhabited

namespace M4

/-- `M4` as pairs of booleans `(x, y)`, ordered componentwise, with `~(x, y) = (¬y, ¬x)`. -/
def toPair : M4 → Bool × Bool
  | zero => (false, false)
  | a => (true, false)
  | b => (false, true)
  | one => (true, true)

def ofPair : Bool × Bool → M4
  | (false, false) => zero
  | (true, false) => a
  | (false, true) => b
  | (true, true) => one

def meet (x y : M4) : M4 := ofPair (x.toPair.1 && y.toPair.1, x.toPair.2 && y.toPair.2)
def join (x y : M4) : M4 := ofPair (x.toPair.1 || y.toPair.1, x.toPair.2 || y.toPair.2)
def neg (x : M4) : M4 := ofPair (!x.toPair.2, !x.toPair.1)

end M4

def eval (ρ : Nat → M4) : I → M4
  | zero => .zero
  | one => .one
  | var i => ρ i
  | neg r => (r.eval ρ).neg
  | and r s => (r.eval ρ).meet (s.eval ρ)
  | or r s => (r.eval ρ).join (s.eval ρ)

/-- Equality of interval terms: equality in the free De Morgan algebra. -/
def Eq (r s : I) : Prop := ∀ ρ : Nat → M4, r.eval ρ = s.eval ρ

/-! ### Cofibrations: the face lattice -/

/-- A face: a conjunction of `i = 1` (true) and `i = 0` (false) constraints. -/
abbrev Face := List (Nat × Bool)

def Face.consistent (α : Face) : Bool :=
  α.all fun (i, d) => !α.contains (i, !d)

/-- Disjunctive normal form of `r = 1` (if `pos`) or `r = 0` (if not), as a list of faces. -/
def dnf : Bool → I → List Face
  | true, zero => []
  | false, zero => [[]]
  | true, one => [[]]
  | false, one => []
  | pos, var i => [[(i, pos)]]
  | pos, neg r => dnf (!pos) r
  | true, and r s => (dnf true r).flatMap fun c => (dnf true s).map (c ++ ·)
  | false, and r s => dnf false r ++ dnf false s
  | true, or r s => dnf true r ++ dnf true s
  | false, or r s => (dnf false r).flatMap fun c => (dnf false s).map (c ++ ·)

/-- The faces of the cofibration `r = 1`. -/
def faces (r : I) : List Face := (dnf true r).filter Face.consistent

/-- Entailment in the face lattice: every face of `φ` lies in some face of `ψ`. -/
def entails (φ ψ : I) : Bool :=
  φ.faces.all fun c => ψ.faces.any fun d => d.all (c.contains ·)

def Entails (φ ψ : I) : Prop := entails φ ψ = true

instance (φ ψ : I) : Decidable (Entails φ ψ) := inferInstanceAs (Decidable (_ = true))

/-- The cofibration `i = d`. -/
def lit (i : Nat) : Bool → I
  | true => var i
  | false => neg (var i)

def ofDir : Bool → I
  | true => one
  | false => zero

def ofFace (α : Face) : I := α.foldr (fun (i, d) r => and (lit i d) r) one

def ofFaces (cs : List Face) : I := cs.foldr (fun α r => or (ofFace α) r) zero

/-- `∀ i. φ` for the interval variable 0: the faces of `φ` that do not mention it,
with the remaining variables lowered. -/
def forall0 (φ : I) : I :=
  ofFaces ((φ.faces.filter fun α => α.all (·.1 != 0)).map fun α => α.map fun (i, d) => (i - 1, d))

end I

/-! ## Terms -/

inductive Tm where
  | var (x : Nat)
  /-- a global definition from the signature -/
  | const (k : Nat)
  | univ (l : Nat)
  /-- `B` binds a term variable -/
  | pi (A B : Tm)
  /-- `λ (x : A). t`, annotated with its domain -/
  | lam (A t : Tm)
  | app (f a : Tm)
  | sigma (A B : Tm)
  | pair (a b : Tm)
  | fst (p : Tm)
  | snd (p : Tm)
  /-- `PathP (i. A) a b`; `A` binds an interval variable -/
  | path (A a b : Tm)
  | plam (t : Tm)
  | papp (p : Tm) (r : I)
  /-- `(i : I) → A`; `A` binds an interval variable. Elements are `plam`s. -/
  | ipi (A : Tm)
  /-- the system `[φ ↦ t, ψ ↦ u]` -/
  | split (φ : I) (t : Tm) (ψ : I) (u : Tm)
  /-- the empty system -/
  | abort
  /-- `transp (i. A) φ a` -/
  | transp (A : Tm) (φ : I) (a : Tm)
  /-- `hcomp A [φ ↦ i. u] a` -/
  | hcomp (A : Tm) (φ : I) (u a : Tm)
  /-- `Glue A [φ ↦ (T, e)]` -/
  | glue (A : Tm) (φ : I) (T e : Tm)
  /-- `glue [φ ↦ t] a`, carrying the equivalence `e` of its Glue type -/
  | glueEl (φ : I) (e t a : Tm)
  /-- `unglue` carries the equivalence `e` of the Glue type -/
  | unglue (φ : I) (e g : Tm)
  /-- argument lists (parameters, constructor arguments, branches) are terms built from `tnil`
  and `tcons`, so that `Tm` is not a nested inductive; they have no typing rules of their own -/
  | tnil
  | tcons (t ts : Tm)
  /-- the inductive type `d` of the signature at the parameters `ps` (a list) -/
  | data (d : Nat) (ps : Tm)
  /-- constructor `c` of `d` at the parameters `ps`, with arguments `args` (a list) and interval
  arguments `rs` -/
  | con (d c : Nat) (ps args : Tm) (rs : List I)
  /-- `elim d ps (x. P) bs t`: the eliminator of `d` at the parameters `ps` with motive `P`
  (binding `x : data d ps`) and branches `bs` (a list, one per constructor) -/
  | elim (d : Nat) (ps P bs t : Tm)
  deriving DecidableEq, Repr, Inhabited

namespace Tm

def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Rename term variables by `ρ` and interval variables by `δ`. -/
def ren (ρ δ : Nat → Nat) : Tm → Tm
  | var x => var (ρ x)
  | const k => const k
  | univ l => univ l
  | pi A B => pi (A.ren ρ δ) (B.ren (upRen ρ) δ)
  | lam A t => lam (A.ren ρ δ) (t.ren (upRen ρ) δ)
  | app f a => app (f.ren ρ δ) (a.ren ρ δ)
  | sigma A B => sigma (A.ren ρ δ) (B.ren (upRen ρ) δ)
  | pair a b => pair (a.ren ρ δ) (b.ren ρ δ)
  | fst p => fst (p.ren ρ δ)
  | snd p => snd (p.ren ρ δ)
  | path A a b => path (A.ren ρ (upRen δ)) (a.ren ρ δ) (b.ren ρ δ)
  | plam t => plam (t.ren ρ (upRen δ))
  | papp p r => papp (p.ren ρ δ) (r.ren δ)
  | ipi A => ipi (A.ren ρ (upRen δ))
  | split φ t ψ u => split (φ.ren δ) (t.ren ρ δ) (ψ.ren δ) (u.ren ρ δ)
  | abort => abort
  | transp A φ a => transp (A.ren ρ (upRen δ)) (φ.ren δ) (a.ren ρ δ)
  | hcomp A φ u a => hcomp (A.ren ρ δ) (φ.ren δ) (u.ren ρ (upRen δ)) (a.ren ρ δ)
  | glue A φ T e => glue (A.ren ρ δ) (φ.ren δ) (T.ren ρ δ) (e.ren ρ δ)
  | glueEl φ e t a => glueEl (φ.ren δ) (e.ren ρ δ) (t.ren ρ δ) (a.ren ρ δ)
  | unglue φ e g => unglue (φ.ren δ) (e.ren ρ δ) (g.ren ρ δ)
  | tnil => tnil
  | tcons t ts => tcons (t.ren ρ δ) (ts.ren ρ δ)
  | data d ps => data d (ps.ren ρ δ)
  | con d c ps args rs => con d c (ps.ren ρ δ) (args.ren ρ δ) (rs.map (·.ren δ))
  | elim d ps P bs t => elim d (ps.ren ρ δ) (P.ren (upRen ρ) δ) (bs.ren ρ δ) (t.ren ρ δ)

/-- Weaken by a term variable. -/
def shift (t : Tm) : Tm := t.ren Nat.succ id

/-- Weaken by an interval variable. -/
def dshift (t : Tm) : Tm := t.ren id Nat.succ

def up (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | n + 1 => (σ n).shift

/-- Simultaneous substitution of term variables by `σ` and interval variables by `τ`. -/
def subst (σ : Nat → Tm) (τ : Nat → I) : Tm → Tm
  | var x => σ x
  | const k => const k
  | univ l => univ l
  | pi A B => pi (A.subst σ τ) (B.subst (up σ) τ)
  | lam A t => lam (A.subst σ τ) (t.subst (up σ) τ)
  | app f a => app (f.subst σ τ) (a.subst σ τ)
  | sigma A B => sigma (A.subst σ τ) (B.subst (up σ) τ)
  | pair a b => pair (a.subst σ τ) (b.subst σ τ)
  | fst p => fst (p.subst σ τ)
  | snd p => snd (p.subst σ τ)
  | path A a b => path (A.subst (fun n => (σ n).dshift) (I.up τ)) (a.subst σ τ) (b.subst σ τ)
  | plam t => plam (t.subst (fun n => (σ n).dshift) (I.up τ))
  | papp p r => papp (p.subst σ τ) (r.subst τ)
  | ipi A => ipi (A.subst (fun n => (σ n).dshift) (I.up τ))
  | split φ t ψ u => split (φ.subst τ) (t.subst σ τ) (ψ.subst τ) (u.subst σ τ)
  | abort => abort
  | transp A φ a => transp (A.subst (fun n => (σ n).dshift) (I.up τ)) (φ.subst τ) (a.subst σ τ)
  | hcomp A φ u a =>
    hcomp (A.subst σ τ) (φ.subst τ) (u.subst (fun n => (σ n).dshift) (I.up τ)) (a.subst σ τ)
  | glue A φ T e => glue (A.subst σ τ) (φ.subst τ) (T.subst σ τ) (e.subst σ τ)
  | glueEl φ e t a => glueEl (φ.subst τ) (e.subst σ τ) (t.subst σ τ) (a.subst σ τ)
  | unglue φ e g => unglue (φ.subst τ) (e.subst σ τ) (g.subst σ τ)
  | tnil => tnil
  | tcons t ts => tcons (t.subst σ τ) (ts.subst σ τ)
  | data d ps => data d (ps.subst σ τ)
  | con d c ps args rs => con d c (ps.subst σ τ) (args.subst σ τ) (rs.map (·.subst τ))
  | elim d ps P bs t => elim d (ps.subst σ τ) (P.subst (up σ) τ) (bs.subst σ τ) (t.subst σ τ)

/-- Substitute interval variables only. -/
def dsubst (τ : Nat → I) (t : Tm) : Tm := t.subst var τ

/-- `t[a/0]` for the term variable 0. -/
def inst (t a : Tm) : Tm := t.subst (fun | 0 => a | n + 1 => var n) I.var

/-- `t[r/0]` for the interval variable 0. -/
def dinst (t : Tm) (r : I) : Tm := t.dsubst (I.inst0 r)

/-- `t[d/i]` for an arbitrary interval variable `i`, keeping all other variables. -/
def dset (t : Tm) (i : Nat) (d : I) : Tm := t.dsubst fun n => if n = i then d else .var n

/-- `t` has free term variables below `n` and free interval variables below `m`. -/
def closedB (n m : Nat) : Tm → Bool
  | var x => decide (x < n)
  | const _ | univ _ | abort => true
  | pi A B | sigma A B => A.closedB n m && B.closedB (n + 1) m
  | lam A t => A.closedB n m && t.closedB (n + 1) m
  | app f a | pair f a => f.closedB n m && a.closedB n m
  | fst p | snd p => p.closedB n m
  | path A a b => A.closedB n (m + 1) && a.closedB n m && b.closedB n m
  | plam t | ipi t => t.closedB n (m + 1)
  | papp p r => p.closedB n m && r.scopedB m
  | split φ t ψ u => φ.scopedB m && t.closedB n m && ψ.scopedB m && u.closedB n m
  | transp A φ a => A.closedB n (m + 1) && φ.scopedB m && a.closedB n m
  | hcomp A φ u a => A.closedB n m && φ.scopedB m && u.closedB n (m + 1) && a.closedB n m
  | glue A φ T e => A.closedB n m && φ.scopedB m && T.closedB n m && e.closedB n m
  | glueEl φ e t a => φ.scopedB m && e.closedB n m && t.closedB n m && a.closedB n m
  | unglue φ e g => φ.scopedB m && e.closedB n m && g.closedB n m
  | tnil => true
  | tcons t ts => t.closedB n m && ts.closedB n m
  | data _ ps => ps.closedB n m
  | con _ _ ps args rs => ps.closedB n m && args.closedB n m && rs.all (·.scopedB m)
  | elim _ ps P bs t => ps.closedB n m && P.closedB (n + 1) m && bs.closedB n m && t.closedB n m

/-- Non-dependent function type. -/
def arrow (A B : Tm) : Tm := pi A B.shift

/-! ## Defined types -/

/-- `Path A a b` for a type `A` not depending on the path variable. -/
def pathC (A a b : Tm) : Tm := path A.dshift a b

/-- `isContr X = Σ (c : X), (x : X) → Path X c x` -/
def isContr (X : Tm) : Tm := sigma X (pi X.shift (pathC X.shift.shift (var 1) (var 0)))

/-- `fiber f y = Σ (x : T), Path A (f x) y` -/
def fiber (T A f y : Tm) : Tm := sigma T (pathC A.shift (app f.shift (var 0)) y.shift)

/-- `isEquiv f = (y : A) → isContr (fiber f y)` -/
def isEquiv (T A f : Tm) : Tm := pi A (isContr (fiber T.shift A.shift f.shift (var 0)))

/-- `Equiv T A = Σ (f : T → A), isEquiv f` -/
def equiv (T A : Tm) : Tm := sigma (arrow T A) (isEquiv T.shift A.shift (var 0))

/-! ## Derived Kan operations -/

/-- Interval substitution for a line `A` (variable 0) used under one more binder
(new variable 0), sending the old variable 0 to `r`. -/
def bind2 (r : I) : Nat → I
  | 0 => r
  | n + 1 => .var (n + 2)

/-- `comp (i. C) [ψ ↦ i. u] u0 = hcomp C(1) [ψ ↦ k. transp (m. C(k ∨ m)) (k = 1) u(k)] (transp (i. C) 0 u0)` -/
def comp (C : Tm) (ψ : I) (u u0 : Tm) : Tm :=
  hcomp (C.dinst .one) ψ
    (transp (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u)
    (transp C .zero u0)

/-- The filler `hfill A [φ ↦ i. u] u0` at the interval variable 0:
`hcomp A [φ ↦ k. u(i ∧ k), i = 0 ↦ u0] u0`. -/
def hfill (A : Tm) (φ : I) (u u0 : Tm) : Tm :=
  hcomp A.dshift (.or φ.shift (.neg (.var 0)))
    (split φ.shift.shift (u.dsubst (bind2 (.and (.var 1) (.var 0)))) (.neg (.var 1)) u0.dshift.dshift)
    u0.dshift

/-- The filler of heterogeneous composition at the interval variable 0:
`fill (i. C) [ψ ↦ u] u0 = comp (j. C(i ∧ j)) [ψ ↦ j. u(i ∧ j), i = 0 ↦ u0] u0`. -/
def fill (C : Tm) (ψ : I) (u u0 : Tm) : Tm :=
  comp (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0)))
    (split ψ.shift.shift (u.dsubst (bind2 (.and (.var 1) (.var 0)))) (.neg (.var 1)) u0.dshift.dshift)
    u0.dshift

/-- The transport filler at the interval variable 0: `transp (j. A(i ∧ j)) (φ ∨ i = 0) a`. -/
def transpFill (A : Tm) (φ : I) (a : Tm) : Tm :=
  transp (A.dsubst (bind2 (.and (.var 1) (.var 0)))) (.or φ.shift (.neg (.var 0))) a.dshift

/-! ## Computation rules of the Kan operations (Coquand–Huber–Mörtberg) -/

/-- `transp (i. Π A B) φ u0 = λ v. transp (i. B[w(i)]) φ (u0 w(0))`
where `w(i) = transp (j. A(i ∨ ~j)) (φ ∨ i = 1) v`. -/
def transpPi (A B : Tm) (φ : I) (u0 : Tm) : Tm :=
  let w := transp (A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0)) (var 0)
  let w0 := transp (A.shift.dsubst fun | 0 => .neg (.var 0) | n + 1 => .var (n + 1)) φ (var 0)
  lam (A.dinst .one) (transp (B.subst (fun | 0 => w | n + 1 => var (n + 1)) .var) φ (app u0.shift w0))

/-- `transp (i. Σ A B) φ u0 = (transp A φ u0.1, transp (i. B[a(i)]) φ u0.2)`
with `a` the transport filler of `u0.1`. -/
def transpSigma (A B : Tm) (φ : I) (u0 : Tm) : Tm :=
  let a := transpFill A φ (fst u0)
  pair (transp A φ (fst u0)) (transp (B.subst (fun | 0 => a | n + 1 => var n) .var) φ (snd u0))

/-- `transp (i. PathP (j. A) a b) φ p0 = ⟨j⟩ comp (i. A) [φ ↦ p0 j, j = 0 ↦ a, j = 1 ↦ b] (p0 j)`.
Here `A` has interval variables `j` (0) and `i` (1); `a`, `b` mention `i` (0). -/
def transpPath (A a b : Tm) (φ : I) (p0 : Tm) : Tm :=
  -- inside ⟨j⟩: variable 0 is j. The composition binds i, giving i = 0, j = 1.
  let C := A.dsubst fun | 0 => .var 1 | 1 => .var 0 | n + 2 => .var (n + 2)
  let ins1 : Nat → I := fun | 0 => .var 0 | n + 1 => .var (n + 2)
  let sys := split φ.shift.shift (papp p0.dshift.dshift (.var 1)) (.or (.neg (.var 1)) (.var 1))
    (split (.neg (.var 1)) (a.dsubst ins1) (.var 1) (b.dsubst ins1))
  plam (comp C (.or φ.shift (.or (.neg (.var 0)) (.var 0))) sys (papp p0.dshift (.var 0)))

/-- `transp (i. (j : I) → A) φ u0 = ⟨j⟩ transp (i. A) φ (u0 j)`; `A` has `j` (0) and `i` (1). -/
def transpIPi (A : Tm) (φ : I) (u0 : Tm) : Tm :=
  plam (transp (A.dsubst fun | 0 => .var 1 | 1 => .var 0 | n + 2 => .var (n + 2)) φ.shift
    (papp u0.dshift (.var 0)))

/-- `hcomp ((j : I) → A) [φ ↦ u] u0 = ⟨j⟩ hcomp A [φ ↦ u j] (u0 j)` -/
def hcompIPi (A : Tm) (φ : I) (u u0 : Tm) : Tm :=
  plam (hcomp A φ.shift (papp (u.dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) (.var 1))
    (papp u0.dshift (.var 0)))

/-- `hcomp (Π A B) [φ ↦ u] u0 = λ v. hcomp B [φ ↦ u v] (u0 v)` -/
def hcompPi (A B : Tm) (φ : I) (u u0 : Tm) : Tm :=
  lam A (hcomp B φ (app u.shift (var 0)) (app u0.shift (var 0)))

/-- `hcomp (Σ A B) [φ ↦ u] u0 = (hcomp A [φ ↦ u.1] u0.1, comp (i. B[hfill]) [φ ↦ u.2] u0.2)` -/
def hcompSigma (A B : Tm) (φ : I) (u u0 : Tm) : Tm :=
  let f := hfill A φ (fst u) (fst u0)
  pair (hcomp A φ (fst u) (fst u0))
    (comp (B.dshift.subst (fun | 0 => f | n + 1 => var n) .var) φ (snd u) (snd u0))

/-- `hcomp (PathP (j. A) a b) [φ ↦ u] p0 = ⟨j⟩ hcomp A [φ ↦ u j, j = 0 ↦ a, j = 1 ↦ b] (p0 j)` -/
def hcompPath (A a b : Tm) (φ : I) (u p0 : Tm) : Tm :=
  let ins1 : Nat → I := fun | 0 => .var 0 | n + 1 => .var (n + 2)
  let sys := split φ.shift.shift (papp (u.dsubst ins1) (.var 1)) (.or (.neg (.var 1)) (.var 1))
    (split (.neg (.var 1)) a.dshift.dshift (.var 1) b.dshift.dshift)
  plam (hcomp A (.or φ.shift (.or (.neg (.var 0)) (.var 0))) sys (papp p0.dshift (.var 0)))

/-- `hcomp (Glue A [φ ↦ (T, e)]) [ψ ↦ u] u0 =
  glue [φ ↦ hcomp T [ψ ↦ u] u0] (hcomp A [ψ ↦ unglue u, φ ↦ e.1 (hfill T [ψ ↦ u] u0)] (unglue u0))` -/
def hcompGlue (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u u0 : Tm) : Tm :=
  let _ := T
  glueEl φ e (hcomp T ψ u u0)
    (hcomp A (.or ψ φ)
      (split ψ.shift (unglue φ.shift e.dshift u) φ.shift (app (fst e.dshift) (hfill T ψ u u0)))
      (unglue φ e u0))

/-- Transport in Glue types (CHM). The line `Glue A [φ ↦ (T, e)]` has all components in
the interval variable 0. -/
def transpGlue (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) : Tm :=
  let φ0 := φ.subst (I.inst0 .zero)
  let φ1 := φ.subst (I.inst0 .one)
  let A1 := A.dinst .one
  let T1 := T.dinst .one
  let e1 := e.dinst .one
  let δ := φ.forall0
  -- the base, composed along the unglued tube: on ψ the Glue line is constant, so
  -- `i ↦ unglue φ(i) e(i) u0` is a tube in the line `A`
  let a0 := unglue φ0 (e.dinst .zero) u0
  let tube := unglue φ e u0.dshift
  let a1' := comp A ψ tube a0
  -- on δ: transport in T, and a path from e(1).1 t1' to a1'
  let t1' := transp T ψ u0
  let ins1 : Nat → I := fun | 0 => .var 0 | n + 1 => .var (n + 2)
  let e' := e.dsubst ins1
  let sysω := split ψ.shift.shift (app (fst e') u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
    (split (.neg (.var 1)) (app (fst e') ((transpFill T ψ u0).dsubst ins1))
      (.var 1) ((fill A ψ tube a0).dsubst ins1))
  let ω := plam (comp (A.dsubst ins1) (.or ψ.shift (.or (.neg (.var 0)) (.var 0))) sysω
    (app (fst (e.dinst .zero).dshift) u0.dshift))
  -- extend the partial fibre over a1' to a total one, by contractibility
  let c := app (snd e1) a1'
  let fib := fiber T1 A1 (fst e1) a1'
  let ext := hcomp fib (.or δ ψ)
    (split δ.shift (papp (app (snd c).dshift (pair t1'.dshift ω.dshift)) (.var 0))
      ψ.shift (papp (app (snd c).dshift (pair u0.dshift (plam a1'.dshift.dshift))) (.var 0)))
    (fst c)
  let a1 := hcomp A1 (.or φ1 ψ)
    (split φ1.shift (papp (snd ext).dshift (.neg (.var 0))) ψ.shift a1'.dshift) a1'
  glueEl φ1 e1 (fst ext) a1

/-- `f_i = λ x. transp (j. B(i ∧ j)) (i = 0) x : B(0) → B(i)`, for a line `B` in the interval
variable 0 (`i`). At `i = 0` it is the identity (`transp` on a true face). -/
def lineFun (B : Tm) : Tm :=
  lam (B.dinst .zero).dshift (transp (B.shift.dsubst (bind2 (.and (.var 1) (.var 0)))) (.neg (.var 0)) (var 0))

/-- `isEquiv f` for an `f : T → T` that is (judgmentally, pointwise) the identity:
`λ y. ((y, ⟨_⟩ y), λ (x, p). ⟨i⟩ (p(~i), ⟨j⟩ p(~i ∨ j)))`. -/
def idIsEquiv (T f : Tm) : Tm :=
  lam T (pair (pair (var 0) (plam (var 0)))
    (lam (fiber T.shift T.shift f.shift (var 0))
      (plam (pair (papp (snd (var 0)) (.neg (.var 0)))
        (plam (papp (snd (var 0)) (.or (.neg (.var 1)) (.var 0))))))))

/-- Transport along a line `B` (variable 0) is an equivalence `B(0) ≃ B(1)`: transport the
proof that `f_0` is an equivalence along `i ↦ isEquiv f_i`. -/
def lineEquiv (B : Tm) : Tm :=
  pair ((lineFun B).dinst .one)
    (transp (isEquiv (B.dinst .zero).dshift B (lineFun B)) .zero
      (idIsEquiv (B.dinst .zero) ((lineFun B).dinst .zero)))

/-- `hcomp U [φ ↦ i. u] u0 = Glue u0 [φ ↦ (u(1), e)]`, where `e : u(1) ≃ u0` is transport
backwards along the tube (`lineEquiv` of the reversed tube; on `φ`, `u(0) ≡ u0`). -/
def hcompU (φ : I) (u u0 : Tm) : Tm :=
  glue u0 φ (u.dinst .one) (lineEquiv (u.dsubst fun | 0 => .neg (.var 0) | n + 1 => .var (n + 1)))

end Tm

/-! ## Inductive types (phase 2, `docs/inductive-types.md`) -/

namespace Tm

def ofList : List Tm → Tm
  | [] => tnil
  | t :: ts => tcons t (ofList ts)

/-- The elements of a list term (other terms give `[]`). -/
def toList : Tm → List Tm
  | tcons t ts => t :: ts.toList
  | _ => []

/-- Substitute the term variables `j < L.length` by `L[j]` (most recent first) and lower the
others. -/
def substList (L : List Tm) (t : Tm) : Tm :=
  t.subst (fun j => L.getD j (var (j - L.length))) I.var

/-- Weaken by `n` term and `m` interval variables. -/
def wkN (n m : Nat) (t : Tm) : Tm := t.ren (· + n) (· + m)

def apps (f : Tm) (as : List Tm) : Tm := as.foldl app f

def papps (f : Tm) (rs : List I) : Tm := rs.foldl papp f

/-- Whether `t` mentions the inductive type `d` (its type former, constructors or eliminator). -/
def mentionsData (d : Nat) : Tm → Bool
  | var _ | const _ | univ _ | abort | tnil => false
  | pi A B | lam A B | app A B | sigma A B | pair A B | tcons A B => A.mentionsData d || B.mentionsData d
  | fst t | snd t | plam t | ipi t | papp t _ => t.mentionsData d
  | path A a b | glueEl _ A a b => A.mentionsData d || a.mentionsData d || b.mentionsData d
  | unglue _ a b => a.mentionsData d || b.mentionsData d
  | split _ t _ u | transp t _ u => t.mentionsData d || u.mentionsData d
  | hcomp A _ u a => A.mentionsData d || u.mentionsData d || a.mentionsData d
  | glue A _ T e => A.mentionsData d || T.mentionsData d || e.mentionsData d
  | data d' ps => d' == d || ps.mentionsData d
  | con d' _ ps args _ => d' == d || ps.mentionsData d || args.mentionsData d
  | elim d' ps P bs t => d' == d || ps.mentionsData d || P.mentionsData d || bs.mentionsData d ||
      t.mentionsData d

/-- Whether the term variable `x` occurs free in `t`. -/
def freeIn (x : Nat) : Tm → Bool
  | var y => y == x
  | const _ | univ _ | abort | tnil => false
  | pi A B | sigma A B | lam A B => A.freeIn x || B.freeIn (x + 1)
  | app A B | pair A B | tcons A B => A.freeIn x || B.freeIn x
  | fst t | snd t | plam t | ipi t | papp t _ | data _ t => t.freeIn x
  | path A a b | glueEl _ A a b => A.freeIn x || a.freeIn x || b.freeIn x
  | unglue _ a b | split _ a _ b | transp a _ b => a.freeIn x || b.freeIn x
  | hcomp A _ u a | glue A _ u a => A.freeIn x || u.freeIn x || a.freeIn x
  | con _ _ ps args _ => ps.freeIn x || args.freeIn x
  | elim _ ps P bs t => ps.freeIn x || P.freeIn (x + 1) || bs.freeIn x || t.freeIn x

end Tm

/-- A constructor argument: a point argument of a type not mentioning the inductive type, or a
recursive argument (of the inductive type itself, at the same parameters). -/
inductive Arg where
  | point (A : Tm)
  | recur
  deriving DecidableEq, Repr, Inhabited

/-- A constructor `c (x₁ : A₁) … (xₙ : Aₙ) (i₁ … iₘ : I) [ψ ↦ b]`. The type of argument `k` lives
in the context of the parameters and the arguments before it. The boundary is a system over
the interval arguments (`iₘ` is interval variable 0), with elements in the context of the
parameters and all arguments. -/
structure Ctor where
  args : List Arg
  dims : Nat
  bnd : List (I × Tm)
  deriving DecidableEq, Repr, Inhabited

/-- `data D (Δ) : U l := ctors`. Parameter `j` lives in the context of the parameters before it. -/
structure DataDecl where
  level : Nat
  params : List Tm
  ctors : List Ctor
  deriving DecidableEq, Repr, Inhabited

/-- An entry of the signature: a definition `(body, type)` or an inductive type. -/
inductive Entry where
  | defn (t A : Tm)
  | data (D : DataDecl)
  deriving DecidableEq, Repr, Inhabited

/-- A signature; constant `k` and inductive type `k` refer to entry `k`. -/
abbrev Sig := List Entry

namespace Ctor

def isRec (C : Ctor) (k : Nat) : Bool := C.args[k]? == some .recur

/-- The positions of the recursive arguments. -/
def recPos (C : Ctor) : List Nat := (List.range C.args.length).filter C.isRec

/-- The parameters of `d` as variables, in a context with `depth` variables after them. -/
def paramVars (np depth : Nat) : Tm := Tm.ofList ((List.range np).map fun p => .var (depth + np - 1 - p))

/-- The type of argument `k` of a constructor of `d` with `np` parameters, in the context of
the parameters and the arguments before it. -/
def argTy (C : Ctor) (d np k : Nat) : Tm :=
  match C.args[k]? with
  | some (.point A) => A
  | _ => .data d (paramVars np k)

/-- The point argument type `A` at position `k` does not mention the recursive arguments
before it. -/
def noRecDeps (C : Ctor) (k : Nat) (A : Tm) : Bool :=
  (List.range k).all fun j => !C.isRec j || !A.freeIn (k - 1 - j)

def argTys (C : Ctor) (d np : Nat) : List Tm := (List.range C.args.length).map (C.argTy d np)

/-- The boundary element `b` at parameters `ps`, arguments `args` and interval arguments `rs`. -/
def bndAt (b : Tm) (ps args : List Tm) (rs : List I) : Tm :=
  b.subst (fun j => (args.reverse ++ ps.reverse).getD j (.var j)) (fun i => rs.reverse.getD i (.var i))

/-- The boundary cofibration `ψ` at interval arguments `rs`. -/
def cofAt (ψ : I) (rs : List I) : I := ψ.subst fun i => rs.reverse.getD i (.var i)

/-! ### Simple boundaries

A boundary element of constructor `c` (with `n` arguments) is *simple* if it is a recursive
argument of `c`, or a constructor `c' < c` of the same type at the same parameters whose
recursive arguments are simple and whose point arguments are point arguments of `c`. -/

mutual
def simpleB (ctors : List Ctor) (d np c n : Nat) (C : Ctor) : Tm → Bool
  | .var j => decide (j < n) && C.isRec (n - 1 - j)
  | .con d' c' ps as rs =>
    d' == d && decide (c' < c) && ps == paramVars np n &&
      (match ctors[c']? with
       | some C' => as.toList.length == C'.args.length && rs.length == C'.dims &&
           simpleArgs ctors d np c n C C' 0 as
       | none => false)
  | _ => false
def simpleArgs (ctors : List Ctor) (d np c n : Nat) (C C' : Ctor) (k : Nat) : Tm → Bool
  | .tcons a as =>
    (if C'.isRec k then simpleB ctors d np c n C a
     else match a with
       | .var j => decide (j < n) && !C.isRec (n - 1 - j)
       | _ => false) &&
    simpleArgs ctors d np c n C C' (k + 1) as
  | .tnil => true
  | _ => false
end

end Ctor

namespace DataDecl

/-! ### The eliminator

The branch for constructor `c` is a function of the arguments, an induction hypothesis for each
recursive argument, and the interval arguments. In its body (the *branch context*) argument `k`
is variable `r + n - 1 - k` and hypothesis `s` is variable `r - 1 - s` (with `n` arguments and `r`
recursive ones), and interval argument `l` is interval variable `m - 1 - l`. -/

/-- `P[con d c ps xs is]` in the branch context, for `P` and `ps` over the outer context. -/
def branchBody (d c : Nat) (C : Ctor) (ps P : Tm) : Tm :=
  let n := C.args.length
  let r := C.recPos.length
  let m := C.dims
  let xs := (List.range n).map fun k => Tm.var (r + n - 1 - k)
  let is := (List.range m).map fun l => I.var (m - 1 - l)
  let conTm := Tm.con d c (ps.wkN (n + r) m) (Tm.ofList xs) is
  P.subst (fun | 0 => conTm | j + 1 => .var (j + n + r)) (fun i => .var (i + m))

/-- The type of argument `k` in the context extended by the arguments before it. -/
def branchArgTy (d np : Nat) (C : Ctor) (ps : Tm) (k : Nat) : Tm :=
  (C.argTy d np k).substList ((List.range k).map Tm.var ++ ps.toList.reverse.map (·.wkN k 0))

/-- The type of hypothesis `s` in the context extended by the arguments and hypotheses before it. -/
def branchIhTy (C : Ctor) (P : Tm) (s : Nat) : Tm :=
  let n := C.args.length
  P.subst (fun | 0 => .var (s + n - 1 - C.recPos.getD s 0) | j + 1 => .var (j + n + s)) I.var

/-- The type of the branch for constructor `c`. -/
def branchTy (D : DataDecl) (d c : Nat) (C : Ctor) (ps P : Tm) : Tm :=
  let n := C.args.length
  let r := C.recPos.length
  let inner := (List.range C.dims).foldl (fun acc _ => Tm.ipi acc) (branchBody d c C ps P)
  let withIhs := (List.range r).foldr (fun s acc => Tm.pi (branchIhTy C P s) acc) inner
  (List.range n).foldr (fun k acc => Tm.pi (branchArgTy d D.params.length C ps k) acc) withIhs

/-- The branch context (arguments, hypotheses; innermost first) over `Γ`, under the
interval arguments. -/
def branchCtx (D : DataDecl) (d : Nat) (C : Ctor) (ps P : Tm) (Γ : List Tm) : List Tm :=
  let n := C.args.length
  let r := C.recPos.length
  (((List.range r).reverse.map (branchIhTy C P)) ++
    ((List.range n).reverse.map (branchArgTy d D.params.length C ps)) ++ Γ).map
    (·.ren id (· + C.dims))

/-- The branch `b` applied to the variables of the branch context. -/
def branchApp (C : Ctor) (b : Tm) : Tm :=
  let n := C.args.length
  let r := C.recPos.length
  let m := C.dims
  Tm.papps (Tm.apps (b.wkN (n + r) m)
    ((List.range n).map (fun k => Tm.var (r + n - 1 - k)) ++ (List.range r).map fun s => Tm.var (r - 1 - s)))
    ((List.range m).map fun l => I.var (m - 1 - l))

/-- A boundary element as a point of the branch context. -/
def bndPoint (C : Ctor) (ps : Tm) (b : Tm) : Tm :=
  let n := C.args.length
  let r := C.recPos.length
  b.subst (fun j => if j < n then .var (j + r) else (ps.toList.reverse.getD (j - n) (.var 0)).wkN (n + r) C.dims)
    I.var

mutual
/-- The eliminator on a simple boundary element, computed from the branches in the branch
context: a recursive argument gives its hypothesis, a constructor its branch. -/
def bndElim (D : DataDecl) (C : Ctor) (ps bs : Tm) : Tm → Tm
  | .var j =>
    let n := C.args.length
    let r := C.recPos.length
    match C.recPos.idxOf? (n - 1 - j) with
    | some s => .var (r - 1 - s)
    | none => .abort
  | .con _ c' _ as rs =>
    match D.ctors[c']?, bs.toList[c']? with
    | some C', some b =>
      Tm.papps (Tm.apps (b.wkN (C.args.length + C.recPos.length) C.dims)
        (as.toList.map (bndPoint C ps) ++ bndElimArgs D C ps bs C' 0 as)) rs
    | _, _ => .abort
  | _ => .abort
/-- The hypotheses for the recursive arguments of a boundary constructor. -/
def bndElimArgs (D : DataDecl) (C : Ctor) (ps bs : Tm) (C' : Ctor) (k : Nat) : Tm → List Tm
  | .tcons a as =>
    (if C'.isRec k then [bndElim D C ps bs a] else []) ++ bndElimArgs D C ps bs C' (k + 1) as
  | _ => []
end

end DataDecl

namespace Tm

/-- Transport of a telescope of constructor arguments along the parameter line `psL` (in the
context extended by the interval variable 0): each argument is transported along its type
line, whose earlier arguments are the transport fillers of the earlier arguments. -/
def transpTele (argTy : Nat → Tm) (psL : List Tm) (φ : I) : Nat → List Tm → List Tm → List Tm
  | _, _, [] => []
  | k, fills, a :: as =>
    let L := (argTy k).substList (fills ++ psL.reverse)
    transp L φ a :: transpTele argTy psL φ (k + 1) (transpFill L φ a :: fills) as

end Tm

/-- Universe levels are bounded, so that the model can be built from finitely many
Grothendieck universes (an unbounded tower is not constructible in Lean). -/
def maxLevel : Nat := 4

/-- Contexts: types of term variables, the most recent first. -/
abbrev Ctx := List Tm

/-- Weaken a context by an interval variable. -/
def Ctx.dshift (Γ : Ctx) : Ctx := Γ.map Tm.dshift

/-- The type of variable `x`, weakened to the full context. -/
def Ctx.lookup : Ctx → Nat → Option Tm
  | [], _ => none
  | A :: _, 0 => some A.shift
  | _ :: Γ, x + 1 => (Ctx.lookup Γ x).map Tm.shift

end KubusCore
