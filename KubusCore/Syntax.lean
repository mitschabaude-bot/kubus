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
  | lam (t : Tm)
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
  /-- `glue [φ ↦ t] a` -/
  | glueEl (φ : I) (t a : Tm)
  | unglue (φ : I) (g : Tm)
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
  | lam t => lam (t.ren (upRen ρ) δ)
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
  | glueEl φ t a => glueEl (φ.ren δ) (t.ren ρ δ) (a.ren ρ δ)
  | unglue φ g => unglue (φ.ren δ) (g.ren ρ δ)

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
  | lam t => lam (t.subst (up σ) τ)
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
  | glueEl φ t a => glueEl (φ.subst τ) (t.subst σ τ) (a.subst σ τ)
  | unglue φ g => unglue (φ.subst τ) (g.subst σ τ)

/-- Substitute interval variables only. -/
def dsubst (τ : Nat → I) (t : Tm) : Tm := t.subst var τ

/-- `t[a/0]` for the term variable 0. -/
def inst (t a : Tm) : Tm := t.subst (fun | 0 => a | n + 1 => var n) I.var

/-- `t[r/0]` for the interval variable 0. -/
def dinst (t : Tm) (r : I) : Tm := t.dsubst (I.inst0 r)

/-- `t[d/i]` for an arbitrary interval variable `i`, keeping all other variables. -/
def dset (t : Tm) (i : Nat) (d : I) : Tm := t.dsubst fun n => if n = i then d else .var n

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

/-- The transport filler at the interval variable 0: `transp (j. A(i ∧ j)) (φ ∨ i = 0) a`. -/
def transpFill (A : Tm) (φ : I) (a : Tm) : Tm :=
  transp (A.dsubst (bind2 (.and (.var 1) (.var 0)))) (.or φ.shift (.neg (.var 0))) a.dshift

/-! ## Computation rules of the Kan operations (Coquand–Huber–Mörtberg) -/

/-- `transp (i. Π A B) φ u0 = λ v. transp (i. B[w(i)]) φ (u0 w(0))`
where `w(i) = transp (j. A(i ∨ ~j)) (φ ∨ i = 1) v`. -/
def transpPi (A B : Tm) (φ : I) (u0 : Tm) : Tm :=
  let w := transp (A.shift.dsubst (bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0)) (var 0)
  let w0 := transp (A.shift.dsubst fun | 0 => .neg (.var 0) | n + 1 => .var (n + 1)) φ (var 0)
  lam (transp (B.subst (fun | 0 => w | n + 1 => var (n + 1)) .var) φ (app u0.shift w0))

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
def hcompPi (B : Tm) (φ : I) (u u0 : Tm) : Tm :=
  lam (hcomp B φ (app u.shift (var 0)) (app u0.shift (var 0)))

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
  glueEl φ (hcomp T ψ u u0)
    (hcomp A (.or ψ φ)
      (split ψ.shift (unglue φ.shift u) φ.shift (app (fst e.dshift) (hfill T ψ u u0)))
      (unglue φ u0))

/-- Transport in Glue types (CHM). The line `Glue A [φ ↦ (T, e)]` has all components in
the interval variable 0. -/
def transpGlue (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) : Tm :=
  let φ0 := φ.subst (I.inst0 .zero)
  let φ1 := φ.subst (I.inst0 .one)
  let A1 := A.dinst .one
  let T1 := T.dinst .one
  let e1 := e.dinst .one
  let δ := φ.forall0
  -- naive transport of the base
  let a0 := unglue φ0 u0
  let a1' := transp A ψ a0
  -- on δ: transport in T, and a path from e(1).1 t1' to a1'
  let t1' := transp T ψ u0
  let ins1 : Nat → I := fun | 0 => .var 0 | n + 1 => .var (n + 2)
  let e' := e.dsubst ins1
  let sysω := split ψ.shift.shift (app (fst e') u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
    (split (.neg (.var 1)) (app (fst e') ((transpFill T ψ u0).dsubst ins1))
      (.var 1) ((transpFill A ψ a0).dsubst ins1))
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
  glueEl φ1 (fst ext) a1

end Tm

/-- A signature of global definitions `(body, type)`; constant `k` refers to entry `k`.
Bodies and types are closed. -/
abbrev Sig := List (Tm × Tm)

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
