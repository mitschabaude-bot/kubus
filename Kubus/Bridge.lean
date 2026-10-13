import Kubus.Top
import KubusCore

/-!
# Bridge to the certified kernel (run by `kubus` on every definition)

Translates elaborated definitions into KubusCore signature entries and checks them with the
kernel (`KubusCore.Kernel`). The translation is not trusted: whatever it produces is checked
by the kernel.

- Kubus core terms use one de Bruijn context for term and interval variables; KubusCore has
  two sorts, so indices are split.
- KubusCore lambdas carry their domain and `unglue` carries the Glue equivalence, which Kubus
  core terms do not record. The translation is therefore type-directed: it runs alongside
  the kernel, taking lambda domains from the expected Π type and equivalences from the Glue
  type of `unglue`'s argument.
- `let` is translated by substitution.
- Data types, constructors and pattern-matching definitions are phase 2: definitions using
  them are skipped.
-/

namespace Kubus.Bridge

open KubusCore.Kernel
open KubusCore (HasTy KCtx Sig cof)

abbrev KTm := KubusCore.Tm
abbrev KI := KubusCore.I

/-- Entries of the translation context, the most recent first. -/
inductive Entry
  | tm
  | dim
  /-- a `let`-bound value, in the context where it was defined -/
  | defn (t : KTm)

def countTm (es : List Entry) : Nat := es.countP fun | .tm => true | _ => false
def countDim (es : List Entry) : Nat := es.countP fun | .dim => true | _ => false

def trVar (ks : List Entry) (k : Nat) : Except String KTm :=
  match ks[k]? with
  | some .tm => pure (.var (countTm (ks.take k)))
  | some (.defn t) => pure (t.ren (· + countTm (ks.take k)) (· + countDim (ks.take k)))
  | some .dim => throw s!"variable #{k} is an interval variable"
  | none => throw s!"variable #{k} out of scope"

def trI (ks : List Entry) : ITm → Except String KI
  | .zero => pure .zero
  | .one => pure .one
  | .var i =>
    match ks[i]? with
    | some .dim => pure (.var (countDim (ks.take i)))
    | _ => throw s!"variable #{i} is not an interval variable"
  | .neg r => return .neg (← trI ks r)
  | .and r s => return .and (← trI ks r) (← trI ks s)
  | .or r s => return .or (← trI ks r) (← trI ks s)

/-! ## Inlining `let`

Kubus core terms do not record the type of a `let`-bound value, so the value is substituted
before translation and translated at each use, against the type expected there. -/

def mapI (f : Nat → Nat → ITm) (c : Nat) : ITm → ITm
  | .var i => f c i
  | .neg r => .neg (mapI f c r)
  | .and r s => .and (mapI f c r) (mapI f c s)
  | .or r s => .or (mapI f c r) (mapI f c s)
  | r => r

/-- Map the free variables (term and interval, which share one index space) of a term; `c`
counts the binders crossed. `pre c t` may replace a whole subterm first. -/
partial def mapTm (pre : Nat → Kubus.Tm → Option Kubus.Tm) (f : Nat → Nat → Kubus.Tm)
    (g : Nat → Nat → ITm) (c : Nat) (t : Kubus.Tm) : Kubus.Tm :=
  match pre c t with
  | some t' => t'
  | none =>
  let go := mapTm pre f g
  let sysUnder (sys : List (ITm × Kubus.Tm)) := sys.map fun (r, t) => (mapI g c r, go (c + 1) t)
  let sys0 (sys : List (ITm × Kubus.Tm)) := sys.map fun (r, t) => (mapI g c r, go c t)
  match t with
  | .var i => f c i
  | .pi x a b => .pi x (go c a) (go (c + 1) b)
  | .sigma x a b => .sigma x (go c a) (go (c + 1) b)
  | .lam x b => .lam x (go (c + 1) b)
  | .app a b => .app (go c a) (go c b)
  | .pair a b => .pair (go c a) (go c b)
  | .fst t => .fst (go c t)
  | .snd t => .snd (go c t)
  | .piI i a => .piI i (go (c + 1) a)
  | .pathP a u v => .pathP (go c a) (go c u) (go c v)
  | .plam i b => .plam i (go (c + 1) b)
  | .papp t r => .papp (go c t) (mapI g c r)
  | .comp i a sys u0 => .comp i (go (c + 1) a) (sysUnder sys) (go c u0)
  | .hcomp i a sys u0 => .hcomp i (go c a) (sysUnder sys) (go c u0)
  | .fill i a sys u0 => .fill i (go (c + 1) a) (sysUnder sys) (go c u0)
  | .glueTy a sys => .glueTy (go c a) (sys0 sys)
  | .glue sys a => .glue (sys0 sys) (go c a)
  | .unglue u b sys => .unglue (go c u) (go c b) (sys0 sys)
  | .compU a sys => .compU (go c a) (sys0 sys)
  | .unglueU u b sys => .unglueU (go c u) (go c b) (sys0 sys)
  | .data d k ps => .data d k (ps.map (go c))
  | .con n as ds => .con n (as.map (go c)) (ds.map (mapI g c))
  | .letE x t b => .letE x (go c t) (go (c + 1) b)
  | .ann t ty => .ann (go c t) (go c ty)
  | t => t

def mapVars (f : Nat → Nat → Kubus.Tm) (g : Nat → Nat → ITm) (c : Nat) (t : Kubus.Tm) : Kubus.Tm :=
  mapTm (fun _ _ => none) f g c t

def shiftK (n : Nat) (t : Kubus.Tm) : Kubus.Tm :=
  if n == 0 then t else
  mapVars (fun c i => .var (if i ≥ c then i + n else i))
    (fun c i => .var (if i ≥ c then i + n else i)) 0 t

/-- `b[v/0]` -/
def subst0 (b v : Kubus.Tm) : Kubus.Tm :=
  mapVars (fun c i => if i == c then shiftK c v else .var (if i > c then i - 1 else i))
    (fun c i => .var (if i > c then i - 1 else i)) 0 b

partial def inlineLets : Kubus.Tm → Kubus.Tm
  | .letE _ t b => subst0 (inlineLets b) (inlineLets t)
  | t => mapVars (fun _ i => .var i) (fun _ i => .var i) 0 (descend t)
where
  descend : Kubus.Tm → Kubus.Tm
  | .pi x a b => .pi x (inlineLets a) (inlineLets b)
  | .sigma x a b => .sigma x (inlineLets a) (inlineLets b)
  | .lam x b => .lam x (inlineLets b)
  | .app a b => .app (inlineLets a) (inlineLets b)
  | .pair a b => .pair (inlineLets a) (inlineLets b)
  | .fst t => .fst (inlineLets t)
  | .snd t => .snd (inlineLets t)
  | .piI i a => .piI i (inlineLets a)
  | .pathP a u v => .pathP (inlineLets a) (inlineLets u) (inlineLets v)
  | .plam i b => .plam i (inlineLets b)
  | .papp t r => .papp (inlineLets t) r
  | .comp i a sys u0 => .comp i (inlineLets a) (sys.map fun (r, t) => (r, inlineLets t)) (inlineLets u0)
  | .hcomp i a sys u0 => .hcomp i (inlineLets a) (sys.map fun (r, t) => (r, inlineLets t)) (inlineLets u0)
  | .fill i a sys u0 => .fill i (inlineLets a) (sys.map fun (r, t) => (r, inlineLets t)) (inlineLets u0)
  | .glueTy a sys => .glueTy (inlineLets a) (sys.map fun (r, t) => (r, inlineLets t))
  | .glue sys a => .glue (sys.map fun (r, t) => (r, inlineLets t)) (inlineLets a)
  | .unglue u b sys => .unglue (inlineLets u) (inlineLets b) (sys.map fun (r, t) => (r, inlineLets t))
  | .data d k ps => .data d k (ps.map inlineLets)
  | .con n as ds => .con n (as.map inlineLets) ds
  | .ann t ty => .ann (inlineLets t) (inlineLets ty)
  | t => t

/-! ## Systems and canonical cofibrations -/

def faceLt : KubusCore.I.Face → KubusCore.I.Face → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => litLt a b || (a == b && faceLt as bs)

/-- The disjunction of keys as a canonical cofibration: its faces, sorted and deduplicated,
so that the Glue type, `glue` and `unglue` agree syntactically. -/
def canonCof (keys : List KI) : KI :=
  let faces := keys.flatMap fun r => r.faces.map normFace
  KubusCore.I.ofFaces (faces.eraseDups.mergeSort fun a b => !faceLt b a)

/-- Nested `split` for a system; `[]` is `abort`. -/
def mkSys : List (KI × KTm) → KTm
  | [] => .abort
  | [(_, t)] => t
  | (r, t) :: rest => .split r t (rest.foldr (fun (s, _) acc => .or s acc) .zero) (mkSys rest)

def disj (keys : List KI) : KI := keys.foldr (fun r acc => .or r acc) .zero

/-! ## Type-directed translation -/

structure Env where
  /-- constant index of a global with its displacement -/
  consts : Std.HashMap (String × Nat) Nat := {}
  /-- index of an inductive type with its displacement -/
  datas : Std.HashMap (String × Nat) Nat := {}
  globals : Globals := {}

/-- Inductive types that do not mention universes are not displaced. -/
def Env.dataKey (env : Env) (dn : String) (k : Nat) : String × Nat :=
  match env.globals.datas[dn]? with
  | some i => if i.liftInvariant then (dn, 0) else (dn, k)
  | none => (dn, k)

def Env.dataIdx (env : Env) (dn : String) (k : Nat) : Except String Nat :=
  match env.datas[env.dataKey dn k]? with
  | some i => pure i
  | none => throw s!"uses the data type {dn}, which is not in the kernel signature"

/-- The data type of a constructor and its index. -/
def Env.ctorOf (env : Env) (c : String) : Except String (String × Nat) :=
  match env.globals.ctors[c]? with
  | some ci =>
    match env.globals.datas[ci.data]? with
    | some di =>
      match di.ctors.findIdx? (·.name == c) with
      | some i => pure (ci.data, i)
      | none => throw s!"unknown constructor {c}"
    | none => throw s!"unknown data type {ci.data}"
  | none => throw s!"unknown constructor {c}"

def appSpine : Kubus.Tm → Kubus.Tm × List Kubus.Tm
  | .app f a => let (h, as) := appSpine f; (h, as ++ [a])
  | t => (t, [])

/-- Prepare the body of the clause of a pattern-matching definition `f` (with `nParams`
parameters) for a constructor with `n` arguments (recursive ones at `recPos`) and `m` interval
arguments: make room for the `r` induction hypotheses between the arguments and the interval
arguments, and replace the structurally recursive calls `f params x` by the hypothesis for `x`. -/
def prepBranch (f : String) (k nParams m n : Nat) (recPos : List Nat) (body : Kubus.Tm) : Kubus.Tm :=
  let r := recPos.length
  let pre (c : Nat) (t : Kubus.Tm) : Option Kubus.Tm :=
    let (h, args) := appSpine t
    match h, args.getLast? with
    | .glob g k', some (.var j) =>
      if g == f && k' == k && args.length == nParams + 1 && c + m ≤ j && j < c + m + n then
        let paramsOk := (List.range nParams).all fun i =>
          match args[i]? with
          | some (.var x) => x == c + m + n + (nParams - 1 - i)
          | _ => false
        match recPos.idxOf? (n - 1 - (j - c - m)) with
        | some s => if paramsOk then some (.var (c + m + (r - 1 - s))) else none
        | none => none
      else none
    | _, _ => none
  mapTm pre (fun c i => .var (if i ≥ c + m then i + r else i))
    (fun c i => .var (if i ≥ c + m then i + r else i)) 0 body

/-- An expected type with its level. -/
abbrev Exp (S : Sig) (Ψ : Nat) (Φ : KI) (Γ : KubusCore.Ctx) :=
  Option ((A : KTm) × (l : Nat) × PLift (HasTy S Ψ Φ Γ A (.univ l)))

variable {S : Sig}

def expOf (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : KTm) : K S (Exp S Ψ Φ Γ) := do
  match ← KubusCore.Kernel.tryOpt (KubusCore.Kernel.inferType R E A) with
  | some ⟨l, h⟩ => pure (some ⟨A, l, h⟩)
  | none => pure none

def cofOf {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (r : KI) : K S (KCtx S Ψ (cof Φ r) Γ) := do
  let ⟨h⟩ ← KubusCore.Kernel.ensureScoped r Ψ
  pure (E.cof r h)

/-! ### Implicit arguments

Kubus inserts the solutions of implicit arguments as normal forms of its own evaluator, which
may rely on computation that CCHM does not have (regularity). The translation therefore
recovers implicit arguments by first-order matching of the parameter types of the head against
the inferred types of the explicit arguments, and uses Kubus's solutions only for implicit
arguments that are not determined this way. -/

/-- Which of the first `n` binders of the type of `g` are implicit. -/
def implMask (env : Env) (g : String) (n : Nat) : Option (List Bool) :=
  match env.globals.defs[g]? with
  | some info =>
    let rec go : Nat → Kubus.Tm → Option (List Bool)
      | 0, _ => some []
      | n + 1, .pi x _ b => (isImplName x :: ·) <$> go n b
      | _, _ => none
    go n info.tyTm
  | none => none

def piDoms : Nat → KTm → List KTm
  | n + 1, .pi A B => A :: piDoms n B
  | _, _ => []

def markVar : Nat := 1000000000

/-- `t` under `k` term and `m` interval binders, lowered to the outer context (if it does not
mention the bound variables). -/
def lowerTm (k m : Nat) (t : KTm) : Option KTm :=
  let t' := t.subst (fun x => .var (if x < k then markVar else x - k))
    (fun i => .var (if i < m then markVar else i - m))
  if t'.closedB markVar markVar then some t' else none

/-- Match the parameter type `pat` (in which variable `j ≥ dT` with `j - dT < i` stands for
argument `i - 1 - (j - dT)`) against `t`, recording the arguments found. -/
partial def matchPat (i : Nat) (vals : Array (Option KTm)) (dT dI : Nat) (pat t : KTm) :
    Array (Option KTm) :=
  let go := matchPat i
  match pat, t with
  | .var j, t =>
    if dT ≤ j && j - dT < i then
      let pos := i - 1 - (j - dT)
      match vals[pos]?, lowerTm dT dI t with
      | some none, some v => vals.set! pos (some v)
      | _, _ => vals
    else vals
  | .pi A B, .pi A' B' | .sigma A B, .sigma A' B' | .lam A B, .lam A' B' =>
    go (go vals dT dI A A') (dT + 1) dI B B'
  | .app f a, .app f' a' | .pair f a, .pair f' a' | .tcons f a, .tcons f' a' =>
    go (go vals dT dI f f') dT dI a a'
  | .fst p, .fst p' | .snd p, .snd p' | .papp p _, .papp p' _ | .data _ p, .data _ p' => go vals dT dI p p'
  | .plam b, .plam b' | .ipi b, .ipi b' => go vals dT (dI + 1) b b'
  | .path A a b, .path A' a' b' => go (go (go vals dT (dI + 1) A A') dT dI a a') dT dI b b'
  | .con _ _ ps as _, .con _ _ ps' as' _ => go (go vals dT dI ps ps') dT dI as as'
  | _, _ => vals

mutual

/-- Translate `t`, against the expected type if given. -/
partial def elabT (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry)
    (t : Kubus.Tm) (exp : Exp S Ψ Φ Γ) : K S KTm := do
  match t with
  | .var i => trVar ks i
  | .glob n k =>
    match env.consts[(n, k)]? with
    | some c => pure (.const c)
    | none => throw s!"uses {if k == 0 then n else s!"{n}^{k}"}, which is not in the kernel signature"
  | .univ l => pure (.univ l)
  | .pi _ a b => do
    let A ← elabT R env E ks a none
    let ⟨l, ⟨hA⟩⟩ ← KubusCore.Kernel.inferType R E A
    return .pi A (← elabT R env (E.ext A l hA) (.tm :: ks) b none)
  | .sigma _ a b => do
    let A ← elabT R env E ks a none
    let ⟨l, ⟨hA⟩⟩ ← KubusCore.Kernel.inferType R E A
    return .sigma A (← elabT R env (E.ext A l hA) (.tm :: ks) b none)
  | .lam _ b => do
    let some ⟨T, l, ⟨hT⟩⟩ := exp | throw "cannot determine the domain of a λ (no expected type)"
    match ← KubusCore.Kernel.whnfTy R E T l hT with
    | ⟨.pi A B, e⟩ =>
      have hP := HasTy.eqR e
      return .lam A (← elabT R env (E.ext A l (HasTy.piDom hP)) (.tm :: ks) b
        (some ⟨B, l, ⟨HasTy.piCod hP⟩⟩))
    | ⟨T', _⟩ => throw s!"a λ is expected to have type {KubusCore.Kernel.short T'}"
  | .app f a => do
    let (h, args) := appSpine (.app f a)
    let implicit := match h with
      | .glob g k => match implMask env g args.length with
        | some mask => if mask.any id then some (g, k, mask) else none
        | none => none
      | _ => none
    if let some (g, k, mask) := implicit then
      return ← elabImplSpine R env E ks g k args mask
    let f' ← elabT R env E ks f none
    match ← KubusCore.Kernel.inferW R E f' with
    | ⟨.pi A _, l, hP, _⟩ => return .app f' (← elabT R env E ks a (some ⟨A, l, ⟨HasTy.piDom hP⟩⟩))
    | ⟨T, _, _, _⟩ => throw s!"applying a term of type {KubusCore.Kernel.short T}"
  | .pair a b => do
    let dflt := do return KubusCore.Tm.pair (← elabT R env E ks a none) (← elabT R env E ks b none)
    match exp with
    | some ⟨T, l, ⟨hT⟩⟩ =>
      match ← KubusCore.Kernel.whnfTy R E T l hT with
      | ⟨.sigma A B, e⟩ =>
        have hP := HasTy.eqR e
        let a' ← elabT R env E ks a (some ⟨A, l, ⟨HasTy.sigmaDom hP⟩⟩)
        let ⟨ha⟩ ← R.check E a' A l (HasTy.sigmaDom hP)
        let b' ← elabT R env E ks b (some ⟨B.inst a', l, ⟨HasTy.subst (HasTy.sigmaCod hP) ha⟩⟩)
        return .pair a' b'
      | _ => dflt
    | none => dflt
  | .fst p => return .fst (← elabT R env E ks p none)
  | .snd p => return .snd (← elabT R env E ks p none)
  | .piI _ a => return .ipi (← elabT R env E.dext (.dim :: ks) a none)
  | .pathP a u v => do
    let L ← match a with
      | .plam _ b => elabT R env E.dext (.dim :: ks) b none
      | a => return .papp (← elabT R env E ks a none).dshift (.var 0)
    let ⟨l, ⟨hL⟩⟩ ← KubusCore.Kernel.inferType R E.dext L
    let u' ← elabT R env E ks u (some ⟨L.dinst .zero, l, ⟨HasTy.dsubst hL trivial⟩⟩)
    let v' ← elabT R env E ks v (some ⟨L.dinst .one, l, ⟨HasTy.dsubst hL trivial⟩⟩)
    return .path L u' v'
  | .plam _ b => do
    let line : Exp S (Ψ + 1) Φ.shift Γ.dshift ← match exp with
      | some ⟨T, l, ⟨hT⟩⟩ => do
        match ← KubusCore.Kernel.whnfTy R E T l hT with
        | ⟨.path A _ _, e⟩ => pure (some ⟨A, l, ⟨HasTy.pathLine (HasTy.eqR e)⟩⟩)
        | ⟨.ipi A, e⟩ => pure (some ⟨A, l, ⟨HasTy.ipiLine (HasTy.eqR e)⟩⟩)
        | _ => pure none
      | none => pure none
    return .plam (← elabT R env E.dext (.dim :: ks) b line)
  | .papp p r => return .papp (← elabT R env E ks p none) (← trI ks r)
  | .comp _ a sys u0 => do
    let L ← elabT R env E.dext (.dim :: ks) a none
    let ⟨l, ⟨hL⟩⟩ ← KubusCore.Kernel.inferType R E.dext L
    let (ψ, u) ← elabSysUnder R env E ks sys fun _ hk => some ⟨L, l, ⟨HasTy.rsd E hk hL⟩⟩
    let u0' ← elabT R env E ks u0 (some ⟨L.dinst .zero, l, ⟨HasTy.dsubst hL trivial⟩⟩)
    return KubusCore.Tm.comp L ψ u u0'
  | .hcomp _ a sys u0 => do
    let A ← elabT R env E ks a none
    let ⟨l, ⟨hA⟩⟩ ← KubusCore.Kernel.inferType R E A
    let (ψ, u) ← elabSysUnder R env E ks sys fun _ hk => some ⟨A.dshift, l, ⟨HasTy.dwkCof E hk hA⟩⟩
    return .hcomp A ψ u (← elabT R env E ks u0 (some ⟨A, l, ⟨hA⟩⟩))
  | .fill _ a sys u0 => do
    let L ← elabT R env E.dext (.dim :: ks) a none
    let ⟨l, ⟨hL⟩⟩ ← KubusCore.Kernel.inferType R E.dext L
    let (ψ, u) ← elabSysUnder R env E ks sys fun _ hk => some ⟨L, l, ⟨HasTy.rsd E hk hL⟩⟩
    let u0' ← elabT R env E ks u0 (some ⟨L.dinst .zero, l, ⟨HasTy.dsubst hL trivial⟩⟩)
    if !L.mentionsI 0 then
      -- homogeneous filler, so that `fill … 1` is the `hcomp`
      return .plam (KubusCore.Tm.hfill (L.dinst .zero) ψ u u0')
    else
      -- `⟨j⟩ comp (i. A(i ∧ j)) [ψ ↦ u(i ∧ j), j = 0 ↦ u0] u0`
      let σ : Nat → KI := fun | 0 => .and (.var 0) (.var 1) | n + 1 => .var (n + 2)
      let sys' := KubusCore.Tm.split ψ.shift.shift (u.dsubst σ) (.neg (.var 1)) u0'.dshift.dshift
      return .plam (KubusCore.Tm.comp (L.dsubst σ) (.or ψ.shift (.neg (.var 0))) sys' u0'.dshift)
  | .glueTy a sys => do
    let A ← elabT R env E ks a none
    let ⟨l, _⟩ ← KubusCore.Kernel.inferType R E A
    let mut es : Array (KI × KTm) := #[]
    for (key, p) in sys do
      let r ← trI ks key
      let Ek ← cofOf E r
      let pTy : KTm := .sigma (.univ l) (KubusCore.Tm.equiv (.var 0) A.shift)
      es := es.push (r, ← elabT R env Ek ks p (← expOf R Ek pTy))
    let es' := es.toList
    return .glue A (canonCof (es'.map (·.1))) (mkSys (es'.map fun (r, p) => (r, .fst p)))
      (mkSys (es'.map fun (r, p) => (r, .snd p)))
  | .glue sys a => do
    let keys ← sys.mapM fun (r, _) => trI ks r
    let some ⟨G, l, ⟨hG⟩⟩ := exp | throw "glue without an expected type"
    -- the cofibration of the Glue type as the kernel sees it (Kubus may have elaborated the
    -- element against the Glue type restricted to a face)
    -- under a face the Glue type may reduce: use its unreduced form if it is one
    let parts : Option (KTm × KTm × KTm × KI) := match G with
      | .glue A φ' T e => some (A, T, e, φ')
      | _ => none
    let (A, T, e, φ) ← match parts with
      | some p => pure p
      | none => do
        let φ ← match ← KubusCore.Kernel.whnfTy R E G l hG with
          | ⟨.glue _ φ' _ _, _⟩ => pure φ'
          | _ => pure (canonCof keys)
        let ⟨A, T, e, _⟩ ← KubusCore.Kernel.toGlue R E G l hG φ
        pure (A, T, e, φ)
    let ⟨_, ⟨hA⟩⟩ ← KubusCore.Kernel.inferType R E A
    let a' ← elabT R env E ks a (some ⟨A, _, ⟨hA⟩⟩)
    let mut es : Array (KI × KTm) := #[]
    for ((_, t), r) in sys.zip keys do
      let Ek ← cofOf E r
      es := es.push (r, ← elabT R env Ek ks t (← expOf R Ek T))
    return .glueEl φ e (mkSys es.toList) a'
  | .unglue u base sys => do
    let keys ← sys.mapM fun (r, _) => trI ks r
    -- the argument is checked against the Glue type recorded by Kubus, if it translates
    let G ← match ← KubusCore.Kernel.tryOpt (elabT R env E ks (.glueTy base sys) none) with
      | some G => expOf R E G
      | none => pure none
    let g ← elabT R env E ks u G
    let i ← R.infer E g
    match i.ty with
    | .glue _ φ' _ e => return .unglue φ' e g
    | _ =>
      let φ ← match ← KubusCore.Kernel.whnfTy R E i.ty i.lvl i.hty with
        | ⟨.glue _ φ' _ _, _⟩ => pure φ'
        | _ => pure (canonCof keys)
      let ⟨_, _, e, _⟩ ← KubusCore.Kernel.toGlue R E i.ty i.lvl i.hty φ
      return .unglue φ e g
  | .ann t ty => do
    -- the type recorded by the elaborator, where no expected type is known
    match exp with
    | some _ => elabT R env E ks t exp
    | none =>
      let ty' ← elabT R env E ks ty none
      elabT R env E ks t (← expOf R E ty')
  | .letE _ t b => do
    let t' ← elabT R env E ks t none
    elabT R env E (.defn t' :: ks) b exp
  | .compU .. | .unglueU .. => throw "composition in the universe is not supported"
  | .data dn k ps => do
    let d ← env.dataIdx dn k
    let ⟨D, _⟩ ← KubusCore.Kernel.lookupData S d
    return .data d (KubusCore.Tm.ofList (← elabTele R env E ks D.params [] ps))
  | .con c args dims => do
    let (dn, cIdx) ← env.ctorOf c
    -- the parameters come from the expected type
    let (d, ps) ← match exp with
      | some ⟨T, l, ⟨hT⟩⟩ => do
        match ← KubusCore.Kernel.whnfTy R E T l hT with
        | ⟨.data d ps, _⟩ => pure (d, ps)
        | ⟨T', _⟩ => throw s!"constructor {c} at type {KubusCore.Kernel.short T'}"
      | none => do
        let d ← env.dataIdx dn 0
        let ⟨D, _⟩ ← KubusCore.Kernel.lookupData S d
        if D.params.isEmpty then pure (d, KubusCore.Tm.tnil)
        else throw s!"cannot infer the parameters of {c}"
    let ⟨D, _⟩ ← KubusCore.Kernel.lookupData S d
    let ⟨C, _⟩ ← KubusCore.Kernel.lookupCtor D cIdx
    let args' ← elabTele R env E ks (C.argTys d D.params.length) ps.toList.reverse args
    return .con d cIdx ps (KubusCore.Tm.ofList args') (← dims.mapM fun r => (monadLift (trI ks r) : K S KI))
  | .split f k => elabSplit R env E ks f k exp

/-- An application of a global with implicit parameters. -/
partial def elabImplSpine (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry)
    (g : String) (k : Nat) (args : List Kubus.Tm) (mask : List Bool) : K S KTm := do
  let some c := env.consts[(g, k)]? | throw s!"uses {g}, which is not in the kernel signature"
  let F ← match S[c]? with
    | some (.defn _ A) => pure A
    | _ => throw s!"internal: {g} is not a definition"
  let n := args.length
  let doms := piDoms n F
  if doms.length != n then throw s!"too many arguments for {g}"
  -- explicit arguments that can be inferred determine the implicit ones before them
  let mut vals : Array (Option KTm) := Array.replicate n none
  let mut infd : Array (Option KTm) := Array.replicate n none
  for i in List.range n do
    if !(mask.getD i false) then
      if let some t ← KubusCore.Kernel.tryOpt (elabT R env E ks (args.getD i (.univ 0)) none) then
        if let some inf ← KubusCore.Kernel.tryOpt (KubusCore.Kernel.inferW R E t) then
          infd := infd.set! i (some t)
          vals := matchPat i vals 0 0 (doms.getD i (.univ 0)) inf.ty
  let mut final : Array KTm := #[]
  for i in List.range n do
    let D := (doms.getD i (.univ 0)).substList final.toList.reverse
    let given := if mask.getD i false then vals.getD i none else infd.getD i none
    match given with
    | some t => final := final.push t
    | none => final := final.push (← elabT R env E ks (args.getD i (.univ 0)) (← expOf R E D))
  return KubusCore.Tm.apps (.const c) final.toList

/-- Translate a list against a telescope. -/
partial def elabTele (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry) :
    List KTm → List KTm → List Kubus.Tm → K S (List KTm)
  | A :: Δ, prev, t :: ts => do
    let t' ← elabT R env E ks t (← expOf R E (A.substList prev))
    return t' :: (← elabTele R env E ks Δ (t' :: prev) ts)
  | [], _, [] => pure []
  | _, _, _ => throw "wrong number of arguments"

/-- Translate `body` under binders: `true` for a term binder of the Π type `T`, `false` for an
interval binder of `(i : I) → T`. -/
partial def elabUnder (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry)
    (T : KTm) : List Bool → Kubus.Tm → K S KTm
  | [], body => do elabT R env E ks body (← expOf R E T)
  | true :: bs, body => do
    match T with
    | .pi A B =>
      let ⟨l, ⟨hA⟩⟩ ← KubusCore.Kernel.inferType R E A
      return .lam A (← elabUnder R env (E.ext A l hA) (.tm :: ks) B bs body)
    | _ => throw "branch type mismatch"
  | false :: bs, body => do
    match T with
    | .ipi B => return .plam (← elabUnder R env E.dext (.dim :: ks) B bs body)
    | _ => throw "branch type mismatch"

/-- A pattern-matching function: `λ x. elim d ps (x. B) bs x`, with a branch for each clause. -/
partial def elabSplit (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry)
    (f : String) (k : Nat) (exp : Exp S Ψ Φ Γ) : K S KTm := do
  let some ⟨T, l, ⟨hT⟩⟩ := exp | throw "pattern matching without an expected type"
  let some info := env.globals.defs[f]? | throw s!"unknown definition {f}"
  match ← KubusCore.Kernel.whnfTy R E T l hT with
  | ⟨.pi A B, e⟩ =>
    have hP := HasTy.eqR e
    match ← KubusCore.Kernel.whnfTy R E A l (HasTy.piDom hP) with
    | ⟨.data d ps, _⟩ =>
      let ⟨D, _⟩ ← KubusCore.Kernel.lookupData S d
      let mut bs : Array KTm := #[]
      for (C, c) in D.ctors.zip (List.range D.ctors.length) do
        let some br := info.branches[c]? | throw s!"missing clause in {f}"
        let n := C.args.length
        let r := C.recPos.length
        let m := C.dims
        let body := prepBranch f k info.nParams m n C.recPos (inlineLets (br.body.lift k))
        bs := bs.push (← elabUnder R env E ks (D.branchTy d c C ps B)
          (List.replicate (n + r) true ++ List.replicate m false) body)
      return .lam A (.elim d ps.shift (B.ren (KubusCore.Tm.upRen Nat.succ) id) (KubusCore.Tm.ofList bs.toList).shift (.var 0))
    | ⟨A', _⟩ => throw s!"pattern matching on {KubusCore.Kernel.short A'}"
  | ⟨T', _⟩ => throw s!"pattern matching at type {KubusCore.Kernel.short T'}"

/-- A system whose elements bind an interval variable: the disjunction of the keys and the
elements as a nested `split`, in the context extended by the bound variable. -/
partial def elabSysUnder (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry)
    (sys : List (ITm × Kubus.Tm))
    (ty : (r : KI) → (hk : r.Scoped Ψ) → Exp S (Ψ + 1) (cof Φ r).shift Γ.dshift) :
    K S (KI × KTm) := do
  let mut es : Array (KI × KTm) := #[]
  for (key, t) in sys do
    let r ← trI ks key
    let ⟨hk⟩ ← KubusCore.Kernel.ensureScoped r Ψ
    es := es.push (r, ← elabT R env (E.cof r hk).dext (.dim :: ks) t (ty r hk))
  let es' := es.toList
  return (disj (es'.map (·.1)), mkSys (es'.map fun (r, t) => (r.shift, t)))

end

/-! ## Definitions -/

structure State where
  env : Env := {}
  sig : CheckedSig := .empty
  /-- reasons why a global (with displacement) is not in the signature -/
  skipped : Std.HashMap (String × Nat) String := {}
  certified : Nat := 0
  rejected : Nat := 0
  /-- add the translated term and type to rejections -/
  verbose : Bool := false

def showName (n : String) (k : Nat) : String := if k == 0 then n else s!"{n}^{k}"

/-- Globals mentioned by a core term, with their displacement. -/
partial def globs : Kubus.Tm → List (String × Nat)
  | .glob n j => [(n, j)]
  | t => t.children.flatMap fun (_, c) => globs c

/-- Data types mentioned by a core term (constructors and pattern matching included). -/
partial def datasOf (g : Globals) : Kubus.Tm → List (String × Nat)
  | .data d k ps => (d, k) :: ps.flatMap (datasOf g)
  | .con c as _ => ((g.ctors[c]?.map fun ci => [(ci.data, 0)]).getD []) ++ as.flatMap (datasOf g)
  | .split f _ =>
    match g.defs[f]? with
    | some info => info.branches.flatMap fun b =>
        ((g.ctors[b.ctor]?.map fun ci => [(ci.data, 0)]).getD []) ++ datasOf g b.body
    | none => []
  | t => t.children.flatMap fun (_, c) => datasOf g c

/-- Translation of the types in a data declaration (no λ or Glue elements occur there). -/
partial def trPlain (env : Env) (ks : List Entry) : Kubus.Tm → Except String KTm
  | .var i => trVar ks i
  | .glob n k =>
    match env.consts[(n, k)]? with
    | some c => pure (.const c)
    | none => throw s!"uses {showName' n k}, which is not in the kernel signature"
  | .univ l => pure (.univ l)
  | .pi _ a b => return .pi (← trPlain env ks a) (← trPlain env (.tm :: ks) b)
  | .sigma _ a b => return .sigma (← trPlain env ks a) (← trPlain env (.tm :: ks) b)
  | .app f a => return .app (← trPlain env ks f) (← trPlain env ks a)
  | .fst t => return .fst (← trPlain env ks t)
  | .snd t => return .snd (← trPlain env ks t)
  | .papp t r => return .papp (← trPlain env ks t) (← trI ks r)
  | .piI _ a => return .ipi (← trPlain env (.dim :: ks) a)
  | .pathP (.plam _ a) u v => return .path (← trPlain env (.dim :: ks) a) (← trPlain env ks u) (← trPlain env ks v)
  | .data dn k ps => return .data (← env.dataIdx dn k) (KubusCore.Tm.ofList (← ps.mapM (trPlain env ks)))
  | _ => throw "unsupported term in a data declaration"
where showName' (n : String) (k : Nat) : String := if k == 0 then n else s!"{n}^{k}"

/-- A boundary element of a constructor of the data type `d` (with `np` parameters) with `n`
arguments: argument variables and constructors of `d`. -/
partial def trBnd (env : Env) (di : DataInfo) (d np n : Nat) (ks : List Entry) : Kubus.Tm → Except String KTm
  | .var i => trVar ks i
  | .con c as rs => do
    let some ci := di.ctors.findIdx? (·.name == c) | throw s!"boundary uses {c}, a constructor of another type"
    return .con d ci (KubusCore.Ctor.paramVars np n) (KubusCore.Tm.ofList (← as.mapM (trBnd env di d np n ks)))
      (← rs.mapM (trI ks))
  | _ => throw "the boundary is not simple"

/-- Translate the declaration of a data type, which will have index `d`. -/
def transData (env : Env) (di : DataInfo) (k d : Nat) : Except String KubusCore.DataDecl := do
  let np := di.params.length
  let params ← (di.params.zip (List.range np)).mapM fun ((_, ty), j) =>
    trPlain env (List.replicate j .tm) (ty.lift k)
  let ctors ← di.ctors.mapM fun ci => do
    let n := ci.tele.length
    let args ← ((ci.tele.zip ci.recArgs).zip (List.range n)).mapM fun (((_, ty), isRec), j) => do
      if isRec then
        match ty with
        | .data dn _ ps =>
          let ok := dn == di.name && ps.length == np &&
            (ps.zip (List.range np)).all fun (p, q) => match p with
              | .var x => x == j + np - 1 - q
              | _ => false
          if ok then pure KubusCore.Arg.recur else throw s!"recursive argument of {ci.name} is not of the form {di.name} params"
        | _ => throw s!"recursive argument of {ci.name} is infinitary (not supported)"
      else return KubusCore.Arg.point (← trPlain env (List.replicate (np + j) .tm) (ty.lift k))
    let m := ci.dims.length
    let ks := List.replicate m Entry.dim ++ List.replicate (n + np) Entry.tm
    let bnd ← ci.boundary.mapM fun (key, el) => do
      return (← trI ks key, ← trBnd env di d np n ks (el.lift k))
    return ({ args, dims := m, bnd } : KubusCore.Ctor)
  return { level := di.level + k, params, ctors }

/-- Translate a closed definition. -/
def translate (env : Env) (R : Rec S) (E : KCtx S 0 .one []) (ty body : Kubus.Tm) : K S (KTm × KTm) := do
  let kty ← elabT R env E [] (inlineLets ty) none
  let ⟨l, ⟨hA⟩⟩ ← KubusCore.Kernel.inferType R E kty
  let kbody ← elabT R env E [] (inlineLets body) (some ⟨kty, l, ⟨hA⟩⟩)
  return (kty, kbody)

/-- Translate a definition and check it, sharing the kernel's cache. The inner error is a
failed translation; the outer one a rejection by the kernel. -/
def translateCheck (env : Env) (C : CheckedSig) (ty body : Kubus.Tm) (verbose : Bool := false) :
    Except String (Except String (KTm × KTm × CheckedSig)) := runK do
  let (R, E) ← setup C.sig
  match ← tryCatch (Except.ok <$> translate env R E ty body) (fun e => pure (.error e)) with
  | .error e => return .error e
  | .ok (kty, kbody) =>
    let ⟨h⟩ ← if verbose then
        mapErr (· ++ s!"\n  translated term: {Tm.pp kbody}\n  translated type: {Tm.pp kty}")
          (checkEntryK C.sig R E kbody kty)
      else checkEntryK C.sig R E kbody kty
    return .ok (kty, kbody, ⟨C.sig ++ [.defn kbody kty], wfSig_append C.wf h⟩)

mutual

/-- Add the data type `dn` displaced by `k` to the signature. -/
partial def addData (g : Globals) (dn : String) (k : Nat) : StateM State (List String) := do
  let s ← get
  let key := { s.env with globals := g }.dataKey dn k
  let name := "data " ++ showName key.1 key.2
  if s.env.datas.contains key || s.skipped.contains key then return []
  let skip (why : String) : StateM State (List String) := do
    modify fun s => { s with skipped := s.skipped.insert key why }
    return [s!"kernel: skipped {name}: {why}"]
  let some di := g.datas[dn]? | skip "unknown data type"
  let mut out : List String := []
  let tys := di.params.map (·.2) ++ di.ctors.flatMap fun ci => ci.tele.map (·.2)
  for t in tys do
    for (m, j) in globs t do out := out ++ (← addGlobal g m j)
    for (m, j) in datasOf g t do
      if m != dn then out := out ++ (← addData g m j)
  let s ← get
  let env := { s.env with globals := g }
  match transData env di key.2 s.sig.sig.length with
  | .error e => return out ++ (← skip e)
  | .ok D =>
    match s.sig.extendData D with
    | .ok sig' =>
      set { s with sig := sig', env.datas := s.env.datas.insert key s.sig.sig.length,
                   certified := s.certified + 1 }
      return out ++ [s!"kernel: certified {name}"]
    | .error e =>
      set { s with skipped := s.skipped.insert key "rejected", rejected := s.rejected + 1 }
      return out ++ [s!"kernel: REJECTED {name}: {e}"]

/-- Add the global `n` displaced by `k` to the signature (and the globals it uses first).
Returns the messages to print. -/
partial def addGlobal (g : Globals) (n : String) (k : Nat) : StateM State (List String) := do
  let s ← get
  if s.env.consts.contains (n, k) || s.skipped.contains (n, k) then return []
  let skip (why : String) : StateM State (List String) := do
    modify fun s => { s with skipped := s.skipped.insert (n, k) why }
    return [s!"kernel: skipped {showName n k}: {why}"]
  let some info := g.defs[n]? | skip "not a definition"
  let some body := info.body | skip "no body"
  let ty := info.tyTm.lift k
  let body := body.lift k
  let parts := ty :: body :: info.branches.map (·.body.lift k)
  let mut out : List String := []
  for t in parts do
    for (m, j) in globs t do
      if m != n then out := out ++ (← addGlobal g m j)
    for (m, j) in datasOf g t do out := out ++ (← addData g m j)
  let s ← get
  match translateCheck { s.env with globals := g } s.sig ty body s.verbose with
  | .ok (.error e) => return out ++ (← skip e)
  | .ok (.ok (_, _, sig')) =>
      set { s with sig := sig', env.consts := s.env.consts.insert (n, k) s.sig.sig.length,
                   certified := s.certified + 1 }
      return out ++ [s!"kernel: certified {showName n k}"]
  | .error e =>
      set { s with skipped := s.skipped.insert (n, k) "rejected", rejected := s.rejected + 1 }
      return out ++ [s!"kernel: REJECTED {showName n k}: {e}"]

end

end Kubus.Bridge
