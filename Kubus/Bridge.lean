import Kubus.Top
import KubusCore

/-!
# Bridge to the certified kernel (`kubus --kernel`)

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
counts the binders crossed. -/
partial def mapVars (f : Nat → Nat → Kubus.Tm) (g : Nat → Nat → ITm) (c : Nat) : Kubus.Tm → Kubus.Tm
  | .var i => f c i
  | .pi x a b => .pi x (mapVars f g c a) (mapVars f g (c + 1) b)
  | .sigma x a b => .sigma x (mapVars f g c a) (mapVars f g (c + 1) b)
  | .lam x b => .lam x (mapVars f g (c + 1) b)
  | .app a b => .app (mapVars f g c a) (mapVars f g c b)
  | .pair a b => .pair (mapVars f g c a) (mapVars f g c b)
  | .fst t => .fst (mapVars f g c t)
  | .snd t => .snd (mapVars f g c t)
  | .piI i a => .piI i (mapVars f g (c + 1) a)
  | .pathP a u v => .pathP (mapVars f g c a) (mapVars f g c u) (mapVars f g c v)
  | .plam i b => .plam i (mapVars f g (c + 1) b)
  | .papp t r => .papp (mapVars f g c t) (mapI g c r)
  | .comp i a sys u0 => .comp i (mapVars f g (c + 1) a) (sysUnder sys) (mapVars f g c u0)
  | .hcomp i a sys u0 => .hcomp i (mapVars f g c a) (sysUnder sys) (mapVars f g c u0)
  | .fill i a sys u0 => .fill i (mapVars f g (c + 1) a) (sysUnder sys) (mapVars f g c u0)
  | .glueTy a sys => .glueTy (mapVars f g c a) (sys0 sys)
  | .glue sys a => .glue (sys0 sys) (mapVars f g c a)
  | .unglue u b sys => .unglue (mapVars f g c u) (mapVars f g c b) (sys0 sys)
  | .compU a sys => .compU (mapVars f g c a) (sys0 sys)
  | .unglueU u b sys => .unglueU (mapVars f g c u) (mapVars f g c b) (sys0 sys)
  | .data d k ps => .data d k (ps.map (mapVars f g c))
  | .con n as ds => .con n (as.map (mapVars f g c)) (ds.map (mapI g c))
  | .letE x t b => .letE x (mapVars f g c t) (mapVars f g (c + 1) b)
  | t => t
where
  sysUnder (sys : List (ITm × Kubus.Tm)) := sys.map fun (r, t) => (mapI g c r, mapVars f g (c + 1) t)
  sys0 (sys : List (ITm × Kubus.Tm)) := sys.map fun (r, t) => (mapI g c r, mapVars f g c t)

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

/-- An expected type with its level. -/
abbrev Exp (S : Sig) (Ψ : Nat) (Φ : KI) (Γ : KubusCore.Ctx) :=
  Option ((A : KTm) × (l : Nat) × PLift (HasTy S Ψ Φ Γ A (.univ l)))

variable {S : Sig}

def expOf (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : KTm) : Exp S Ψ Φ Γ :=
  match KubusCore.Kernel.inferType R E A with
  | .ok ⟨l, h⟩ => some ⟨A, l, h⟩
  | .error _ => none

def cofOf {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (r : KI) : Except String (KCtx S Ψ (cof Φ r) Γ) := do
  let ⟨h⟩ ← KubusCore.Kernel.ensureScoped r Ψ
  pure (E.cof r h)

mutual

/-- Translate `t`, against the expected type if given. -/
partial def elabT (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry)
    (t : Kubus.Tm) (exp : Exp S Ψ Φ Γ) : Except String KTm := do
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
      es := es.push (r, ← elabT R env Ek ks p (expOf R Ek pTy))
    let es' := es.toList
    return .glue A (canonCof (es'.map (·.1))) (mkSys (es'.map fun (r, p) => (r, .fst p)))
      (mkSys (es'.map fun (r, p) => (r, .snd p)))
  | .glue sys a => do
    let keys ← sys.mapM fun (r, _) => trI ks r
    let φ := canonCof keys
    let some ⟨G, l, ⟨hG⟩⟩ := exp | throw "glue without an expected type"
    let ⟨A, T, e, ⟨hA, _⟩⟩ ← KubusCore.Kernel.toGlue R E G l hG φ
    let a' ← elabT R env E ks a (some ⟨A, l, ⟨hA⟩⟩)
    let mut es : Array (KI × KTm) := #[]
    for ((_, t), r) in sys.zip keys do
      let Ek ← cofOf E r
      es := es.push (r, ← elabT R env Ek ks t (expOf R Ek T))
    return .glueEl φ e (mkSys es.toList) a'
  | .unglue u _ sys => do
    let keys ← sys.mapM fun (r, _) => trI ks r
    let φ := canonCof keys
    let g ← elabT R env E ks u none
    let i ← R.infer E g
    let ⟨_, _, e, _⟩ ← KubusCore.Kernel.toGlue R E i.ty i.lvl i.hty φ
    return .unglue φ e g
  | .letE _ t b => do
    let t' ← elabT R env E ks t none
    elabT R env E (.defn t' :: ks) b exp
  | .compU .. | .unglueU .. => throw "composition in the universe is not supported"
  | .data d _ _ => throw s!"uses the data type {d} (phase 2)"
  | .con c _ _ => throw s!"uses the constructor {c} (phase 2)"
  | .split f _ => throw s!"is defined by pattern matching ({f}) (phase 2)"

/-- A system whose elements bind an interval variable: the disjunction of the keys and the
elements as a nested `split`, in the context extended by the bound variable. -/
partial def elabSysUnder (R : Rec S) (env : Env) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ks : List Entry)
    (sys : List (ITm × Kubus.Tm))
    (ty : (r : KI) → (hk : r.Scoped Ψ) → Exp S (Ψ + 1) (cof Φ r).shift Γ.dshift) :
    Except String (KI × KTm) := do
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

def showName (n : String) (k : Nat) : String := if k == 0 then n else s!"{n}^{k}"

/-- Globals mentioned by a core term, with their displacement. -/
partial def globs : Kubus.Tm → List (String × Nat)
  | .glob n j => [(n, j)]
  | t => t.children.flatMap fun (_, c) => globs c

/-- Translate a closed definition. -/
def translate (env : Env) (S : Sig) (ty body : Kubus.Tm) : Except String (KTm × KTm) := do
  let (R, E) ← setup S
  let kty ← elabT R env E [] (inlineLets ty) none
  let ⟨l, ⟨hA⟩⟩ ← KubusCore.Kernel.inferType R E kty
  let kbody ← elabT R env E [] (inlineLets body) (some ⟨kty, l, ⟨hA⟩⟩)
  return (kty, kbody)

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
  if !info.branches.isEmpty then return ← skip "pattern matching (phase 2)"
  let ty := info.tyTm.lift k
  let body := body.lift k
  let mut out : List String := []
  for (m, j) in globs ty ++ globs body do
    if m != n then out := out ++ (← addGlobal g m j)
  let s ← get
  match translate s.env s.sig.sig ty body with
  | .error e => return out ++ (← skip e)
  | .ok (kty, kbody) =>
    match s.sig.extend kbody kty with
    | .ok sig' =>
      set { s with sig := sig', env.consts := s.env.consts.insert (n, k) s.sig.sig.length,
                   certified := s.certified + 1 }
      return out ++ [s!"kernel: certified {showName n k}"]
    | .error e =>
      set { s with skipped := s.skipped.insert (n, k) "rejected", rejected := s.rejected + 1 }
      return out ++ [s!"kernel: REJECTED {showName n k}: {e}"]

end Kubus.Bridge
