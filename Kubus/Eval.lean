import Kubus.Value

/-!
# Evaluation and Kan operations

The Kan operations are those of the specification (`KubusCore/Syntax.lean`,
`KubusCore/Rules.lean`): `transp` and `hcomp` are primitive and compute by the
Coquand–Huber–Mörtberg rules; heterogeneous composition and the fillers are derived exactly
as in the specification. Higher inductive types have a formal homogeneous composition as a
canonical form; other inductive types compose componentwise. There is no regularity: a
transport along a constant line only reduces where the specification's rules apply.
-/

namespace Kubus

def atomF (i : Atom) : Formula := Formula.atom i
def natomF (i : Atom) : Formula := Formula.natom i

def envGet (env : Env) (i : Nat) : M EnvE :=
  match env[i]? with
  | some e => pure e
  | none => throw s!"internal: unbound variable #{i}"

def evalI (env : Env) : ITm → M Formula
  | .zero => pure Formula.zero
  | .one => pure Formula.one
  | .var i => do
    match ← envGet env i with
    | .d r => pure r
    | .v _ => throw "internal: expected an interval variable"
  | .neg r => return (← evalI env r).neg
  | .and r s => return (← evalI env r).and (← evalI env s)
  | .or r s => return (← evalI env r).or (← evalI env s)

/-! ## Term templates for equivalences

`Equiv T A = Σ (f : T → A), (y : A) → isContr (Σ (x : T), Path A (f x) y)`
with `isContr X = Σ (c : X), (x : X) → Path X c x`. -/

/-- Terms built over de Bruijn levels: a function from the current depth. -/
abbrev B := Nat → Tm

def B.var (lvl : Nat) : B := fun d => .var (d - lvl - 1)
def B.pi (x : String) (a : B) (b : Nat → B) : B := fun d => .pi x (a d) (b d (d + 1))
def B.sigma (x : String) (a : B) (b : Nat → B) : B := fun d => .sigma x (a d) (b d (d + 1))
def B.app (f a : B) : B := fun d => .app (f d) (a d)
def B.path (a u v : B) : B := fun d => .pathP (.plam "_" (a (d + 1))) (u d) (v d)
def B.univ (l : Nat) : B := fun _ => .univ l

def B.isContr (X : B) : B :=
  .sigma "c" X fun c => .pi "x" X fun x => .path X (.var c) (.var x)
def B.fiber (T A f y : B) : B := .sigma "x" T fun x => .path A (.app f (.var x)) y
def B.isEquiv (T A f : B) : B := .pi "y" A fun y => B.isContr (B.fiber T A f (.var y))
def B.equiv (T A : B) : B := .sigma "f" (.pi "_" T fun _ => A) fun f => B.isEquiv T A (.var f)

/-- `Σ (T : U l), Equiv T A` in context `[A]`. -/
def equivPairTm (l : Nat) : Tm :=
  (B.sigma "T" (B.univ l) fun t => B.equiv (.var t) (.var 0)) 1

/-- `Σ (x : T), Path A (f x) y` in context `[T, A, f, y]`. -/
def fiberTm : Tm := (B.fiber (.var 0) (.var 1) (.var 2) (.var 3)) 4

/-- Interval terms over de Bruijn levels. -/
abbrev IB := Nat → ITm

def IB.var (lvl : Nat) : IB := fun d => .var (d - lvl - 1)
def IB.zero : IB := fun _ => .zero
def IB.one : IB := fun _ => .one
def IB.neg (r : IB) : IB := fun d => .neg (r d)
def IB.and (r s : IB) : IB := fun d => .and (r d) (s d)
def IB.or (r s : IB) : IB := fun d => .or (r d) (s d)

def B.lam (x : String) (b : Nat → B) : B := fun d => .lam x (b d (d + 1))
def B.plam (b : Nat → B) : B := fun d => .plam "_" (b d (d + 1))
def B.papp (t : B) (r : IB) : B := fun d => .papp (t d) (r d)
def B.pair (a b : B) : B := fun d => .pair (a d) (b d)
def B.snd (t : B) : B := fun d => .snd (t d)
def B.transp (a : Nat → B) (φ : IB) (u0 : B) : B := fun d => .transp "j" (a d (d + 1)) (φ d) (u0 d)

/-- `f_r = λ x. transp (j. B(r ∧ j)) (r = 0) x : B(0) → B(r)`, for the line `B` at level 0. -/
def B.lineFunAt (r : IB) : B :=
  .lam "x" fun x => .transp (fun j => .papp (.var 0) (.and r (.var j))) (.neg r) (.var x)

/-- `idIsEquiv`: `λ y. ((y, ⟨_⟩ y), λ z. ⟨i⟩ (z.2 @ ~i, ⟨j⟩ z.2 @ (~i ∨ j)))`. -/
def B.idIsEquiv : B :=
  .lam "y" fun y => .pair (.pair (.var y) (.plam fun _ => .var y))
    (.lam "z" fun z => .plam fun i => .pair (.papp (.snd (.var z)) (.neg (.var i)))
      (.plam fun j => .papp (.snd (.var z)) (.or (.neg (.var i)) (.var j))))

/-- `lineEquiv B : B(0) ≃ B(1)` in context `[B]` (a line of types): the transport function,
and `idIsEquiv` transported along `i ↦ isEquiv f_i`. -/
def lineEquivTm : Tm :=
  (B.pair (B.lineFunAt .one)
    (B.transp (fun i => B.isEquiv (.papp (.var 0) .zero) (.papp (.var 0) (.var i)) (B.lineFunAt (.var i)))
      .zero B.idIsEquiv)) 1

mutual

partial def eval (env : Env) (t : Tm) : M Val := do
  tick
  match t with
  | .var i => do
    match ← envGet env i with
    | .v v => pure v
    | .d _ => throw "internal: expected a term variable"
  | .glob n k => evalGlob n k
  | .univ l => pure (.univ l)
  | .pi x a b => return .pi x (← eval env a) env b
  | .lam x b => pure (.lam x env b)
  | .app f a => do app (← eval env f) (← eval env a)
  | .sigma x a b => return .sigma x (← eval env a) env b
  | .pair a b => return .pair (← eval env a) (← eval env b)
  | .fst t => do fstV (← eval env t)
  | .snd t => do sndV (← eval env t)
  | .piI _ a => do
    let i ← freshAtom
    return .piI (.plam i (← eval (.d (atomF i) :: env) a))
  | .pathP a u v => return .pathP (← eval env a) (← eval env u) (← eval env v)
  | .plam _ b => do
    let i ← freshAtom
    return .plam i (← eval (.d (atomF i) :: env) b)
  | .papp t r => do papp (← eval env t) (← evalI env r)
  | .comp _ a sys u0 => do
    let i ← freshAtom
    let av ← eval (.d (atomF i) :: env) a
    let us ← evalSysUnder env i sys
    comp i av (← eval env u0) us
  | .hcomp _ a sys u0 => do
    let i ← freshAtom
    let us ← evalSysUnder env i sys
    hcomp i (← eval env a) (← eval env u0) us
  | .transp _ a φ u0 => do
    let i ← freshAtom
    transp i (← eval (.d (atomF i) :: env) a) (← evalI env φ) (← eval env u0)
  | .fill _ a sys u0 => do
    let i ← freshAtom
    let av ← eval (.d (atomF i) :: env) a
    let us ← evalSysUnder env i sys
    return .plam i (← fill i av (← eval env u0) us)
  | .hfill _ a sys u0 => do
    let i ← freshAtom
    let us ← evalSysUnder env i sys
    return .plam i (← hfill i (← eval env a) (← eval env u0) us)
  | .glueTy a sys => do mkGlueTy (← eval env a) (← evalSys env sys)
  | .glue sys a => do mkGlue (← eval env a) (← evalSys env sys)
  | .unglue u b sys => do unglueV (← eval env u) (← eval env b) (← evalSys env sys)
  | .data d k ps => do
    let k := if k == 0 || (← lookupData d).liftInvariant then 0 else k
    return .data d k (← ps.mapM (eval env))
  | .con c args dims => do
    let as ← args.mapM (eval env)
    if dims.isEmpty then pure (.con c as) else mkPCon c as (← dims.mapM (evalI env))
  | .split f k => pure (.split f k env)
  | .letE _ t b => do eval (.v (← eval env t) :: env) b
  | .ann t _ => eval env t

partial def evalGlob (n : String) (k : Nat) : M Val := do
  if let some m := metaId? n then
    match (← get).metas[m]? with
    | some { solV := some v, .. } => return v
    | some mi => return .gvar n mi.ty
    | none => throw s!"internal: unknown metavariable {n}"
  let info ← lookupDef n
  match info.body with
  | none => pure (.gvar n info.ty)
  | some _ => pure (.glued n k [])

/-- The value of the body of the global `n^k` (cached). -/
partial def globValue (n : String) (k : Nat) : M Val := do
  let info ← lookupDef n
  let cached := if k == 0 then info.value else info.lifted.lookup k
  match cached with
  | some v => pure v
  | none =>
    match info.body with
    | none => pure (.gvar n info.ty)
    | some body =>
      let v ← eval [] (body.lift k)
      let info' := if k == 0 then { info with value := some v } else { info with lifted := (k, v) :: info.lifted }
      modify fun s => { s with globals.defs := s.globals.defs.insert n info' }
      pure v

/-- Unfold glued globals at the head. -/
partial def unfoldM (v : Val) : M Val := do
  match v with
  | .glued g k sp =>
    let mut u ← globValue g k
    for e in sp.reverse do
      u ← match e with
        | .v a => app u a
        | .d r => papp u r
    unfoldM u
  | v => pure v

partial def evalSys (env : Env) (sys : TSys Tm) : M (System Val) := do
  let mut out : System Val := []
  for (key, t) in sys do
    let r ← evalI env key
    for α in r.faces do
      out := System.insert α (← eval (← faceEnv env α) t) out
  return out

/-- Evaluate a system whose elements bind an extra interval variable, instantiated with `i`. -/
partial def evalSysUnder (env : Env) (i : Atom) (sys : TSys Tm) : M (System Val) := do
  let mut out : System Val := []
  for (key, t) in sys do
    let r ← evalI env key
    for α in r.faces do
      out := System.insert α (← eval (.d (atomF i) :: (← faceEnv env α)) t) out
  return out

partial def inst (env : Env) (b : Tm) (v : Val) : M Val := eval (.v v :: env) b

partial def app (f a : Val) : M Val := do
  match f with
  | .glued g k sp => return .glued g k (.v a :: sp)
  | .lam _ env b => eval (.v a :: env) b
  | .split fn k env => splitApp fn k env a
  | .transp line φ u0 => appTransp line φ u0 a
  | .hcomp ty u0 sys => appHcomp ty u0 sys a
  | _ =>
    if f.isNeutral then pure (.app f a)
    else throw "internal: applying a non-function"

partial def fstV (p : Val) : M Val := do
  let p ← unfoldM p
  match p with
  | .pair a _ => pure a
  | _ => if p.isNeutral then pure (.fst p) else throw "internal: fst of a non-pair"

partial def sndV (p : Val) : M Val := do
  let p ← unfoldM p
  match p with
  | .pair _ b => pure b
  | _ => if p.isNeutral then pure (.snd p) else throw "internal: snd of a non-pair"

partial def papp (v : Val) (r : Formula) : M Val := do
  match v with
  | .glued g k sp => return .glued g k (.d r :: sp)
  | .plam i b => act i r b
  | _ =>
    match r.toDir? with
    | some d =>
      match ← inferNe v with
      | some (.pathP _ a b) => pure (if d == .zero then a else b)
      | _ => pure (.papp v r)
    | none => pure (.papp v r)

/-- If the head of a neutral is a solved metavariable, the value with the solution plugged in. -/
partial def forceHead? (v : Val) : M (Option Val) := do
  match v with
  | .gvar n _ =>
    match metaId? n with
    | some m => pure ((← get).metas[m]?.bind (·.solV))
    | none => pure none
  | .app f a => match ← forceHead? f with
    | some f' => some <$> app f' a
    | none => pure none
  | .papp p r => match ← forceHead? p with
    | some p' => some <$> papp p' r
    | none => pure none
  | .fst p => match ← forceHead? p with
    | some p' => some <$> fstV p'
    | none => pure none
  | .snd p => match ← forceHead? p with
    | some p' => some <$> sndV p'
    | none => pure none
  | .splitApp f k env a => match ← forceHead? a with
    | some a' => some <$> splitApp f k env a'
    | none => pure none
  | .unglue u b sys => match ← forceHead? u with
    | some u' => some <$> unglueV u' b sys
    | none => pure none
  -- a Kan operation stuck on a solved metavariable in its type: recompute it
  | .transp line φ u0 => do
    let k ← freshAtom
    match ← forceHead? (← papp line (atomF k)) with
    | some a => some <$> transp k a φ u0
    | none => pure none
  | .hcomp a u0 sys => do
    match ← forceHead? a with
    | some a' => some <$> hcompLines a' u0 sys
    | none => pure none
  | _ => pure none

/-- Plug in solved metavariables everywhere in a value (`none` if there are none). Values
computed while a metavariable was unsolved can be stuck on it; this recomputes them. -/
partial def refresh? (v : Val) : M (Option Val) := do
  let r := refresh?
  let rs (sys : System Val) : M (Option (System Val)) := do
    let parts ← sys.mapM fun (α, u) => return (α, u, ← r u)
    if parts.all (·.2.2.isNone) then return none
    return some (parts.map fun (α, u, u') => (α, u'.getD u))
  let re (env : Env) : M (Option Env) := do
    let parts ← env.mapM fun e => match e with
      | .v u => return (e, (← r u).map EnvE.v)
      | .d _ => return (e, none)
    if parts.all (·.2.isNone) then return none
    return some (parts.map fun (e, e') => e'.getD e)
  let rl (vs : List Val) : M (Option (List Val)) := do
    let parts ← vs.mapM fun u => return (u, ← r u)
    if parts.all (·.2.isNone) then return none
    return some (parts.map fun (u, u') => u'.getD u)
  match v with
  | .glued g k sp => return (← re sp).map (.glued g k ·)
  | .univ _ | .var .. => pure none
  | .gvar n _ =>
    match metaId? n with
    | some m => match (← get).metas[m]?.bind (·.solV) with
      | some s => return some ((← r s).getD s)
      | none => pure none
    | none => pure none
  | .pi x a env b => do
    let a' ← r a; let env' ← re env
    if a'.isNone && env'.isNone then return none
    return some (.pi x (a'.getD a) (env'.getD env) b)
  | .sigma x a env b => do
    let a' ← r a; let env' ← re env
    if a'.isNone && env'.isNone then return none
    return some (.sigma x (a'.getD a) (env'.getD env) b)
  | .lam x env b => return (← re env).map (.lam x · b)
  | .split f k env => return (← re env).map (.split f k ·)
  | .pair a b => do
    let a' ← r a; let b' ← r b
    if a'.isNone && b'.isNone then return none
    return some (.pair (a'.getD a) (b'.getD b))
  | .piI l => return (← r l).map .piI
  | .pathP l a b => do
    let l' ← r l; let a' ← r a; let b' ← r b
    if l'.isNone && a'.isNone && b'.isNone then return none
    return some (.pathP (l'.getD l) (a'.getD a) (b'.getD b))
  | .plam i b => return (← r b).map (.plam i ·)
  | .data d k ps => return (← rl ps).map (.data d k ·)
  | .con c as => return (← rl as).map (.con c ·)
  | .pcon c as ds => return (← rl as).map (.pcon c · ds)
  | .hcompF ty u sys => do
    let ty' ← r ty; let u' ← r u; let sys' ← rs sys
    if ty'.isNone && u'.isNone && sys'.isNone then return none
    return some (← mkHCompF (ty'.getD ty) (u'.getD u) (sys'.getD sys))
  | .glueTy b sys => do
    let b' ← r b; let sys' ← rs sys
    if b'.isNone && sys'.isNone then return none
    return some (← mkGlueTy (b'.getD b) (sys'.getD sys))
  | .glue a sys => do
    let a' ← r a; let sys' ← rs sys
    if a'.isNone && sys'.isNone then return none
    return some (← mkGlue (a'.getD a) (sys'.getD sys))
  | .app f a => do
    let f' ← r f; let a' ← r a
    if f'.isNone && a'.isNone then return none
    return some (← app (f'.getD f) (a'.getD a))
  | .fst p => do return (← (← r p).mapM fstV)
  | .snd p => do return (← (← r p).mapM sndV)
  | .papp p s => do return (← (← r p).mapM (papp · s))
  | .splitApp f k env a => do
    let env' ← re env; let a' ← r a
    if env'.isNone && a'.isNone then return none
    return some (← splitApp f k (env'.getD env) (a'.getD a))
  | .transp l φ u => do
    let l' ← r l; let u' ← r u
    if l'.isNone && u'.isNone then return none
    return some (← transpLine (l'.getD l) φ (u'.getD u))
  | .hcomp a u sys => do
    let a' ← r a; let u' ← r u; let sys' ← rs sys
    if a'.isNone && u'.isNone && sys'.isNone then return none
    return some (← hcompLines (a'.getD a) (u'.getD u) (sys'.getD sys))
  | .unglue u b sys => do
    let u' ← r u; let b' ← r b; let sys' ← rs sys
    if u'.isNone && b'.isNone && sys'.isNone then return none
    return some (← unglueV (u'.getD u) (b'.getD b) (sys'.getD sys))


/-- Plug in solved metavariables at the head of a value (glued globals stay folded). -/
partial def forceM (v : Val) : M Val := do
  if !v.isNeutral || (← get).metas.isEmpty then return v
  match ← forceHead? v with
  | some v' => forceM v'
  | none => pure v

/-- The head normal form of a value: unfold glued globals, plug in solved metavariables. -/
partial def force (v : Val) : M Val := do
  let v' ← forceM (← unfoldM v)
  match v' with
  | .glued .. => force v'
  | _ => pure v'

/-- Type of a neutral value, if it can be determined. -/
partial def inferNe (v : Val) : M (Option Val) := do
  match ← inferNe' v with
  | some ty => return some (← force ty)
  | none => return none

partial def inferNe' (v : Val) : M (Option Val) := do
  match ← unfoldM v with
  | .var _ ty | .gvar _ ty => pure (some ty)
  | .app f a =>
    match ← inferNe f with
    | some (.pi _ _ env b) => return some (← inst env b a)
    | _ => pure none
  | .fst p =>
    match ← inferNe p with
    | some (.sigma _ a _ _) => pure (some a)
    | _ => pure none
  | .snd p =>
    match ← inferNe p with
    | some (.sigma _ _ env b) => return some (← inst env b (← fstV p))
    | _ => pure none
  | .papp p r =>
    match ← inferNe p with
    | some (.pathP l _ _) | some (.piI l) => return some (← papp l r)
    | _ => pure none
  | .splitApp f k env a =>
    match ← splitFnType f k env with
    | .pi _ _ env' b => return some (← inst env' b a)
    | _ => pure none
  | .transp l _ _ => return some (← papp l Formula.one)
  | .hcomp a _ _ => pure (some a)
  | .unglue _ b _ => pure (some b)
  | _ => pure none

/-- The type `(x : D) → B x` of the split of `f`, with `f`'s parameters instantiated. -/
partial def splitFnType (f : String) (k : Nat) (env : Env) : M Val := do
  let info ← lookupDef f
  let ty0 ← if k == 0 then pure info.ty else eval [] (info.tyTm.lift k)
  let mut ty := ty0
  for e in env.reverse do
    match ← unfoldM ty, e with
    | .pi _ _ env' b, .v p => ty ← inst env' b p
    | _, _ => throw "internal: bad split type"
  return ty

partial def splitApp (f : String) (k : Nat) (env : Env) (a : Val) : M Val := do
  let a ← unfoldM a
  match a with
  | .con c args =>
    let br ← findBranch f c
    eval (args.reverse.map .v ++ env) (br.body.lift k)
  | .pcon c args dims =>
    let br ← findBranch f c
    eval (dims.reverse.map .d ++ args.reverse.map .v ++ env) (br.body.lift k)
  | .hcompF d u0 sys => do
    match ← splitFnType f k env with
    | .pi _ _ envB b =>
      let j ← freshAtom
      let wsj ← sys.mapM fun (α, l) => return (α, ← papp l (atomF j))
      let fl ← hfill j d u0 wsj
      let motive ← inst envB b fl
      let u0' ← splitApp f k env u0
      let us' ← wsj.mapM fun (α, w) => do return (α, ← app (← faceV (.split f k env) α) w)
      comp j motive u0' us'
    | _ => throw "internal: bad split type"
  | _ =>
    if a.isNeutral then pure (.splitApp f k env a)
    else throw s!"internal: pattern matching on a non-constructor in {f}"

partial def findBranch (f c : String) : M Branch := do
  let info ← lookupDef f
  match info.branches.find? (·.ctor == c) with
  | some b => pure b
  | none => throw s!"internal: no branch for {c} in {f}"

-- ### Nominal action: substitute formula `r` for atom `i`

partial def act (i : Atom) (r : Formula) (v : Val) : M Val := do
  tick
  if !v.hasAtom i then return v
  match v with
  | .glued g k sp => return .glued g k (← actEnv i r sp)
  | .univ _ => pure v
  | .pi x a env b => return .pi x (← act i r a) (← actEnv i r env) b
  | .lam x env b => return .lam x (← actEnv i r env) b
  | .sigma x a env b => return .sigma x (← act i r a) (← actEnv i r env) b
  | .pair a b => return .pair (← act i r a) (← act i r b)
  | .piI l => return .piI (← act i r l)
  | .pathP l a b => return .pathP (← act i r l) (← act i r a) (← act i r b)
  | .plam j b =>
    if j == i then pure v
    else if r.mentions j then
      let k ← freshAtom
      let b' ← act j (atomF k) b
      return .plam k (← act i r b')
    else return .plam j (← act i r b)
  | .data d k ps => return .data d k (← ps.mapM (act i r))
  | .con c as => return .con c (← as.mapM (act i r))
  | .pcon c as ds => do mkPCon c (← as.mapM (act i r)) (ds.map (·.subst i r))
  | .hcompF ty u sys => do mkHCompF (← act i r ty) (← act i r u) (← actSys i r sys)
  | .glueTy b sys => do mkGlueTy (← act i r b) (← actSys i r sys)
  | .glue a sys => do mkGlue (← act i r a) (← actSys i r sys)
  | .split f k env => return .split f k (← actEnv i r env)
  | .var l ty => return .var l (← act i r ty)
  | .gvar n ty => return .gvar n (← act i r ty)
  | .app f a => do app (← act i r f) (← act i r a)
  | .fst p => do fstV (← act i r p)
  | .snd p => do sndV (← act i r p)
  | .papp p s => do papp (← act i r p) (s.subst i r)
  | .splitApp f k env a => do splitApp f k (← actEnv i r env) (← act i r a)
  | .transp l φ u => do transpLine (← act i r l) (φ.subst i r) (← act i r u)
  | .hcomp a u sys => do hcompLines (← act i r a) (← act i r u) (← actSys i r sys)
  | .unglue u b sys => do unglueV (← act i r u) (← act i r b) (← actSys i r sys)

partial def actEnv (i : Atom) (r : Formula) (env : Env) : M Env :=
  env.mapM fun
    | .v v => return .v (← act i r v)
    | .d s => pure (.d (s.subst i r))

partial def actSys (i : Atom) (r : Formula) (sys : System Val) : M (System Val) := do
  let mut out : System Val := []
  for (α, u) in sys.reverse do
    match α.lookup i with
    | some d =>
      let β := α.erase i
      for δ in (β.applyF r).inv d do
        match Face.meet? δ β with
        | some m => out := System.insert m (← faceV u (δ.minus β)) out
        | none => pure ()
    | none => out := System.insert α (← act i (α.applyF r) u) out
  return out

partial def faceV (v : Val) (α : Face) : M Val :=
  α.foldlM (fun v (i, d) => act i (Formula.ofDir d) v) v

partial def faceEnv (env : Env) (α : Face) : M Env :=
  α.foldlM (fun env (i, d) => actEnv i (Formula.ofDir d) env) env

partial def faceSys (sys : System Val) (α : Face) : M (System Val) :=
  α.foldlM (fun s (i, d) => actSys i (Formula.ofDir d) s) sys

-- ### Smart constructors

partial def mkGlueTy (b : Val) (sys : System Val) : M Val := do
  match sys.eps? with
  | some te => fstV te
  | none => pure (.glueTy b sys)

partial def mkGlue (a : Val) (sys : System Val) : M Val :=
  match sys.eps? with
  | some t => pure t
  | none => pure (.glue a sys)

partial def mkHCompF (ty u : Val) (sys : System Val) : M Val := do
  match sys.eps? with
  | some l => papp l Formula.one
  | none => pure (.hcompF ty u sys)

partial def mkPCon (c : String) (args : List Val) (dims : List Formula) : M Val := do
  let info ← lookupCtor c
  let env := dims.reverse.map EnvE.d ++ args.reverse.map EnvE.v
  let bsys ← evalSys env info.boundary
  match bsys.eps? with
  | some v => pure v
  | none => pure (.pcon c args dims)

partial def unglueV (u b : Val) (sys : System Val) : M Val := do
  match sys.eps? with
  | some te => app (← fstV (← sndV te)) u
  | none =>
    match ← unfoldM u with
    | .glue a _ => pure a
    | _ => pure (.unglue u b sys)

-- ### Kan operations (the specification's: `transp` and `hcomp` primitive, `comp` and the
-- fillers derived; Coquand–Huber–Mörtberg's computation rules)

partial def lines (i : Atom) (us : System Val) : System Val := us.map fun (α, v) => (α, .plam i v)

/-- The cofibration of a face. -/
partial def faceF (α : Face) : Formula :=
  α.foldl (fun r (i, d) => r.and (if d == .one then atomF i else natomF i)) Formula.one

/-- `v` on the faces of `φ`, as a system (elements restricted to their faces). -/
partial def sysOf (φ : Formula) (v : Val) : M (System Val) :=
  φ.faces.foldlM (fun s α => do return System.insert α (← faceV v α) s) []

/-- `transp i a φ u0`: `a` mentions `i`, is constant where `φ` holds, and `u0 : a(i/0)`. -/
partial def transp (i : Atom) (a : Val) (φ : Formula) (u0 : Val) : M Val := do
  if φ.isOne then return u0
  let stuck : M Val := pure (.transp (.plam i a) φ u0)
  match ← force a with
  | .univ _ => pure u0
  | .sigma _ a1 env b =>
    let u1 ← fstV u0
    let u2 ← sndV u0
    let f1 ← if b.occurs 0 then transpFill i a1 φ u1 else pure u1
    return .pair (← transp i a1 φ u1) (← transp i (← inst env b f1) φ u2)
  | .pathP p v0 v1 =>
    let j ← freshAtom
    let uj ← papp u0 (atomF j)
    let sys := System.insert [(j, .zero)] (← faceV v0 [(j, .zero)])
      (System.insert [(j, .one)] (← faceV v1 [(j, .one)]) (← sysOf φ uj))
    return .plam j (← comp i (← papp p (atomF j)) uj sys)
  | .piI p =>
    let j ← freshAtom
    return .plam j (← transp i (← papp p (atomF j)) φ (← papp u0 (atomF j)))
  | .glueTy b es => transpGlue i b es φ u0
  | .data d k ps =>
    -- `transpData0`: the identity on a type without parameters
    if ps.isEmpty then pure u0
    else
      match ← force u0 with
      | .con c args => return .con c (← transpArgs i d k ps φ c args)
      | .pcon c args dims => mkPCon c (← transpArgs i d k ps φ c args) dims
      | .hcompF _ v sys =>
        -- `transpHcomp`: transport the base and the sides
        let line : Val := .data d k ps
        let sys' ← sys.mapM fun (α, l) => do
          let j ← freshAtom
          return (α, .plam j (← transp i (← faceV line α) (α.applyF φ) (← papp l (atomF j))))
        mkHCompF (← act i Formula.one line) (← transp i line φ v) sys'
      | _ => stuck
  | _ => stuck

/-- The transport filler `transp j (a(i ∧ j)) (φ ∨ i = 0) u`, a value mentioning `i`. -/
partial def transpFill (i : Atom) (a : Val) (φ : Formula) (u : Val) : M Val := do
  let j ← freshAtom
  transp j (← act i ((atomF i).and (atomF j)) a) (φ.or (natomF i)) u

/-- `transpCon`: the arguments of a constructor, transported along their types (a telescope
whose earlier entries are the transport fillers). -/
partial def transpArgs (i : Atom) (d : String) (k : Nat) (ps : List Val) (φ : Formula) (c : String)
    (args : List Val) : M (List Val) := do
  let _ := d
  let ctor ← lookupCtor c
  let tele := ctor.tele.map fun (x, t) => (x, t.lift k)
  let mut env : Env := ps.reverse.map .v
  let mut out := #[]
  let mut rest := tele
  for a in args do
    let (ty, later) := match rest with
      | (_, ty) :: later => (ty, later)
      | [] => (Tm.univ 0, [])
    rest := later
    let A ← eval env ty
    out := out.push (← transp i A φ a)
    let needed := (later.zip (List.range later.length)).any fun ((_, t), n) => t.occurs n
    env := .v (← if needed then transpFill i A φ a else pure a) :: env
  return out.toList

/-- `hcomp i a u0 us`: `a` does not mention `i`; the elements of `us` do, and `us(i/0) = u0`. -/
partial def hcomp (i : Atom) (a u0 : Val) (us : System Val) : M Val := do
  match us.eps? with
  | some v => act i Formula.one v
  | none =>
  let stuck : M Val := pure (.hcomp a u0 (lines i us))
  match ← force a with
  | .sigma _ a1 env b =>
    let u1 ← fstV u0
    let u2 ← sndV u0
    let us1 ← us.mapM fun (α, v) => return (α, ← fstV v)
    let us2 ← us.mapM fun (α, v) => return (α, ← sndV v)
    let h1 ← if b.occurs 0 then hfill i a1 u1 us1 else pure u1
    return .pair (← hcomp i a1 u1 us1) (← comp i (← inst env b h1) u2 us2)
  | .pathP p v0 v1 =>
    let j ← freshAtom
    let usj ← us.mapM fun (α, v) => return (α, ← papp v (atomF j))
    let sys := System.insert [(j, .zero)] (← faceV v0 [(j, .zero)])
      (System.insert [(j, .one)] (← faceV v1 [(j, .one)]) usj)
    return .plam j (← hcomp i (← papp p (atomF j)) (← papp u0 (atomF j)) sys)
  | .piI p =>
    let j ← freshAtom
    let usj ← us.mapM fun (α, v) => return (α, ← papp v (atomF j))
    return .plam j (← hcomp i (← papp p (atomF j)) (← papp u0 (atomF j)) usj)
  | .glueTy b es => hcompGlue i b es u0 us
  | .univ _ => hcompU i u0 us
  | .data d k ps =>
    if (← lookupData d).isHIT then mkHCompF a u0 (lines i us)
    else
      -- `hcompCon`: componentwise on a constructor whose sides are the same constructor
      match ← force u0 with
      | .con c args =>
        let cols? ← us.foldrM (fun (α, v) acc => do
          match acc with
          | none => pure none
          | some cols =>
            match ← force v with
            | .con c' bs => pure (if c' == c && bs.length == cols.length
                then some ((cols.zip bs).map fun (col, b) => (α, b) :: col) else none)
            | _ => pure none) (some (args.map fun _ => []))
        match cols? with
        | some cols => return .con c (← hcompArgs i d k ps c args cols)
        | none => stuck
      | _ => stuck
  | _ => stuck

/-- `hcompCon`'s telescope: recursive arguments by `hcomp`, the others by `comp` along their
types, in which earlier arguments are their fillers. -/
partial def hcompArgs (i : Atom) (d : String) (k : Nat) (ps : List Val) (c : String)
    (args : List Val) (cols : List (System Val)) : M (List Val) := do
  let ctor ← lookupCtor c
  let tele := ctor.tele.map fun (x, t) => (x, t.lift k)
  let mut env : Env := ps.reverse.map .v
  let mut out := #[]
  let mut rest := tele
  let mut n := 0
  for (a, s) in args.zip cols do
    let (ty, later) := match rest with
      | (_, ty) :: later => (ty, later)
      | [] => (Tm.univ 0, [])
    rest := later
    let A ← eval env ty
    let isRec := ctor.recArgs.getD n false
    n := n + 1
    let _ := d
    out := out.push (← if isRec then hcomp i A a s else comp i A a s)
    let needed := (later.zip (List.range later.length)).any fun ((_, t), m) => t.occurs m
    env := .v (← if !needed then pure a else if isRec then hfill i A a s else fill i A a s) :: env
  return out.toList

/-- The filler `hcomp j a [us(i ∧ j), i = 0 ↦ u0] u0`, a value mentioning `i`. -/
partial def hfill (i : Atom) (a u0 : Val) (us : System Val) : M Val := do
  let j ← freshAtom
  let ij := (atomF i).and (atomF j)
  let us' ← us.mapM fun (α, v) => return (α, ← act i ij v)
  hcomp j a u0 (System.insert [(i, .zero)] u0 us')

/-- `comp i a u0 us = hcomp a(1) [us ↦ k. transp (m. a(k ∨ m)) (k = 1) u(k)] (transp i a 0 u0)`. -/
partial def comp (i : Atom) (a u0 : Val) (us : System Val) : M Val := do
  match us.eps? with
  | some v => act i Formula.one v
  | none =>
  let k ← freshAtom
  let sys ← us.mapM fun (α, v) => do
    let m ← freshAtom
    let lineα ← faceV (← act i ((atomF k).or (atomF m)) a) α
    return (α, ← transp m lineα (atomF k) (← act i (atomF k) v))
  hcomp k (← act i Formula.one a) (← transp i a Formula.zero u0) sys

/-- `fill i a u us`: a value mentioning `i`, equal to `u` at `i = 0` and the composition at `i = 1`. -/
partial def fill (i : Atom) (a u : Val) (us : System Val) : M Val := do
  let j ← freshAtom
  let ij := (atomF i).and (atomF j)
  let a' ← act i ij a
  let us' ← us.mapM fun (α, v) => return (α, ← act i ij v)
  comp j a' u (System.insert [(i, Dir.zero)] u us')

/-- A stuck transport along `line`, recomputed. -/
partial def transpLine (line : Val) (φ : Formula) (u0 : Val) : M Val := do
  let k ← freshAtom
  transp k (← papp line (atomF k)) φ u0

/-- A stuck composition with sides given as lines, recomputed. -/
partial def hcompLines (a u0 : Val) (sys : System Val) : M Val := do
  let k ← freshAtom
  hcomp k a u0 (← sys.mapM fun (α, l) => return (α, ← papp l (atomF k)))

/-- `transpPi`, when a stuck transport in a Π-type is applied:
`(transp (i. Π A B) φ u0) v = transp (i. B[w(i)]) φ (u0 w(0))`, `w(i) = transp (j. A(i ∨ ~j)) (φ ∨ i) v`. -/
partial def appTransp (line : Val) (φ : Formula) (u0 v : Val) : M Val := do
  let i ← freshAtom
  match ← force (← papp line (atomF i)) with
  | .pi _ a envB b =>
    let j ← freshAtom
    let w ← transp j (← act i ((atomF i).or (natomF j)) a) (φ.or (atomF i)) v
    let w0 ← act i Formula.zero w
    transp i (← inst envB b w) φ (← app u0 w0)
  | _ => pure (.app (.transp line φ u0) v)

/-- `hcompPi`, when a stuck composition in a Π-type is applied. -/
partial def appHcomp (a u0 : Val) (sys : System Val) (v : Val) : M Val := do
  match ← force a with
  | .pi _ _ envB b =>
    let i ← freshAtom
    let us ← sys.mapM fun (α, l) => do return (α, ← app (← papp l (atomF i)) (← faceV v α))
    hcomp i (← inst envB b v) (← app u0 v) us
  | _ => pure (.app (.hcomp a u0 sys) v)

/-- `Σ (x : T), Path A (f x) y` -/
partial def fiberTy (t a f y : Val) : M Val := eval [.v y, .v f, .v a, .v t] fiberTm

/-- `hcompU`: `hcomp U [φ ↦ i. u] u0 = Glue u0 [φ ↦ (u(1), lineEquiv (u(~i)))]`. -/
partial def hcompU (i : Atom) (u0 : Val) (us : System Val) : M Val := do
  let es ← us.mapM fun (α, v) => do
    let k ← freshAtom
    let line : Val := .plam k (← act i (natomF k) v)
    return (α, Val.pair (← act i Formula.one v) (← eval [.v line] lineEquivTm))
  mkGlueTy u0 es

/-- `hcompGlue`: `glue [φ ↦ hcomp T [ψ ↦ u] u0]
  (hcomp A [ψ ↦ unglue u, φ ↦ e.1 (hfill T [ψ ↦ u] u0)] (unglue u0))`. -/
partial def hcompGlue (i : Atom) (b : Val) (es : System Val) (u0 : Val) (us : System Val) : M Val := do
  let parts ← es.mapM fun (α, te) => do
    let t ← fstV te
    let e ← sndV te
    let u0α ← faceV u0 α
    let usα ← faceSys us α
    let tα ← hcomp i t u0α usα
    let hf ← hfill i t u0α usα
    return (α, tα, ← app (← fstV e) hf)
  let usU ← us.mapM fun (β, v) => do return (β, ← unglueV v (← faceV b β) (← faceSys es β))
  let sys := System.union usU (parts.map fun (α, _, h) => (α, h))
  let a1 ← hcomp i b (← unglueV u0 b es) sys
  mkGlue a1 (parts.map fun (α, t, _) => (α, t))

/-- `transpGlue` (CHM): transport in a line of Glue types `Glue b(i) [φ(i) ↦ (T(i), e(i))]`. -/
partial def transpGlue (i : Atom) (b : Val) (es : System Val) (ψ : Formula) (u0 : Val) : M Val := do
  let b0 ← act i Formula.zero b
  let es0 ← actSys i Formula.zero es
  let a0 ← unglueV u0 b0 es0
  -- on ψ the Glue line is constant, so ungluing `u0` along it gives a tube in `b`
  let tube ← unglueV u0 b es
  let tubeSys ← sysOf ψ tube
  let a1' ← comp i b a0 tubeSys
  let b1 ← act i Formula.one b
  let es1 ← actSys i Formula.one es
  -- `∀ i. φ`: the faces of the Glue line that do not mention `i`
  let δs := es.filter fun (β, _) => !β.mentions i
  let exts ← es1.mapM fun (α, te1) => do
    let t1 ← fstV te1
    let e1 ← sndV te1
    let a1'α ← faceV a1' α
    let c ← app (← sndV e1) a1'α
    let fib ← fiberTy t1 (← faceV b1 α) (← fstV e1) a1'α
    let k ← freshAtom
    let mut sys : System Val := []
    -- on `∀ i. φ`: the transported fibre element `(transp T ψ u0, ω)`
    for (β, te) in δs do
      if let some γ := Face.meet? α β then
        let tγ ← faceV (← fstV te) γ
        let eγ ← faceV (← sndV te) γ
        let ψγ := γ.applyF ψ
        let u0γ ← faceV u0 γ
        let bγ ← faceV b γ
        let f := fun (x : Val) => do app (← fstV eγ) x
        let t1' ← transp i tγ ψγ u0γ
        let j ← freshAtom
        let tf ← transpFill i tγ ψγ u0γ
        let fl ← fill i bγ (← faceV a0 γ) (← sysOf ψγ (← faceV tube γ))
        let sω := System.insert [(j, .zero)] (← f tf)
          (System.insert [(j, .one)] fl (← sysOf ψγ (← f u0γ)))
        let base ← app (← fstV (← act i Formula.zero eγ)) u0γ
        let ω : Val := .plam j (← comp i bγ base sω)
        let cγ ← faceV c γ
        -- (the extension lives under `α`: its faces are relative to `α`)
        sys := System.insert (γ.minus α) (← papp (← app (← sndV cγ) (.pair t1' ω)) (atomF k)) sys
    -- on ψ: the fibre element `(u0, refl)`
    for δψ in ψ.faces do
      if let some γ := Face.meet? α δψ then
        let cγ ← faceV c γ
        let j ← freshAtom
        let pt : Val := .pair (← faceV u0 γ) (.plam j (← faceV a1' γ))
        sys := System.insert (γ.minus α) (← papp (← app (← sndV cγ) pt) (atomF k)) sys
    return (α, ← hcomp k fib (← fstV c) sys)
  let k ← freshAtom
  let mut sysA : System Val := ← sysOf ψ a1'
  for (α, ext) in exts do
    sysA := System.insert α (← papp (← sndV ext) (natomF k)) sysA
  let a1 ← hcomp k b1 a1' sysA
  mkGlue a1 (← exts.mapM fun (α, ext) => return (α, ← fstV ext))
end

end Kubus
