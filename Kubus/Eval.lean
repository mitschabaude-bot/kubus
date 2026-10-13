import Kubus.Value

/-!
# Evaluation and Kan operations

The Kan operations follow CCHM ("Cubical Type Theory: a constructive interpretation
of the univalence axiom") and the cubicaltt implementation: a heterogeneous
composition `comp i A u0 [α ↦ u]` is primitive and computes by cases on `A`.
Higher inductive types have a formal homogeneous composition as a canonical form.
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
    let av ← eval env a
    -- in a higher inductive type, homogeneous composition is the formal `hcomp` constructor
    -- (read-back prints `hcompF` as `hcomp`, so this keeps evaluation stable under read-back)
    if let .data d _ _ := av then
      if (← lookupData d).isHIT then
        if let some v := us.eps? then return ← act i Formula.one v
        return ← mkHCompF av (← eval env u0) (lines i us)
    comp i av (← eval env u0) us
  | .fill _ a sys u0 => do
    let i ← freshAtom
    let av ← eval (.d (atomF i) :: env) a
    let us ← evalSysUnder env i sys
    return .plam i (← fill i av (← eval env u0) us)
  | .glueTy a sys => do mkGlueTy (← eval env a) (← evalSys env sys)
  | .glue sys a => do mkGlue (← eval env a) (← evalSys env sys)
  | .unglue u b sys => do unglueV (← eval env u) (← eval env b) (← evalSys env sys)
  | .compU a sys => do mkCompU (← eval env a) (← evalSys env sys)
  | .unglueU u b sys => do unglueUV (← eval env u) (← eval env b) (← evalSys env sys)
  | .data d k ps => do
    let k := if k == 0 || (← lookupData d).liftInvariant then 0 else k
    return .data d k (← ps.mapM (eval env))
  | .con c args dims => do
    let as ← args.mapM (eval env)
    if dims.isEmpty then pure (.con c as) else mkPCon c as (← dims.mapM (evalI env))
  | .split f k => pure (.split f k env)
  | .letE _ t b => do eval (.v (← eval env t) :: env) b

partial def evalGlob (n : String) (k : Nat) : M Val := do
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
  | .lam _ env b => eval (.v a :: env) b
  | .split fn k env => splitApp fn k env a
  | .comp line u0 sys => appComp line u0 sys a
  | _ =>
    if f.isNeutral then pure (.app f a)
    else throw "internal: applying a non-function"

partial def fstV (p : Val) : M Val := do
  match p with
  | .pair a _ => pure a
  | _ => if p.isNeutral then pure (.fst p) else throw "internal: fst of a non-pair"

partial def sndV (p : Val) : M Val := do
  match p with
  | .pair _ b => pure b
  | _ => if p.isNeutral then pure (.snd p) else throw "internal: snd of a non-pair"

partial def papp (v : Val) (r : Formula) : M Val := do
  match v with
  | .plam i b => act i r b
  | _ =>
    match r.toDir? with
    | some d =>
      match ← inferNe v with
      | some (.pathP _ a b) => pure (if d == .zero then a else b)
      | _ => pure (.papp v r)
    | none => pure (.papp v r)

/-- Type of a neutral value, if it can be determined. -/
partial def inferNe (v : Val) : M (Option Val) := do
  match v with
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
  | .comp l _ _ => return some (← papp l Formula.one)
  | .unglue _ b _ | .unglueU _ b _ => pure (some b)
  | _ => pure none

/-- The type `(x : D) → B x` of the split of `f`, with `f`'s parameters instantiated. -/
partial def splitFnType (f : String) (k : Nat) (env : Env) : M Val := do
  let info ← lookupDef f
  let ty0 ← if k == 0 then pure info.ty else eval [] (info.tyTm.lift k)
  let mut ty := ty0
  for e in env.reverse do
    match ty, e with
    | .pi _ _ env' b, .v p => ty ← inst env' b p
    | _, _ => throw "internal: bad split type"
  return ty

partial def splitApp (f : String) (k : Nat) (env : Env) (a : Val) : M Val := do
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
      let fl ← fill j d u0 wsj
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

/-- Application of a stuck composition in a Π-type. -/
partial def appComp (line u0 : Val) (sys : System Val) (v1 : Val) : M Val := do
  let j ← freshAtom
  match ← papp line (atomF j) with
  | .pi _ a envB b =>
    let w ← transFillNeg j a v1
    let w0 ← act j Formula.zero w
    let motive ← inst envB b w
    let us ← sys.mapM fun (α, l) => do
      return (α, ← app (← papp l (atomF j)) (← faceV w α))
    comp j motive (← app u0 w0) us
  | _ => pure (.app (.comp line u0 sys) v1)

-- ### Nominal action: substitute formula `r` for atom `i`

partial def act (i : Atom) (r : Formula) (v : Val) : M Val := do
  tick
  match v with
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
  | .compU b sys => do mkCompU (← act i r b) (← actSys i r sys)
  | .split f k env => return .split f k (← actEnv i r env)
  | .var l ty => return .var l (← act i r ty)
  | .gvar n ty => return .gvar n (← act i r ty)
  | .app f a => do app (← act i r f) (← act i r a)
  | .fst p => do fstV (← act i r p)
  | .snd p => do sndV (← act i r p)
  | .papp p s => do papp (← act i r p) (s.subst i r)
  | .splitApp f k env a => do splitApp f k (← actEnv i r env) (← act i r a)
  | .comp l u sys => do compLine (← act i r l) (← act i r u) (← actSys i r sys)
  | .unglue u b sys => do unglueV (← act i r u) (← act i r b) (← actSys i r sys)
  | .unglueU u b sys => do unglueUV (← act i r u) (← act i r b) (← actSys i r sys)

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

partial def mkCompU (b : Val) (sys : System Val) : M Val := do
  match sys.eps? with
  | some l => papp l Formula.one
  | none => pure (.compU b sys)

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
    match u with
    | .glue a _ => pure a
    | _ => pure (.unglue u b sys)

/-- The function `E(1) → E(0)` of a line of types: transport backwards. -/
partial def lineFun (line u : Val) : M Val := do
  let j ← freshAtom
  transNeg j (← papp line (atomF j)) u

partial def unglueUV (u b : Val) (sys : System Val) : M Val := do
  match sys.eps? with
  | some line => lineFun line u
  | none =>
    match u with
    | .glue a _ => pure a
    | _ => pure (.unglueU u b sys)

-- ### Composition

partial def lines (i : Atom) (us : System Val) : System Val := us.map fun (α, v) => (α, .plam i v)

partial def compLine (line u : Val) (sys : System Val) : M Val := do
  let i ← freshAtom
  let a ← papp line (atomF i)
  let us ← sys.mapM fun (α, l) => return (α, ← papp l (atomF i))
  comp i a u us

/-- `comp i a u us`: `a` and the elements of `us` may mention `i`; `u : a(i/0)`. Result in `a(i/1)`. -/
partial def comp (i : Atom) (a u : Val) (us : System Val) : M Val := do
  match us.eps? with
  | some v => act i Formula.one v
  | none =>
  let stuck : M Val := pure (.comp (.plam i a) u (lines i us))
  match a with
  | .pathP p v0 v1 =>
    let j ← freshAtom
    let pj ← papp p (atomF j)
    let usj ← us.mapM fun (α, v) => return (α, ← papp v (atomF j))
    let sys := System.insert [(j, Dir.zero)] v0 (System.insert [(j, Dir.one)] v1 usj)
    return .plam j (← comp i pj (← papp u (atomF j)) sys)
  | .piI p =>
    let j ← freshAtom
    let usj ← us.mapM fun (α, v) => return (α, ← papp v (atomF j))
    return .plam j (← comp i (← papp p (atomF j)) (← papp u (atomF j)) usj)
  | .sigma _ a env b =>
    let u1 ← fstV u
    let u2 ← sndV u
    let us1 ← us.mapM fun (α, v) => return (α, ← fstV v)
    let us2 ← us.mapM fun (α, v) => return (α, ← sndV v)
    -- the filler is only needed if the second component's type is dependent
    let f1 ← if b.occurs 0 then fill i a u1 us1 else pure u1
    let c1 ← comp i a u1 us1
    let c2 ← comp i (← inst env b f1) u2 us2
    return .pair c1 c2
  | .univ _ => mkCompU u (lines i us)
  | .compU b es => compGlue true i b es u us
  | .glueTy b es => compGlue false i b es u us
  | .data d k ps =>
    let info ← lookupData d
    if info.isHIT then
      if ps.isEmpty then mkHCompF a u (lines i us) else compHIT i a u us
    else if info.firstOrder && us.isEmpty then pure u
    else
      match u with
      | .con c args =>
        let sysArgs? : Option (List (System Val)) :=
          us.foldr (fun (α, v) acc => acc.bind fun cols =>
            match v with
            | .con c' bs => if c' == c && bs.length == cols.length
                then some ((cols.zip bs).map fun (col, b) => (α, b) :: col) else none
            | _ => none) (some (args.map fun _ => []))
        match sysArgs? with
        | some cols =>
          let ctor ← lookupCtor c
          return .con c (← comps i (ctor.tele.map fun (x, t) => (x, t.lift k)) (ps.reverse.map .v) args cols)
        | none => stuck
      | _ => stuck
  | _ => stuck

/-- Composition in a higher inductive type with parameters (Coquand–Huber–Mörtberg):
transport the base and the sides to `i = 1`, then take the formal homogeneous composition. -/
partial def compHIT (i : Atom) (a u : Val) (us : System Val) : M Val := do
  let stuck : M Val := pure (.comp (.plam i a) u (lines i us))
  match ← hitPush i a u none with
  | none => stuck
  | some u1 =>
    let a1 ← act i Formula.one a
    let mut sys : System Val := []
    for (α, v) in us do
      let j ← freshAtom
      let aij ← faceV (← act i ((atomF i).or (atomF j)) a) α
      match ← hitPush j aij v (some (Face.single i .one)) with
      | some w => sys := System.insert α w sys
      | none => return ← stuck
    mkHCompF a1 u1 (lines i sys)

/-- Componentwise `comp j a v [face ↦ v]` on canonical elements of a higher inductive type
(`face` must not mention `j`). Returns `none` on neutral elements. -/
partial def hitPush (j : Atom) (a v : Val) (face : Option Face) : M (Option Val) := do
  match a with
  | .data d dk ps =>
    let pushArgs (c : String) (args : List Val) : M (Option (List Val)) := do
      let ctor ← lookupCtor c
      let mut env : Env := ps.reverse.map .v
      let mut out : Array Val := #[]
      let mut rest := ctor.tele.map fun (x, t) => (x, t.lift dk)
      for arg in args do
        let (ty, later) := match rest with
          | (_, ty) :: later => (ty, later)
          | [] => (Tm.univ 0, [])
        rest := later
        let A ← eval env ty
        -- system elements must be restricted to their faces (`actSys` relies on it)
        let sysK : System Val ← match face with
          | some f => do pure [(f, ← faceV arg f)]
          | none => pure []
        let r ← match A with
          | .data d' _ _ => if d' == d then hitPush j A arg face else some <$> comp j A arg sysK
          | _ => some <$> comp j A arg sysK
        match r with
        | some r => out := out.push r
        | none => return none
        let needed := (later.zip (List.range later.length)).any fun ((_, t), k) => t.occurs k
        env := .v (← if needed then fill j A arg sysK else pure arg) :: env
      return some out.toList
    match v with
    | .con c args => return (← pushArgs c args).map (.con c)
    | .pcon c args dims =>
      match ← pushArgs c args with
      | some outs => some <$> mkPCon c outs dims
      | none => pure none
    | .hcompF _ u0 sys =>
      let some u0' ← hitPush j a u0 face | return none
      let mut sys' : System Val := []
      for (α, l) in sys do
        let k ← freshAtom
        let faceα := face.bind fun f => if f.compatible α then some (f.minus α) else none
        let some w ← hitPush j (← faceV a α) (← papp l (atomF k)) faceα | return none
        sys' := System.insert α (.plam k w) sys'
      some <$> mkHCompF (← act j Formula.one a) u0' sys'
    | _ => pure none
  | _ => pure none

/-- Componentwise composition along a telescope. -/
partial def comps (i : Atom) (tele : List (String × Tm)) (env : Env) (as : List Val)
    (sys : List (System Val)) : M (List Val) := do
  let mut env := env
  let mut out := #[]
  let mut rest := tele
  for (a, s) in as.zip sys do
    let (ty, later) := match rest with
      | (_, ty) :: later => (ty, later)
      | [] => (Tm.univ 0, [])
    rest := later
    let A ← eval env ty
    out := out.push (← comp i A a s)
    -- the filler is only needed if a later argument type depends on this argument
    let needed := (later.zip (List.range later.length)).any fun ((_, t), k) => t.occurs k
    env := .v (← if needed then fill i A a s else pure a) :: env
  return out.toList

/-- `fill i a u us`: a value mentioning `i`, equal to `u` at `i = 0` and the composition at `i = 1`. -/
partial def fill (i : Atom) (a u : Val) (us : System Val) : M Val := do
  let j ← freshAtom
  let ij := (atomF i).and (atomF j)
  let a' ← act i ij a
  let us' ← us.mapM fun (α, v) => return (α, ← act i ij v)
  comp j a' u (System.insert [(i, Dir.zero)] u us')

partial def sym (i : Atom) (v : Val) : M Val := act i (natomF i) v

partial def compNeg (i : Atom) (a u : Val) (us : System Val) : M Val := do
  comp i (← sym i a) u (← us.mapM fun (α, v) => return (α, ← sym i v))

partial def transNeg (i : Atom) (a u : Val) : M Val := do comp i (← sym i a) u []

partial def transFill (i : Atom) (a u : Val) : M Val := fill i a u []

/-- A line from `transNeg i a u` (at `i = 0`) to `u` (at `i = 1`). -/
partial def transFillNeg (i : Atom) (a u : Val) : M Val := do sym i (← fill i (← sym i a) u [])

/-- `Σ (x : T), Path A (f x) y` -/
partial def fiberTy (t a f y : Val) : M Val := eval [.v y, .v f, .v a, .v t] fiberTm

/-- Extend a partial element of a fiber of an equivalence to a total one, using contractibility. -/
partial def extendFiber (te b y : Val) (partial_ : System Val) : M Val := do
  let t ← fstV te
  let e ← sndV te
  let f ← fstV e
  let contr ← app (← sndV e) y
  let c ← fstV contr
  let h ← sndV contr
  let k ← freshAtom
  let sys ← partial_.mapM fun (α, x) => do
    return (α, ← papp (← app (← faceV h α) x) (atomF k))
  comp k (← fiberTy t b f y) c sys

/-- Extend a partial element of a fiber of `lineFun e` over `b` to a total one. -/
partial def extendFiberLine (e b : Val) (partial_ : System Val) : M Val := do
  let i ← freshAtom
  let j ← freshAtom
  let ej ← papp e (atomF j)
  let e1 ← papp e Formula.one
  let tfb ← transFill j ej b
  let tb1 ← act j Formula.one tfb
  let thetas ← partial_.mapM fun (α, ap) => do
    let a ← fstV ap
    let qi ← papp (← sndV ap) (natomF i)
    let ejα ← faceV ej α
    let th ← fill j ejα qi
      (System.ofList [([(i, .zero)], ← faceV tfb α), ([(i, .one)], ← transFillNeg j ejα a)])
    return (α, th)
  let p1s ← thetas.mapM fun (α, th) => return (α, ← act j Formula.one th)
  let a ← comp i e1 tb1 p1s
  let atil ← fill i e1 tb1 p1s
  let sys := System.union thetas
    (System.ofList [([(i, .zero)], tfb), ([(i, .one)], ← transFillNeg j ej a)])
  let q ← compNeg j ej atil sys
  let k ← freshAtom
  return .pair a (.plam k (← act i (natomF k) q))

/-- Composition in `Glue b es` (or, if `isU`, in the composition type `compU b es`). -/
partial def compGlue (isU : Bool) (i : Atom) (b : Val) (es : System Val) (wi0 : Val) (ws : System Val) : M Val := do
  let ung (w : Val) (φ : Face) : M Val := do
    if isU then unglueUV w (← faceV b φ) (← faceSys es φ)
    else unglueV w (← faceV b φ) (← faceSys es φ)
  let dom (e : Val) : M Val := if isU then papp e Formula.one else fstV e
  let fn (e x : Val) : M Val := do
    if isU then lineFun e x else app (← fstV (← sndV e)) x
  let i0 := Face.single i .zero
  let i1 := Face.single i .one
  let vs ← ws.mapM fun (α, w) => return (α, ← ung w α)
  let vi0 ← ung wi0 i0
  let vi1' ← comp i b vi0 vs
  let esI1 ← faceSys es i1
  -- fibres are only needed where the type is glued at i = 1
  let es' := if esI1.isEmpty then [] else es.filter fun (γ, _) => !γ.mentions i
  let fibersys ← es'.mapM fun (γ, e) => do
    let t ← dom e
    let wγ ← faceV wi0 γ
    let wsγ ← faceSys ws γ
    let us' ← fill i t wγ wsγ
    let usi1' ← comp i t wγ wsγ
    let j ← freshAtom
    let fu ← fn e us'
    let l ← comp i (← faceV b γ) (← faceV vi0 γ) (System.insert [(j, Dir.zero)] fu (← faceSys vs γ))
    return (γ, Val.pair usi1' (.plam j l))
  let wsi1 ← faceSys ws i1
  let fibersys' ← esI1.mapM fun (δ, e) => do
    let fibs1 ← faceSys fibersys δ
    let fibs2 ← (← faceSys wsi1 δ).mapM fun (α, w) => do
      let v ← ung w (i1 ++ δ ++ α)
      let k ← freshAtom
      return (α, Val.pair w (.plam k v))
    let partial_ := System.union fibs1 fibs2
    let y ← faceV vi1' δ
    let ext ← if isU then extendFiberLine e y partial_
      else extendFiber e (← faceV b (i1 ++ δ)) y partial_
    return (δ, ext)
  let usi1 ← fibersys'.mapM fun (δ, p) => return (δ, ← fstV p)
  let k ← freshAtom
  let sides1 ← fibersys'.mapM fun (δ, p) => do return (δ, ← papp (← sndV p) (natomF k))
  let vsi1 ← faceSys vs i1
  let vi1 ← comp k (← faceV b i1) vi1' (System.union sides1 vsi1)
  mkGlue vi1 usi1

end

end Kubus
