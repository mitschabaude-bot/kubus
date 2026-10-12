import Kubus.Check

/-! # Declarations: definitions, data types, termination and positivity checks -/

namespace Kubus

def Tm.children : Tm → List (Nat × Tm)
  | .pi _ a b | .sigma _ a b => [(0, a), (1, b)]
  | .lam _ b | .piI _ b | .plam _ b => [(1, b)]
  | .app f a | .pair f a => [(0, f), (0, a)]
  | .fst t | .snd t | .papp t _ => [(0, t)]
  | .pathP a u v => [(0, a), (0, u), (0, v)]
  | .comp _ a sys u0 | .fill _ a sys u0 => (1, a) :: (0, u0) :: sys.map fun (_, t) => (1, t)
  | .hcomp _ a sys u0 => (0, a) :: (0, u0) :: sys.map fun (_, t) => (1, t)
  | .glueTy a sys | .glue sys a | .compU a sys => (0, a) :: sys.map fun (_, t) => (0, t)
  | .unglue u b sys | .unglueU u b sys => (0, u) :: (0, b) :: sys.map fun (_, t) => (0, t)
  | .data _ _ ps => ps.map (0, ·)
  | .con _ as _ => as.map (0, ·)
  | .letE _ t b => [(0, t), (1, b)]
  | _ => []

/-- Application spine: head and term arguments (interval applications are skipped). -/
def Tm.spine : Tm → Tm × List Tm
  | .app f a => let (h, as) := f.spine; (h, as ++ [a])
  | .papp f _ => f.spine
  | t => (t, [])

/-- Structural recursion: every occurrence of `f` is applied to its `k` parameters and a
structurally smaller argument: a recursive pattern variable, possibly applied (infinitary). -/
partial def termCheck (f : String) (k : Nat) (rec : List Nat) (depth : Nat) (t : Tm) : Except String Unit := do
  let (h, args) := t.spine
  match h with
  | .glob g _ =>
    if g == f then
      match args[k]? with
      | some a =>
        let ok := match a.spine.1 with
          | .var j => j ≥ depth && rec.contains (j - depth)
          | _ => false
        if !ok then throw s!"termination check failed: recursive call of {f} on an argument that is not structurally smaller"
      | none => throw s!"termination check failed: {f} must be applied to its parameters and a structurally smaller argument"
    for a in args do termCheck f k rec depth a
  | _ =>
    if args.isEmpty then
      for (s, c) in t.children do termCheck f k rec (depth + s) c
    else
      termCheck f k rec depth h
      for a in args do termCheck f k rec depth a

partial def Tm.mentionsData (d : String) (t : Tm) : Bool :=
  match t with
  | .data d' _ ps => d == d' || ps.any (·.mentionsData d)
  | _ => t.children.any fun (_, c) => c.mentionsData d

/-- Strict positivity of `d` in an argument type, at context depth `depth` with `np` parameters. -/
partial def strictPos (d : String) (np depth : Nat) (t : Tm) : Bool :=
  match t with
  | .data d' _ ps =>
    if d' == d then
      ps.length == np && (ps.zip (List.range np)).all fun (p, j) => match p with
        | .var i => i == depth - 1 - j
        | _ => false
    else !t.mentionsData d
  | .pi _ a b => !a.mentionsData d && strictPos d np (depth + 1) b
  | _ => !t.mentionsData d

/-- Boundary terms that commute with componentwise transport: point arguments of the
constructor (indices `nd ≤ i < nd + na`) and constructor applications. -/
partial def simpleBoundary (np na nd : Nat) (t : Tm) : Bool :=
  let _ := np
  match t with
  | .var i => nd ≤ i && i < nd + na
  | .con _ as _ => as.all (simpleBoundary np na nd)
  | _ => false

def isRecArg (d : String) : Tm → Bool
  | .data d' _ _ => d == d'
  | .pi _ _ b => isRecArg d b
  | _ => false

def ensureFresh (ctx : Ctx) (n : String) : M Unit := do
  let g ← getGlobals
  if g.defs.contains n || g.datas.contains n || g.ctors.contains n then
    err ctx s!"{n} is already defined"

/-- Elaborate a telescope; `none` marks interval binders. -/
def elabTele (ctx : Ctx) (bs : List Binder) : M (Ctx × List (String × Option Tm)) := do
  let mut ctx := ctx
  let mut out : Array (String × Option Tm) := #[]
  for b in bs do
    if let .intervalTy := stripLoc b.ty then
      let (c, _) ← ctx.bindDim b.name
      ctx := c
      out := out.push (b.name, none)
    else
      let (ta, _) ← inferType ctx b.ty
      let (c, _) := ctx.bindVar b.name (← eval ctx.env ta)
      ctx := c
      out := out.push (b.name, some ta)
  return (ctx, out.toList)

def teleType (tele : List (String × Option Tm)) (ty : Tm) : Tm :=
  tele.foldr (fun (x, a?) b => match a? with
    | some a => .pi x a b
    | none => .piI x b) ty

def teleLam (tele : List (String × Option Tm)) (body : Tm) : Tm :=
  tele.foldr (fun (x, a?) b => match a? with
    | some _ => .lam x b
    | none => .plam x b) body

def addDef (info : DefInfo) : M Unit :=
  modify fun s => { s with globals.defs := s.globals.defs.insert info.name info }

def checkDefn (name : String) (ps : List Binder) (ty body : Raw) (pos : Pos) : M Unit := do
  let ctx0 : Ctx := { pos }
  ensureFresh ctx0 name
  let (ctx, tele) ← elabTele ctx0 ps
  let (tty, _) ← inferType ctx ty
  let tbody ← check ctx body (← eval ctx.env tty)
  let fullTy := teleType tele tty
  addDef { name, ty := ← eval [] fullTy, tyTm := fullTy, body := some (teleLam tele tbody),
           value := none, nParams := 0, branches := [] }

def checkSplit (name : String) (ps : List Binder) (ty : Raw) (clauses : List Clause') (pos : Pos) : M Unit := do
  let ctx0 : Ctx := { pos }
  ensureFresh ctx0 name
  let (ctx, tele) ← elabTele ctx0 ps
  if tele.any (·.2.isNone) then err ctx0 "pattern-matching definitions cannot have interval parameters"
  let (tty, _) ← inferType ctx ty
  let vty ← eval ctx.env tty
  let (dName, dk, dps, envB, motive) ← match vty with
    | .pi _ (.data d dk dps) envB b => pure (d, dk, dps, envB, b)
    | _ => err ctx s!"a pattern-matching definition must have a type of the form (x : D) → B with D a data type"
  let fullTy := teleType tele tty
  let k := tele.length
  -- while its clauses are checked, `name` is an opaque constant
  addDef { name, ty := ← eval [] fullTy, tyTm := fullTy, body := none, value := none, nParams := k, branches := [] }
  let info ← lookupData dName
  for cl in clauses do
    if !(info.ctors.any (·.name == cl.ctor)) then
      err { ctx with pos := cl.pos } s!"{cl.ctor} is not a constructor of {dName}"
    if (clauses.filter (·.ctor == cl.ctor)).length > 1 then
      err { ctx with pos := cl.pos } s!"duplicate clause for {cl.ctor}"
  let mut branches : Array Branch := #[]
  let mut pending : Array (Ctx × Tm × Val × CtorInfo × List Val × List Formula) := #[]
  for ctor in info.ctors do
    let some cl := clauses.find? (·.ctor == ctor.name)
      | err ctx s!"missing clause for constructor {ctor.name}"
    let cctx := { ctx with pos := cl.pos }
    let nargs := ctor.tele.length
    let ndims := ctor.dims.length
    if cl.vars.length != nargs + ndims then
      err cctx s!"constructor {ctor.name} expects {nargs + ndims} pattern variables"
    let mut bctx := cctx
    let mut env : Env := dps.reverse.map .v
    let mut argVals : Array Val := #[]
    for ((_, aTy), x) in ctor.tele.zip (cl.vars.take nargs) do
      let a ← eval env (aTy.lift dk)
      let (c, xv) := bctx.bindVar x a
      bctx := c
      env := .v xv :: env
      argVals := argVals.push xv
    let mut dims : Array Formula := #[]
    for x in cl.vars.drop nargs do
      let (c, kAtom) ← bctx.bindDim x
      bctx := c
      dims := dims.push (Formula.atom kAtom)
    let cval ← if ndims == 0 then pure (Val.con ctor.name argVals.toList)
      else mkPCon ctor.name argVals.toList dims.toList
    let expected ← inst envB motive cval
    let tbody ← check bctx cl.body expected
    let rec_ := (List.range nargs).filter (ctor.recArgs[·]!) |>.map fun j => ndims + (nargs - 1 - j)
    match termCheck name k rec_ 0 tbody with
    | .ok () => pure ()
    | .error e => err cctx e
    branches := branches.push { ctor := ctor.name, nArgs := nargs, nDims := ndims, body := tbody }
    if ndims > 0 then pending := pending.push (bctx, tbody, expected, ctor, argVals.toList, dims.toList)
  addDef { name, ty := ← eval [] fullTy, tyTm := fullTy, body := some (teleLam tele (.split name 0)),
           value := none, nParams := k, branches := branches.toList }
  -- clauses for path constructors must agree with the clauses for their boundary
  for (bctx, tbody, expected, ctor, args, dims) in pending do
    let benv := dims.reverse.map EnvE.d ++ args.reverse.map EnvE.v
    let bsys ← evalSys benv ctor.boundary
    for (α, bv) in bsys do
      let ctxα ← bctx.face α
      let lhs ← eval ctxα.env tbody
      let penv ← faceEnv ctx.env α
      let rhs ← splitApp name 0 penv bv
      if !(← conv ctxα.lvl (← faceV expected α) lhs rhs) then
        err bctx s!"clause for {ctor.name} does not agree with its boundary:\n  clause gives: {← ppVal ctxα lhs}\n  boundary:     {← ppVal ctxα rhs}"

def checkData (name : String) (ps : List Binder) (lvl : Nat) (ctors : List CtorDecl) (pos : Pos) : M Unit := do
  let ctx0 : Ctx := { pos }
  ensureFresh ctx0 name
  let (ctx, tele) ← elabTele ctx0 ps
  if tele.any (·.2.isNone) then err ctx0 "data types cannot have interval parameters"
  let params := tele.map fun (x, a) => (x, a.get!)
  let np := params.length
  let dinfo : DataInfo := { name, params, level := lvl, ctors := [], isHIT := false, firstOrder := params.isEmpty }
  modify fun s => { s with globals.datas := s.globals.datas.insert name dinfo }
  for cd in ctors do
    let cctx := { ctx with pos := cd.pos }
    ensureFresh cctx cd.name
    let mut bctx := cctx
    let mut ctele : Array (String × Tm) := #[]
    let mut recArgs : Array Bool := #[]
    let mut dims : Array String := #[]
    for b in cd.args do
      if let .intervalTy := stripLoc b.ty then
        let (c, _) ← bctx.bindDim b.name
        bctx := c
        dims := dims.push b.name
      else
        if !dims.isEmpty then err cctx "interval arguments of a constructor must come last"
        let (ta, la) ← inferType bctx b.ty
        if la > lvl then err cctx s!"argument {b.name} of {cd.name} lives in universe {la}, but {name} is in universe {lvl}"
        if !strictPos name np bctx.lvl ta then
          err cctx s!"{name} does not occur strictly positively in the type of argument {b.name} of {cd.name}"
        ctele := ctele.push (b.name, ta)
        recArgs := recArgs.push (isRecArg name ta)
        let (c, _) := bctx.bindVar b.name (← eval bctx.env ta)
        bctx := c
    if dims.isEmpty && !cd.boundary.isEmpty then err cctx "only constructors with interval arguments can have a boundary"
    let dataV := Val.data name 0 (← (List.range np).mapM fun j => do
      match ← envGet ctx.env (np - 1 - j) with
      | .v v => pure v
      | _ => err cctx "internal")
    let (tsys, _) ← checkSys bctx none cd.boundary fun _ α _ => faceV dataV α
    if !dims.isEmpty && np > 0 && !(tsys.all fun (_, t) => simpleBoundary np ctele.size dims.size t) then
      err cctx "the boundary of a path constructor of a parameterised type may only use the constructor's point arguments and other constructors"
    let info : CtorInfo := { name := cd.name, data := name, tele := ctele.toList, recArgs := recArgs.toList,
                             dims := dims.toList, boundary := tsys }
    let g ← getGlobals
    let fo := dims.isEmpty && ctele.all fun (_, t) => match t with
      | .data d' _ [] => d' == name || (g.datas[d']?.map (·.firstOrder)).getD false
      | _ => false
    let upd (d : DataInfo) : DataInfo :=
      { d with ctors := d.ctors ++ [info], isHIT := d.isHIT || !info.dims.isEmpty, firstOrder := d.firstOrder && fo }
    modify fun s => { s with globals.ctors := s.globals.ctors.insert cd.name info,
                             globals.datas := s.globals.datas.modify name upd }

/-- Process a declaration (other than imports); returns output to print. -/
def checkDecl : Decl → M (Option String)
  | .defn n ps ty body pos => do checkDefn n ps ty body pos; pure none
  | .defSplit n ps ty cls pos => do checkSplit n ps ty cls pos; pure none
  | .data n ps l cs pos => do checkData n ps l cs pos; pure none
  | .eval t pos => do
    let ctx : Ctx := { pos }
    let (tm, ty) ← infer ctx t
    let v ← eval [] tm
    let nf ← quote ctx.qctx v
    let tyNf ← quote ctx.qctx ty
    pure (some s!"{pp [] 0 nf}\n  : {pp [] 0 tyNf}")
  | .check t pos => do
    let ctx : Ctx := { pos }
    let (_, ty) ← infer ctx t
    pure (some (pp [] 0 (← quote ctx.qctx ty)))
  | .importFile .. => pure none

end Kubus
