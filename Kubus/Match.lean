import Kubus.SelfCheck

/-! # Pattern matching

Clauses `| p1, ..., pn => t` with nested constructor patterns are compiled to a case tree of
single-argument splits, the only eliminator of the core language. The root split is the
definition itself: its parameters are the definition's parameters and the arguments before
the first column that contains a constructor pattern. A split whose branch needs further
matching calls an auxiliary split `f#n`, whose parameters are the variables bound so far and
whose arguments are the remaining columns. Auxiliary splits do not refer to `f`: recursive
calls on the recursive arguments of the root split's constructor are passed to them as
arguments, so every split only calls itself, structurally. Coverage is checked while
splitting (a constructor without clauses is a missing case), and a clause that is never used is
reported as redundant.
-/

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
      let (c, _) := ctx.bindVar (plainName b.name) (← eval ctx.env ta)
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

def zonkTele (tele : List (String × Option Tm)) : M (List (String × Option Tm)) :=
  tele.mapM fun (x, a?) => return (x, ← a?.mapM zonk)

def addDef (info : DefInfo) : M Unit :=
  modify fun s => { s with globals.defs := s.globals.defs.insert info.name info }

/-- A partial pattern, for messages about missing cases. -/
inductive PT
  | hole (id : Nat)
  | con (c : String) (args : List PT)
  deriving Inhabited

partial def PT.fill (id : Nat) (t : PT) : PT → PT
  | .hole i => if i == id then t else .hole i
  | .con c as => .con c (as.map (PT.fill id t))

partial def PT.show (top : Bool) : PT → String
  | .hole _ => "_"
  | .con c [] => c
  | .con c as =>
    let s := " ".intercalate (c :: as.map (PT.show false))
    if top then s else s!"({s})"

inductive ColKind
  | plain
  /-- the `r`-th argument of the root split's constructor, which is recursive -/
  | recArg (r : Nat)
  /-- the recursive call on the `r`-th argument of the root split's constructor -/
  | recFn (r : Nat)
  deriving Inhabited, BEq

structure Col where
  id : Nat
  kind : ColKind := .plain
  deriving Inhabited

structure Row where
  idx : Nat
  pats : List Pat
  /-- pattern variables bound to values: name, type, value -/
  aliases : List (String × Val × Val) := []
  body : Raw
  pos : Pos
  deriving Inhabited

structure MState where
  fname : String
  /-- number of parameters of the root split -/
  rootK : Nat := 0
  templates : List PT
  nextId : Nat
  used : Array Bool
  nAux : Nat := 0
  /-- self-check items for the clause bodies -/
  items : Array SCItem := #[]

abbrev MM := StateT MState M

/-- Levels of the variables holding the root constructor's recursive arguments (`recVars`)
and the recursive calls on them (`recFns`), by argument position. -/
structure RecInfo where
  recVars : List (Nat × Nat) := []
  recFns : List (Nat × Nat) := []

def RecInfo.bind (ri : RecInfo) (k : ColKind) (lvl : Nat) : RecInfo :=
  match k with
  | .plain => ri
  | .recArg r => { ri with recVars := (r, lvl) :: ri.recVars }
  | .recFn r => { ri with recFns := (r, lvl) :: ri.recFns }

/-- A constructor pattern: constructor, arguments, position. -/
def ctorPat? (p : Pat) : M (Option (String × List Pat × Pos)) := do
  match p with
  | .con c as pos => return some (c, as, pos)
  | .var x pos => return if (← getGlobals).ctors.contains x then some (x, [], pos) else none

def isCtorPat (p : Pat) : M Bool := return (← ctorPat? p).isSome

def wild (pos : Pos) : Pat := .var "_" pos

def errAt {α} (pos : Pos) (msg : String) : M α := throw s!"{pos.line}:{pos.col}: {msg}"

/-- The name to bind a column under: the first row's variable, if it has one. -/
def colName (rows : List Row) (i : Nat) (dflt : String) : M String := do
  match rows.head? >>= (·.pats[i]?) with
  | some (.var x _) => if x != "_" && !(← isCtorPat (.var x ⟨0, 0⟩)) then return x else return dflt
  | _ => return dflt

/-- Record the variable patterns of the first `n` columns as aliases of the bound values, and
drop these columns. -/
def bindPats (rows : List Row) (vals : List (String × Val × Val)) : List Row :=
  rows.map fun row =>
    let n := vals.length
    let al := (row.pats.take n).zip vals |>.filterMap fun (p, (nm, a, v)) => match p with
      | .var y _ => if y != "_" && y != nm then some (y, a, v) else none
      | _ => none
    { row with pats := row.pats.drop n, aliases := row.aliases ++ al }

/-- `Π (entries) . ty` over the innermost `n` entries of `ctx`, as a term in the context
without them. -/
def piOverEntries (ctx : Ctx) (n : Nat) (ty : Val) : M Tm := do
  let mut t ← quote ctx.fqctx ty
  let mut rest := ctx.entries
  for _ in [0:n] do
    match rest with
    | e :: es =>
      let sub : Ctx := { ctx with entries := es }
      t ← match e.ty with
        | some a => do pure (Tm.pi e.name (← quote sub.fqctx a) t)
        | none => pure (Tm.piI e.name t)
      rest := es
    | [] => pure ()
  return t

/-- Variables of the context as application arguments, outermost first, at depth `shift`. -/
def ctxArgs (ctx : Ctx) (shift : Nat) : List SArg :=
  let n := ctx.entries.length
  (List.range n).reverse.map fun i => match (ctx.entries[i]?.map (·.ty.isSome)) with
    | some true => SArg.tm (.var (i + shift))
    | _ => SArg.dim (.var (i + shift))

/-- Replace recursive calls `f ps (y_r) rest`, where `ps` are the root parameters, by the
variable holding the recursive call on `y_r`, applied to `rest`. -/
partial def rewriteRec (f : String) (k lvl : Nat) (ri : RecInfo) (c : Nat) (t : Tm) : Except String Tm := do
  let (h, args) := t.sargs
  match h with
  | .glob g _ =>
    if g == f then
      let paramsOk := (List.range k).all fun p => match args[p]? with
        | some (.tm (.var i)) => i == c + (lvl - 1 - p)
        | _ => false
      let target : Option (Nat × Nat) := match args[k]? with
        | some (.tm (.var v)) => ri.recVars.find? fun (rl : Nat × Nat) => v == c + (lvl - 1 - rl.2)
        | _ => none
      match paramsOk, target with
      | true, some (r, _) =>
        match ri.recFns.find? (fun (rl : Nat × Nat) => rl.1 == r) with
        | some (_, l) =>
          let rest ← (args.extract (k + 1) args.size).mapM fun (x : SArg) => match x with
            | .tm a => SArg.tm <$> rewriteRec f k lvl ri c a
            | .dim r => pure (SArg.dim r)
          return rest.foldl SArg.apply (.var (c + (lvl - 1 - l)))
        | none => throw "internal: missing recursive call"
      | _, _ => throw s!"termination check failed: under nested patterns, a recursive call of {f} must keep the parameters and the arguments before the matched one"
  | _ => pure ()
  if args.isEmpty then
    t.mapChildrenM fun n u => rewriteRec f k lvl ri (c + n) u
  else
    let h' ← rewriteRec f k lvl ri c h
    let args' ← args.mapM fun
      | .tm a => SArg.tm <$> rewriteRec f k lvl ri c a
      | .dim r => pure (SArg.dim r)
    return args'.foldl SArg.apply h'

/-- A leaf of the case tree: the remaining columns are variables; bind them and elaborate the
first row's body. Returns a term in `ctx`. -/
partial def compileLeaf (ctx : Ctx) (ty : Val) (cols : List Col) (rows : List Row) (ri : RecInfo)
    (underAux : Bool) : MM Tm := do
  let some row := rows.head? | throw "internal: empty leaf"
  modify fun s => { s with used := s.used.set! row.idx true }
  let mut lctx := ctx
  let mut ty := ty
  let mut ri := ri
  let mut binders : Array (String × Bool) := #[]
  for (col, p) in cols.zip row.pats do
    let nm := match p with | .var x _ => x | _ => "_"
    match ← force ty with
    | .pi x a env b =>
      let (c, xv) := lctx.bindVar nm a
      ri := ri.bind col.kind lctx.lvl
      lctx := c
      binders := binders.push ((if isImplName x then implName nm else nm), false)
      ty ← inst env b xv
    | .piI line =>
      let (c, k) ← lctx.bindDim nm
      lctx := c
      binders := binders.push (nm, true)
      ty ← papp line (atomF k)
    | t => errAt row.pos s!"too many patterns: {← ppVal lctx t} is not a function type"
  let mut bctx : Ctx := { lctx with pos := row.pos }
  for (y, a, v) in row.aliases do bctx := bctx.define y a v
  let tb ← check bctx row.body ty
  checkMetas
  let tb ← zonk tb
  let aliasTms ← row.aliases.toArray.mapM fun ((_, _, v) : String × Val × Val) => do
    return SArg.tm (← quote lctx.qctx v)
  let tb := tb.substArgs aliasTms
  let st ← get
  let lvl := lctx.lvl
  let recIdx := ri.recVars.map fun (_, l) => lvl - 1 - l
  match termCheck st.fname st.rootK recIdx 0 tb with
  | .ok () => pure ()
  | .error e => errAt row.pos e
  let tb ← if underAux then
      match rewriteRec st.fname st.rootK lvl ri 0 tb with
      | .ok t => pure t
      | .error e => errAt row.pos e
    else pure tb
  modify fun s => { s with items := s.items.push ⟨{ lctx with pos := row.pos }, tb, ty, s!"clause of {st.fname}"⟩ }
  return binders.foldr (fun (x, isDim) b => if isDim then .plam x b else .lam x b) tb

/-- Compile `rows` into the split function `name`, with parameters `ctx` (named `names` in its
body) followed by the leading columns, of type `Π ctx. ty`. -/
partial def compileSplit (name : String) (names : List String) (ctx : Ctx) (ty : Val) (cols : List Col)
    (rows : List Row) (ri : RecInfo) (isRoot : Bool) (defPos : Pos) : MM Unit := do
  -- the column to split on: the first one with a constructor pattern
  let mut j? : Option Nat := none
  for i in [0:cols.length] do
    if j?.isNone then
      if ← rows.anyM fun r => (match r.pats[i]? with | some p => isCtorPat p | none => pure false : M Bool) then
        j? := some i
  let j := j?.getD 0
  -- bind the columns before it as parameters
  let mut ctx := ctx
  let mut ty := ty
  let mut rows := rows
  let mut ri := ri
  let mut names := names
  for (col, i) in (cols.take j).zip (List.range j) do
    match ← force ty with
    | .pi x a env b =>
      let nm ← colName rows 0 (plainName x)
      let (c, xv) := ctx.bindVar nm a
      ri := ri.bind col.kind ctx.lvl
      rows := bindPats rows [(nm, a, xv)]
      ctx := c
      names := names ++ [if isImplName x then implName nm else nm]
      ty ← inst env b xv
    | .piI .. => errAt defPos s!"cannot match on an argument that follows an interval argument"
    | t => errAt defPos s!"too many patterns: {← ppVal ctx t} is not a function type"
    let _ := i
  let cols := cols.drop j
  let some col := cols.head? | errAt defPos "internal: no column to split"
  let restCols := cols.tail
  let (a, envB, motive) ← match ← force ty with
    | .pi _ a envB motive => pure (a, envB, motive)
    | t => errAt defPos s!"too many patterns: {← ppVal ctx t} is not a function type"
  let (d, dk, dps) ← match ← force a with
    | .data d dk dps => pure (d, dk, dps)
    | t => errAt defPos s!"cannot match on an argument of type {← ppVal ctx t}, which is not a data type"
  let info ← lookupData d
  if isRoot then modify fun s => { s with rootK := ctx.lvl }
  let fname := (← get).fname
  -- check the constructor patterns of this column
  for row in rows do
    if let some (c, sub, ppos) ← ctorPat? row.pats.head! then
      match info.ctors.find? (·.name == c) with
      | none => errAt ppos s!"{c} is not a constructor of {d}"
      | some ctor =>
        let n := ctor.tele.length + ctor.dims.length
        if sub.length != n then errAt ppos s!"constructor {c} expects {n} arguments, got {sub.length}"
  let mut branches : Array Branch := #[]
  let mut pathChecks : Array (Ctx × Tm × Val × CtorInfo × List Val × List Formula) := #[]
  for ctor in info.ctors do
    let nargs := ctor.tele.length
    let ndims := ctor.dims.length
    let nsub := nargs + ndims
    -- specialise the rows to this constructor
    let mut rowsC : Array (Row × Option String) := #[]
    for row in rows do
      let p := row.pats.head!
      match ← ctorPat? p with
      | some (c, sub, _) =>
        if c == ctor.name then
          rowsC := rowsC.push ({ row with pats := sub ++ row.pats.tail }, none)
      | none =>
        let y := match p with | .var y _ => y | _ => "_"
        rowsC := rowsC.push ({ row with pats := (List.replicate nsub (wild p.pos)) ++ row.pats.tail },
                             if y == "_" then none else some y)
    let st0 ← get
    let ids := List.range nsub |>.map (st0.nextId + ·)
    let filled := PT.con ctor.name (ids.map .hole)
    modify fun s => { s with nextId := s.nextId + nsub, templates := s.templates.map (PT.fill col.id filled) }
    if rowsC.isEmpty then
      let tpl := (← get).templates.map (PT.show true)
      errAt defPos s!"missing clause for {", ".intercalate tpl}"
    let rowsL := rowsC.toList.map (·.1)
    -- bind the constructor's arguments
    let mut bctx := ctx
    let mut env : Env := dps.reverse.map .v
    let mut argVals : Array Val := #[]
    let mut bound : Array (String × Val × Val) := #[]
    for ((fx, aTy), i) in ctor.tele.zip (List.range nargs) do
      let aty ← eval env (aTy.lift dk)
      let nm ← colName rowsL i fx
      let (c, xv) := bctx.bindVar nm aty
      bctx := c
      env := .v xv :: env
      argVals := argVals.push xv
      bound := bound.push (nm, aty, xv)
    let mut dims : Array Formula := #[]
    for (dx, i) in ctor.dims.zip (List.range ndims) do
      let nm ← colName rowsL (nargs + i) dx
      let (c, kAtom) ← bctx.bindDim nm
      bctx := c
      dims := dims.push (Formula.atom kAtom)
    let cval ← if ndims == 0 then pure (Val.con ctor.name argVals.toList)
      else mkPCon ctor.name argVals.toList dims.toList
    -- variable patterns in the split column are aliases of the constructor
    let rowsC2 := rowsC.toList.map fun (row, y?) => match y? with
      | some y => { row with aliases := row.aliases ++ [(y, a, cval)] }
      | none => row
    let bTy ← inst envB motive cval
    let isRec := fun i => isRoot && (ctor.recArgs[i]?.getD false)
    let argCols : List Col := (List.range nargs).map fun i =>
      { id := ids[i]!, kind := if isRec i then .recArg i else .plain }
    let ctorInSub ← rowsC2.anyM fun r => (r.pats.take nsub).anyM (fun p => (isCtorPat p : M Bool))
    let ctorInRest ← rowsC2.anyM fun r => (r.pats.drop nsub).anyM (fun p => (isCtorPat p : M Bool))
    let tbody ← if !ctorInSub && !ctorInRest then do
        -- a leaf: the constructor's arguments are variables
        let mut riB := ri
        for i in [0:nargs] do
          riB := riB.bind (argCols[i]!).kind (ctx.lvl + i)
        -- (only the first row reaches the leaf, and its interval variables are the bound ones)
        let rowsB := (bindPats rowsC2 bound.toList).map fun r => { r with pats := r.pats.drop ndims }
        compileLeaf bctx bTy restCols rowsB riB (!isRoot)
      else do
        if ndims > 0 then
          errAt defPos s!"clauses for the path constructor {ctor.name} cannot use nested patterns or match on further arguments"
        -- an auxiliary split over the constructor's arguments, the recursive calls on them, and
        -- the remaining columns
        let n := (← get).nAux + 1
        modify fun s => { s with nAux := n }
        let aux := s!"{fname}#{n}"
        let recPos := (List.range nargs).filter isRec
        let mut rctx := bctx
        for p in recPos do
          let (c, _) := rctx.bindVar "rec" (← inst envB motive argVals[p]!)
          rctx := c
        let auxTyTm ← piOverEntries rctx (nargs + recPos.length) bTy
        let auxTy ← eval ctx.env auxTyTm
        let recCols : List Col := recPos.map fun p => { id := 0, kind := .recFn p }
        let rowsA := rowsC2.map fun r =>
          { r with pats := r.pats.take nargs ++ recPos.map (fun _ => wild r.pos) ++ r.pats.drop nargs }
        compileSplit aux (ctx.entries.reverse.map (·.name)) ctx auxTy (argCols ++ recCols ++ restCols)
          rowsA ri false defPos
        -- `aux ctx args (f ps y_r)…`
        let k := (← get).rootK
        let recCalls := recPos.map fun p =>
          let ps := (List.range k).map fun q => SArg.tm (.var (bctx.lvl - 1 - q))
          let y := Tm.var (nargs - 1 - p)
          SArg.tm (.app (ps.foldl SArg.apply (.glob fname 0)) y)
        let args := ctxArgs ctx nargs ++ (List.range nargs).reverse.map (fun i => SArg.tm (.var i)) ++ recCalls
        pure (args.foldl SArg.apply (.glob aux 0))
    branches := branches.push { ctor := ctor.name, nArgs := nargs, nDims := ndims, body := tbody }
    if ndims > 0 then pathChecks := pathChecks.push (bctx, tbody, bTy, ctor, argVals.toList, dims.toList)
    modify fun s => { s with templates := st0.templates }
  -- add the split
  let body := names.foldr (fun x b => .lam x b) (.split name 0)
  if isRoot then
    let info ← lookupDef name
    addDef { info with body := some body, nParams := ctx.lvl, branches := branches.toList }
  else
    let tyTm ← piOverEntries ctx ctx.lvl ty
    addDef { name, ty := ← eval [] tyTm, tyTm, body := some body, value := none, nParams := ctx.lvl,
             branches := branches.toList }
  -- clauses for path constructors must agree with the clauses for their boundary
  for (bctx, tbody, expected, ctor, args, dims) in pathChecks do
    let benv := dims.reverse.map EnvE.d ++ args.reverse.map EnvE.v
    let bsys ← evalSys benv ctor.boundary
    for (α, bv) in bsys do
      let ctxα ← bctx.face α
      let lhs ← eval ctxα.env tbody
      let penv ← faceEnv ctx.env α
      let rhs ← splitApp name 0 penv bv
      if !(← convC ctxα (← faceV expected α) lhs rhs) then
        err bctx s!"clause for {ctor.name} does not agree with its boundary:\n  clause gives: {← ppVal ctxα lhs}\n  boundary:     {← ppVal ctxα rhs}{← ctxMsg ctxα}"

def checkSplit (name : String) (ps : List Binder) (ty : Raw) (clauses : List Clause') (pos : Pos) : M Unit := do
  let ctx0 : Ctx := { pos }
  ensureFresh ctx0 name
  let (ctx, tele) ← elabTele ctx0 ps
  if tele.any (·.2.isNone) then err ctx0 "pattern-matching definitions cannot have interval parameters"
  let (tty, _) ← inferType ctx ty
  checkMetas
  let tele ← zonkTele tele
  let tty ← zonk tty
  let vty ← eval ctx.env tty
  let fullTy := teleType tele tty
  -- while its clauses are checked, `name` is an opaque constant
  addDef { name, ty := ← eval [] fullTy, tyTm := fullTy, body := none, value := none, nParams := tele.length,
           branches := [] }
  let ncols := (clauses.head?.map (·.pats.length)).getD 1
  for cl in clauses do
    if cl.pats.length != ncols then
      err { ctx with pos := cl.pos } s!"this clause has {cl.pats.length} patterns, but the first clause has {ncols}"
  let cols : List Col := (List.range ncols).map fun i => { id := i }
  let rows := clauses.zip (List.range clauses.length) |>.map fun (cl, i) =>
    ({ idx := i, pats := cl.pats, body := cl.body, pos := cl.pos } : Row)
  if !clauses.isEmpty then
    if !(← rows.anyM fun r => r.pats.anyM (fun p => (isCtorPat p : M Bool))) then
      err ctx0 "a pattern-matching definition needs a constructor pattern; use := for a definition without matching"
  let st : MState := { fname := name, templates := cols.map (PT.hole ·.id), nextId := ncols,
                       used := Array.replicate clauses.length false }
  let ((), st) ← (compileSplit name (tele.map (·.1)) ctx vty cols rows {} true pos).run st
  for (cl, i) in clauses.zip (List.range clauses.length) do
    if !st.used[i]! then err { ctx with pos := cl.pos } "redundant clause: it is covered by the clauses before it"
  if (← get).selfcheck then
    for it in st.items do scTerm it.ctx it.tm it.ty it.label

end Kubus
