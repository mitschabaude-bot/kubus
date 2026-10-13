import Kubus.Conv

/-! # Bidirectional elaboration of surface syntax into core terms -/

namespace Kubus

namespace Ctx

def env (c : Ctx) : Env := c.entries.map (·.val)
def lvl (c : Ctx) : Nat := c.entries.length
def names (c : Ctx) : List String := c.entries.map (·.name)

/-- Bind a term variable. User-written implicit binders `{x}` are bound as `x`; binders inserted
by the elaborator keep their braces and cannot be referred to. -/
def bindVar (c : Ctx) (x : String) (a : Val) : Ctx × Val :=
  let v := Val.var c.lvl a
  ({ c with entries := ⟨x, some a, .v v⟩ :: c.entries }, v)

def bindDim (c : Ctx) (i : String) : M (Ctx × Atom) := do
  let k ← freshAtom
  return ({ c with entries := ⟨i, none, .d (Formula.atom k)⟩ :: c.entries }, k)

def define (c : Ctx) (x : String) (a v : Val) : Ctx :=
  { c with entries := ⟨x, some a, .v v⟩ :: c.entries }

def face (c : Ctx) (α : Face) : M Ctx := do
  let es ← c.entries.mapM fun e => do
    let ty ← e.ty.mapM (faceV · α)
    let val ← match e.val with
      | .v v => EnvE.v <$> faceV v α
      | .d r => pure (EnvE.d (α.applyF r))
    return { e with ty, val }
  return { c with entries := es }

def lookup (c : Ctx) (x : String) : Option (Nat × CEntry) :=
  let rec go (i : Nat) : List CEntry → Option (Nat × CEntry)
    | [] => none
    | e :: es => if e.name == x then some (i, e) else go (i + 1) es
  go 0 c.entries

def qctx (c : Ctx) : QCtx :=
  { es := c.entries.map fun e => match e.val with
      | .v (.var l _) => .tv l
      | .d r => match r.dnf with
        | [[l]] => if l.pos then .dim l.atom else .other
        | _ => .other
      | _ => .other
    next := c.lvl }

/-- Read-back context that keeps definitions folded. -/
def fqctx (c : Ctx) : QCtx := { c.qctx with fold := true }

end Ctx

def err {α} (ctx : Ctx) (msg : String) : M α := do
  let p := ctx.pos
  -- in editor mode, errors carry the end of the source range
  if (← get).lsp && p.eline > 0 then throw s!"{p.line}:{p.col}-{p.eline}:{p.ecol}: {msg}"
  throw s!"{p.line}:{p.col}: {msg}"

/-- Record the type of a source range (editor mode). -/
def recordHover (ctx : Ctx) (p : Pos) (ty : Val) : M Unit :=
  modify fun s => if s.lsp && p.eline > 0 then { s with pendingHovers := s.pendingHovers.push (p, ctx, ty) } else s

/-- Which binders of the type of each global are implicit, for printing. -/
def implMasks : M (String → List Bool) := do
  let g ← getGlobals
  return fun f => match g.defs[f]? with
    | some info => mask info.tyTm
    | none => []
where
  mask : Tm → List Bool
    | .pi x _ b => isImplName x :: mask b
    | .piI _ b => false :: mask b
    | _ => []

def ppI' : M PPI := do
  let ms := (← get).metas
  return { mask := ← implMasks, metaStr := fun m => "?" ++ ((ms[m]?.map (·.short)).getD s!"m{m}") }

def ppTm (ctx : Ctx) (t : Tm) : M String := do
  return pp ctx.names 0 t { (← ppI') with showImplicit := false }

/-- Print a value, with definitions folded. -/
def ppVal (ctx : Ctx) (v : Val) : M String := do
  ppTm ctx (← quote ctx.fqctx v)

/-- Undo metavariable solutions made by a failed conversion check. -/
def withRollback (x : M Bool) : M Bool := do
  let saved := (← get).metas
  let r ← x
  if !r then modify fun s => { s with metas := saved }
  return r

/-- A fresh metavariable of type `ty` in `ctx`: returns the core term (the metavariable applied
to the variables of the context) and its value. -/
def freshMeta (ctx : Ctx) (ty : Val) (desc : String) (short : String := "_") : M (Tm × Val) := do
  let m := (← get).metas.size
  let mut tyTm ← quote ctx.fqctx ty
  let mut rest := ctx.entries
  while true do
    match rest with
    | e :: es =>
      let sub : Ctx := { ctx with entries := es }
      tyTm ← match e.ty with
        | some a => do pure (Tm.pi e.name (← quote sub.fqctx a) tyTm)
        | none => pure (Tm.piI e.name tyTm)
      rest := es
    | [] => break
  let closedTy ← eval [] tyTm
  modify fun s => { s with metas := s.metas.push { ty := closedTy, ctx, ctxTy := ty, desc, short } }
  let n := ctx.entries.length
  let mut tm : Tm := .glob (metaName m) 0
  for idx in (List.range n).reverse do
    tm := match ctx.entries[idx]? with
      | some { ty := some _, .. } => .app tm (.var idx)
      | _ => .papp tm (.var idx)
  return (tm, ← eval ctx.env tm)

/-- Apply a closed metavariable solution `λ xs. b` to a spine, substituting. -/
def applySol (sol : Tm) (args : Array SArg) : Tm :=
  let rec go (b : Tm) (i : Nat) (acc : Array SArg) (fuel : Nat) : Tm :=
    match fuel, b, args[i]? with
    | fuel + 1, .lam _ b, some (.tm a) => go b (i + 1) (acc.push (.tm a)) fuel
    | fuel + 1, .plam _ b, some (.dim r) => go b (i + 1) (acc.push (.dim r)) fuel
    | _, _, _ => (args.extract i args.size).foldl SArg.apply (b.substArgs acc)
  go sol 0 #[] (args.size + 1)

/-- Replace solved metavariables by their solutions. -/
partial def zonk (t : Tm) : M Tm := do
  let (h, args) := t.sargs
  if let .glob n _ := h then
    if let some m := metaId? n then
      if let some sol := (← get).metas[m]?.bind (·.sol) then
        let args ← args.mapM fun
          | .tm a => SArg.tm <$> zonk a
          | .dim r => pure (SArg.dim r)
        return ← zonk (applySol sol args)
  t.mapChildrenM fun _ => zonk

/-- Conversion; in self-check mode also checks that it is symmetric. -/
def convC (ctx : Ctx) (ty u v : Val) : M Bool := do
  let r ← withRollback (conv ctx.lvl ty u v)
  if (← get).selfcheck then
    let r' ← try conv ctx.lvl ty v u catch e => do
      recordViolation s!"{ctx.pos.line}:{ctx.pos.col}: [conv-symmetry] conv v u raised: {e}"; pure r
    if r != r' then
      recordViolation s!"{ctx.pos.line}:{ctx.pos.col}: [conv-symmetry] conv u v = {r} but conv v u = {r'}\n  u = {← ppVal ctx u}\n  v = {← ppVal ctx v}\n  at type {← ppVal ctx ty}"
  return r

def convTyC (ctx : Ctx) (a b : Val) : M Bool := do
  let r ← withRollback (convTy ctx.lvl a b)
  if (← get).selfcheck then
    let r' ← try convTy ctx.lvl b a catch e => do
      recordViolation s!"{ctx.pos.line}:{ctx.pos.col}: [conv-symmetry] convTy b a raised: {e}"; pure r
    if r != r' then
      recordViolation s!"{ctx.pos.line}:{ctx.pos.col}: [conv-symmetry] convTy a b = {r} but convTy b a = {r'}\n  a = {← ppVal ctx a}\n  b = {← ppVal ctx b}"
  return r

def ppCtx (ctx : Ctx) : M String := do
  let mut lines : Array String := #[]
  let mut rest := ctx.entries
  while !rest.isEmpty do
    match rest with
    | e :: es =>
      let sub : Ctx := { ctx with entries := es }
      match e.ty with
      | some a => lines := lines.push s!"  {e.name} : {← ppVal sub a}"
      | none => lines := lines.push s!"  {e.name} : I"
      rest := es
    | [] => pure ()
  return "\n".intercalate lines.reverse.toList

/-- The context, for error messages (empty if there are no variables). -/
def ctxMsg (ctx : Ctx) : M String := do
  if ctx.entries.isEmpty then return ""
  return s!"\ncontext:\n{← ppCtx ctx}"

/-- Fail on the first unsolved metavariable. -/
def checkMetas : M Unit := do
  for mi in (← get).metas do
    if mi.sol.isNone && !mi.hole then
      err mi.ctx s!"could not infer {mi.desc}\n  of type {← ppVal mi.ctx mi.ctxTy}{← ctxMsg mi.ctx}"

/-- The first difference between two terms of the same shape, descending through
applications, path types, data types, constructors and pairs (`none` if the terms are equal
or differ at the top). -/
partial def tmDiff (a b : Tm) : Option (Tm × Tm) :=
  go a b |>.bind fun (x, y) => if x == a && y == b then none else some (x, y)
where
  go (a b : Tm) : Option (Tm × Tm) :=
    if a == b then none else
    match a, b with
    | .app f x, .app g y => if f == g then go x y else if x == y then go f g else some (a, b)
    | .papp f r, .papp g s => if r == s then go f g else some (a, b)
    | .pathP l u v, .pathP l' u' v' =>
      if l == l' && u == u' then go v v'
      else if l == l' && v == v' then go u u'
      else if u == u' && v == v' then go l l'
      else some (a, b)
    | .pair x y, .pair x' y' => if x == x' then go y y' else if y == y' then go x x' else some (a, b)
    | .data d _ ps, .data d' _ ps' | .con d ps _, .con d' ps' _ =>
      if d != d' || ps.length != ps'.length then some (a, b) else
      match (ps.zip ps').filter (fun (x, y) => !(x == y)) with
      | [(x, y)] => go x y
      | _ => some (a, b)
    | _, _ => some (a, b)

def stripLoc : Raw → Raw
  | .loc _ t => stripLoc t
  | t => t

/-- An argument in an application spine: explicit, or `{a}` / `{x := a}`. -/
inductive SpArg
  | expl (a : Raw)
  | impl (x : Option String) (a : Raw)
  deriving Inhabited

/-- Collect an application spine `h a1 ... an`. -/
def unspine (t : Raw) : Raw × List SpArg :=
  let rec go (t : Raw) (acc : List SpArg) : Raw × List SpArg :=
    match t with
    | .app f a | .loc _ (.app f a) => go f (.expl a :: acc)
    | .iapp f x a | .loc _ (.iapp f x a) => go f (.impl x a :: acc)
    | t => (t, acc)
  go t []

/-- The explicit arguments of a spine (for constructors and data types, which have no
implicit arguments). -/
def explArgs (ctx : Ctx) (args : List SpArg) : M (List Raw) :=
  args.mapM fun
    | .expl a => pure a
    | .impl .. => throw s!"{ctx.pos.line}:{ctx.pos.col}: constructors and data types take no implicit arguments"

def headVar? (t : Raw) : Option String :=
  match stripLoc t with
  | .var x => some x
  | _ => none

/-- Head of a spine that may be a displaced global. -/
def headGlobal? (t : Raw) : Option (String × Nat) :=
  match stripLoc t with
  | .var x | .explicit x => some (x, 0)
  | .lift x k => some (x, k)
  | _ => none

def isExplicitHead (t : Raw) : Bool :=
  match stripLoc (unspine t).1 with
  | .explicit _ => true
  | _ => false

def isImplLam (t : Raw) : Bool :=
  match stripLoc t with
  | .lam x .. => isImplName x
  | _ => false

/-- Description of the head of an application, for messages about its implicit arguments. -/
def headDesc (t : Raw) : String :=
  match headGlobal? t with
  | some (x, _) => s!" of {x}"
  | none => ""

def defType (info : DefInfo) (k : Nat) : M Val :=
  if k == 0 then pure info.ty else eval [] (info.tyTm.lift k)

def headPos (ctx : Ctx) : Raw → Pos
  | .loc p _ => p
  | _ => ctx.pos

mutual

partial def check (ctx : Ctx) (t : Raw) (ty : Val) : M Tm := do
  if let .loc p t := t then
    let ctx' := { ctx with pos := p }
    let tm ← check ctx' t ty
    recordHover ctx' p ty
    return tm
  -- the expected type as given: inference compares against it before unfolding globals
  let ty0 := ty
  let ty ← force ty
  -- against an implicit Π-type, insert an implicit lambda
  if let .pi x a env bTy := ty then
    if isImplName x && !isImplLam t then
      let (ctx', xv) := ctx.bindVar x a
      return .ann (.lam x (← check ctx' t (← inst env bTy xv))) (← quote ctx.qctx ty)
  match t with
  | .var "_" => return (← freshMeta ctx ty "the hole _").1
  | .lam x tyR b =>
    if isImplName x then
      match ty with
      | .pi y .. => if !isImplName y then err ctx s!"implicit lambda, but the expected type is the explicit function type {← ppVal ctx ty}"
      | _ => pure ()
    if let some tyR := tyR then
      let isI := match stripLoc tyR with | .intervalTy => true | _ => false
      match ty, isI with
      | .pi _ a _ _, false =>
        let (ta, _) ← inferType ctx tyR
        if !(← convTyC ctx (← eval ctx.env ta) a) then
          err ctx s!"lambda binder type does not match the expected domain {← ppVal ctx a}"
      | .pi .., true => err ctx "lambda binder of type I, but a function was expected"
      | _, false => err ctx s!"a lambda over a type cannot have type {← ppVal ctx ty}"
      | _, true => pure ()
    match ty with
    | .pi _ a env bTy =>
      let (ctx', xv) := ctx.bindVar (plainName x) a
      -- the type, for the certified kernel's translation (core λs carry no domain)
      return .ann (.lam x (← check ctx' b (← inst env bTy xv))) (← quote ctx.qctx ty)
    | .piI line =>
      let (ctx', k) ← ctx.bindDim x
      let lk ← papp line (atomF k)
      let tb ← check ctx' b lk
      scPush ctx' tb lk "body of an interval lambda"
      return .plam x tb
    | .pathP line a0 a1 =>
      let (ctx', k) ← ctx.bindDim x
      let lk ← papp line (atomF k)
      let tb ← check ctx' b lk
      scPush ctx' tb lk "body of a path lambda"
      let v ← eval ctx'.env tb
      for (d, e) in [(Dir.zero, a0), (Dir.one, a1)] do
        let vd ← act k (Formula.ofDir d) v
        let tyd ← papp line (Formula.ofDir d)
        if !(← convC ctx tyd vd e) then
          let ds := if d == .zero then "0" else "1"
          err ctx s!"path boundary mismatch at {x} = {ds}:\n  expected {← ppVal ctx e}\n  but got  {← ppVal ctx vd}{← ctxMsg ctx}"
      return .plam x tb
    | _ => err ctx s!"a lambda cannot have type {← ppVal ctx ty}"
  | .pair a b =>
    match ty with
    | .sigma _ aTy env bTy =>
      let ta ← check ctx a aTy
      let va ← eval ctx.env ta
      return .pair ta (← check ctx b (← inst env bTy va))
    -- an unknown expected type (e.g. an unsolved implicit argument): infer the pair's type
    | _ =>
      let rec head : Val → Option String
        | .gvar n _ => some n
        | .app f _ | .papp f _ => head f
        | _ => none
      if ((head ty).bind metaId?).isSome then checkInfer ctx t ty0
      else err ctx s!"a pair cannot have type {← ppVal ctx ty}"
  | .glue sys a =>
    match ty with
    | .glueTy base esys =>
      let ta ← check ctx a base
      let va ← eval ctx.env ta
      let (tsys, elems) ← checkSys ctx none sys fun _ α _ => do
        match (← faceSys esys α).eps? with
        | some te => fstV te
        | none => faceV ty α
      -- the system must be defined exactly where the Glue type is
      for (α, _) in esys do
        if !(elems.any fun (β, _) => α.leq β) then
          err ctx "glue: the system does not cover the faces of the Glue type"
      for (β, _) in elems do
        if !(esys.any fun (α, _) => β.leq α) then
          err ctx "glue: the system is defined outside the faces of the Glue type"
      for (α, tα) in elems do
        let ctxα ← ctx.face α
        let vt ← eval ctxα.env tα
        match (← faceSys esys α).eps? with
        | some te =>
          let fv ← app (← fstV (← sndV te)) vt
          if !(← convC ctxα (← faceV base α) fv (← faceV va α)) then
            err ctx "glue: the system does not agree with the base element"
        | none => err ctx "glue: internal face error"
      return .glue tsys ta
    | _ =>
      -- Under a face where the Glue type has already reduced to `T` (system elements are
      -- checked under their faces), `glue [φ ↦ t] a` is `t`. The base type is not known
      -- any more, so `a` is only inferred.
      let total ← sys.anyM fun (key, _) => do return (← evalI ctx.env (← elabI ctx key)).isOne
      if !total then err ctx s!"glue cannot have type {← ppVal ctx ty}"
      let (tsys, _) ← checkSys ctx none sys fun _ α _ => faceV ty α
      let (ta, _) ← infer ctx a
      return .glue tsys ta
  | .letE x tyR t b =>
    let (tt, a) ← inferLet ctx tyR t
    let vt ← eval ctx.env tt
    return .letE x (.ann tt (← quote ctx.qctx a)) (← check (ctx.define x a vt) b ty)
  | .hole =>
    if !(← get).lsp then err ctx s!"hole\ngoal: {← ppVal ctx ty}\ncontext:\n{← ppCtx ctx}"
    -- editor mode: report the goal and continue
    let (tm, _) ← freshMeta ctx ty "a hole"
    modify fun s => { s with pendingGoals := s.pendingGoals.push (ctx.pos, ctx, ty),
                             metas := s.metas.modify (s.metas.size - 1) (fun mi => { mi with hole := true }) }
    return tm
  | _ =>
    let (h, args) := unspine t
    match headVar? h, ty with
    | some c, .data d k ps =>
      if (ctx.lookup c).isNone && (← getGlobals).ctors.contains c then
        let (tm, _) ← elabCon { ctx with pos := headPos ctx h } c (← explArgs ctx args) (some (d, k, ps))
        return tm
      else checkInfer ctx t ty0
    | _, _ => checkInfer ctx t ty0

partial def checkInfer (ctx : Ctx) (t : Raw) (ty : Val) : M Tm := do
  let (tm, ty') ← inferIns ctx t
  if !(← subtype ctx.lvl ty' ty) then
    let e ← quote ctx.fqctx ty
    let g ← quote ctx.fqctx ty'
    let diff ← match tmDiff e g with
      | some (a, b) => pure s!"\n  ({← ppTm ctx a} vs {← ppTm ctx b})"
      | none => pure ""
    err ctx s!"type mismatch\n  expected: {← ppTm ctx e}\n  but got:  {← ppTm ctx g}{diff}{← ctxMsg ctx}"
  return tm

/-- Infer, then insert metavariables for leading implicit arguments (unless the term is `@f …`
or an implicit lambda). -/
partial def inferIns (ctx : Ctx) (t : Raw) : M (Tm × Val) := do
  let (tm, ty) ← infer ctx t
  if isExplicitHead t || isImplLam t then return (tm, ty)
  insertImplicits ctx (headDesc (unspine t).1) tm ty none

/-- Apply `tm : ty` to fresh metavariables while `ty` is an implicit Π-type (up to the binder
named `stop`). -/
partial def insertImplicits (ctx : Ctx) (desc : String) (tm : Tm) (ty : Val) (stop : Option String) :
    M (Tm × Val) := do
  let mut tm := tm
  let mut ty := ty
  repeat
    match ← force ty with
    | .pi x a env b =>
      if !isImplName x || stop == some (plainName x) then break
      let (mt, mv) ← freshMeta ctx a s!"the implicit argument {plainName x}{desc}" (plainName x)
      tm := .app tm mt
      ty ← inst env b mv
    | _ => break
  return (tm, ty)

partial def inferLet (ctx : Ctx) (tyR : Option Raw) (t : Raw) : M (Tm × Val) := do
  match tyR with
  | some tyR =>
    let (ta, _) ← inferType ctx tyR
    let a ← eval ctx.env ta
    return (← check ctx t a, a)
  | none => infer ctx t

partial def inferType (ctx : Ctx) (t : Raw) : M (Tm × Nat) := do
  let (tm, ty) ← infer ctx t
  match ← force ty with
  | .univ l => pure (tm, l)
  | _ => err ctx s!"expected a type, but this has type {← ppVal ctx ty}"

partial def elabI (ctx : Ctx) (t : Raw) : M ITm := do
  match t with
  | .loc p t => elabI { ctx with pos := p } t
  | .izero => pure .zero
  | .ione => pure .one
  | .var x =>
    match ctx.lookup x with
    | some (i, { ty := none, .. }) => pure (.var i)
    | some _ => err ctx s!"{x} is not an interval variable"
    | none => err ctx s!"unknown interval variable {x}"
  | .ineg r => return .neg (← elabI ctx r)
  | .iand r s => return .and (← elabI ctx r) (← elabI ctx s)
  | .ior r s => return .or (← elabI ctx r) (← elabI ctx s)
  | .ieq r d => do let r' ← elabI ctx r; return if d then r' else .neg r'
  | _ => err ctx "expected an interval expression"

/-- Check a system. Elements optionally bind an interval variable. `elemTy` gets the
restricted context (with the bound variable) and the face. Returns the core system and
the elaborated element for each face. Checks that elements agree on overlaps. -/
partial def checkSys (ctx : Ctx) (binder : Option String) (sys : List (Raw × Raw))
    (elemTy : Ctx → Face → Option Atom → M Val) : M (List (ITm × Tm) × List (Face × Tm)) := do
  let mut out : Array (ITm × Tm) := #[]
  let mut elems : Array (Face × Tm) := #[]
  for (key, t) in sys do
    let r ← elabI ctx key
    let rv ← evalI ctx.env r
    let faces := rv.faces
    for α in faces do
      let (ctxα, k?) ← restrict ctx α binder
      let ety ← elemTy ctxα α k?
      let tm ← check ctxα t ety
      scPush ctxα tm ety "system element"
      elems := elems.push (α, tm)
      -- elaboration may depend on the face, so each face gets its own core term
      out := out.push (if faces.length == 1 then r else quoteFace ctx.qctx α, tm)
  for h : a in [0:elems.size] do
    for h' : b in [a + 1:elems.size] do
      let (α, ta) := elems[a]
      let (β, tb) := elems[b]
      if let some γ := Face.meet? α β then
        let (ctxγ, k?) ← restrict ctx γ binder
        let ety ← elemTy ctxγ γ k?
        if !(← convC ctxγ ety (← eval ctxγ.env ta) (← eval ctxγ.env tb)) then
          err ctx "system elements do not agree on their overlap"
  return (out.toList, elems.toList)

partial def restrict (ctx : Ctx) (α : Face) (binder : Option String) : M (Ctx × Option Atom) := do
  let ctxα ← ctx.face α
  match binder with
  | some i => do
    let (c, k) ← ctxα.bindDim i
    pure (c, some k)
  | none => pure (ctxα, none)

/-- Check that the system elements at `i = 0` agree with the base. -/
partial def checkBase (ctx : Ctx) (elems : List (Face × Tm)) (a0 u0 : Val) : M Unit := do
  for (α, tα) in elems do
    let ctxα ← ctx.face α
    let v ← eval (.d Formula.zero :: ctxα.env) tα
    if !(← convC ctxα (← faceV a0 α) v (← faceV u0 α)) then
      err ctx s!"the system does not agree with the base:\n  base:   {← ppVal ctxα (← faceV u0 α)}\n  system: {← ppVal ctxα v}{← ctxMsg ctxα}"

partial def elabCon (ctx : Ctx) (c : String) (args : List Raw) (expected : Option (String × Nat × List Val)) :
    M (Tm × Val) := do
  let ctor ← lookupCtor c
  let info ← lookupData ctor.data
  let (k, ps) ← match expected with
    | some (d, k, ps) =>
      if d != ctor.data then err ctx s!"constructor {c} does not belong to {d}"
      pure (k, ps)
    | none =>
      let mut env : Env := []
      let mut ps : Array Val := #[]
      for (x, pTy) in info.params do
        let (_, mv) ← freshMeta ctx (← eval env pTy) s!"the parameter {x} of {c}" x
        ps := ps.push mv
        env := .v mv :: env
      pure (0, ps.toList)
  let n := ctor.tele.length
  if args.length != n + ctor.dims.length then
    err ctx s!"constructor {c} expects {n + ctor.dims.length} arguments, got {args.length}"
  let mut env : Env := ps.reverse.map .v
  let mut targs : Array Tm := #[]
  for ((_, aTy), arg) in ctor.tele.zip (args.take n) do
    let a ← eval env (aTy.lift k)
    let ta ← check ctx arg a
    targs := targs.push ta
    env := .v (← eval ctx.env ta) :: env
  let tdims ← (args.drop n).mapM (elabI ctx)
  let ty : Val := .data ctor.data k ps
  -- the data type with its parameters, for the certified kernel's translation
  let tc : Tm := .con c targs.toList tdims
  let tc ← if ps.isEmpty then pure tc else pure (.ann tc (← quote ctx.qctx ty))
  return (tc, ty)

partial def infer (ctx : Ctx) (t : Raw) : M (Tm × Val) := do
  match t with
  | .loc p t =>
    let ctx' := { ctx with pos := p }
    let (tm, ty) ← infer ctx' t
    recordHover ctx' p ty
    return (tm, ty)
  | .var "_" => err ctx "cannot infer the type of the hole _; add a type annotation"
  | .var x =>
    match ctx.lookup x with
    | some (i, { ty := some a, .. }) => pure (.var i, a)
    | some _ => err ctx s!"{x} is an interval variable, not a term"
    | none =>
      let g ← getGlobals
      if let some info := g.defs[x]? then return (.glob x 0, info.ty)
      if g.ctors.contains x then return ← elabCon ctx x [] none
      if let some info := g.datas[x]? then
        if info.params.isEmpty then return (.data x 0 [], .univ info.level)
        err ctx s!"data type {x} expects {info.params.length} parameters"
      err ctx s!"unknown identifier {x}"
  | .lift x k =>
    if (ctx.lookup x).isSome then err ctx s!"only global definitions and data types can be displaced"
    let g ← getGlobals
    if let some info := g.defs[x]? then
      if info.body.isNone && k > 0 then err ctx s!"{x} cannot be displaced inside its own definition"
      return (.glob x k, ← defType info k)
    if let some info := g.datas[x]? then
      let k := if info.liftInvariant then 0 else k
      if info.params.isEmpty then return (.data x k [], .univ (info.level + k))
      err ctx s!"data type {x} expects {info.params.length} parameters"
    err ctx s!"unknown global {x}"
  | .univ l => pure (.univ l, .univ (l + 1))
  | .intervalTy => err ctx "the interval I is not a type; it may only appear in binders"
  | .pi x a b =>
    if let .intervalTy := stripLoc a then
      let (ctx', _) ← ctx.bindDim x
      let (tb, l) ← inferType ctx' b
      return (.piI x tb, .univ l)
    let (ta, la) ← inferType ctx a
    let (ctx', _) := ctx.bindVar (plainName x) (← eval ctx.env ta)
    let (tb, lb) ← inferType ctx' b
    return (.pi x ta tb, .univ (max la lb))
  | .sigma x a b =>
    let (ta, la) ← inferType ctx a
    let (ctx', _) := ctx.bindVar (plainName x) (← eval ctx.env ta)
    let (tb, lb) ← inferType ctx' b
    return (.sigma x ta tb, .univ (max la lb))
  | .app .. | .iapp .. =>
    let (h, args) := unspine t
    let g ← getGlobals
    match headGlobal? h, stripLoc h with
    | some (c, k), .var _ | some (c, k), .lift .. =>
      let hctx := { ctx with pos := headPos ctx h }
      if (ctx.lookup c).isNone && g.ctors.contains c && k == 0 then
        return ← elabCon hctx c (← explArgs hctx args) none
      if (ctx.lookup c).isNone && g.datas.contains c then
        return ← elabData hctx c k (← explArgs hctx args)
      inferApp ctx h args
    | _, _ => inferApp ctx h args
  | .explicit x => infer ctx (.var x)
  | .fst p =>
    let (tp, ty) ← inferIns ctx p
    match ← force ty with
    | .sigma _ a _ _ => pure (.fst tp, a)
    | _ => err ctx s!"projection from a non-Σ type {← ppVal ctx ty}"
  | .snd p =>
    let (tp, ty) ← inferIns ctx p
    match ← force ty with
    | .sigma _ _ env b => return (.snd tp, ← inst env b (← fstV (← eval ctx.env tp)))
    | _ => err ctx s!"projection from a non-Σ type {← ppVal ctx ty}"
  | .path a u v =>
    if let .hole := stripLoc a then
      let (tu, au) ← infer ctx u
      let tv ← check ctx v au
      let l ← levelOf ctx.lvl au
      let (ctx', k) ← ctx.bindDim "_"
      let _ := k
      let ta ← quote ctx'.qctx au
      return (.pathP (.plam "_" ta) tu tv, .univ l)
    let (ta, l) ← inferType ctx a
    let av ← eval ctx.env ta
    let tu ← check ctx u av
    let tv ← check ctx v av
    let (ctx', _) ← ctx.bindDim "_"
    let (ta', _) ← inferType ctx' a
    return (.pathP (.plam "_" ta') tu tv, .univ l)
  | .pathP p u v =>
    match stripLoc p with
    | .lam i _ body =>
      let (ctx', _) ← ctx.bindDim i
      let (tb, l) ← inferType ctx' body
      let line ← eval ctx.env (.plam i tb)
      let tu ← check ctx u (← papp line Formula.zero)
      let tv ← check ctx v (← papp line Formula.one)
      return (.pathP (.plam i tb) tu tv, .univ l)
    | _ =>
      let (tp, tyP) ← infer ctx p
      match ← force tyP with
      | .pathP lineU _ _ =>
        let k ← freshAtom
        match ← force (← papp lineU (atomF k)) with
        | .univ l =>
          let line ← eval ctx.env tp
          let tu ← check ctx u (← papp line Formula.zero)
          let tv ← check ctx v (← papp line Formula.one)
          return (.pathP tp tu tv, .univ l)
        | _ => err ctx "PathP expects a path of types"
      | _ => err ctx "PathP expects a path of types"
  | .comp i a sys u0 =>
    let (ctx', _) ← ctx.bindDim i
    let (ta, _) ← inferType ctx' a
    let a0 ← eval (.d Formula.zero :: ctx.env) ta
    let a1 ← eval (.d Formula.one :: ctx.env) ta
    let tu0 ← check ctx u0 a0
    let vu0 ← eval ctx.env tu0
    let (tsys, elems) ← checkSys ctx (some i) sys fun ctxα _ _ => eval ctxα.env ta
    checkBase ctx elems a0 vu0
    return (.comp i ta tsys tu0, a1)
  | .hcomp i a sys u0 =>
    let (ta, _) ← inferType ctx a
    let av ← eval ctx.env ta
    let tu0 ← check ctx u0 av
    let vu0 ← eval ctx.env tu0
    let (tsys, elems) ← checkSys ctx (some i) sys fun _ α _ => faceV av α
    checkBase ctx elems av vu0
    return (.hcomp i ta tsys tu0, av)
  | .transp i a φ u0 =>
    let (ctx', k) ← ctx.bindDim i
    let (ta, _) ← inferType ctx' a
    let tφ ← elabI ctx φ
    let fφ ← evalI ctx.env tφ
    let ak ← eval ctx'.env ta
    let a0 ← act k Formula.zero ak
    -- the line is constant where the cofibration holds
    for α in fφ.faces do
      if !(← convTyC ctx' (← faceV ak α) (← faceV a0 α)) then
        err ctx s!"transp: the line {← ppVal ctx' ak} is not constant where the cofibration holds"
    let tu0 ← check ctx u0 a0
    return (.transp i ta tφ tu0, ← act k Formula.one ak)
  | .hfill i a sys u0 =>
    let (ta, _) ← inferType ctx a
    let av ← eval ctx.env ta
    let tu0 ← check ctx u0 av
    let vu0 ← eval ctx.env tu0
    let (tsys, elems) ← checkSys ctx (some i) sys fun _ α _ => faceV av α
    checkBase ctx elems av vu0
    let c ← eval ctx.env (.hcomp i ta tsys tu0)
    let k ← freshAtom
    let line : Val := .plam k av
    return (.hfill i ta tsys tu0, .pathP line vu0 c)
  | .fill i a sys u0 =>
    let (ctx', _) ← ctx.bindDim i
    let (ta, _) ← inferType ctx' a
    let a0 ← eval (.d Formula.zero :: ctx.env) ta
    let tu0 ← check ctx u0 a0
    let vu0 ← eval ctx.env tu0
    let (tsys, elems) ← checkSys ctx (some i) sys fun ctxα _ _ => eval ctxα.env ta
    checkBase ctx elems a0 vu0
    let line ← eval ctx.env (.plam i ta)
    let c ← eval ctx.env (.comp i ta tsys tu0)
    return (.fill i ta tsys tu0, .pathP line vu0 c)
  | .glueTy a sys =>
    let (ta, l) ← inferType ctx a
    let av ← eval ctx.env ta
    let (tsys, _) ← checkSys ctx none sys fun _ α _ => do equivPairTy l (← faceV av α)
    return (.glueTy ta tsys, .univ l)
  | .unglue u =>
    let (tu, ty) ← match stripLoc u with
      | .ann t a => inferAnnGlue ctx t a
      | _ => infer ctx u
    match ← force ty with
    | .glueTy b sys =>
      let q := ctx.qctx
      return (.unglue tu (← quote q b) (← quoteSys q sys), b)
    | _ => err ctx s!"unglue expects an element of a Glue type, got {← ppVal ctx ty}"
  | .ann t a =>
    let (ta, _) ← inferType ctx a
    let av ← eval ctx.env ta
    -- the ascription is kept for the certified kernel's translation
    match stripLoc t, ta, av with
    | .glue .., .glueTy .., .glueTy .. => return (.ann (← check ctx t av) ta, av)
    | .glue .., .glueTy .., _ => return (.ann (← inferAnnGlue ctx t a).1 ta, av)
    | _, _, _ => return (.ann (← check ctx t av) ta, av)
  | .letE x tyR t b =>
    let (tt, a) ← inferLet ctx tyR t
    let vt ← eval ctx.env tt
    let (tb, bTy) ← infer (ctx.define x a vt) b
    return (.letE x (.ann tt (← quote ctx.qctx a)) tb, bTy)
  | .pair a b =>
    let (ta, aTy) ← infer ctx a
    let (tb, bTy) ← infer ctx b
    return (.pair ta tb, .sigma "_" aTy [.v bTy] (.var 1))
  | .hole => err ctx "cannot infer the type of a hole; add a type annotation"
  | .lam x (some tyR) b =>
    if let .intervalTy := stripLoc tyR then
      let (ctx', k) ← ctx.bindDim x
      let (tb, bTy) ← infer ctx' b
      scPush ctx' tb bTy "body of an interval lambda"
      return (.plam x tb, .piI (.plam k bTy))
    let (ta, _) ← inferType ctx tyR
    let a ← eval ctx.env ta
    let (ctx', _) := ctx.bindVar (plainName x) a
    let (tb, bTy) ← infer ctx' b
    let qb ← quote ctx'.qctx bTy
    return (.ann (.lam x tb) (.pi x ta qb), .pi x a ctx.env qb)
  | .lam _ none _ => err ctx "cannot infer the type of a lambda; annotate the binder"
  | .glue .. => err ctx "cannot infer the type of glue; add a type annotation"
  | .izero | .ione | .ineg _ | .iand .. | .ior .. | .ieq .. =>
    err ctx "an interval expression cannot be used as a term"

/-- `(t : Glue A [φ ↦ (T, e)])`, typed by the Glue type *before* it reduces: under a face
where `φ` holds the annotation evaluates to `T`, but `glue` and `unglue` still need `A` and
`e` (system elements are checked under their faces, so this arises from well-typed terms). -/
partial def inferAnnGlue (ctx : Ctx) (t a : Raw) : M (Tm × Val) := do
  let (ta, _) ← inferType ctx a
  let av ← eval ctx.env ta
  match ta with
  | .glueTy tA tsys =>
    let g ← match ← unfoldM av with
      | .glueTy .. => pure av
      | _ => pure (.glueTy (← eval ctx.env tA) (← evalSys ctx.env tsys))
    match stripLoc t with
    | .glue .. => return (← check ctx t g, g)
    | _ => return (← check ctx t av, g)
  | _ => return (← check ctx t av, av)

partial def inferApp (ctx : Ctx) (h : Raw) (args : List SpArg) : M (Tm × Val) := do
  let expl := match stripLoc h with | .explicit _ => true | _ => false
  let hctx := { ctx with pos := headPos ctx h }
  let desc := headDesc h
  let (tf, tyf) ← infer ctx h
  let mut tf := tf
  let mut tyf := tyf
  for arg in args do
    match arg with
    | .expl arg =>
      if !expl then (tf, tyf) ← insertImplicits hctx desc tf tyf none
      match ← force tyf with
      | .pi _ a env b =>
        let ta ← check ctx arg a
        tyf ← inst env b (← eval ctx.env ta)
        tf := .app tf ta
      | .pathP line _ _ | .piI line =>
        let r ← elabI ctx arg
        tyf ← papp line (← evalI ctx.env r)
        tf := .papp tf r
      | ty => err ctx s!"too many arguments: a term of type {← ppVal ctx ty} is not a function"
    | .impl x arg =>
      if expl then err hctx "with @, implicit arguments are given as ordinary arguments"
      if let some x := x then (tf, tyf) ← insertImplicits hctx desc tf tyf (some x)
      match ← force tyf, x with
      | .pi y a env b, _ =>
        if !isImplName y then
          match x with
          | some x => err ctx s!"no implicit argument named {x}"
          | none => err ctx s!"unexpected implicit argument: the function expects an explicit argument of type {← ppVal ctx a}"
        let ta ← check ctx arg a
        tyf ← inst env b (← eval ctx.env ta)
        tf := .app tf ta
      | _, some x => err ctx s!"no implicit argument named {x}"
      | ty, none => err ctx s!"unexpected implicit argument: a term of type {← ppVal ctx ty} has no implicit arguments"
  if !expl then (tf, tyf) ← insertImplicits hctx desc tf tyf none
  return (tf, tyf)

partial def elabData (ctx : Ctx) (d : String) (k : Nat) (args : List Raw) : M (Tm × Val) := do
  let info ← lookupData d
  let k := if info.liftInvariant then 0 else k
  if args.length != info.params.length then
    err ctx s!"data type {d} expects {info.params.length} parameters, got {args.length}"
  let mut env : Env := []
  let mut tps : Array Tm := #[]
  for ((_, pTy), arg) in info.params.zip args do
    let a ← eval env (pTy.lift k)
    let ta ← check ctx arg a
    tps := tps.push ta
    env := .v (← eval ctx.env ta) :: env
  return (.data d k tps.toList, .univ (info.level + k))

end

end Kubus
