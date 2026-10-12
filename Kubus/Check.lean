import Kubus.Quote

/-! # Bidirectional elaboration of surface syntax into core terms -/

namespace Kubus

structure CEntry where
  name : String
  /-- `none` for interval variables -/
  ty : Option Val
  val : EnvE

structure Ctx where
  entries : List CEntry := []
  pos : Pos := ⟨0, 0⟩

namespace Ctx

def env (c : Ctx) : Env := c.entries.map (·.val)
def lvl (c : Ctx) : Nat := c.entries.length
def names (c : Ctx) : List String := c.entries.map (·.name)

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

end Ctx

def err {α} (ctx : Ctx) (msg : String) : M α :=
  throw s!"{ctx.pos.line}:{ctx.pos.col}: {msg}"

def ppVal (ctx : Ctx) (v : Val) : M String := do
  return pp ctx.names 0 (← quote ctx.qctx v)

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

def stripLoc : Raw → Raw
  | .loc _ t => stripLoc t
  | t => t

/-- Collect an application spine `h a1 ... an`. -/
def unspine (t : Raw) : Raw × List Raw :=
  let rec go (t : Raw) (acc : List Raw) : Raw × List Raw :=
    match t with
    | .app f a => go f (a :: acc)
    | .loc _ (.app f a) => go f (a :: acc)
    | t => (t, acc)
  go t []

def headVar? (t : Raw) : Option String :=
  match stripLoc t with
  | .var x => some x
  | _ => none

/-- Head of a spine that may be a displaced global. -/
def headGlobal? (t : Raw) : Option (String × Nat) :=
  match stripLoc t with
  | .var x => some (x, 0)
  | .lift x k => some (x, k)
  | _ => none

def defType (info : DefInfo) (k : Nat) : M Val :=
  if k == 0 then pure info.ty else eval [] (info.tyTm.lift k)

def headPos (ctx : Ctx) : Raw → Pos
  | .loc p _ => p
  | _ => ctx.pos

/-- Universe level of a type. -/
partial def levelOf (l : Nat) (v : Val) : M Nat := do
  match v with
  | .univ n => pure (n + 1)
  | .pi _ a env b | .sigma _ a env b =>
    return max (← levelOf l a) (← levelOf (l + 1) (← inst env b (.var l a)))
  | .piI line | .pathP line _ _ => do
    let k ← freshAtom
    levelOf l (← papp line (atomF k))
  | .data d k _ => return (← lookupData d).level + k
  | .glueTy b _ | .compU b _ => levelOf l b
  | _ =>
    match ← inferNe v with
    | some (.univ n) => pure n
    | _ => pure 0

mutual

partial def check (ctx : Ctx) (t : Raw) (ty : Val) : M Tm := do
  match t with
  | .loc p t => check { ctx with pos := p } t ty
  | .lam x tyR b =>
    if let some tyR := tyR then
      let isI := match stripLoc tyR with | .intervalTy => true | _ => false
      match ty, isI with
      | .pi _ a _ _, false =>
        let (ta, _) ← inferType ctx tyR
        if !(← convTy ctx.lvl (← eval ctx.env ta) a) then
          err ctx s!"lambda binder type does not match the expected domain {← ppVal ctx a}"
      | .pi .., true => err ctx "lambda binder of type I, but a function was expected"
      | _, false => err ctx s!"a lambda over a type cannot have type {← ppVal ctx ty}"
      | _, true => pure ()
    match ty with
    | .pi _ a env bTy =>
      let (ctx', xv) := ctx.bindVar x a
      return .lam x (← check ctx' b (← inst env bTy xv))
    | .piI line =>
      let (ctx', k) ← ctx.bindDim x
      return .plam x (← check ctx' b (← papp line (atomF k)))
    | .pathP line a0 a1 =>
      let (ctx', k) ← ctx.bindDim x
      let tb ← check ctx' b (← papp line (atomF k))
      let v ← eval ctx'.env tb
      for (d, e) in [(Dir.zero, a0), (Dir.one, a1)] do
        let vd ← act k (Formula.ofDir d) v
        let tyd ← papp line (Formula.ofDir d)
        if !(← conv ctx.lvl tyd vd e) then
          let ds := if d == .zero then "0" else "1"
          err ctx s!"path boundary mismatch at {x} = {ds}:\n  expected {← ppVal ctx e}\n  but got  {← ppVal ctx vd}"
      return .plam x tb
    | _ => err ctx s!"a lambda cannot have type {← ppVal ctx ty}"
  | .pair a b =>
    match ty with
    | .sigma _ aTy env bTy =>
      let ta ← check ctx a aTy
      let va ← eval ctx.env ta
      return .pair ta (← check ctx b (← inst env bTy va))
    | _ => err ctx s!"a pair cannot have type {← ppVal ctx ty}"
  | .glue sys a =>
    match ty with
    | .glueTy base esys =>
      let ta ← check ctx a base
      let va ← eval ctx.env ta
      let (tsys, elems) ← checkSys ctx none sys fun _ α _ => faceV ty α
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
          if !(← conv ctxα.lvl (← faceV base α) fv (← faceV va α)) then
            err ctx "glue: the system does not agree with the base element"
        | none => err ctx "glue: internal face error"
      return .glue tsys ta
    | _ => err ctx s!"glue cannot have type {← ppVal ctx ty}"
  | .letE x tyR t b =>
    let (tt, a) ← inferLet ctx tyR t
    let vt ← eval ctx.env tt
    return .letE x tt (← check (ctx.define x a vt) b ty)
  | .hole =>
    err ctx s!"hole\ngoal: {← ppVal ctx ty}\ncontext:\n{← ppCtx ctx}"
  | _ =>
    let (h, args) := unspine t
    match headVar? h, ty with
    | some c, .data d k ps =>
      if (ctx.lookup c).isNone && (← getGlobals).ctors.contains c then
        let (tm, _) ← elabCon { ctx with pos := headPos ctx h } c args (some (d, k, ps))
        return tm
      else checkInfer ctx t ty
    | _, _ => checkInfer ctx t ty

partial def checkInfer (ctx : Ctx) (t : Raw) (ty : Val) : M Tm := do
  let (tm, ty') ← infer ctx t
  if !(← subtype ctx.lvl ty' ty) then
    err ctx s!"type mismatch\n  expected: {← ppVal ctx ty}\n  but got:  {← ppVal ctx ty'}"
  return tm

partial def inferLet (ctx : Ctx) (tyR : Option Raw) (t : Raw) : M (Tm × Val) := do
  match tyR with
  | some tyR =>
    let (ta, _) ← inferType ctx tyR
    let a ← eval ctx.env ta
    return (← check ctx t a, a)
  | none => infer ctx t

partial def inferType (ctx : Ctx) (t : Raw) : M (Tm × Nat) := do
  let (tm, ty) ← infer ctx t
  match ty with
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
    let mut tm? : Option Tm := none
    for α in rv.faces do
      let (ctxα, k?) ← restrict ctx α binder
      let tm ← check ctxα t (← elemTy ctxα α k?)
      if tm?.isNone then tm? := some tm
      elems := elems.push (α, tm)
    if let some tm := tm? then out := out.push (r, tm)
  for h : a in [0:elems.size] do
    for h' : b in [a + 1:elems.size] do
      let (α, ta) := elems[a]
      let (β, tb) := elems[b]
      if let some γ := Face.meet? α β then
        let (ctxγ, k?) ← restrict ctx γ binder
        let ety ← elemTy ctxγ γ k?
        if !(← conv ctxγ.lvl ety (← eval ctxγ.env ta) (← eval ctxγ.env tb)) then
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
    if !(← conv ctxα.lvl (← faceV a0 α) v (← faceV u0 α)) then
      err ctx s!"the system does not agree with the base:\n  base:   {← ppVal ctxα (← faceV u0 α)}\n  system: {← ppVal ctxα v}"

partial def elabCon (ctx : Ctx) (c : String) (args : List Raw) (expected : Option (String × Nat × List Val)) :
    M (Tm × Val) := do
  let ctor ← lookupCtor c
  let info ← lookupData ctor.data
  let (k, ps) ← match expected with
    | some (d, k, ps) =>
      if d != ctor.data then err ctx s!"constructor {c} does not belong to {d}"
      pure (k, ps)
    | none =>
      if !info.params.isEmpty then err ctx s!"cannot infer the parameters of {c}; add a type annotation"
      pure (0, [])
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
  return (.con c targs.toList tdims, .data ctor.data k ps)

partial def infer (ctx : Ctx) (t : Raw) : M (Tm × Val) := do
  match t with
  | .loc p t => infer { ctx with pos := p } t
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
    if let some info := g.defs[x]? then return (.glob x k, ← defType info k)
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
    let (ctx', _) := ctx.bindVar x (← eval ctx.env ta)
    let (tb, lb) ← inferType ctx' b
    return (.pi x ta tb, .univ (max la lb))
  | .sigma x a b =>
    let (ta, la) ← inferType ctx a
    let (ctx', _) := ctx.bindVar x (← eval ctx.env ta)
    let (tb, lb) ← inferType ctx' b
    return (.sigma x ta tb, .univ (max la lb))
  | .app .. =>
    let (h, args) := unspine t
    let g ← getGlobals
    match headGlobal? h with
    | some (c, k) =>
      if (ctx.lookup c).isNone && g.ctors.contains c && k == 0 then
        return ← elabCon { ctx with pos := headPos ctx h } c args none
      if (ctx.lookup c).isNone && g.datas.contains c then
        return ← elabData { ctx with pos := headPos ctx h } c k args
      inferApp ctx h args
    | none => inferApp ctx h args
  | .fst p =>
    let (tp, ty) ← infer ctx p
    match ty with
    | .sigma _ a _ _ => pure (.fst tp, a)
    | _ => err ctx s!"projection from a non-Σ type {← ppVal ctx ty}"
  | .snd p =>
    let (tp, ty) ← infer ctx p
    match ty with
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
      match tyP with
      | .pathP lineU _ _ =>
        match ← papp lineU Formula.zero with
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
    let (tu, ty) ← infer ctx u
    match ty with
    | .glueTy b sys =>
      let q := ctx.qctx
      return (.unglue tu (← quote q b) (← quoteSys q sys), b)
    | _ => err ctx s!"unglue expects an element of a Glue type, got {← ppVal ctx ty}"
  | .ann t a =>
    let (ta, _) ← inferType ctx a
    let av ← eval ctx.env ta
    return (← check ctx t av, av)
  | .letE x tyR t b =>
    let (tt, a) ← inferLet ctx tyR t
    let vt ← eval ctx.env tt
    let (tb, bTy) ← infer (ctx.define x a vt) b
    return (.letE x tt tb, bTy)
  | .pair a b =>
    let (ta, aTy) ← infer ctx a
    let (tb, bTy) ← infer ctx b
    return (.pair ta tb, .sigma "_" aTy [.v bTy] (.var 1))
  | .hole => err ctx "cannot infer the type of a hole; add a type annotation"
  | .lam x (some tyR) b =>
    if let .intervalTy := stripLoc tyR then
      let (ctx', k) ← ctx.bindDim x
      let (tb, bTy) ← infer ctx' b
      return (.plam x tb, .piI (.plam k bTy))
    let (ta, _) ← inferType ctx tyR
    let a ← eval ctx.env ta
    let (ctx', _) := ctx.bindVar x a
    let (tb, bTy) ← infer ctx' b
    return (.lam x tb, .pi x a ctx.env (← quote ctx'.qctx bTy))
  | .lam _ none _ => err ctx "cannot infer the type of a lambda; annotate the binder"
  | .glue .. => err ctx "cannot infer the type of glue; add a type annotation"
  | .izero | .ione | .ineg _ | .iand .. | .ior .. | .ieq .. =>
    err ctx "an interval expression cannot be used as a term"

partial def inferApp (ctx : Ctx) (h : Raw) (args : List Raw) : M (Tm × Val) := do
  let (tf, tyf) ← infer ctx h
  let mut tf := tf
  let mut tyf := tyf
  for arg in args do
    match tyf with
    | .pi _ a env b =>
      let ta ← check ctx arg a
      tyf ← inst env b (← eval ctx.env ta)
      tf := .app tf ta
    | .pathP line _ _ | .piI line =>
      let r ← elabI ctx arg
      tyf ← papp line (← evalI ctx.env r)
      tf := .papp tf r
    | _ => err ctx s!"too many arguments: a term of type {← ppVal ctx tyf} is not a function"
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
