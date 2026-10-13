import Kubus.Match

/-! # Declarations: definitions, data types, termination and positivity checks -/

namespace Kubus

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

/-- Whether a type mentions universes, globals, or data types that are not lift-invariant
(other than `self`). -/
partial def Tm.liftInvariant (g : Globals) (self : String) (t : Tm) : Bool :=
  match t with
  | .univ _ | .glob .. | .split .. => false
  | .data d _ ps => (d == self || (g.datas[d]?.map (·.liftInvariant)).getD false) &&
      ps.all (·.liftInvariant g self)
  | _ => t.children.all fun (_, c) => c.liftInvariant g self

def isRecArg (d : String) : Tm → Bool
  | .data d' _ _ => d == d'
  | .pi _ _ b => isRecArg d b
  | _ => false

def checkDefn (name : String) (ps : List Binder) (ty body : Raw) (pos : Pos) : M Unit := do
  let ctx0 : Ctx := { pos }
  ensureFresh ctx0 name
  let (ctx, tele) ← elabTele ctx0 ps
  let (tty, tbody) ← match ty with
    | .hole => do
      let (tbody, vty) ← inferIns ctx body
      pure (← quote ctx.qctx vty, tbody)
    | _ => do
      let (tty, _) ← inferType ctx ty
      pure (tty, ← check ctx body (← eval ctx.env tty))
  checkMetas
  let tele ← zonkTele tele
  let tty ← zonk tty
  let tbody ← zonk tbody
  let fullTy := teleType tele tty
  addDef { name, ty := ← eval [] fullTy, tyTm := fullTy, body := some (teleLam tele tbody),
           value := none, nParams := 0, branches := [] }
  if (← get).selfcheck then scTerm ctx tbody (← eval ctx.env tty) s!"definition {name}"

def checkData (name : String) (ps : List Binder) (lvl : Nat) (ctors : List CtorDecl) (pos : Pos) : M Unit := do
  let ctx0 : Ctx := { pos }
  ensureFresh ctx0 name
  let (ctx, tele) ← elabTele ctx0 ps
  if tele.any (·.2.isNone) then err ctx0 "data types cannot have interval parameters"
  checkMetas
  let tele ← zonkTele tele
  let params := tele.map fun (x, a) => (x, a.get!)
  let np := params.length
  let g0 ← getGlobals
  let li0 := params.all fun (_, t) => t.liftInvariant g0 name
  -- Kan operations in the type during its own declaration must already use the right rules
  let isHIT := ctors.any fun cd => cd.args.any fun b => match stripLoc b.ty with | .intervalTy => true | _ => false
  let dinfo : DataInfo := { name, params, level := lvl, ctors := [], isHIT, firstOrder := false,
                            liftInvariant := li0 }
  modify fun s => { s with globals.datas := s.globals.datas.insert name dinfo }
  let mut allFo := params.isEmpty && !isHIT
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
        checkMetas
        let ta ← zonk ta
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
    checkMetas
    let tsys ← tsys.mapM fun (r, t) => return (r, ← zonk t)
    if !dims.isEmpty && np > 0 && !(tsys.all fun (_, t) => simpleBoundary np ctele.size dims.size t) then
      err cctx "the boundary of a path constructor of a parameterised type may only use the constructor's point arguments and other constructors"
    let info : CtorInfo := { name := cd.name, data := name, tele := ctele.toList, recArgs := recArgs.toList,
                             dims := dims.toList, boundary := tsys }
    let g ← getGlobals
    let fo := dims.isEmpty && ctele.all fun (_, t) => match t with
      | .data d' _ [] => d' == name || (g.datas[d']?.map (·.firstOrder)).getD false
      | _ => false
    let li := (ctele.toList.all fun (_, t) => t.liftInvariant g name) &&
      tsys.all fun (_, t) => t.liftInvariant g name
    let upd (d : DataInfo) : DataInfo :=
      { d with ctors := d.ctors ++ [info],
               liftInvariant := d.liftInvariant && li }
    modify fun s => { s with globals.ctors := s.globals.ctors.insert cd.name info,
                             globals.datas := s.globals.datas.modify name upd }
    allFo := allFo && fo
  let fin (d : DataInfo) : DataInfo := { d with firstOrder := allFo }
  modify fun s => { s with globals.datas := s.globals.datas.modify name fin }

/-- Process a declaration (other than imports); returns output to print. -/
def checkDecl' : Decl → M (Option String)
  | .defn n ps ty body pos => do checkDefn n ps ty body pos; pure none
  | .defSplit n ps ty cls pos => do checkSplit n ps ty cls pos; pure none
  | .data n ps l cs pos => do checkData n ps l cs pos; pure none
  | .eval t pos => do
    let ctx : Ctx := { pos }
    let (tm, ty) ← infer ctx t
    checkMetas
    let tm ← zonk tm
    let v ← eval [] tm
    let nf ← quote ctx.qctx v
    let tyNf ← quote ctx.qctx ty
    if (← get).selfcheck then scTerm ctx tm ty "#eval" (checkTy := true)
    pure (some s!"{← ppTm ctx nf}\n  : {← ppTm ctx tyNf}")
  | .check t pos => do
    let ctx : Ctx := { pos }
    let (tm, ty) ← infer ctx t
    checkMetas
    let tm ← zonk tm
    if (← get).selfcheck then scTerm ctx tm ty "#check" (checkTy := true)
    -- the elaborated term (without implicit arguments) and its type
    let tmS := pp [] 0 tm { (← ppI') with showImplicit := false }
    pure (some s!"{tmS} : {← ppVal ctx ty}")
  | .importFile .. => pure none

/-- Process a declaration, then self-check the terms recorded during elaboration. -/
def checkDecl (d : Decl) : M (Option String) := do
  modify fun s => { s with metas := #[] }
  let out ← checkDecl' d
  if (← get).selfcheck then scDrain
  return out

end Kubus
