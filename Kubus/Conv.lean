import Kubus.Quote

/-! # Type-directed conversion checking -/

namespace Kubus

/-- `Σ (T : U l), Equiv T A` -/
def equivPairTy (l : Nat) (a : Val) : M Val := eval [.v a] (equivPairTm l)

/-- Universe level of a type. -/
partial def levelOf (l : Nat) (v : Val) : M Nat := do
  match ← force v with
  | .univ n => pure (n + 1)
  | .pi _ a env b | .sigma _ a env b =>
    return max (← levelOf l a) (← levelOf (l + 1) (← inst env b (.var l a)))
  | .piI line | .pathP line _ _ => do
    let k ← freshAtom
    levelOf l (← papp line (atomF k))
  | .data d k _ => return (← lookupData d).level + k
  | .glueTy b _ | .compU b _ => levelOf l b
  | v =>
    match ← inferNe v with
    | some (.univ n) => pure n
    | _ => pure 0

/-! ## Unification

A value whose head is an unsolved metavariable `?m` applied to a spine is *flexible*. Comparing
it with a value `v` solves `?m := λ xs. v`, where the spine arguments that are distinct
variables are abstracted (pattern unification). Other spine arguments may not occur in the
solution. -/

/-- An unsolved metavariable and its spine (outermost argument first). -/
partial def flex? (v : Val) : M (Option (Nat × List EnvE)) := do
  if (← get).metas.isEmpty then return none
  let rec go (v : Val) (acc : List EnvE) : M (Option (Nat × List EnvE)) := do
    match v with
    | .gvar n _ =>
      match metaId? n with
      | some m => return if ((← get).metas[m]?.bind (·.sol)).isNone then some (m, acc) else none
      | none => return none
    | .app f a => go f (.v a :: acc)
    | .papp p r => go p (.d r :: acc)
    | _ => return none
  go v []

/-- Whether a quoted solution candidate mentions variables that are not in scope (quote marks
them as `?x` globals and interval indices ≥ 1000000) or the metavariable itself. -/
partial def Tm.badSolution (m : Nat) (t : Tm) : Bool :=
  let badI : ITm → Bool := fun r => go r
  match t with
  | .glob n _ => n.startsWith "?x" || n == metaName m
  | .papp t r => t.badSolution m || badI r
  | .con _ as ds => as.any (·.badSolution m) || ds.any badI
  | .comp _ a sys u0 | .hcomp _ a sys u0 | .fill _ a sys u0 =>
    a.badSolution m || u0.badSolution m || sys.any fun (r, t) => badI r || t.badSolution m
  | .glueTy a sys | .glue sys a | .compU a sys => a.badSolution m || sys.any fun (r, t) => badI r || t.badSolution m
  | .unglue u b sys | .unglueU u b sys =>
    u.badSolution m || b.badSolution m || sys.any fun (r, t) => badI r || t.badSolution m
  | .pi _ a b | .sigma _ a b | .app a b | .pair a b | .letE _ a b => a.badSolution m || b.badSolution m
  | .lam _ b | .piI _ b | .plam _ b | .fst b | .snd b => b.badSolution m
  | .pathP a u v => a.badSolution m || u.badSolution m || v.badSolution m
  | .data _ _ ps => ps.any (·.badSolution m)
  | _ => false
where
  go : ITm → Bool
    | .var i => i ≥ 1000000
    | .neg r => go r
    | .and r s | .or r s => go r || go s
    | _ => false

/-- The type of `?m sp`. -/
partial def spineType (ty : Val) (sp : List EnvE) : M Val := do
  let mut ty := ty
  for e in sp do
    match ← force ty, e with
    | .pi _ _ env b, .v a => ty ← inst env b a
    | .piI line, .d r => ty ← papp line r
    | _, _ => return ty
  return ty

/-- Try to solve `?m sp := v` at context level `l`. -/
partial def solveMeta (l : Nat) (m : Nat) (sp : List EnvE) (v : Val) : M Bool := do
  let es := sp.reverse.map fun
    | .v (.var lv _) => QE.tv lv
    | .d r => match r.dnf with
      | [[lit]] => if lit.pos then .dim lit.atom else .other
      | _ => .other
    | _ => .other
  let body ← quote { es, next := l } v
  if body.badSolution m then return false
  let some mi := (← get).metas[m]? | return false
  if let .univ n ← spineType mi.ty sp then
    if (← levelOf l v) > n then return false
  let tm := sp.foldr (fun e b => match e with | .v _ => .lam "x" b | .d _ => .plam "i" b) body
  let solV ← eval [] tm
  modify fun s => { s with metas := s.metas.modify m fun mi => { mi with sol := some tm, solV := some solV } }
  return true

/-- If one side is flexible, try to solve it with the other side. -/
partial def flexSolve (l : Nat) (u v : Val) : M (Option Bool) := do
  let fu ← flex? u
  let fv ← flex? v
  match fu, fv with
  | some (m, _), some (m', _) => if m == m' then return none
  | _, _ => pure ()
  if let some (m, sp) := fu then
    if ← solveMeta l m sp v then return some true
  if let some (m, sp) := fv then
    if ← solveMeta l m sp u then return some true
  return none

mutual

partial def conv (l : Nat) (ty u v : Val) : M Bool := do
  let u ← force u
  let v ← force v
  if let some r ← flexSolve l u v then return r
  match ← force ty with
  | .pi _ a env b =>
    let x := Val.var l a
    conv (l + 1) (← inst env b x) (← app u x) (← app v x)
  | .sigma _ a env b =>
    let u1 ← fstV u
    let v1 ← fstV v
    if !(← conv l a u1 v1) then return false
    conv l (← inst env b u1) (← sndV u) (← sndV v)
  | .pathP line _ _ | .piI line =>
    let k ← freshAtom
    conv l (← papp line (atomF k)) (← papp u (atomF k)) (← papp v (atomF k))
  | .univ _ => convTy l u v
  | .glueTy b sys =>
    if !(← conv l b (← unglueV u b sys) (← unglueV v b sys)) then return false
    sys.allM fun (α, te) => do conv l (← fstV te) (← faceV u α) (← faceV v α)
  | .compU b es =>
    if !(← conv l b (← unglueUV u b es) (← unglueUV v b es)) then return false
    es.allM fun (α, e) => do conv l (← papp e Formula.one) (← faceV u α) (← faceV v α)
  | .data d k ps => convData l d k ps u v
  | _ => convNeB l u v

partial def convNeB (l : Nat) (u v : Val) : M Bool := do
  if u.isNeutral && v.isNeutral then return (← convNe l u v).isSome
  return false

partial def convData (l : Nat) (d : String) (k : Nat) (ps : List Val) (u v : Val) : M Bool := do
  match u, v with
  | .con c as, .con c' bs =>
    if c != c' then return false
    let ctor ← lookupCtor c
    convTele l (ctor.tele.map fun (x, t) => (x, t.lift k)) (ps.reverse.map .v) as bs
  | .pcon c as ds, .pcon c' bs ds' =>
    if c != c' || ds != ds' then return false
    let ctor ← lookupCtor c
    convTele l (ctor.tele.map fun (x, t) => (x, t.lift k)) (ps.reverse.map .v) as bs
  | .hcompF ty u0 s, .hcompF _ u0' s' =>
    if !(← conv l ty u0 u0') then return false
    convSysWith (fun α x y => do
      let k ← freshAtom
      conv l (← faceV ty α) (← papp x (atomF k)) (← papp y (atomF k))) s s'
  | _, _ => let _ := d; convNeB l u v

/-- Compare argument lists along a telescope. -/
partial def convTele (l : Nat) (tele : List (String × Tm)) (env : Env) (as bs : List Val) : M Bool := do
  let mut env := env
  for ((_, ty), a, b) in tele.zip (as.zip bs) do
    let A ← eval env ty
    if !(← conv l A a b) then return false
    env := .v a :: env
  return as.length == bs.length

/-- Two systems are equal if each is defined wherever the other is, with equal elements. -/
partial def convSysWith (cmp : Face → Val → Val → M Bool) (s1 s2 : System Val) : M Bool := do
  for (α, x) in s1 do
    match (← faceSys s2 α).eps? with
    | some y => if !(← cmp α x y) then return false
    | none => return false
  for (α, y) in s2 do
    match (← faceSys s1 α).eps? with
    | some x => if !(← cmp α x y) then return false
    | none => return false
  return true

partial def convTy (l : Nat) (a b : Val) : M Bool := do
  let a ← force a
  let b ← force b
  if let some r ← flexSolve l a b then return r
  match a, b with
  | .univ m, .univ n => pure (m == n)
  | .pi _ a1 e1 b1, .pi _ a2 e2 b2 | .sigma _ a1 e1 b1, .sigma _ a2 e2 b2 =>
    if !(← convTy l a1 a2) then return false
    let x := Val.var l a1
    convTy (l + 1) (← inst e1 b1 x) (← inst e2 b2 x)
  | .piI l1, .piI l2 =>
    let k ← freshAtom
    convTy l (← papp l1 (atomF k)) (← papp l2 (atomF k))
  | .pathP l1 u1 v1, .pathP l2 u2 v2 =>
    let k ← freshAtom
    if !(← convTy l (← papp l1 (atomF k)) (← papp l2 (atomF k))) then return false
    if !(← conv l (← papp l1 Formula.zero) u1 u2) then return false
    conv l (← papp l1 Formula.one) v1 v2
  | .data d k ps, .data d' k' qs =>
    if d != d' || k != k' then return false
    let info ← lookupData d
    convTele l (info.params.map fun (x, t) => (x, t.lift k)) [] ps qs
  | .glueTy b1 s1, .glueTy b2 s2 =>
    if !(← convTy l b1 b2) then return false
    convSysWith (fun α x y => do conv l (← equivPairTy 0 (← faceV b1 α)) x y) s1 s2
  | .compU b1 s1, .compU b2 s2 =>
    if !(← convTy l b1 b2) then return false
    convSysWith (fun _ x y => do
      let k ← freshAtom
      convTy l (← papp x (atomF k)) (← papp y (atomF k))) s1 s2
  | _, _ => convNeB l a b

/-- Compare neutral values; returns their type if equal. -/
partial def convNe (l : Nat) (u v : Val) : M (Option Val) := do
  match u, v with
  | .var x ty, .var y _ => pure (if x == y then some ty else none)
  | .gvar x ty, .gvar y _ => pure (if x == y then some ty else none)
  | .app f a, .app g b =>
    match ← convNe l f g with
    | some (.pi _ dom env cod) =>
      if ← conv l dom a b then return some (← inst env cod a) else return none
    | _ => pure none
  | .fst p, .fst q =>
    match ← convNe l p q with
    | some (.sigma _ a _ _) => pure (some a)
    | _ => pure none
  | .snd p, .snd q =>
    match ← convNe l p q with
    | some (.sigma _ _ env b) => return some (← inst env b (← fstV p))
    | _ => pure none
  | .papp p r, .papp q s =>
    if r != s then return none
    match ← convNe l p q with
    | some (.pathP line _ _) | some (.piI line) => return some (← papp line r)
    | _ => pure none
  | .splitApp f k env a, .splitApp g k' env' b =>
    if f != g || k != k' then return none
    let info ← lookupDef f
    let ty0 ← if k == 0 then pure info.ty else eval [] (info.tyTm.lift k)
    let mut ty := ty0
    for (e, e') in env.reverse.zip env'.reverse do
      match ty, e, e' with
      | .pi _ dom envB cod, .v p, .v q =>
        if !(← conv l dom p q) then return none
        ty ← inst envB cod p
      | _, _, _ => return none
    match ty with
    | .pi _ dom envB cod =>
      if ← conv l dom a b then return some (← inst envB cod a) else return none
    | _ => pure none
  | .comp l1 u1 s1, .comp l2 u2 s2 =>
    let k ← freshAtom
    let a1 ← papp l1 (atomF k)
    if !(← convTy l a1 (← papp l2 (atomF k))) then return none
    if !(← conv l (← papp l1 Formula.zero) u1 u2) then return none
    let ok ← convSysWith (fun α x y => do
      let k ← freshAtom
      conv l (← faceV (← papp l1 (atomF k)) α) (← papp x (atomF k)) (← papp y (atomF k))) s1 s2
    if ok then return some (← papp l1 Formula.one) else return none
  | .unglue u b s, .unglue u' _ _ | .unglueU u b s, .unglueU u' _ _ =>
    let _ := s
    match ← convNe l u u' with
    | some _ => pure (some b)
    | none => pure none
  | _, _ => pure none

end

/-- Subtyping by cumulativity of universes. -/
partial def subtype (l : Nat) (a b : Val) : M Bool := do
  let a ← force a
  let b ← force b
  if let some r ← flexSolve l a b then return r
  match a, b with
  | .univ m, .univ n => pure (m ≤ n)
  | .pi _ a1 e1 b1, .pi _ a2 e2 b2 =>
    if !(← convTy l a2 a1) then return false
    let x := Val.var l a2
    subtype (l + 1) (← inst e1 b1 x) (← inst e2 b2 x)
  | _, _ => convTy l a b

end Kubus
