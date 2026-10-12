import Kubus.Eval

/-! # Type-directed conversion checking -/

namespace Kubus

/-- `Σ (T : U l), Equiv T A` -/
def equivPairTy (l : Nat) (a : Val) : M Val := eval [.v a] (equivPairTm l)

mutual

partial def conv (l : Nat) (ty u v : Val) : M Bool := do
  match ty with
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
  match a, b with
  | .univ m, .univ n => pure (m ≤ n)
  | .pi _ a1 e1 b1, .pi _ a2 e2 b2 =>
    if !(← convTy l a2 a1) then return false
    let x := Val.var l a2
    subtype (l + 1) (← inst e1 b1 x) (← inst e2 b2 x)
  | _, _ => convTy l a b

end Kubus
