import Kubus.Check
import Kubus.Parser

/-!
# Invariant self-checks (`kubus --selfcheck`)

Every definition body, pattern-matching clause, `#eval`/`#check` term, path/interval lambda
body and system element is checked against invariants that a correct evaluator and
conversion checker satisfy:

- `conv-refl`: the value is convertible to itself (and its type to itself);
- `roundtrip`: `eval (quote v)` is convertible to `v`, in both directions;
- `recheck`: the printed normal form parses and elaborates again at the same type, to a value
  convertible to `v` (for `#eval`/`#check`, the printed type re-elaborates to the same type);
- `stability`: for every interval variable `i` of the context and every substitution
  `σ ∈ {0, 1, ~i, i ∧ j, i ∨ j, k}` (`j` fresh, `k` another variable of the context),
  `(eval ρ t)σ` is convertible to `eval (ρσ) t` at type `Aσ`;
- `conv-symmetry` (in the elaborator): every conversion check also holds the other way round.

Each check gets its own evaluation budget; checks that run out of budget are skipped and
counted. Violations are recorded in `St.violations`.
-/

namespace Kubus

/-- Whether a core term has surface syntax, so that its printed form can be re-elaborated. -/
partial def Tm.hasSurface : Tm → Bool
  | .split .. => false
  | .var _ | .glob .. | .univ _ => true
  | .pi _ a b | .sigma _ a b | .app a b | .pair a b | .letE _ a b => a.hasSurface && b.hasSurface
  | .lam _ b | .piI _ b | .plam _ b | .fst b | .snd b | .papp b _ => b.hasSurface
  | .pathP a u v => a.hasSurface && u.hasSurface && v.hasSurface
  | .transp _ a _ u0 => a.hasSurface && u0.hasSurface
  | .comp _ a sys u0 | .hcomp _ a sys u0 | .fill _ a sys u0 | .hfill _ a sys u0 =>
    a.hasSurface && u0.hasSurface && sys.all (·.2.hasSurface)
  | .glueTy a sys | .glue sys a => a.hasSurface && sys.all (·.2.hasSurface)
  | .unglue u _ _ => u.hasSurface
  | .data _ _ ps => ps.all (·.hasSurface)
  | .con _ as _ => as.all (·.hasSurface)
  | .ann t _ => t.hasSurface

def globalNames : M (List String) := do
  let g ← getGlobals
  return g.defs.toList.map (·.1) ++ g.datas.toList.map (·.1) ++ g.ctors.toList.map (·.1) ++ keywords

/-- Rename the context so that its names are distinct from each other and from all globals. -/
def uniqueCtx (ctx : Ctx) : M Ctx := do
  let mut taken ← globalNames
  let mut out : List CEntry := []
  for e in ctx.entries.reverse do
    let x := freshName taken (if e.name == "_" || e.name == "" then "x" else plainName e.name)
    taken := x :: taken
    out := { e with name := x } :: out
  return { ctx with entries := out }

/-- Run one check with a fresh budget and with the self-check hooks disabled. Errors other
than running out of budget are violations of `inv`. -/
def scRun (pos inv label : String) (x : M Unit) : M Unit := do
  let s ← get
  set { s with selfcheck := false, limit := s.steps + s.budget, nChecks := s.nChecks + 1 }
  let r ← try x; pure none catch e => pure (some e)
  modify fun s => { s with selfcheck := true, limit := 0 }
  match r with
  | none => pure ()
  | some e =>
    if e == budgetExceeded then modify fun s => { s with nSkipped := s.nSkipped + 1, skips := s.skips.push s!"{pos}: [{inv}] {label}" }
    else recordViolation s!"{pos}: [{inv}] {label}: raised an error: {e}"

def truncate (s : String) (n : Nat := 2000) : String :=
  if s.length ≤ n then s else (s.take n).toString ++ " ..."

def atomName (ctx : Ctx) (i : Atom) : String :=
  match ctx.entries.find? fun e => match e.val with
      | .d r => r == Formula.atom i
      | _ => false with
  | some e => e.name
  | none => s!"?i{i}"

def scTerm (ctx : Ctx) (tm : Tm) (ty : Val) (label : String) (checkTy : Bool := false) : M Unit := do
  let pos := s!"{ctx.pos.line}:{ctx.pos.col}"
  let fail (inv msg : String) : M Unit := recordViolation s!"{pos}: [{inv}] {label}: {msg}"
  let lvl := ctx.lvl
  scRun pos "conv-refl" label do
    let v ← eval ctx.env tm
    if !(← conv lvl ty v v) then fail "conv-refl" s!"value not convertible to itself:\n  {truncate (← ppVal ctx v)}"
    if !(← convTy lvl ty ty) then fail "conv-refl" s!"type not convertible to itself:\n  {truncate (← ppVal ctx ty)}"
  scRun pos "roundtrip" label do
    let v ← eval ctx.env tm
    let nf ← quote ctx.qctx v
    let v' ← eval ctx.env nf
    let a ← conv lvl ty v' v
    let b ← conv lvl ty v v'
    if !a || !b then
      fail "roundtrip" s!"eval (quote v) is not convertible to v ({a}/{b})\n  quote v:            {truncate (pp ctx.names 0 nf)}\n  quote (eval (quote v)): {truncate (← ppVal ctx v')}"
    if checkTy then
      let tnf ← quote ctx.qctx ty
      let ty' ← eval ctx.env tnf
      if !(← convTy lvl ty ty') || !(← convTy lvl ty' ty) then
        fail "roundtrip" s!"eval (quote A) is not convertible to the type A = {truncate (pp ctx.names 0 tnf)}"
  scRun pos "recheck" label do
    let v ← eval ctx.env tm
    let nf ← quote ctx.qctx v
    -- pattern-matching functions have no surface syntax as terms
    if !nf.hasSurface || !(← quote ctx.qctx ty).hasSurface then
      modify fun s => { s with nGaps := s.nGaps + 1 }
      return
    let ctx' ← uniqueCtx ctx
    let names := ctx'.names ++ (← globalNames)
    let reparse (src : String) (k : Raw → M Unit) : M Unit := do
      match parseTerm src with
      | .error e => fail "recheck" s!"printed normal form does not parse: {e}\n  {truncate src}"
      | .ok raw =>
        try k raw catch e =>
          if e == budgetExceeded then throw e
          fail "recheck" s!"printed normal form does not re-elaborate: {e}\n  {truncate src}"
    let src := pp names 0 nf { mask := ← implMasks }
    reparse src fun raw => do
      let tm' ← check ctx' raw ty
      let v'' ← eval ctx.env tm'
      if !(← conv lvl ty v'' v) then
        fail "recheck" s!"re-elaborated normal form is not convertible to the original value\n  {truncate src}"
    if checkTy then
      let tnf ← quote ctx.qctx ty
      if tnf.hasSurface then
        let tsrc := pp names 0 tnf { mask := ← implMasks }
        reparse tsrc fun raw => do
          let (tt, _) ← inferType ctx' raw
          if !(← convTy lvl (← eval ctx.env tt) ty) then
            fail "recheck" s!"re-elaborated type is not convertible to the original type\n  {truncate tsrc}"
  -- stability under interval substitutions
  let atoms := ctx.env.foldl (fun acc e => match e with
    | .d r => r.support.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) acc
    | .v _ => acc) []
  for i in atoms do
    let j ← freshAtom
    let others := atoms.filter (· != i)
    let iN := atomName ctx i
    let subs : List (String × Formula) :=
      [("0", Formula.zero), ("1", Formula.one), (s!"~{iN}", natomF i),
       (s!"{iN} ∧ j'", (atomF i).and (atomF j)), (s!"{iN} ∨ j'", (atomF i).or (atomF j))] ++
      (others.take 1).map fun k => (atomName ctx k, atomF k)
    for (sname, σ) in subs do
      let desc := s!"{iN} := {sname}"
      scRun pos "stability" label do
        let v ← eval ctx.env tm
        let lhs ← act i σ v
        let rhs ← eval (← actEnv i σ ctx.env) tm
        let tyσ ← act i σ ty
        let a ← conv lvl tyσ lhs rhs
        let b ← conv lvl tyσ rhs lhs
        if !a || !b then
          fail "stability" s!"substituting {desc}: (eval ρ t)σ ≠ eval (ρσ) t ({a}/{b})\n  (eval ρ t)σ = {truncate (← ppVal ctx lhs)}\n  eval (ρσ) t = {truncate (← ppVal ctx rhs)}"

/-- Self-check all terms recorded by the elaborator. -/
def scDrain : M Unit := do
  let items := (← get).pending
  modify fun s => { s with pending := #[] }
  for it in items do scTerm it.ctx it.tm it.ty it.label

end Kubus
