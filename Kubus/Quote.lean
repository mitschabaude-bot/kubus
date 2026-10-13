import Kubus.Eval

/-! # Read-back of values into normal forms, and pretty printing -/

namespace Kubus

inductive QE
  | tv (lvl : Nat)
  | dim (a : Atom)
  | other
  deriving BEq, Inhabited

/-- Read-back context: entries for de Bruijn indices, and the next fresh level. -/
structure QCtx where
  es : List QE
  next : Nat
  /-- print applications of globals folded (for display and metavariable solutions) rather than
  in normal form -/
  fold : Bool := false

def QCtx.pushV (q : QCtx) : QCtx × Val := ({ q with es := .tv q.next :: q.es, next := q.next + 1 }, .var q.next (.univ 0))
def QCtx.pushD (q : QCtx) (a : Atom) : QCtx := { q with es := .dim a :: q.es }

def quoteAtom (q : QCtx) (a : Atom) : Nat := (q.es.findIdx? (· == .dim a)).getD (1000000 + a)

def quoteF (q : QCtx) (r : Formula) : ITm :=
  let lit (l : Lit) : ITm := if l.pos then .var (quoteAtom q l.atom) else .neg (.var (quoteAtom q l.atom))
  let clause (c : Clause) : ITm := match c with
    | [] => .one
    | l :: ls => ls.foldl (fun acc l => .and acc (lit l)) (lit l)
  match r.dnf with
  | [] => .zero
  | c :: cs => cs.foldl (fun acc c => .or acc (clause c)) (clause c)

def quoteFace (q : QCtx) (α : Face) : ITm :=
  match α with
  | [] => .one
  | (i, d) :: rest =>
    let lit := fun (i : Atom) (d : Dir) => match d with
      | .one => ITm.var (quoteAtom q i)
      | .zero => ITm.neg (.var (quoteAtom q i))
    rest.foldl (fun acc (i, d) => .and acc (lit i d)) (lit i d)

mutual

partial def quote (q : QCtx) (v : Val) : M Tm := do
  match ← forceM v with
  | .glued g k sp =>
    -- applications to an endpoint are shown computed
    let endpoint := sp.any fun | .d r => r.toDir?.isSome | _ => false
    if q.fold && !endpoint then quoteSpine q (.glob g k) sp else quote q (← unfoldM v)
  | .univ l => pure (.univ l)
  | .pi x a env b =>
    let (q', xv) := q.pushV
    return .pi x (← quote q a) (← quote q' (← inst env b xv))
  | .lam x env b =>
    let (q', xv) := q.pushV
    return .lam x (← quote q' (← inst env b xv))
  | .sigma x a env b =>
    let (q', xv) := q.pushV
    return .sigma x (← quote q a) (← quote q' (← inst env b xv))
  | .pair a b => return .pair (← quote q a) (← quote q b)
  | .piI line =>
    let k ← freshAtom
    return .piI "i" (← quote (q.pushD k) (← papp line (atomF k)))
  | .pathP line a b => return .pathP (← quote q line) (← quote q a) (← quote q b)
  | .plam i b => return .plam "i" (← quote (q.pushD i) b)
  | .data d k ps => return .data d k (← ps.mapM (quote q))
  | .con c as => return .con c (← as.mapM (quote q)) []
  | .pcon c as ds => return .con c (← as.mapM (quote q)) (ds.map (quoteF q))
  | .hcompF ty u sys => return .hcomp "k" (← quote q ty) (← quoteLines q sys) (← quote q u)
  | .glueTy b sys => return .glueTy (← quote q b) (← quoteSys q sys)
  | .glue a sys => return .glue (← quoteSys q sys) (← quote q a)
  | .split f k env => quoteSpine q (.glob f k) env
  | .var lvl _ =>
    match q.es.findIdx? (· == .tv lvl) with
    | some i => pure (.var i)
    | none => pure (.glob s!"?x{lvl}" 0)
  | .gvar n _ => pure (.glob n 0)
  | .app f a => return .app (← quote q f) (← quote q a)
  | .fst p => return .fst (← quote q p)
  | .snd p => return .snd (← quote q p)
  | .papp p r => return .papp (← quote q p) (quoteF q r)
  | .splitApp f k env a => return .app (← quoteSpine q (.glob f k) env) (← quote q a)
  | .transp line φ u =>
    let k ← freshAtom
    return .transp "i" (← quote (q.pushD k) (← papp line (atomF k))) (quoteF q φ) (← quote q u)
  | .hcomp ty u sys => return .hcomp "k" (← quote q ty) (← quoteLines q sys) (← quote q u)
  | .unglue u b sys => return .unglue (← quote q u) (← quote q b) (← quoteSys q sys)

partial def quoteSpine (q : QCtx) (h : Tm) (env : Env) : M Tm := do
  let mut t := h
  for e in env.reverse do
    match e with
    | .v v => t := .app t (← quote q v)
    | .d r => t := .papp t (quoteF q r)
  return t

partial def quoteSys (q : QCtx) (sys : System Val) : M (List (ITm × Tm)) :=
  sys.mapM fun (α, v) => return (quoteFace q α, ← quote q v)

partial def quoteLines (q : QCtx) (sys : System Val) : M (List (ITm × Tm)) :=
  sys.mapM fun (α, l) => do
    let k ← freshAtom
    return (quoteFace q α, ← quote (q.pushD k) (← papp l (atomF k)))

end

/-! ## Pretty printing -/

def freshName (names : List String) (x : String) : String :=
  if x == "_" then "_" else
  if !names.contains x then x else
  let rec go (n : Nat) (fuel : Nat) : String :=
    match fuel with
    | 0 => x ++ "'"
    | fuel + 1 => let c := x ++ toString n; if names.contains c then go (n + 1) fuel else c
  go 1 1000

def nameAt (names : List String) (i : Nat) : String :=
  match names[i]? with
  | some x => x
  | none => if i ≥ 1000000 then s!"?i{i - 1000000}" else s!"#{i}"

partial def ppI (names : List String) (p : Nat) : ITm → String
  | .zero => "0"
  | .one => "1"
  | .var i => nameAt names i
  | .neg r => "~" ++ ppI names 3 r
  | .and r s => let str := ppI names 2 r ++ " /\\ " ++ ppI names 2 s; if p > 2 then s!"({str})" else str
  | .or r s => let str := ppI names 1 r ++ " \\/ " ++ ppI names 1 s; if p > 1 then s!"({str})" else str

def paren (b : Bool) (s : String) : String := if b then s!"({s})" else s

/-- Printing options: which binders of each global's type are implicit (printed as `{a}`). -/
structure PPI where
  mask : String → List Bool := fun _ => []
  /-- how to print a metavariable -/
  metaStr : Nat → String := fun m => s!"?m{m}"
  /-- print the arguments for implicit binders (as `{a}`); otherwise they are omitted -/
  showImplicit : Bool := true
  deriving Inhabited

mutual
/-- Precedences: 0 binders, 1 arrows, 2 application, 3 atoms. -/
partial def pp (names : List String) (p : Nat) (t : Tm) (im : PPI := {}) : String :=
  let pp := fun names p t => pp names p t im
  let ppSys := fun kn en sys => ppSys kn en sys im
  match t with
  | .ann t _ => pp names p t
  | .var i => nameAt names i
  | .glob n 0 => match metaId? n with
    | some m => im.metaStr m
    | none => n
  | .glob n k => s!"{n}^{k}"
  | .univ 0 => "U"
  | .univ l => paren (p > 2) s!"U {l}"
  | .pi x a b =>
    let impl := isImplName x
    if impl || b.occurs 0 then
      -- consecutive binders with the same domain are grouped: `(x y : A) → B`
      let (xs, ns, body) := Id.run do
        let x' := freshName names (plainName x)
        let mut ns := x' :: names
        let mut xs := #[x']
        let mut body := b
        repeat
          match body with
          | .pi y a2 b2 =>
            if isImplName y == impl && (impl || b2.occurs 0) && a2 == a.shift xs.size then
              let y' := freshName ns (plainName y)
              ns := y' :: ns
              xs := xs.push y'
              body := b2
            else break
          | _ => break
        return (xs, ns, body)
      let bs := " ".intercalate xs.toList
      let binder := if impl then "{" ++ bs ++ " : " ++ pp names 0 a ++ "}" else s!"({bs} : {pp names 0 a})"
      paren (p > 1) s!"{binder} → {pp ns 1 body}"
    else paren (p > 1) s!"{pp names 2 a} → {pp ("_" :: names) 1 b}"
  | .sigma x a b =>
    if b.occurs 0 then
      let x' := freshName names x
      paren (p > 1) s!"({x'} : {pp names 0 a}) × {pp (x' :: names) 1 b}"
    else paren (p > 1) s!"{pp names 2 a} × {pp ("_" :: names) 1 b}"
  | .lam x b | .plam x b =>
    let impl := isImplName x
    let x := plainName x
    let x' := freshName names (if x == "_" && (b.occurs 0 || impl) then "x" else x)
    let bx := if impl then "{" ++ x' ++ "}" else x'
    paren (p > 0) s!"λ {bx} → {pp (x' :: names) 0 b}"
  | .piI i a =>
    let i' := freshName names (if i == "_" && a.occurs 0 then "i" else i)
    paren (p > 1) s!"({i'} : I) → {pp (i' :: names) 1 a}"
  | .app .. | .papp .. =>
    let (h, args) := t.sargs
    match h with
    | .glob n _ => match metaId? n with
      | some m => im.metaStr m
      | none => ppApp names p h args im
    | _ => ppApp names p h args im
  | .pair a b => s!"({pp names 0 a}, {pp names 0 b})"
  | .fst t => s!"{pp names 3 t}.1"
  | .snd t => s!"{pp names 3 t}.2"
  | .pathP (.plam i a) u v =>
    if a.occurs 0 then
      let i' := freshName names i
      paren (p > 2) s!"PathP (λ {i'} → {pp (i' :: names) 0 a}) {pp names 3 u} {pp names 3 v}"
    else paren (p > 2) s!"Path {pp ("_" :: names) 3 a} {pp names 3 u} {pp names 3 v}"
  | .pathP a u v => paren (p > 2) s!"PathP {pp names 3 a} {pp names 3 u} {pp names 3 v}"
  | .comp i a sys u0 =>
    let i' := freshName names i
    paren (p > 2) s!"comp {i'} {pp (i' :: names) 3 a} {ppSys names (i' :: names) sys} {pp names 3 u0}"
  | .hcomp i a sys u0 =>
    let i' := freshName names i
    paren (p > 2) s!"hcomp {i'} {pp names 3 a} {ppSys names (i' :: names) sys} {pp names 3 u0}"
  | .fill i a sys u0 =>
    let i' := freshName names i
    paren (p > 2) s!"fill {i'} {pp (i' :: names) 3 a} {ppSys names (i' :: names) sys} {pp names 3 u0}"
  | .hfill i a sys u0 =>
    let i' := freshName names i
    paren (p > 2) s!"hfill {i'} {pp names 3 a} {ppSys names (i' :: names) sys} {pp names 3 u0}"
  | .glueTy a sys => paren (p > 2) s!"Glue {pp names 3 a} {ppSys names names sys}"
  | .glue sys a => paren (p > 2) s!"glue {ppSys names names sys} {pp names 3 a}"
  | .unglue u _ _ => paren (p > 2) s!"unglue {pp names 3 u}"
  | .transp i a φ u0 =>
    let i' := freshName names i
    paren (p > 2) s!"transp {i'} {pp (i' :: names) 3 a} [{ppI names 0 φ}] {pp names 3 u0}"
  | .data d k [] => if k == 0 then d else s!"{d}^{k}"
  | .data d k ps => paren (p > 2) (" ".intercalate ((if k == 0 then d else s!"{d}^{k}") :: ps.map (pp names 3)))
  | .con c [] [] => c
  | .con c as ds => paren (p > 2) (" ".intercalate (c :: as.map (pp names 3) ++ ds.map (ppI names 3)))
  | .split f _ => s!"<split {f}>"
  | .letE x t b =>
    let x' := freshName names x
    paren (p > 0) s!"let {x'} := {pp names 0 t} in {pp (x' :: names) 0 b}"

/-- An application; arguments for implicit binders of a global are printed as `{a}`. -/
partial def ppApp (names : List String) (p : Nat) (h : Tm) (args : Array SArg) (im : PPI := {}) : String :=
  let mask := match h with
    | .glob f _ => im.mask f
    | _ => []
  let parts := (List.range args.size).zip args.toList |>.filterMap fun (i, a) => match a with
    | .tm a =>
      if mask[i]?.getD false then
        if im.showImplicit then some ("{" ++ pp names 0 a im ++ "}") else none
      else some (pp names 3 a im)
    | .dim r => some (ppI names 3 r)
  if parts.isEmpty then pp names p h im else
  paren (p > 2) (" ".intercalate (pp names 2 h im :: parts))

partial def ppSys (keyNames elemNames : List String) (sys : List (ITm × Tm)) (im : PPI := {}) : String :=
  "[" ++ ", ".intercalate (sys.map fun (r, t) => s!"{ppKey keyNames r} -> {pp elemNames 0 t im}") ++ "]"

/-- System keys are printed as faces `i = 0 /\\ j = 1` when possible. -/
partial def ppKey (names : List String) (r : ITm) : String :=
  let rec lits : ITm → Option (List String)
    | .var i => some [s!"{nameAt names i} = 1"]
    | .neg (.var i) => some [s!"{nameAt names i} = 0"]
    | .and a b => do return (← lits a) ++ (← lits b)
    | _ => none
  match lits r with
  | some ls => " /\\ ".intercalate ls
  | none => ppI names 0 r
end

end Kubus
