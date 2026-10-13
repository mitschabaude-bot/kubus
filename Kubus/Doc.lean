import Lean.Data.Json
import Kubus.Lsp

/-! # Documentation mode (`kubus --doc FILE`)

Elaborates a file and prints, as JSON, everything needed to render it as hyperlinked,
highlighted source (the website's code blocks and library pages):

- `tokens`: every token and comment, with its class (keyword, definition, global, constructor,
  data type, bound variable, interval variable/operator, system arrow, universe, hole, …), the
  type of the identifier under it (from the elaborator, as the language server shows it), and
  for globals the place of their definition;
- `decls`: every declaration, with its source lines, the `#eval`/`#check` output, the error it
  raised (elaboration continues with the next declaration), the goals of its holes, and the
  kernel's verdict;
- `defs`: where every global known to the file (including imports) is defined.
-/

namespace Kubus.Doc

open Lean (Json)

structure Site where
  file : String
  line : Nat
  col : Nat

structure Tok where
  line : Nat
  col : Nat
  len : Nat
  kind : String
  hover : Option String := none
  site : Option Site := none
  /-- an anchor (the name), at definition sites -/
  anchor : Option String := none

structure DeclOut where
  name : Option String
  line : Nat
  endLine : Nat
  out : Option String := none
  error : Option (Pos × String) := none
  goals : Array (Pos × String) := #[]
  /-- `certified`, `rejected`, `skipped`, or none for commands and failed declarations -/
  kernel : Option String := none
  kernelMsg : Option String := none

/-! ## Lexical classes -/

def keywordClass (s : String) : Option String :=
  if ["def", "data", "import", "let", "in", "fun", "#eval", "#check"].contains s then some "keyword"
  else if ["comp", "hcomp", "fill", "Glue", "glue", "unglue"].contains s then some "kan"
  else if ["Path", "PathP"].contains s then some "builtin"
  else if s == "U" then some "universe"
  else if s == "I" then some "interval"
  else none

def symClass (s : String) (inSystem : Bool) : String :=
  if ["/\\", "\\/", "∧", "∨", "~"].contains s then "interval-op"
  else if s == "=" then "face"
  else if ["->", "→", "↦", "=>"].contains s then (if inSystem then "system-arrow" else "arrow")
  else if s == "\\" || s == "λ" then "lambda"
  else if s == "[" || s == "]" then "system"
  else if s == "?" then "hole"
  else if s == "{" || s == "}" then "implicit"
  else "punct"

/-- Comment spans `(line, col, len)`, one per line. -/
def comments (src : String) : Array (Nat × Nat × Nat) := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut out := #[]
  let mut i := 0
  let mut line := 1
  let mut col := 1
  let mut depth := 0
  let mut start : Option (Nat × Nat) := none
  let at_ := fun (i : Nat) (s : String) => (List.range s.length).all fun k => cs[i + k]? == s.toList[k]?
  while i < n do
    let c := cs[i]!
    if depth == 0 && at_ i "--" then
      let (l, c0) := (line, col)
      while i < n && cs[i]! != '\n' do i := i + 1; col := col + 1
      out := out.push (l, c0, col - c0)
    else if at_ i "{-" then
      if depth == 0 then start := some (line, col)
      depth := depth + 1; i := i + 2; col := col + 2
    else if depth > 0 && at_ i "-}" then
      depth := depth - 1; i := i + 2; col := col + 2
      if depth == 0 then
        if let some (l, c0) := start then out := out.push (l, c0, col - c0)
        start := none
    else if c == '\n' then
      if depth > 0 then
        if let some (l, c0) := start then out := out.push (l, c0, col - c0)
        start := some (line + 1, 1)
      i := i + 1; line := line + 1; col := 1
    else
      i := i + 1; col := col + 1
  return out

/-! ## Elaboration with recorded contexts -/

/-- The hover records of the last declaration: range, context, printed type. -/
abbrev Records := Array (Pos × Ctx × String)

def inRange (p : Pos) (l c : Nat) : Bool :=
  p.eline > 0 && (p.line < l || (p.line == l && p.col ≤ c)) && (l < p.eline || (l == p.eline && c < p.ecol))

/-- Check a declaration like `checkDecl` in editor mode, keeping the contexts of the recorded
subterms. -/
def docDecl (d : Decl) : M (Option String × Records × Array (Pos × String)) := do
  modify fun s => { s with metas := #[], lsp := true, pendingHovers := #[], pendingGoals := #[] }
  let out ← checkDecl' d
  let recs ← (← get).pendingHovers.mapM fun (p, ctx, ty) => return (p, ctx, ← ppVal ctx ty)
  let goals ← (← get).pendingGoals.mapM fun (p, ctx, ty) => do
    return (p, s!"goal: {← ppVal ctx ty}\ncontext:\n{← ppCtx ctx}")
  modify fun st => { st with pendingHovers := #[], pendingGoals := #[], hovers := #[], goals := #[] }
  if (← get).metas.any (·.hole) then
    match d with
    | .defn n .. | .defSplit n .. =>
      let mkOpaque := fun (i : DefInfo) => { i with body := none, value := none, branches := [] }
      modify fun st => { st with globals.defs := st.globals.defs.modify n mkOpaque }
    | _ => pure ()
  return (out, recs, goals)

/-- The type of a local variable `x` in a context, if bound there. -/
def localInfo (ctx : Ctx) (x : String) : M (Option (Bool × String)) := do
  match ctx.lookup x with
  | some (i, e) =>
    match e.ty with
    | some a => return some (false, ← ppVal { ctx with entries := ctx.entries.drop (i + 1) } a)
    | none => return some (true, "I")
  | none => return none

/-- The types of data types and constructors, for hovers: `D : (ps) → U n`, and
`c : {ps} → (args) → (i : I) → D ps`. -/
def dataTypeTm (info : DataInfo) : Tm :=
  info.params.foldr (fun (x, a) b => .pi x a b) (.univ info.level)

def ctorTypeTm (info : DataInfo) (c : CtorInfo) : Tm :=
  let np := info.params.length
  let na := c.tele.length
  let nd := c.dims.length
  let res : Tm := .data info.name 0 ((List.range np).map fun j => .var (na + nd + np - 1 - j))
  let withDims := c.dims.foldr (fun i b => .piI i b) res
  let withArgs := c.tele.foldr (fun (x, a) b => .pi x a b) withDims
  info.params.foldr (fun (x, a) b => .pi (implName x) a b) withArgs

def globalHover (x : String) : M (Option String) := do
  let g ← getGlobals
  if let some info := g.defs[x]? then return some s!"{x} : {← ppVal {} info.ty}"
  if let some info := g.datas[x]? then return some s!"{x} : {← ppTm {} (dataTypeTm info)}"
  if let some c := g.ctors[x]? then
    if let some info := g.datas[c.data]? then return some s!"{x} : {← ppTm {} (ctorTypeTm info c)}"
  return none

/-- Classify the identifier tokens of a declaration. -/
def classify (src : Array Kubus.Tok) (recs : Records) (defs : Std.HashMap String Site)
    (declName : Option String) (ctorNames : List String) : M (Array Tok) := do
  let g ← getGlobals
  let mut out := #[]
  let mut inSystem := 0
  let mut prev : Option TokK := none
  let mut prevUniverse := false
  for t in src do
    let l := t.pos.line
    let c := t.pos.col
    match t.k with
    | .sym s =>
      if s == "[" then inSystem := inSystem + 1
      let k := symClass s (inSystem > 0)
      if s == "]" then inSystem := inSystem - 1
      out := out.push { line := l, col := c, len := t.len, kind := k }
    | .num _ =>
      out := out.push { line := l, col := c, len := t.len, kind := if prevUniverse then "universe" else "interval-const" }
    | .ident x =>
      if let some k := keywordClass x then
        out := out.push { line := l, col := c, len := t.len, kind := k }
      else
        let exact := recs.find? fun (p, _, _) => p.line == l && p.col == c && p.eline == l && p.ecol == c + t.len
        let isDefSite := (prev == some (.ident "def") || prev == some (.ident "data")) && declName == some x
        let isCtorSite := ctorNames.contains x && (prev == some (.ident "data") || prev == some (.sym "|") || prev == some (.sym ":="))
        if isDefSite || isCtorSite then
          let hover ← globalHover x
          out := out.push { line := l, col := c, len := t.len, kind := if isDefSite then "definition" else "constructor",
                            anchor := some x, hover }
        else
          -- a local variable: bound in the context of the record at this token, or (binder
          -- sites) of a record after it
          let ctxRec := match exact with
            | some r => some r
            | none => recs.find? fun (p, ctx, _) =>
                (p.line > l || (p.line == l && p.col > c)) && (ctx.lookup x).isSome
          let loc ← match ctxRec with
            | some (_, ctx, _) => localInfo ctx x
            | none => pure none
          let local? := match exact, loc with
            | some (_, ctx, _), _ => (ctx.lookup x).isSome
            | none, some _ => true
            | none, none => false
          let encl := recs.foldl (fun acc (p, ctx, _) =>
            if inRange p l c && (ctx.lookup x).isSome then some ctx else acc) none
          let interval ← match encl with
            | some ctx => pure (((← localInfo ctx x).map (·.1)).getD false)
            | none => pure ((loc.map (·.1)).getD false)
          if x == "_" then
            out := out.push { line := l, col := c, len := t.len, kind := "hole" }
          else if local? || interval then
            let isI := interval || (loc.map (·.1)).getD false
            let hover := match exact, loc with
              | some (_, _, ty), _ => some s!"{x} : {ty}"
              | none, some (false, ty) => some s!"{x} : {ty}"
              | _, _ => if isI then some s!"{x} : I" else none
            out := out.push { line := l, col := c, len := t.len, kind := if isI then "interval-var" else "variable", hover }
          else
            let kind := if g.ctors.contains x then "constructor"
              else if g.datas.contains x then "data"
              else if g.defs.contains x then "global"
              else "unknown"
            let hover := (exact.map fun (_, _, ty) => s!"{x} : {ty}")
            let hover ← match hover with
              | none => globalHover x
              | h => pure h
            out := out.push { line := l, col := c, len := t.len, kind, hover, site := defs[x]? }
    | .eof => pure ()
    prevUniverse := t.k == .ident "U"
    prev := some t.k
  return out

/-! ## Files -/

structure FileOut where
  tokens : Array Tok := #[]
  decls : Array DeclOut := #[]

def declName : Decl → Option String
  | .defn n .. | .defSplit n .. | .data n .. => some n
  | _ => none

def ctorsOf : Decl → List (String × Pos)
  | .data _ _ _ cs _ => cs.map fun c => (c.name, c.pos)
  | _ => []

/-- Definition sites of a file's declarations. -/
def sitesOf (file : String) (decls : List Decl) : List (String × Site) :=
  decls.flatMap fun d =>
    let p := Lsp.declPos d
    (match declName d with
     | some n => [(n, ⟨file, p.line, p.col⟩)]
     | none => []) ++ (ctorsOf d).map fun (c, cp) => (c, ⟨file, cp.line, cp.col⟩)

/-- Load an import (recursively), recording definition sites. -/
partial def loadImport (path : System.FilePath) (st : St) (loaded : List System.FilePath)
    (sites : Std.HashMap String Site) : ExceptT String IO (St × List System.FilePath × Std.HashMap String Site) := do
  if loaded.contains path then return (st, loaded, sites)
  let mut loaded := path :: loaded
  let mut st := st
  let mut sites := sites
  let decls ← match parseFile (← IO.FS.readFile path) with
    | .ok ds => pure ds
    | .error e => throw s!"{path}:{e}"
  let modName := path.fileStem.getD path.toString
  for (n, s) in sitesOf modName decls do sites := sites.insert n s
  for d in decls do
    match d with
    | .importFile name _ =>
      match ← Lsp.findImport (path.parent.getD ".") name with
      | some f => (st, loaded, sites) ← loadImport f st loaded sites
      | none => throw s!"{path}: cannot find module {name}"
    | _ =>
      match (checkDecl d).run st with
      | .ok (_, st') => st := st'
      | .error e => throw s!"{path}:{e}"
  return (st, loaded, sites)

def docFile (path : System.FilePath) (kernel : Bool) : ExceptT String IO FileOut := do
  let text ← IO.FS.readFile path
  let decls ← match parseFile text with
    | .ok ds => pure ds
    | .error e => throw s!"{path}:{e}"
  let modName := path.fileStem.getD path.toString
  let mut st : St := {}
  let mut loaded : List System.FilePath := []
  let mut sites : Std.HashMap String Site := {}
  for d in decls do
    if let .importFile name _ := d then
      match ← Lsp.findImport (path.parent.getD ".") name with
      | some f => (st, loaded, sites) ← loadImport f st loaded sites
      | none => throw s!"{path}: cannot find module {name}"
  for (n, s) in sitesOf modName decls do sites := sites.insert n s
  let toks ← match lex text with
    | .ok ts => pure ts
    | .error e => throw s!"{path}:{e}"
  let lines := (text.splitOn "\n").length
  let starts := decls.map fun d => (Lsp.declPos d).line
  let mut out : FileOut := {}
  let mut ks : Bridge.State := {}
  for (c0, c1, n) in comments text do out := { out with tokens := out.tokens.push { line := c0, col := c1, len := n, kind := "comment" } }
  for (d, di) in decls.zipIdx do
    let p := Lsp.declPos d
    let endLine := ((starts[di + 1]?).getD (lines + 1)) - 1
    let dtoks := toks.filter fun t => t.pos.line ≥ p.line && t.pos.line ≤ endLine && t.k != .eof
    let mut dout : DeclOut := { name := declName d, line := p.line, endLine }
    if let .importFile name _ := d then
      out := { out with tokens := out.tokens ++ dtoks.map fun t => match t.k with
        | .ident x => if x == "import" then { line := t.pos.line, col := t.pos.col, len := t.len, kind := "keyword" : Tok }
          else { line := t.pos.line, col := t.pos.col, len := t.len, kind := "module", site := some ⟨name, 1, 1⟩ }
        | _ => { line := t.pos.line, col := t.pos.col, len := t.len, kind := "punct" } }
      out := { out with decls := out.decls.push dout }
      continue
    match (docDecl d).run st with
    | .ok ((o, recs, goals), st') =>
      let ctorNames := (ctorsOf d).map (·.1)
      match (classify dtoks recs sites (declName d) ctorNames).run st' with
      | .ok (ts, _) => out := { out with tokens := out.tokens ++ ts }
      | .error e => throw s!"{path}: internal error while classifying: {e}"
      dout := { dout with out := o, goals := goals }
      st := st'
      if kernel then
        if let some n := declName d then
          let run := match d with
            | .data .. => Bridge.addData st'.globals n 0
            | _ => Bridge.addGlobal st'.globals n 0
          let (msgs, ks') := run.run ks
          ks := ks'
          let verdict := if msgs.any (fun m => m == s!"kernel: certified {n}" || m == s!"kernel: certified data {n}") then "certified"
            else if msgs.any (·.startsWith "kernel: REJECTED") then "rejected" else "skipped"
          let msg := msgs.find? fun m => !m.startsWith "kernel: certified"
          dout := { dout with kernel := some verdict, kernelMsg := msg }
    | .error e =>
      let (ep, msg) := Lsp.parseError e
      dout := { dout with error := some (ep, msg) }
      -- tokens without semantic information
      match (classify dtoks #[] sites (declName d) ((ctorsOf d).map (·.1))).run st with
      | .ok (ts, _) => out := { out with tokens := out.tokens ++ ts }
      | .error _ => pure ()
    out := { out with decls := out.decls.push dout }
  return out

/-! ## JSON -/

def jpos (p : Pos) : Json :=
  Json.mkObj [("line", p.line), ("col", p.col), ("eline", p.eline), ("ecol", p.ecol)]

def Tok.json (t : Tok) : Json :=
  Json.mkObj <| [("l", Json.num t.line), ("c", Json.num t.col), ("n", Json.num t.len), ("k", Json.str t.kind)] ++
    (t.hover.map fun h => [("h", Json.str h)]).getD [] ++
    (t.site.map fun s => [("d", Json.mkObj [("f", s.file), ("l", s.line), ("c", s.col)])]).getD [] ++
    (t.anchor.map fun a => [("a", Json.str a)]).getD []

def DeclOut.json (d : DeclOut) : Json :=
  Json.mkObj <| [("line", Json.num d.line), ("endLine", Json.num d.endLine)] ++
    (d.name.map fun n => [("name", Json.str n)]).getD [] ++
    (d.out.map fun o => [("out", Json.str o)]).getD [] ++
    (d.error.map fun (p, m) => [("error", Json.mkObj [("pos", jpos p), ("msg", m)])]).getD [] ++
    (if d.goals.isEmpty then [] else
      [("goals", Json.arr (d.goals.map fun (p, g) => Json.mkObj [("pos", jpos p), ("msg", g)]))]) ++
    (d.kernel.map fun k => [("kernel", Json.str k)]).getD [] ++
    (d.kernelMsg.map fun k => [("kernelMsg", Json.str k)]).getD []

/-- `kubus --doc FILE`: print the JSON description of the file. -/
def main (file : String) (kernel : Bool) : IO UInt32 := do
  match ← (docFile file kernel).run with
  | .ok o =>
    let toks := o.tokens.qsort fun a b => a.line < b.line || (a.line == b.line && a.col < b.col)
    IO.println (Json.mkObj [("tokens", Json.arr (toks.map Tok.json)), ("decls", Json.arr (o.decls.map DeclOut.json))]).compress
    return 0
  | .error e => IO.eprintln e; return 1

end Kubus.Doc
