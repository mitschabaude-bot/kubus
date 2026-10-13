import Lean.Data.Json
import Kubus.Top
import Kubus.Parser

/-! # A minimal language server (`kubus --lsp`)

LSP over standard input/output: full document sync; on open, change and save the document
is checked and diagnostics are published (errors with their source range, `#eval`/`#check`
results and the goals of `?` holes as information); hover shows the type of the smallest
elaborated subterm under the cursor. Imports are resolved from the document's directory and
`KUBUS_PATH`, and cached until a file is saved.
-/

namespace Kubus.Lsp

open Lean (Json)

/-! ## Transport -/

def readMessage (h : IO.FS.Stream) : IO (Option Json) := do
  let mut len : Option Nat := none
  repeat
    let line ← h.getLine
    if line.isEmpty then return none
    let line := line.trimAscii.toString
    if line.isEmpty then break
    if line.startsWith "Content-Length:" then
      len := (line.drop 15).trimAscii.toString.toNat?
  let some n := len | return none
  let mut buf := ByteArray.empty
  while buf.size < n do
    let chunk ← h.read (n - buf.size).toUSize
    if chunk.isEmpty then return none
    buf := buf ++ chunk
  match String.fromUTF8? buf with
  | some s => return (Json.parse s).toOption
  | none => return none

def writeMessage (h : IO.FS.Stream) (j : Json) : IO Unit := do
  let s := j.compress
  h.putStr s!"Content-Length: {s.utf8ByteSize}\r\n\r\n{s}"
  h.flush

/-! ## Checking a document -/

structure Diag where
  pos : Pos
  severity : Nat
  msg : String

structure Result where
  diags : Array Diag := #[]
  hovers : Array (Pos × String) := #[]

/-- Split `l:c: msg` or `l:c-el:ec: msg` (positions of `checkDecl` errors). -/
def parseError (e : String) : Pos × String :=
  match e.splitOn ": " with
  | loc :: rest =>
    let msg := ": ".intercalate rest
    let (s, en) := match loc.splitOn "-" with
      | [s, en] => (s, some en)
      | _ => (loc, none)
    let lc (x : String) : Option (Nat × Nat) := match x.splitOn ":" with
      | [l, c] => do return (← l.toNat?, ← c.toNat?)
      | _ => none
    match lc s with
    | some (l, c) =>
      let p : Pos := { line := l, col := c }
      match en.bind lc with
      | some (el, ec) => ({ p with eline := el, ecol := ec }, msg)
      | none => (p, msg)
    | none => ({ line := 1, col := 1 }, e)
  | [] => ({ line := 1, col := 1 }, e)

def findImport (dir : System.FilePath) (name : String) : IO (Option System.FilePath) := do
  let envPath := ((← IO.getEnv "KUBUS_PATH").getD "").splitOn ":" |>.filter (· != "")
  for d in dir :: envPath.map System.FilePath.mk do
    let f := d / (name ++ ".ktt")
    if ← f.pathExists then return some (← IO.FS.realPath f)
  return none

/-- Load an imported file (and its imports) into `st`. -/
partial def loadFile (path : System.FilePath) (st : St) (loaded : List System.FilePath) :
    ExceptT String IO (St × List System.FilePath) := do
  if loaded.contains path then return (st, loaded)
  let mut loaded := path :: loaded
  let mut st := st
  let decls ← match parseFile (← IO.FS.readFile path) with
    | .ok ds => pure ds
    | .error e => throw s!"{path}:{e}"
  for d in decls do
    match d with
    | .importFile name _ =>
      match ← findImport (path.parent.getD ".") name with
      | some f => (st, loaded) ← loadFile f st loaded
      | none => throw s!"{path}: cannot find module {name}"
    | _ =>
      match (checkDecl d).run st with
      | .ok (_, st') => st := st'
      | .error e => throw s!"{path}:{e}"
  return (st, loaded)

/-- The state after loading imports, cached by the list of imported files. -/
initialize importCache : IO.Ref (Option (List System.FilePath × St)) ← IO.mkRef none

def checkText (path : System.FilePath) (text : String) : IO Result := do
  let mut res : Result := {}
  let decls ← match parseFile text with
    | .ok ds => pure ds
    | .error e =>
      let (p, msg) := parseError e
      return { res with diags := #[⟨p, 1, msg⟩] }
  -- imports first
  let dir := path.parent.getD "."
  let mut files : Array System.FilePath := #[]
  for d in decls do
    if let .importFile name pos := d then
      match ← findImport dir name with
      | some f => files := files.push f
      | none => res := { res with diags := res.diags.push ⟨pos, 1, s!"cannot find module {name}"⟩ }
  let mut st : St := {}
  match ← importCache.get with
  | some (fs, st') => if fs == files.toList then st := st'
  | none => pure ()
  if (← importCache.get).all (·.1 != files.toList) then
    let mut loaded : List System.FilePath := []
    for f in files do
      match ← (loadFile f st loaded).run with
      | .ok (st', l) => st := st'; loaded := l
      | .error e =>
        let pos := (decls.findSome? fun | .importFile _ p => some p | _ => none).getD { line := 1, col := 1 }
        res := { res with diags := res.diags.push ⟨pos, 1, s!"error in an imported file: {e}"⟩ }
    importCache.set (some (files.toList, st))
  st := { st with lsp := true }
  for d in decls do
    if let .importFile .. := d then continue
    match (checkDecl d).run st with
    | .ok (out, st') =>
      let pos := match d with
        | .defn _ _ _ _ p | .defSplit _ _ _ _ p | .data _ _ _ _ p | .eval _ p | .check _ p | .importFile _ p => p
      if let some o := out then res := { res with diags := res.diags.push ⟨pos, 3, o⟩ }
      for (p, g) in st'.goals do res := { res with diags := res.diags.push ⟨p, 3, g⟩ }
      res := { res with hovers := res.hovers ++ st'.hovers }
      st := { st' with goals := #[], hovers := #[] }
    | .error e =>
      let (p, msg) := parseError e
      res := { res with diags := res.diags.push ⟨p, 1, msg⟩ }
  return res

/-! ## Positions -/

def lineOf (text : String) (l : Nat) : String := ((text.splitOn "\n")[l - 1]?).getD ""

/-- The end of a range: as recorded, or the end of the word at its start. -/
def rangeEnd (text : String) (p : Pos) : Nat × Nat :=
  if p.eline > 0 then (p.eline, p.ecol) else
  let cs := (lineOf text p.line).toList.drop (p.col - 1)
  let n := (cs.takeWhile fun c => !c.isWhitespace && !"()[],".contains c).length
  (p.line, p.col + max n 1)

def jpos (l c : Nat) : Json := Json.mkObj [("line", (l - 1 : Nat)), ("character", (c - 1 : Nat))]

def jrange (text : String) (p : Pos) : Json :=
  let (el, ec) := rangeEnd text p
  Json.mkObj [("start", jpos p.line p.col), ("end", jpos el ec)]

/-- The source text of a range. -/
def slice (text : String) (p : Pos) : String :=
  let ls := text.splitOn "\n"
  let (el, ec) := rangeEnd text p
  if el == p.line then
    String.ofList (((ls[p.line - 1]?).getD "").toList.drop (p.col - 1) |>.take (ec - p.col))
  else
    let first := String.ofList (((ls[p.line - 1]?).getD "").toList.drop (p.col - 1))
    let mid := (ls.drop p.line).take (el - p.line - 1)
    let last := String.ofList (((ls[el - 1]?).getD "").toList.take (ec - 1))
    "\n".intercalate (first :: mid ++ [last])

def contains (text : String) (p : Pos) (l c : Nat) : Bool :=
  let (el, ec) := rangeEnd text p
  (p.line < l || (p.line == l && p.col ≤ c)) && (l < el || (l == el && c < ec))

/-- A measure of the size of a range (lines, then columns). -/
def size (text : String) (p : Pos) : Nat :=
  let (el, ec) := rangeEnd text p
  (el - p.line) * 100000 + (if el == p.line then ec - p.col else ec)

/-! ## The server -/

structure Doc where
  text : String
  hovers : Array (Pos × String) := #[]

def uriToPath (uri : String) : System.FilePath :=
  let s := if uri.startsWith "file://" then (uri.drop 7).toString else uri
  -- percent-decoding of the common cases
  let s := (s.replace "%20" " ").replace "%3A" ":"
  System.FilePath.mk s

def str (j : Json) (path : List String) : Option String := do
  let mut j := j
  for k in path do j ← (j.getObjVal? k).toOption
  (j.getStr?).toOption

def nat (j : Json) (path : List String) : Option Nat := do
  let mut j := j
  for k in path do j ← (j.getObjVal? k).toOption
  (j.getNat?).toOption

def publish (out : IO.FS.Stream) (uri text : String) (r : Result) : IO Unit := do
  let ds := r.diags.map fun d => Json.mkObj [("range", jrange text d.pos), ("severity", d.severity),
    ("source", "kubus"), ("message", d.msg)]
  writeMessage out (Json.mkObj [("jsonrpc", "2.0"), ("method", "textDocument/publishDiagnostics"),
    ("params", Json.mkObj [("uri", uri), ("diagnostics", Json.arr ds)])])

def respond (out : IO.FS.Stream) (id : Json) (result : Json) : IO Unit :=
  writeMessage out (Json.mkObj [("jsonrpc", "2.0"), ("id", id), ("result", result)])

partial def serve : IO UInt32 := do
  let inp ← IO.getStdin
  let out ← IO.getStdout
  let docs ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap String Doc)
  let recheck (uri text : String) : IO Unit := do
    let r ← try checkText (uriToPath uri) text
      catch e => pure { diags := #[⟨{ line := 1, col := 1 }, 1, s!"internal error: {e}"⟩] }
    docs.modify (·.insert uri { text, hovers := r.hovers })
    publish out uri text r
  repeat
    let some msg ← readMessage inp | return 0
    let method := (str msg ["method"]).getD ""
    let id := msg.getObjValD "id"
    let params := msg.getObjValD "params"
    match method with
    | "initialize" =>
      respond out id (Json.mkObj [
        ("capabilities", Json.mkObj [
          ("textDocumentSync", Json.mkObj [("openClose", true), ("change", (1 : Nat)),
            ("save", Json.mkObj [("includeText", false)])]),
          ("hoverProvider", true)]),
        ("serverInfo", Json.mkObj [("name", "kubus")])])
    | "shutdown" => respond out id Json.null
    | "exit" => return 0
    | "textDocument/didOpen" =>
      if let (some uri, some text) := (str params ["textDocument", "uri"], str params ["textDocument", "text"]) then
        recheck uri text
    | "textDocument/didChange" =>
      if let some uri := str params ["textDocument", "uri"] then
        let changes := ((params.getObjValD "contentChanges").getArr?).toOption.getD #[]
        if let some text := changes.back?.bind (str · ["text"]) then recheck uri text
    | "textDocument/didSave" =>
      importCache.set none
      if let some uri := str params ["textDocument", "uri"] then
        if let some d := (← docs.get)[uri]? then recheck uri d.text
    | "textDocument/didClose" =>
      if let some uri := str params ["textDocument", "uri"] then
        docs.modify (·.erase uri)
        publish out uri "" {}
    | "textDocument/hover" =>
      let uri := (str params ["textDocument", "uri"]).getD ""
      let l := (nat params ["position", "line"]).getD 0 + 1
      let c := (nat params ["position", "character"]).getD 0 + 1
      match (← docs.get)[uri]? with
      | some d =>
        let hits := d.hovers.filter fun (p, _) => contains d.text p l c
        let best := hits.foldl (fun acc h => match acc with
          | none => some h
          | some a => if size d.text h.1 < size d.text a.1 then some h else some a) none
        match best with
        | some (p, ty) =>
          let src := slice d.text p
          let src := if src.length > 60 then "" else s!"{src} : "
          respond out id (Json.mkObj [
            ("contents", Json.mkObj [("kind", "markdown"), ("value", s!"```kubus\n{src}{ty}\n```")]),
            ("range", jrange d.text p)])
        | none => respond out id Json.null
      | none => respond out id Json.null
    | _ =>
      -- unknown requests get an error; unknown notifications are ignored
      if !id.isNull then
        writeMessage out (Json.mkObj [("jsonrpc", "2.0"), ("id", id),
          ("error", Json.mkObj [("code", (-32601 : Int)), ("message", s!"unsupported: {method}")])])
  return 0

end Kubus.Lsp
