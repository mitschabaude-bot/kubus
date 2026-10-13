import Kubus
import Kubus.Bridge

open Kubus

structure Driver where
  st : St := {}
  loaded : List System.FilePath := []
  violations : Nat := 0
  verbose : Bool := false
  selfcheck : Bool := false
  /-- self-check imported files too -/
  selfcheckImports : Bool := true
  /-- `--kernel`: check definitions with the certified kernel -/
  kernel : Option Bridge.State := none

abbrev DM := StateT Driver (ExceptT String IO)

mutual
partial def runFile (path : System.FilePath) (top : Bool := true) : DM Unit := do
  let path ← IO.FS.realPath path
  if (← get).loaded.contains path then return
  modify fun d => { d with loaded := path :: d.loaded }
  let src ← IO.FS.readFile path
  let decls ← match parseFile src with
    | .ok ds => pure ds
    | .error e => throw s!"{path}:{e}"
  runDecls path.toString (path.parent.getD ".") decls top

/-- Check declarations; `src` names their source in messages, `dir` is searched for imports. -/
partial def runDecls (path : String) (dir : System.FilePath) (decls : List Decl) (top : Bool) : DM Unit := do
  for d in decls do
    match d with
    | .importFile name _ =>
      let envPath := ((← IO.getEnv "KUBUS_PATH").getD "").splitOn ":" |>.filter (· != "")
      let searchPath : List System.FilePath := dir :: envPath.map System.FilePath.mk
      let mut found : Option System.FilePath := none
      for d in searchPath do
        if found.isNone && (← (d / (name ++ ".ktt")).pathExists) then found := some (d / (name ++ ".ktt"))
      match found with
      | some f => runFile f false
      | none => throw s!"{path}: cannot find module {name} (searched {searchPath})"
    | _ =>
      let dr ← get
      let st := { dr.st with selfcheck := dr.selfcheck && (top || dr.selfcheckImports) }
      match (checkDecl d).run st with
      | .ok (out, st') =>
        for v in st'.violations do IO.eprintln s!"{path}:{v}"
        if (← get).verbose then
          for v in st'.skips do IO.eprintln s!"{path}:{v}: skipped (budget)"
        modify fun dr => { dr with st := { st' with violations := #[], skips := #[] },
                                   violations := dr.violations + st'.violations.size }
        if let some s := out then IO.println s
        if let some ks := (← get).kernel then
          let name? := match d with
            | .defn n .. | .defSplit n .. => some n
            | _ => none
          if let some n := name? then
            let (msgs, ks') := (Bridge.addGlobal st'.globals n 0).run ks
            for m in msgs do IO.println m
            modify fun dr => { dr with kernel := some ks' }
          if let .data n .. := d then
            let (msgs, ks') := (Bridge.addData st'.globals n 0).run ks
            for m in msgs do IO.println m
            modify fun dr => { dr with kernel := some ks' }
      | .error e => throw s!"{path}:{e}"
end

def isEofError (e : String) : Bool := (e.splitOn "(at 'end of file')").length > 1

/-- `kubus --interactive`: read declarations, `#eval`/`#check` commands and terms (evaluated)
from standard input. Declarations by pattern matching and data types end with an empty line. -/
partial def repl : DM Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut buf := ""
  let mut n := 0
  repeat
    stdout.putStr (if buf.isEmpty then "kubus> " else "   ...> ")
    stdout.flush
    let line ← stdin.getLine
    if line.isEmpty then break
    let l := line.trimAscii.toString
    if buf.isEmpty then
      if l.isEmpty then continue
      if l == ":q" || l == ":quit" then break
      if l == ":help" then
        IO.println "declarations (def, data, import), #eval t, #check t, or a term t (evaluated); :load FILE, :q"
        continue
      if l.startsWith ":load " then
        try runFile ((l.drop 6).trimAscii.toString) catch e => IO.eprintln e
        continue
    let blank := l.isEmpty
    buf := buf ++ line
    let isDecl := ["def", "data", "import", "#eval", "#check"].any (buf.trimAsciiStart.toString.startsWith ·)
    let parsed := if isDecl then parseFile buf else (parseTerm buf).map fun t => [Decl.eval t ⟨1, 1⟩]
    match parsed with
    | .error e =>
      if isEofError e && !blank then continue
      IO.eprintln s!"<input>:{e}"
      buf := ""
    | .ok decls =>
      let multiline := decls.any fun | .defSplit .. | .data .. => true | _ => false
      if multiline && !blank then continue
      n := n + 1
      try runDecls s!"<input {n}>" "." decls true catch e => IO.eprintln e
      buf := ""

def usage : String :=
  "usage: kubus [--selfcheck | --selfcheck-main] [--budget N] [--verbose] [--interactive] FILE.ktt...\n" ++
  "  --interactive  after loading the files, read declarations and terms from standard input\n" ++
  "  --selfcheck  check evaluator/checker invariants on every definition and #eval\n" ++
  "  --selfcheck-main  the same, but only for the given files, not their imports\n" ++
  "  --budget N   evaluation steps per self-check before it is skipped (default 1000000)\n" ++
  "  --verbose    list the self-checks that were skipped\n" ++
  "  --kernel     also check every definition with the certified KubusCore kernel"

def main (args : List String) : IO UInt32 := do
  let mut drv : Driver := {}
  let mut files : Array String := #[]
  let mut interactive := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--selfcheck" :: r => drv := { drv with selfcheck := true }; rest := r
    | "--selfcheck-main" :: r => drv := { drv with selfcheck := true, selfcheckImports := false }; rest := r
    | "--verbose" :: r => drv := { drv with verbose := true }; rest := r
    | "--kernel" :: r => drv := { drv with kernel := some {} }; rest := r
    | "--interactive" :: r => interactive := true; rest := r
    | "--budget" :: n :: r =>
      match n.toNat? with
      | some b => drv := { drv with st.budget := b }; rest := r
      | none => IO.eprintln usage; return 2
    | f :: r => files := files.push f; rest := r
    | [] => pure ()
  if files.isEmpty && !interactive then
    IO.eprintln usage
    return 2
  for a in files do
    match ← ((runFile a).run drv).run with
    | .ok ((), d) => drv := d
    | .error e =>
      IO.eprintln e
      return 1
  if interactive then
    match ← (repl.run drv).run with
    | .ok ((), d) => drv := d
    | .error e => IO.eprintln e; return 1
  if drv.selfcheck then
    let st := drv.st
    IO.eprintln s!"selfcheck: {st.nChecks} checks, {st.nSkipped} skipped (budget), {st.nGaps} re-checks skipped (no surface syntax), {drv.violations} violations"
    if drv.violations > 0 then return 1
  if let some ks := drv.kernel then
    IO.println s!"kernel: {ks.certified} certified, {ks.skipped.size - ks.rejected} skipped, {ks.rejected} rejected"
    if ks.rejected > 0 then return 1
  return 0
