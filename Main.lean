import Kubus

open Kubus

structure Driver where
  st : St := {}
  loaded : List System.FilePath := []
  violations : Nat := 0
  verbose : Bool := false

partial def runFile (path : System.FilePath) : StateT Driver (ExceptT String IO) Unit := do
  let path ← IO.FS.realPath path
  if (← get).loaded.contains path then return
  modify fun d => { d with loaded := path :: d.loaded }
  let src ← IO.FS.readFile path
  let decls ← match parseFile src with
    | .ok ds => pure ds
    | .error e => throw s!"{path}:{e}"
  let dir := path.parent.getD "."
  for d in decls do
    match d with
    | .importFile name _ =>
      let envPath := ((← IO.getEnv "KUBUS_PATH").getD "").splitOn ":" |>.filter (· != "")
      let searchPath : List System.FilePath := dir :: envPath.map System.FilePath.mk
      let mut found : Option System.FilePath := none
      for d in searchPath do
        if found.isNone && (← (d / (name ++ ".ktt")).pathExists) then found := some (d / (name ++ ".ktt"))
      match found with
      | some f => runFile f
      | none => throw s!"{path}: cannot find module {name} (searched {searchPath})"
    | _ =>
      match (checkDecl d).run (← get).st with
      | .ok (out, st') =>
        for v in st'.violations do IO.eprintln s!"{path}:{v}"
        if (← get).verbose then
          for v in st'.skips do IO.eprintln s!"{path}:{v}: skipped (budget)"
        modify fun dr => { dr with st := { st' with violations := #[], skips := #[] },
                                   violations := dr.violations + st'.violations.size }
        if let some s := out then IO.println s
      | .error e => throw s!"{path}:{e}"

def usage : String :=
  "usage: kubus [--selfcheck] [--budget N] [--verbose] FILE.ktt...\n" ++
  "  --selfcheck  check evaluator/checker invariants on every definition and #eval\n" ++
  "  --budget N   evaluation steps per self-check before it is skipped (default 1000000)\n" ++
  "  --verbose    list the self-checks that were skipped"

def main (args : List String) : IO UInt32 := do
  let mut drv : Driver := {}
  let mut files : Array String := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--selfcheck" :: r => drv := { drv with st.selfcheck := true }; rest := r
    | "--verbose" :: r => drv := { drv with verbose := true }; rest := r
    | "--budget" :: n :: r =>
      match n.toNat? with
      | some b => drv := { drv with st.budget := b }; rest := r
      | none => IO.eprintln usage; return 2
    | f :: r => files := files.push f; rest := r
    | [] => pure ()
  if files.isEmpty then
    IO.eprintln usage
    return 2
  for a in files do
    match ← ((runFile a).run drv).run with
    | .ok ((), d) => drv := d
    | .error e =>
      IO.eprintln e
      return 1
  if drv.st.selfcheck then
    let st := drv.st
    IO.eprintln s!"selfcheck: {st.nChecks} checks, {st.nSkipped} skipped (budget), {st.nGaps} re-checks skipped (no surface syntax), {drv.violations} violations"
    if drv.violations > 0 then return 1
  return 0
