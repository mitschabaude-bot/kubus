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

partial def runFile (path : System.FilePath) (top : Bool := true) : StateT Driver (ExceptT String IO) Unit := do
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
      | .error e => throw s!"{path}:{e}"

def usage : String :=
  "usage: kubus [--selfcheck | --selfcheck-main] [--budget N] [--verbose] FILE.ktt...\n" ++
  "  --selfcheck  check evaluator/checker invariants on every definition and #eval\n" ++
  "  --selfcheck-main  the same, but only for the given files, not their imports\n" ++
  "  --budget N   evaluation steps per self-check before it is skipped (default 1000000)\n" ++
  "  --verbose    list the self-checks that were skipped\n" ++
  "  --kernel     also check every definition with the certified KubusCore kernel"

def main (args : List String) : IO UInt32 := do
  let mut drv : Driver := {}
  let mut files : Array String := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--selfcheck" :: r => drv := { drv with selfcheck := true }; rest := r
    | "--selfcheck-main" :: r => drv := { drv with selfcheck := true, selfcheckImports := false }; rest := r
    | "--verbose" :: r => drv := { drv with verbose := true }; rest := r
    | "--kernel" :: r => drv := { drv with kernel := some {} }; rest := r
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
  if drv.selfcheck then
    let st := drv.st
    IO.eprintln s!"selfcheck: {st.nChecks} checks, {st.nSkipped} skipped (budget), {st.nGaps} re-checks skipped (no surface syntax), {drv.violations} violations"
    if drv.violations > 0 then return 1
  if let some ks := drv.kernel then
    IO.println s!"kernel: {ks.certified} certified, {ks.skipped.size - ks.rejected} skipped, {ks.rejected} rejected"
    if ks.rejected > 0 then return 1
  return 0
