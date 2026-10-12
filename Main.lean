import Kubus

open Kubus

structure Driver where
  st : St := {}
  loaded : List System.FilePath := []

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
        modify fun dr => { dr with st := st' }
        if let some s := out then IO.println s
      | .error e => throw s!"{path}:{e}"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: kubus FILE.ktt..."
    return 2
  let mut drv : Driver := {}
  for a in args do
    match ← ((runFile a).run drv).run with
    | .ok ((), d) => drv := d
    | .error e =>
      IO.eprintln e
      return 1
  return 0
