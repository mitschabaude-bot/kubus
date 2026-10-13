import Kubus.Syntax

/-! # Lexer and recursive-descent parser -/

namespace Kubus

inductive TokK
  | ident (s : String)
  | num (n : Nat)
  | sym (s : String)
  | eof
  deriving BEq, Inhabited, Repr

structure Tok where
  k : TokK
  pos : Pos
  deriving Inhabited

def TokK.show : TokK → String
  | .ident s => s
  | .num n => toString n
  | .sym s => s
  | .eof => "end of file"

def symbols : List String :=
  [":=", "->", "=>", "/\\", "\\/", ".1", ".2", "(", ")", "[", "]", ",", ":", "\\", "~", "=", "|", "?",
   "*", "→", "λ", "×", "↦", "∧", "∨", "≡", "^", "{", "}", "@"]

def unicodeSyms : List Char := ['→', 'λ', '×', '↦', '∧', '∨', '≡']

def isIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '#' || (c.val > 127 && !unicodeSyms.contains c)

partial def lex (src : String) : Except String (Array Tok) := do
  let cs := src.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut line := 1
  let mut col := 1
  let mut out : Array Tok := #[]
  let startsWith (i : Nat) (s : String) : Bool :=
    let sc := s.toList
    sc.length + i ≤ n && (List.range sc.length).all fun k => cs[i + k]! == sc[k]!
  while i < n do
    let c := cs[i]!
    if c == '\n' then
      i := i + 1; line := line + 1; col := 1
    else if c.isWhitespace then
      i := i + 1; col := col + 1
    else if startsWith i "--" then
      while i < n && cs[i]! != '\n' do i := i + 1
    else if startsWith i "{-" then
      let mut depth := 0
      repeat
        if i ≥ n then break
        if startsWith i "{-" then depth := depth + 1; i := i + 2; col := col + 2
        else if startsWith i "-}" then
          depth := depth - 1; i := i + 2; col := col + 2
          if depth == 0 then break
        else
          if cs[i]! == '\n' then line := line + 1; col := 1 else col := col + 1
          i := i + 1
    else if c.isDigit then
      let start := i
      let mut v := 0
      while i < n && cs[i]!.isDigit do
        v := v * 10 + (cs[i]!.toNat - '0'.toNat); i := i + 1
      out := out.push ⟨.num v, ⟨line, col⟩⟩
      col := col + (i - start)
    else
      match symbols.find? (startsWith i ·) with
      | some s =>
        out := out.push ⟨.sym s, ⟨line, col⟩⟩
        i := i + s.length; col := col + s.length
      | none =>
        if isIdChar c then
          let start := i
          let mut s := ""
          while i < n && isIdChar cs[i]! do
            s := s.push cs[i]!; i := i + 1
          out := out.push ⟨.ident s, ⟨line, col⟩⟩
          col := col + (i - start)
        else throw s!"{line}:{col}: unexpected character '{c}'"
  return out.push ⟨.eof, ⟨line, col⟩⟩

abbrev P := ReaderT (Array Tok) (StateT Nat (Except String))

def peekTok : P Tok := do
  let ts ← read
  let i ← get
  return ts[i]?.getD ts.back!

def peek : P TokK := return (← peekTok).k
def peekAt (k : Nat) : P TokK := do
  let ts ← read
  let i ← get
  return (ts[i + k]?.getD ts.back!).k
def advance : P Unit := modify (· + 1)
def curPos : P Pos := return (← peekTok).pos

def perr {α} (msg : String) : P α := do
  let t ← peekTok
  throw s!"{t.pos.line}:{t.pos.col}: parse error: {msg} (at '{t.k.show}')"

def isSym (s : String) : P Bool := return (← peek) == .sym s
def isIdent (s : String) : P Bool := return (← peek) == .ident s

def expectSym (s : String) : P Unit := do
  if ← isSym s then advance else perr s!"expected '{s}'"

def expectOneOf (ss : List String) : P Unit := do
  match ← peek with
  | .sym s => if ss.contains s then advance else perr s!"expected one of {ss}"
  | _ => perr s!"expected one of {ss}"

def keywords : List String :=
  ["def", "data", "import", "let", "in", "fun", "comp", "hcomp", "fill", "Glue", "glue", "unglue",
   "Path", "PathP", "U", "I", "#eval", "#check"]

def ident : P String := do
  match ← peek with
  | .ident s => if keywords.contains s then perr "expected an identifier" else do advance; pure s
  | _ => perr "expected an identifier"

def isArrow : P Bool := return (← isSym "->") || (← isSym "→")
def isTimes : P Bool := return (← isSym "×") || (← isSym "*")
def isMapsto : P Bool := return (← isSym "->") || (← isSym "→") || (← isSym "↦") || (← isSym "=>")

mutual

partial def expr : P Raw := do
  if (← isSym "\\") || (← isSym "λ") || (← isIdent "fun") then
    advance
    let mut xs : Array (String × Option Raw) := #[]
    while !(← isMapsto) do
      if ← isSym "(" then
        advance
        let mut ys : Array String := #[]
        while !(← isSym ":") do ys := ys.push (← ident)
        advance
        let ty ← expr
        expectSym ")"
        for y in ys do xs := xs.push (y, some ty)
      else if ← isSym "{" then
        -- implicit binders `{x y}` or `{x y : A}`
        advance
        let mut ys : Array String := #[]
        while !(← isSym ":") && !(← isSym "}") do ys := ys.push (← ident)
        let ty ← if ← isSym ":" then do advance; some <$> expr else pure none
        expectSym "}"
        for y in ys do xs := xs.push (implName y, ty)
      else xs := xs.push (← ident, none)
    if xs.isEmpty then perr "expected a binder"
    advance
    let b ← expr
    return xs.foldr (fun (x, ty) b => .lam x ty b) b
  if ← isIdent "let" then
    advance
    let x ← ident
    let ty ← if ← isSym ":" then do advance; some <$> expr else pure none
    expectSym ":="
    let t ← expr
    if !(← isIdent "in") then perr "expected 'in'"
    advance
    let b ← expr
    return .letE x ty t b
  arrowExpr

/-- Try to parse telescope binders `(x y : A) (z : B)`; returns none (and backtracks) on failure. -/
partial def binderGroups? : P (Option (List Binder)) := do
  let start ← get
  let mut bs : Array Binder := #[]
  while (← isSym "(") || (← isSym "{") do
    let save ← get
    let impl ← isSym "{"
    advance
    let mut xs : Array String := #[]
    let mut ok := true
    repeat
      match ← peek with
      | .ident s =>
        if keywords.contains s then ok := false; break
        advance; xs := xs.push s
      | .sym ":" => break
      | _ => ok := false; break
    if !ok || xs.isEmpty || !(← isSym ":") then set save; break
    advance
    let ty ← expr
    expectSym (if impl then "}" else ")")
    for x in xs do bs := bs.push ⟨if impl then implName x else x, ty⟩
  if bs.isEmpty then set start; return none
  return some bs.toList

partial def arrowExpr : P Raw := do
  let start ← get
  if (← isSym "(") || (← isSym "{") then
    try
      match ← binderGroups? with
      | some bs =>
        if ← isArrow then
          advance
          let b ← arrowExpr
          return bs.foldr (fun bd b => .pi bd.name bd.ty b) b
        else if ← isTimes then
          advance
          let b ← arrowExpr
          return bs.foldr (fun bd b => .sigma bd.name bd.ty b) b
        else set start
      | none => set start
    catch _ => set start
  let lhs ← orExpr
  if ← isArrow then
    advance
    return .pi "_" lhs (← arrowExpr)
  if ← isTimes then
    advance
    return .sigma "_" lhs (← arrowExpr)
  return lhs

partial def orExpr : P Raw := do
  let mut l ← andExpr
  while (← isSym "\\/") || (← isSym "∨") do
    advance
    l := .ior l (← andExpr)
  return l

partial def andExpr : P Raw := do
  let mut l ← eqExpr
  while (← isSym "/\\") || (← isSym "∧") do
    advance
    l := .iand l (← eqExpr)
  return l

partial def eqExpr : P Raw := do
  let l ← appExpr
  if ← isSym "=" then
    advance
    match ← peek with
    | .num 0 => advance; return .ieq l false
    | .num 1 => advance; return .ieq l true
    | _ => perr "expected 0 or 1"
  return l

partial def sysE : P (List (Raw × Raw)) := do
  expectSym "["
  let mut out : Array (Raw × Raw) := #[]
  if ← isSym "]" then advance; return []
  repeat
    let k ← orExpr
    if !(← isMapsto) then perr "expected '->' in system"
    advance
    let v ← expr
    out := out.push (k, v)
    if ← isSym "," then advance else break
  expectSym "]"
  return out.toList

partial def isAtomStart : P Bool := do
  match ← peek with
  | .ident s => return !keywords.contains s || s == "U" || s == "I"
  | .num _ => return true
  | .sym s => return s == "(" || s == "?" || s == "~" || s == "@"
  | _ => return false

partial def appExpr : P Raw := do
  let pos ← curPos
  let head ← match ← peek with
    | .ident "comp" => do advance; let i ← ident; let a ← atom; let s ← sysE; let u ← atom; pure (Raw.comp i a s u)
    | .ident "hcomp" => do advance; let i ← ident; let a ← atom; let s ← sysE; let u ← atom; pure (Raw.hcomp i a s u)
    | .ident "fill" => do advance; let i ← ident; let a ← atom; let s ← sysE; let u ← atom; pure (Raw.fill i a s u)
    | .ident "Glue" => do advance; let a ← atom; let s ← sysE; pure (Raw.glueTy a s)
    | .ident "glue" => do advance; let s ← sysE; let a ← atom; pure (Raw.glue s a)
    | .ident "unglue" => do advance; pure (Raw.unglue (← atom))
    | .ident "Path" => do advance; let a ← atom; let u ← atom; let v ← atom; pure (Raw.path a u v)
    | .ident "PathP" => do advance; let a ← atom; let u ← atom; let v ← atom; pure (Raw.pathP a u v)
    | .ident "U" => do
      advance
      match ← peek with
      | .num n => advance; pure (Raw.univ n)
      | _ => pure (Raw.univ 0)
    | _ => atom
  let mut t := Raw.loc pos head
  while (← isAtomStart) || (← isSym "{") do
    if ← isSym "{" then
      -- implicit argument `{a}` or `{x := a}`
      advance
      let named ← match ← peek, ← peekAt 1 with
        | .ident x, .sym ":=" => do advance; advance; pure (some x)
        | _, _ => pure none
      let a ← expr
      expectSym "}"
      t := .iapp t named a
    else
      t := .app t (← atom)
  -- `a ≡ b` is notation for `Path _ a b`
  if ← isSym "≡" then
    advance
    let rhs ← appExpr
    return .loc pos (.path .hole t rhs)
  return match t with
    | .loc .. => t
    | _ => .loc pos t

partial def atom : P Raw := do
  let pos ← curPos
  let mut t ← primary
  while (← isSym ".1") || (← isSym ".2") do
    if ← isSym ".1" then t := .fst t else t := .snd t
    advance
  return .loc pos t

partial def primary : P Raw := do
  match ← peek with
  | .ident "U" => advance; return .univ 0
  | .ident "I" => advance; return .intervalTy
  | .ident _ =>
    let x ← ident
    if ← isSym "^" then
      advance
      match ← peek with
      | .num k => advance; return .lift x k
      | _ => perr "expected a number after '^'"
    return .var x
  | .num 0 => advance; return .izero
  | .num 1 => advance; return .ione
  | .num _ => perr "only 0 and 1 are numerals"
  | .sym "?" => advance; return .hole
  | .sym "@" => advance; return .explicit (← ident)
  | .sym "~" => advance; return .ineg (← atom)
  | .sym "(" =>
    advance
    let e ← expr
    if ← isSym "," then
      advance
      let e2 ← expr
      expectSym ")"
      return .pair e e2
    if ← isSym ":" then
      advance
      let ty ← expr
      expectSym ")"
      return .ann e ty
    expectSym ")"
    return e
  | _ => perr "expected an expression"

end

mutual
partial def patAtom : P Pat := do
  let pos ← curPos
  match ← peek with
  | .ident _ => return .var (← ident) pos
  | .sym "(" =>
    advance
    let p ← pattern
    expectSym ")"
    return p
  | _ => perr "expected a pattern"

/-- `c p1 ... pn`, a variable, or `_` -/
partial def pattern : P Pat := do
  let pos ← curPos
  let h ← patAtom
  let mut args : Array Pat := #[]
  while (← isSym "(") || (match ← peek with | .ident s => !keywords.contains s | _ => false) do
    args := args.push (← patAtom)
  if args.isEmpty then return h
  match h with
  | .var c _ => return .con c args.toList pos
  | _ => throw s!"{pos.line}:{pos.col}: parse error: a constructor pattern must start with a constructor"
end

partial def binders : P (List Binder) := do
  match ← binderGroups? with
  | some bs => pure bs
  | none => pure []

def isDeclStart : P Bool := do
  match ← peek with
  | .ident s => return ["def", "data", "import", "#eval", "#check"].contains s
  | .eof => return true
  | _ => return false

partial def decl : P Decl := do
  let pos ← curPos
  match ← peek with
  | .ident "def" =>
    advance
    let name ← ident
    let ps ← binders
    -- `def x (params) := t` infers the type
    if ← isSym ":=" then
      advance
      return .defn name ps .hole (← expr) pos
    expectSym ":"
    let ty ← expr
    if ← isSym ":=" then
      advance
      return .defn name ps ty (← expr) pos
    let mut cls : Array Clause' := #[]
    while ← isSym "|" do
      let cpos ← curPos
      advance
      let mut ps : Array Pat := #[← pattern]
      while ← isSym "," do
        advance
        ps := ps.push (← pattern)
      if !(← isMapsto) then perr "expected '=>' after the patterns"
      advance
      cls := cls.push ⟨ps.toList, ← expr, cpos⟩
    if cls.isEmpty && !(← isDeclStart) then perr "expected ':=' or pattern-matching clauses"
    return .defSplit name ps ty cls.toList pos
  | .ident "data" =>
    advance
    let name ← ident
    let ps ← binders
    expectSym ":"
    let lvl ← match ← expr with
      | .univ l | .loc _ (.univ l) => pure l
      | _ => perr "the type of a data type must be a universe"
    -- a data type without constructors may omit `:=`
    if ← isDeclStart then return .data name ps lvl [] pos
    expectSym ":="
    if ← isDeclStart then return .data name ps lvl [] pos
    if ← isSym "|" then advance
    let mut cs : Array CtorDecl := #[]
    repeat
      let cpos ← curPos
      let c ← ident
      let args ← binders
      let sys ← if ← isSym "[" then sysE else pure []
      cs := cs.push ⟨c, args, sys, cpos⟩
      if ← isSym "|" then advance else break
    return .data name ps lvl cs.toList pos
  | .ident "import" =>
    advance
    return .importFile (← ident) pos
  | .ident "#eval" => advance; return .eval (← expr) pos
  | .ident "#check" => advance; return .check (← expr) pos
  | _ => perr "expected a declaration"

partial def decls : P (List Decl) := do
  let mut out : Array Decl := #[]
  while (← peek) != .eof do
    let d ← decl
    if !(← isDeclStart) then perr "unexpected token after declaration"
    out := out.push d
  return out.toList

def parseFile (src : String) : Except String (List Decl) := do
  let toks ← lex src
  let (ds, _) ← (decls.run toks).run 0
  return ds

/-- Parse a single term (used by the self-checks to re-check printed normal forms). -/
def parseTerm (src : String) : Except String Raw := do
  let toks ← lex src
  let p : P Raw := do
    let t ← expr
    if (← peek) != .eof then perr "unexpected token after term"
    pure t
  let (t, _) ← (p.run toks).run 0
  return t

end Kubus
