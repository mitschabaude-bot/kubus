import KubusCore.Kernel.Ctx
import Std.Data.HashMap

/-!
# Kernel: result types, the recursion record, and helpers

Every kernel function returns a derivation of a judgment of the specification
(`KubusCore/Rules.lean`). The kernel's functions are mutually recursive; to keep each of them
a separate definition, they take a record `Rec S` of the recursive calls, and the knot is
tied by recursion on a fuel parameter (`Kernel.Main`).
-/

namespace KubusCore.Kernel

/-- An inferred type `ty : U lvl` of `t`. -/
structure Inf (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (t : Tm) where
  ty : Tm
  lvl : Nat
  hty : HasTy S Ψ Φ Γ ty (.univ lvl)
  htm : HasTy S Ψ Φ Γ t ty

/-- A reduct `tm` of `t` at type `A`. -/
structure Red (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (t A : Tm) where
  tm : Tm
  eq : EqTm S Ψ Φ Γ t tm A

/-! ## Memoization

Results of the kernel's functions are cached with their derivations, keyed by the context
and the terms. A cached derivation is reused only after the keys are compared for equality,
which yields the proof to transport it along. Equality of terms is decided structurally, with
the pointer-equality shortcut of Lean core's `withPtrEq` (logically just the structural
comparison). -/

/-- Equality of terms, deciding with a pointer-equality shortcut at every node (terms built by
the kernel share most of their subterms), and structurally otherwise. -/
def tmDec : (a b : Tm) → Decidable (a = b)
  | .var x0, .var y0 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .const x0, .const y0 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .univ x0, .univ y0 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .pi x0 x1, .pi y0 y1 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .lam x0 x1, .lam y0 y1 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .app x0 x1, .app y0 y1 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .sigma x0 x1, .sigma y0 y1 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .pair x0 x1, .pair y0 y1 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .fst x0, .fst y0 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .snd x0, .snd y0 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .path x0 x1 x2, .path y0 y1 y2 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .plam x0, .plam y0 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .papp x0 x1, .papp y0 y1 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .ipi x0, .ipi y0 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .split x0 x1 x2 x3, .split y0 y1 y2 y3 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match decEq x2 y2 with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          match withPtrEqDecEq x3 y3 (fun _ => tmDec x3 y3) with
          | isFalse h => isFalse (fun e => by cases e; exact h rfl)
          | isTrue h3 =>
            isTrue (by subst h0; subst h1; subst h2; subst h3; rfl)
  | .transp x0 x1 x2, .transp y0 y1 y2 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .hcomp x0 x1 x2 x3, .hcomp y0 y1 y2 y3 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          match withPtrEqDecEq x3 y3 (fun _ => tmDec x3 y3) with
          | isFalse h => isFalse (fun e => by cases e; exact h rfl)
          | isTrue h3 =>
            isTrue (by subst h0; subst h1; subst h2; subst h3; rfl)
  | .glue x0 x1 x2 x3, .glue y0 y1 y2 y3 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          match withPtrEqDecEq x3 y3 (fun _ => tmDec x3 y3) with
          | isFalse h => isFalse (fun e => by cases e; exact h rfl)
          | isTrue h3 =>
            isTrue (by subst h0; subst h1; subst h2; subst h3; rfl)
  | .glueEl x0 x1 x2 x3, .glueEl y0 y1 y2 y3 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          match withPtrEqDecEq x3 y3 (fun _ => tmDec x3 y3) with
          | isFalse h => isFalse (fun e => by cases e; exact h rfl)
          | isTrue h3 =>
            isTrue (by subst h0; subst h1; subst h2; subst h3; rfl)
  | .unglue x0 x1 x2, .unglue y0 y1 y2 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .tcons x0 x1, .tcons y0 y1 =>
    match withPtrEqDecEq x0 y0 (fun _ => tmDec x0 y0) with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .data x0 x1, .data y0 y1 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .con x0 x1 x2 x3 x4, .con y0 y1 y2 y3 y4 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          match withPtrEqDecEq x3 y3 (fun _ => tmDec x3 y3) with
          | isFalse h => isFalse (fun e => by cases e; exact h rfl)
          | isTrue h3 =>
            match decEq x4 y4 with
            | isFalse h => isFalse (fun e => by cases e; exact h rfl)
            | isTrue h4 =>
              isTrue (by subst h0; subst h1; subst h2; subst h3; subst h4; rfl)
  | .elim x0 x1 x2 x3 x4, .elim y0 y1 y2 y3 y4 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    | isTrue h0 =>
      match withPtrEqDecEq x1 y1 (fun _ => tmDec x1 y1) with
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
      | isTrue h1 =>
        match withPtrEqDecEq x2 y2 (fun _ => tmDec x2 y2) with
        | isFalse h => isFalse (fun e => by cases e; exact h rfl)
        | isTrue h2 =>
          match withPtrEqDecEq x3 y3 (fun _ => tmDec x3 y3) with
          | isFalse h => isFalse (fun e => by cases e; exact h rfl)
          | isTrue h3 =>
            match withPtrEqDecEq x4 y4 (fun _ => tmDec x4 y4) with
            | isFalse h => isFalse (fun e => by cases e; exact h rfl)
            | isTrue h4 =>
              isTrue (by subst h0; subst h1; subst h2; subst h3; subst h4; rfl)
  | .abort, .abort => isTrue rfl
  | .tnil, .tnil => isTrue rfl
  | a, b => decEq a b

/-- Equality of terms, with pointer-equality shortcuts. -/
def tmEq (a b : Tm) : Bool := @decide (a = b) (withPtrEqDecEq a b (fun _ => tmDec a b))

theorem tmEq_sound {a b : Tm} (h : tmEq a b = true) : a = b :=
  @of_decide_eq_true _ (withPtrEqDecEq a b (fun _ => tmDec a b)) h

def ctxEqAux : Ctx → Ctx → Bool
  | [], [] => true
  | A :: Γ, B :: Δ => tmEq A B && withPtrEq Γ Δ (fun _ => decide (Γ = Δ)) (by intro h; simp [h])
  | _, _ => false

/-- Equality of contexts, with pointer-equality shortcuts for the entries and the tails. -/
def ctxEq (Γ Δ : Ctx) : Bool := withPtrEq Γ Δ (fun _ => ctxEqAux Γ Δ) (by
  intro h; subst h
  cases Γ with
  | nil => rfl
  | cons A Γ => simp [ctxEqAux, tmEq, withPtrEq])

theorem ctxEq_sound {Γ Δ : Ctx} (h : ctxEq Γ Δ = true) : Γ = Δ := by
  simp only [ctxEq, withPtrEq] at h
  match Γ, Δ, h with
  | [], [], _ => rfl
  | A :: Γ, B :: Δ, h =>
    simp only [ctxEqAux, Bool.and_eq_true, withPtrEq, decide_eq_true_eq] at h
    rw [tmEq_sound h.1, h.2]
  | [], _ :: _, h => simp [ctxEqAux] at h
  | _ :: _, [], h => simp [ctxEqAux] at h

/-- Equality of interval expressions, with a pointer-equality shortcut. -/
def iEq (a b : I) : Bool := withPtrEq a b (fun _ => decide (a = b)) (by intro h; simp [h])

theorem iEq_sound {a b : I} (h : iEq a b = true) : a = b := by
  simp only [iEq, withPtrEq, decide_eq_true_eq] at h; exact h

/-- A hash of an interval expression. -/
def _root_.KubusCore.I.hashI : I → UInt64
  | .zero => 31
  | .one => 32
  | .var i => mixHash 33 (hash i)
  | .neg r => mixHash 34 r.hashI
  | .and r s => mixHash 35 (mixHash r.hashI s.hashI)
  | .or r s => mixHash 36 (mixHash r.hashI s.hashI)

/-- A hash of the top of a term (a few levels deep), for the cache buckets. -/
def Tm.hashTop : Nat → Tm → UInt64
  | 0, _ => 7
  | n + 1, t =>
    let h := Tm.hashTop n
    match t with
    | .var x => mixHash 1 (hash x)
    | .const k => mixHash 2 (hash k)
    | .univ l => mixHash 3 (hash l)
    | .pi A B => mixHash 4 (mixHash (h A) (h B))
    | .lam A b => mixHash 5 (mixHash (h A) (h b))
    | .app f a => mixHash 6 (mixHash (h f) (h a))
    | .sigma A B => mixHash 7 (mixHash (h A) (h B))
    | .pair a b => mixHash 8 (mixHash (h a) (h b))
    | .fst p => mixHash 9 (h p)
    | .snd p => mixHash 10 (h p)
    | .path A a b => mixHash 11 (mixHash (h A) (mixHash (h a) (h b)))
    | .plam b => mixHash 12 (h b)
    | .papp p r => mixHash 13 (mixHash (h p) r.hashI)
    | .ipi A => mixHash 14 (h A)
    | .split φ t ψ u => mixHash 15 (mixHash (mixHash φ.hashI ψ.hashI) (mixHash (h t) (h u)))
    | .abort => 16
    | .transp A φ a => mixHash 17 (mixHash φ.hashI (mixHash (h A) (h a)))
    | .hcomp A φ u a => mixHash 18 (mixHash φ.hashI (mixHash (h A) (mixHash (h u) (h a))))
    | .glue A φ T e => mixHash 19 <| mixHash φ.hashI <| (mixHash (h A) (mixHash (h T) (h e)))
    | .glueEl φ e t a => mixHash 20 <| mixHash φ.hashI <| (mixHash (h e) (mixHash (h t) (h a)))
    | .unglue φ e g => mixHash 21 <| mixHash φ.hashI <| (mixHash (h e) (h g))
    | .tnil => 22
    | .tcons t ts => mixHash 23 (mixHash (h t) (h ts))
    | .data d ps => mixHash 24 (mixHash (hash d) (h ps))
    | .con d c ps as _ => mixHash 25 (mixHash (hash d) (mixHash (hash c) (mixHash (h ps) (h as))))
    | .elim d ps P bs t => mixHash 26 (mixHash (hash d) (mixHash (h P) (mixHash (h bs) (h t))))

def keyOf (Ψ : Nat) (Γ : Ctx) (ts : List Tm) : UInt64 :=
  ts.foldl (fun acc t => mixHash acc (Tm.hashTop 4 t)) (mixHash (hash Ψ) (hash Γ.length))

/-- A cached result under the restriction `Φ` (with its faces). -/
structure CVar (S : Sig) (F : Sig → Nat → I → Ctx → List Tm → Type) (Ψ : Nat) (Γ : Ctx)
    (ts : List Tm) where
  Φ : I
  v : F S Ψ Φ Γ ts
  fs : List I.Face
  hfs : fs = Φ.faces

/-- The cached results for the terms `ts` in the context `Ψ; Γ`, under various restrictions. -/
structure CEntry (S : Sig) (F : Sig → Nat → I → Ctx → List Tm → Type) where
  Ψ : Nat
  Γ : Ctx
  ts : List Tm
  vs : List (CVar S F Ψ Γ ts)

/-- Moving a cached result to a stronger restriction (`none`: not reusable there). -/
abbrev Restr (S : Sig) (F : Sig → Nat → I → Ctx → List Tm → Type) :=
  ∀ {Ψ : Nat} {Φ Φ' : I} {Γ : Ctx} {ts : List Tm}, Φ'.Scoped Ψ → I.Entails Φ' Φ →
    F S Ψ Φ Γ ts → Option (F S Ψ Φ' Γ ts)

def termsEq : List Tm → List Tm → Bool
  | [], [] => true
  | a :: as, b :: bs => tmEq a b && termsEq as bs
  | _, _ => false

theorem termsEq_sound : ∀ {as bs : List Tm}, termsEq as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [termsEq, Bool.and_eq_true] at h
    rw [tmEq_sound h.1, termsEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [termsEq] at h

abbrev Table (S : Sig) (F : Sig → Nat → I → Ctx → List Tm → Type) :=
  Std.HashMap UInt64 (List (CEntry S F))

/-- The entry for `ts` in `Ψ; Γ`, if any, with the equations that identify its keys. -/
def Table.entry? {S F} (tab : Table S F) (Ψ : Nat) (Γ : Ctx) (ts : List Tm) :
    Option (List (CVar S F Ψ Γ ts)) :=
  (tab.getD (keyOf Ψ Γ ts) []).findSome? fun ⟨Ψ', Γ', ts', vs⟩ =>
    if h : Ψ' = Ψ ∧ termsEq ts' ts = true ∧ ctxEq Γ' Γ = true then
      some (by
        obtain ⟨h1, h3, h4⟩ := h
        rw [← h1, ← termsEq_sound h3, ← ctxEq_sound h4]; exact vs)
    else none

/-- A cached result for `ts` in `Ψ; Φ; Γ` (`fs` are the faces of `Φ`): one for the same
restriction, or one for a weaker restriction moved along `res`. -/
def Table.find? {S F} (tab : Table S F) (Ψ : Nat) (Φ : I) (Γ : Ctx) (ts : List Tm)
    (fs : List I.Face) (hfs : fs = Φ.faces) (hsc : Φ.Scoped Ψ) (res : Restr S F) :
    Option (F S Ψ Φ Γ ts) := do
  let vs ← tab.entry? Ψ Γ ts
  vs.findSome? fun ⟨Φ', v, fs', hfs'⟩ =>
    if h2 : iEq Φ' Φ = true then some (iEq_sound h2 ▸ v)
    else if he : (fs.all fun c => fs'.any fun d => d.all (c.contains ·)) = true then
      res hsc (by show I.entails Φ Φ' = true; unfold I.entails; rw [← hfs, ← hfs']; exact he) v
    else none

def Table.insert {S F} (tab : Table S F) (Ψ : Nat) (Φ : I) (Γ : Ctx) (ts : List Tm)
    (fs : List I.Face) (hfs : fs = Φ.faces) (v : F S Ψ Φ Γ ts) : Table S F :=
  let k := keyOf Ψ Γ ts
  let var : CVar S F Ψ Γ ts := ⟨Φ, v, fs, hfs⟩
  -- one pass over the bucket: the variants for these keys, and the other entries
  let (vs, others) := (tab.getD k []).foldr (init := (([] : List (CVar S F Ψ Γ ts)), ([] : List (CEntry S F))))
    fun e (vs, others) =>
      let ⟨Ψ', Γ', ts', evs⟩ := e
      if h : Ψ' = Ψ ∧ termsEq ts' ts = true ∧ ctxEq Γ' Γ = true then
        (by obtain ⟨h1, h3, h4⟩ := h; rw [← h1, ← termsEq_sound h3, ← ctxEq_sound h4]; exact evs,
          others)
      else (vs, e :: others)
  Std.HashMap.insert tab k (⟨Ψ, Γ, ts, var :: vs.take 31⟩ :: others.take 15)

/-- The cached judgments. -/
def InfF : Sig → Nat → I → Ctx → List Tm → Type
  | S, Ψ, Φ, Γ, [t] => Inf S Ψ Φ Γ t
  | _, _, _, _, _ => PUnit

def WhiF : Sig → Nat → I → Ctx → List Tm → Type
  | S, Ψ, Φ, Γ, [t] => (i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty
  | _, _, _, _, _ => PUnit

def WhF : Sig → Nat → I → Ctx → List Tm → Type
  | S, Ψ, Φ, Γ, [t, A] => Red S Ψ Φ Γ t A
  | _, _, _, _, _ => PUnit

def ChkF : Sig → Nat → I → Ctx → List Tm → Type
  | S, Ψ, Φ, Γ, [t, A] => PLift (HasTy S Ψ Φ Γ t A)
  | _, _, _, _, _ => PUnit

def ConvF : Sig → Nat → I → Ctx → List Tm → Type
  | S, Ψ, Φ, Γ, [A, t, u] => PLift (EqTm S Ψ Φ Γ t u A)
  | _, _, _, _, _ => PUnit

/-- Weak-head normal forms that stay normal under any stronger restriction. -/
def _root_.KubusCore.Tm.rigid : Tm → Bool
  | .univ _ | .pi .. | .sigma .. | .path .. | .ipi _ | .lam .. | .pair .. | .plam _
  | .data .. | .con _ _ _ _ [] => true
  | _ => false

def InfF.restr {S : Sig} : Restr S InfF := fun {Ψ Φ Φ' Γ ts} hs he v =>
  match ts, v with
  | [_], i => some ⟨i.ty, i.lvl, HasTy.restrict hs he i.hty, HasTy.restrict hs he i.htm⟩
  | [], _ | _ :: _ :: _, _ => none

def ChkF.restr {S : Sig} : Restr S ChkF := fun {Ψ Φ Φ' Γ ts} hs he v =>
  match ts, v with
  | [_, _], ⟨h⟩ => some ⟨HasTy.restrict hs he h⟩
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => none

def ConvF.restr {S : Sig} : Restr S ConvF := fun {Ψ Φ Φ' Γ ts} hs he v =>
  match ts, v with
  | [_, _, _], ⟨h⟩ => some ⟨EqTm.restrict hs he h⟩
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => none

def WhF.restr {S : Sig} : Restr S WhF := fun {Ψ Φ Φ' Γ ts} hs he v =>
  match ts, v with
  | [_, _], r => if r.tm.rigid then some ⟨r.tm, EqTm.restrict hs he r.eq⟩ else none
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => none

def WhiF.restr {S : Sig} : Restr S WhiF := fun {Ψ Φ Φ' Γ ts} hs he v =>
  match ts, v with
  | [_], ⟨i, r⟩ =>
    if r.tm.rigid then
      some ⟨⟨i.ty, i.lvl, HasTy.restrict hs he i.hty, HasTy.restrict hs he i.htm⟩,
        ⟨r.tm, EqTm.restrict hs he r.eq⟩⟩
    else none
  | [], _ | _ :: _ :: _, _ => none

def noRestr {S : Sig} {F} : Restr S F := fun _ _ _ => none

/-- The premises of `elim d ps (x. P) bs _` other than the target. -/
structure ElimInfo (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (d : Nat) (ps P bs : Tm) where
  D : DataDecl
  hS : S[d]? = some (.data D)
  m : Nat
  hps : ps = Tm.ofList ps.toList
  hD : HasTy S Ψ Φ Γ (.data d ps) (.univ D.level)
  hP : HasTy S Ψ Φ (.data d ps :: Γ) P (.univ m)
  hbs : bs = Tm.ofList bs.toList
  hlen : bs.toList.length = D.ctors.length
  hbr : ∀ (c : Nat) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
    HasTy S Ψ Φ Γ b (D.branchTy d c C ps P)
  hbnd : ∀ (c : Nat) (C : Ctor) (b : Tm) (k : Nat) (ψ : I) (e : Tm), D.ctors[c]? = some C →
    bs.toList[c]? = some b → C.bnd[k]? = some (ψ, e) →
    EqTm S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)

def ElimInfo.typing {Ψ Φ Γ d ps P bs t} (i : ElimInfo S Ψ Φ Γ d ps P bs)
    (ht : HasTy S Ψ Φ Γ t (.data d ps)) : HasTy S Ψ Φ Γ (.elim d ps P bs t) (P.inst t) :=
  HasTy.elim i.hS i.hps i.hD i.hP i.hbs i.hlen i.hbr i.hbnd ht

def ElimF : Sig → Nat → I → Ctx → List Tm → Type
  | S, Ψ, Φ, Γ, [.data d ps, P, bs] => ElimInfo S Ψ Φ Γ d ps P bs
  | _, _, _, _, _ => PUnit

structure Cache (S : Sig) where
  inf : Table S InfF := {}
  whi : Table S WhiF := {}
  wh : Table S WhF := {}
  chk : Table S ChkF := {}
  conv : Table S ConvF := {}
  elim : Table S ElimF := {}
  /-- comparisons that failed (no proof needed), so that alternatives tried after a failure
  do not repeat it -/
  convFail : Table S (fun _ _ _ _ _ => PUnit) := {}

/-- The kernel monad: errors, and the cache of judgments over the signature `S`. -/
abbrev K (S : Sig) := EStateM String (Cache S)

/-- Errors of pure computations. -/
instance {S : Sig} : MonadLift (Except String) (K S) where
  monadLift
    | .ok a => pure a
    | .error e => throw e

/-- The recursive calls of the kernel. -/
structure Rec (S : Sig) where
  infer : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t : Tm) → K S (Inf S Ψ Φ Γ t)
  check : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t A : Tm) → (l : Nat) → HasTy S Ψ Φ Γ A (.univ l) →
    K S (PLift (HasTy S Ψ Φ Γ t A))
  /-- weak-head normal form at a given type -/
  whnf : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t A : Tm) → (l : Nat) → HasTy S Ψ Φ Γ A (.univ l) →
    HasTy S Ψ Φ Γ t A → K S (Red S Ψ Φ Γ t A)
  /-- infer the type and compute the weak-head normal form -/
  whnfI : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t : Tm) → K S ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty)
  conv : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (A : Tm) → (l : Nat) → HasTy S Ψ Φ Γ A (.univ l) →
    (t u : Tm) → HasTy S Ψ Φ Γ t A → HasTy S Ψ Φ Γ u A → K S (PLift (EqTm S Ψ Φ Γ t u A))
  /-- compare two neutral terms in weak-head normal form, inferring the type of the first -/
  convNe : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t u : Tm) →
    K S ((i : Inf S Ψ Φ Γ t) × PLift (EqTm S Ψ Φ Γ t u i.ty))

def Rec.bot (S : Sig) : Rec S where
  infer := fun _ _ => throw "kernel: out of fuel"
  check := fun _ _ _ _ _ => throw "kernel: out of fuel"
  whnf := fun _ _ _ _ _ _ => throw "kernel: out of fuel"
  whnfI := fun _ _ => throw "kernel: out of fuel"
  conv := fun _ _ _ _ _ _ _ _ => throw "kernel: out of fuel"
  convNe := fun _ _ _ => throw "kernel: out of fuel"

/-! ## Printing (error messages only) -/

def I.pp : I → String
  | .zero => "0"
  | .one => "1"
  | .var i => s!"i{i}"
  | .neg r => s!"~{I.pp r}"
  | .and r s => s!"({I.pp r} ∧ {I.pp s})"
  | .or r s => s!"({I.pp r} ∨ {I.pp s})"

/-- Print `t`, eliding subterms below depth `n`. -/
def Tm.ppD : Nat → Tm → String
  | 0, _ => "…"
  | n + 1, .var x => s!"x{x}"
  | n + 1, .const k => s!"c{k}"
  | n + 1, .univ l => s!"U{l}"
  | n + 1, .pi A B => s!"(Π {Tm.ppD n A}. {Tm.ppD n B})"
  | n + 1, .lam A t => s!"(λ {Tm.ppD n A}. {Tm.ppD n t})"
  | n + 1, .app f a => s!"({Tm.ppD n f} {Tm.ppD n a})"
  | n + 1, .sigma A B => s!"(Σ {Tm.ppD n A}. {Tm.ppD n B})"
  | n + 1, .pair a b => s!"({Tm.ppD n a}, {Tm.ppD n b})"
  | n + 1, .fst p => s!"{Tm.ppD n p}.1"
  | n + 1, .snd p => s!"{Tm.ppD n p}.2"
  | n + 1, .path A a b => s!"(PathP (i. {Tm.ppD n A}) {Tm.ppD n a} {Tm.ppD n b})"
  | n + 1, .plam t => s!"(⟨i⟩ {Tm.ppD n t})"
  | n + 1, .papp p r => s!"({Tm.ppD n p} @ {I.pp r})"
  | n + 1, .ipi A => s!"((i : I) → {Tm.ppD n A})"
  | n + 1, .split φ t ψ u => s!"[{I.pp φ} ↦ {Tm.ppD n t}, {I.pp ψ} ↦ {Tm.ppD n u}]"
  | n + 1, .abort => "[]"
  | n + 1, .transp A φ a => s!"(transp (i. {Tm.ppD n A}) {I.pp φ} {Tm.ppD n a})"
  | n + 1, .hcomp A φ u a => s!"(hcomp {Tm.ppD n A} [{I.pp φ} ↦ i. {Tm.ppD n u}] {Tm.ppD n a})"
  | n + 1, .glue A φ T e => s!"(Glue {Tm.ppD n A} [{I.pp φ} ↦ ({Tm.ppD n T}, {Tm.ppD n e})])"
  | n + 1, .glueEl φ _ t a => s!"(glue [{I.pp φ} ↦ {Tm.ppD n t}] {Tm.ppD n a})"
  | n + 1, .unglue φ _ g => s!"(unglue {I.pp φ} {Tm.ppD n g})"
  | n + 1, .tnil => "[]"
  | n + 1, .tcons t ts => s!"{Tm.ppD n t} :: {Tm.ppD n ts}"
  | n + 1, .data d ps => s!"(D{d} {Tm.ppD n ps})"
  | n + 1, .con d c ps args _ => s!"(D{d}.{c} {Tm.ppD n ps} {Tm.ppD n args})"
  | n + 1, .elim d ps P bs t => s!"(elim D{d} {Tm.ppD n ps} (x. {Tm.ppD n P}) {Tm.ppD n bs} {Tm.ppD n t})"

def Tm.pp (t : Tm) : String := Tm.ppD 1000000 t

def _root_.KubusCore.Tm.size : Tm → Nat
  | .var _ | .const _ | .univ _ | .abort => 1
  | .fst t | .snd t | .plam t | .ipi t | .papp t _ => t.size + 1
  | .pi A B | .sigma A B | .app A B | .pair A B | .split _ A _ B | .transp A _ B | .glueEl _ _ A B
  | .lam A B | .unglue _ A B | .tcons A B | .con _ _ A B _ => A.size + B.size + 1
  | .tnil => 1
  | .data _ ps => ps.size + 1
  | .elim _ ps P bs t => ps.size + P.size + bs.size + t.size + 1
  | .path A a b => A.size + a.size + b.size + 1
  | .hcomp A _ u a => A.size + u.size + a.size + 1
  | .glue A _ T e => A.size + T.size + e.size + 1

def short (t : Tm) : String :=
  let s := Tm.ppD 12 t
  if s.length > 400 then (s.take 400).toString ++ "…" else s

/-! ## Checks that produce proofs -/

def fail {S : Sig} {α : Type} (msg : String) : K S α := throw msg

/-- Add context to an error message. -/
def mapErr {S : Sig} {α : Type} (f : String → String) (x : K S α) : K S α :=
  tryCatch x fun e => throw (f e)

/-- Run `x`, turning failure into `none`. -/
def tryOpt {S : Sig} {α : Type} (x : K S α) : K S (Option α) :=
  tryCatch (some <$> x) fun _ => pure none

def ensureEq {S : Sig} (a b : Tm) (what : String) : K S (PLift (a = b)) :=
  if h : a = b then pure ⟨h⟩ else fail s!"kernel: {what}: {short a} is not {short b}"

def ensureEnt {S : Sig} (φ ψ : I) : K S (PLift (I.Entails φ ψ)) :=
  if h : I.Entails φ ψ then pure ⟨h⟩
  else fail s!"kernel: cofibration {I.pp φ} does not entail {I.pp ψ}"

def ensureEntE {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (ψ : I) : K S (PLift (I.Entails Φ ψ)) :=
  if h : E.Ent ψ then pure ⟨h⟩
  else fail s!"kernel: cofibration {I.pp Φ} does not entail {I.pp ψ}"

def ensureScoped {S : Sig} (r : I) (n : Nat) : K S (PLift (r.Scoped n)) :=
  if h : r.Scoped n then pure ⟨h⟩ else fail s!"kernel: interval term {I.pp r} out of scope"

def ensureIEq {S : Sig} (r s : I) : K S (PLift (I.Eq r s)) :=
  if h : I.eqB r s = true then pure ⟨I.eqB_sound h⟩
  else fail s!"kernel: interval terms {I.pp r} and {I.pp s} differ"

/-! ## Restriction to `Φ ∧ φ` -/

variable {S : Sig} {Ψ : Nat} {Φ : I} {Γ : Ctx}

theorem scoped_cof {n : Nat} {Φ φ : I} (h1 : Φ.Scoped n) (h2 : φ.Scoped n) : (cof Φ φ).Scoped n := ⟨h1, h2⟩

def _root_.KubusCore.KCtx.cof (E : KCtx S Ψ Φ Γ) (φ : I) (hφ : φ.Scoped Ψ) : KCtx S Ψ (KubusCore.cof Φ φ) Γ :=
  E.restrict (KubusCore.cof Φ φ) (scoped_cof E.hsc hφ) (I.entails_and_left Φ φ)

theorem HasTy.rs {t A φ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ) (h : HasTy S Ψ Φ Γ t A) :
    HasTy S Ψ (cof Φ φ) Γ t A :=
  HasTy.restrict (scoped_cof E.hsc hφ) (I.entails_and_left Φ φ) h

theorem EqTm.rs {t u A φ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ) (h : EqTm S Ψ Φ Γ t u A) :
    EqTm S Ψ (cof Φ φ) Γ t u A :=
  EqTm.restrict (scoped_cof E.hsc hφ) (I.entails_and_left Φ φ) h

theorem _root_.KubusCore.KCtx.univTy (E : KCtx S Ψ Φ Γ) (l : Nat) (h : l + 1 ≤ maxLevel) :
    HasTy S Ψ Φ Γ (.univ l) (.univ (l + 1)) :=
  HasTy.univ h E.wf

def ensureLvl (l : Nat) : K S (PLift (l ≤ maxLevel)) :=
  if h : l ≤ maxLevel then pure ⟨h⟩ else fail s!"kernel: universe level {l} exceeds the maximum {maxLevel}"

/-- `U l : U (l + 1)`, if the level is allowed. -/
def univTyK (E : KCtx S Ψ Φ Γ) (l : Nat) : K S (PLift (HasTy S Ψ Φ Γ (.univ l) (.univ (l + 1)))) := do
  let ⟨h⟩ ← ensureLvl (l + 1)
  pure ⟨E.univTy l h⟩

/-- Weaken a type derivation to the shifted restriction `(Φ ∧ φ).shift` -/
theorem HasTy.dwkCof {t A φ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ) (h : HasTy S Ψ Φ Γ t A) :
    HasTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift t.dshift A.dshift :=
  HasTy.dwk (HasTy.rs E hφ h)

theorem EqTm.dwkCof {t u A φ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ) (h : EqTm S Ψ Φ Γ t u A) :
    EqTm S (Ψ + 1) (cof Φ φ).shift Γ.dshift t.dshift u.dshift A.dshift :=
  EqTm.dwk (EqTm.rs E hφ h)

/-- Restrict a derivation in the interval-extended context to `(Φ ∧ φ).shift`. -/
theorem HasTy.rsd {t A φ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ)
    (h : HasTy S (Ψ + 1) Φ.shift Γ.dshift t A) : HasTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift t A :=
  HasTy.restrict ((E.cof φ hφ).dext.hsc) (I.entails_and_left Φ.shift φ.shift) h

theorem EqTm.rsd {t u A φ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ)
    (h : EqTm S (Ψ + 1) Φ.shift Γ.dshift t u A) : EqTm S (Ψ + 1) (cof Φ φ).shift Γ.dshift t u A :=
  EqTm.restrict ((E.cof φ hφ).dext.hsc) (I.entails_and_left Φ.shift φ.shift) h

/-! ## Using the recursive calls -/

section
variable (R : Rec S) (E : KCtx S Ψ Φ Γ)

/-- Compare two types (at the larger of their levels). -/
def convTy (X Y : Tm) (lX lY : Nat) (hX : HasTy S Ψ Φ Γ X (.univ lX))
    (hY : HasTy S Ψ Φ Γ Y (.univ lY)) : K S (PLift (EqTm S Ψ Φ Γ X Y (.univ (max lX lY)))) := do
  let ⟨h1⟩ ← ensureLvl (max lX lY + 1)
  have hm : max lX lY ≤ maxLevel := Nat.le_of_succ_le h1
  R.conv E (.univ (max lX lY)) (max lX lY + 1) (E.univTy _ h1) X Y
    (hX.liftLe (Nat.le_max_left _ _) hm) (hY.liftLe (Nat.le_max_right _ _) hm)

/-- Move an equation from type `T` to type `A`. -/
def bridge {t t' T A : Tm} {lT lA : Nat} (hT : HasTy S Ψ Φ Γ T (.univ lT))
    (hA : HasTy S Ψ Φ Γ A (.univ lA)) (e : EqTm S Ψ Φ Γ t t' T) :
    K S (PLift (EqTm S Ψ Φ Γ t t' A)) :=
  if h : T = A then pure ⟨h ▸ e⟩ else
  match T, A, e, hT, hA with
  | .univ a, .univ b, e, _, _ =>
    if hab : a ≤ b then do
      let ⟨hb⟩ ← ensureLvl b
      pure ⟨e.liftLe hab hb⟩
    else fail s!"kernel: universe U{a} does not fit into U{b}"
  | T, A, e, hT, hA => do
    let ⟨eTA⟩ ← convTy R E T A lT lA hT hA
    pure ⟨EqTm.conv e eTA⟩

/-- Move a typing from type `T` to type `A`. -/
def bridgeHas {t T A : Tm} {lT lA : Nat} (hT : HasTy S Ψ Φ Γ T (.univ lT))
    (hA : HasTy S Ψ Φ Γ A (.univ lA)) (h : HasTy S Ψ Φ Γ t T) : K S (PLift (HasTy S Ψ Φ Γ t A)) :=
  if hTA : T = A then pure ⟨hTA ▸ h⟩ else
  match T, A, h, hT, hA with
  | .univ a, .univ b, h, _, _ =>
    if hab : a ≤ b then do
      let ⟨hb⟩ ← ensureLvl b
      pure ⟨h.liftLe hab hb⟩
    else fail s!"kernel: universe U{a} does not fit into U{b}"
  | T, A, h, hT, hA => do
    let ⟨eTA⟩ ← convTy R E T A lT lA hT hA
    pure ⟨HasTy.conv h eTA⟩

/-- Weak-head normal form of a type. -/
def whnfTy (A : Tm) (l : Nat) (hA : HasTy S Ψ Φ Γ A (.univ l)) : K S (Red S Ψ Φ Γ A (.univ l)) := do
  let ⟨hU⟩ ← univTyK E l
  R.whnf E A (.univ l) (l + 1) hU hA

/-- Infer a type and bring it to weak-head normal form. -/
def inferW (t : Tm) : K S (Inf S Ψ Φ Γ t) := do
  let i ← R.infer E t
  let r ← whnfTy R E i.ty i.lvl i.hty
  pure ⟨r.tm, i.lvl, HasTy.eqR r.eq, HasTy.conv i.htm r.eq⟩

/-- Infer the universe level of a type. -/
def inferType (A : Tm) : K S ((l : Nat) × PLift (HasTy S Ψ Φ Γ A (.univ l))) := do
  match ← inferW R E A with
  | ⟨.univ l, _, _, h⟩ => pure ⟨l, ⟨h⟩⟩
  | ⟨T, _, _, _⟩ => fail s!"kernel: expected a type, but {short A} has type {short T}"

/-- Check a type at a given level. -/
def checkType (A : Tm) (l : Nat) : K S (PLift (HasTy S Ψ Φ Γ A (.univ l))) := do
  let ⟨hU⟩ ← univTyK E l
  R.check E A (.univ l) (l + 1) hU

end

/-! ## Premises of `transp` and `hcomp` -/

structure TranspInfo (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (A : Tm) (φ : I) (a : Tm) where
  l : Nat
  hA : HasTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l)
  hφ : φ.Scoped Ψ
  heq : EqTm S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l)
  ha : HasTy S Ψ Φ Γ a (A.dinst .zero)
  ht : HasTy S Ψ Φ Γ (.transp A φ a) (A.dinst .one)

def inferTransp (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (φ : I) (a : Tm) :
    K S (TranspInfo S Ψ Φ Γ A φ a) := do
  let ⟨hφ⟩ ← ensureScoped φ Ψ
  let ⟨l, ⟨hA⟩⟩ ← inferType R E.dext A
  let hA0 : HasTy S Ψ Φ Γ (A.dinst .zero) (.univ l) := HasTy.dsubst hA trivial
  let ⟨ha⟩ ← R.check E a (A.dinst .zero) l hA0
  let E' := (E.cof φ hφ).dext
  let ⟨hU⟩ ← univTyK E' l
  let ⟨heq⟩ ← R.conv E' (.univ l) (l + 1) hU A (A.dinst .zero).dshift
    (HasTy.rsd E hφ hA) (HasTy.dwkCof E hφ hA0)
  pure ⟨l, hA, hφ, heq, ha, HasTy.transp hA hφ heq ha⟩

structure HcompInfo (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (A : Tm) (φ : I) (u a : Tm) where
  l : Nat
  hA : HasTy S Ψ Φ Γ A (.univ l)
  hφ : φ.Scoped Ψ
  hu : HasTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift
  ha : HasTy S Ψ Φ Γ a A
  heq : EqTm S Ψ (cof Φ φ) Γ (u.dinst .zero) a A
  ht : HasTy S Ψ Φ Γ (.hcomp A φ u a) A

def inferHcomp (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (φ : I) (u a : Tm) :
    K S (HcompInfo S Ψ Φ Γ A φ u a) := do
  let ⟨hφ⟩ ← ensureScoped φ Ψ
  let ⟨l, ⟨hA⟩⟩ ← inferType R E A
  let E1 := E.cof φ hφ
  let ⟨hu⟩ ← R.check E1.dext u A.dshift l (HasTy.dwkCof E hφ hA)
  let ⟨ha⟩ ← R.check E a A l hA
  have hu0 : HasTy S Ψ (cof Φ φ) Γ (u.dinst .zero) A := by
    have := HasTy.dsubst (r := .zero) hu trivial
    rwa [Tm.dshift_dinst] at this
  let ⟨heq⟩ ← R.conv E1 A l (HasTy.rs E hφ hA) (u.dinst .zero) a hu0 (HasTy.rs E hφ ha)
  pure ⟨l, hA, hφ, hu, ha, heq, HasTy.hcomp hA hφ hu ha heq⟩

end KubusCore.Kernel
