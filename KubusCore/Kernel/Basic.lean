import KubusCore.Kernel.Ctx

/-!
# Kernel: result types, the recursion record, and helpers

Every kernel function returns a derivation of a judgment of the specification
(`KubusCore/Rules.lean`). The kernel's functions are mutually recursive; to keep each of them
a separate definition, they take a record `Rec S` of the recursive calls, and the knot is
tied by recursion on a fuel parameter (`Kernel.Main`).
-/

namespace KubusCore.Kernel

abbrev K := Except String

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

/-- The recursive calls of the kernel. -/
structure Rec (S : Sig) where
  infer : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t : Tm) → K (Inf S Ψ Φ Γ t)
  check : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t A : Tm) → (l : Nat) → HasTy S Ψ Φ Γ A (.univ l) →
    K (PLift (HasTy S Ψ Φ Γ t A))
  /-- weak-head normal form at a given type -/
  whnf : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t A : Tm) → (l : Nat) → HasTy S Ψ Φ Γ A (.univ l) →
    HasTy S Ψ Φ Γ t A → K (Red S Ψ Φ Γ t A)
  /-- infer the type and compute the weak-head normal form -/
  whnfI : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t : Tm) → K ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty)
  conv : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (A : Tm) → (l : Nat) → HasTy S Ψ Φ Γ A (.univ l) →
    (t u : Tm) → HasTy S Ψ Φ Γ t A → HasTy S Ψ Φ Γ u A → K (PLift (EqTm S Ψ Φ Γ t u A))
  /-- compare two neutral terms in weak-head normal form, inferring the type of the first -/
  convNe : ∀ {Ψ Φ Γ}, KCtx S Ψ Φ Γ → (t u : Tm) →
    K ((i : Inf S Ψ Φ Γ t) × PLift (EqTm S Ψ Φ Γ t u i.ty))

def Rec.bot (S : Sig) : Rec S where
  infer := fun _ _ => .error "kernel: out of fuel"
  check := fun _ _ _ _ _ => .error "kernel: out of fuel"
  whnf := fun _ _ _ _ _ _ => .error "kernel: out of fuel"
  whnfI := fun _ _ => .error "kernel: out of fuel"
  conv := fun _ _ _ _ _ _ _ _ => .error "kernel: out of fuel"
  convNe := fun _ _ _ => .error "kernel: out of fuel"

/-! ## Printing (error messages only) -/

def I.pp : I → String
  | .zero => "0"
  | .one => "1"
  | .var i => s!"i{i}"
  | .neg r => s!"~{I.pp r}"
  | .and r s => s!"({I.pp r} ∧ {I.pp s})"
  | .or r s => s!"({I.pp r} ∨ {I.pp s})"

def Tm.pp : Tm → String
  | .var x => s!"x{x}"
  | .const k => s!"c{k}"
  | .univ l => s!"U{l}"
  | .pi A B => s!"(Π {Tm.pp A}. {Tm.pp B})"
  | .lam A t => s!"(λ {Tm.pp A}. {Tm.pp t})"
  | .app f a => s!"({Tm.pp f} {Tm.pp a})"
  | .sigma A B => s!"(Σ {Tm.pp A}. {Tm.pp B})"
  | .pair a b => s!"({Tm.pp a}, {Tm.pp b})"
  | .fst p => s!"{Tm.pp p}.1"
  | .snd p => s!"{Tm.pp p}.2"
  | .path A a b => s!"(PathP (i. {Tm.pp A}) {Tm.pp a} {Tm.pp b})"
  | .plam t => s!"(⟨i⟩ {Tm.pp t})"
  | .papp p r => s!"({Tm.pp p} @ {I.pp r})"
  | .ipi A => s!"((i : I) → {Tm.pp A})"
  | .split φ t ψ u => s!"[{I.pp φ} ↦ {Tm.pp t}, {I.pp ψ} ↦ {Tm.pp u}]"
  | .abort => "[]"
  | .transp A φ a => s!"(transp (i. {Tm.pp A}) {I.pp φ} {Tm.pp a})"
  | .hcomp A φ u a => s!"(hcomp {Tm.pp A} [{I.pp φ} ↦ i. {Tm.pp u}] {Tm.pp a})"
  | .glue A φ T e => s!"(Glue {Tm.pp A} [{I.pp φ} ↦ ({Tm.pp T}, {Tm.pp e})])"
  | .glueEl φ _ t a => s!"(glue [{I.pp φ} ↦ {Tm.pp t}] {Tm.pp a})"
  | .unglue φ _ g => s!"(unglue {I.pp φ} {Tm.pp g})"

def _root_.KubusCore.Tm.size : Tm → Nat
  | .var _ | .const _ | .univ _ | .abort => 1
  | .fst t | .snd t | .plam t | .ipi t | .papp t _ => t.size + 1
  | .pi A B | .sigma A B | .app A B | .pair A B | .split _ A _ B | .transp A _ B | .glueEl _ _ A B
  | .lam A B | .unglue _ A B => A.size + B.size + 1
  | .path A a b => A.size + a.size + b.size + 1
  | .hcomp A _ u a => A.size + u.size + a.size + 1
  | .glue A _ T e => A.size + T.size + e.size + 1

def short (t : Tm) : String :=
  let s := Tm.pp t
  if s.length > 400 then (s.take 400).toString ++ "…" else s

/-! ## Checks that produce proofs -/

def fail {α : Type} (msg : String) : K α := .error msg

def ensureEq (a b : Tm) (what : String) : K (PLift (a = b)) :=
  if h : a = b then pure ⟨h⟩ else fail s!"kernel: {what}: {short a} is not {short b}"

def ensureEnt (φ ψ : I) : K (PLift (I.Entails φ ψ)) :=
  if h : I.Entails φ ψ then pure ⟨h⟩
  else fail s!"kernel: cofibration {I.pp φ} does not entail {I.pp ψ}"

def ensureScoped (r : I) (n : Nat) : K (PLift (r.Scoped n)) :=
  if h : r.Scoped n then pure ⟨h⟩ else fail s!"kernel: interval term {I.pp r} out of scope"

def ensureIEq (r s : I) : K (PLift (I.Eq r s)) :=
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

def ensureLvl (l : Nat) : K (PLift (l ≤ maxLevel)) :=
  if h : l ≤ maxLevel then pure ⟨h⟩ else fail s!"kernel: universe level {l} exceeds the maximum {maxLevel}"

/-- `U l : U (l + 1)`, if the level is allowed. -/
def univTyK (E : KCtx S Ψ Φ Γ) (l : Nat) : K (PLift (HasTy S Ψ Φ Γ (.univ l) (.univ (l + 1)))) := do
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
    (hY : HasTy S Ψ Φ Γ Y (.univ lY)) : K (PLift (EqTm S Ψ Φ Γ X Y (.univ (max lX lY)))) := do
  let ⟨h1⟩ ← ensureLvl (max lX lY + 1)
  have hm : max lX lY ≤ maxLevel := Nat.le_of_succ_le h1
  R.conv E (.univ (max lX lY)) (max lX lY + 1) (E.univTy _ h1) X Y
    (hX.liftLe (Nat.le_max_left _ _) hm) (hY.liftLe (Nat.le_max_right _ _) hm)

/-- Move an equation from type `T` to type `A`. -/
def bridge {t t' T A : Tm} {lT lA : Nat} (hT : HasTy S Ψ Φ Γ T (.univ lT))
    (hA : HasTy S Ψ Φ Γ A (.univ lA)) (e : EqTm S Ψ Φ Γ t t' T) :
    K (PLift (EqTm S Ψ Φ Γ t t' A)) :=
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
    (hA : HasTy S Ψ Φ Γ A (.univ lA)) (h : HasTy S Ψ Φ Γ t T) : K (PLift (HasTy S Ψ Φ Γ t A)) :=
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
def whnfTy (A : Tm) (l : Nat) (hA : HasTy S Ψ Φ Γ A (.univ l)) : K (Red S Ψ Φ Γ A (.univ l)) := do
  let ⟨hU⟩ ← univTyK E l
  R.whnf E A (.univ l) (l + 1) hU hA

/-- Infer a type and bring it to weak-head normal form. -/
def inferW (t : Tm) : K (Inf S Ψ Φ Γ t) := do
  let i ← R.infer E t
  let r ← whnfTy R E i.ty i.lvl i.hty
  pure ⟨r.tm, i.lvl, HasTy.eqR r.eq, HasTy.conv i.htm r.eq⟩

/-- Infer the universe level of a type. -/
def inferType (A : Tm) : K ((l : Nat) × PLift (HasTy S Ψ Φ Γ A (.univ l))) := do
  match ← inferW R E A with
  | ⟨.univ l, _, _, h⟩ => pure ⟨l, ⟨h⟩⟩
  | ⟨T, _, _, _⟩ => fail s!"kernel: expected a type, but {short A} has type {short T}"

/-- Check a type at a given level. -/
def checkType (A : Tm) (l : Nat) : K (PLift (HasTy S Ψ Φ Γ A (.univ l))) := do
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
    K (TranspInfo S Ψ Φ Γ A φ a) := do
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
    K (HcompInfo S Ψ Φ Γ A φ u a) := do
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
