import KubusCore.Kernel.Basic

/-!
# Kernel: inductive types

Typing of `data`, `con` and `elim` (including the branch types and the boundary conditions of
branches), telescopes, and the premises that reduction and conversion re-derive. All rules
about inductive types that the kernel uses are applied in this file or by name in
`Whnf.lean`/`Conv.lean`, so that changes to the rules stay local.
-/

namespace KubusCore.Kernel

variable {S : Sig}

def lookupData (S : Sig) (d : Nat) : K S ((D : DataDecl) × PLift (S[d]? = some (.data D))) :=
  match S[d]?, (rfl : S[d]? = S[d]?) with
  | some (.data D), h => pure ⟨D, ⟨h.symm⟩⟩
  | _, _ => fail s!"kernel: D{d} is not an inductive type"

def lookupCtor (D : DataDecl) (c : Nat) : K S ((C : Ctor) × PLift (D.ctors[c]? = some C)) :=
  match D.ctors[c]?, (rfl : D.ctors[c]? = D.ctors[c]?) with
  | some C, h => pure ⟨C, ⟨h.symm⟩⟩
  | none, _ => fail s!"kernel: no constructor {c}"

def getIdx? {α : Type} (l : List α) (k : Nat) : Option ((x : α) × PLift (l[k]? = some x)) :=
  match l[k]?, (rfl : l[k]? = l[k]?) with
  | some x, h => some ⟨x, ⟨h.symm⟩⟩
  | none, _ => none

def getIdx' {α : Type} (l : List α) (k : Nat) :
    ((x : α) × PLift (l[k]? = some x)) ⊕ PLift (l[k]? = none) :=
  match l[k]?, (rfl : l[k]? = l[k]?) with
  | some x, h => .inl ⟨x, ⟨h.symm⟩⟩
  | none, h => .inr ⟨h.symm⟩

/-- `t` is a literal list. -/
def ensureList (t : Tm) : K S (PLift (t = Tm.ofList t.toList)) :=
  if h : t = Tm.ofList t.toList then pure ⟨h⟩ else fail "kernel: expected a list"

/-- Check a list term against a telescope. -/
def checkTele (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    (as : Tm) → (Δ prev : List Tm) → K S (PLift (HasTele S Ψ Φ Γ as Δ prev))
  | .tnil, [], _ => pure ⟨HasTele.nil E.wf⟩
  | .tcons a as, A :: Δ, prev => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E (A.substList prev)
    let ⟨ha⟩ ← R.check E a _ l hA
    let ⟨hs⟩ ← checkTele R E as Δ (a :: prev)
    pure ⟨HasTele.cons ha hs⟩
  | _, _, _ => fail "kernel: wrong number of arguments"

/-- Compare two list terms in a telescope. -/
def convTele (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    (as as' : Tm) → (Δ prev : List Tm) → K S (PLift (EqTele S Ψ Φ Γ as as' Δ prev))
  | .tnil, .tnil, [], _ => pure ⟨EqTele.nil E.wf⟩
  | .tcons a as, .tcons a' as', A :: Δ, prev => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E (A.substList prev)
    let ⟨ha⟩ ← R.check E a _ l hA
    let ⟨ha'⟩ ← R.check E a' _ l hA
    let ⟨e⟩ ← R.conv E _ l hA a a' ha ha'
    let ⟨hs⟩ ← convTele R E as as' Δ (a :: prev)
    pure ⟨EqTele.cons e hs⟩
  | _, _, _, _ => fail "kernel: argument lists differ in length"

theorem HasTele.eqRefl {Ψ Φ Γ} : ∀ {as Δ prev}, HasTele S Ψ Φ Γ as Δ prev →
    EqTele S Ψ Φ Γ as as Δ prev
  | _, _, _, .nil hw => EqTele.nil hw
  | _, _, _, .cons ha hs => EqTele.cons (EqTm.refl ha) (HasTele.eqRefl hs)

/-- `data d ps : U_l`. -/
def inferData (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d : Nat) (ps : Tm) :
    K S ((D : DataDecl) × PLift (S[d]? = some (.data D) ∧ HasTy S Ψ Φ Γ (.data d ps) (.univ D.level))) := do
  let ⟨D, ⟨hS⟩⟩ ← lookupData S d
  let ⟨hl⟩ ← ensureLvl (D.level + 1)
  let ⟨hps⟩ ← checkTele R E ps D.params []
  pure ⟨D, ⟨hS, HasTy.data hS hl hps⟩⟩

/-- `con d c ps args rs : data d ps`. -/
def inferCon (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d c : Nat) (ps args : Tm) (rs : List I) :
    K S ((D : DataDecl) × PLift (S[d]? = some (.data D) ∧
      HasTy S Ψ Φ Γ (.data d ps) (.univ D.level) ∧ HasTy S Ψ Φ Γ (.con d c ps args rs) (.data d ps))) := do
  let ⟨D, ⟨hS, hD⟩⟩ ← inferData R E d ps
  let ⟨C, ⟨hC⟩⟩ ← lookupCtor D c
  let ⟨hl⟩ ← ensureList ps
  let ⟨hargs⟩ ← checkTele R E args (C.argTys d D.params.length) ps.toList.reverse
  if hlen : rs.length = C.dims then
    if hsc : rs.all (·.scopedB Ψ) = true then
      have hsc' : ∀ r ∈ rs, r.Scoped Ψ := fun r hr => (I.scopedB_iff _ _).mp (List.all_eq_true.mp hsc r hr)
      pure ⟨D, ⟨hS, hD, HasTy.con hS hC hl hD hargs hlen hsc'⟩⟩
    else fail "kernel: interval argument out of scope"
  else fail "kernel: wrong number of interval arguments"

/-! ## Contexts for branches -/

def shiftIN : Nat → I → I
  | 0, Φ => Φ
  | m + 1, Φ => (shiftIN m Φ).shift

def dshiftN : Nat → Ctx → Ctx
  | 0, Γ => Γ
  | m + 1, Γ => (dshiftN m Γ).dshift

def _root_.KubusCore.KCtx.dextN {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    (m : Nat) → KCtx S (Ψ + m) (shiftIN m Φ) (dshiftN m Γ)
  | 0 => E
  | m + 1 => (E.dextN m).dext

def castCtx {Ψ Φ Φ' Γ Γ'} (E : KCtx S Ψ Φ Γ) (hΦ : Φ = Φ') (hΓ : Γ = Γ') : KCtx S Ψ Φ' Γ' :=
  hΦ ▸ hΓ ▸ E

/-- Extend a context by a list of types (the first is bound first). -/
def extTypes (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    (As : List Tm) → K S (KCtx S Ψ Φ (As.reverse ++ Γ))
  | [] => pure E
  | A :: As => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E A
    let E' ← extTypes R (E.ext A l hA) As
    pure (by simpa using E')

/-- The branch context of constructor `C`, restricted to the boundary face `ψ`. -/
def branchCtxK (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (D : DataDecl) (d : Nat) (C : Ctor)
    (ps P : Tm) (ψ : I) :
    K S (KCtx S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)) := do
  let n := C.args.length
  let r := C.recPos.length
  let tys := (List.range n).map (DataDecl.branchArgTy d D.params.length C ps) ++
    (List.range r).map (DataDecl.branchIhTy C P)
  let E1 ← extTypes R E tys
  let E2 := E1.dextN C.dims
  if hΦ : shiftIN C.dims Φ = Φ.ren (· + C.dims) then
    if hΓ : dshiftN C.dims (tys.reverse ++ Γ) = D.branchCtx d C ps P Γ then
      let E3 := castCtx E2 hΦ hΓ
      let ⟨hψ⟩ ← ensureScoped ψ (Ψ + C.dims)
      pure (E3.cof ψ hψ)
    else fail "kernel: branch context mismatch"
  else fail "kernel: branch restriction mismatch"

/-! ## Quantifying over constructors -/

/-- Prove a property of all pairs of corresponding elements of two lists by checking each. -/
def forallPairs {α β : Type} (xs : List α) (ys : List β) (P : Nat → α → β → Prop)
    (f : (c : Nat) → (x : α) → (y : β) → xs[c]? = some x → ys[c]? = some y → K S (PLift (P c x y))) :
    (n : Nat) → PLift (∀ c x y, c < n → xs[c]? = some x → ys[c]? = some y → P c x y) →
    K S (PLift (∀ c x y, xs[c]? = some x → ys[c]? = some y → P c x y))
  | n, ⟨acc⟩ =>
    if hn : n < xs.length then
      match hx : xs[n]? with
      | none =>
        forallPairs xs ys P f (n + 1) ⟨fun c x' y' hc hx' hy' => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | hc
          · exact acc c x' y' hc hx' hy'
          · subst hc; rw [hx] at hx'; cases hx'⟩
      | some x =>
        match hy : ys[n]? with
        | none =>
          forallPairs xs ys P f (n + 1) ⟨fun c x' y' hc hx' hy' => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | hc
            · exact acc c x' y' hc hx' hy'
            · subst hc; rw [hy] at hy'; cases hy'⟩
        | some y => do
          let ⟨p⟩ ← f n x y hx hy
          forallPairs xs ys P f (n + 1) ⟨fun c x' y' hc hx' hy' => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | hc
            · exact acc c x' y' hc hx' hy'
            · subst hc; rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; exact p⟩
    else pure ⟨fun c x y hx _ => by
      by_cases hc : c < n
      · exact acc c x y hc hx ‹_›
      · rw [List.getElem?_eq_none (by omega)] at hx; cases hx⟩
termination_by n => xs.length - n

def forallPairs0 {α β : Type} (xs : List α) (ys : List β) (P : Nat → α → β → Prop)
    (f : (c : Nat) → (x : α) → (y : β) → xs[c]? = some x → ys[c]? = some y → K S (PLift (P c x y))) :
    K S (PLift (∀ c x y, xs[c]? = some x → ys[c]? = some y → P c x y)) :=
  forallPairs xs ys P f 0 ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The same for the elements of one list. -/
def forallElems {α : Type} (xs : List α) (P : Nat → α → Prop)
    (f : (k : Nat) → (x : α) → xs[k]? = some x → K S (PLift (P k x))) :
    K S (PLift (∀ k x, xs[k]? = some x → P k x)) := do
  let ⟨h⟩ ← forallPairs0 xs xs (fun k x _ => P k x) (fun k x _ hx _ => f k x hx)
  pure ⟨fun k x hx => h k x x hx hx⟩

/-! ## Typing applications of branches

Branches are λ- and path abstractions, whose inferred types (with `(i : I) → A` for path
abstractions) need not be their branch types. Applications of branches are therefore typed
from the known branch types. -/

def _root_.KubusCore.Tm.unpapps : Tm → Tm × List I
  | .papp t r => let p := Tm.unpapps t; (p.1, p.2 ++ [r])
  | t => (t, [])

def _root_.KubusCore.Tm.unapps : Tm → Tm × List Tm
  | .app t a => let p := Tm.unapps t; (p.1, p.2 ++ [a])
  | t => (t, [])

theorem papps_unpapps (t : Tm) : t.unpapps.1.papps t.unpapps.2 = t := by
  induction t <;> simp_all [Tm.unpapps, Tm.papps, List.foldl_append]

theorem apps_unapps (t : Tm) : t.unapps.1.apps t.unapps.2 = t := by
  induction t <;> simp_all [Tm.unapps, Tm.apps, List.foldl_append]

/-- A typing of an argument at any expected type. -/
abbrev ArgPf (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (a : Tm) :=
  (A : Tm) → (l : Nat) → HasTy S Ψ Φ Γ A (.univ l) → K S (PLift (HasTy S Ψ Φ Γ a A))

/-- Type `f @ r₁ … rₘ` from a typing of `f`. -/
def pappsTyped (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    (f F : Tm) → (l : Nat) → HasTy S Ψ Φ Γ F (.univ l) → HasTy S Ψ Φ Γ f F →
    (rs : List I) → K S (Inf S Ψ Φ Γ (f.papps rs))
  | f, F, l, hF, hf, r :: rs => do
    let ⟨hr⟩ ← ensureScoped r Ψ
    match ← whnfTy R E F l hF with
    | ⟨.path A _ _, e⟩ =>
      have hP := HasTy.eqR e
      pappsTyped R E (.papp f r) (A.dinst r) l (HasTy.dsubst (HasTy.pathLine hP) hr)
        (HasTy.papp (HasTy.conv hf e) hr) rs
    | ⟨.ipi A, e⟩ =>
      have hP := HasTy.eqR e
      pappsTyped R E (.papp f r) (A.dinst r) l (HasTy.dsubst (HasTy.ipiLine hP) hr)
        (HasTy.iapp (HasTy.conv hf e) hr) rs
    | ⟨T, _⟩ => fail s!"kernel: path application at type {short T}"
  | _, F, l, hF, hf, [] => pure ⟨F, l, hF, hf⟩

/-- Type `f a₁ … aₙ @ r₁ … rₘ` from a typing of `f`. -/
def appsTyped (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    (f F : Tm) → (l : Nat) → HasTy S Ψ Φ Γ F (.univ l) → HasTy S Ψ Φ Γ f F →
    (args : List ((a : Tm) × ArgPf S Ψ Φ Γ a)) → (rs : List I) →
    K S (Inf S Ψ Φ Γ ((f.apps (args.map (·.1))).papps rs))
  | f, F, l, hF, hf, ⟨a, pa⟩ :: args, rs => do
    match ← whnfTy R E F l hF with
    | ⟨.pi A B, e⟩ =>
      have hP := HasTy.eqR e
      let ⟨ha⟩ ← pa A l (HasTy.piDom hP)
      appsTyped R E (.app f a) (B.inst a) l (HasTy.subst (HasTy.piCod hP) ha)
        (HasTy.app (HasTy.conv hf e) ha) args rs
    | ⟨T, _⟩ => fail s!"kernel: applying a term of type {short T}"
  | f, F, l, hF, hf, [], rs => pappsTyped R E f F l hF hf rs

/-- Type a term whose spine head is one of the `heads` (with their types); other terms are
inferred. -/
def typeSpine (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (heads : List (Tm × Tm)) :
    Nat → (t : Tm) → K S (Inf S Ψ Φ Γ t)
  | 0, t => R.infer E t
  | n + 1, t =>
    let h1 := t.unpapps
    let h0 := h1.1.unapps
    match heads.find? (·.1 == h0.1) with
    | some (_, H) => do
      let ⟨l, ⟨hH⟩⟩ ← inferType R E H
      let ⟨hh⟩ ← R.check E h0.1 H l hH
      let args : List ((a : Tm) × ArgPf S Ψ Φ Γ a) := h0.2.map fun a =>
        ⟨a, fun A _ hA => do
          let i ← typeSpine R E heads n a
          bridgeHas R E i.hty hA i.htm⟩
      let i ← appsTyped R E h0.1 H l hH hh args h1.2
      have hargs : args.map (·.1) = h0.2 := by
        simp only [args, List.map_map]
        exact List.map_id' h0.2
      have ht : (h0.1.apps (args.map (·.1))).papps h1.2 = t := by
        rw [hargs, apps_unapps, papps_unpapps]
      pure (ht ▸ i)
    | none => R.infer E t

/-! ## The eliminator -/

/-- Check the boundary condition of one branch on one face. -/
def checkBranchBnd (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (D : DataDecl) (d c : Nat) (C : Ctor)
    (ps P bs b : Tm) (ψ : I) (e : Tm) :
    K S (PLift (EqTm S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P))) := do
  let E' ← branchCtxK R E D d C ps P ψ
  let ⟨l, ⟨hT⟩⟩ ← inferType R E' (DataDecl.branchBody d c C ps P)
  let T := C.args.length + C.recPos.length
  let heads := (List.range D.ctors.length).filterMap fun c' =>
    match D.ctors[c']?, bs.toList[c']? with
    | some C', some b' => some (b'.wkN T C.dims, (D.branchTy d c' C' ps P).wkN T C.dims)
    | _, _ => none
  let i1 ← typeSpine R E' heads 1000 (DataDecl.branchApp C b)
  let ⟨h1⟩ ← bridgeHas R E' i1.hty hT i1.htm
  let i2 ← typeSpine R E' heads 1000 (D.bndElim C ps bs e)
  let ⟨h2⟩ ← bridgeHas R E' i2.hty hT i2.htm
  R.conv E' _ l hT _ _ h1 h2

def inferElimInfoRaw (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d : Nat) (ps P bs : Tm) :
    K S (ElimInfo S Ψ Φ Γ d ps P bs) := do
  let ⟨D, ⟨hS, hD⟩⟩ ← inferData R E d ps
  let ⟨m, ⟨hP⟩⟩ ← inferType R (E.ext (.data d ps) D.level hD) P
  let ⟨hps⟩ ← ensureList ps
  if hbs : bs = Tm.ofList bs.toList then
    if hlen : bs.toList.length = D.ctors.length then
      let ⟨hbr⟩ ← forallPairs0 D.ctors bs.toList
        (fun c C b => HasTy S Ψ Φ Γ b (D.branchTy d c C ps P)) fun c C b _ _ => do
          let ⟨l, ⟨hT⟩⟩ ← inferType R E (D.branchTy d c C ps P)
          R.check E b _ l hT
      let ⟨hbnd⟩ ← forallPairs0 D.ctors bs.toList
        (fun c C b => ∀ (k : Nat) (ψ : I) (e : Tm), C.bnd[k]? = some (ψ, e) →
          EqTm S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
            (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P))
        fun c C b _ _ => do
          let ⟨h⟩ ← forallElems C.bnd (fun _ pe => EqTm S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) pe.1)
              (D.branchCtx d C ps P Γ) (DataDecl.branchApp C b) (D.bndElim C ps bs pe.2)
              (DataDecl.branchBody d c C ps P))
            fun _ pe _ => checkBranchBnd R E D d c C ps P bs b pe.1 pe.2
          pure ⟨fun k ψ e hk => h k (ψ, e) hk⟩
      pure ⟨D, hS, m, hps, hD, hP, hbs, hlen, hbr,
        fun c C b k ψ e hC hb hk => hbnd c C b hC hb k ψ e hk⟩
    else fail "kernel: wrong number of branches"
  else fail "kernel: branches must be a list"

/-- `inferElimInfoRaw`, memoized. -/
def inferElimInfo (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d : Nat) (ps P bs : Tm) :
    K S (ElimInfo S Ψ Φ Γ d ps P bs) := do
  if let some v := (← get).elim.find? Ψ Φ Γ [.data d ps, P, bs] E.fs.get E.hfs E.hsc noRestr then return v
  let v ← inferElimInfoRaw R E d ps P bs
  modify fun c => { c with elim := c.elim.insert Ψ Φ Γ [.data d ps, P, bs] E.fs.get E.hfs v }
  return v

end KubusCore.Kernel
