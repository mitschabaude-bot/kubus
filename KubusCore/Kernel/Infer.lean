import KubusCore.Kernel.Data

/-!
# Kernel: type inference and checking

`inferStep` and `checkStep` implement one level of the bidirectional checker; recursive
calls go through the record `R`.
-/

namespace KubusCore.Kernel

variable {S : Sig}

/-- Change the cofibration and the equivalence of a Glue type to equivalent ones. -/
def reglue (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (φ' : I) (T e' : Tm) (φ : I) (e : Tm) (l : Nat)
    (hG' : HasTy S Ψ Φ Γ (.glue A φ' T e') (.univ l)) (hA : HasTy S Ψ Φ Γ A (.univ l)) :
    K (PLift (EqTm S Ψ Φ Γ (.glue A φ' T e') (.glue A φ T e) (.univ l))) := do
  if h : φ' = φ ∧ e' = e then
    return ⟨h.1 ▸ h.2 ▸ EqTm.refl hG'⟩
  let ⟨hφ⟩ ← ensureScoped φ Ψ
  let ⟨hφ'⟩ ← ensureScoped φ' Ψ
  let ⟨h1⟩ ← ensureEnt φ φ'
  let ⟨h2⟩ ← ensureEnt φ' φ
  let ⟨hc⟩ ← ensureEnt (cof Φ φ) (cof Φ φ')
  let ⟨hc'⟩ ← ensureEnt (cof Φ φ') (cof Φ φ)
  let E1 := E.cof φ hφ
  let E1' := E.cof φ' hφ'
  have hT := HasTy.restrict E1.hsc hc (HasTy.glueFib hG')
  let ⟨hq⟩ ← checkType R E1 (Tm.equiv T A) l
  let ⟨he⟩ ← R.check E1 e (Tm.equiv T A) l hq
  have hG2 := HasTy.glue hA hφ hT he
  have hq' := HasTy.restrict E1'.hsc hc' hq
  let ⟨he'⟩ ← R.check E1' e' (Tm.equiv T A) l hq'
  let ⟨ee⟩ ← R.conv E1' (Tm.equiv T A) l hq' e' e he' (HasTy.restrict E1'.hsc hc' he)
  return ⟨EqTm.glue hG' hG2 (EqTm.refl hA) h2 h1 (EqTm.refl (HasTy.glueFib hG')) ee⟩

/-- `e : Equiv T A` under `φ`, checked (Glue types do not imply it, since they reduce on `φ`). -/
def checkEquiv (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (φ : I) (T e : Tm) (l : Nat) :
    K (PLift (HasTy S Ψ (cof Φ φ) Γ e (Tm.equiv T A))) := do
  let ⟨hφ⟩ ← ensureScoped φ Ψ
  let E1 := E.cof φ hφ
  let ⟨hq⟩ ← checkType R E1 (Tm.equiv T A) l
  R.check E1 e (Tm.equiv T A) l hq

/-- Bring a type `G` to the form `Glue A [φ ↦ (T, e)]` with the given `φ`, with a derivation
that the base `A` is a type. -/
def toGlue (R : Rec S) (E : KCtx S Ψ Φ Γ) (G : Tm) (l : Nat) (hG : HasTy S Ψ Φ Γ G (.univ l))
    (φ : I) : K ((A T e : Tm) × PLift (HasTy S Ψ Φ Γ A (.univ l) ∧
      EqTm S Ψ Φ Γ G (.glue A φ T e) (.univ l))) := do
  match ← whnfTy R E G l hG with
  | ⟨.glue A φ' T e', eG⟩ =>
    let ⟨hA⟩ ← checkType R E A l
    let ⟨e2⟩ ← reglue R E A φ' T e' φ e' l (HasTy.eqR eG) hA
    return ⟨A, T, e', ⟨hA, EqTm.trans eG e2⟩⟩
  | ⟨G', _⟩ => fail s!"kernel: expected a Glue type, got {short G'}"

/-- The same, with a given equivalence `e`. -/
def toGlueE (R : Rec S) (E : KCtx S Ψ Φ Γ) (G : Tm) (l : Nat) (hG : HasTy S Ψ Φ Γ G (.univ l))
    (φ : I) (e : Tm) : K ((A T : Tm) × PLift (HasTy S Ψ Φ Γ A (.univ l) ∧
      EqTm S Ψ Φ Γ G (.glue A φ T e) (.univ l))) := do
  match ← whnfTy R E G l hG with
  | ⟨.glue A φ' T e', eG⟩ =>
    let ⟨hA⟩ ← checkType R E A l
    let ⟨e2⟩ ← reglue R E A φ' T e' φ e l (HasTy.eqR eG) hA
    return ⟨A, T, ⟨hA, EqTm.trans eG e2⟩⟩
  | ⟨G', _⟩ =>
    -- under `φ` the Glue type may have reduced already: rebuild it from the type of `e`
    if hφ : I.Entails Φ φ then
      let ⟨hsφ⟩ ← ensureScoped φ Ψ
      let E1 := E.cof φ hsφ
      match ← inferW R E1 e with
      | ⟨.sigma (.pi T A') _, _, _, _⟩ =>
        let A := A'.inst (.var 0)
        let ⟨hA⟩ ← checkType R E A l
        let ⟨hT1⟩ ← checkType R E1 T l
        let ⟨hq⟩ ← checkType R E1 (Tm.equiv T A) l
        let ⟨he⟩ ← R.check E1 e (Tm.equiv T A) l hq
        have hGl := HasTy.glue hA hsφ hT1 he
        have eF := EqTm.glueFace hφ hGl
        let ⟨hc⟩ ← ensureEnt Φ (cof Φ φ)
        let ⟨hU⟩ ← univTyK E l
        let ⟨eGT⟩ ← R.conv E (.univ l) (l + 1) hU G T hG (HasTy.restrict E.hsc hc hT1)
        return ⟨A, T, ⟨hA, EqTm.trans eGT (EqTm.symm eF)⟩⟩
      | ⟨Q, _, _, _⟩ => fail s!"kernel: expected an equivalence, got {short Q}"
    else fail s!"kernel: expected a Glue type, got {short G'}"

/-- Context conversion for the last variable. -/
theorem ctxConv {Ψ Φ Γ A A1 B m} (hA : HasTy S Ψ Φ Γ A (.univ m))
    (hP : HasTy S Ψ Φ Γ (.pi A1 B) (.univ m)) (eA : EqTm S Ψ Φ Γ A A1 (.univ m)) :
    HasTy S Ψ Φ (A :: Γ) B (.univ m) := by
  have h1 : HasTy S Ψ Φ (A :: Γ) (.pi A1.shift (B.ren (Tm.upRen Nat.succ) id)) (.univ m) :=
    HasTy.wk hA hP
  have hv : HasTy S Ψ Φ (A :: Γ) (.var 0) A1.shift :=
    HasTy.conv (HasTy.var (Wf.cons hA) rfl) (EqTm.wk hA eA)
  have := HasTy.subst (HasTy.piCod h1) hv
  rwa [Tm.upShift_inst0] at this

theorem HasTy.cofcof {Ψ Φ Γ t A φ ψ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ)
    (h : HasTy S Ψ Φ Γ t A) : HasTy S Ψ (cof (cof Φ φ) ψ) Γ t A :=
  HasTy.rs (E.cof φ hφ) hψ (HasTy.rs E hφ h)

/-- Guess `T` and `A` with `e : Equiv T A` from the type of `e`; a system of equivalences
gives a system of types. Only a guess: the caller checks it. -/
def guessEquivTy (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) : Tm → K (Tm × Tm)
  | .split φ e1 ψ e2 => do
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨hψ⟩ ← ensureScoped ψ Ψ
    let (T1, A) ← guessEquivTy R (E.cof φ hφ) e1
    let (T2, _) ← guessEquivTy R (E.cof ψ hψ) e2
    pure (.split φ T1 ψ T2, A)
  | e => do
    match ← inferW R E e with
    | ⟨.sigma (.pi T A') _, _, _, _⟩ => pure (T, A'.inst (.var 0))
    | ⟨Q, _, _, _⟩ => fail s!"kernel: expected an equivalence, got {short Q}"

/-- The type of `g` in `unglue φ e g`: inferred, or else the Glue type rebuilt from the type
of `e` (for arguments that cannot be inferred, like `glue` elements). -/
def inferUnglueArg (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (φ : I) (e g : Tm) :
    K (Inf S Ψ Φ Γ g) :=
  match R.infer E g with
  | .ok i => pure i
  | .error err => ((do
    let ⟨hsφ⟩ ← ensureScoped φ Ψ
    let E1 := E.cof φ hsφ
    let (T, A) ← guessEquivTy R E1 e
    let ⟨l, ⟨hA⟩⟩ ← inferType R E A
    let ⟨hT⟩ ← checkType R E1 T l
    let ⟨hq⟩ ← checkType R E1 (Tm.equiv T A) l
    let ⟨he⟩ ← R.check E1 e (Tm.equiv T A) l hq
    have hG := HasTy.glue hA hsφ hT he
    let ⟨hg⟩ ← R.check E g (.glue A φ T e) l hG
    pure ⟨.glue A φ T e, l, hG, hg⟩) : K (Inf S Ψ Φ Γ g)).mapError (fun e2 => err ++ "\n  and: " ++ e2)

/-- Combine two type derivations at the larger level. -/
def joinLvl (l1 l2 : Nat) : K (PLift (max l1 l2 + 1 ≤ maxLevel)) := ensureLvl (max l1 l2 + 1)

def inferStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) : (t : Tm) → K (Inf S Ψ Φ Γ t)
  | .var x =>
    match h : Γ.lookup x, hl : E.lv[x]? with
    | some A, some l => pure ⟨A, l, E.varOk x A l h hl, HasTy.var E.wf h⟩
    | _, _ => fail s!"kernel: unbound variable x{x}"
  | .const k =>
    match h : S[k]?, hl : E.sig.lv[k]? with
    | some (.defn b A), some l => pure ⟨A, l, E.constOk k b A l h hl, HasTy.const E.wf h⟩
    | _, _ => fail s!"kernel: unknown constant c{k}"
  | .univ l => do
    let ⟨h1⟩ ← ensureLvl (l + 2)
    pure ⟨.univ (l + 1), l + 2, E.univTy (l + 1) h1, E.univTy l (Nat.le_of_succ_le h1)⟩
  | .pi A B => do
    let ⟨l1, ⟨hA⟩⟩ ← inferType R E A
    let ⟨l2, ⟨hB⟩⟩ ← inferType R (E.ext A l1 hA) B
    let ⟨hm⟩ ← joinLvl l1 l2
    have hm' := Nat.le_of_succ_le hm
    pure ⟨.univ (max l1 l2), max l1 l2 + 1, E.univTy _ hm,
      HasTy.pi (hA.liftLe (Nat.le_max_left _ _) hm') (hB.liftLe (Nat.le_max_right _ _) hm')⟩
  | .sigma A B => do
    let ⟨l1, ⟨hA⟩⟩ ← inferType R E A
    let ⟨l2, ⟨hB⟩⟩ ← inferType R (E.ext A l1 hA) B
    let ⟨hm⟩ ← joinLvl l1 l2
    have hm' := Nat.le_of_succ_le hm
    pure ⟨.univ (max l1 l2), max l1 l2 + 1, E.univTy _ hm,
      HasTy.sigma (hA.liftLe (Nat.le_max_left _ _) hm') (hB.liftLe (Nat.le_max_right _ _) hm')⟩
  | .lam A t => do
    let ⟨l1, ⟨hA⟩⟩ ← inferType R E A
    let it ← R.infer (E.ext A l1 hA) t
    let ⟨hm⟩ ← ensureLvl (max l1 it.lvl)
    have hP : HasTy S Ψ Φ Γ (.pi A it.ty) (.univ (max l1 it.lvl)) :=
      HasTy.pi (hA.liftLe (Nat.le_max_left _ _) hm) (it.hty.liftLe (Nat.le_max_right _ _) hm)
    pure ⟨.pi A it.ty, max l1 it.lvl, hP, HasTy.lam hP it.htm⟩
  | .app f a => do
    match ← inferW R E f with
    | ⟨.pi A B, l, hP, hf⟩ =>
      let ⟨ha⟩ ← R.check E a A l (HasTy.piDom hP)
      pure ⟨B.inst a, l, HasTy.subst (HasTy.piCod hP) ha, HasTy.app hf ha⟩
    | ⟨T, _, _, _⟩ => fail s!"kernel: applying {short f} of non-function type {short T}"
  | .fst p => do
    match ← inferW R E p with
    | ⟨.sigma A _, l, hS, hp⟩ => pure ⟨A, l, HasTy.sigmaDom hS, HasTy.fst hp⟩
    | ⟨T, _, _, _⟩ => fail s!"kernel: projection from non-Σ type {short T}"
  | .snd p => do
    match ← inferW R E p with
    | ⟨.sigma _ B, l, hS, hp⟩ =>
      pure ⟨B.inst (.fst p), l, HasTy.subst (HasTy.sigmaCod hS) (HasTy.fst hp), HasTy.snd hp⟩
    | ⟨T, _, _, _⟩ => fail s!"kernel: projection from non-Σ type {short T}"
  | .pair a b => do
    -- non-dependent pair
    let ia ← R.infer E a
    let ib ← R.infer E b
    let ⟨hm⟩ ← ensureLvl (max ia.lvl ib.lvl)
    have hB : HasTy S Ψ Φ (ia.ty :: Γ) ib.ty.shift (.univ (max ia.lvl ib.lvl)) :=
      HasTy.wk ia.hty (ib.hty.liftLe (Nat.le_max_right _ _) hm)
    have hS := HasTy.sigma (ia.hty.liftLe (Nat.le_max_left _ _) hm) hB
    have hb : HasTy S Ψ Φ Γ b (ib.ty.shift.inst a) := by rw [Tm.shift_inst]; exact ib.htm
    pure ⟨.sigma ia.ty ib.ty.shift, max ia.lvl ib.lvl, hS, HasTy.pair hS ia.htm hb⟩
  | .path A a b => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E.dext A
    let ⟨hU⟩ ← univTyK E l
    let ⟨ha⟩ ← R.check E a (A.dinst .zero) l (HasTy.dsubst hA trivial)
    let ⟨hb⟩ ← R.check E b (A.dinst .one) l (HasTy.dsubst hA trivial)
    pure ⟨.univ l, l + 1, hU, HasTy.path hA ha hb⟩
  | .plam t => do
    let it ← R.infer E.dext t
    pure ⟨.ipi it.ty, it.lvl, HasTy.ipi it.hty, HasTy.ilam (HasTy.ipi it.hty) it.htm⟩
  | .papp p r => do
    let ⟨hr⟩ ← ensureScoped r Ψ
    match ← inferW R E p with
    | ⟨.path A _ _, l, hP, hp⟩ =>
      pure ⟨A.dinst r, l, HasTy.dsubst (HasTy.pathLine hP) hr, HasTy.papp hp hr⟩
    | ⟨.ipi A, l, hP, hp⟩ =>
      pure ⟨A.dinst r, l, HasTy.dsubst (HasTy.ipiLine hP) hr, HasTy.iapp hp hr⟩
    | ⟨T, _, _, _⟩ => fail s!"kernel: path application of {short p} of type {short T}"
  | .ipi A => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E.dext A
    let ⟨hU⟩ ← univTyK E l
    pure ⟨.univ l, l + 1, hU, HasTy.ipi hA⟩
  | .split φ t ψ u => do
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨hψ⟩ ← ensureScoped ψ Ψ
    let ⟨hcov⟩ ← ensureEnt Φ (.or φ ψ)
    let E2 := (E.cof φ hφ).cof ψ hψ
    if I.entails Φ φ then
      let it ← R.infer E t
      let ⟨hu⟩ ← R.check (E.cof ψ hψ) u it.ty it.lvl (HasTy.rs E hψ it.hty)
      let ⟨hc⟩ ← ensureEnt (cof (cof Φ φ) ψ) (cof Φ ψ)
      let ⟨e⟩ ← R.conv E2 it.ty it.lvl (HasTy.cofcof E hφ hψ it.hty) t u
        (HasTy.cofcof E hφ hψ it.htm) (HasTy.restrict E2.hsc hc hu)
      pure ⟨it.ty, it.lvl, it.hty, HasTy.split hφ hψ hcov it.hty (HasTy.rs E hφ it.htm) hu e⟩
    else if I.entails Φ ψ then
      let iu ← R.infer E u
      let ⟨ht⟩ ← R.check (E.cof φ hφ) t iu.ty iu.lvl (HasTy.rs E hφ iu.hty)
      let ⟨e⟩ ← R.conv E2 iu.ty iu.lvl (HasTy.cofcof E hφ hψ iu.hty) t u
        (HasTy.rs (E.cof φ hφ) hψ ht) (HasTy.cofcof E hφ hψ iu.htm)
      pure ⟨iu.ty, iu.lvl, iu.hty, HasTy.split hφ hψ hcov iu.hty ht (HasTy.rs E hψ iu.htm) e⟩
    else fail "kernel: cannot infer the type of a system"
  | .abort => fail "kernel: cannot infer the type of the empty system"
  | .transp A φ a => do
    let i ← inferTransp R E A φ a
    pure ⟨A.dinst .one, i.l, HasTy.dsubst i.hA trivial, i.ht⟩
  | .hcomp A φ u a => do
    let i ← inferHcomp R E A φ u a
    pure ⟨A, i.l, i.hA, i.ht⟩
  | .glue A φ T e => do
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨l, ⟨hA⟩⟩ ← inferType R E A
    let ⟨hU⟩ ← univTyK E l
    let E1 := E.cof φ hφ
    let ⟨hT⟩ ← checkType R E1 T l
    let ⟨hEq⟩ ← checkType R E1 (Tm.equiv T A) l
    let ⟨he⟩ ← R.check E1 e (Tm.equiv T A) l hEq
    pure ⟨.univ l, l + 1, hU, HasTy.glue hA hφ hT he⟩
  | .glueEl φ e t a => do
    -- the Glue type: the base from `a`, the fibres from the type of the equivalence
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let E1 := E.cof φ hφ
    let (T, _) ← guessEquivTy R E1 e
    let ia ← R.infer E a
    let l := ia.lvl
    let ⟨hT⟩ ← checkType R E1 T l
    let ⟨hq⟩ ← checkType R E1 (Tm.equiv T ia.ty) l
    let ⟨he⟩ ← R.check E1 e (Tm.equiv T ia.ty) l hq
    have hG := HasTy.glue ia.hty hφ hT he
    let ⟨ht⟩ ← R.check E1 t T l hT
    have hfe : HasTy S Ψ (cof Φ φ) Γ (.app (.fst e) t) ia.ty := by
      have := HasTy.app (HasTy.fst he) ht
      rwa [Tm.shift_inst] at this
    let ⟨ee⟩ ← R.conv E1 ia.ty l (HasTy.rs E hφ ia.hty) (.app (.fst e) t) a hfe (HasTy.rs E hφ ia.htm)
    pure ⟨.glue ia.ty φ T e, l, hG, HasTy.glueEl hG ht ia.htm ee⟩
  | .unglue φ e g => do
    let i ← inferUnglueArg R E φ e g
    let ⟨A, T, ⟨hA, eG⟩⟩ ← toGlueE R E i.ty i.lvl i.hty φ e
    let ⟨he⟩ ← checkEquiv R E A φ T e i.lvl
    pure ⟨A, i.lvl, hA, HasTy.unglue (HasTy.eqR eG) hA he (HasTy.conv i.htm eG)⟩
  | .tnil | .tcons .. => fail "kernel: a list is not a term"
  | .data d ps => do
    let ⟨D, ⟨_, hD⟩⟩ ← inferData R E d ps
    let ⟨hU⟩ ← univTyK E D.level
    pure ⟨.univ D.level, D.level + 1, hU, hD⟩
  | .con d c ps args rs => do
    let ⟨D, ⟨_, hD, hc⟩⟩ ← inferCon R E d c ps args rs
    pure ⟨.data d ps, D.level, hD, hc⟩
  | .elim d ps P bs t => do
    let i ← inferElimInfo R E d ps P bs
    let ⟨ht⟩ ← R.check E t (.data d ps) i.D.level i.hD
    pure ⟨P.inst t, i.m, HasTy.subst i.hP ht, i.typing ht⟩

def checkByInfer (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K (PLift (HasTy S Ψ Φ Γ t A)) := do
  let i ← R.infer E t
  bridgeHas R E i.hty hA i.htm

def checkStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K (PLift (HasTy S Ψ Φ Γ t A)) :=
  match t with
  | .lam A' b => do
    match ← whnfTy R E A l hA with
    | ⟨.pi A1 B1, e⟩ =>
      have hP := HasTy.eqR e
      if h : A' = A1 then
        let ⟨hb⟩ ← R.check (E.ext A1 l (HasTy.piDom hP)) b B1 l (HasTy.piCod hP)
        pure ⟨HasTy.conv (by rw [h]; exact HasTy.lam hP hb) (EqTm.symm e)⟩
      else
        let ⟨hA'⟩ ← checkType R E A' l
        let ⟨hU⟩ ← univTyK E l
        let ⟨eA⟩ ← R.conv E (.univ l) (l + 1) hU A' A1 hA' (HasTy.piDom hP)
        have hB := ctxConv hA' hP eA
        let ⟨hb⟩ ← R.check (E.ext A' l hA') b B1 l hB
        have e2 : EqTm S Ψ Φ Γ (.pi A' B1) (.pi A1 B1) (.univ l) := EqTm.pi eA (EqTm.refl hB)
        pure ⟨HasTy.conv (HasTy.conv (HasTy.lam (HasTy.pi hA' hB) hb) e2) (EqTm.symm e)⟩
    | ⟨T, _⟩ => fail s!"kernel: a λ cannot have type {short T}"
  | .plam b => do
    match ← whnfTy R E A l hA with
    | ⟨.path A1 a0 a1, e⟩ =>
      have hP := HasTy.eqR e
      have hL := HasTy.pathLine hP
      let ⟨hb⟩ ← R.check E.dext b A1 l hL
      let ⟨e0⟩ ← R.conv E (A1.dinst .zero) l (HasTy.dsubst hL trivial) (b.dinst .zero) a0
        (HasTy.dsubst hb trivial) (HasTy.pathLeft hP)
      let ⟨e1⟩ ← R.conv E (A1.dinst .one) l (HasTy.dsubst hL trivial) (b.dinst .one) a1
        (HasTy.dsubst hb trivial) (HasTy.pathRight hP)
      pure ⟨HasTy.conv (HasTy.plam hP hb e0 e1) (EqTm.symm e)⟩
    | ⟨.ipi A1, e⟩ =>
      have hP := HasTy.eqR e
      let ⟨hb⟩ ← R.check E.dext b A1 l (HasTy.ipiLine hP)
      pure ⟨HasTy.conv (HasTy.ilam hP hb) (EqTm.symm e)⟩
    | ⟨T, _⟩ => fail s!"kernel: a path abstraction cannot have type {short T}"
  | .pair a b => do
    match ← whnfTy R E A l hA with
    | ⟨.sigma A1 B1, e⟩ =>
      have hP := HasTy.eqR e
      let ⟨ha⟩ ← R.check E a A1 l (HasTy.sigmaDom hP)
      let ⟨hb⟩ ← R.check E b (B1.inst a) l (HasTy.subst (HasTy.sigmaCod hP) ha)
      pure ⟨HasTy.conv (HasTy.pair hP ha hb) (EqTm.symm e)⟩
    | ⟨T, _⟩ => fail s!"kernel: a pair cannot have type {short T}"
  | .split φ t1 ψ u1 => do
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨hψ⟩ ← ensureScoped ψ Ψ
    let ⟨hcov⟩ ← ensureEnt Φ (.or φ ψ)
    let ⟨h1⟩ ← R.check (E.cof φ hφ) t1 A l (HasTy.rs E hφ hA)
    let ⟨h2⟩ ← R.check (E.cof ψ hψ) u1 A l (HasTy.rs E hψ hA)
    let E2 := (E.cof φ hφ).cof ψ hψ
    let ⟨hc⟩ ← ensureEnt (cof (cof Φ φ) ψ) (cof Φ ψ)
    let ⟨e⟩ ← R.conv E2 A l (HasTy.cofcof E hφ hψ hA) t1 u1 (HasTy.rs (E.cof φ hφ) hψ h1)
      (HasTy.restrict E2.hsc hc h2)
    pure ⟨HasTy.split hφ hψ hcov hA h1 h2 e⟩
  | .abort => do
    let ⟨h⟩ ← ensureEnt Φ .zero
    pure ⟨HasTy.abort h hA⟩
  | .glueEl φ e t1 a1 => do
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨A1, T, ⟨hA1, eG⟩⟩ ← toGlueE R E A l hA φ e
    have hG := HasTy.eqR eG
    let E1 := E.cof φ hφ
    let ⟨ht⟩ ← R.check E1 t1 T l (HasTy.glueFib hG)
    let ⟨ha⟩ ← R.check E a1 A1 l hA1
    let ⟨hq⟩ ← checkType R E1 (Tm.equiv T A1) l
    let ⟨he⟩ ← R.check E1 e (Tm.equiv T A1) l hq
    have hfe : HasTy S Ψ (cof Φ φ) Γ (.app (.fst e) t1) A1 := by
      have := HasTy.app (HasTy.fst he) ht
      rwa [Tm.shift_inst] at this
    let ⟨ee⟩ ← R.conv E1 A1 l (HasTy.rs E hφ hA1) (.app (.fst e) t1) a1 hfe (HasTy.rs E hφ ha)
    pure ⟨HasTy.conv (HasTy.glueEl hG ht ha ee) (EqTm.symm eG)⟩
  | .pi B C => do
    match ← whnfTy R E A l hA with
    | ⟨.univ m, e⟩ =>
      let ⟨h1⟩ ← checkType R E B m
      let ⟨h2⟩ ← checkType R (E.ext B m h1) C m
      pure ⟨HasTy.conv (HasTy.pi h1 h2) (EqTm.symm e)⟩
    | _ => checkByInfer R E (.pi B C) A l hA
  | .sigma B C => do
    match ← whnfTy R E A l hA with
    | ⟨.univ m, e⟩ =>
      let ⟨h1⟩ ← checkType R E B m
      let ⟨h2⟩ ← checkType R (E.ext B m h1) C m
      pure ⟨HasTy.conv (HasTy.sigma h1 h2) (EqTm.symm e)⟩
    | _ => checkByInfer R E (.sigma B C) A l hA
  | .path L a b => do
    match ← whnfTy R E A l hA with
    | ⟨.univ m, e⟩ =>
      let ⟨hL⟩ ← checkType R E.dext L m
      let ⟨ha⟩ ← R.check E a (L.dinst .zero) m (HasTy.dsubst hL trivial)
      let ⟨hb⟩ ← R.check E b (L.dinst .one) m (HasTy.dsubst hL trivial)
      pure ⟨HasTy.conv (HasTy.path hL ha hb) (EqTm.symm e)⟩
    | _ => checkByInfer R E (.path L a b) A l hA
  | .ipi L => do
    match ← whnfTy R E A l hA with
    | ⟨.univ m, e⟩ =>
      let ⟨hL⟩ ← checkType R E.dext L m
      pure ⟨HasTy.conv (HasTy.ipi hL) (EqTm.symm e)⟩
    | _ => checkByInfer R E (.ipi L) A l hA
  | .glue B φ T e' => do
    match ← whnfTy R E A l hA with
    | ⟨.univ m, e⟩ =>
      let ⟨hφ⟩ ← ensureScoped φ Ψ
      let ⟨hB⟩ ← checkType R E B m
      let E1 := E.cof φ hφ
      let ⟨hT⟩ ← checkType R E1 T m
      let ⟨hq⟩ ← checkType R E1 (Tm.equiv T B) m
      let ⟨he⟩ ← R.check E1 e' (Tm.equiv T B) m hq
      pure ⟨HasTy.conv (HasTy.glue hB hφ hT he) (EqTm.symm e)⟩
    | _ => checkByInfer R E (.glue B φ T e') A l hA
  | .fst (.pair a b) => do
    -- check-mode β-redex: `(a, b).1 : A` if `a : A`
    let ⟨ha⟩ ← R.check E a A l hA
    let ib ← R.infer E b
    let ⟨hm⟩ ← ensureLvl (max l ib.lvl)
    have hB : HasTy S Ψ Φ (A :: Γ) ib.ty.shift (.univ (max l ib.lvl)) :=
      HasTy.wk hA (ib.hty.liftLe (Nat.le_max_right _ _) hm)
    have hS := HasTy.sigma (hA.liftLe (Nat.le_max_left _ _) hm) hB
    have hb : HasTy S Ψ Φ Γ b (ib.ty.shift.inst a) := by rw [Tm.shift_inst]; exact ib.htm
    pure ⟨HasTy.fst (HasTy.pair hS ha hb)⟩
  | .snd (.pair a b) => do
    let ia ← R.infer E a
    let ⟨hb⟩ ← R.check E b A l hA
    let ⟨hm⟩ ← ensureLvl (max ia.lvl l)
    have hB : HasTy S Ψ Φ (ia.ty :: Γ) A.shift (.univ (max ia.lvl l)) :=
      HasTy.wk ia.hty (hA.liftLe (Nat.le_max_right _ _) hm)
    have hS := HasTy.sigma (ia.hty.liftLe (Nat.le_max_left _ _) hm) hB
    have hb' : HasTy S Ψ Φ Γ b (A.shift.inst a) := by rw [Tm.shift_inst]; exact hb
    have := HasTy.snd (HasTy.pair hS ia.htm hb')
    pure ⟨by rw [Tm.shift_inst] at this; exact this⟩
  | .app (.lam D b) a => do
    match R.infer E (.app (.lam D b) a) with
    | .ok i => bridgeHas R E i.hty hA i.htm
    | .error _ =>
      -- check-mode β-redex with a non-dependent codomain
      let ⟨lD, ⟨hD⟩⟩ ← inferType R E D
      let ⟨ha⟩ ← R.check E a D lD hD
      let ⟨hb⟩ ← R.check (E.ext D lD hD) b A.shift l (HasTy.wk hD hA)
      let ⟨hm⟩ ← ensureLvl (max lD l)
      have hP : HasTy S Ψ Φ Γ (.pi D A.shift) (.univ (max lD l)) :=
        HasTy.pi (hD.liftLe (Nat.le_max_left _ _) hm) (HasTy.wk hD (hA.liftLe (Nat.le_max_right _ _) hm))
      have := HasTy.app (HasTy.lam hP hb) ha
      pure ⟨by rw [Tm.shift_inst] at this; exact this⟩
  | .papp (.plam b) r => do
    match R.infer E (.papp (.plam b) r) with
    | .ok i => bridgeHas R E i.hty hA i.htm
    | .error _ =>
      let ⟨hr⟩ ← ensureScoped r Ψ
      have hA' : HasTy S (Ψ + 1) Φ.shift Γ.dshift A.dshift (.univ l) := HasTy.dwk hA
      let ⟨hb⟩ ← R.check E.dext b A.dshift l hA'
      have := HasTy.iapp (HasTy.ilam (HasTy.ipi hA') hb) hr
      pure ⟨by rw [Tm.dshift_dinst] at this; exact this⟩
  | t => checkByInfer R E t A l hA

end KubusCore.Kernel
