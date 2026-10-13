import KubusCore.Kernel.Basic

/-!
# Kernel: type inference and checking

`inferStep` and `checkStep` implement one level of the bidirectional checker; recursive
calls go through the record `R`.
-/

namespace KubusCore.Kernel

variable {S : Sig}

/-- Change the cofibration of a Glue type to an equivalent one. -/
def rephi (E : KCtx S Ψ Φ Γ) (A : Tm) (φ' : I) (T e : Tm) (φ : I) (l : Nat)
    (hG : HasTy S Ψ Φ Γ (.glue A φ' T e) (.univ l)) :
    K (PLift (EqTm S Ψ Φ Γ (.glue A φ' T e) (.glue A φ T e) (.univ l))) := do
  if h : φ' = φ then return ⟨h ▸ EqTm.refl hG⟩
  let ⟨hφ⟩ ← ensureScoped φ Ψ
  let ⟨h1⟩ ← ensureEnt φ φ'
  let ⟨h2⟩ ← ensureEnt φ' φ
  let ⟨hc⟩ ← ensureEnt (cof Φ φ) (cof Φ φ')
  have hs := scoped_cof E.hsc hφ
  have hT := HasTy.restrict hs hc (HasTy.glueFib hG)
  have he := HasTy.restrict hs hc (HasTy.glueEquiv hG)
  have hG2 := HasTy.glue (HasTy.glueBase hG) hφ hT he
  return ⟨EqTm.glue hG hG2 (EqTm.refl (HasTy.glueBase hG)) h2 h1 (EqTm.refl (HasTy.glueFib hG))
    (EqTm.refl (HasTy.glueEquiv hG))⟩

/-- Infer the type of a term whose type is a Glue type with cofibration `φ`. -/
structure GlueInf (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (g : Tm) (φ : I) where
  A : Tm
  T : Tm
  e : Tm
  l : Nat
  hG : HasTy S Ψ Φ Γ (.glue A φ T e) (.univ l)
  hg : HasTy S Ψ Φ Γ g (.glue A φ T e)

/-- Bring a type `G` to the form `Glue A [φ ↦ (T, e)]` with the given `φ`. -/
def toGlue (R : Rec S) (E : KCtx S Ψ Φ Γ) (G : Tm) (l : Nat) (hG : HasTy S Ψ Φ Γ G (.univ l))
    (φ : I) : K ((A T e : Tm) × PLift (EqTm S Ψ Φ Γ G (.glue A φ T e) (.univ l))) := do
  match ← whnfTy R E G l hG with
  | ⟨.glue A φ' T e, eG⟩ =>
    let ⟨e2⟩ ← rephi E A φ' T e φ l (HasTy.eqR eG)
    pure ⟨A, T, e, ⟨EqTm.trans eG e2⟩⟩
  | ⟨G', _⟩ => fail s!"kernel: expected a Glue type, got {short G'}"

def inferGlue (R : Rec S) (E : KCtx S Ψ Φ Γ) (g : Tm) (φ : I) : K (GlueInf S Ψ Φ Γ g φ) := do
  let i ← R.infer E g
  let ⟨A, T, e, ⟨eG⟩⟩ ← toGlue R E i.ty i.lvl i.hty φ
  pure ⟨A, T, e, i.lvl, HasTy.eqR eG, HasTy.conv i.htm eG⟩

theorem HasTy.cofcof {Ψ Φ Γ t A φ ψ} (E : KCtx S Ψ Φ Γ) (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ)
    (h : HasTy S Ψ Φ Γ t A) : HasTy S Ψ (cof (cof Φ φ) ψ) Γ t A :=
  HasTy.rs (E.cof φ hφ) hψ (HasTy.rs E hφ h)

def inferStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) : (t : Tm) → K (Inf S Ψ Φ Γ t)
  | .var x =>
    match h : Γ.lookup x, hl : E.lv[x]? with
    | some A, some l => pure ⟨A, l, E.varOk x A l h hl, HasTy.var E.wf h⟩
    | _, _ => fail s!"kernel: unbound variable x{x}"
  | .const k =>
    match h : S[k]?, hl : E.sig.lv[k]? with
    | some (b, A), some l => pure ⟨A, l, E.constOk k b A l h hl, HasTy.const E.wf h⟩
    | _, _ => fail s!"kernel: unknown constant c{k}"
  | .univ l => pure ⟨.univ (l + 1), l + 2, E.univTy (l + 1), E.univTy l⟩
  | .pi A B => do
    let ⟨l1, ⟨hA⟩⟩ ← inferType R E A
    let ⟨l2, ⟨hB⟩⟩ ← inferType R (E.ext A l1 hA) B
    pure ⟨.univ (max l1 l2), max l1 l2 + 1, E.univTy _,
      HasTy.pi (hA.liftLe (Nat.le_max_left _ _)) (hB.liftLe (Nat.le_max_right _ _))⟩
  | .sigma A B => do
    let ⟨l1, ⟨hA⟩⟩ ← inferType R E A
    let ⟨l2, ⟨hB⟩⟩ ← inferType R (E.ext A l1 hA) B
    pure ⟨.univ (max l1 l2), max l1 l2 + 1, E.univTy _,
      HasTy.sigma (hA.liftLe (Nat.le_max_left _ _)) (hB.liftLe (Nat.le_max_right _ _))⟩
  | .lam _ => fail "kernel: cannot infer the type of a λ"
  | .app f a =>
    match f with
    | .lam b => do
      -- a β-redex: the domain is the type of the argument
      let ia ← R.infer E a
      let ib ← R.infer (E.ext ia.ty ia.lvl ia.hty) b
      have hpi : HasTy S Ψ Φ Γ (.pi ia.ty ib.ty) (.univ (max ia.lvl ib.lvl)) :=
        HasTy.pi (ia.hty.liftLe (Nat.le_max_left _ _)) (ib.hty.liftLe (Nat.le_max_right _ _))
      pure ⟨ib.ty.inst a, ib.lvl, HasTy.subst ib.hty ia.htm, HasTy.app (HasTy.lam hpi ib.htm) ia.htm⟩
    | f => do
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
    have hB : HasTy S Ψ Φ (ia.ty :: Γ) ib.ty.shift (.univ (max ia.lvl ib.lvl)) :=
      HasTy.wk ia.hty (ib.hty.liftLe (Nat.le_max_right _ _))
    have hS := HasTy.sigma (ia.hty.liftLe (Nat.le_max_left _ _)) hB
    have hb : HasTy S Ψ Φ Γ b (ib.ty.shift.inst a) := by rw [Tm.shift_inst]; exact ib.htm
    pure ⟨.sigma ia.ty ib.ty.shift, max ia.lvl ib.lvl, hS, HasTy.pair hS ia.htm hb⟩
  | .path A a b => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E.dext A
    let ⟨ha⟩ ← R.check E a (A.dinst .zero) l (HasTy.dsubst hA trivial)
    let ⟨hb⟩ ← R.check E b (A.dinst .one) l (HasTy.dsubst hA trivial)
    pure ⟨.univ l, l + 1, E.univTy l, HasTy.path hA ha hb⟩
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
    pure ⟨.univ l, l + 1, E.univTy l, HasTy.ipi hA⟩
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
    let E1 := E.cof φ hφ
    let ⟨hT⟩ ← checkType R E1 T l
    let ⟨le, ⟨hEq⟩⟩ ← inferType R E1 (Tm.equiv T A)
    let ⟨he⟩ ← R.check E1 e (Tm.equiv T A) le hEq
    pure ⟨.univ l, l + 1, E.univTy l, HasTy.glue hA hφ hT he⟩
  | .glueEl .. => fail "kernel: cannot infer the type of glue"
  | .unglue φ g => do
    let gi ← inferGlue R E g φ
    pure ⟨gi.A, gi.l, HasTy.glueBase gi.hG, HasTy.unglue gi.hG gi.hg⟩

def checkStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K (PLift (HasTy S Ψ Φ Γ t A)) :=
  match t with
  | .lam b => do
    match ← whnfTy R E A l hA with
    | ⟨.pi A1 B1, e⟩ =>
      have hP := HasTy.eqR e
      let ⟨hb⟩ ← R.check (E.ext A1 l (HasTy.piDom hP)) b B1 l (HasTy.piCod hP)
      pure ⟨HasTy.conv (HasTy.lam hP hb) (EqTm.symm e)⟩
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
  | .glueEl φ t1 a1 => do
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨A1, T, e, ⟨eG⟩⟩ ← toGlue R E A l hA φ
    have hG := HasTy.eqR eG
    let E1 := E.cof φ hφ
    let ⟨ht⟩ ← R.check E1 t1 T l (HasTy.glueFib hG)
    let ⟨ha⟩ ← R.check E a1 A1 l (HasTy.glueBase hG)
    have hfe : HasTy S Ψ (cof Φ φ) Γ (.app (.fst e) t1) A1 := by
      have := HasTy.app (HasTy.fst (HasTy.glueEquiv hG)) ht
      rwa [Tm.shift_inst] at this
    let ⟨ee⟩ ← R.conv E1 A1 l (HasTy.rs E hφ (HasTy.glueBase hG)) (.app (.fst e) t1) a1 hfe
      (HasTy.rs E hφ ha)
    pure ⟨HasTy.conv (HasTy.glueEl hG ht ha ee) (EqTm.symm eG)⟩
  | t => do
    let i ← R.infer E t
    bridgeHas R E i.hty hA i.htm

end KubusCore.Kernel
