import KubusCore.Kernel.Whnf

/-!
# Kernel: conversion

`convStep` decides `t ≡ u : A`. It first splits the restriction `Φ` into its faces
(`EqTm.local`), substitutes the endpoints fixed by the face (`EqTm.face`), and then compares
type-directedly: η for Π, Σ, PathP, `(i : I) → A` and Glue, structural comparison of types,
and comparison of neutral terms (`convNeStep`) after weak-head reduction.
-/

namespace KubusCore.Kernel

variable {S : Sig}

/-! ## Faces of a cofibration -/

/-- `d ⊆ c` as constraint sets: the face `c` lies in the face `d`. -/
def faceLe (d c : I.Face) : Bool := d.all (c.contains ·)

/-- The maximal faces of `Φ`. -/
def canonFaces (Φ : I) : List I.Face :=
  (Φ.faces.foldl (fun acc c =>
    if acc.any (fun d => faceLe d c) then acc else c :: acc.filter (fun d => !faceLe c d)) []).reverse

def litLt (a b : Nat × Bool) : Bool := a.1 < b.1 || (a.1 == b.1 && !a.2 && b.2)

/-- A face with sorted, distinct literals. -/
def normFace (α : I.Face) : I.Face := (α.mergeSort fun a b => !litLt b a).eraseDups

/-- The canonical form of a cofibration: the disjunction of its maximal faces. -/
def canonPhi (Φ : I) : I := I.ofFaces ((canonFaces Φ).map normFace)

/-- Substitute the endpoints of the face `α` into `t` (for variables that occur). -/
def faceSubst {Ψ Φ Γ} (A : Tm) (t0 : Tm) : I.Face → (t : Tm) → EqTm S Ψ Φ Γ t0 t A →
    K (Red S Ψ Φ Γ t0 A)
  | [], t, e => pure ⟨t, e⟩
  | (i, d) :: α, t, e =>
    if hi : i < Ψ ∧ t.mentionsI i = true then
      if hent : I.Entails Φ (I.lit i d) then
        faceSubst A t0 α _ (EqTm.trans e (EqTm.face hi.1 hent (HasTy.eqR e)))
      else faceSubst A t0 α t e
    else faceSubst A t0 α t e

/-! ## Context conversion for the codomain of Π and Σ -/

theorem ctxConvPi {Ψ Φ Γ A1 B1 A2 B2 m} (hX : HasTy S Ψ Φ Γ (.pi A1 B1) (.univ m))
    (hY : HasTy S Ψ Φ Γ (.pi A2 B2) (.univ m)) (eA : EqTm S Ψ Φ Γ A1 A2 (.univ m)) :
    HasTy S Ψ Φ (A1 :: Γ) B2 (.univ m) := by
  have hD := HasTy.piDom hX
  have h1 : HasTy S Ψ Φ (A1 :: Γ) (.pi A2.shift (B2.ren (Tm.upRen Nat.succ) id)) (.univ m) :=
    HasTy.wk hD hY
  have hv : HasTy S Ψ Φ (A1 :: Γ) (.var 0) A2.shift :=
    HasTy.conv (HasTy.var (Wf.cons hD) rfl) (EqTm.wk hD eA)
  have := HasTy.subst (HasTy.piCod h1) hv
  rwa [Tm.upShift_inst0] at this

theorem ctxConvSigma {Ψ Φ Γ A1 B1 A2 B2 m} (hX : HasTy S Ψ Φ Γ (.sigma A1 B1) (.univ m))
    (hY : HasTy S Ψ Φ Γ (.sigma A2 B2) (.univ m)) (eA : EqTm S Ψ Φ Γ A1 A2 (.univ m)) :
    HasTy S Ψ Φ (A1 :: Γ) B2 (.univ m) := by
  have hD := HasTy.sigmaDom hX
  have h1 : HasTy S Ψ Φ (A1 :: Γ) (.sigma A2.shift (B2.ren (Tm.upRen Nat.succ) id)) (.univ m) :=
    HasTy.wk hD hY
  have hv : HasTy S Ψ Φ (A1 :: Γ) (.var 0) A2.shift :=
    HasTy.conv (HasTy.var (Wf.cons hD) rfl) (EqTm.wk hD eA)
  have := HasTy.subst (HasTy.sigmaCod h1) hv
  rwa [Tm.upShift_inst0] at this

/-- Both terms are spines (applications, path applications, projections) of the same constant. -/
def constHead : Tm → Option Nat
  | .app f _ | .papp f _ | .fst f | .snd f => constHead f
  | .const k => some k
  | _ => none

def sameConstHead (t u : Tm) : Bool :=
  match constHead t, constHead u with
  | some k, some k' => k == k'
  | _, _ => false

/-- The first projection of `t`, contracted if `t` is a pair. -/
def projFst {Ψ Φ Γ} (t A : Tm) (h : HasTy S Ψ Φ Γ (.fst t) A) : Red S Ψ Φ Γ (.fst t) A :=
  match t, h with
  | .pair a _, h => ⟨a, EqTm.fstBeta h⟩
  | t, h => ⟨.fst t, EqTm.refl h⟩

/-- The second projection of `t`, contracted if `t` is a pair. -/
def projSnd {Ψ Φ Γ} (t A : Tm) (h : HasTy S Ψ Φ Γ (.snd t) A) : Red S Ψ Φ Γ (.snd t) A :=
  match t, h with
  | .pair _ b, h => ⟨b, EqTm.sndBeta h⟩
  | t, h => ⟨.snd t, EqTm.refl h⟩

/-- Unfold the head constant of a spine once, and contract the β-redexes this exposes along the
spine, without reducing further. Returns the inferred type of the spine. -/
def unfoldHead (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    (t : Tm) → K (Option ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty))
  | .const k =>
    match h : S[k]?, hl : E.sig.lv[k]? with
    | some (.defn b Ak), some lk =>
      pure (some ⟨⟨Ak, lk, E.constOk k b Ak lk h hl, HasTy.const E.wf h⟩,
        ⟨b, EqTm.delta (HasTy.const E.wf h) h⟩⟩)
    | _, _ => pure none
  | .app f a => do
    match ← unfoldHead R E f with
    | none => pure none
    | some ⟨fi, fr⟩ =>
      match ← whnfTy R E fi.ty fi.lvl fi.hty with
      | ⟨.pi A1 B1, eF⟩ =>
        have hP := HasTy.eqR eF
        let ⟨ha⟩ ← R.check E a A1 fi.lvl (HasTy.piDom hP)
        let inf : Inf S Ψ Φ Γ (.app f a) :=
          ⟨B1.inst a, fi.lvl, HasTy.subst (HasTy.piCod hP) ha, HasTy.app (HasTy.conv fi.htm eF) ha⟩
        have e1 : EqTm S Ψ Φ Γ (.app f a) (.app fr.tm a) (B1.inst a) :=
          EqTm.app (EqTm.conv fr.eq eF) (EqTm.refl ha)
        match h : fr.tm with
        | .lam D b =>
          have e1' : EqTm S Ψ Φ Γ (.app f a) (.app (.lam D b) a) (B1.inst a) := h ▸ e1
          pure (some ⟨inf, ⟨_, EqTm.trans e1' (EqTm.piBeta (HasTy.eqR e1'))⟩⟩)
        | f' => pure (some ⟨inf, ⟨.app f' a, h ▸ e1⟩⟩)
      | _ => pure none
  | .papp p r => do
    match ← unfoldHead R E p with
    | none => pure none
    | some ⟨pi, pr⟩ =>
      let ⟨hr⟩ ← ensureScoped r Ψ
      match ← whnfTy R E pi.ty pi.lvl pi.hty with
      | ⟨.path A1 _ _, eP⟩ =>
        have hP := HasTy.eqR eP
        have hp := HasTy.conv pi.htm eP
        let inf : Inf S Ψ Φ Γ (.papp p r) :=
          ⟨A1.dinst r, pi.lvl, HasTy.dsubst (HasTy.pathLine hP) hr, HasTy.papp hp hr⟩
        have e1 : EqTm S Ψ Φ Γ (.papp p r) (.papp pr.tm r) (A1.dinst r) :=
          EqTm.papp (EqTm.conv pr.eq eP) hr hr (fun _ => rfl)
        match h : pr.tm with
        | .plam b =>
          have e1' : EqTm S Ψ Φ Γ (.papp p r) (.papp (.plam b) r) (A1.dinst r) := h ▸ e1
          pure (some ⟨inf, ⟨_, EqTm.trans e1' (EqTm.pathBeta (HasTy.eqR e1'))⟩⟩)
        | p' => pure (some ⟨inf, ⟨.papp p' r, h ▸ e1⟩⟩)
      | ⟨.ipi A1, eP⟩ =>
        have hP := HasTy.eqR eP
        have hp := HasTy.conv pi.htm eP
        let inf : Inf S Ψ Φ Γ (.papp p r) :=
          ⟨A1.dinst r, pi.lvl, HasTy.dsubst (HasTy.ipiLine hP) hr, HasTy.iapp hp hr⟩
        have e1 : EqTm S Ψ Φ Γ (.papp p r) (.papp pr.tm r) (A1.dinst r) :=
          EqTm.iapp (EqTm.conv pr.eq eP) hr hr (fun _ => rfl)
        match h : pr.tm with
        | .plam b =>
          have e1' : EqTm S Ψ Φ Γ (.papp p r) (.papp (.plam b) r) (A1.dinst r) := h ▸ e1
          pure (some ⟨inf, ⟨_, EqTm.trans e1' (EqTm.pathBeta (HasTy.eqR e1'))⟩⟩)
        | p' => pure (some ⟨inf, ⟨.papp p' r, h ▸ e1⟩⟩)
      | _ => pure none
  | _ => pure none

section
variable (R : Rec S) {Ψ : Nat} {Φ : I} {Γ : Ctx} (E : KCtx S Ψ Φ Γ)

/-- Lazy δ: compare `t ≡ u` (both of type `A`) by unfolding the head constant defined later
first, and comparing again; `none` if neither side has a constant head or nothing matched. -/
def lazyDelta (A : Tm) (l : Nat) (hA : HasTy S Ψ Φ Γ A (.univ l)) :
    Nat → (t u : Tm) → HasTy S Ψ Φ Γ t A → HasTy S Ψ Φ Γ u A →
    K (Option (PLift (EqTm S Ψ Φ Γ t u A)))
  | 0, _, _, _, _ => pure none
  | n + 1, t, u, ht, hu => do
    if h : t = u then return some ⟨h ▸ EqTm.refl ht⟩
    if sameConstHead t u then
      if let .ok ⟨ni, ⟨en⟩⟩ := R.convNe E t u then
        if let .ok ⟨en'⟩ := bridge R E ni.hty hA en then return some ⟨en'⟩
    let unfoldLeft := match constHead t, constHead u with
      | some k, some k' => decide (k' ≤ k)
      | some _, none => true
      | _, _ => false
    let unfoldRight := match constHead t, constHead u with
      | some k, some k' => decide (k ≤ k')
      | none, some _ => true
      | _, _ => false
    if unfoldLeft then
      if let some ⟨ti, tr⟩ ← unfoldHead R E t then
        let ⟨et⟩ ← bridge R E ti.hty hA tr.eq
        if let some ⟨e⟩ ← lazyDelta A l hA n tr.tm u (HasTy.eqR et) hu then
          return some ⟨EqTm.trans et e⟩
        return none
    if unfoldRight then
      if let some ⟨ui, ur⟩ ← unfoldHead R E u then
        let ⟨eu⟩ ← bridge R E ui.hty hA ur.eq
        if let some ⟨e⟩ ← lazyDelta A l hA n t ur.tm ht (HasTy.eqR eu) then
          return some ⟨EqTm.trans e (EqTm.symm eu)⟩
        return none
    pure none

def convTyData (m d : Nat) (ps ps' : Tm) (hm : m + 1 ≤ maxLevel) :
    K (PLift (EqTm S Ψ Φ Γ (.data d ps) (.data d ps') (.univ m))) := do
  let ⟨D, ⟨hS, hD⟩⟩ ← inferData R E d ps
  let ⟨D', ⟨hS', hD'⟩⟩ ← inferData R E d ps'
  have hDD : D' = D := by rw [hS] at hS'; cases hS'; rfl
  let ⟨e⟩ ← convTele R E ps ps' D.params []
  if hl : D.level ≤ m then pure ⟨(EqTm.data hS hD (hDD ▸ hD') e).liftLe hl (Nat.le_of_succ_le hm)⟩
  else fail "kernel: universe level mismatch"

/-- Structural comparison of two types in weak-head normal form. -/
def convTyWhnf (m : Nat) (X Y : Tm) (hX : HasTy S Ψ Φ Γ X (.univ m))
    (hY : HasTy S Ψ Φ Γ Y (.univ m)) : K (PLift (EqTm S Ψ Φ Γ X Y (.univ m))) :=
  if h : X = Y then pure ⟨h ▸ EqTm.refl hX⟩ else do
  let ⟨hm⟩ ← ensureLvl (m + 1)
  match X, Y, hX, hY with
  | .pi A1 B1, .pi A2 B2, hX, hY => do
    let ⟨eA⟩ ← R.conv E (.univ m) (m + 1) (E.univTy m hm) A1 A2 (HasTy.piDom hX) (HasTy.piDom hY)
    let ⟨eB⟩ ← R.conv (E.ext A1 m (HasTy.piDom hX)) (.univ m) (m + 1)
      (HasTy.univ hm (Wf.cons (HasTy.piDom hX))) B1 B2 (HasTy.piCod hX) (ctxConvPi hX hY eA)
    pure ⟨EqTm.pi eA eB⟩
  | .sigma A1 B1, .sigma A2 B2, hX, hY => do
    let ⟨eA⟩ ← R.conv E (.univ m) (m + 1) (E.univTy m hm) A1 A2 (HasTy.sigmaDom hX) (HasTy.sigmaDom hY)
    let ⟨eB⟩ ← R.conv (E.ext A1 m (HasTy.sigmaDom hX)) (.univ m) (m + 1)
      (HasTy.univ hm (Wf.cons (HasTy.sigmaDom hX))) B1 B2 (HasTy.sigmaCod hX) (ctxConvSigma hX hY eA)
    pure ⟨EqTm.sigma eA eB⟩
  | .path A1 a1 b1, .path A2 a2 b2, hX, hY => do
    let ⟨eA⟩ ← R.conv E.dext (.univ m) (m + 1) (E.dext.univTy m hm) A1 A2 (HasTy.pathLine hX)
      (HasTy.pathLine hY)
    have e0 : EqTm S Ψ Φ Γ (A1.dinst .zero) (A2.dinst .zero) (.univ m) := EqTm.dsubst eA trivial
    have e1 : EqTm S Ψ Φ Γ (A1.dinst .one) (A2.dinst .one) (.univ m) := EqTm.dsubst eA trivial
    let ⟨ea⟩ ← R.conv E (A1.dinst .zero) m (HasTy.dsubst (HasTy.pathLine hX) trivial) a1 a2
      (HasTy.pathLeft hX) (HasTy.conv (HasTy.pathLeft hY) (EqTm.symm e0))
    let ⟨eb⟩ ← R.conv E (A1.dinst .one) m (HasTy.dsubst (HasTy.pathLine hX) trivial) b1 b2
      (HasTy.pathRight hX) (HasTy.conv (HasTy.pathRight hY) (EqTm.symm e1))
    pure ⟨EqTm.path eA ea eb⟩
  | .ipi A1, .ipi A2, hX, hY => do
    let ⟨eA⟩ ← R.conv E.dext (.univ m) (m + 1) (E.dext.univTy m hm) A1 A2 (HasTy.ipiLine hX)
      (HasTy.ipiLine hY)
    pure ⟨EqTm.ipi eA⟩
  | .glue A1 φ1 T1 e1, .glue A2 φ2 T2 e2, hX, hY => do
    let ⟨hA1⟩ ← checkType R E A1 m
    let ⟨hA2⟩ ← checkType R E A2 m
    let ⟨eA⟩ ← R.conv E (.univ m) (m + 1) (E.univTy m hm) A1 A2 hA1 hA2
    let ⟨h12⟩ ← ensureEnt φ1 φ2
    let ⟨h21⟩ ← ensureEnt φ2 φ1
    let ⟨hφ1⟩ ← ensureScoped φ1 Ψ
    let E1 := E.cof φ1 hφ1
    let ⟨hc⟩ ← ensureEnt (cof Φ φ1) (cof Φ φ2)
    let ⟨eT⟩ ← R.conv E1 (.univ m) (m + 1) (E1.univTy m hm) T1 T2 (HasTy.glueFib hX)
      (HasTy.restrict E1.hsc hc (HasTy.glueFib hY))
    let ⟨l1, ⟨hq1⟩⟩ ← inferType R E1 (Tm.equiv T1 A1)
    let ⟨l2, ⟨hq2⟩⟩ ← inferType R E1 (Tm.equiv T2 A2)
    let ⟨eq⟩ ← convTy R E1 (Tm.equiv T2 A2) (Tm.equiv T1 A1) l2 l1 hq2 hq1
    let ⟨he1⟩ ← R.check E1 e1 (Tm.equiv T1 A1) l1 hq1
    let ⟨he2⟩ ← R.check E1 e2 (Tm.equiv T2 A2) l2 hq2
    let ⟨ee⟩ ← R.conv E1 (Tm.equiv T1 A1) l1 hq1 e1 e2 he1 (HasTy.conv he2 eq)
    pure ⟨EqTm.glue hX hY eA h12 h21 eT ee⟩
  | .data d ps, .data d' ps', hX, hY =>
    if hd : d' = d then by subst hd; exact convTyData R E m d' ps ps' hm
    else fail s!"kernel: different inductive types D{d} and D{d'}"
  | X, Y, _, _ => do
    let ⟨ni, ⟨en⟩⟩ ← R.convNe E X Y
    bridge R E ni.hty (E.univTy m hm) en

/-- Compare two types. -/
def convTypes (m : Nat) (X Y : Tm) (hX : HasTy S Ψ Φ Γ X (.univ m))
    (hY : HasTy S Ψ Φ Γ Y (.univ m)) : K (PLift (EqTm S Ψ Φ Γ X Y (.univ m))) := do
  let rX ← whnfTy R E X m hX
  let rY ← whnfTy R E Y m hY
  let ⟨e⟩ ← convTyWhnf R E m rX.tm rY.tm (HasTy.eqR rX.eq) (HasTy.eqR rY.eq)
  pure ⟨EqTm.trans rX.eq (EqTm.trans e (EqTm.symm rY.eq))⟩

/-- Type-directed comparison at a type in weak-head normal form. -/
def convAt (A : Tm) (l : Nat) (hA : HasTy S Ψ Φ Γ A (.univ l)) (t u : Tm)
    (ht : HasTy S Ψ Φ Γ t A) (hu : HasTy S Ψ Φ Γ u A) : K (PLift (EqTm S Ψ Φ Γ t u A)) :=
  match A, hA, ht, hu with
  | .pi A1 B1, hP, ht, hu => do
    have hD := HasTy.piDom hP
    let E1 := E.ext A1 l hD
    have hv : HasTy S Ψ Φ (A1 :: Γ) (.var 0) A1.shift := HasTy.var E1.wf rfl
    have ht1 : HasTy S Ψ Φ (A1 :: Γ) (.app t.shift (.var 0)) B1 := by
      have := HasTy.app (B := B1.ren (Tm.upRen Nat.succ) id) (HasTy.wk hD ht) hv
      rwa [Tm.upShift_inst0] at this
    have hu1 : HasTy S Ψ Φ (A1 :: Γ) (.app u.shift (.var 0)) B1 := by
      have := HasTy.app (B := B1.ren (Tm.upRen Nat.succ) id) (HasTy.wk hD hu) hv
      rwa [Tm.upShift_inst0] at this
    let ⟨eb⟩ ← R.conv E1 B1 l (HasTy.piCod hP) _ _ ht1 hu1
    pure ⟨EqTm.trans (EqTm.piEta ht) (EqTm.trans (EqTm.lam hP eb) (EqTm.symm (EqTm.piEta hu)))⟩
  | .sigma A1 B1, hP, ht, hu => do
    have hft := HasTy.fst ht
    let rft := projFst t A1 hft
    let rfu := projFst u A1 (HasTy.fst hu)
    let ⟨e1'⟩ ← R.conv E A1 l (HasTy.sigmaDom hP) _ _ (HasTy.eqR rft.eq) (HasTy.eqR rfu.eq)
    have e1 := EqTm.trans rft.eq (EqTm.trans e1' (EqTm.symm rfu.eq))
    have hC := HasTy.sigmaCod hP
    have hsu : HasTy S Ψ Φ Γ (.snd u) (B1.inst (.fst t)) :=
      HasTy.conv (HasTy.snd hu) (EqTm.subst (EqTm.refl hC) (EqTm.symm e1))
    let rst := projSnd t _ (HasTy.snd ht)
    let rsu := projSnd u _ hsu
    let ⟨e2'⟩ ← R.conv E (B1.inst (.fst t)) l (HasTy.subst hC hft) _ _ (HasTy.eqR rst.eq)
      (HasTy.eqR rsu.eq)
    have e2 := EqTm.trans rst.eq (EqTm.trans e2' (EqTm.symm rsu.eq))
    pure ⟨EqTm.trans (EqTm.sigmaEta ht)
      (EqTm.trans (EqTm.pair hP e1 e2) (EqTm.symm (EqTm.sigmaEta hu)))⟩
  | .path A1 a0 a1, hP, ht, hu => do
    have hr : I.Scoped (Ψ + 1) (.var 0) := Nat.zero_lt_succ _
    have ht1 : HasTy S (Ψ + 1) Φ.shift Γ.dshift (.papp t.dshift (.var 0)) A1 := by
      have := HasTy.papp (A := A1.ren id (Tm.upRen Nat.succ)) (HasTy.dwk ht) hr
      rwa [Tm.upDShift_dinst0] at this
    have hu1 : HasTy S (Ψ + 1) Φ.shift Γ.dshift (.papp u.dshift (.var 0)) A1 := by
      have := HasTy.papp (A := A1.ren id (Tm.upRen Nat.succ)) (HasTy.dwk hu) hr
      rwa [Tm.upDShift_dinst0] at this
    let ⟨eb⟩ ← R.conv E.dext A1 l (HasTy.pathLine hP) _ _ ht1 hu1
    pure ⟨EqTm.trans (EqTm.pathEta ht) (EqTm.trans
      (EqTm.plam hP (HasTy.eqR (EqTm.pathEta ht)) (HasTy.eqR (EqTm.pathEta hu)) eb)
      (EqTm.symm (EqTm.pathEta hu)))⟩
  | .ipi A1, hP, ht, hu => do
    have hr : I.Scoped (Ψ + 1) (.var 0) := Nat.zero_lt_succ _
    have ht1 : HasTy S (Ψ + 1) Φ.shift Γ.dshift (.papp t.dshift (.var 0)) A1 := by
      have := HasTy.iapp (A := A1.ren id (Tm.upRen Nat.succ)) (HasTy.dwk ht) hr
      rwa [Tm.upDShift_dinst0] at this
    have hu1 : HasTy S (Ψ + 1) Φ.shift Γ.dshift (.papp u.dshift (.var 0)) A1 := by
      have := HasTy.iapp (A := A1.ren id (Tm.upRen Nat.succ)) (HasTy.dwk hu) hr
      rwa [Tm.upDShift_dinst0] at this
    let ⟨eb⟩ ← R.conv E.dext A1 l (HasTy.ipiLine hP) _ _ ht1 hu1
    pure ⟨EqTm.trans (EqTm.ipiEta ht) (EqTm.trans (EqTm.ilam hP eb) (EqTm.symm (EqTm.ipiEta hu)))⟩
  | .glue A1 φ T e, hP, ht, hu => do
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨hA1⟩ ← checkType R E A1 l
    let ⟨he⟩ ← checkEquiv R E A1 φ T e l
    let ⟨e1⟩ ← R.conv E A1 l hA1 _ _ (HasTy.unglue hP hA1 he ht) (HasTy.unglue hP hA1 he hu)
    have eGT : EqTm S Ψ (cof Φ φ) Γ (.glue A1 φ T e) T (.univ l) :=
      EqTm.glueFace (I.entails_and_right Φ φ) (HasTy.rs E hφ hP)
    let ⟨e2⟩ ← R.conv (E.cof φ hφ) T l (HasTy.glueFib hP) t u (HasTy.conv (HasTy.rs E hφ ht) eGT)
      (HasTy.conv (HasTy.rs E hφ hu) eGT)
    have e := EqTm.glueEl (HasTy.eqR (EqTm.glueEta ht)) (HasTy.eqR (EqTm.glueEta hu))
      (I.entails_refl φ) (I.entails_refl φ) e2 e1
    pure ⟨EqTm.trans (EqTm.glueEta ht) (EqTm.trans e (EqTm.symm (EqTm.glueEta hu)))⟩
  | .univ m, _, ht, hu => convTypes R E m t u ht hu
  | A, hA, ht, hu => do
    -- lazy δ: unfold the head constant defined later first
    if let .ok (some e) := lazyDelta R E A l hA 20 t u ht hu then return e
    let rt ← R.whnf E t A l hA ht
    let ru ← R.whnf E u A l hA hu
    if h : rt.tm = ru.tm then
      return ⟨EqTm.trans rt.eq (EqTm.symm (h ▸ ru.eq))⟩
    let ⟨ni, ⟨en⟩⟩ ← (R.convNe E rt.tm ru.tm).mapError (· ++ s!"\n  at type {short A}")
    let ⟨en'⟩ ← bridge R E ni.hty hA en
    pure ⟨EqTm.trans rt.eq (EqTm.trans en' (EqTm.symm ru.eq))⟩

/-- Comparison under a single face `α` of the restriction. -/
def convFace (A : Tm) (l : Nat) (hA : HasTy S Ψ Φ Γ A (.univ l)) (t u : Tm)
    (ht : HasTy S Ψ Φ Γ t A) (hu : HasTy S Ψ Φ Γ u A) (α : I.Face) :
    K (PLift (EqTm S Ψ Φ Γ t u A)) := do
  let rt ← faceSubst A t α t (EqTm.refl ht)
  let ru ← faceSubst A u α u (EqTm.refl hu)
  if h : rt.tm = ru.tm then
    return ⟨EqTm.trans rt.eq (EqTm.symm (h ▸ ru.eq))⟩
  let rA ← whnfTy R E A l hA
  have hA' := HasTy.eqR rA.eq
  let ⟨e⟩ ← convAt R E rA.tm l hA' rt.tm ru.tm (HasTy.conv (HasTy.eqR rt.eq) rA.eq)
    (HasTy.conv (HasTy.eqR ru.eq) rA.eq)
  pure ⟨EqTm.trans rt.eq (EqTm.trans (EqTm.conv e (EqTm.symm rA.eq)) (EqTm.symm ru.eq))⟩

end

def convStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (t u : Tm) (ht : HasTy S Ψ Φ Γ t A)
    (hu : HasTy S Ψ Φ Γ u A) : K (PLift (EqTm S Ψ Φ Γ t u A)) := do
  if h : t = u then return ⟨h ▸ EqTm.refl ht⟩
  match canonFaces Φ with
  | [] =>
    let ⟨h0⟩ ← ensureEnt Φ .zero
    pure ⟨EqTm.absurd h0 ht hu⟩
  | [α] =>
    let Φ' := I.ofFace α
    if Φ' = Φ then convFace R E A l hA t u ht hu α
    else
      let ⟨h1⟩ ← ensureEnt Φ' Φ
      let ⟨h2⟩ ← ensureEnt Φ Φ'
      let ⟨hs⟩ ← ensureScoped Φ' Ψ
      let ⟨e⟩ ← convFace R (E.restrict Φ' hs h1) A l (HasTy.restrict hs h1 hA) t u
        (HasTy.restrict hs h1 ht) (HasTy.restrict hs h1 hu) α
      pure ⟨EqTm.restrict E.hsc h2 e⟩
  | α :: rest =>
    let φ := I.ofFace α
    let ψ := I.ofFaces rest
    let ⟨hφ⟩ ← ensureScoped φ Ψ
    let ⟨hψ⟩ ← ensureScoped ψ Ψ
    let ⟨hcov⟩ ← ensureEnt Φ (.or φ ψ)
    let ⟨e1⟩ ← R.conv (E.cof φ hφ) A l (HasTy.rs E hφ hA) t u (HasTy.rs E hφ ht) (HasTy.rs E hφ hu)
    let ⟨e2⟩ ← R.conv (E.cof ψ hψ) A l (HasTy.rs E hψ hA) t u (HasTy.rs E hψ ht) (HasTy.rs E hψ hu)
    pure ⟨EqTm.local hφ hψ hcov ht hu e1 e2⟩

def convNeUnglue (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (φ : I) (e g : Tm) (φ' : I) (g' : Tm) :
    K ((i : Inf S Ψ Φ Γ (.unglue φ e g)) × PLift (EqTm S Ψ Φ Γ (.unglue φ e g) (.unglue φ' e g') i.ty)) := do
  let ⟨gi, ⟨eg⟩⟩ ← R.convNe E g g'
  let ⟨A1, T, ⟨hA1, eG⟩⟩ ← toGlueE R E gi.ty gi.lvl gi.hty φ e
  have hG := HasTy.eqR eG
  have eg2 := EqTm.conv eg eG
  let ⟨h1⟩ ← ensureEnt φ φ'
  let ⟨h2⟩ ← ensureEnt φ' φ
  let ⟨he⟩ ← checkEquiv R E A1 φ T e gi.lvl
  let ⟨he'⟩ ← checkEquiv R E A1 φ' T e gi.lvl
  let ⟨eG'⟩ ← reglue R E A1 φ T e φ' e gi.lvl hG hA1
  have hu := HasTy.unglue (HasTy.eqR eG') hA1 he' (HasTy.conv (HasTy.eqR eg2) eG')
  return ⟨⟨A1, gi.lvl, hA1, HasTy.unglue hG hA1 he (HasTy.conv gi.htm eG)⟩,
    ⟨EqTm.unglue (HasTy.unglue hG hA1 he (HasTy.conv gi.htm eG)) hu h1 h2 eg2⟩⟩

def convNeCon (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d c : Nat) (ps args : Tm) (rs : List I)
    (ps' args' : Tm) (rs' : List I) :
    K ((i : Inf S Ψ Φ Γ (.con d c ps args rs)) ×
      PLift (EqTm S Ψ Φ Γ (.con d c ps args rs) (.con d c ps' args' rs') i.ty)) := do
  let ⟨D, ⟨hS, hD, h1⟩⟩ ← inferCon R E d c ps args rs
  let ⟨C, ⟨hC⟩⟩ ← lookupCtor D c
  let ⟨h2⟩ ← R.check E (.con d c ps' args' rs') (.data d ps) D.level hD
  let ⟨eps⟩ ← convTele R E ps ps' D.params []
  let ⟨eas⟩ ← convTele R E args args' (C.argTys d D.params.length) ps.toList.reverse
  if hlen : rs.length = rs'.length then
    let ⟨hrs⟩ ← forallPairs0 rs rs' (fun _ r r' => I.Eq r r') fun _ r r' _ _ => ensureIEq r r'
    return ⟨⟨_, D.level, hD, h1⟩, ⟨EqTm.con hS hC h1 h2 eps eas hlen hrs⟩⟩
  else fail "kernel: interval arguments differ in number"

def convNeElim (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d : Nat) (ps P bs t ps' P' bs' t' : Tm) :
    K ((i : Inf S Ψ Φ Γ (.elim d ps P bs t)) ×
      PLift (EqTm S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps' P' bs' t') i.ty)) := do
  let info ← inferElimInfo R E d ps P bs
  let ⟨ht⟩ ← R.check E t (.data d ps) info.D.level info.hD
  have h1 := info.typing ht
  have hT := HasTy.subst info.hP ht
  let ⟨h2⟩ ← R.check E (.elim d ps' P' bs' t') (P.inst t) info.m hT
  let ⟨eps⟩ ← convTele R E ps ps' info.D.params []
  let Ex := E.ext (.data d ps) info.D.level info.hD
  let ⟨hU⟩ ← univTyK Ex info.m
  let ⟨hP'⟩ ← checkType R Ex P' info.m
  let ⟨eP⟩ ← R.conv Ex (.univ info.m) (info.m + 1) hU P P' info.hP hP'
  if hlen : bs.toList.length = bs'.toList.length then
    let ⟨hbr⟩ ← forallPairs0 bs.toList bs'.toList
      (fun c b b' => ∀ C, info.D.ctors[c]? = some C → EqTm S Ψ Φ Γ b b' (info.D.branchTy d c C ps P))
      fun c b b' hb _ => do
        match getIdx' info.D.ctors c with
        | .inl ⟨C, ⟨hC⟩⟩ =>
          let ⟨l, ⟨hB⟩⟩ ← inferType R E (info.D.branchTy d c C ps P)
          let ⟨hb1⟩ ← R.check E b _ l hB
          let ⟨hb2⟩ ← R.check E b' _ l hB
          let ⟨e⟩ ← R.conv E _ l hB b b' hb1 hb2
          pure ⟨fun C' hC' => by rw [hC] at hC'; cases hC'; exact e⟩
        | .inr ⟨hC⟩ => pure ⟨fun C' hC' => by rw [hC] at hC'; cases hC'⟩
    let ⟨ht'⟩ ← R.check E t' (.data d ps) info.D.level info.hD
    let ⟨et⟩ ← R.conv E _ info.D.level info.hD t t' ht ht'
    return ⟨⟨_, info.m, hT, h1⟩, ⟨EqTm.elim info.hS h1 h2 eps eP hlen
      (fun c C b b' hC hb hb' => hbr c b b' hb hb' C hC) et⟩⟩
  else fail "kernel: different numbers of branches"

/-- Comparison of neutral terms in weak-head normal form; returns the type of the first. -/
def convNeStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t u : Tm) :
    K ((i : Inf S Ψ Φ Γ t) × PLift (EqTm S Ψ Φ Γ t u i.ty)) :=
  match t, u with
  | .const k, .const k' => do
    if h : k = k' then
      let i ← R.infer E (.const k)
      return ⟨i, ⟨h ▸ EqTm.refl i.htm⟩⟩
    else fail s!"kernel: constants c{k} and c{k'} differ"
  | .var x, .var y => do
    if h : x = y then
      let i ← R.infer E (.var x)
      return ⟨i, ⟨h ▸ EqTm.refl i.htm⟩⟩
    else fail s!"kernel: variables x{x} and x{y} differ"
  | .app f a, .app f' a' => do
    let ⟨fi, ⟨ef⟩⟩ ← R.convNe E f f'
    match ← whnfTy R E fi.ty fi.lvl fi.hty with
    | ⟨.pi A1 B1, eF⟩ =>
      have hP := HasTy.eqR eF
      let ⟨ha⟩ ← R.check E a A1 fi.lvl (HasTy.piDom hP)
      let ⟨ha'⟩ ← R.check E a' A1 fi.lvl (HasTy.piDom hP)
      let ⟨ea⟩ ← R.conv E A1 fi.lvl (HasTy.piDom hP) a a' ha ha'
      return ⟨⟨B1.inst a, fi.lvl, HasTy.subst (HasTy.piCod hP) ha, HasTy.app (HasTy.conv fi.htm eF) ha⟩,
        ⟨EqTm.app (EqTm.conv ef eF) ea⟩⟩
    | ⟨T, _⟩ => fail s!"kernel: applying a term of non-function type {short T}"
  | .fst p, .fst p' => do
    let ⟨pi, ⟨ep⟩⟩ ← R.convNe E p p'
    match ← whnfTy R E pi.ty pi.lvl pi.hty with
    | ⟨.sigma A1 _, eP⟩ =>
      have hP := HasTy.eqR eP
      return ⟨⟨A1, pi.lvl, HasTy.sigmaDom hP, HasTy.fst (HasTy.conv pi.htm eP)⟩,
        ⟨EqTm.fst (EqTm.conv ep eP)⟩⟩
    | ⟨T, _⟩ => fail s!"kernel: projection from non-Σ type {short T}"
  | .snd p, .snd p' => do
    let ⟨pi, ⟨ep⟩⟩ ← R.convNe E p p'
    match ← whnfTy R E pi.ty pi.lvl pi.hty with
    | ⟨.sigma _ B1, eP⟩ =>
      have hP := HasTy.eqR eP
      have hp := HasTy.conv pi.htm eP
      return ⟨⟨B1.inst (.fst p), pi.lvl, HasTy.subst (HasTy.sigmaCod hP) (HasTy.fst hp), HasTy.snd hp⟩,
        ⟨EqTm.snd (EqTm.conv ep eP)⟩⟩
    | ⟨T, _⟩ => fail s!"kernel: projection from non-Σ type {short T}"
  | .papp p r, .papp p' r' => do
    let ⟨pi, ⟨ep⟩⟩ ← R.convNe E p p'
    let ⟨hr⟩ ← ensureScoped r Ψ
    let ⟨hr'⟩ ← ensureScoped r' Ψ
    let ⟨hq⟩ ← ensureIEq r r'
    match ← whnfTy R E pi.ty pi.lvl pi.hty with
    | ⟨.path A1 _ _, eP⟩ =>
      have hP := HasTy.eqR eP
      return ⟨⟨A1.dinst r, pi.lvl, HasTy.dsubst (HasTy.pathLine hP) hr,
        HasTy.papp (HasTy.conv pi.htm eP) hr⟩, ⟨EqTm.papp (EqTm.conv ep eP) hr hr' hq⟩⟩
    | ⟨.ipi A1, eP⟩ =>
      have hP := HasTy.eqR eP
      return ⟨⟨A1.dinst r, pi.lvl, HasTy.dsubst (HasTy.ipiLine hP) hr,
        HasTy.iapp (HasTy.conv pi.htm eP) hr⟩, ⟨EqTm.iapp (EqTm.conv ep eP) hr hr' hq⟩⟩
    | ⟨T, _⟩ => fail s!"kernel: path application at type {short T}"
  | .transp A φ a, .transp A' φ' a' => do
    let ti ← inferTransp R E A φ a
    let ⟨l2, ⟨hA'⟩⟩ ← inferType R E.dext A'
    let m := max ti.l l2
    let ⟨hm⟩ ← ensureLvl (m + 1)
    have hm' := Nat.le_of_succ_le hm
    let ⟨eL⟩ ← R.conv E.dext (.univ m) (m + 1) (E.dext.univTy m hm) A A'
      (ti.hA.liftLe (Nat.le_max_left _ _) hm') (hA'.liftLe (Nat.le_max_right _ _) hm')
    let ⟨h1⟩ ← ensureEnt φ φ'
    let ⟨h2⟩ ← ensureEnt φ' φ
    have hA0 : HasTy S Ψ Φ Γ (A.dinst .zero) (.univ ti.l) := HasTy.dsubst ti.hA trivial
    let ⟨ha'⟩ ← R.check E a' (A.dinst .zero) ti.l hA0
    let ⟨ea⟩ ← R.conv E (A.dinst .zero) ti.l hA0 a a' ti.ha ha'
    let ui ← inferTransp R E A' φ' a'
    have e1 : EqTm S Ψ Φ Γ (A.dinst .one) (A'.dinst .one) (.univ m) := EqTm.dsubst eL trivial
    return ⟨⟨A.dinst .one, ti.l, HasTy.dsubst ti.hA trivial, ti.ht⟩,
      ⟨EqTm.transp ti.ht (HasTy.conv ui.ht (EqTm.symm e1)) eL h1 h2 ea⟩⟩
  | .hcomp A φ v a, .hcomp A' φ' v' a' => do
    let ti ← inferHcomp R E A φ v a
    let ui ← inferHcomp R E A' φ' v' a'
    let m := max ti.l ui.l
    let ⟨hm⟩ ← ensureLvl (m + 1)
    have hm' := Nat.le_of_succ_le hm
    let ⟨eA⟩ ← R.conv E (.univ m) (m + 1) (E.univTy m hm) A A'
      (ti.hA.liftLe (Nat.le_max_left _ _) hm') (ui.hA.liftLe (Nat.le_max_right _ _) hm')
    let ⟨h1⟩ ← ensureEnt φ φ'
    let ⟨h2⟩ ← ensureEnt φ' φ
    let E1 := E.cof φ ti.hφ
    have hAs := HasTy.dwkCof E ti.hφ ti.hA
    let ⟨hv'⟩ ← R.check E1.dext v' A.dshift ti.l hAs
    let ⟨ev⟩ ← R.conv E1.dext A.dshift ti.l hAs v v' ti.hu hv'
    let ⟨ea⟩ ← R.conv E A ti.l ti.hA a a' ti.ha (HasTy.conv ui.ha (EqTm.symm eA))
    return ⟨⟨A, ti.l, ti.hA, ti.ht⟩,
      ⟨EqTm.hcomp ti.ht (HasTy.conv ui.ht (EqTm.symm eA)) eA h1 h2 ev ea⟩⟩
  | .unglue φ e g, .unglue φ' e' g' =>
    if he : e' = e then by subst he; exact convNeUnglue R E φ _ g φ' g'
    else fail s!"kernel: unglue with different equivalences:\n  {short e}\n  {short e'}"
  | .con d c ps args rs, .con d' c' ps' args' rs' =>
    if h : d' = d ∧ c' = c then by
      obtain ⟨rfl, rfl⟩ := h; exact convNeCon R E d' c' ps args rs ps' args' rs'
    else fail s!"kernel: different constructors D{d}.{c} and D{d'}.{c'}"
  | .elim d ps P bs t, .elim d' ps' P' bs' t' =>
    if h : d' = d then by subst h; exact convNeElim R E d' ps P bs t ps' P' bs' t'
    else fail "kernel: eliminators of different types"
  | t, u => fail s!"kernel: not convertible:\n  {short t}\n  {short u}"

end KubusCore.Kernel
