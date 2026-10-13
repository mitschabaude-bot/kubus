import KubusCore.Kernel.Infer

/-!
# Kernel: typed weak-head reduction

`whnfStep` performs one head step at a given type: β, projections, path application,
endpoints, systems, δ-unfolding, the face rules of `transp`/`hcomp`/Glue, and the CHM
computation rules of the Kan operations. Eliminations whose head is not a redex are reduced
by `whnfIStep`, which infers the type of the head, reduces it, and continues.
-/

namespace KubusCore.Kernel

variable {S : Sig}

/-- An interval variable of `r` that the restriction `Φ` fixes to an endpoint. -/
def fixedVar (Ψ : Nat) (Φ : I) :
    List Nat → Option ((i : Nat) × (d : Bool) × PLift (i < Ψ ∧ I.Entails Φ (I.lit i d)))
  | [] => none
  | i :: is =>
    if hi : i < Ψ then
      if h1 : I.Entails Φ (I.lit i true) then some ⟨i, true, ⟨hi, h1⟩⟩
      else if h0 : I.Entails Φ (I.lit i false) then some ⟨i, false, ⟨hi, h0⟩⟩
      else fixedVar Ψ Φ is
    else fixedVar Ψ Φ is

/-- Computation rule of `transp` for a line in weak-head normal form. -/
def transpRule (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (L : Tm) (φ : I) (a T : Tm)
    (ht : HasTy S Ψ Φ Γ (.transp L φ a) T) : K (Option (Red S Ψ Φ Γ (.transp L φ a) T)) :=
  match L, ht with
  | .univ _, ht => pure (some ⟨a, EqTm.transpU ht⟩)
  | .pi A B, ht => pure (some ⟨Tm.transpPi A B φ a, EqTm.transpPi ht⟩)
  | .sigma A B, ht => pure (some ⟨Tm.transpSigma A B φ a, EqTm.transpSigma ht⟩)
  | .path A b0 b1, ht => pure (some ⟨Tm.transpPath A b0 b1 φ a, EqTm.transpPath ht⟩)
  | .glue A ψ T' e, ht => do
    -- the base and the equivalence of the Glue line, which the rule takes as premises
    let ⟨l, ⟨hA⟩⟩ ← inferType R E.dext A
    let ⟨he⟩ ← checkEquiv R E.dext A ψ T' e l
    pure (some ⟨Tm.transpGlue A ψ T' e φ a, EqTm.transpGlue ht hA he⟩)
  | .ipi A, ht => pure (some ⟨Tm.transpIPi A φ a, EqTm.transpIPi ht⟩)
  | _, _ => pure none

/-- Computation rule of `hcomp` for a type in weak-head normal form. -/
def hcompRule (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : Tm) (φ : I) (u a T : Tm)
    (ht : HasTy S Ψ Φ Γ (.hcomp A φ u a) T) : K (Option (Red S Ψ Φ Γ (.hcomp A φ u a) T)) :=
  match A, ht with
  | .pi A B, ht => pure (some ⟨Tm.hcompPi A B φ u a, EqTm.hcompPi ht⟩)
  | .sigma A B, ht => pure (some ⟨Tm.hcompSigma A B φ u a, EqTm.hcompSigma ht⟩)
  | .path A b0 b1, ht => pure (some ⟨Tm.hcompPath A b0 b1 φ u a, EqTm.hcompPath ht⟩)
  | .glue A ψ T' e, ht => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E A
    let ⟨he⟩ ← checkEquiv R E A ψ T' e l
    pure (some ⟨Tm.hcompGlue A ψ T' e φ u a, EqTm.hcompGlue ht hA he⟩)
  | .ipi A, ht => pure (some ⟨Tm.hcompIPi A φ u a, EqTm.hcompIPi ht⟩)
  | _, _ => pure none

/-- `transp`: face rule, reduction of the line, computation rule. -/
def transpStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (L : Tm) (φ : I) (a A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ (.transp L φ a) A) :
    K (Option (Red S Ψ Φ Γ (.transp L φ a) A × Bool)) := do
  if h : I.Entails Φ φ then return some (⟨a, EqTm.transpFace h ht⟩, false)
  let ⟨l1, ⟨hL⟩⟩ ← inferType R E.dext L
  let r ← whnfTy R E.dext L l1 hL
  if r.tm = L then
    return (← transpRule R E L φ a A ht).map (·, false)
  let i ← inferTransp R E L φ a
  let m := max l1 i.l
  let ⟨hm⟩ ← ensureLvl m
  have eL : EqTm S (Ψ + 1) Φ.shift Γ.dshift L r.tm (.univ m) := r.eq.liftLe (Nat.le_max_left _ _) hm
  have hL' := HasTy.eqR eL
  have e0 : EqTm S Ψ Φ Γ (L.dinst .zero) (r.tm.dinst .zero) (.univ m) := EqTm.dsubst eL trivial
  have e1 : EqTm S Ψ Φ Γ (L.dinst .one) (r.tm.dinst .one) (.univ m) := EqTm.dsubst eL trivial
  have heq' : EqTm S (Ψ + 1) (cof Φ φ).shift Γ.dshift r.tm (r.tm.dinst .zero).dshift (.univ m) :=
    EqTm.trans (EqTm.symm (EqTm.rsd E i.hφ eL))
      (EqTm.trans (i.heq.liftLe (Nat.le_max_right _ _) hm) (EqTm.dwkCof E i.hφ e0))
  have ht' := HasTy.transp hL' i.hφ heq' (HasTy.conv i.ha e0)
  have e := EqTm.transp i.ht (HasTy.conv ht' (EqTm.symm e1)) eL (I.entails_refl φ)
    (I.entails_refl φ) (EqTm.refl i.ha)
  let ⟨e⟩ ← bridge R E (HasTy.dsubst (r := .one) i.hA trivial) hA e
  match ← transpRule R E r.tm φ a A (HasTy.eqR e) with
  | some r2 => return some (⟨r2.tm, EqTm.trans e r2.eq⟩, false)
  | none => return some (⟨.transp r.tm φ a, e⟩, true)

/-- `hcomp`: face rule, reduction of the type, computation rule. -/
def hcompStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (B : Tm) (φ : I) (u a A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ (.hcomp B φ u a) A) :
    K (Option (Red S Ψ Φ Γ (.hcomp B φ u a) A × Bool)) := do
  if h : I.Entails Φ φ then return some (⟨u.dinst .one, EqTm.hcompFace h ht⟩, false)
  let ⟨l1, ⟨hB⟩⟩ ← inferType R E B
  let r ← whnfTy R E B l1 hB
  if r.tm = B then
    return (← hcompRule R E B φ u a A ht).map (·, false)
  let i ← inferHcomp R E B φ u a
  let m := max l1 i.l
  let ⟨hm⟩ ← ensureLvl m
  have eB : EqTm S Ψ Φ Γ B r.tm (.univ m) := r.eq.liftLe (Nat.le_max_left _ _) hm
  have hB' := HasTy.eqR eB
  have hu' := HasTy.conv i.hu (EqTm.dwkCof E i.hφ eB)
  have heq' := EqTm.conv i.heq (EqTm.rs E i.hφ eB)
  have ht' := HasTy.hcomp hB' i.hφ hu' (HasTy.conv i.ha eB) heq'
  have e := EqTm.hcomp i.ht (HasTy.conv ht' (EqTm.symm eB)) eB (I.entails_refl φ)
    (I.entails_refl φ) (EqTm.refl i.hu) (EqTm.refl i.ha)
  let ⟨e⟩ ← bridge R E i.hA hA e
  match ← hcompRule R E r.tm φ u a A (HasTy.eqR e) with
  | some r2 => return some (⟨r2.tm, EqTm.trans e r2.eq⟩, false)
  | none => return some (⟨.hcomp r.tm φ u a, e⟩, true)

/-- Reduce an elimination whose head is not a redex. -/
def elimStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K (Option (Red S Ψ Φ Γ t A × Bool)) := do
  let ⟨i, r⟩ ← (R.whnfI E t).mapError (· ++ s!"\n  reducing {short t}")
  if r.tm = t then pure none
  else
    let ⟨e⟩ ← bridge R E i.hty hA r.eq
    pure (some (⟨r.tm, e⟩, true))

/-- One head step at type `A`; `none` if `t` is in weak-head normal form. The flag says that
the result is already in weak-head normal form. -/
def whnfStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) :
    K (Option (Red S Ψ Φ Γ t A × Bool)) :=
  match t, ht with
  | .app (.lam _ b) a, ht => pure (some (⟨b.inst a, EqTm.piBeta ht⟩, false))
  | .fst (.pair a _), ht => pure (some (⟨a, EqTm.fstBeta ht⟩, false))
  | .snd (.pair _ b), ht => pure (some (⟨b, EqTm.sndBeta ht⟩, false))
  | .papp (.plam b) r, ht => pure (some (⟨b.dinst r, EqTm.pathBeta ht⟩, false))
  | .split φ t1 ψ u1, ht =>
    if h : I.Entails Φ φ then pure (some (⟨t1, EqTm.splitL h ht⟩, false))
    else if h : I.Entails Φ ψ then pure (some (⟨u1, EqTm.splitR h ht⟩, false))
    else pure none
  | .glue _ φ T _, ht =>
    if h : I.Entails Φ φ then pure (some (⟨T, EqTm.glueFace h ht⟩, false)) else pure none
  | .unglue φ e (.glueEl φ' e' t1 a1), ht =>
    if h : φ' = φ ∧ e' = e then
      pure (some (⟨a1, by obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact EqTm.glueBeta ht⟩, false))
    else elimStep R E (.unglue φ e (.glueEl φ' e' t1 a1)) A l hA
  | .glueEl φ _ t1 _, ht =>
    if h : I.Entails Φ φ then pure (some (⟨t1, EqTm.glueElFace h ht⟩, false)) else pure none
  | .const k, _ =>
    match h : S[k]?, hl : E.sig.lv[k]? with
    | some (b, Ak), some lk => do
      let ⟨e⟩ ← bridge R E (E.constOk k b Ak lk h hl) hA (EqTm.delta (HasTy.const E.wf h) h)
      pure (some (⟨b, e⟩, false))
    | _, _ => fail s!"kernel: unknown constant c{k}"
  | .transp L φ a, ht => transpStep R E L φ a A l hA ht
  | .hcomp B φ u a, ht => hcompStep R E B φ u a A l hA ht
  | .app f a, _ => elimStep R E (.app f a) A l hA
  | .fst p, _ => elimStep R E (.fst p) A l hA
  | .snd p, _ => elimStep R E (.snd p) A l hA
  | .papp p r, _ => elimStep R E (.papp p r) A l hA
  | .unglue φ e g, _ => elimStep R E (.unglue φ e g) A l hA
  | _, _ => pure none

def whnfLoop (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (t0 : Tm) :
    Nat → (t : Tm) → EqTm S Ψ Φ Γ t0 t A → K (Red S Ψ Φ Γ t0 A)
  | 0, _, _ => fail "kernel: too many reduction steps"
  | n + 1, t, e => do
    match ← whnfStep R E t A l hA (HasTy.eqR e) with
    | none => pure ⟨t, e⟩
    | some (r, true) => pure ⟨r.tm, EqTm.trans e r.eq⟩
    | some (r, false) => whnfLoop R E A l hA t0 n r.tm (EqTm.trans e r.eq)

def whnfMain (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) : K (Red S Ψ Φ Γ t A) :=
  whnfLoop R E A l hA t 100000 t (EqTm.refl ht)

/-- Infer and reduce; eliminations reduce their head first. -/
def whnfIDefault (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) := do
  let i ← (R.infer E t).mapError (· ++ s!"\n  inferring {short t}")
  let r ← R.whnf E t i.ty i.lvl i.hty i.htm
  pure ⟨i, r⟩

def whnfIStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) :=
  match t with
  | .app f a =>
    match f with
    | .lam A' b => whnfIDefault R E (.app (.lam A' b) a)
    | f => do
      let ⟨fi, fr⟩ ← R.whnfI E f
      match ← whnfTy R E fi.ty fi.lvl fi.hty with
      | ⟨.pi A1 B1, eF⟩ =>
        have hP := HasTy.eqR eF
        let ⟨ha⟩ ← R.check E a A1 fi.lvl (HasTy.piDom hP)
        let inf : Inf S Ψ Φ Γ (.app f a) :=
          ⟨B1.inst a, fi.lvl, HasTy.subst (HasTy.piCod hP) ha, HasTy.app (HasTy.conv fi.htm eF) ha⟩
        if fr.tm = f then return ⟨inf, ⟨_, EqTm.refl inf.htm⟩⟩
        have e1 : EqTm S Ψ Φ Γ (.app f a) (.app fr.tm a) (B1.inst a) :=
          EqTm.app (EqTm.conv fr.eq eF) (EqTm.refl ha)
        match h : fr.tm with
        | .lam A' b =>
          have e1' : EqTm S Ψ Φ Γ (.app f a) (.app (.lam A' b) a) (B1.inst a) := h ▸ e1
          have e2 := EqTm.piBeta (HasTy.eqR e1')
          let r3 ← R.whnf E (b.inst a) (B1.inst a) fi.lvl inf.hty (HasTy.eqR e2)
          return ⟨inf, ⟨r3.tm, EqTm.trans e1' (EqTm.trans e2 r3.eq)⟩⟩
        | f' => return ⟨inf, ⟨.app f' a, h ▸ e1⟩⟩
      | ⟨T, _⟩ => fail s!"kernel: applying {short f} of non-function type {short T}"
  | .fst (.pair a b) => whnfIDefault R E (.fst (.pair a b))
  | .snd (.pair a b) => whnfIDefault R E (.snd (.pair a b))
  | .fst p => do
    let ⟨pi, pr⟩ ← R.whnfI E p
    match ← whnfTy R E pi.ty pi.lvl pi.hty with
    | ⟨.sigma A1 _, eP⟩ =>
      have hP := HasTy.eqR eP
      let inf : Inf S Ψ Φ Γ (.fst p) := ⟨A1, pi.lvl, HasTy.sigmaDom hP, HasTy.fst (HasTy.conv pi.htm eP)⟩
      if pr.tm = p then return ⟨inf, ⟨_, EqTm.refl inf.htm⟩⟩
      have e1 : EqTm S Ψ Φ Γ (.fst p) (.fst pr.tm) A1 := EqTm.fst (EqTm.conv pr.eq eP)
      match h : pr.tm with
      | .pair a _ =>
        have e1' : EqTm S Ψ Φ Γ (.fst p) (.fst (.pair a _)) A1 := h ▸ e1
        have e2 := EqTm.fstBeta (HasTy.eqR e1')
        let r3 ← R.whnf E a A1 pi.lvl inf.hty (HasTy.eqR e2)
        return ⟨inf, ⟨r3.tm, EqTm.trans e1' (EqTm.trans e2 r3.eq)⟩⟩
      | p' => return ⟨inf, ⟨.fst p', h ▸ e1⟩⟩
    | ⟨T, _⟩ => fail s!"kernel: projection from non-Σ type {short T}"
  | .snd p => do
    let ⟨pi, pr⟩ ← R.whnfI E p
    match ← whnfTy R E pi.ty pi.lvl pi.hty with
    | ⟨.sigma _ B1, eP⟩ =>
      have hP := HasTy.eqR eP
      have hp := HasTy.conv pi.htm eP
      let inf : Inf S Ψ Φ Γ (.snd p) :=
        ⟨B1.inst (.fst p), pi.lvl, HasTy.subst (HasTy.sigmaCod hP) (HasTy.fst hp), HasTy.snd hp⟩
      if pr.tm = p then return ⟨inf, ⟨_, EqTm.refl inf.htm⟩⟩
      have e1 : EqTm S Ψ Φ Γ (.snd p) (.snd pr.tm) (B1.inst (.fst p)) := EqTm.snd (EqTm.conv pr.eq eP)
      match h : pr.tm with
      | .pair _ b =>
        have e1' : EqTm S Ψ Φ Γ (.snd p) (.snd (.pair _ b)) (B1.inst (.fst p)) := h ▸ e1
        have e2 := EqTm.sndBeta (HasTy.eqR e1')
        let r3 ← R.whnf E b (B1.inst (.fst p)) pi.lvl inf.hty (HasTy.eqR e2)
        return ⟨inf, ⟨r3.tm, EqTm.trans e1' (EqTm.trans e2 r3.eq)⟩⟩
      | p' => return ⟨inf, ⟨.snd p', h ▸ e1⟩⟩
    | ⟨T, _⟩ => fail s!"kernel: projection from non-Σ type {short T}"
  | .papp p r =>
    match p with
    | .plam b => whnfIDefault R E (.papp (.plam b) r)
    | p => do
      let ⟨hr⟩ ← ensureScoped r Ψ
      match fixedVar Ψ Φ r.vars with
      | some ⟨i, d, ⟨hi, hent⟩⟩ =>
        -- the restriction fixes a variable of `r`: substitute it
        let it ← R.infer E (.papp p r)
        have e := EqTm.face hi hent it.htm
        let r2 ← R.whnf E _ it.ty it.lvl it.hty (HasTy.eqR e)
        return ⟨it, ⟨r2.tm, EqTm.trans e r2.eq⟩⟩
      | none =>
      let ⟨pi, pr⟩ ← R.whnfI E p
      match ← whnfTy R E pi.ty pi.lvl pi.hty with
      | ⟨.path A1 a0 a1, eP⟩ =>
        have hP := HasTy.eqR eP
        have hp := HasTy.conv pi.htm eP
        have hL := HasTy.pathLine hP
        let inf : Inf S Ψ Φ Γ (.papp p r) := ⟨A1.dinst r, pi.lvl, HasTy.dsubst hL hr, HasTy.papp hp hr⟩
        if h0 : r = .zero then
          have e : EqTm S Ψ Φ Γ (.papp p r) a0 (A1.dinst r) := h0 ▸ EqTm.pathZero hp
          let r2 ← R.whnf E a0 (A1.dinst r) pi.lvl inf.hty (HasTy.eqR e)
          return ⟨inf, ⟨r2.tm, EqTm.trans e r2.eq⟩⟩
        if h1 : r = .one then
          have e : EqTm S Ψ Φ Γ (.papp p r) a1 (A1.dinst r) := h1 ▸ EqTm.pathOne hp
          let r2 ← R.whnf E a1 (A1.dinst r) pi.lvl inf.hty (HasTy.eqR e)
          return ⟨inf, ⟨r2.tm, EqTm.trans e r2.eq⟩⟩
        if hz : I.eqB r .zero = true then
          have e := EqTm.papp (r' := .zero) (EqTm.refl hp) hr trivial (I.eqB_sound hz)
          let ⟨e'⟩ ← bridge R E (HasTy.dsubst (r := .zero) hL trivial) inf.hty (EqTm.pathZero hp)
          have e := EqTm.trans e e'
          let r2 ← R.whnf E a0 (A1.dinst r) pi.lvl inf.hty (HasTy.eqR e)
          return ⟨inf, ⟨r2.tm, EqTm.trans e r2.eq⟩⟩
        if ho : I.eqB r .one = true then
          have e := EqTm.papp (r' := .one) (EqTm.refl hp) hr trivial (I.eqB_sound ho)
          let ⟨e'⟩ ← bridge R E (HasTy.dsubst (r := .one) hL trivial) inf.hty (EqTm.pathOne hp)
          have e := EqTm.trans e e'
          let r2 ← R.whnf E a1 (A1.dinst r) pi.lvl inf.hty (HasTy.eqR e)
          return ⟨inf, ⟨r2.tm, EqTm.trans e r2.eq⟩⟩
        if pr.tm = p then return ⟨inf, ⟨_, EqTm.refl inf.htm⟩⟩
        have e1 : EqTm S Ψ Φ Γ (.papp p r) (.papp pr.tm r) (A1.dinst r) :=
          EqTm.papp (EqTm.conv pr.eq eP) hr hr (fun _ => rfl)
        match h : pr.tm with
        | .plam b =>
          have e1' : EqTm S Ψ Φ Γ (.papp p r) (.papp (.plam b) r) (A1.dinst r) := h ▸ e1
          have e2 := EqTm.pathBeta (HasTy.eqR e1')
          let r3 ← R.whnf E (b.dinst r) (A1.dinst r) pi.lvl inf.hty (HasTy.eqR e2)
          return ⟨inf, ⟨r3.tm, EqTm.trans e1' (EqTm.trans e2 r3.eq)⟩⟩
        | p' => return ⟨inf, ⟨.papp p' r, h ▸ e1⟩⟩
      | ⟨.ipi A1, eP⟩ =>
        have hP := HasTy.eqR eP
        have hp := HasTy.conv pi.htm eP
        let inf : Inf S Ψ Φ Γ (.papp p r) :=
          ⟨A1.dinst r, pi.lvl, HasTy.dsubst (HasTy.ipiLine hP) hr, HasTy.iapp hp hr⟩
        if pr.tm = p then return ⟨inf, ⟨_, EqTm.refl inf.htm⟩⟩
        have e1 : EqTm S Ψ Φ Γ (.papp p r) (.papp pr.tm r) (A1.dinst r) :=
          EqTm.iapp (EqTm.conv pr.eq eP) hr hr (fun _ => rfl)
        match h : pr.tm with
        | .plam b =>
          have e1' : EqTm S Ψ Φ Γ (.papp p r) (.papp (.plam b) r) (A1.dinst r) := h ▸ e1
          have e2 := EqTm.pathBeta (HasTy.eqR e1')
          let r3 ← R.whnf E (b.dinst r) (A1.dinst r) pi.lvl inf.hty (HasTy.eqR e2)
          return ⟨inf, ⟨r3.tm, EqTm.trans e1' (EqTm.trans e2 r3.eq)⟩⟩
        | p' => return ⟨inf, ⟨.papp p' r, h ▸ e1⟩⟩
      | ⟨T, _⟩ => fail s!"kernel: path application of {short p} of type {short T}"
  | .unglue φ e g => do
    let ⟨gi, gr⟩ ← match R.whnfI E g with
      | .ok r => pure r
      | .error _ => do
        let gi ← inferUnglueArg R E φ e g
        pure ⟨gi, ← R.whnf E g gi.ty gi.lvl gi.hty gi.htm⟩
    let ⟨A1, T, ⟨hA1, eG⟩⟩ ← toGlueE R E gi.ty gi.lvl gi.hty φ e
    have hG := HasTy.eqR eG
    have hg := HasTy.conv gi.htm eG
    let ⟨he⟩ ← checkEquiv R E A1 φ T e gi.lvl
    let inf : Inf S Ψ Φ Γ (.unglue φ e g) := ⟨A1, gi.lvl, hA1, HasTy.unglue hG hA1 he hg⟩
    if hφ : I.Entails Φ φ then
      let ⟨hc⟩ ← ensureEnt Φ (cof Φ φ)
      have e1 := EqTm.unglueFace hφ hg hA1 (HasTy.restrict E.hsc hc he)
      let r2 ← R.whnf E _ A1 gi.lvl inf.hty (HasTy.eqR e1)
      return ⟨inf, ⟨r2.tm, EqTm.trans e1 r2.eq⟩⟩
    if gr.tm = g then return ⟨inf, ⟨_, EqTm.refl inf.htm⟩⟩
    have eg := EqTm.conv gr.eq eG
    have e1 : EqTm S Ψ Φ Γ (.unglue φ e g) (.unglue φ e gr.tm) A1 :=
      EqTm.unglue inf.htm (HasTy.unglue hG hA1 he (HasTy.eqR eg)) (I.entails_refl φ) (I.entails_refl φ) eg
    match h : gr.tm with
    | .glueEl φ' e' t1 a1 =>
      if hφ' : φ' = φ ∧ e' = e then
        have e1' : EqTm S Ψ Φ Γ (.unglue φ e g) (.unglue φ e (.glueEl φ e t1 a1)) A1 := by
          rw [h, hφ'.1, hφ'.2] at e1; exact e1
        have e2 := EqTm.glueBeta (HasTy.eqR e1')
        let r3 ← R.whnf E a1 A1 gi.lvl inf.hty (HasTy.eqR e2)
        return ⟨inf, ⟨r3.tm, EqTm.trans e1' (EqTm.trans e2 r3.eq)⟩⟩
      else return ⟨inf, ⟨_, h ▸ e1⟩⟩
    | g' => return ⟨inf, ⟨.unglue φ e g', h ▸ e1⟩⟩
  | t => whnfIDefault R E t

end KubusCore.Kernel
