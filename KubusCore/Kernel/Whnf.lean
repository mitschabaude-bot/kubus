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
def fixedVar {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) :
    List Nat → Option ((i : Nat) × (d : Bool) × PLift (i < Ψ ∧ I.Entails Φ (I.lit i d)))
  | [] => none
  | i :: is =>
    if hi : i < Ψ then
      if h1 : E.Ent (I.lit i true) then some ⟨i, true, ⟨hi, h1⟩⟩
      else if h0 : E.Ent (I.lit i false) then some ⟨i, false, ⟨hi, h0⟩⟩
      else fixedVar E is
    else fixedVar E is

def transpConK (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (D : DataDecl) {d : Nat}
    (hS : S[d]? = some (.data D)) (hp : D.params ≠ [])
    (c : Nat) {ps : Tm} {φ : I} {qs args : Tm} {rs : List I} {T : Tm}
    (ht : HasTy S Ψ Φ Γ (.transp (.data d ps) φ (.con d c qs args rs)) T) :
    K S (Option (Red S Ψ Φ Γ (.transp (.data d ps) φ (.con d c qs args rs)) T)) := do
  let ⟨C, ⟨hC⟩⟩ ← lookupCtor D c
  let ⟨h1⟩ ← ensureList ps
  let ⟨h2⟩ ← ensureList args
  -- the arguments at the parameters of the line's start
  let ⟨hc⟩ ← checkTele R E args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse
  return some ⟨_, EqTm.transpCon hS hp hC h1 h2 hc ht⟩

/-- Computation rule of `transp` for a line in weak-head normal form. -/
def transpRule (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (L : Tm) (φ : I) (a T : Tm)
    (ht : HasTy S Ψ Φ Γ (.transp L φ a) T) : K S (Option (Red S Ψ Φ Γ (.transp L φ a) T)) :=
  match L, ht with
  | .univ _, ht => pure (some ⟨a, EqTm.transpU ht⟩)
  | .pi A B, ht => pure (some ⟨Tm.transpPi A B φ a, EqTm.transpPi ht⟩)
  | .sigma A B, ht => pure (some ⟨Tm.transpSigma A B φ a, EqTm.transpSigma ht⟩)
  | .path A b0 b1, ht => pure (some ⟨Tm.transpPath A b0 b1 φ a, EqTm.transpPath ht⟩)
  | .glue A ψ T' e, ht => do
    -- the base and the equivalence of the Glue line, which the rule takes as premises
    let ⟨l, ⟨hA⟩⟩ ← inferType R E.dext A
    let ⟨he⟩ ← checkEquiv R E.dext A ψ T' e l
    pure (some ⟨Tm.transpGlue A ψ T' e φ a, EqTm.transpGlue ht hA he (I.entails_refl _) (I.entails_refl _)⟩)
  | .ipi A, ht => pure (some ⟨Tm.transpIPi A φ a, EqTm.transpIPi ht⟩)
  | .data d ps, ht => do
    let ⟨D, ⟨hS⟩⟩ ← lookupData S d
    if hp : D.params = [] then return some ⟨a, EqTm.transpData0 hS hp ht⟩
    else
      match a, ht with
      | .con d' c qs args rs, ht =>
        if hd : d' = d then (by subst hd; exact transpConK R E D hS hp c ht) else pure none
      | .hcomp (.data d' qs) ψ u a0, ht =>
        if hd : d' = d then (by
          subst hd
          exact do
            -- the composition at the parameters of the line's start
            let ⟨l, ⟨hD⟩⟩ ← inferType R E (.data d' (ps.dinst .zero))
            let ⟨hh⟩ ← R.check E (.hcomp (.data d' (ps.dinst .zero)) ψ u a0) _ l hD
            pure (some ⟨_, EqTm.transpHcomp hS hp hh ht⟩))
        else pure none
      | _, _ => return none
  | _, _ => pure none

/-- Computation rule of `hcomp` for a type in weak-head normal form. -/
def hcompRule (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : Tm) (φ : I) (u a T : Tm)
    (ht : HasTy S Ψ Φ Γ (.hcomp A φ u a) T) : K S (Option (Red S Ψ Φ Γ (.hcomp A φ u a) T)) :=
  match A, ht with
  | .pi A B, ht => pure (some ⟨Tm.hcompPi A B φ u a, EqTm.hcompPi ht⟩)
  | .sigma A B, ht => pure (some ⟨Tm.hcompSigma A B φ u a, EqTm.hcompSigma ht⟩)
  | .path A b0 b1, ht => pure (some ⟨Tm.hcompPath A b0 b1 φ u a, EqTm.hcompPath ht⟩)
  | .glue A ψ T' e, ht => do
    let ⟨l, ⟨hA⟩⟩ ← inferType R E A
    let ⟨he⟩ ← checkEquiv R E A ψ T' e l
    pure (some ⟨Tm.hcompGlue A ψ T' e φ u a, EqTm.hcompGlue ht hA he⟩)
  | .ipi A, ht => pure (some ⟨Tm.hcompIPi A φ u a, EqTm.hcompIPi ht⟩)
  | .univ _, ht => pure (some ⟨Tm.hcompU φ u a, EqTm.hcompU ht⟩)
  | _, _ => pure none

/-- Transport in an inductive type with parameters computes on constructors and formal
compositions: reduce the transported element. -/
def transpArgStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (L : Tm) (φ : I) (a A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K S (Option (Red S Ψ Φ Γ (.transp L φ a) A × Bool)) := do
  let i ← inferTransp R E L φ a
  have hA0 : HasTy S Ψ Φ Γ (L.dinst .zero) (.univ i.l) := HasTy.dsubst i.hA trivial
  let ⟨ai, ar⟩ ← R.whnfI E a
  if ar.tm = a then return none
  let ⟨ea⟩ ← bridge R E ai.hty hA0 ar.eq
  have ht2 := HasTy.transp i.hA i.hφ i.heq (HasTy.eqR ea)
  have e := EqTm.transp i.ht ht2 (EqTm.refl i.hA) (I.entails_refl φ) (I.entails_refl φ) ea
  let ⟨e⟩ ← bridge R E (HasTy.dsubst (r := .one) i.hA trivial) hA e
  return some (⟨_, e⟩, false)

/-- `transp`: face rule, reduction of the line, computation rule. -/
def transpStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (L : Tm) (φ : I) (a A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ (.transp L φ a) A) :
    K S (Option (Red S Ψ Φ Γ (.transp L φ a) A × Bool)) := do
  if h : E.Ent φ then return some (⟨a, EqTm.transpFace h ht⟩, false)
  let ⟨l1, ⟨hL⟩⟩ ← inferType R E.dext L
  let r ← whnfTy R E.dext L l1 hL
  if r.tm = L then
    match ← transpRule R E L φ a A ht with
    | some r2 => return some (r2, false)
    | none =>
      let r2 ← if (match L with | .data .. => true | _ => false) then transpArgStep R E L φ a A l hA
        else pure none
      return r2
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
  | none => return some (⟨.transp r.tm φ a, e⟩, false)

/-- `hcomp`: face rule, reduction of the type, computation rule. -/
def hcompStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (B : Tm) (φ : I) (u a A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ (.hcomp B φ u a) A) :
    K S (Option (Red S Ψ Φ Γ (.hcomp B φ u a) A × Bool)) := do
  if h : E.Ent φ then return some (⟨u.dinst .one, EqTm.hcompFace h ht⟩, false)
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
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K S (Option (Red S Ψ Φ Γ t A × Bool)) := do
  let ⟨i, r⟩ ← mapErr (· ++ s!"\n  reducing {short t}") (R.whnfI E t)
  if r.tm = t then pure none
  else
    let ⟨e⟩ ← bridge R E i.hty hA r.eq
    pure (some (⟨r.tm, e⟩, true))

/-- The first `k < n` for which `f k` gives a result. -/
def firstSome {α : Type} (f : Nat → K S (Option α)) : Nat → Nat → K S (Option α)
  | 0, _ => pure none
  | n + 1, k => do
    match ← f k with
    | some x => pure (some x)
    | none => firstSome f n (k + 1)

/-- A constructor equals its boundary on the faces of the boundary. -/
def conBndStep {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d c : Nat) (ps args : Tm) (rs : List I) (A : Tm)
    (ht : HasTy S Ψ Φ Γ (.con d c ps args rs) A) :
    K S (Option (Red S Ψ Φ Γ (.con d c ps args rs) A × Bool)) := do
  let ⟨D, ⟨hS⟩⟩ ← lookupData S d
  let ⟨C, ⟨hC⟩⟩ ← lookupCtor D c
  let ⟨h1⟩ ← ensureList ps
  let ⟨h2⟩ ← ensureList args
  firstSome (fun k =>
    match getIdx? C.bnd k with
    | some ⟨(ψ, _), ⟨hk⟩⟩ =>
      if hent : E.Ent (Ctor.cofAt ψ rs) then
        pure (some (⟨_, EqTm.conBnd hS hC hk hent h1 h2 ht⟩, false))
      else pure none
    | none => pure none) C.bnd.length 0

def elimConK (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d c : Nat) (ps P bs qs args : Tm) (rs : List I) (T : Tm)
    (ht : HasTy S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs)) T) :
    K S (Option (Red S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs)) T × Bool)) := do
  let ⟨D, ⟨hS⟩⟩ ← lookupData S d
  let ⟨C, ⟨hC⟩⟩ ← lookupCtor D c
  let ⟨h1⟩ ← ensureList args
  let ⟨h2⟩ ← ensureList bs
  -- the arguments at the eliminator's parameters
  let ⟨hc⟩ ← checkTele R E args (C.argTys d D.params.length) ps.toList.reverse
  match getIdx? bs.toList c with
  | some ⟨_, ⟨hb⟩⟩ => pure (some (⟨_, EqTm.elimCon hS hC hb h1 h2 hc ht⟩, false))
  | none => fail "kernel: missing branch"

def elimHcompK (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d : Nat) (ps P bs qs : Tm) (φ : I) (u a T : Tm)
    (ht : HasTy S Ψ Φ Γ (.elim d ps P bs (.hcomp (.data d qs) φ u a)) T) :
    K S (Option (Red S Ψ Φ Γ (.elim d ps P bs (.hcomp (.data d qs) φ u a)) T × Bool)) := do
  let ⟨_, ⟨hS⟩⟩ ← lookupData S d
  -- the composition at the eliminator's parameters
  let ⟨l, ⟨hD⟩⟩ ← inferType R E (.data d ps)
  let ⟨hh⟩ ← R.check E (.hcomp (.data d ps) φ u a) _ l hD
  pure (some (⟨_, EqTm.elimHcomp hS hh ht⟩, false))

/-- Reduce the target of an eliminator. -/
def elimTargetStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d : Nat) (ps P bs t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K S (Option (Red S Ψ Φ Γ (.elim d ps P bs t) A × Bool)) := do
  let ⟨ti, tr⟩ ← R.whnfI E t
  if tr.tm = t then return none
  let info ← inferElimInfo R E d ps P bs
  let ⟨et⟩ ← bridge R E ti.hty info.hD tr.eq
  have h1 := info.typing (HasTy.eqL et)
  have eP := EqTm.subst (EqTm.refl info.hP) (EqTm.symm et)
  have h2 := HasTy.conv (info.typing (HasTy.eqR et)) eP
  let ⟨hps⟩ ← checkTele R E ps info.D.params []
  have e := EqTm.elim info.hS h1 h2 (HasTele.eqRefl hps) (EqTm.refl info.hP) info.hbs info.hbs rfl
    (fun c C b b' hC hb hb' => by
      rw [hb] at hb'; cases hb'; exact EqTm.refl (info.hbr c C b hC hb)) et
  let ⟨e⟩ ← bridge R E (HasTy.subst info.hP (HasTy.eqL et)) hA e
  let canonical := match tr.tm with
    | .con .. | .hcomp (.data ..) .. => true
    | _ => false
  return some (⟨_, e⟩, !canonical)

/-- β for the eliminator on constructors and formal compositions. -/
def dataElimStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (d : Nat) (ps P bs t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ (.elim d ps P bs t) A) :
    K S (Option (Red S Ψ Φ Γ (.elim d ps P bs t) A × Bool)) :=
  match t, ht with
  | .con d' c qs args rs, ht =>
    if hd : d' = d then (by subst hd; exact elimConK R E d' c ps P bs qs args rs A ht)
    else pure none
  | .hcomp (.data d' qs) φ u a, ht =>
    if hd : d' = d then (by subst hd; exact elimHcompK R E d' ps P bs qs φ u a A ht)
    else pure none
  | t, _ => elimTargetStep R E d ps P bs t A l hA

/-- One head step at type `A`; `none` if `t` is in weak-head normal form. The flag says that
the result is already in weak-head normal form. -/
def whnfStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) :
    K S (Option (Red S Ψ Φ Γ t A × Bool)) :=
  match t, ht with
  | .app (.lam _ b) a, ht => pure (some (⟨b.inst a, EqTm.piBeta ht⟩, false))
  | .fst (.pair a _), ht => pure (some (⟨a, EqTm.fstBeta ht⟩, false))
  | .snd (.pair _ b), ht => pure (some (⟨b, EqTm.sndBeta ht⟩, false))
  | .papp (.plam b) r, ht => pure (some (⟨b.dinst r, EqTm.pathBeta ht⟩, false))
  | .split φ t1 ψ u1, ht =>
    if h : E.Ent φ then pure (some (⟨t1, EqTm.splitL h ht⟩, false))
    else if h : E.Ent ψ then pure (some (⟨u1, EqTm.splitR h ht⟩, false))
    else pure none
  | .glue _ φ T _, ht =>
    if h : E.Ent φ then pure (some (⟨T, EqTm.glueFace h ht⟩, false)) else pure none
  | .unglue φ e (.glueEl φ' e' t1 a1), ht =>
    if h : φ' = φ ∧ e' = e then
      pure (some (⟨a1, by obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact EqTm.glueBeta ht⟩, false))
    else elimStep R E (.unglue φ e (.glueEl φ' e' t1 a1)) A l hA
  | .glueEl φ _ t1 _, ht =>
    if h : E.Ent φ then pure (some (⟨t1, EqTm.glueElFace h ht⟩, false)) else pure none
  | .const k, _ =>
    match h : S[k]?, hl : E.sig.lv[k]? with
    | some (.defn b Ak), some lk => do
      let ⟨e⟩ ← bridge R E (E.constOk k b Ak lk h hl) hA (EqTm.delta (HasTy.const E.wf h) h)
      pure (some (⟨b, e⟩, false))
    | _, _ => fail s!"kernel: unknown constant c{k}"
  | .transp L φ a, ht => transpStep R E L φ a A l hA ht
  | .con d c ps args rs, ht => conBndStep E d c ps args rs A ht
  | .elim d ps P bs t, ht => dataElimStep R E d ps P bs t A l hA ht
  | .hcomp B φ u a, ht => hcompStep R E B φ u a A l hA ht
  | .app f a, _ => elimStep R E (.app f a) A l hA
  | .fst p, _ => elimStep R E (.fst p) A l hA
  | .snd p, _ => elimStep R E (.snd p) A l hA
  | .papp p r, _ => elimStep R E (.papp p r) A l hA
  | .unglue φ e g, _ => elimStep R E (.unglue φ e g) A l hA
  | _, _ => pure none

def whnfLoop (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (t0 : Tm) :
    Nat → (t : Tm) → EqTm S Ψ Φ Γ t0 t A → K S (Red S Ψ Φ Γ t0 A)
  | 0, _, _ => fail "kernel: too many reduction steps"
  | n + 1, t, e => do
    match ← whnfStep R E t A l hA (HasTy.eqR e) with
    | none => pure ⟨t, e⟩
    | some (r, true) => pure ⟨r.tm, EqTm.trans e r.eq⟩
    | some (r, false) => whnfLoop R E A l hA t0 n r.tm (EqTm.trans e r.eq)

def whnfMain (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) : K S (Red S Ψ Φ Γ t A) :=
  whnfLoop R E A l hA t 100000 t (EqTm.refl ht)

/-- Infer and reduce; eliminations reduce their head first. -/
def whnfIDefault (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K S ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) := do
  let i ← mapErr (· ++ s!"\n  inferring {short t}") (R.infer E t)
  let r ← R.whnf E t i.ty i.lvl i.hty i.htm
  pure ⟨i, r⟩

/-- The number of λs before the body of a constant defined by an eliminator on its last
argument, `λ x₁ … xₙ. elim d ps P bs xₙ`. -/
def splitArity (S : Sig) (k : Nat) : Option Nat :=
  match S[k]? with
  | some (.defn b _) =>
    let rec go : Nat → Tm → Option Nat
      | n, .lam _ t => go (n + 1) t
      | n, .elim _ _ _ _ (.var 0) => if n > 0 then some n else none
      | _, _ => none
    go 0 b
  | _ => none

/-- An application `c a₁ … aₙ` of such a constant to all its arguments. -/
def isSplitApp (S : Sig) (t : Tm) : Bool :=
  let (h, args) := t.unapps
  match h with
  | .const k => splitArity S k == some args.length
  | _ => false

/-- For such an application, reduce the scrutinee (the last argument) first, keeping the
constant folded: then the eliminator meets a constructor after unfolding. -/
def scrutineeStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (f a : Tm) :
    K S (Option ((i : Inf S Ψ Φ Γ (.app f a)) × Red S Ψ Φ Γ (.app f a) i.ty)) := do
  let fi ← R.infer E f
  match ← whnfTy R E fi.ty fi.lvl fi.hty with
  | ⟨.pi A1 B1, eF⟩ =>
    have hP := HasTy.eqR eF
    have hf := HasTy.conv fi.htm eF
    let ⟨ha⟩ ← R.check E a A1 fi.lvl (HasTy.piDom hP)
    let ra ← R.whnf E a A1 fi.lvl (HasTy.piDom hP) ha
    if ra.tm = a then return none
    let inf : Inf S Ψ Φ Γ (.app f a) :=
      ⟨B1.inst a, fi.lvl, HasTy.subst (HasTy.piCod hP) ha, HasTy.app hf ha⟩
    have e1 : EqTm S Ψ Φ Γ (.app f a) (.app f ra.tm) (B1.inst a) := EqTm.app (EqTm.refl hf) ra.eq
    let r2 ← R.whnf E _ _ fi.lvl inf.hty (HasTy.eqR e1)
    return some ⟨inf, ⟨r2.tm, EqTm.trans e1 r2.eq⟩⟩
  | _ => return none

def whnfIStep (R : Rec S) {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K S ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) :=
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
      match fixedVar E r.vars with
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
    let ⟨gi, gr⟩ ← tryCatch (R.whnfI E g) fun _ => do
        let gi ← inferUnglueArg R E φ e g
        pure ⟨gi, ← R.whnf E g gi.ty gi.lvl gi.hty gi.htm⟩
    let ⟨A1, T, ⟨hA1, eG⟩⟩ ← toGlueE R E gi.ty gi.lvl gi.hty φ e
    have hG := HasTy.eqR eG
    have hg := HasTy.conv gi.htm eG
    let ⟨he⟩ ← checkEquiv R E A1 φ T e gi.lvl
    let inf : Inf S Ψ Φ Γ (.unglue φ e g) := ⟨A1, gi.lvl, hA1, HasTy.unglue hG hA1 he hg⟩
    if hφ : E.Ent φ then
      let ⟨hc⟩ ← ensureEntE E (cof Φ φ)
      have e1 := EqTm.unglueFace hφ hg hA1 (HasTy.restrict E.hsc hc he)
      let r2 ← R.whnf E _ A1 gi.lvl inf.hty (HasTy.eqR e1)
      return ⟨inf, ⟨r2.tm, EqTm.trans e1 r2.eq⟩⟩
    if gr.tm = g then return ⟨inf, ⟨_, EqTm.refl inf.htm⟩⟩
    have eg := EqTm.conv gr.eq eG
    have e1 : EqTm S Ψ Φ Γ (.unglue φ e g) (.unglue φ e gr.tm) A1 :=
      EqTm.unglue inf.htm (HasTy.unglue hG hA1 he (HasTy.eqR eg)) (I.entails_refl φ) (I.entails_refl φ) (EqTm.refl he) eg
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
