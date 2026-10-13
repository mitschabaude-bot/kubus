import KubusCore.Kernel.Conv

/-!
# Kernel: entry points

`Kernel.rec S n` ties the knot of the mutually recursive kernel functions with fuel `n`
(the nesting depth of recursive calls). `checkSig S` checks a signature and returns a proof
of `WfSig S`; `CheckedSig.extend` checks one more definition against a checked signature.
-/

namespace KubusCore.Kernel

variable {S : Sig}

/-! ## Canonical restrictions

Each kernel call first replaces the restriction `Φ` by its canonical form `Φ'` (the
disjunction of its maximal faces), checking `Φ ⊨ Φ'` and `Φ' ⊨ Φ`, and moves the results
back with the restriction rule. This keeps `Φ` small under nested systems. -/

/-- The canonical form of the restriction of `E` (computed once per context). -/
def canonical {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) : Option ((Φ' : I) × Equiv' Ψ Φ Φ') := E.cn.get

variable {Ψ : Nat} {Φ : I} {Γ : Ctx}

def canonInferRaw (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) : K S (Inf S Ψ Φ Γ t) :=
  match (if E.canon then none else canonical E) with
  | none => inferStep R { E with canon := true } t
  | some ⟨Φ', q⟩ => do
    let i ← inferStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t
    pure ⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩

def canonCheckRaw (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K S (PLift (HasTy S Ψ Φ Γ t A)) :=
  match (if E.canon then none else canonical E) with
  | none => checkStep R { E with canon := true } t A l hA
  | some ⟨Φ', q⟩ => do
    let ⟨h⟩ ← checkStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t A l (HasTy.restrict q.hs q.h1 hA)
    pure ⟨HasTy.restrict E.hsc q.h2 h⟩

def canonWhnfRaw (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) : K S (Red S Ψ Φ Γ t A) :=
  match (if E.canon then none else canonical E) with
  | none => whnfMain R { E with canon := true } t A l hA ht
  | some ⟨Φ', q⟩ => do
    let r ← whnfMain R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t A l (HasTy.restrict q.hs q.h1 hA)
      (HasTy.restrict q.hs q.h1 ht)
    pure ⟨r.tm, EqTm.restrict E.hsc q.h2 r.eq⟩

def canonWhnfIRaw (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K S ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) :=
  match (if E.canon then none else canonical E) with
  | none => whnfIStep R { E with canon := true } t
  | some ⟨Φ', q⟩ => do
    let ⟨i, r⟩ ← whnfIStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t
    pure ⟨⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩,
      ⟨r.tm, EqTm.restrict E.hsc q.h2 r.eq⟩⟩

def canonConvRaw (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (t u : Tm) (ht : HasTy S Ψ Φ Γ t A)
    (hu : HasTy S Ψ Φ Γ u A) : K S (PLift (EqTm S Ψ Φ Γ t u A)) :=
  if h : t = u then pure ⟨h ▸ EqTm.refl ht⟩ else
  match (if E.canon then none else canonical E) with
  | none => convStep R { E with canon := true } A l hA t u ht hu
  | some ⟨Φ', q⟩ => do
    let ⟨e⟩ ← convStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) A l (HasTy.restrict q.hs q.h1 hA) t u
      (HasTy.restrict q.hs q.h1 ht) (HasTy.restrict q.hs q.h1 hu)
    pure ⟨EqTm.restrict E.hsc q.h2 e⟩

def canonConvNe (R : Rec S) (E : KCtx S Ψ Φ Γ) (t u : Tm) :
    K S ((i : Inf S Ψ Φ Γ t) × PLift (EqTm S Ψ Φ Γ t u i.ty)) :=
  match (if E.canon then none else canonical E) with
  | none => convNeStep R { E with canon := true } t u
  | some ⟨Φ', q⟩ => do
    let ⟨i, ⟨e⟩⟩ ← convNeStep R ({ E.restrict Φ' q.hs q.h1 with canon := true }) t u
    pure ⟨⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩,
      ⟨EqTm.restrict E.hsc q.h2 e⟩⟩

/-! Memoized versions: a hit transports the cached derivation along the equality of the
keys (checked structurally, with a pointer-equality shortcut). -/

def canonInfer (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) : K S (Inf S Ψ Φ Γ t) := do
  -- cheap cases, not worth a lookup
  if (match t with | .var _ | .const _ => true | _ => false) then return ← inferStep R E t
  if let some v := (← get).inf.find? Ψ Φ Γ [t] E.fs.get E.hfs E.hsc InfF.restr then return v
  let v ← canonInferRaw R E t
  modify fun c => { c with inf := c.inf.insert Ψ Φ Γ [t] E.fs.get E.hfs v }
  return v

def canonCheck (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K S (PLift (HasTy S Ψ Φ Γ t A)) := do
  if let some v := (← get).chk.find? Ψ Φ Γ [t, A] E.fs.get E.hfs E.hsc ChkF.restr then return v
  let v ← canonCheckRaw R E t A l hA
  modify fun c => { c with chk := c.chk.insert Ψ Φ Γ [t, A] E.fs.get E.hfs v }
  return v

def canonWhnf (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) : K S (Red S Ψ Φ Γ t A) := do
  if t.rigid then return ⟨t, EqTm.refl ht⟩
  if let some v := (← get).wh.find? Ψ Φ Γ [t, A] E.fs.get E.hfs E.hsc WhF.restr then return v
  let v ← canonWhnfRaw R E t A l hA ht
  modify fun c => { c with wh := c.wh.insert Ψ Φ Γ [t, A] E.fs.get E.hfs v }
  return v

def canonWhnfI (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K S ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) := do
  if let some v := (← get).whi.find? Ψ Φ Γ [t] E.fs.get E.hfs E.hsc WhiF.restr then return v
  let v ← canonWhnfIRaw R E t
  modify fun c => { c with whi := c.whi.insert Ψ Φ Γ [t] E.fs.get E.hfs v }
  return v

def canonConv (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (t u : Tm) (ht : HasTy S Ψ Φ Γ t A)
    (hu : HasTy S Ψ Φ Γ u A) : K S (PLift (EqTm S Ψ Φ Γ t u A)) := do
  if h : tmEq t u = true then return ⟨tmEq_sound h ▸ EqTm.refl ht⟩
  if let some v := (← get).conv.find? Ψ Φ Γ [A, t, u] E.fs.get E.hfs E.hsc ConvF.restr then return v
  let v ← canonConvRaw R E A l hA t u ht hu
  modify fun c => { c with conv := c.conv.insert Ψ Φ Γ [A, t, u] E.fs.get E.hfs v }
  return v

/-- The kernel with `n` levels of nested recursive calls. Each level is built lazily. -/
def rec (S : Sig) : Nat → Rec S
  | 0 => Rec.bot S
  | n + 1 =>
    { infer := fun E t => canonInfer (rec S n) E t
      check := fun E t A l hA => canonCheck (rec S n) E t A l hA
      whnf := fun E t A l hA ht => canonWhnf (rec S n) E t A l hA ht
      whnfI := fun E t => canonWhnfI (rec S n) E t
      conv := fun E A l hA t u ht hu => canonConv (rec S n) E A l hA t u ht hu
      convNe := fun E t u => canonConvNe (rec S n) E t u }

/-- Default nesting depth. -/
def defaultFuel : Nat := 20000

/-! ## Signatures -/

/-- Add the level of the next constant's type to the signature information. -/
def SigInfo.next (R : Rec S) (si : SigInfo S) : K S (Option (SigInfo S)) :=
  match h : S[si.lv.length]? with
  | none => pure none
  | some (.data _) =>
    -- inductive types are not supported by the kernel yet: a placeholder level, never used
    pure (some
      { lv := si.lv ++ [0]
        closed := by
          intro k t A' hk hlt
          simp only [List.length_append, List.length_singleton] at hlt
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · exact si.closed k t A' hk hlt
          · subst heq; rw [h] at hk; cases hk
        ok := by
          intro k t A' l' hk hl
          have hlt := KCtx.lt_of_getElem? hl
          simp only [List.length_append, List.length_singleton] at hlt
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
          · rw [List.getElem?_append_left hlt] at hl
            exact si.ok k t A' l' hk hl
          · subst heq; rw [h] at hk; cases hk })
  | some (.defn b A) =>
    if hc : A.closedB 0 0 = true then do
      let ⟨l, ⟨hA⟩⟩ ← inferType R (KCtx.root si) A
      pure (some
        { lv := si.lv ++ [l]
          closed := by
            intro k t A' hk hlt
            simp only [List.length_append, List.length_singleton] at hlt
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
            · exact si.closed k t A' hk hlt
            · subst heq; rw [h] at hk; cases hk; exact hc
          ok := by
            intro k t A' l' hk hl
            have hlt := KCtx.lt_of_getElem? hl
            simp only [List.length_append, List.length_singleton] at hlt
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
            · rw [List.getElem?_append_left hlt] at hl
              exact si.ok k t A' l' hk hl
            · subst heq; rw [h] at hk; cases hk
              rw [List.getElem?_append_right (Nat.le_refl _)] at hl
              simp at hl; subst hl; exact hA })
    else fail s!"kernel: the type of constant c{si.lv.length} is not closed"

def SigInfo.empty (S : Sig) : SigInfo S where
  lv := []
  closed := fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  ok := fun _ _ _ _ _ h => by simp at h

/-- Levels of all constant types of `S`. -/
def SigInfo.build (R : Rec S) : Nat → SigInfo S → K S (SigInfo S)
  | 0, si => pure si
  | n + 1, si => do
    match ← SigInfo.next R si with
    | none => pure si
    | some si' => SigInfo.build R n si'

/-- The kernel and the empty context for the signature `S`. -/
def setup (S : Sig) (fuel : Nat := defaultFuel) : K S (Rec S × KCtx S 0 .one []) := do
  let R := rec S fuel
  let si ← SigInfo.build R S.length (SigInfo.empty S)
  pure (R, KCtx.root si)

/-- Lift the result of a pure computation. -/
def liftM' {S : Sig} {α : Type} (x : Except String α) : K S α := monadLift x

/-- Run a kernel computation with an empty cache. -/
def runK {S : Sig} {α : Type} (x : K S α) : Except String α :=
  match x.run {} with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- Check one definition `(t, A)` against the signature `S`, given the kernel for `S`. -/
def checkEntryK (S : Sig) (R : Rec S) (E : KCtx S 0 .one []) (t A : Tm) :
    K S (PLift (t.closedB 0 0 = true ∧ A.closedB 0 0 = true ∧
      (∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A)) := do
  let ⟨l, ⟨hA⟩⟩ ← inferType R E A
  let ⟨ht⟩ ← R.check E t A l hA
  if hc : t.closedB 0 0 = true ∧ A.closedB 0 0 = true then
    pure ⟨hc.1, hc.2, ⟨l, hA⟩, ht⟩
  else fail "kernel: the definition is not closed"

/-- Check one definition `(t, A)` against the signature `S`. -/
def checkEntry (S : Sig) (t A : Tm) (fuel : Nat := defaultFuel) :
    Except String (PLift (t.closedB 0 0 = true ∧ A.closedB 0 0 = true ∧
      (∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A)) := runK do
  let (R, E) ← setup S fuel
  checkEntryK S R E t A

theorem wfSig_append {S : Sig} {t A : Tm} (hS : WfSig S)
    (h : t.closedB 0 0 = true ∧ A.closedB 0 0 = true ∧
      (∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A) :
    WfSig (S ++ [.defn t A]) := by
  refine ⟨?_, ?_⟩
  · intro k t' A' hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.1 k t' A' hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      have hk0 : k - S.length = 0 := by
        cases h' : k - S.length with
        | zero => rfl
        | succ n => rw [h'] at hk; simp at hk
      have hkeq : k = S.length := by omega
      subst hkeq
      simp at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [List.take_left' rfl]
      exact h
  · intro k D hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.2 k D hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      cases h' : k - S.length with
      | zero => rw [h'] at hk; simp at hk
      | succ n => rw [h'] at hk; simp at hk

theorem wfSig_appendData {S : Sig} {D : DataDecl} (hS : WfSig S)
    (h : D.Wf S S.length) : WfSig (S ++ [.data D]) := by
  refine ⟨?_, ?_⟩
  · intro k t' A' hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.1 k t' A' hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      cases h' : k - S.length with
      | zero => rw [h'] at hk; simp at hk
      | succ n => rw [h'] at hk; simp at hk
  · intro k D' hk
    by_cases hlt : k < S.length
    · rw [List.getElem?_append_left hlt] at hk
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hS.2 k D' hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      have hk0 : k - S.length = 0 := by
        cases h' : k - S.length with
        | zero => rfl
        | succ n => rw [h'] at hk; simp at hk
      have hkeq : k = S.length := by omega
      subst hkeq
      simp at hk
      subst hk
      rw [List.take_left' rfl]
      exact h

/-! ## Data declarations -/

section
variable {S : Sig}

/-- The context of the parameters and the arguments before argument `k`. -/
def argCtxK (R : Rec S) (E0 : KCtx S 0 .one []) (D : DataDecl) (d : Nat) (C : Ctor) (k : Nat) :
    K S (KCtx S 0 .one (D.argCtx d C k)) := do
  let E1 ← extTypes R E0 D.params
  let E2 ← extTypes R E1 ((List.range k).map (C.argTy d D.params.length))
  if h : ((List.range k).map (C.argTy d D.params.length)).reverse ++ (D.params.reverse ++ []) =
      D.argCtx d C k then pure (castCtx E2 rfl h)
  else fail "kernel: argument context mismatch"

/-- The same context at `Ψ = m` interval variables, restricted to `ψ`. -/
def bndCtxK (E : KCtx S 0 .one Γ) (m : Nat) (ψ : I) : K S (KCtx S m ψ Γ) := do
  let E1 := E.dextN m
  if h : shiftIN m .one = .one ∧ dshiftN m Γ = Γ then
    let E2 : KCtx S (0 + m) .one Γ := castCtx E1 h.1 h.2
    let E3 : KCtx S m .one Γ := Nat.zero_add m ▸ E2
    let ⟨hψ⟩ ← ensureScoped ψ m
    pure (E3.restrict ψ hψ (I.entails_one ψ))
  else fail "kernel: boundary context mismatch"

/-- The context of the parameters and the point arguments of `C` before `n`. -/
def pointCtxK (R : Rec S) (E0 : KCtx S 0 .one []) (D : DataDecl) (d : Nat) (C : Ctor) (n : Nat) :
    K S (KCtx S 0 .one (D.pointCtx d C n)) := do
  let E1 ← extTypes R E0 D.params
  let As := ((List.range n).filter fun k => !C.isRec k).map fun k =>
    (C.argTy d D.params.length k).ren (C.pointRen k) id
  let E2 ← extTypes R E1 As
  if h : As.reverse ++ (D.params.reverse ++ []) = D.pointCtx d C n then pure (castCtx E2 rfl h)
  else fail "kernel: point argument context mismatch"

/-! ### Typing of boundary arguments -/

mutual
def checkBndTyped (R : Rec S) {m ψ Γp} (Ep : KCtx S m ψ Γp) (Γ : Ctx) (C : Ctor) (lvl : Nat)
    (ctors : List Ctor) (d np : Nat) :
    (t : Tm) → K S (PLift (Ctor.bndTyped S m ψ Γ C Γp lvl ctors d np t))
  | .con d' c' ps as rs =>
    match getIdx' ctors c' with
    | .inl ⟨C', ⟨h⟩⟩ => do
      let ⟨p⟩ ← checkBndTypedArgs R Ep Γ C lvl ctors d np C' ps 0 [] as
      pure ⟨by simp only [Ctor.bndTyped, h]; exact p⟩
    | .inr ⟨h⟩ => pure ⟨by simp only [Ctor.bndTyped, h]⟩
  | .var .. | .const .. | .univ .. | .pi .. | .lam .. | .app .. | .sigma .. | .pair .. | .fst ..
  | .snd .. | .path .. | .plam .. | .papp .. | .ipi .. | .split .. | .abort | .transp .. | .hcomp ..
  | .glue .. | .glueEl .. | .unglue .. | .tnil | .tcons .. | .data .. | .elim .. =>
    pure ⟨by simp [Ctor.bndTyped]⟩
def checkBndTypedArgs (R : Rec S) {m ψ Γp} (Ep : KCtx S m ψ Γp) (Γ : Ctx) (C : Ctor) (lvl : Nat)
    (ctors : List Ctor) (d np : Nat) (C' : Ctor) (ps : Tm) (k : Nat) (prev : List Tm) :
    (t : Tm) → K S (PLift (Ctor.bndTypedArgs S m ψ Γ C Γp lvl ctors d np C' ps k prev t))
  | .tcons a as => do
    let ⟨h1⟩ ← checkBndVar R Ep Γ C lvl d np C' ps k prev a
    let ⟨h2⟩ ← if hr : C'.isRec k = true then do
        let ⟨h⟩ ← checkBndTyped R Ep Γ C lvl ctors d np a
        pure (PLift.up (fun _ => h))
      else pure (PLift.up (fun h => absurd h hr))
    let ⟨h3⟩ ← checkBndTypedArgs R Ep Γ C lvl ctors d np C' ps (k + 1) (a :: prev) as
    pure ⟨by simp only [Ctor.bndTypedArgs]; exact ⟨h1, h2, h3⟩⟩
  | .var .. | .const .. | .univ .. | .pi .. | .lam .. | .app .. | .sigma .. | .pair .. | .fst ..
  | .snd .. | .path .. | .plam .. | .papp .. | .ipi .. | .split .. | .abort | .transp .. | .hcomp ..
  | .glue .. | .glueEl .. | .unglue .. | .tnil | .con .. | .data .. | .elim .. =>
    pure ⟨by simp [Ctor.bndTypedArgs]⟩
/-- A point argument variable of a nested constructor has the argument type (in the context
without the recursive arguments). -/
def checkBndVar (R : Rec S) {m ψ Γp} (Ep : KCtx S m ψ Γp) (Γ : Ctx) (C : Ctor) (lvl d np : Nat)
    (C' : Ctor) (ps : Tm) (k : Nat) (prev : List Tm) (a : Tm) :
    K S (PLift (∀ (j : Nat) (T : Tm), a = .var j → C'.isRec k = false → Γ.lookup j = some T →
      C.mentionsRec C.args.length T = false ∧
      C.mentionsRec C.args.length ((C'.argTy d np k).substList (prev ++ ps.toList.reverse)) = false ∧
      EqTm S m ψ Γp (T.ren (C.pointRen C.args.length) id)
        (((C'.argTy d np k).substList (prev ++ ps.toList.reverse)).ren (C.pointRen C.args.length) id)
        (.univ lvl))) :=
  match a with
  | .var j =>
    if hr : C'.isRec k = false then
      match hT : Γ.lookup j with
      | some T => do
        let n := C.args.length
        let A' := (C'.argTy d np k).substList (prev ++ ps.toList.reverse)
        if hm : C.mentionsRec n T = false ∧ C.mentionsRec n A' = false then
          let ⟨h1⟩ ← checkType R Ep (T.ren (C.pointRen n) id) lvl
          let ⟨h2⟩ ← checkType R Ep (A'.ren (C.pointRen n) id) lvl
          let ⟨hU⟩ ← univTyK Ep lvl
          let ⟨e⟩ ← R.conv Ep (.univ lvl) (lvl + 1) hU _ _ h1 h2
          pure ⟨fun j' T' hj _ hT' => by cases hj; rw [hT] at hT'; cases hT'; exact ⟨hm.1, hm.2, e⟩⟩
        else fail "kernel: a boundary argument type mentions a recursive argument"
      | none => pure ⟨fun j' T' hj _ hT' => by cases hj; rw [hT] at hT'; cases hT'⟩
    else pure ⟨fun _ _ _ h => absurd h hr⟩
  | .const .. | .univ .. | .pi .. | .lam .. | .app .. | .sigma .. | .pair .. | .fst ..
  | .snd .. | .path .. | .plam .. | .papp .. | .ipi .. | .split .. | .abort | .transp .. | .hcomp ..
  | .glue .. | .glueEl .. | .unglue .. | .tnil | .tcons .. | .con .. | .data .. | .elim .. =>
    pure ⟨fun _ _ h => by cases h⟩
end

/-- The type equations of the boundaries of constructor `C`, in the signature before the
declaration. -/
def checkCtorBndTyped (R : Rec S) (E0 : KCtx S 0 .one []) (d : Nat) (D : DataDecl) (C : Ctor) :
    K S (PLift (∀ (k : Nat) (ψ : I) (b : Tm), C.bnd[k]? = some (ψ, b) →
      Ctor.bndTyped S C.dims ψ (D.argCtx d C C.args.length) C (D.pointCtx d C C.args.length)
        D.level D.ctors d D.params.length b)) := do
  let Ep ← pointCtxK R E0 D d C C.args.length
  let ⟨h⟩ ← forallElems C.bnd (fun _ pb => Ctor.bndTyped S C.dims pb.1 (D.argCtx d C C.args.length) C
      (D.pointCtx d C C.args.length) D.level D.ctors d D.params.length pb.2) fun _ pb _ => do
    let Eb ← bndCtxK Ep C.dims pb.1
    checkBndTyped R Eb (D.argCtx d C C.args.length) C D.level D.ctors d D.params.length pb.2
  pure ⟨fun k ψ b hk => h k (ψ, b) hk⟩

/-- Check the point argument types of constructor `C` in `S0` (the declaration without
constructors). -/
def checkCtorArgs (S0 : Sig) (d : Nat) (D : DataDecl) (C : Ctor) :
    K S0 (PLift (∀ (k : Nat) (A : Tm), C.args[k]? = some (.point A) →
      A.closedB (D.params.length + k) 0 = true ∧ A.mentionsData d = false ∧ C.noRecDeps k A = true ∧
      HasTy S0 0 .one (D.argCtx d C k) A (.univ D.level))) := do
  let np := D.params.length
  let (R0, E00) ← setup S0
  let ⟨hargs⟩ ← forallElems C.args (fun k a => ∀ A, a = .point A → A.closedB (np + k) 0 = true ∧
      A.mentionsData d = false ∧ C.noRecDeps k A = true ∧
      HasTy S0 0 .one (D.argCtx d C k) A (.univ D.level)) fun k a _ =>
    match a with
    | .point A => do
      let Ek ← argCtxK R0 E00 D d C k
      let ⟨hA⟩ ← checkType R0 Ek A D.level
      if hc : A.closedB (np + k) 0 = true ∧ A.mentionsData d = false ∧ C.noRecDeps k A = true then
        pure ⟨fun A' hA' => by cases hA'; exact ⟨hc.1, hc.2.1, hc.2.2, hA⟩⟩
      else fail "kernel: argument type not closed, mentions the type or an earlier recursive argument"
    | .recur => pure ⟨fun _ h => by cases h⟩
  pure ⟨fun k A hk => hargs k (.point A) hk A rfl⟩

/-- Check the boundary of constructor `c` in `Sc` (the declaration truncated to the
constructors before `c`). -/
def checkCtorBnd (Sc : Sig) (d : Nat) (D : DataDecl) (c : Nat) (C : Ctor) :
    K Sc (PLift ((∀ (k : Nat) (ψ : I) (b : Tm), C.bnd[k]? = some (ψ, b) → ψ.Scoped C.dims ∧
        b.closedB (D.params.length + C.args.length) C.dims = true ∧
        Ctor.simpleB D.ctors d D.params.length c C.args.length C b = true ∧
        HasTy Sc C.dims ψ (D.argCtx d C C.args.length) b (.data d (Ctor.paramVars D.params.length C.args.length))) ∧
      (∀ (k k' : Nat) (ψ ψ' : I) (b b' : Tm), C.bnd[k]? = some (ψ, b) → C.bnd[k']? = some (ψ', b') →
        EqTm Sc C.dims (.and ψ ψ') (D.argCtx d C C.args.length) b b'
          (.data d (Ctor.paramVars D.params.length C.args.length))))) := do
  let np := D.params.length
  let (R, E0) ← setup Sc
  let En ← argCtxK R E0 D d C C.args.length
  let T : Tm := .data d (Ctor.paramVars np C.args.length)
  let ⟨hb⟩ ← forallElems C.bnd (fun _ pb => pb.1.Scoped C.dims ∧
      pb.2.closedB (np + C.args.length) C.dims = true ∧
      Ctor.simpleB D.ctors d np c C.args.length C pb.2 = true ∧
      HasTy Sc C.dims pb.1 (D.argCtx d C C.args.length) pb.2 T)
      fun _ pb _ => do
    let Eb ← bndCtxK En C.dims pb.1
    let ⟨hψ⟩ ← ensureScoped pb.1 C.dims
    let ⟨l, ⟨hT⟩⟩ ← inferType R Eb T
    let ⟨h⟩ ← R.check Eb pb.2 T l hT
    if hc : pb.2.closedB (np + C.args.length) C.dims = true ∧
        Ctor.simpleB D.ctors d np c C.args.length C pb.2 = true then pure ⟨hψ, hc.1, hc.2, h⟩
    else fail "kernel: boundary not closed or not simple"
  let ⟨hagree⟩ ← forallElems C.bnd (fun k pb => ∀ (k' : Nat) (ψ' : I) (b' : Tm), C.bnd[k']? = some (ψ', b') →
      EqTm Sc C.dims (.and pb.1 ψ') (D.argCtx d C C.args.length) pb.2 b' T) fun k pb hk => do
    let ⟨h⟩ ← forallElems C.bnd (fun _ pb' => EqTm Sc C.dims (.and pb.1 pb'.1)
        (D.argCtx d C C.args.length) pb.2 pb'.2 T) fun k' pb' hk' => do
      let Eb ← bndCtxK En C.dims (.and pb.1 pb'.1)
      let ⟨l, ⟨hT⟩⟩ ← inferType R Eb T
      let ⟨h1⟩ ← R.check Eb pb.2 T l hT
      let ⟨h2⟩ ← R.check Eb pb'.2 T l hT
      R.conv Eb T l hT _ _ h1 h2
    pure ⟨fun k' ψ' b' hk' => h k' (ψ', b') hk'⟩
  pure ⟨fun k ψ b hk => hb k (ψ, b) hk, fun k k' ψ ψ' b b' hk hk' => hagree k (ψ, b) hk k' ψ' b' hk'⟩

def checkData (S : Sig) (d : Nat) (D : DataDecl) : K S (PLift (D.Wf S d)) := do
  let np := D.params.length
  let (R, E0) ← setup S
  let ⟨hl⟩ ← ensureLvl (D.level + 1)
  let ⟨hps⟩ ← forallElems D.params (fun j A => A.closedB j 0 = true ∧ A.mentionsData d = false ∧
      ∃ l, HasTy S 0 .one (D.paramCtx j) A (.univ l)) fun j A _ => do
    let E1 ← extTypes R E0 (D.params.take j)
    if h : (D.params.take j).reverse ++ [] = D.paramCtx j then
      let ⟨l, ⟨hA⟩⟩ ← inferType R (castCtx E1 rfl h) A
      if hc : A.closedB j 0 = true ∧ A.mentionsData d = false then pure ⟨hc.1, hc.2, l, hA⟩
      else fail "kernel: parameter type not closed or mentions the type"
    else fail "kernel: parameter context mismatch"
  let ⟨hcs⟩ ← forallElems D.ctors (fun c C =>
      let Sc := S ++ [.data (D.truncate c)]
      
      (∀ (k : Nat) (A : Tm), C.args[k]? = some (.point A) → A.closedB (np + k) 0 = true ∧
        A.mentionsData d = false ∧ C.noRecDeps k A = true ∧
        HasTy (S ++ [.data (D.truncate 0)]) 0 .one (D.argCtx d C k) A (.univ D.level)) ∧
      (∀ (k : Nat) (ψ : I) (b : Tm), C.bnd[k]? = some (ψ, b) → ψ.Scoped C.dims ∧
        b.closedB (np + C.args.length) C.dims = true ∧
        Ctor.simpleB D.ctors d np c C.args.length C b = true ∧
        HasTy Sc C.dims ψ (D.argCtx d C C.args.length) b (.data d (Ctor.paramVars np C.args.length)) ∧
        Ctor.bndTyped S C.dims ψ (D.argCtx d C C.args.length) C (D.pointCtx d C C.args.length)
          D.level D.ctors d np b) ∧
      (∀ (k k' : Nat) (ψ ψ' : I) (b b' : Tm), C.bnd[k]? = some (ψ, b) → C.bnd[k']? = some (ψ', b') →
        EqTm Sc C.dims (.and ψ ψ') (D.argCtx d C C.args.length) b b'
          (.data d (Ctor.paramVars np C.args.length)))) fun c C _ => do
      let ⟨ha⟩ ← liftM' (runK (checkCtorArgs (S ++ [.data (D.truncate 0)]) d D C))
      let ⟨hb⟩ ← liftM' (runK (checkCtorBnd (S ++ [.data (D.truncate c)]) d D c C))
      let ⟨hty⟩ ← checkCtorBndTyped R E0 d D C
      pure ⟨ha, fun k ψ b hk => ⟨(hb.1 k ψ b hk).1, (hb.1 k ψ b hk).2.1, (hb.1 k ψ b hk).2.2.1,
        (hb.1 k ψ b hk).2.2.2, hty k ψ b hk⟩, hb.2⟩
  pure ⟨hl, hps, fun c C hC => hcs c C hC⟩

end

/-- A signature together with a proof that it is well-formed. -/
structure CheckedSig where
  sig : Sig
  wf : WfSig sig

def CheckedSig.empty : CheckedSig := ⟨[], fun k _ _ h => by simp at h, fun k _ h => by simp at h⟩

/-- Check one more definition. -/
def CheckedSig.extend (C : CheckedSig) (t A : Tm) (fuel : Nat := defaultFuel) :
    Except String CheckedSig := do
  let ⟨h⟩ ← checkEntry C.sig t A fuel
  pure ⟨C.sig ++ [.defn t A], wfSig_append C.wf h⟩

/-- Check one more inductive type. -/
def CheckedSig.extendData (C : CheckedSig) (D : DataDecl) (fuel : Nat := defaultFuel) :
    Except String CheckedSig := do
  let S' := C.sig ++ [.data D]
  let ⟨h⟩ ← runK (checkData C.sig C.sig.length D)
  pure ⟨S', wfSig_appendData C.wf h⟩

def checkSigAux (pre : Sig) (hpre : WfSig pre) : (rest : Sig) → Except String (PLift (WfSig (pre ++ rest)))
  | [] => pure ⟨by simpa using hpre⟩
  | .defn t A :: rest => do
    let ⟨h⟩ ← checkEntry pre t A
    let ⟨h'⟩ ← checkSigAux (pre ++ [.defn t A]) (wfSig_append hpre h) rest
    pure ⟨by simpa using h'⟩
  | .data D :: rest => do
    let ⟨h⟩ ← runK (checkData pre pre.length D)
    let ⟨h'⟩ ← checkSigAux (pre ++ [.data D]) (wfSig_appendData hpre h) rest
    pure ⟨by simpa using h'⟩

/-- Check a whole signature. -/
def checkSig (S : Sig) : Except String (PLift (WfSig S)) := do
  let ⟨h⟩ ← checkSigAux [] ⟨fun k _ _ h => by simp at h, fun k _ h => by simp at h⟩ S
  pure ⟨by simpa using h⟩

/-- Soundness of the kernel: by construction, `checkSig` only succeeds with a proof. -/
theorem checkSig_sound {S : Sig} {h : PLift (WfSig S)} (_ : checkSig S = .ok h) : WfSig S :=
  h.down

end KubusCore.Kernel
