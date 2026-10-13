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

/-- Proofs that `Φ'` is equivalent to `Φ`. -/
structure Equiv' (Ψ : Nat) (Φ Φ' : I) : Type where
  hs : Φ'.Scoped Ψ
  h1 : I.Entails Φ' Φ
  h2 : I.Entails Φ Φ'

def canonical (Ψ : Nat) (Φ : I) : Option ((Φ' : I) × Equiv' Ψ Φ Φ') :=
  let Φ' := canonPhi Φ
  if Φ' = Φ then none else
  if hs : Φ'.Scoped Ψ then
    if h1 : I.Entails Φ' Φ then
      if h2 : I.Entails Φ Φ' then some ⟨Φ', hs, h1, h2⟩ else none
    else none
  else none

variable {Ψ : Nat} {Φ : I} {Γ : Ctx}

def canonInfer (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) : K (Inf S Ψ Φ Γ t) :=
  match canonical Ψ Φ with
  | none => inferStep R E t
  | some ⟨Φ', q⟩ => do
    let i ← inferStep R (E.restrict Φ' q.hs q.h1) t
    pure ⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩

def canonCheck (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) : K (PLift (HasTy S Ψ Φ Γ t A)) :=
  match canonical Ψ Φ with
  | none => checkStep R E t A l hA
  | some ⟨Φ', q⟩ => do
    let ⟨h⟩ ← checkStep R (E.restrict Φ' q.hs q.h1) t A l (HasTy.restrict q.hs q.h1 hA)
    pure ⟨HasTy.restrict E.hsc q.h2 h⟩

def canonWhnf (R : Rec S) (E : KCtx S Ψ Φ Γ) (t A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (ht : HasTy S Ψ Φ Γ t A) : K (Red S Ψ Φ Γ t A) :=
  match canonical Ψ Φ with
  | none => whnfMain R E t A l hA ht
  | some ⟨Φ', q⟩ => do
    let r ← whnfMain R (E.restrict Φ' q.hs q.h1) t A l (HasTy.restrict q.hs q.h1 hA)
      (HasTy.restrict q.hs q.h1 ht)
    pure ⟨r.tm, EqTm.restrict E.hsc q.h2 r.eq⟩

def canonWhnfI (R : Rec S) (E : KCtx S Ψ Φ Γ) (t : Tm) :
    K ((i : Inf S Ψ Φ Γ t) × Red S Ψ Φ Γ t i.ty) :=
  match canonical Ψ Φ with
  | none => whnfIStep R E t
  | some ⟨Φ', q⟩ => do
    let ⟨i, r⟩ ← whnfIStep R (E.restrict Φ' q.hs q.h1) t
    pure ⟨⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩,
      ⟨r.tm, EqTm.restrict E.hsc q.h2 r.eq⟩⟩

def canonConv (R : Rec S) (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat)
    (hA : HasTy S Ψ Φ Γ A (.univ l)) (t u : Tm) (ht : HasTy S Ψ Φ Γ t A)
    (hu : HasTy S Ψ Φ Γ u A) : K (PLift (EqTm S Ψ Φ Γ t u A)) :=
  if h : t = u then pure ⟨h ▸ EqTm.refl ht⟩ else
  match canonical Ψ Φ with
  | none => convStep R E A l hA t u ht hu
  | some ⟨Φ', q⟩ => do
    let ⟨e⟩ ← convStep R (E.restrict Φ' q.hs q.h1) A l (HasTy.restrict q.hs q.h1 hA) t u
      (HasTy.restrict q.hs q.h1 ht) (HasTy.restrict q.hs q.h1 hu)
    pure ⟨EqTm.restrict E.hsc q.h2 e⟩

def canonConvNe (R : Rec S) (E : KCtx S Ψ Φ Γ) (t u : Tm) :
    K ((i : Inf S Ψ Φ Γ t) × PLift (EqTm S Ψ Φ Γ t u i.ty)) :=
  match canonical Ψ Φ with
  | none => convNeStep R E t u
  | some ⟨Φ', q⟩ => do
    let ⟨i, ⟨e⟩⟩ ← convNeStep R (E.restrict Φ' q.hs q.h1) t u
    pure ⟨⟨i.ty, i.lvl, HasTy.restrict E.hsc q.h2 i.hty, HasTy.restrict E.hsc q.h2 i.htm⟩,
      ⟨EqTm.restrict E.hsc q.h2 e⟩⟩

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
def SigInfo.next (R : Rec S) (si : SigInfo S) : K (Option (SigInfo S)) :=
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
def SigInfo.build (R : Rec S) : Nat → SigInfo S → K (SigInfo S)
  | 0, si => pure si
  | n + 1, si => do
    match ← SigInfo.next R si with
    | none => pure si
    | some si' => SigInfo.build R n si'

/-- The kernel and the empty context for the signature `S`. -/
def setup (S : Sig) (fuel : Nat := defaultFuel) : K (Rec S × KCtx S 0 .one []) := do
  let R := rec S fuel
  let si ← SigInfo.build R S.length (SigInfo.empty S)
  pure (R, KCtx.root si)

/-- Check one definition `(t, A)` against the signature `S`. -/
def checkEntry (S : Sig) (t A : Tm) (fuel : Nat := defaultFuel) :
    K (PLift (t.closedB 0 0 = true ∧ A.closedB 0 0 = true ∧
      (∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A)) := do
  let (R, E) ← setup S fuel
  let ⟨l, ⟨hA⟩⟩ ← inferType R E A
  let ⟨ht⟩ ← R.check E t A l hA
  if hc : t.closedB 0 0 = true ∧ A.closedB 0 0 = true then
    pure ⟨hc.1, hc.2, ⟨l, hA⟩, ht⟩
  else fail "kernel: the definition is not closed"

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
      rw [List.take_append_of_le_length hlt]
      exact hS.2 k D hk
    · have hge : S.length ≤ k := Nat.le_of_not_lt hlt
      rw [List.getElem?_append_right hge] at hk
      cases h' : k - S.length with
      | zero => rw [h'] at hk; simp at hk
      | succ n => rw [h'] at hk; simp at hk

/-- A signature together with a proof that it is well-formed. -/
structure CheckedSig where
  sig : Sig
  wf : WfSig sig

def CheckedSig.empty : CheckedSig := ⟨[], fun k _ _ h => by simp at h, fun k _ h => by simp at h⟩

/-- Check one more definition. -/
def CheckedSig.extend (C : CheckedSig) (t A : Tm) (fuel : Nat := defaultFuel) : K CheckedSig := do
  let ⟨h⟩ ← checkEntry C.sig t A fuel
  pure ⟨C.sig ++ [.defn t A], wfSig_append C.wf h⟩

def checkSigAux (pre : Sig) (hpre : WfSig pre) : (rest : Sig) → K (PLift (WfSig (pre ++ rest)))
  | [] => pure ⟨by simpa using hpre⟩
  | .defn t A :: rest => do
    let ⟨h⟩ ← checkEntry pre t A
    let ⟨h'⟩ ← checkSigAux (pre ++ [.defn t A]) (wfSig_append hpre h) rest
    pure ⟨by simpa using h'⟩
  | .data _ :: _ => fail "kernel: inductive types are not supported yet"

/-- Check a whole signature. -/
def checkSig (S : Sig) : K (PLift (WfSig S)) := do
  let ⟨h⟩ ← checkSigAux [] ⟨fun k _ _ h => by simp at h, fun k _ h => by simp at h⟩ S
  pure ⟨by simpa using h⟩

/-- Soundness of the kernel: by construction, `checkSig` only succeeds with a proof. -/
theorem checkSig_sound {S : Sig} {h : PLift (WfSig S)} (_ : checkSig S = .ok h) : WfSig S :=
  h.down

end KubusCore.Kernel
