import KubusCore.Kernel.Conv

/-!
# Kernel: entry points

`Kernel.rec S n` ties the knot of the mutually recursive kernel functions with fuel `n`
(the nesting depth of recursive calls). `checkSig S` checks a signature and returns a proof
of `WfSig S`; `CheckedSig.extend` checks one more definition against a checked signature.
-/

namespace KubusCore.Kernel

variable {S : Sig}

/-- The kernel with `n` levels of nested recursive calls. Each level is built lazily. -/
def rec (S : Sig) : Nat → Rec S
  | 0 => Rec.bot S
  | n + 1 =>
    { infer := fun E t => inferStep (rec S n) E t
      check := fun E t A l hA => checkStep (rec S n) E t A l hA
      whnf := fun E t A l hA ht => whnfMain (rec S n) E t A l hA ht
      whnfI := fun E t => whnfIStep (rec S n) E t
      conv := fun E A l hA t u ht hu => convStep (rec S n) E A l hA t u ht hu
      convNe := fun E t u => convNeStep (rec S n) E t u }

/-- Default nesting depth. -/
def defaultFuel : Nat := 20000

/-! ## Signatures -/

/-- Add the level of the next constant's type to the signature information. -/
def SigInfo.next (R : Rec S) (si : SigInfo S) : K (Option (SigInfo S)) :=
  match h : S[si.lv.length]? with
  | none => pure none
  | some (b, A) =>
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

/-- Check one definition `(t, A)` against the signature `S`. -/
def checkEntry (S : Sig) (t A : Tm) (fuel : Nat := defaultFuel) :
    K (PLift ((∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A)) := do
  let R := rec S fuel
  let si ← SigInfo.build R S.length (SigInfo.empty S)
  let E := KCtx.root si
  let ⟨l, ⟨hA⟩⟩ ← inferType R E A
  let ⟨ht⟩ ← R.check E t A l hA
  pure ⟨⟨l, hA⟩, ht⟩

theorem wfSig_append {S : Sig} {t A : Tm} (hS : WfSig S)
    (h : (∃ l, HasTy S 0 .one [] A (.univ l)) ∧ HasTy S 0 .one [] t A) :
    WfSig (S ++ [(t, A)]) := by
  intro k t' A' hk
  by_cases hlt : k < S.length
  · rw [List.getElem?_append_left hlt] at hk
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hS k t' A' hk
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

/-- A signature together with a proof that it is well-formed. -/
structure CheckedSig where
  sig : Sig
  wf : WfSig sig

def CheckedSig.empty : CheckedSig := ⟨[], fun k _ _ h => by simp at h⟩

/-- Check one more definition. -/
def CheckedSig.extend (C : CheckedSig) (t A : Tm) (fuel : Nat := defaultFuel) : K CheckedSig := do
  let ⟨h⟩ ← checkEntry C.sig t A fuel
  pure ⟨C.sig ++ [(t, A)], wfSig_append C.wf h⟩

def checkSigAux (pre : Sig) (hpre : WfSig pre) : (rest : Sig) → K (PLift (WfSig (pre ++ rest)))
  | [] => pure ⟨by simpa using hpre⟩
  | (t, A) :: rest => do
    let ⟨h⟩ ← checkEntry pre t A
    let ⟨h'⟩ ← checkSigAux (pre ++ [(t, A)]) (wfSig_append hpre h) rest
    pure ⟨by simpa using h'⟩

/-- Check a whole signature. -/
def checkSig (S : Sig) : K (PLift (WfSig S)) := do
  let ⟨h⟩ ← checkSigAux [] (fun k _ _ h => by simp at h) S
  pure ⟨by simpa using h⟩

/-- Soundness of the kernel: by construction, `checkSig` only succeeds with a proof. -/
theorem checkSig_sound {S : Sig} {h : PLift (WfSig S)} (_ : checkSig S = .ok h) : WfSig S :=
  h.down

end KubusCore.Kernel
