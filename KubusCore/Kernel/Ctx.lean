import KubusCore.Kernel.Lemmas

/-!
# Kernel contexts

A kernel context for `Ψ; Φ; Γ` carries the universe level of every variable's type and of
every constant's type, with derivations that these types are well-formed, so that types
obtained from variables and constants can be decomposed by the inversion rules.
-/

namespace KubusCore

/-- Levels of the types of the signature's constants, with closedness and typing in the
empty context. -/
structure SigInfo (S : Sig) where
  lv : List Nat
  closed : ∀ (k : Nat) (t A : Tm), S[k]? = some (t, A) → k < lv.length → A.closedB 0 0 = true
  ok : ∀ (k : Nat) (t A : Tm) (l : Nat), S[k]? = some (t, A) → lv[k]? = some l → HasTy S 0 .one [] A (.univ l)

structure KCtx (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) where
  sig : SigInfo S
  lv : List Nat
  wf : Wf S Ψ Φ Γ
  hsc : Φ.Scoped Ψ
  varOk : ∀ (x : Nat) (A : Tm) (l : Nat), Γ.lookup x = some A → lv[x]? = some l → HasTy S Ψ Φ Γ A (.univ l)
  constOk : ∀ (k : Nat) (t A : Tm) (l : Nat), S[k]? = some (t, A) → sig.lv[k]? = some l → HasTy S Ψ Φ Γ A (.univ l)

namespace KCtx

variable {S : Sig}

def root (sig : SigInfo S) : KCtx S 0 .one [] where
  sig := sig
  lv := []
  wf := Wf.nil trivial
  hsc := trivial
  varOk := fun x A l h _ => by simp [Ctx.lookup] at h
  constOk := sig.ok

theorem lt_of_getElem? {l : List Nat} {k n : Nat} (h : l[k]? = some n) : k < l.length := by
  exact (List.getElem?_eq_some_iff.mp h).1

/-- Extend by a term variable of type `A`. -/
def ext {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (A : Tm) (l : Nat) (hA : HasTy S Ψ Φ Γ A (.univ l)) :
    KCtx S Ψ Φ (A :: Γ) where
  sig := E.sig
  lv := l :: E.lv
  wf := Wf.cons hA
  hsc := E.hsc
  varOk := by
    intro x B l' hx hl
    cases x with
    | zero =>
      simp [Ctx.lookup] at hx; simp at hl
      subst hx; subst hl
      exact HasTy.wk hA hA
    | succ x =>
      rw [Ctx.lookup_cons_succ] at hx
      simp only [List.getElem?_cons_succ] at hl
      cases h : Γ.lookup x with
      | none => rw [h] at hx; cases hx
      | some B' =>
        rw [h] at hx; simp at hx; subst hx
        exact HasTy.wk hA (E.varOk x B' l' h hl)
  constOk := by
    intro k t B l' hk hl
    have hc := E.sig.closed k t B hk (lt_of_getElem? hl)
    have := HasTy.wk hA (E.constOk k t B l' hk hl)
    rw [Tm.shift_closed hc] at this
    exact this

/-- Extend by an interval variable. -/
def dext {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) : KCtx S (Ψ + 1) Φ.shift Γ.dshift where
  sig := E.sig
  lv := E.lv
  wf := E.wf.dwk E.hsc
  hsc := I.scoped_shift E.hsc
  varOk := by
    intro x B l hx hl
    rw [Ctx.lookup_dshift] at hx
    cases h : Γ.lookup x with
    | none => rw [h] at hx; cases hx
    | some B' =>
      rw [h] at hx; simp at hx; subst hx
      exact HasTy.dwk (E.varOk x B' l h hl)
  constOk := by
    intro k t B l hk hl
    have hc := E.sig.closed k t B hk (lt_of_getElem? hl)
    have := HasTy.dwk (E.constOk k t B l hk hl)
    rw [Tm.dshift_closed hc] at this
    exact this

/-- Strengthen the restriction to `Φ'` with `Φ' ⊨ Φ`. -/
def restrict {Ψ Φ Γ} (E : KCtx S Ψ Φ Γ) (Φ' : I) (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    KCtx S Ψ Φ' Γ where
  sig := E.sig
  lv := E.lv
  wf := E.wf.restrict hs he
  hsc := hs
  varOk := fun x A l hx hl => HasTy.restrict hs he (E.varOk x A l hx hl)
  constOk := fun k t A l hk hl => HasTy.restrict hs he (E.constOk k t A l hk hl)

end KCtx

end KubusCore
