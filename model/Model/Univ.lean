import Model.Interp
import Model.Tower

/-!
# The empty type, well-formed codes, universes

`WF l m c`: `c` is a well-formed code of level `l` at stage `m`, an inductive predicate on the
intensional shape of codes. This is what validates the spec's inversion rules (`piDom`, …): a
Π-code is well-formed at level `l` only if its domain and codomain family are.

The universe `U_l` at stage `m` is the code `univC m l` whose elements are the well-formed level-`l`
codes in `Vt l`. Universes are defined by recursion on the level (`Ucodes`), since `WF l` refers to
the codes of the universes below `l`.

The empty type `emptyC` belongs to `U_0`; it is what refutes `(X : U₀) → X`.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

section
variable {k m n : ℕ}

/-! ### The empty type -/

def emptyDatum : V := quad (tagZ tEmpty ∅) ∅ ∅ ∅

def emptyC (m : ℕ) : V := mkKV m fun _ _ => emptyDatum

@[simp] theorem El_emptyC (f : Hom k m) : El (emptyC m) f = ∅ := by simp [emptyC, emptyDatum]

theorem res_emptyC (h : Hom k m) : res h (emptyC m) = emptyC k := by simp [emptyC]

theorem fib_emptyC : Fib (emptyC m) m where
  kv := isKV_mkKV _
  elKV _ _ _ hv := by simp at hv
  elRes _ _ _ hv := by simp at hv
  hcMem _ _ _ _ _ _ hu0 := by simp at hu0
  hcFace _ _ _ _ _ _ hu0 := by simp at hu0
  hcRes _ _ _ _ _ _ hu0 := by simp at hu0
  trMem _ _ _ _ _ _ ha := by simp at ha
  trFace _ _ _ _ _ _ ha := by simp at ha
  trRes _ _ _ _ _ _ ha := by simp at ha

end

/-! ### Equivalences -/

/-- The code `Equiv T A` (the spec's `Tm.equiv`) for codes `T`, `A` at stage `m`. -/
def equivCode (m : ℕ) (T A : V) : V :=
  interp (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => True) (Tm.equiv (.var 1) (.var 0)) m (fun _ => DM.zero m)
    (TEnv.cons (TEnv.cons (fun _ => ∅) T) A)

/-! ### Universes -/

def univTr (W : ℕ → V → Prop) (l : ℕ) : ℕ → V
  | 0 => ∅
  | n + 1 => trGraph n (ZFSet.sep (W n) (Vt l)) fun _ a => a

/-- The datum of the universe of level `l` at stage `k`, given its well-formedness predicate.
TODO: `hcomp` in the universe (Glue along the transport equivalence). -/
def univDatum (W : ℕ → V → Prop) (l k : ℕ) : V :=
  quad (tagZ tUniv (natZ l)) (ZFSet.sep (W k) (Vt l)) (univTr W l k) ∅

def univCode (W : ℕ → V → Prop) (l m : ℕ) : V := mkKV m fun k _ => univDatum W l k

/-- Well-formed codes of level `l`, given the codes `U m l'` of the universes below `l`. -/
inductive WFI (U : ℕ → ℕ → V) (l : ℕ) : ℕ → V → Prop
  | empty {m} : WFI U l m (emptyC m)
  | pi {m A B} : WFI U l m A → IsKV m B →
      (∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f))) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, WFI U l k (apZ (dat B k f) a)) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
        res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)) →
      WFI U l m (piC m A B)
  | sigma {m A B} : WFI U l m A → IsKV m B →
      (∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f))) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, WFI U l k (apZ (dat B k f) a)) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
        res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)) →
      WFI U l m (sigmaC m A B)
  | path {m L a0 a1} : WFI U l (m + 1) L → a0 ∈ El L (Hom.endpt m (DM.zero m)) →
      a1 ∈ El L (Hom.endpt m (DM.one m)) → WFI U l m (pathC m L a0 a1)
  | ipi {m L} : WFI U l (m + 1) L → WFI U l m (ipiC m L)
  | univ {m l'} : l' < l → WFI U l m (U m l')
  | glue {m A φ Tp ep} : WFI U l m A → φ.IsCof → ¬ φ.holds →
      Tp = partialKV m φ (fun k f => dat Tp k f) → ep = partialKV m φ (fun k f => dat ep k f) →
      (∀ k (f : Hom k m), (φ.restr f).holds → WFI U l k (dat Tp k f)) →
      (∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h)) →
      (∀ k (f : Hom k m), (φ.restr f).holds →
        dat ep k f ∈ El (equivCode k (dat Tp k f) (res f A)) (Hom.id k)) →
      (∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat ep k f) = dat ep n (f.comp h)) →
      WFI U l m (glueC m A φ Tp ep)

/-- The universe codes below a level bound. -/
def Ucodes : ℕ → ℕ → ℕ → V
  | 0 => fun _ _ => ∅
  | l + 1 => fun m l' =>
    if l' < l then Ucodes l m l' else if l' = l then univCode (WFI (Ucodes l) l) l m else ∅

/-- Well-formed codes of level `l`. -/
def WF (l : ℕ) : ℕ → V → Prop := WFI (Ucodes l) l

/-- The code of the universe `U_l` at stage `m`. -/
def univC (m l : ℕ) : V := univCode (WF l) l m

variable {k m n : ℕ}

theorem Ucodes_lt : ∀ {l l' : ℕ} (m : ℕ), l' < l → Ucodes l m l' = univC m l'
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | l + 1, l', m, h => by
    simp only [Ucodes]
    by_cases h1 : l' < l
    · rw [if_pos h1]; exact Ucodes_lt m h1
    · rw [if_neg h1, if_pos (by omega)]
      have : l' = l := by omega
      subst this; rfl

@[simp] theorem El_univC (l : ℕ) (f : Hom k m) : El (univC m l) f = ZFSet.sep (WF l k) (Vt l) := by
  simp [univC, univCode, univDatum]

theorem res_univC (l : ℕ) (h : Hom k m) : res h (univC m l) = univC k l := by
  simp [univC, univCode]

end

end Model
