import Model.Canon.Unfold

/-!
# Canonicity: induction on well-formed codes

By the level, then on the derivation of well-formedness: the universes below a level are handled
by the induction hypothesis for that level.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore ZFSet

noncomputable section

variable {k m : ℕ}

theorem code_ind (P : ℕ → V → Prop)
    (hemp : ∀ m, P m (emptyC m))
    (hpi : ∀ l m A B, WF l m A → IsKV m B →
      (∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f))) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, WF l k (apZ (dat B k f) a)) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
        res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)) →
      P m A → (∀ k (f : Hom k m), ∀ a ∈ El A f, P k (apZ (dat B k f) a)) → P m (piC m A B))
    (hsigma : ∀ l m A B, WF l m A → IsKV m B →
      (∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f))) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, WF l k (apZ (dat B k f) a)) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
        res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)) →
      P m A → (∀ k (f : Hom k m), ∀ a ∈ El A f, P k (apZ (dat B k f) a)) → P m (sigmaC m A B))
    (hpath : ∀ l m L a0 a1, WF l (m + 1) L → a0 ∈ El L (Hom.endpt m (DM.zero m)) →
      a1 ∈ El L (Hom.endpt m (DM.one m)) → P (m + 1) L → P m (pathC m L a0 a1))
    (hipi : ∀ l m L, WF l (m + 1) L → P (m + 1) L → P m (ipiC m L))
    (huniv : ∀ m l, l ≤ maxLevel → (∀ m' X, WF l m' X → P m' X) → P m (univC m l))
    (hglue : ∀ l m A (φ : Cof m) Tp ep, l ≤ maxLevel → WF l m A → φ.IsCof → ¬ φ.holds →
      Tp = partialKV m φ (fun k f => dat Tp k f) → ep = partialKV m φ (fun k f => dat ep k f) →
      (∀ k (f : Hom k m), (φ.restr f).holds → WF l k (dat Tp k f)) →
      (∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h)) →
      (∀ k (f : Hom k m), (φ.restr f).holds →
        dat ep k f ∈ El (equivCode k (dat Tp k f) (res f A)) (Hom.id k)) →
      (∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat ep k f) = dat ep n (f.comp h)) →
      P m A → (∀ k (f : Hom k m), (φ.restr f).holds → P k (dat Tp k f)) → P m (glueC m A φ Tp ep))
    (hdata : ∀ l m (Θ : SData m), Θ.GoodCore →
      (∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → WF l n (Θ.ty c j n g pre)) →
      (∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → P n (Θ.ty c j n g pre)) → P m (dataC Θ)) :
    ∀ l, l ≤ maxLevel → ∀ m X, WF l m X → P m X := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ihl =>
    intro hl m X hX
    induction hX with
    | empty => exact hemp _
    | pi hA hB hBf hBw hBn ihA ihB => exact hpi l _ _ _ hA hB hBf hBw hBn ihA ihB
    | sigma hA hB hBf hBw hBn ihA ihB => exact hsigma l _ _ _ hA hB hBf hBw hBn ihA ihB
    | path hL h0 h1 ihL => exact hpath l _ _ _ _ hL h0 h1 ihL
    | ipi hL ihL => exact hipi l _ _ hL ihL
    | @univ m l' hl' =>
      show P m (Ucodes l m l')
      rw [Ucodes_lt m hl']
      exact huniv m l' (by omega) fun m' X hX => ihl l' hl' (by omega) m' X hX
    | glue hA hφ hn hTp hep hTw hTn hem hen ihA ihT =>
      exact hglue l _ _ _ _ _ hl hA hφ hn hTp hep hTw hTn hem hen ihA ihT
    | data Θ hc hw ih => exact hdata l _ Θ hc hw ih

/-- The induction principle for the codes of types (`TyCode`: well-formed codes and universes). -/
theorem tyCode_ind (P : ℕ → V → Prop)
    (hemp : ∀ m, P m (emptyC m))
    (hpi : ∀ l m A B, WF l m A → IsKV m B →
      (∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f))) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, WF l k (apZ (dat B k f) a)) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
        res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)) →
      P m A → (∀ k (f : Hom k m), ∀ a ∈ El A f, P k (apZ (dat B k f) a)) → P m (piC m A B))
    (hsigma : ∀ l m A B, WF l m A → IsKV m B →
      (∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f))) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, WF l k (apZ (dat B k f) a)) →
      (∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
        res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)) →
      P m A → (∀ k (f : Hom k m), ∀ a ∈ El A f, P k (apZ (dat B k f) a)) → P m (sigmaC m A B))
    (hpath : ∀ l m L a0 a1, WF l (m + 1) L → a0 ∈ El L (Hom.endpt m (DM.zero m)) →
      a1 ∈ El L (Hom.endpt m (DM.one m)) → P (m + 1) L → P m (pathC m L a0 a1))
    (hipi : ∀ l m L, WF l (m + 1) L → P (m + 1) L → P m (ipiC m L))
    (huniv : ∀ m l, l ≤ maxLevel → (∀ m' X, WF l m' X → P m' X) → P m (univC m l))
    (hglue : ∀ l m A (φ : Cof m) Tp ep, l ≤ maxLevel → WF l m A → φ.IsCof → ¬ φ.holds →
      Tp = partialKV m φ (fun k f => dat Tp k f) → ep = partialKV m φ (fun k f => dat ep k f) →
      (∀ k (f : Hom k m), (φ.restr f).holds → WF l k (dat Tp k f)) →
      (∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h)) →
      (∀ k (f : Hom k m), (φ.restr f).holds →
        dat ep k f ∈ El (equivCode k (dat Tp k f) (res f A)) (Hom.id k)) →
      (∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat ep k f) = dat ep n (f.comp h)) →
      P m A → (∀ k (f : Hom k m), (φ.restr f).holds → P k (dat Tp k f)) → P m (glueC m A φ Tp ep))
    (hdata : ∀ l m (Θ : SData m), Θ.GoodCore →
      (∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → WF l n (Θ.ty c j n g pre)) →
      (∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → P n (Θ.ty c j n g pre)) → P m (dataC Θ)) :
    ∀ m X, TyCode m X → P m X := by
  have hwf := code_ind P hemp hpi hsigma hpath hipi huniv hglue hdata
  rintro m X ⟨l, hl, (⟨hX, -⟩ | rfl)⟩
  · exact hwf l hl m X hX
  · exact huniv m l hl fun m' X hX => hwf l hl m' X hX

end

end Model.Canon
