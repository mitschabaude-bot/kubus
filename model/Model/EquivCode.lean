import Model.GlueFib

/-!
# The code of equivalences, concretely

`equivCode m T A` is defined as the interpretation of the spec's `Tm.equiv`; here we compute it
as a model code `equivM` built from `sigmaC`, `piC` and `pathC`, for fibrant `T` and `A`. This
gives access to the contractibility data of an equivalence (used by Glue transport).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem lamV_congr {D : (n : ℕ) → Hom n k → V} {F G : (n : ℕ) → Hom n k → V → V}
    (h : ∀ n (g : Hom n k), ∀ a ∈ D n g, F n g a = G n g a) : lamV k D F = lamV k D G := by
  unfold lamV; congr 1; funext n g; exact fnZ_congr (h n g)

theorem famV_congr {A : V} {F G : (n : ℕ) → Hom n m → V → V}
    (h : ∀ n (g : Hom n m), ∀ a ∈ El A g, F n g a = G n g a) : famV m A F = famV m A G :=
  lamV_congr h

/-! ### The model codes -/

/-- `fiber f y = Σ (t : T), Path A (f t) y`. -/
def fiberM (k : ℕ) (T A f y : V) : V :=
  sigmaC k T (famV k T fun k' g t => pathC k' (res (Hom.wk k') (res g A)) (appV k' (res g f) t) (res g y))

/-- `isContr X = Σ (c : X), (x : X) → Path X c x`. -/
def isContrM (k : ℕ) (X : V) : V :=
  sigmaC k X (famV k X fun k' g c => piC k' (res g X)
    (famV k' (res g X) fun k'' h x => pathC k'' (res (Hom.wk k'') (res h (res g X))) (res h c) x))

/-- `isEquiv f = (y : A) → isContr (fiber f y)`. -/
def isEquivM (k : ℕ) (T A f : V) : V :=
  piC k A (famV k A fun k' g y => isContrM k' (fiberM k' (res g T) (res g A) (res g f) y))

/-- `T → A`. -/
def arrowM (k : ℕ) (T A : V) : V := piC k T (famV k T fun _ g _ => res g A)

/-- `Equiv T A = Σ (f : T → A), isEquiv f`. -/
def equivM (k : ℕ) (T A : V) : V :=
  sigmaC k (arrowM k T A) (famV k (arrowM k T A) fun k' g p => isEquivM k' (res g T) (res g A) p)

/-! ### Unfolding the interpretation -/

section interp

variable (cst uc : ℕ → ℕ → V) (good : ℕ → V → Prop)

theorem interp_sigma_kv {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (hA : IsKV m (interp cst uc good A m ρ γ)) :
    interp cst uc good (.sigma A B) m ρ γ = sigmaC m (interp cst uc good A m ρ γ)
      (famV m (interp cst uc good A m ρ γ) fun k f a =>
        interp cst uc good B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) := by
  simp only [interp]; rw [if_pos hA]

theorem interp_pi_kv {A B : Tm} {ρ : IEnv m} {γ : ℕ → V} (hA : IsKV m (interp cst uc good A m ρ γ)) :
    interp cst uc good (.pi A B) m ρ γ = piC m (interp cst uc good A m ρ γ)
      (famV m (interp cst uc good A m ρ γ) fun k f a =>
        interp cst uc good B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)) := by
  simp only [interp]; rw [if_pos hA]

end interp

end

end Model
