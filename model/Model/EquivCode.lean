import Model.SemBasic
import Model.GlueElem

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

/-- Terms without constants, universes and Kan operations. -/
def _root_.KubusCore.Tm.pureB : Tm → Bool
  | .var _ | .abort => true
  | .const _ | .univ _ | .transp _ _ _ | .hcomp _ _ _ _ => false
  | .pi A B | .sigma A B | .lam A B | .app A B | .pair A B => A.pureB && B.pureB
  | .fst p | .snd p | .plam p | .ipi p | .papp p _ => p.pureB
  | .unglue _ e g => e.pureB && g.pureB
  | .path A a b => A.pureB && a.pureB && b.pureB
  | .split _ t _ u => t.pureB && u.pureB
  | .glue A _ T e => A.pureB && T.pureB && e.pureB
  | .glueEl _ e t a => e.pureB && t.pureB && a.pureB

/-- The denotation of a pure term does not depend on constants, universes and good codes. -/
theorem interp_congr_pure (cst cst' uc uc' : ℕ → ℕ → V) (good good' : ℕ → V → Prop) :
    ∀ (t : Tm), t.pureB = true → interp cst uc good t = interp cst' uc' good' t := by
  intro t
  induction t with
  | var _ | abort => intro _; rfl
  | const _ | univ _ => intro h; simp [Tm.pureB] at h
  | transp _ _ _ _ _ => intro h; simp [Tm.pureB] at h
  | hcomp _ _ _ _ _ _ _ => intro h; simp [Tm.pureB] at h
  | pi _ _ iA iB | sigma _ _ iA iB | lam _ _ iA iB | app _ _ iA iB | pair _ _ iA iB =>
    intro h; simp only [Tm.pureB, Bool.and_eq_true] at h
    funext m ρ γ; simp only [interp]; rw [iA h.1, iB h.2]
  | fst _ ip | snd _ ip | plam _ ip | ipi _ ip | papp _ _ ip =>
    intro h; simp only [Tm.pureB] at h
    funext m ρ γ; simp only [interp]; rw [ip h]
  | unglue _ _ _ ie ig =>
    intro h; simp only [Tm.pureB, Bool.and_eq_true] at h
    funext m ρ γ; simp only [interp]; rw [ie h.1, ig h.2]
  | path _ _ _ iA ia ib | glue _ _ _ _ iA ia ib | glueEl _ _ _ _ iA ia ib =>
    intro h; simp only [Tm.pureB, Bool.and_eq_true] at h
    funext m ρ γ; simp only [interp]; rw [iA h.1.1, ia h.1.2, ib h.2]
  | split _ _ _ _ it iu =>
    intro h; simp only [Tm.pureB, Bool.and_eq_true] at h
    funext m ρ γ; simp only [interp]; rw [it h.1, iu h.2]

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

/-! ### Restriction and fibrancy of the model codes -/

theorem famV_graph (A : V) (F : (k : ℕ) → Hom k m → V → V) (f : Hom k m) :
    dat (famV m A F) k f = fnZ (El A f) (apZ (dat (famV m A F) k f)) := by
  have e := dat_famV A F f
  rw [e]; exact fnZ_congr fun t ht => (apZ_fnZ (F k f) ht).symm

theorem res_arrowM (T A : V) (h : Hom n k) : res h (arrowM k T A) = arrowM n (res h T) (res h A) := by
  unfold arrowM; rw [res_piC, res_famV]; simp only [res_res]

theorem res_fiberM (T A f y : V) (h : Hom n k) :
    res h (fiberM k T A f y) = fiberM n (res h T) (res h A) (res h f) (res h y) := by
  unfold fiberM; rw [res_sigmaC, res_famV]; simp only [res_res]

theorem mem_arrowM {T A f : V} (hT : IsKV k T) (hf : f ∈ El (arrowM k T A) (Hom.id k)) :
    f ∈ piElSet k T (famV k T fun _ g _ => res g A) := by
  unfold arrowM at hf; rwa [El_piC, res_id hT, res_id (isKV_famV _ _)] at hf

theorem appV_arrowM {T A f t : V} (hT : IsKV k T) (hf : f ∈ El (arrowM k T A) (Hom.id k))
    (ht : t ∈ El T (Hom.id k)) : appV k f t ∈ El A (Hom.id k) := by
  have := appV_mem_piElSet (mem_arrowM hT hf) ht
  rwa [apZ_dat_famV _ _ _ ht, El_res, Hom.comp_id] at this

theorem appV_arrowM_res {T A f t : V} (hT : IsKV k T) (hf : f ∈ El (arrowM k T A) (Hom.id k))
    (ht : t ∈ El T (Hom.id k)) (h : Hom n k) : res h (appV k f t) = appV n (res h f) (res h t) :=
  res_appV (mem_arrowM hT hf) ht h

theorem arrowM_elRes {T A f : V} (hT : IsKV k T) (hf : f ∈ El (arrowM k T A) (Hom.id k)) (h : Hom n k) :
    res h f ∈ El (arrowM n (res h T) (res h A)) (Hom.id n) := by
  rw [← res_arrowM, El_res, Hom.comp_id]
  unfold arrowM; rw [El_piC]; exact res_mem_piElSet (mem_arrowM hT hf) h

/-- Fiber codes of fibrant codes are fibrant. -/
theorem fib_fiberM {T A f y : V} (hT : Fib T k) (hA : Fib A k) (hf : f ∈ El (arrowM k T A) (Hom.id k))
    (hy : y ∈ El A (Hom.id k)) : Fib (fiberM k T A f y) k := by
  unfold fiberM
  refine fib_sigmaC hT ⟨isKV_famV _ _, fun k' g => ?_, fun k' g t ht => ?_, fun k' g t ht n h => ?_⟩
  · exact famV_graph _ _ _
  · rw [apZ_dat_famV _ _ _ ht]
    have hfg := arrowM_elRes hT.kv hf g
    have htg : t ∈ El (res g T) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact ht
    refine fib_pathC ((hA.restr g).restr (Hom.wk k')) ?_ ?_
    · rw [El_res, Hom.wk_comp_endpt, El_res, Hom.comp_id]
      have := appV_arrowM (hT.restr g).kv hfg htg
      rwa [El_res, Hom.comp_id] at this
    · rw [El_res, Hom.wk_comp_endpt, El_res, Hom.comp_id]
      have := hA.elRes _ _ _ hy k' g; rwa [Hom.id_comp] at this
  · have hfg := arrowM_elRes hT.kv hf g
    have htg : t ∈ El (res g T) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact ht
    rw [apZ_dat_famV _ _ _ ht, apZ_dat_famV _ _ _ (hT.elRes _ _ _ ht n h), res_pathC, res_res, res_res,
      Hom.wk_comp_lift, ← res_res, ← res_res g, appV_arrowM_res (hT.restr g).kv hfg htg h, res_res, res_res,
      res_res, res_res, res_res]

end

end Model
