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

/-! ### The interpretation of the equivalence type formers -/

section sem

variable {S : Sig}

theorem sem_fiber {T A f y : Tm} {ρ : IEnv k} {γ : ℕ → V} (hT : Natural S T k ρ γ) (hA : Natural S A k ρ γ)
    (hf : Natural S f k ρ γ) (hy : Natural S y k ρ γ) (hTf : Fib (sem S T k ρ γ) k) (hAf : Fib (sem S A k ρ γ) k)
    (hfm : sem S f k ρ γ ∈ El (arrowM k (sem S T k ρ γ) (sem S A k ρ γ)) (Hom.id k)) :
    sem S (Tm.fiber T A f y) k ρ γ = fiberM k (sem S T k ρ γ) (sem S A k ρ γ) (sem S f k ρ γ) (sem S y k ρ γ) := by
  unfold Tm.fiber Tm.pathC
  rw [sem_sigma hTf.kv]
  unfold fiberM
  congr 1
  apply famV_congr
  intro k' g t ht
  have hN : Natural S A.shift.dshift (k' + 1) (ρ.restr g).ext
      (TEnv.restr (TEnv.cons (TEnv.restr γ g) t) (Hom.wk k')) := ((hA.restr g).shift t).dshift
  have eL : lineV S A.shift.dshift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) t) = res (Hom.wk k') (res g (sem S A k ρ γ)) := by
    show sem S A.shift.dshift (k' + 1) (ρ.restr g).ext _ = _
    rw [sem_dshift, TEnv.restr_cons, sem_shift, hA.restr g (k' + 1) (Hom.wk k'), hA k' g]
  have hfg := arrowM_elRes hTf.kv hfm g
  have htg : t ∈ El (res g (sem S T k ρ γ)) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact ht
  have ea : sem S (.app f.shift (.var 0)) k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) t) =
      appV k' (res g (sem S f k ρ γ)) t := by
    rw [sem_app_of_nat (natural_var S 0 _ _), sem_shift, sem_var, TEnv.cons_zero, hf k' g]
  have hakv : IsKV k' (appV k' (res g (sem S f k ρ γ)) t) :=
    (hAf.restr g).elKV _ _ _ (appV_arrowM (isKV_res _ _) hfg htg)
  rw [sem_path hN (by rw [eL]; exact isKV_res _ _) (by rw [ea]; exact hakv)
    (by rw [sem_shift, hy k' g]; exact isKV_res _ _), eL, ea, sem_shift, hy k' g]

theorem natural_fiber {T A f y : Tm} {ρ : IEnv k} {γ : ℕ → V} (hT : Natural S T k ρ γ) (hA : Natural S A k ρ γ)
    (hf : Natural S f k ρ γ) (hy : Natural S y k ρ γ) (hTf : Fib (sem S T k ρ γ) k) (hAf : Fib (sem S A k ρ γ) k)
    (hfm : sem S f k ρ γ ∈ El (arrowM k (sem S T k ρ γ) (sem S A k ρ γ)) (Hom.id k)) :
    Natural S (Tm.fiber T A f y) k ρ γ := by
  intro n g
  have hfm' := arrowM_elRes hTf.kv hfm g
  rw [← hT n g, ← hA n g, ← hf n g] at hfm'
  rw [sem_fiber (hT.restr g) (hA.restr g) (hf.restr g) (hy.restr g) (by rw [hT n g]; exact hTf.restr g)
    (by rw [hA n g]; exact hAf.restr g) hfm', sem_fiber hT hA hf hy hTf hAf hfm, res_fiberM, hT n g, hA n g,
    hf n g, hy n g]

theorem sem_isContr {X : Tm} {ρ : IEnv k} {γ : ℕ → V} (hX : Natural S X k ρ γ) (hXf : Fib (sem S X k ρ γ) k) :
    sem S (Tm.isContr X) k ρ γ = isContrM k (sem S X k ρ γ) := by
  unfold Tm.isContr Tm.pathC
  rw [sem_sigma hXf.kv]
  unfold isContrM
  congr 1
  apply famV_congr
  intro k' g c hc
  have eX : sem S X.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) c) = res g (sem S X k ρ γ) := by
    rw [sem_shift, hX k' g]
  rw [sem_pi (by rw [eX]; exact isKV_res _ _), eX]
  congr 1
  apply famV_congr
  intro k'' h x hx
  set env := TEnv.cons (TEnv.restr (TEnv.cons (TEnv.restr γ g) c) h) x
  have hN : Natural S X.shift.shift.dshift (k'' + 1) ((ρ.restr g).restr h).ext (TEnv.restr env (Hom.wk k'')) :=
    (((((hX.restr g).shift c).restr h).shift x)).dshift
  have eL : lineV S X.shift.shift.dshift k'' ((ρ.restr g).restr h) env =
      res (Hom.wk k'') (res h (res g (sem S X k ρ γ))) := by
    show sem S X.shift.shift.dshift (k'' + 1) ((ρ.restr g).restr h).ext _ = _
    rw [sem_dshift, TEnv.restr_cons, sem_shift, TEnv.restr_restr, TEnv.restr_cons, sem_shift, IEnv.restr_restr,
      IEnv.restr_restr, TEnv.restr_restr, hX, res_res, res_res]
  have hxkv : IsKV k'' x := (hXf.restr g).elKV _ _ _ hx
  rw [sem_path (a := .var 1) (b := .var 0) hN (by rw [eL]; exact isKV_res _ _) (isKV_res _ _) hxkv, eL]
  rfl

theorem sem_isEquiv {T A f : Tm} {ρ : IEnv k} {γ : ℕ → V} (hT : Natural S T k ρ γ) (hA : Natural S A k ρ γ)
    (hf : Natural S f k ρ γ) (hTf : Fib (sem S T k ρ γ) k) (hAf : Fib (sem S A k ρ γ) k)
    (hfm : sem S f k ρ γ ∈ El (arrowM k (sem S T k ρ γ) (sem S A k ρ γ)) (Hom.id k)) :
    sem S (Tm.isEquiv T A f) k ρ γ = isEquivM k (sem S T k ρ γ) (sem S A k ρ γ) (sem S f k ρ γ) := by
  unfold Tm.isEquiv
  rw [sem_pi hAf.kv]
  unfold isEquivM
  congr 1
  apply famV_congr
  intro k' g y hy
  have eT : sem S T.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) = res g (sem S T k ρ γ) := by
    rw [sem_shift, hT k' g]
  have eA : sem S A.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) = res g (sem S A k ρ γ) := by
    rw [sem_shift, hA k' g]
  have ef : sem S f.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) = res g (sem S f k ρ γ) := by
    rw [sem_shift, hf k' g]
  have hTf' : Fib (sem S T.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y)) k' := by rw [eT]; exact hTf.restr g
  have hAf' : Fib (sem S A.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y)) k' := by rw [eA]; exact hAf.restr g
  have hfm' : sem S f.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) ∈
      El (arrowM k' (sem S T.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y))
        (sem S A.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y))) (Hom.id k') := by
    rw [eT, eA, ef]; exact arrowM_elRes hTf.kv hfm g
  have hnT := (hT.restr g).shift y
  have hnA := (hA.restr g).shift y
  have hnf := (hf.restr g).shift y
  have hfib := sem_fiber (y := .var 0) hnT hnA hnf (natural_var S 0 _ _) hTf' hAf' hfm'
  have hyA : y ∈ El (res g (sem S A k ρ γ)) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact hy
  rw [sem_isContr (natural_fiber hnT hnA hnf (natural_var S 0 _ _) hTf' hAf' hfm')
    (by rw [hfib, eT, eA, ef]; exact fib_fiberM (hTf.restr g) (hAf.restr g) (arrowM_elRes hTf.kv hfm g) hyA),
    hfib, eT, eA, ef]
  rfl

theorem sem_equivT {T A : Tm} {ρ : IEnv k} {γ : ℕ → V} (hT : Natural S T k ρ γ) (hA : Natural S A k ρ γ)
    (hTf : Fib (sem S T k ρ γ) k) (hAf : Fib (sem S A k ρ γ) k) :
    sem S (Tm.equiv T A) k ρ γ = equivM k (sem S T k ρ γ) (sem S A k ρ γ) := by
  unfold Tm.equiv Tm.arrow
  have eArr : sem S (.pi T A.shift) k ρ γ = arrowM k (sem S T k ρ γ) (sem S A k ρ γ) := by
    rw [sem_pi hTf.kv]; unfold arrowM; congr 1; apply famV_congr; intro k' g t _; rw [sem_shift, hA k' g]
  have hPkv : IsKV k (arrowM k (sem S T k ρ γ) (sem S A k ρ γ)) := by unfold arrowM piC; exact isKV_mkKV _
  rw [sem_sigma (by rw [eArr]; exact hPkv), eArr]
  unfold equivM
  congr 1
  apply famV_congr
  intro k' g p hp
  have eT : sem S T.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) p) = res g (sem S T k ρ γ) := by
    rw [sem_shift, hT k' g]
  have eA : sem S A.shift k' (ρ.restr g) (TEnv.cons (TEnv.restr γ g) p) = res g (sem S A k ρ γ) := by
    rw [sem_shift, hA k' g]
  have hpm : p ∈ El (arrowM k' (res g (sem S T k ρ γ)) (res g (sem S A k ρ γ))) (Hom.id k') := by
    rw [← res_arrowM, El_res, Hom.comp_id]; exact hp
  rw [sem_isEquiv ((hT.restr g).shift p) ((hA.restr g).shift p) (natural_var S 0 _ _)
    (by rw [eT]; exact hTf.restr g) (by rw [eA]; exact hAf.restr g) (by rw [eT, eA]; exact hpm), eT, eA]
  rfl

end sem

/-- For fibrant `T`, `A`, the code `Equiv T A` is the model code `equivM`. -/
theorem equivCode_eq_equivM {T A : V} (hT : Fib T m) (hA : Fib A m) : equivCode m T A = equivM m T A := by
  unfold equivCode
  rw [interp_congr_pure (fun _ _ => ∅) (cstFn []) (fun _ _ => ∅) univC (fun _ _ => True) TyCode _ (by decide)]
  exact sem_equivT (S := []) (natural_var _ 1 _ _) (natural_var _ 0 _ _) hT hA


/-! ### Elements of the model codes -/

theorem mem_sigmaC_id {A B v : V} (hA : IsKV k A) (hB : IsKV k B) :
    v ∈ El (sigmaC k A B) (Hom.id k) ↔ ∃ a ∈ El A (Hom.id k), ∃ b ∈ El (apZ (dat B k (Hom.id k)) a) (Hom.id k),
      v = pairV k a b := by
  rw [El_sigmaC, res_id hA, res_id hB, sigmaElSet, mem_sigmaEl]

theorem mem_fiberM {T A f y v : V} (hT : IsKV k T) (hA : IsKV k A) (hf : IsKV k f) (hy : IsKV k y)
    (hv : v ∈ El (fiberM k T A f y) (Hom.id k)) :
    ∃ t ∈ El T (Hom.id k), ∃ p ∈ El (pathC k (res (Hom.wk k) A) (appV k f t) y) (Hom.id k), v = pairV k t p := by
  unfold fiberM at hv
  rw [mem_sigmaC_id hT (isKV_famV _ _)] at hv
  obtain ⟨t, ht, p, hp, rfl⟩ := hv
  rw [apZ_dat_famV _ _ _ ht, res_id hA, res_id hf, res_id hy] at hp
  exact ⟨t, ht, p, hp, rfl⟩

theorem pairV_mem_fiberM {T A f y t p : V} (hT : IsKV k T) (hA : IsKV k A) (hf : IsKV k f) (hy : IsKV k y)
    (ht : t ∈ El T (Hom.id k)) (hp : p ∈ El (pathC k (res (Hom.wk k) A) (appV k f t) y) (Hom.id k)) :
    pairV k t p ∈ El (fiberM k T A f y) (Hom.id k) := by
  unfold fiberM
  rw [mem_sigmaC_id hT (isKV_famV _ _)]
  refine ⟨t, ht, p, ?_, rfl⟩
  rw [apZ_dat_famV _ _ _ ht, res_id hA, res_id hf, res_id hy]; exact hp

theorem mem_isContrM {X c : V} (hX : Fib X k) (hc : c ∈ El (isContrM k X) (Hom.id k)) :
    ∃ cen ∈ El X (Hom.id k), ∃ ctr ∈ piElSet k X (famV k X fun k' h x => pathC k' (res (Hom.wk k') (res h X)) (res h cen) x),
      c = pairV k cen ctr := by
  unfold isContrM at hc
  rw [mem_sigmaC_id hX.kv (isKV_famV _ _)] at hc
  obtain ⟨cen, hcen, ctr, hctr, rfl⟩ := hc
  rw [apZ_dat_famV _ _ _ hcen, res_id hX.kv, El_piC, res_id hX.kv, res_id (isKV_famV _ _)] at hctr
  exact ⟨cen, hcen, ctr, hctr, rfl⟩

theorem mem_equivM {T A e : V} (hT : Fib T k) (hA : Fib A k) (he : e ∈ El (equivM k T A) (Hom.id k)) :
    ∃ p ∈ El (arrowM k T A) (Hom.id k),
      ∃ q ∈ piElSet k A (famV k A fun k' g y => isContrM k' (fiberM k' (res g T) (res g A) (res g p) y)),
      e = pairV k p q := by
  have hPkv : IsKV k (arrowM k T A) := by unfold arrowM piC; exact isKV_mkKV _
  unfold equivM at he
  rw [mem_sigmaC_id hPkv (isKV_famV _ _)] at he
  obtain ⟨p, hp, q, hq, rfl⟩ := he
  rw [apZ_dat_famV _ _ _ hp, res_id hT.kv, res_id hA.kv] at hq
  unfold isEquivM at hq
  rw [El_piC, res_id hA.kv, res_id (isKV_famV _ _)] at hq
  exact ⟨p, hp, q, hq, rfl⟩

end

end Model
