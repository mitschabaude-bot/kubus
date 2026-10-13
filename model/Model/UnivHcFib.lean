import Model.GlueTransp
import Model.Small

/-!
# `hcomp` in the universe: fibrancy

Transport along a line of codes is an equivalence (`eqTr_mem`), so `univHcF` is a well-formed Glue
code; it is `u(1)` on the face of the tube, and natural.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k k' m n n' : ℕ}

/-! ### The equivalence codes are fibrant -/

theorem famOK_famV {A : V} {F : (k : ℕ) → Hom k m → V → V} (hA : Fib A m)
    (hfib : ∀ k (f : Hom k m), ∀ a ∈ El A f, Fib (F k f a) k)
    (hcoh : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k), res h (F k f a) = F n (f.comp h) (res h a)) :
    FamOK A (famV m A F) m :=
  ⟨isKV_famV _ _, fun k f => famV_graph _ _ _, fun k f a ha => by rw [apZ_dat_famV _ _ _ ha]; exact hfib k f a ha,
    fun k f a ha n h => by
      rw [apZ_dat_famV _ _ _ ha, apZ_dat_famV _ _ _ (hA.elRes _ _ _ ha n h)]; exact hcoh k f a ha n h⟩

theorem res_isContrM (X : V) (h : Hom n k) : res h (isContrM k X) = isContrM n (res h X) := by
  unfold isContrM; rw [res_sigmaC, res_famV]; simp only [res_res]

theorem res_isEquivM (T A f : V) (h : Hom n k) :
    res h (isEquivM k T A f) = isEquivM n (res h T) (res h A) (res h f) := by
  unfold isEquivM; rw [res_piC, res_famV]; simp only [res_res]

theorem fib_isContrM {X : V} (hX : Fib X k) : Fib (isContrM k X) k := by
  unfold isContrM
  refine fib_sigmaC hX (famOK_famV hX (fun k' g c hc => ?_) fun k' g c hc n h => ?_)
  · refine fib_piC (hX.restr g) (famOK_famV (hX.restr g) (fun k'' h x hx => ?_) fun k'' h x hx n' h' => ?_)
    · refine fib_pathC (((hX.restr g).restr h).restr _) ?_ ?_
      · rw [El_res, Hom.wk_comp_endpt, El_res, El_res, Hom.comp_id]
        have := hX.elRes _ _ _ hc _ h; exact this
      · simp only [El_res, Hom.wk_comp_endpt, Hom.comp_id] at hx ⊢; exact hx
    · rw [res_pathC]; simp only [res_res, Hom.wk_comp_lift, Hom.comp_assoc]
  · rw [res_piC, res_famV]; simp only [res_res, Hom.comp_assoc]

theorem fib_isEquivM {T A f : V} (hT : Fib T k) (hA : Fib A k) (hf : f ∈ El (arrowM k T A) (Hom.id k)) :
    Fib (isEquivM k T A f) k := by
  unfold isEquivM
  refine fib_piC hA (famOK_famV hA (fun k' g y hy => ?_) fun k' g y hy n h => ?_)
  · have hyg : y ∈ El (res g A) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact hy
    exact fib_isContrM (fib_fiberM (hT.restr g) (hA.restr g) (arrowM_elRes hT.kv hf g) hyg)
  · rw [res_isContrM, res_fiberM]; simp only [res_res]

theorem lamV_mem_arrowM {T A : V} (hT : Fib T k) (hA : IsKV k A) {F : (n : ℕ) → Hom n k → V → V}
    (hF : ∀ n (g : Hom n k), ∀ x ∈ El T g, F n g x ∈ El A g)
    (hcoh : ∀ n (g : Hom n k), ∀ x ∈ El T g, ∀ n' (h : Hom n' n), res h (F n g x) = F n' (g.comp h) (res h x)) :
    lamV k (fun _ g => El T g) F ∈ El (arrowM k T A) (Hom.id k) := by
  have e : El (arrowM k T A) (Hom.id k) = piElSet k T (famV k T fun _ g _ => res g A) := by
    unfold arrowM; rw [El_piC, res_id hT.kv, res_id (isKV_famV _ _)]
  rw [e, piElSet, mem_piEl]
  refine ⟨isKV_mkKV _, fun n g => ⟨?_, fun x hx => ?_⟩, fun n g x hx n' h => ?_⟩
  · rw [dat_lamV]; exact fnZ_congr fun x hx => (apZ_fnZ _ hx).symm
  · rw [dat_lamV, apZ_fnZ _ hx, apZ_dat_famV _ _ _ hx, El_res, Hom.comp_id]; exact hF n g x hx
  · rw [dat_lamV, dat_lamV, apZ_fnZ _ hx, apZ_fnZ _ (hT.elRes _ _ _ hx n' h)]; exact hcoh n g x hx n' h

/-! ### The transport function `f_i` -/

theorem eqLine_endpt0 (g : Hom k (n + 1)) :
    (eqLine n g).comp (Hom.endpt k (DM.zero k)) = (eZ n).comp ((Hom.wk n).comp g) := by
  apply Hom.ext_snoc <;> intro p <;> simp [eqLine]

theorem eqLine_endpt1 (g : Hom k (n + 1)) : (eqLine n g).comp (Hom.endpt k (DM.one k)) = g := by
  apply Hom.ext_snoc <;> intro p <;> simp [eqLine]

theorem eqLine_lift (g : Hom k (n + 1)) (h : Hom k' k) : (eqLine n g).comp (Hom.lift h) = eqLine n (g.comp h) := by
  apply Hom.ext_snoc <;> intro p <;> simp [eqLine]

theorem eqLine_zero {g : Hom k (n + 1)} {h : Hom k' k} (hh : ((Cof.eq0 ((lastVar n).restr g)).restr h).holds)
    (r : DM k') : (eqLine n g).comp (Hom.snoc h r) = (eqLine n g).comp (Hom.snoc h (DM.zero k')) := by
  rw [Cof.eq0_restr, DM.restr_restr] at hh
  have h0 := DM.eq_zero_of_holds_eq0 hh
  apply Hom.ext_snoc
  · intro p; simp [eqLine]
  · intro p
    have := congrArg (fun d : DM k' => d.fn p) h0
    have h1 : g.app (h.app p) (Fin.last n) = KubusCore.I.M4.zero := by simpa using this
    simp [eqLine, h1]

section eqFun

variable {B : V} (hB : Fib B (n + 1))
include hB

theorem eqLine_const (g : Hom k (n + 1)) : ConstOn B (eqLine n g) (Cof.eq0 ((lastVar n).restr g)) := by
  intro k' h hh r; rw [eqLine_zero hh r]

theorem eqFunL_base {g : Hom k (n + 1)} {x : V} (hx : x ∈ El (res (Hom.wk n) (res (eZ n) B)) g) :
    x ∈ El B ((eqLine n g).comp (Hom.endpt k (DM.zero k))) := by
  rw [eqLine_endpt0]; rw [El_res, El_res] at hx; rw [← Hom.comp_assoc]; exact hx

theorem eqFunL_val {g : Hom k (n + 1)} {x : V} (hx : x ∈ El (res (Hom.wk n) (res (eZ n) B)) g) :
    transpAt B (eqLine n g) (Cof.eq0 ((lastVar n).restr g)) x ∈ El B g := by
  have := hB.trMem k _ _ x (Cof.isCof_eq0 _) (eqLine_const hB g) (eqFunL_base hB hx)
  rwa [eqLine_endpt1] at this

theorem eqFunL_res {g : Hom k (n + 1)} {x : V} (hx : x ∈ El (res (Hom.wk n) (res (eZ n) B)) g) (h : Hom k' k) :
    res h (transpAt B (eqLine n g) (Cof.eq0 ((lastVar n).restr g)) x) =
      transpAt B (eqLine n (g.comp h)) (Cof.eq0 ((lastVar n).restr (g.comp h))) (res h x) := by
  rw [hB.trRes k _ _ x (Cof.isCof_eq0 _) (eqLine_const hB g) (eqFunL_base hB hx) k' h, eqLine_lift,
    Cof.eq0_restr, DM.restr_restr]

theorem eqFunL_mem : eqFunL n B ∈ El (arrowM (n + 1) (res (Hom.wk n) (res (eZ n) B)) B) (Hom.id (n + 1)) :=
  lamV_mem_arrowM ((hB.restr _).restr _) hB.kv (fun _ _ _ hx => eqFunL_val hB hx)
    fun _ _ _ hx _ h => eqFunL_res hB hx h

/-- At `i = 0`, `f_i` is the identity. -/
theorem eqFunL_zero {g : Hom k n} {x : V} (hx : x ∈ El (res (eZ n) B) g) :
    appV k (res g (res (eZ n) (eqFunL n B))) x = x := by
  have hx' : x ∈ El (res (Hom.wk n) (res (eZ n) B)) ((eZ n).comp g) := by
    rw [El_res] at hx; rw [El_res, El_res, ← Hom.comp_assoc (Hom.wk n), Hom.wk_comp_endpt, Hom.id_comp]; exact hx
  rw [appV, here, dat_res, dat_res, Hom.comp_id, eqFunL, dat_lamV, apZ_fnZ _ hx']
  refine hB.trFace k _ _ x (Cof.isCof_eq0 _) (eqLine_const hB _) (eqFunL_base hB hx') ?_
  rw [← DM.restr_restr, show (lastVar n).restr (eZ n) = DM.zero n from lastVar_restr_snoc _ _, DM.zero_restr]
  rw [Cof.eq0_zero]; exact Cof.holds_top

end eqFun

end

end Model
