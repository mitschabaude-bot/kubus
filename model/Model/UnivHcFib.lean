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

/-! ### The identity is an equivalence -/

theorem connHom_endpt0 : (connHom k).comp (Hom.endpt (k + 1) (DM.zero (k + 1))) =
    Hom.snoc (Hom.wk k) (DM.neg (lastVar k)) := by
  apply Hom.ext_snoc <;> intro p <;> simp [connHom, iVar, jVar]

theorem connHom_endpt1 : (connHom k).comp (Hom.endpt (k + 1) (DM.one (k + 1))) =
    (Hom.endpt k (DM.one k)).comp (Hom.wk k) := by
  apply Hom.ext_snoc <;> intro p <;> simp [connHom, iVar, jVar]

theorem connHom_lift0 : (connHom k).comp (Hom.lift (Hom.endpt k (DM.zero k))) =
    (Hom.endpt k (DM.one k)).comp (Hom.wk k) := by
  apply Hom.ext_snoc <;> intro p <;> simp [connHom, iVar, jVar]

theorem connHom_lift1 : (connHom k).comp (Hom.lift (Hom.endpt k (DM.one k))) = Hom.id (k + 1) := by
  apply Hom.ext_snoc <;> intro p <;> simp [connHom, iVar, jVar]

theorem negLine_endpt0 : (Hom.snoc (Hom.wk k) (DM.neg (lastVar k))).comp (Hom.endpt k (DM.zero k)) =
    Hom.endpt k (DM.one k) := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem negLine_endpt1 : (Hom.snoc (Hom.wk k) (DM.neg (lastVar k))).comp (Hom.endpt k (DM.one k)) =
    Hom.endpt k (DM.zero k) := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem connHom_lift_lift (h : Hom k' k) : (connHom k).comp (Hom.lift (Hom.lift h)) = (Hom.lift h).comp (connHom k') := by
  apply Hom.ext_snoc <;> intro p <;> simp [connHom, iVar, jVar]

theorem negLine_lift (h : Hom k' k) :
    (Hom.snoc (Hom.wk k) (DM.neg (lastVar k))).comp (Hom.lift h) = (Hom.lift h).comp (Hom.snoc (Hom.wk k') (DM.neg (lastVar k'))) := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem isKV_pathOfLine (p : V) : IsKV k (pathOfLine k p) := by unfold pathOfLine; exact isKV_mkKV _

theorem connV_eq {x q : V} (hq : IsKV (k + 1) q) :
    connV k (pairV k x (pathOfLine k q)) =
      pairV (k + 1) (res (Hom.snoc (Hom.wk k) (DM.neg (lastVar k))) q) (pathOfLine (k + 1) (res (connHom k) q)) := by
  rw [connV, sndV_pairV (isKV_pathOfLine q), lineOf_pathOfLine hq, res_pathOfLine, pappV_pathOfLine, res_res,
    Hom.lift_comp_endpt']

theorem connV_res {x q : V} (hq : IsKV (k + 1) q) (h : Hom k' k) :
    res (Hom.lift h) (connV k (pairV k x (pathOfLine k q))) = connV k' (res h (pairV k x (pathOfLine k q))) := by
  rw [res_pairV, res_pathOfLine, connV_eq hq, connV_eq (isKV_res _ _), res_pairV, res_pathOfLine, res_res, res_res,
    res_res, res_res, negLine_lift, connHom_lift_lift]

theorem wk_comp_connHom : (Hom.wk k).comp (connHom k) = (Hom.wk k).comp (Hom.wk (k + 1)) := by
  rw [connHom, Hom.wk_comp_snoc]

/-- The contraction path of the fiber of the identity. -/
theorem connV_mem {T F y z : V} (hT : Fib T k) (hid : ∀ k' (g : Hom k' k), ∀ x ∈ El T g, appV k' (res g F) x = x)
    (hFkv : IsKV k F) (hy : y ∈ El T (Hom.id k)) (hz : z ∈ El (fiberM k T T F y) (Hom.id k)) :
    connV k z ∈ El (res (Hom.wk k) (fiberM k T T F y)) (Hom.id (k + 1)) ∧
      res (Hom.endpt k (DM.zero k)) (connV k z) = pairV k y (pathOfLine k (res (Hom.wk k) y)) ∧
      res (Hom.endpt k (DM.one k)) (connV k z) = z := by
  have hykv := hT.elKV _ _ _ hy
  obtain ⟨x, hx, p, hp, rfl⟩ := mem_fiberM hT.kv hT.kv hFkv hykv hz
  obtain ⟨q, hq, rfl, h0, h1⟩ := mem_pathC.1 hp
  have hxkv := hT.elKV _ _ _ hx
  have hFx : appV k F x = x := by have := hid k (Hom.id k) x hx; rwa [res_id hFkv] at this
  rw [Hom.lift_id, El_res, Hom.comp_id] at hq
  have hqkv : IsKV (k + 1) q := hT.elKV _ _ _ hq
  rw [hFx, res_id hxkv] at h0
  rw [res_id hykv] at h1
  rw [connV_eq hqkv]
  have hfirst : res (Hom.snoc (Hom.wk k) (DM.neg (lastVar k))) q ∈ El T (Hom.wk k) := by
    have := hT.elRes _ _ _ hq _ (Hom.snoc (Hom.wk k) (DM.neg (lastVar k))); rwa [Hom.wk_comp_snoc] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [res_fiberM]
    refine pairV_mem_fiberM (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) (isKV_res _ _)
      (by rw [El_res, Hom.comp_id]; exact hfirst) ?_
    rw [hid (k + 1) (Hom.wk k) _ hfirst, mem_pathC, Hom.lift_id]
    refine ⟨_, ?_, rfl, ?_, ?_⟩
    · rw [El_res, El_res, Hom.comp_id, ← wk_comp_connHom]
      exact hT.elRes _ _ _ hq _ (connHom k)
    · rw [res_res, connHom_endpt0, res_id (isKV_res _ _)]
    · rw [res_res, connHom_endpt1, ← res_res, h1, res_id (isKV_res _ _)]
  · rw [res_pairV, res_res, negLine_endpt0, h1, res_pathOfLine, res_res, connHom_lift0, ← res_res, h1]
  · rw [res_pairV, res_res, negLine_endpt1, h0, res_pathOfLine, res_res, connHom_lift1, res_id hqkv]

theorem lamV_mem_piElSet {A : V} (hA : Fib A k) {G F : (n : ℕ) → Hom n k → V → V}
    (hF : ∀ n (g : Hom n k), ∀ x ∈ El A g, F n g x ∈ El (G n g x) (Hom.id n))
    (hcoh : ∀ n (g : Hom n k), ∀ x ∈ El A g, ∀ n' (h : Hom n' n), res h (F n g x) = F n' (g.comp h) (res h x)) :
    lamV k (fun _ g => El A g) F ∈ piElSet k A (famV k A G) := by
  rw [piElSet, mem_piEl]
  refine ⟨isKV_mkKV _, fun n g => ⟨?_, fun x hx => ?_⟩, fun n g x hx n' h => ?_⟩
  · rw [dat_lamV]; exact fnZ_congr fun x hx => (apZ_fnZ _ hx).symm
  · rw [dat_lamV, apZ_fnZ _ hx, apZ_dat_famV _ _ _ hx]; exact hF n g x hx
  · rw [dat_lamV, dat_lamV, apZ_fnZ _ hx, apZ_fnZ _ (hA.elRes _ _ _ hx n' h)]; exact hcoh n g x hx n' h

theorem pairV_mem_isContrM {X cen ctr : V} (hX : Fib X k) (hcen : cen ∈ El X (Hom.id k))
    (hctr : ctr ∈ piElSet k X (famV k X fun k' h x => pathC k' (res (Hom.wk k') (res h X)) (res h cen) x)) :
    pairV k cen ctr ∈ El (isContrM k X) (Hom.id k) := by
  unfold isContrM
  rw [mem_sigmaC_id hX.kv (isKV_famV _ _)]
  refine ⟨cen, hcen, ctr, ?_, rfl⟩
  rw [apZ_dat_famV _ _ _ hcen, res_id hX.kv, El_piC, res_id hX.kv, res_id (isKV_famV _ _)]
  exact hctr

theorem res_refl (y : V) (h : Hom k' k) :
    res h (pairV k y (pathOfLine k (res (Hom.wk k) y))) = pairV k' (res h y) (pathOfLine k' (res (Hom.wk k') (res h y))) := by
  rw [res_pairV, res_pathOfLine, res_res, res_res, Hom.wk_comp_lift]

/-- The identity (a function acting as the identity) is an equivalence. -/
theorem idEqV_mem {T F : V} (hT : Fib T n) (hF : F ∈ El (arrowM n T T) (Hom.id n))
    (hid : ∀ k (g : Hom k n), ∀ x ∈ El T g, appV k (res g F) x = x) :
    idEqV n T F ∈ El (isEquivM n T T F) (Hom.id n) := by
  have hFkv : IsKV n F := (mem_piEl.1 (mem_arrowM hT.kv hF)).1
  unfold isEquivM
  rw [El_piC, res_id hT.kv, res_id (isKV_famV _ _)]
  refine lamV_mem_piElSet hT (fun k g y hy => ?_) fun k g y hy k' h => ?_
  · -- the data at `g`
    have hTg := hT.restr g
    have hFg := arrowM_elRes hT.kv hF g
    have hyg : y ∈ El (res g T) (Hom.id k) := by rw [El_res, Hom.comp_id]; exact hy
    have hidg : ∀ k' (g' : Hom k' k), ∀ x ∈ El (res g T) g', appV k' (res g' (res g F)) x = x := by
      intro k' g' x hx; rw [res_res]; rw [El_res] at hx; exact hid k' _ x hx
    have hX := fib_fiberM hTg hTg hFg hyg
    have hFgkv : IsKV k (res g F) := isKV_res _ _
    have hykv := hTg.elKV _ _ _ hyg
    refine pairV_mem_isContrM hX ?_ ?_
    · refine pairV_mem_fiberM hTg.kv hTg.kv hFgkv hykv hyg ?_
      have hyy : appV k (res g F) y = y := by have := hidg k (Hom.id k) y hyg; rwa [res_id hFgkv] at this
      rw [hyy, mem_pathC, Hom.lift_id]
      refine ⟨_, ?_, rfl, ?_, ?_⟩
      · rw [El_res, El_res, Hom.comp_id]
        have := hT.elRes _ _ _ hy _ (Hom.wk k); exact this
      · rw [res_res, Hom.wk_comp_endpt, res_id hykv]
      · rw [res_res, Hom.wk_comp_endpt, res_id hykv]
    · refine lamV_mem_piElSet hX (fun k' g' z hz => ?_) fun k' g' z hz k'' h => ?_
      · have hz' : z ∈ El (res g' (fiberM k (res g T) (res g T) (res g F) y)) (Hom.id k') := by
          rw [El_res, Hom.comp_id]; exact hz
        rw [res_fiberM] at hz'
        have hidg' : ∀ k'' (g'' : Hom k'' k'), ∀ x ∈ El (res g' (res g T)) g'',
            appV k'' (res g'' (res g' (res g F))) x = x := by
          intro k'' g'' x hx; rw [res_res]; rw [El_res] at hx; exact hidg k'' _ x hx
        have hyg' : res g' y ∈ El (res g' (res g T)) (Hom.id k') := by
          rw [El_res, Hom.comp_id]; have := hTg.elRes _ _ _ hyg _ g'; rwa [Hom.id_comp] at this
        obtain ⟨hc, h0, h1⟩ := connV_mem (hTg.restr g') hidg' (isKV_res _ _) hyg' hz'
        have hzkv : IsKV k' z := hX.elKV _ _ _ hz
        rw [mem_pathC, Hom.lift_id]
        refine ⟨_, ?_, rfl, ?_, ?_⟩
        · rw [← res_fiberM] at hc; exact hc
        · rw [h0, res_id (isKV_res _ _), res_refl]
        · rw [h1, res_id hzkv]
      · have hz' : z ∈ El (res g' (fiberM k (res g T) (res g T) (res g F) y)) (Hom.id k') := by
          rw [El_res, Hom.comp_id]; exact hz
        rw [res_fiberM] at hz'
        obtain ⟨x, -, p, hp, rfl⟩ := mem_fiberM (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) hz'
        obtain ⟨q, hq, rfl, -, -⟩ := mem_pathC.1 hp
        have hqkv : IsKV (k' + 1) q := ((hTg.restr g').restr _).elKV _ _ _ hq
        rw [res_pathOfLine, connV_res hqkv]
  · -- naturality in `g`
    rw [res_pairV, res_refl, res_lamV]
    congr 2
    funext n' g'
    rw [← El_res, res_fiberM, res_res, res_res]

/-! ### Transport is an equivalence -/

theorem pairV_mem_equivM {T A p q : V} (hT : Fib T k) (hA : Fib A k) (hp : p ∈ El (arrowM k T A) (Hom.id k))
    (hq : q ∈ El (isEquivM k T A p) (Hom.id k)) : pairV k p q ∈ El (equivM k T A) (Hom.id k) := by
  have hPkv : IsKV k (arrowM k T A) := by unfold arrowM piC; exact isKV_mkKV _
  unfold equivM
  rw [mem_sigmaC_id hPkv (isKV_famV _ _)]
  refine ⟨p, hp, q, ?_, rfl⟩
  rw [apZ_dat_famV _ _ _ hp, res_id hT.kv, res_id hA.kv]; exact hq

theorem res_eZ_T' (B : V) : res (eZ n) (res (Hom.wk n) (res (eZ n) B)) = res (eZ n) B := by
  rw [res_res, Hom.wk_comp_endpt, res_id (isKV_res _ _)]

theorem res_eO_T' (B : V) : res (eO n) (res (Hom.wk n) (res (eZ n) B)) = res (eZ n) B := by
  rw [res_res, Hom.wk_comp_endpt, res_id (isKV_res _ _)]

section eqTr

variable {B : V} (hB : Fib B (n + 1))
include hB

theorem fib_eqQ : Fib (eqQ n B) (n + 1) :=
  fib_isEquivM ((hB.restr _).restr _) hB (eqFunL_mem hB)

theorem idEq_mem : idEqV n (res (eZ n) B) (res (eZ n) (eqFunL n B)) ∈
    El (eqQ n B) ((Hom.id (n + 1)).comp (Hom.endpt n (DM.zero n))) := by
  rw [Hom.id_comp, El_eq_res_id, eqQ, res_isEquivM, res_eZ_T']
  have hF := arrowM_elRes (isKV_res _ _) (eqFunL_mem hB) (eZ n)
  rw [res_eZ_T'] at hF
  exact idEqV_mem (hB.restr _) hF fun k g x hx => eqFunL_zero hB hx

theorem eqTr_mem : eqTr n B ∈ El (equivM n (res (eZ n) B) (res (eO n) B)) (Hom.id n) := by
  have hQ := fib_eqQ hB
  have hq := hQ.trMem n (Hom.id (n + 1)) (Cof.bot n) _ (Cof.isCof_bot n) (constOn_bot _ _) (idEq_mem hB)
  rw [Hom.id_comp, El_eq_res_id, eqQ, res_isEquivM, res_eO_T'] at hq
  have hF := arrowM_elRes (isKV_res _ _) (eqFunL_mem hB) (eO n)
  rw [res_eO_T'] at hF
  exact pairV_mem_equivM (hB.restr _) (hB.restr _) hF hq


end eqTr

/-! ### Naturality of the equivalence -/

theorem eqLine_lift_comp (h : Hom n' n) (g : Hom k (n' + 1)) :
    eqLine n ((Hom.lift h).comp g) = (Hom.lift h).comp (eqLine n' g) := by
  apply Hom.ext_snoc <;> intro p <;> simp [eqLine]

theorem T'_hom (h : Hom n' n) (g : Hom k (n' + 1)) :
    (eZ n).comp ((Hom.wk n).comp ((Hom.lift h).comp g)) = (Hom.lift h).comp ((eZ n').comp ((Hom.wk n').comp g)) := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem eqFunL_res_lift (B : V) (h : Hom n' n) : res (Hom.lift h) (eqFunL n B) = eqFunL n' (res (Hom.lift h) B) := by
  unfold eqFunL
  rw [res_lamV]
  congr 1
  · funext k g; simp only [El_res]; rw [T'_hom]
  · funext k g x
    rw [transpAt_res, eqLine_lift_comp, ← DM.restr_restr, lastVar_restr_lift]

theorem idEqV_res (T F : V) (h : Hom n' n) : res h (idEqV n T F) = idEqV n' (res h T) (res h F) := by
  simp only [idEqV, res_lamV, El_res, res_res]

theorem res_T' (B : V) (h : Hom n' n) :
    res (Hom.lift h) (res (Hom.wk n) (res (eZ n) B)) = res (Hom.wk n') (res (eZ n') (res (Hom.lift h) B)) := by
  simp only [res_res]; congr 1
  apply Hom.ext_snoc <;> intro p <;> simp

theorem eqQ_res_lift (B : V) (h : Hom n' n) : res (Hom.lift h) (eqQ n B) = eqQ n' (res (Hom.lift h) B) := by
  rw [eqQ, eqQ, res_isEquivM, res_T', eqFunL_res_lift]

theorem eqTr_res {B : V} (hB : Fib B (n + 1)) (h : Hom n' n) : res h (eqTr n B) = eqTr n' (res (Hom.lift h) B) := by
  have hQ := fib_eqQ hB
  rw [eqTr, eqTr, res_pairV,
    hQ.trRes n (Hom.id (n + 1)) (Cof.bot n) _ (Cof.isCof_bot n) (constOn_bot _ _) (idEq_mem hB) n' h,
    Hom.id_comp, transpAt_eq_res_id, eqQ_res_lift, Cof.bot_restr, idEqV_res, res_res, res_res, res_res,
    ← TranspPi.lift_comp_endpt1, ← TranspPi.lift_comp_endpt0, ← res_res, ← res_res (Hom.lift h) (eZ n'),
    ← res_res (Hom.lift h) (eZ n'), eqFunL_res_lift]

end

end Model
