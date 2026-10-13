import Model.Rules.TranspGlue

/-!
# The computation rule `hcompU`

`hcomp U [φ ↦ u] u0` reduces to `Glue u0 [φ ↦ (u(1), lineEquiv (u reversed))]`; the model's
`hcomp` in the universe (`univHcF`) is exactly this Glue code, with `lineEquiv B` denoting
`eqTr` of the line `B`.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' m n : ℕ}

/-! ### Well-formedness of the equivalence codes -/

theorem wf_piC_famV {l : ℕ} {A : V} {F : (k : ℕ) → Hom k m → V → V} (hA : WF l m A)
    (hfam : ∀ k (f : Hom k m), ∀ a ∈ El A f, WF l k (F k f a))
    (hcoh : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k), res h (F k f a) = F n (f.comp h) (res h a)) :
    WF l m (piC m A (famV m A F)) := by
  unfold WF
  refine WFI.pi hA (isKV_famV _ _) (fun k f => famV_graph _ _ _) (fun k f a ha => ?_) (fun k f a ha n h => ?_)
  · rw [apZ_dat_famV _ _ _ ha]; exact hfam k f a ha
  · rw [apZ_dat_famV _ _ _ ha, apZ_dat_famV _ _ _ (hA.fib.elRes _ _ _ ha n h)]; exact hcoh k f a ha n h

theorem wf_sigmaC_famV {l : ℕ} {A : V} {F : (k : ℕ) → Hom k m → V → V} (hA : WF l m A)
    (hfam : ∀ k (f : Hom k m), ∀ a ∈ El A f, WF l k (F k f a))
    (hcoh : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k), res h (F k f a) = F n (f.comp h) (res h a)) :
    WF l m (sigmaC m A (famV m A F)) := by
  unfold WF
  refine WFI.sigma hA (isKV_famV _ _) (fun k f => famV_graph _ _ _) (fun k f a ha => ?_) (fun k f a ha n h => ?_)
  · rw [apZ_dat_famV _ _ _ ha]; exact hfam k f a ha
  · rw [apZ_dat_famV _ _ _ ha, apZ_dat_famV _ _ _ (hA.fib.elRes _ _ _ ha n h)]; exact hcoh k f a ha n h

theorem wf_pathC {l : ℕ} {L a0 a1 : V} (hL : WF l (m + 1) L) (ha0 : a0 ∈ El L (Hom.endpt m (DM.zero m)))
    (ha1 : a1 ∈ El L (Hom.endpt m (DM.one m))) : WF l m (pathC m L a0 a1) := by
  unfold WF; exact WFI.path hL ha0 ha1

theorem wf_fiberM {l : ℕ} {T A f y : V} (hT : WF l k T) (hA : WF l k A) (hf : f ∈ El (arrowM k T A) (Hom.id k))
    (hy : y ∈ El A (Hom.id k)) : WF l k (fiberM k T A f y) := by
  unfold fiberM
  refine wf_sigmaC_famV hT (fun k' g t ht => ?_) fun k' g t ht n h => ?_
  · have hfg := arrowM_elRes hT.fib.kv hf g
    have htg : t ∈ El (res g T) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact ht
    refine wf_pathC ((hA.res g).res _) ?_ ?_
    · rw [El_res, Hom.wk_comp_endpt, El_res, Hom.comp_id]
      have := appV_arrowM (hT.fib.restr g).kv hfg htg
      rwa [El_res, Hom.comp_id] at this
    · rw [El_res, Hom.wk_comp_endpt, El_res, Hom.comp_id]
      have := hA.fib.elRes _ _ _ hy k' g; rwa [Hom.id_comp] at this
  · have hfg := arrowM_elRes hT.fib.kv hf g
    have htg : t ∈ El (res g T) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact ht
    rw [res_pathC, res_res, res_res, Hom.wk_comp_lift, ← res_res, ← res_res g,
      appV_arrowM_res (hT.fib.restr g).kv hfg htg h, res_res, res_res, res_res, res_res, res_res]

theorem wf_isContrM {l : ℕ} {X : V} (hX : WF l k X) : WF l k (isContrM k X) := by
  unfold isContrM
  refine wf_sigmaC_famV hX (fun k' g c hc => ?_) fun k' g c hc n h => ?_
  · refine wf_piC_famV (hX.res g) (fun k'' h x hx => ?_) fun k'' h x hx n' h' => ?_
    · refine wf_pathC (((hX.res g).res h).res _) ?_ ?_
      · rw [El_res, Hom.wk_comp_endpt, El_res, El_res, Hom.comp_id]
        have := hX.fib.elRes _ _ _ hc _ h; exact this
      · simp only [El_res, Hom.wk_comp_endpt, Hom.comp_id] at hx ⊢; exact hx
    · rw [res_pathC]; simp only [res_res, Hom.wk_comp_lift, Hom.comp_assoc]
  · rw [res_piC, res_famV]; simp only [res_res, Hom.comp_assoc]

theorem wf_isEquivM {l : ℕ} {T A f : V} (hT : WF l k T) (hA : WF l k A) (hf : f ∈ El (arrowM k T A) (Hom.id k)) :
    WF l k (isEquivM k T A f) := by
  unfold isEquivM
  refine wf_piC_famV hA (fun k' g y hy => ?_) fun k' g y hy n h => ?_
  · have hyg : y ∈ El (res g A) (Hom.id k') := by rw [El_res, Hom.comp_id]; exact hy
    exact wf_isContrM (wf_fiberM (hT.res g) (hA.res g) (arrowM_elRes hT.fib.kv hf g) hyg)
  · rw [res_isContrM, res_fiberM]; simp only [res_res]

/-! ### The function `f_i` -/

theorem env_eqLine (ρ : IEnv k) (g : Hom n (k + 1)) :
    (fun i => ival (ρ.ext.restr g).ext (Tm.bind2 (.and (.var 1) (.var 0)) i)) = ρ.ext.restr (eqLine k g) := by
  funext i
  rcases i with _ | i
  · ext p; simp [Tm.bind2, IEnv.ext, IEnv.restr, eqLine, I.eval, Hom.snoc, Hom.app, Hom.wk]
  · simp only [Tm.bind2, ival.var, IEnv.ext, IEnv.restr, DM.restr_restr]
    congr 1
    simp only [eqLine, Hom.wk_comp_snoc, Hom.comp_assoc]

section line

variable {B : Tm} {ρ : IEnv k} {γ : ℕ → V} (hγ : ∀ x, IsKV k (γ x))
  (hBn : Natural S B (k + 1) ρ.ext (TEnv.restr γ (Hom.wk k))) (hBt : TyCode (k + 1) (lineV S B k ρ γ))

include hγ hBn in
theorem sem_B0 : sem S (B.dinst .zero) k ρ γ = res (eZ k) (lineV S B k ρ γ) := by
  rw [sem_dinst, ival_zero, line_endpt hγ hBn]

include hγ hBn in
theorem nat_B0 : Natural S (B.dinst .zero) k ρ γ :=
  Natural.dinst (by rw [ival_zero]; exact line_endpt_nat hγ hBn _)

include hγ hBn hBt in
theorem lineFun_body (h : Hom n (k + 1)) {x : V}
    (hx : x ∈ El (res (Hom.wk k) (res (eZ k) (lineV S B k ρ γ))) h) :
    sem S (.transp ((B.shift).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.neg (.var 0)) (.var 0)) n
      (ρ.ext.restr h) (TEnv.cons (TEnv.restr (TEnv.restr γ (Hom.wk k)) h) x) =
      transpAt (lineV S B k ρ γ) (eqLine k h) (Cof.eq0 ((lastVar k).restr h)) x := by
  have hLf := hBt.fib
  have eL : ∀ n'' (h' : Hom n'' (n + 1)),
      sem S ((B.shift).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) n'' ((ρ.ext.restr h).ext.restr h')
        (TEnv.restr (TEnv.restr (TEnv.cons (TEnv.restr (TEnv.restr γ (Hom.wk k)) h) x) (Hom.wk n)) h') =
        res h' (res (eqLine k h) (lineV S B k ρ γ)) := by
    intro n'' h'
    rw [sem_dsubst, TEnv.restr_cons, TEnv.restr_cons, sem_shift]
    have e1 : (fun i => ival ((ρ.ext.restr h).ext.restr h') (Tm.bind2 (.and (.var 1) (.var 0)) i)) =
        ρ.ext.restr ((eqLine k h).comp h') := by
      rw [← IEnv.restr_restr, ← env_eqLine]; rfl
    have hw : (Hom.wk k).comp ((eqLine k h).comp h') = (((Hom.wk k).comp h).comp (Hom.wk n)).comp h' := by
      rw [← Hom.comp_assoc, eqLine, Hom.wk_comp_snoc]; try rfl
    have e2 : TEnv.restr (TEnv.restr (TEnv.restr (TEnv.restr γ (Hom.wk k)) h) (Hom.wk n)) h' =
        TEnv.restr (TEnv.restr γ (Hom.wk k)) ((eqLine k h).comp h') := by
      simp only [TEnv.restr_restr]; rw [hw]; try rfl
    rw [e1, e2, hBn, res_res]
  have eL0 : lineV S ((B.shift).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) n (ρ.ext.restr h)
      (TEnv.cons (TEnv.restr (TEnv.restr γ (Hom.wk k)) h) x) = res (eqLine k h) (lineV S B k ρ γ) := by
    have := eL (n + 1) (Hom.id (n + 1))
    rwa [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr (TEnv.cons (TEnv.restr (TEnv.restr γ (Hom.wk k)) h) x)
      (Hom.wk n)) (fun y => isKV_res _ _), res_id (isKV_res _ _)] at this
  have hface : (ival (ρ.ext.restr h) (.neg (.var 0))).face = Cof.eq0 ((lastVar k).restr h) := rfl
  have tc : TranspCond S ((B.shift).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.neg (.var 0)) (.var 0) n
      (ρ.ext.restr h) (TEnv.cons (TEnv.restr (TEnv.restr γ (Hom.wk k)) h) x) := by
    refine ⟨?_, ?_, ?_, fun n'' h' => by rw [eL n'' h']; exact congrArg (res h') eL0.symm, natural_var S 0 _ _⟩
    · rw [eL0]; exact hBt.res _
    · rw [eL0, hface]; exact (eqLine_const hLf h).res_id
    · rw [eL0, sem_var, TEnv.cons_zero, El_res, Hom.id_comp]; exact eqFunL_base hLf hx
  rw [sem_transp tc, eL0, hface, sem_var, TEnv.cons_zero, transpAt_res, Hom.comp_id]

include hγ hBn hBt in
theorem sem_lineFun_at (g : Hom n (k + 1)) :
    sem S (Tm.lineFun B) n (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk k)) g) =
      res g (eqFunL k (lineV S B k ρ γ)) := by
  have eD : (fun n' (f : Hom n' n) => El (sem S (B.dinst .zero).dshift n (ρ.ext.restr g)
      (TEnv.restr (TEnv.restr γ (Hom.wk k)) g)) f) =
      fun n' f => El (res (Hom.wk k) (res (eZ k) (lineV S B k ρ γ))) (g.comp f) := by
    funext n' f
    rw [sem_dshift_tail, IEnv.tail_restr, show ρ.ext.tail = ρ.restr (Hom.wk k) from rfl, IEnv.restr_restr,
      TEnv.restr_restr, nat_B0 hγ hBn, sem_B0 hγ hBn]
    simp only [El_res, Hom.comp_assoc]
  rw [Tm.lineFun, sem_lam, eqFunL, res_lamV, eD]
  apply lamV_congr
  intro n' f x hx
  rw [IEnv.restr_restr, TEnv.restr_restr]
  exact lineFun_body hγ hBn hBt (g.comp f) hx

include hγ hBn hBt in
theorem sem_lineFun : sem S (Tm.lineFun B) (k + 1) ρ.ext (TEnv.restr γ (Hom.wk k)) = eqFunL k (lineV S B k ρ γ) := by
  have hkv : IsKV (k + 1) (eqFunL k (lineV S B k ρ γ)) := by unfold eqFunL lamV; exact isKV_mkKV _
  have := sem_lineFun_at hγ hBn hBt (Hom.id (k + 1))
  rwa [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk k)) (fun y => isKV_res _ _),
    res_id hkv] at this

include hγ hBn hBt in
theorem nat_lineFun : Natural S (Tm.lineFun B) (k + 1) ρ.ext (TEnv.restr γ (Hom.wk k)) := by
  intro n g; rw [sem_lineFun_at hγ hBn hBt g, sem_lineFun hγ hBn hBt]

include hγ hBn hBt in
theorem sem_lineFun_dinst (r : I) :
    sem S ((Tm.lineFun B).dinst r) k ρ γ = res (Hom.endpt k (ival ρ r)) (eqFunL k (lineV S B k ρ γ)) := by
  rw [sem_dinst, ← IEnv.ext_restr_endpt, ← sem_lineFun_at hγ hBn hBt, TEnv.restr_restr, Hom.wk_comp_endpt,
    TEnv.restr_id_of_kv hγ]

end line

/-! ### The identity is an equivalence -/

theorem ival_neg' (ρ : IEnv m) (r : I) : ival ρ (.neg r) = DM.neg (ival ρ r) := by ext p; simp [I.eval]

theorem ival_or' (ρ : IEnv m) (r s : I) : ival ρ (.or r s) = DM.max (ival ρ r) (ival ρ s) := by
  ext p; simp [I.eval]

theorem natural_papp_snd0 {r : I} {ρ : IEnv m} {γ : ℕ → V} {x q : V} (hz : γ 0 = pairV m x (pathOfLine m q)) :
    Natural S (.papp (.snd (.var 0)) r) m ρ γ := by
  intro k f
  rw [sem_papp, sem_papp, sem_snd, sem_snd, sem_var, sem_var]
  show pappV k (sndV k (res f (γ 0))) (ival (ρ.restr f) r) = res f (pappV m (sndV m (γ 0)) (ival ρ r))
  rw [hz, res_pairV, sndV_pairV (isKV_res _ _), sndV_pairV (isKV_pathOfLine q), res_pappV_pathOfLine, ival.restr]

theorem natural_plam' {t : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : Natural S t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) :
    Natural S (.plam t) m ρ γ := by
  intro k f
  rw [sem_plam (line_restr_nat h f), sem_plam h, line_restr h f, res_pathOfLine]

theorem natural_pair' {a b : Tm} {ρ : IEnv m} {γ : ℕ → V} (ha : Natural S a m ρ γ) (hb : Natural S b m ρ γ)
    (hka : IsKV m (sem S a m ρ γ)) (hkb : IsKV m (sem S b m ρ γ)) : Natural S (.pair a b) m ρ γ := by
  intro k f
  rw [sem_pair_of_kv (by rw [ha k f]; exact isKV_res _ _) (by rw [hb k f]; exact isKV_res _ _),
    sem_pair_of_kv hka hkb, res_pairV, ha k f, hb k f]

theorem connHom_eq (ρ : IEnv n) :
    ((Hom.lift (Hom.wk n)).comp (Hom.lift (Hom.wk (n + 1)))).comp
      (Hom.endpt (n + 2) (ival ρ.ext.ext (.or (.neg (.var 1)) (.var 0)))) = connHom n := by
  rw [ival_or', ival_neg']
  apply Hom.ext_snoc <;> intro p <;> simp [connHom, iVar, jVar, IEnv.ext]

/-- The contraction `⟨i⟩ (p(~i), ⟨j⟩ p(~i ∨ j))` of an element `(x, p)` of a fiber. -/
theorem sem_contr {ρ : IEnv n} {γ : ℕ → V} {x q : V} (hq : IsKV (n + 1) q) (hz : γ 0 = pairV n x (pathOfLine n q)) :
    Natural S (.plam (.pair (.papp (.snd (.var 0)) (.neg (.var 0)))
      (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0)))))) n ρ γ ∧
    sem S (.plam (.pair (.papp (.snd (.var 0)) (.neg (.var 0)))
      (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0)))))) n ρ γ =
      pathOfLine n (connV n (pairV n x (pathOfLine n q))) := by
  have hz1 : TEnv.restr γ (Hom.wk n) 0 = pairV (n + 1) (res (Hom.wk n) x) (pathOfLine (n + 1) (res (Hom.lift (Hom.wk n)) q)) := by
    show res (Hom.wk n) (γ 0) = _; rw [hz, res_pairV, res_pathOfLine]
  have hz2 : TEnv.restr (TEnv.restr γ (Hom.wk n)) (Hom.wk (n + 1)) 0 = pairV (n + 2) (res (Hom.wk (n + 1)) (res (Hom.wk n) x))
      (pathOfLine (n + 2) (res (Hom.lift (Hom.wk (n + 1))) (res (Hom.lift (Hom.wk n)) q))) := by
    show res (Hom.wk (n + 1)) (TEnv.restr γ (Hom.wk n) 0) = _; rw [hz1, res_pairV, res_pathOfLine]
  have nY := natural_papp_snd0 (S := S) (r := .or (.neg (.var 1)) (.var 0)) (ρ := ρ.ext.ext) hz2
  have nb := natural_plam' (S := S) nY
  have na := natural_papp_snd0 (S := S) (r := .neg (.var 0)) (ρ := ρ.ext) hz1
  have ea : sem S (.papp (.snd (.var 0)) (.neg (.var 0))) (n + 1) ρ.ext (TEnv.restr γ (Hom.wk n)) =
      res (Hom.snoc (Hom.wk n) (DM.neg (lastVar n))) q := by
    rw [sem_papp, sem_snd, sem_var, hz1, sndV_pairV (isKV_pathOfLine _), pappV_pathOfLine, res_res, ival_neg',
      ival.var, Hom.lift_comp_endpt']; rfl
  have eb : sem S (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0)))) (n + 1) ρ.ext
      (TEnv.restr γ (Hom.wk n)) = pathOfLine (n + 1) (res (connHom n) q) := by
    rw [sem_plam nY, lineV, sem_papp, sem_snd, sem_var, hz2, sndV_pairV (isKV_pathOfLine _), pappV_pathOfLine,
      res_res, res_res, ← Hom.comp_assoc, connHom_eq]
  have nX : Natural S (.pair (.papp (.snd (.var 0)) (.neg (.var 0)))
      (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0))))) (n + 1) ρ.ext (TEnv.restr γ (Hom.wk n)) :=
    natural_pair' na nb (by rw [ea]; exact isKV_res _ _) (by rw [eb]; exact isKV_pathOfLine _)
  refine ⟨natural_plam' nX, ?_⟩
  rw [sem_plam nX, lineV, sem_pair_of_kv (by rw [ea]; exact isKV_res _ _) (by rw [eb]; exact isKV_pathOfLine _),
    ea, eb, connV_eq hq]

theorem isKV_pairV' (a b : V) : IsKV n (pairV n a b) := by unfold pairV; exact isKV_mkKV _

theorem sem_idIsEquiv {T f : Tm} {ρ : IEnv k} {γ : ℕ → V} (hTn : Natural S T k ρ γ) (hfn : Natural S f k ρ γ)
    (hTf : Fib (sem S T k ρ γ) k) (hfm : sem S f k ρ γ ∈ El (arrowM k (sem S T k ρ γ) (sem S T k ρ γ)) (Hom.id k)) :
    sem S (Tm.idIsEquiv T f) k ρ γ = idEqV k (sem S T k ρ γ) (sem S f k ρ γ) := by
  rw [Tm.idIsEquiv, sem_lam, idEqV]
  apply lamV_congr
  intro n g y hy
  have hykv : IsKV n y := hTf.elKV _ _ _ hy
  have eP : sem S (.pair (.var 0) (.plam (.var 0))) n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) =
      pairV n y (pathOfLine n (res (Hom.wk n) y)) := by
    rw [sem_pair_of_kv hykv (by rw [sem_plam (natural_var S 0 _ _)]; exact isKV_pathOfLine _),
      sem_plam (natural_var S 0 _ _)]; rfl
  have hTs : Natural S T.shift n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) := (hTn.restr g).shift y
  have hfs : Natural S f.shift n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) := (hfn.restr g).shift y
  have eT : sem S T.shift n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) = res g (sem S T k ρ γ) := by
    rw [sem_shift, hTn n g]
  have ef : sem S f.shift n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) = res g (sem S f k ρ γ) := by
    rw [sem_shift, hfn n g]
  have hTg : Fib (res g (sem S T k ρ γ)) n := hTf.restr g
  have hfg := arrowM_elRes hTf.kv hfm g
  have eFib : sem S (Tm.fiber T.shift T.shift f.shift (.var 0)) n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) =
      fiberM n (res g (sem S T k ρ γ)) (res g (sem S T k ρ γ)) (res g (sem S f k ρ γ)) y := by
    rw [sem_fiber hTs hTs hfs (natural_var S 0 _ _) (by rw [eT]; exact hTg) (by rw [eT]; exact hTg)
      (by rw [eT, ef]; exact hfg), eT, ef]; rfl
  have eC : sem S (.lam (Tm.fiber T.shift T.shift f.shift (.var 0))
      (.plam (.pair (.papp (.snd (.var 0)) (.neg (.var 0)))
        (.plam (.papp (.snd (.var 0)) (.or (.neg (.var 1)) (.var 0))))))) n (ρ.restr g) (TEnv.cons (TEnv.restr γ g) y) =
      lamV n (fun _ g' => El (fiberM n (res g (sem S T k ρ γ)) (res g (sem S T k ρ γ)) (res g (sem S f k ρ γ)) y) g')
        fun k' _ z => pathOfLine k' (connV k' z) := by
    rw [sem_lam, eFib]
    apply lamV_congr
    intro k' g' z hz
    have hz' : z ∈ El (res g' (fiberM n (res g (sem S T k ρ γ)) (res g (sem S T k ρ γ)) (res g (sem S f k ρ γ)) y))
        (Hom.id k') := by rw [El_res, Hom.comp_id]; exact hz
    rw [res_fiberM] at hz'
    obtain ⟨x, -, p, hp, rfl⟩ := mem_fiberM (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) hz'
    obtain ⟨q, hq, rfl, -, -⟩ := mem_pathC.1 hp
    have hqkv : IsKV (k' + 1) q := ((hTg.restr g').restr _).elKV _ _ _ hq
    exact (sem_contr hqkv rfl).2
  rw [sem_pair_of_kv (by rw [eP]; exact isKV_pairV' _ _) (by rw [eC]; exact isKV_mkKV _), eP, eC]

/-! ### The line equivalence -/

section lineEquiv

variable {B : Tm} {ρ : IEnv k} {γ : ℕ → V} (hγ : ∀ x, IsKV k (γ x))
  (hBn : Natural S B (k + 1) ρ.ext (TEnv.restr γ (Hom.wk k))) {l : ℕ} (hl : l ≤ maxLevel)
  (hBw : WF l (k + 1) (lineV S B k ρ γ)) (hBv : lineV S B k ρ γ ∈ Vt l)

theorem tyCode_of {l : ℕ} {c : V} (hl : l ≤ maxLevel) (hw : WF l m c) (hv : c ∈ Vt l) : TyCode m c :=
  ⟨l, hl, Or.inl ⟨hw, hv⟩⟩

include hγ hBn hl hBw hBv in
theorem sem_Q_at (g : Hom n (k + 1)) :
    sem S (Tm.isEquiv (B.dinst .zero).dshift B (Tm.lineFun B)) n (ρ.ext.restr g)
      (TEnv.restr (TEnv.restr γ (Hom.wk k)) g) = res g (eqQ k (lineV S B k ρ γ)) := by
  have hBt := tyCode_of hl hBw hBv
  have hLf := hBt.fib
  have hT0n : Natural S (B.dinst .zero).dshift (k + 1) ρ.ext (TEnv.restr γ (Hom.wk k)) := (nat_B0 hγ hBn).dshift
  have eT0 : sem S (B.dinst .zero).dshift (k + 1) ρ.ext (TEnv.restr γ (Hom.wk k)) =
      res (Hom.wk k) (res (eZ k) (lineV S B k ρ γ)) := by
    rw [sem_dshift, nat_B0 hγ hBn, sem_B0 hγ hBn]
  have hFm := arrowM_elRes (isKV_res _ _) (eqFunL_mem hLf) g
  rw [sem_isEquiv (hT0n.restr g) (hBn.restr g) ((nat_lineFun hγ hBn hBt).restr g)
    (by rw [hT0n n g, eT0]; exact (hLf.restr _ |>.restr _).restr g) (by rw [hBn n g]; exact hLf.restr g)
    (by rw [hT0n n g, eT0, hBn n g, sem_lineFun_at hγ hBn hBt g]; exact hFm),
    hT0n n g, eT0, hBn n g, sem_lineFun_at hγ hBn hBt g, eqQ, res_isEquivM]

include hγ hBn hl hBw hBv in
theorem sem_idEq_at (f : Hom n k) :
    sem S (Tm.idIsEquiv (B.dinst .zero) ((Tm.lineFun B).dinst .zero)) n (ρ.restr f) (TEnv.restr γ f) =
      res f (idEqV k (res (eZ k) (lineV S B k ρ γ)) (res (eZ k) (eqFunL k (lineV S B k ρ γ)))) := by
  have hBt := tyCode_of hl hBw hBv
  have hLf := hBt.fib
  have hT0 := nat_B0 hγ hBn
  have hF0 : Natural S ((Tm.lineFun B).dinst .zero) k ρ γ :=
    Natural.dinst (by rw [ival_zero]; exact line_endpt_nat hγ (nat_lineFun hγ hBn hBt) _)
  have eF0 : sem S ((Tm.lineFun B).dinst .zero) k ρ γ = res (eZ k) (eqFunL k (lineV S B k ρ γ)) := by
    rw [sem_lineFun_dinst hγ hBn hBt, ival_zero]
  have hFm := arrowM_elRes (isKV_res _ _) (eqFunL_mem hLf) (eZ k)
  rw [res_eZ_T'] at hFm
  have hFm' := arrowM_elRes (isKV_res _ _) hFm f
  rw [sem_idIsEquiv (hT0.restr f) (hF0.restr f) (by rw [hT0 n f, sem_B0 hγ hBn]; exact (hLf.restr _).restr f)
    (by rw [hT0 n f, hF0 n f, sem_B0 hγ hBn, eF0]; exact hFm'), hT0 n f, hF0 n f, sem_B0 hγ hBn, eF0, idEqV_res]

include hγ hBn hl hBw hBv in
theorem sem_lineEquiv : sem S (Tm.lineEquiv B) k ρ γ = eqTr k (lineV S B k ρ γ) := by
  have hBt := tyCode_of hl hBw hBv
  have hLf := hBt.fib
  have eQ : lineV S (Tm.isEquiv (B.dinst .zero).dshift B (Tm.lineFun B)) k ρ γ = eqQ k (lineV S B k ρ γ) := by
    have := sem_Q_at hγ hBn hl hBw hBv (Hom.id (k + 1))
    rwa [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr γ (Hom.wk k)) (fun y => isKV_res _ _),
      res_id (fib_eqQ hLf).kv] at this
  have eI : sem S (Tm.idIsEquiv (B.dinst .zero) ((Tm.lineFun B).dinst .zero)) k ρ γ =
      idEqV k (res (eZ k) (lineV S B k ρ γ)) (res (eZ k) (eqFunL k (lineV S B k ρ γ))) := by
    have := sem_idEq_at hγ hBn hl hBw hBv (Hom.id k)
    rwa [IEnv.restr_id, TEnv.restr_id_of_kv hγ, res_id (by unfold idEqV lamV; exact isKV_mkKV _)] at this
  have tc : TranspCond S (Tm.isEquiv (B.dinst .zero).dshift B (Tm.lineFun B)) .zero
      (Tm.idIsEquiv (B.dinst .zero) ((Tm.lineFun B).dinst .zero)) k ρ γ := by
    refine ⟨?_, ?_, ?_, fun n g => ?_, fun n f => ?_⟩
    · rw [eQ]
      exact tyCode_of hl (wf_isEquivM ((hBw.res _).res _) hBw (eqFunL_mem hLf))
        (isEquivM_mem_Vt (res_mem_Vt (res_mem_Vt hBv _) _) hBv (eqFunL_mem_Vt hBv))
    · rw [face_ival_zero]; exact constOn_bot _ _
    · rw [eQ, eI]; exact idEq_mem hLf
    · rw [sem_Q_at hγ hBn hl hBw hBv g, ← eQ]
    · rw [sem_idEq_at hγ hBn hl hBw hBv f, eI]
  have hq := (fib_eqQ hLf).trMem k (Hom.id (k + 1)) (Cof.bot k) _ (Cof.isCof_bot k) (constOn_bot _ _) (idEq_mem hLf)
  rw [Tm.lineEquiv, sem_pair_of_kv (by rw [sem_lineFun_dinst hγ hBn hBt]; exact isKV_res _ _)
    (by rw [sem_transp tc, eQ, eI, face_ival_zero]; exact (fib_eqQ hLf).elKV _ _ _ hq),
    sem_lineFun_dinst hγ hBn hBt, ival_one, sem_transp tc, eQ, eI, face_ival_zero, eqTr]

end lineEquiv

/-! ### The rule -/

section rule

variable {u u0 : Tm} {φ : I} {l : ℕ} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
  (hc : HcompCond S (.univ l) φ u u0 m ρ γ) {τ : ℕ → I} (hτ0 : τ 0 = .neg (.var 0))
  (hτs : ∀ i, τ (i + 1) = .var (i + 1))

theorem env_rev {τ : ℕ → I} (hτ0 : τ 0 = .neg (.var 0)) (hτs : ∀ i, τ (i + 1) = .var (i + 1)) (E : IEnv n) :
    (fun i => ival E (τ i)) = E.tail.cons (DM.neg (E 0)) := by
  funext i; cases i with
  | zero => rw [hτ0, ival_neg']; rfl
  | succ i => rw [hτs]; rfl

include hc in
theorem hcU_mem {n : ℕ} {g : Hom n m} (hg : (Cof.restr (ival ρ φ).face g).holds) (r : DM n) :
    WF l n (tubeV S u ρ γ n g r) ∧ tubeV S u ρ γ n g r ∈ Vt l := by
  have := hc.2.1.mem n g r hg
  rw [sem_univ, El_univC, ZFSet.mem_sep] at this; exact ⟨this.2, this.1⟩

include hc hτ0 hτs in
/-- The reversed tube line at a point of the face. -/
theorem hcU_line {n : ℕ} {g : Hom n m} (hg : (Cof.restr (ival ρ φ).face g).holds) :
    Natural S (u.dsubst τ) (n + 1) (ρ.restr g).ext (TEnv.restr (TEnv.restr γ g) (Hom.wk n)) ∧
      lineV S (u.dsubst τ) n (ρ.restr g) (TEnv.restr γ g) =
        res (revLine n) (tubeLine (tubeV S u ρ γ) g) := by
  have hφ := isCof_ival_face ρ φ
  have hcoh := hc.2.1.coh
  have hgw : (Cof.restr (ival ρ φ).face (g.comp (Hom.wk n))).holds := holds_comp hφ hg _
  have eAt : ∀ n'' (h : Hom n'' (n + 1)), sem S (u.dsubst τ) n'' ((ρ.restr g).ext.restr h)
      (TEnv.restr (TEnv.restr (TEnv.restr γ g) (Hom.wk n)) h) =
      tubeV S u ρ γ n'' ((g.comp (Hom.wk n)).comp h) ((DM.neg (lastVar n)).restr h) := by
    intro n'' h
    rw [sem_dsubst, env_rev hτ0 hτs]
    simp only [tubeV, TEnv.restr_restr]
    rfl
  have e0 : lineV S (u.dsubst τ) n (ρ.restr g) (TEnv.restr γ g) =
      tubeV S u ρ γ (n + 1) (g.comp (Hom.wk n)) (DM.neg (lastVar n)) := by
    have := eAt (n + 1) (Hom.id (n + 1))
    rw [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr (TEnv.restr γ g) (Hom.wk n)) (fun y => isKV_res _ _),
      Hom.comp_id, DM.restr_id] at this
    exact this
  refine ⟨fun n'' h => ?_, ?_⟩
  · rw [eAt]
    show _ = res h (lineV S (u.dsubst τ) n (ρ.restr g) (TEnv.restr γ g))
    rw [e0, hcoh _ _ _ hgw]
  · rw [e0, revLine, hcoh _ _ _ hgw, Hom.comp_assoc, Hom.wk_comp_snoc, lastVar_restr_snoc]

include hγ hc hτ0 hτs in
theorem sem_hcU_e {n : ℕ} {g : Hom n m} (hg : (Cof.restr (ival ρ φ).face g).holds) :
    sem S (Tm.lineEquiv (u.dsubst τ)) n (ρ.restr g) (TEnv.restr γ g) =
      eqTr n (res (revLine n) (tubeLine (tubeV S u ρ γ) g)) := by
  have hφ := isCof_ival_face ρ φ
  obtain ⟨hn, hL⟩ := hcU_line hc hτ0 hτs hg
  have hl : l ≤ maxLevel := TyCode.univ_le hc.1
  have hm := hcU_mem hc (holds_comp hφ hg (Hom.wk n)) (DM.neg (lastVar n))
  have hL' : lineV S (u.dsubst τ) n (ρ.restr g) (TEnv.restr γ g) =
      tubeV S u ρ γ (n + 1) (g.comp (Hom.wk n)) (DM.neg (lastVar n)) := by
    rw [hL, revLine, hc.2.1.coh _ _ _ (holds_comp hφ hg _), Hom.comp_assoc, Hom.wk_comp_snoc, lastVar_restr_snoc]
  rw [sem_lineEquiv (ρ := ρ.restr g) (γ := TEnv.restr γ g) (fun x => isKV_res _ _) hn hl (by rw [hL']; exact hm.1) (by rw [hL']; exact hm.2), hL]

include hγ hc hτ0 hτs in
theorem faceNat_hcU_e : FaceNat S (Tm.lineEquiv (u.dsubst τ)) φ m ρ γ := by
  have hφ := isCof_ival_face ρ φ
  intro k f hf n g
  have hfg : (Cof.restr (ival ρ φ).face (f.comp g)).holds := holds_comp hφ hf g
  have hW : ∀ k' (c : V), WF l k' c → Fib c k' := fun k' c hc' => hc'.fib
  have hmem : ∀ n' (h : Hom n' m) r, (Cof.restr (ival ρ φ).face h).holds →
      WF l n' (tubeV S u ρ γ n' h r) ∧ tubeV S u ρ γ n' h r ∈ Vt l := fun n' h r hh => hcU_mem hc hh r
  rw [IEnv.restr_restr, TEnv.restr_restr, sem_hcU_e hγ hc hτ0 hτs hfg, sem_hcU_e hγ hc hτ0 hτs hf,
    eqTr_res (fib_revLine hW hφ hmem hf) g, revLine_lift hφ hc.2.1.coh hf]

include hc in
theorem faceNat_hcU_T : FaceNat S (u.dinst .one) φ m ρ γ := by
  have hφ := isCof_ival_face ρ φ
  intro k f hf n g
  rw [sem_dinst, sem_dinst, ival_one, ival_one, IEnv.restr_restr, TEnv.restr_restr]
  show tubeV S u ρ γ n (f.comp g) (DM.one n) = res g (tubeV S u ρ γ k f (DM.one k))
  rw [hc.2.1.coh _ _ _ hf, DM.one_restr]

include hγ hc hτ0 hτs in
theorem sem_hcompU :
    sem S (Tm.glue u0 φ (u.dinst .one) (Tm.lineEquiv (u.dsubst τ))) m ρ γ = sem S (.hcomp (.univ l) φ u u0) m ρ γ := by
  have hφ := isCof_ival_face ρ φ
  have hT := faceNat_hcU_T (S := S) hc
  have he := faceNat_hcU_e hγ hc hτ0 hτs
  rw [sem_hcomp hc, sem_univ, hcompAt_univC hφ hc.2.1 hc.2.2.1, univHcF]
  by_cases hh : Cof.holds (ival ρ φ).face
  · rw [if_pos hh, sem_glue_holds hγ ((holds_iff_face ρ φ).2 hh) hT he
      (hT.kv_of_holds hγ ((holds_iff_face ρ φ).2 hh)), sem_dinst, ival_one]
    show _ = tubeV S u ρ γ m (Hom.id m) (DM.one m)
    simp only [tubeV, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
  · rw [if_neg hh, sem_glue hT he]
    congr 1
    · exact partialKV_congr fun n g hg => by rw [faceVals, sem_dinst, ival_one]; rfl
    · exact partialKV_congr fun n g hg => by rw [faceVals, sem_hcU_e hγ hc hτ0 hτs hg]

end rule

end

end Model
