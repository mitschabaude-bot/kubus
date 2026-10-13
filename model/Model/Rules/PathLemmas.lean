import Model.Rules.Basic

/-!
# Helpers for the rules of path types and interval function types

A point of the interval-extended context `Ψ + 1; Φ.shift; Γ.dshift` at stage `k` is a point
`(ρ, γ)` of `Ψ; Φ; Γ` together with an interval value `r`; the generic one is
`(ρ.ext, γ.restr wk)` at stage `k + 1`, and every other one is a restriction of it along
`endpt r`. The interpretation of `path`/`ipi` checks that its line is natural at the generic
point, which makes the line's value at any point a restriction of the generic value.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem IsPoint.dext {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} (hwf : SemWf S Ψ Φ Γ)
    (hp : IsPoint S Φ Γ m ρ γ) : IsPoint S Φ.shift Γ.dshift (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) :=
  isPoint_dshift_iff.2 (hp.restr hwf (Hom.wk m))


/-! ### Path types -/

theorem below_pathC_line (L a0 a1 : V) (hL : IsKV (m + 1) L) : Below L (pathC m L a0 a1) := by
  have h2 : Below (res (Hom.lift (Hom.id m)) L) (pathC m L a0 a1) := by
    unfold pathC
    refine Below.trans ?_ (below_dat_mkKV _ (Hom.id m))
    simp only [pathDatum, quad, tagZ]
    exact ((below_pair_left _ _).trans (below_pair_right _ _)).trans (below_pair_left _ _)
  rwa [Hom.lift_id, res_id hL] at h2

/-- Path codes of small components are small. -/
theorem pathC_mem_Vt {l : ℕ} {L a0 a1 : V} (hL : L ∈ Vt l)
    (ha0 : a0 ∈ El L (Hom.endpt m (DM.zero m))) (ha1 : a1 ∈ El L (Hom.endpt m (DM.one m))) :
    pathC m L a0 a1 ∈ Vt l := by
  have hl := le_of_mem_Vt hL
  exact pathC_mem_Vt' hl hL (Vt_trans l (El_mem_Vt hl hL _) ha0) (Vt_trans l (El_mem_Vt hl hL _) ha1)

theorem WF.path_inv {l : ℕ} {L a0 a1 : V} (hL : IsKV (m + 1) L) (ha0 : IsKV m a0) (ha1 : IsKV m a1)
    (h : WF l m (pathC m L a0 a1)) :
    WF l (m + 1) L ∧ a0 ∈ El L (Hom.endpt m (DM.zero m)) ∧ a1 ∈ El L (Hom.endpt m (DM.one m)) := by
  generalize hc : pathC m L a0 a1 = c at h
  have htag : codeTag m c = natZ tPath := by rw [← hc]; simp [codeTag, pathC, pathDatum, tagZ]
  unfold WF at h
  cases h with
  | empty => simp [tEmpty, tPath] at htag
  | pi => simp [tPi, tPath] at htag
  | sigma => simp [tSigma, tPath] at htag
  | @path _ L' a0' a1' hL' ha0' ha1' =>
    have hf := (wf_props l _ L' hL').1
    obtain ⟨rfl, rfl, rfl⟩ := pathC_inj hL ha0 ha1 hf.kv (hf.elKV _ _ _ ha0') (hf.elKV _ _ _ ha1') hc
    exact ⟨hL', ha0', ha1'⟩
  | ipi => simp [tIPi, tPath] at htag
  | univ => rw [Ucodes_lt _ ‹_›, codeTag_univC] at htag; simp [tUniv, tPath] at htag
  | glue _ hφ hn => rw [codeTag_glueC hn hφ] at htag; simp [tGlue, tPath] at htag
  | data => simp [tData, tPath] at htag

/-- What a path type in a universe gives at a point. -/
theorem SemTy.path_at {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A a b : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ Γ (.path A a b) (.univ l)) {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧ IsKV (m + 1) (lineV S A m ρ γ) ∧
      IsKV m (sem S a m ρ γ) ∧ IsKV m (sem S b m ρ γ) ∧
      sem S (.path A a b) m ρ γ = pathC m (lineV S A m ρ γ) (sem S a m ρ γ) (sem S b m ρ γ) ∧
      l ≤ maxLevel ∧ lineV S A m ρ γ ∈ Vt l ∧ WF l (m + 1) (lineV S A m ρ γ) ∧
      sem S a m ρ γ ∈ El (lineV S A m ρ γ) (Hom.endpt m (DM.zero m)) ∧
      sem S b m ρ γ ∈ El (lineV S A m ρ γ) (Hom.endpt m (DM.one m)) := by
  obtain ⟨hmem, -, hUty, -⟩ := h.2.2.2 m ρ γ hp
  obtain ⟨hN, hL, ha, hb⟩ := kv_of_sem_path (hUty.ne_empty hmem)
  rw [sem_path hN hL ha hb, sem_univ, mem_El_univ_iff] at hmem
  obtain ⟨hWL, ha0, ha1⟩ := WF.path_inv hL ha hb hmem.2
  have hl : l ≤ maxLevel := by unfold TyOK at hUty; rw [sem_univ] at hUty; exact hUty.univ_le
  exact ⟨hN, hL, ha, hb, sem_path hN hL ha hb, hl, Vt_below (below_pathC_line _ _ _ hL) hmem.1, hWL, ha0, ha1⟩

/-- A line of types, natural at every generic point, is a type in the extended context. -/
theorem SemTy.of_line {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A : Tm} {l : ℕ} (hwf : SemWf S Ψ Φ Γ)
    (hA : A.ConstsLt S.length)
    (h : ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → l ≤ maxLevel ∧
      Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧ lineV S A m ρ γ ∈ Vt l ∧
        WF l (m + 1) (lineV S A m ρ γ)) :
    SemTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l) := by
  refine ⟨hwf.dshift, hA, trivial, fun k ρ' γ hp => ?_⟩
  obtain ⟨ρ, r, rfl⟩ := ρ'.exists_cons
  have hp' : IsPoint S Φ Γ k ρ γ := isPoint_dshift_iff.1 hp
  obtain ⟨hl, hN, hV, hW⟩ := h k ρ γ hp'
  refine ⟨?_, line_endpt_nat hp'.kv hN r, ?_, fun n f => by simp [res_univC]⟩
  · rw [line_endpt hp'.kv hN r, sem_univ, mem_El_univ_iff]
    exact ⟨res_mem_Vt hV _, hW.res _⟩
  · unfold TyOK; rw [sem_univ]; exact ⟨l, hl, Or.inr rfl⟩

theorem SemTy.pathLine {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A a b : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ Γ (.path A a b) (.univ l)) : SemTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l) :=
  SemTy.of_line h.1 h.2.1.1 fun _ _ _ hp => by
    obtain ⟨hN, -, -, -, -, hl, hV, hW, -⟩ := h.path_at hp; exact ⟨hl, hN, hV, hW⟩

theorem SemTy.pathEnd {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A a b : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ Γ (.path A a b) (.univ l)) :
    SemTy S Ψ Φ Γ a (A.dinst .zero) ∧ SemTy S Ψ Φ Γ b (A.dinst .one) := by
  constructor
  · refine ⟨h.1, h.2.1.2.1, h.2.1.1.dinst _, fun m ρ γ hp => ?_⟩
    obtain ⟨hN, hL, ha, hb, hsem, hl, hV, hW, ha0, -⟩ := h.path_at hp
    have e : sem S (A.dinst .zero) m ρ γ = res (Hom.endpt m (DM.zero m)) (lineV S A m ρ γ) := by
      rw [sem_dinst, ival_zero, line_endpt hp.kv hN]
    refine ⟨by rw [e, El_res, Hom.comp_id]; exact ha0, fun k f => ?_, ?_,
      Natural.dinst (by rw [ival_zero]; exact line_endpt_nat hp.kv hN _)⟩
    · obtain ⟨-, hL', ha', hb', hsem', -⟩ := h.path_at (hp.restr h.1 f)
      have := (h.2.2.2 m ρ γ hp).2.1 k f
      rw [hsem', hsem, res_pathC] at this
      exact (pathC_inj hL' ha' hb' (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) this).2.1
    · unfold TyOK; rw [e]; exact ⟨l, hl, Or.inl ⟨hW.res _, res_mem_Vt hV _⟩⟩
  · refine ⟨h.1, h.2.1.2.2, h.2.1.1.dinst _, fun m ρ γ hp => ?_⟩
    obtain ⟨hN, hL, ha, hb, hsem, hl, hV, hW, -, ha1⟩ := h.path_at hp
    have e : sem S (A.dinst .one) m ρ γ = res (Hom.endpt m (DM.one m)) (lineV S A m ρ γ) := by
      rw [sem_dinst, ival_one, line_endpt hp.kv hN]
    refine ⟨by rw [e, El_res, Hom.comp_id]; exact ha1, fun k f => ?_, ?_,
      Natural.dinst (by rw [ival_one]; exact line_endpt_nat hp.kv hN _)⟩
    · obtain ⟨-, hL', ha', hb', hsem', -⟩ := h.path_at (hp.restr h.1 f)
      have := (h.2.2.2 m ρ γ hp).2.1 k f
      rw [hsem', hsem, res_pathC] at this
      exact (pathC_inj hL' ha' hb' (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) this).2.2
    · unfold TyOK; rw [e]; exact ⟨l, hl, Or.inl ⟨hW.res _, res_mem_Vt hV _⟩⟩

theorem mem_El_pathC {L a0 a1 v : V} (hL : IsKV (m + 1) L) (ha : IsKV m a0) (hb : IsKV m a1) :
    v ∈ El (pathC m L a0 a1) (Hom.id m) ↔ ∃ p ∈ El L (Hom.id (m + 1)), v = pathOfLine m p ∧
      res (Hom.endpt m (DM.zero m)) p = a0 ∧ res (Hom.endpt m (DM.one m)) p = a1 := by
  rw [El_pathC, Hom.lift_id, res_id hL, res_id ha, res_id hb]; exact mem_pathEl

/-- What a good path type gives at a point. -/
theorem TyOK.path_at {A a b : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : TyOK S (.path A a b) m ρ γ) :
    Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧ IsKV (m + 1) (lineV S A m ρ γ) ∧
      IsKV m (sem S a m ρ γ) ∧ IsKV m (sem S b m ρ γ) ∧
      sem S (.path A a b) m ρ γ = pathC m (lineV S A m ρ γ) (sem S a m ρ γ) (sem S b m ρ γ) ∧
      ∃ l ≤ maxLevel, lineV S A m ρ γ ∈ Vt l ∧ WF l (m + 1) (lineV S A m ρ γ) ∧
      sem S a m ρ γ ∈ El (lineV S A m ρ γ) (Hom.endpt m (DM.zero m)) ∧
      sem S b m ρ γ ∈ El (lineV S A m ρ γ) (Hom.endpt m (DM.one m)) := by
  have hne : sem S (.path A a b) m ρ γ ≠ ∅ := by
    intro he; unfold TyOK at h; rw [he] at h; exact not_isKV_empty h.fib.kv
  obtain ⟨hN, hL, ha, hb⟩ := kv_of_sem_path hne
  have hsem := sem_path hN hL ha hb
  unfold TyOK at h; rw [hsem] at h
  obtain ⟨l, hl, h | h⟩ := h
  · obtain ⟨hWL, ha0, ha1⟩ := WF.path_inv hL ha hb h.1
    exact ⟨hN, hL, ha, hb, hsem, l, hl, Vt_below (below_pathC_line _ _ _ hL) h.2, hWL, ha0, ha1⟩
  · have h1 : codeTag m (pathC m (lineV S A m ρ γ) (sem S a m ρ γ) (sem S b m ρ γ)) = natZ tPath := by
      simp [codeTag, pathC, pathDatum, tagZ]
    rw [h, codeTag_univC] at h1; simp [tUniv, tPath] at h1

theorem pappV_empty (r : DM m) : pappV m (∅ : V) r = ∅ := by
  simp [pappV, here, dat_empty', apC, apZ]

theorem isPoint_cons_iff {Φ : I} {Γ : Ctx} {ρ : IEnv m} {γ : ℕ → V} {r : DM m} :
    IsPoint S Φ.shift Γ.dshift m (ρ.cons r) γ ↔ IsPoint S Φ Γ m ρ γ := isPoint_dshift_iff

/-- The body of the η-expansion of a path `p = ⟨P⟩` at the generic point is `P`. -/
theorem sem_eta_body {p : Tm} {ρ : IEnv m} {γ : ℕ → V} {P : V} (hnat : Natural S p m ρ γ)
    (hP : sem S p m ρ γ = pathOfLine m P) (k : ℕ) (g : Hom k (m + 1)) :
    sem S (.papp p.dshift (.var 0)) k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) = res g P := by
  rw [sem_papp, sem_dshift_tail, IEnv.tail_restr]
  have e1 : (ρ.ext).tail = ρ.restr (Hom.wk m) := rfl
  rw [e1, IEnv.restr_restr, TEnv.restr_restr, hnat k, hP, res_pathOfLine, pappV_pathOfLine, res_res,
    Hom.lift_comp_endpt']
  show res (Hom.snoc ((Hom.wk m).comp g) ((lastVar m).restr g)) P = _
  rw [snoc_wk_lastVar]

/-! ### Interval function types -/

theorem sem_ipi {A : Tm} {ρ : IEnv m} {γ : ℕ → V}
    (hN : Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (hL : IsKV (m + 1) (lineV S A m ρ γ)) :
    sem S (.ipi A) m ρ γ = ipiC m (lineV S A m ρ γ) := by
  simp only [sem, interp]; exact if_pos ⟨hN, hL⟩

theorem kv_of_sem_ipi {A : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : sem S (.ipi A) m ρ γ ≠ ∅) :
    Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧ IsKV (m + 1) (lineV S A m ρ γ) := by
  simp only [sem, interp] at h; split at h
  · assumption
  · exact absurd rfl h

theorem below_ipiC_line (L : V) (hL : IsKV (m + 1) L) : Below L (ipiC m L) := by
  have h2 : Below (res (Hom.lift (Hom.id m)) L) (ipiC m L) := by
    unfold ipiC
    refine Below.trans ?_ (below_dat_mkKV _ (Hom.id m))
    simp only [ipiDatum, quad, tagZ]
    exact ((below_pair_left _ _).trans (below_pair_right _ _)).trans (below_pair_left _ _)
  rwa [Hom.lift_id, res_id hL] at h2

/-- Codes of interval function types of small lines are small. -/
theorem ipiC_mem_Vt {l : ℕ} {L : V} (hL : L ∈ Vt l) : ipiC m L ∈ Vt l := ipiC_mem_Vt' (le_of_mem_Vt hL) hL

theorem WF.ipi_inv {l : ℕ} {L : V} (hL : IsKV (m + 1) L) (h : WF l m (ipiC m L)) : WF l (m + 1) L := by
  generalize hc : ipiC m L = c at h
  have htag : codeTag m c = natZ tIPi := by rw [← hc]; simp [codeTag, ipiC, ipiDatum, tagZ]
  unfold WF at h
  cases h with
  | empty => simp [tEmpty, tIPi] at htag
  | pi => simp [tPi, tIPi] at htag
  | sigma => simp [tSigma, tIPi] at htag
  | path => simp [codeTag, pathC, pathDatum, tagZ, tPath, tIPi] at htag
  | @ipi _ L' hL' =>
    obtain rfl := ipiC_inj hL (wf_props l _ L' hL').1.kv hc
    exact hL'
  | univ => rw [Ucodes_lt _ ‹_›, codeTag_univC] at htag; simp [tUniv, tIPi] at htag
  | glue _ hφ hn => rw [codeTag_glueC hn hφ] at htag; simp [tGlue, tIPi] at htag
  | data => simp [tData, tIPi] at htag

theorem mem_El_ipiC {L v : V} (hL : IsKV (m + 1) L) :
    v ∈ El (ipiC m L) (Hom.id m) ↔ ∃ p ∈ El L (Hom.id (m + 1)), v = pathOfLine m p := by
  rw [El_ipiC, Hom.lift_id, res_id hL]; exact mem_ipiEl

/-- What a good interval function type gives at a point. -/
theorem TyOK.ipi_at {A : Tm} {ρ : IEnv m} {γ : ℕ → V} (h : TyOK S (.ipi A) m ρ γ) :
    Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧ IsKV (m + 1) (lineV S A m ρ γ) ∧
      sem S (.ipi A) m ρ γ = ipiC m (lineV S A m ρ γ) ∧
      ∃ l ≤ maxLevel, lineV S A m ρ γ ∈ Vt l ∧ WF l (m + 1) (lineV S A m ρ γ) := by
  have hne : sem S (.ipi A) m ρ γ ≠ ∅ := by
    intro he; unfold TyOK at h; rw [he] at h; exact not_isKV_empty h.fib.kv
  obtain ⟨hN, hL⟩ := kv_of_sem_ipi hne
  have hsem := sem_ipi hN hL
  unfold TyOK at h; rw [hsem] at h
  obtain ⟨l, hl, h | h⟩ := h
  · exact ⟨hN, hL, hsem, l, hl, Vt_below (below_ipiC_line _ hL) h.2, WF.ipi_inv hL h.1⟩
  · have h1 : codeTag m (ipiC m (lineV S A m ρ γ)) = natZ tIPi := by
      simp [codeTag, ipiC, ipiDatum, tagZ]
    rw [h, codeTag_univC] at h1; simp [tUniv, tIPi] at h1

theorem SemTy.ipi_at {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A : Tm} {l : ℕ}
    (h : SemTy S Ψ Φ Γ (.ipi A) (.univ l)) {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧ IsKV (m + 1) (lineV S A m ρ γ) ∧
      sem S (.ipi A) m ρ γ = ipiC m (lineV S A m ρ γ) ∧ l ≤ maxLevel ∧
      lineV S A m ρ γ ∈ Vt l ∧ WF l (m + 1) (lineV S A m ρ γ) := by
  obtain ⟨hmem, -, hUty, -⟩ := h.2.2.2 m ρ γ hp
  obtain ⟨hN, hL⟩ := kv_of_sem_ipi (hUty.ne_empty hmem)
  rw [sem_ipi hN hL, sem_univ, mem_El_univ_iff] at hmem
  have hl : l ≤ maxLevel := by unfold TyOK at hUty; rw [sem_univ] at hUty; exact hUty.univ_le
  exact ⟨hN, hL, sem_ipi hN hL, hl, Vt_below (below_ipiC_line _ hL) hmem.1, WF.ipi_inv hL hmem.2⟩

end

end Model
