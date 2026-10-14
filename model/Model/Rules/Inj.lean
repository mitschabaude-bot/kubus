import Model.Rules.Stubs

/-!
# Injectivity and no-confusion of type formers

The codes of the type formers with a head (`Tm.tyHead`) carry their head (tag, and for
inductive types the index), and the codes of `Π`, `Σ`, path types, `(i : I) → A` and inductive
types are injective in their components (inductive types record their parameter values).
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore KubusCore.Tm

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-- The head of a code: its tag, and for an inductive type its index. -/
def codeHead (m : ℕ) (c : V) : V :=
  ZFSet.pair (codeTag m c) (if codeTag m c = natZ tData then π1 (π2 (shapeOf c (Hom.id m))) else ∅)

/-- The tag of a syntactic head. -/
def headTag : ℕ → ℕ
  | 0 => tPi
  | 1 => tSigma
  | 2 => tPath
  | 3 => tIPi
  | 4 => tUniv
  | _ => tData

def headEnc : ℕ × ℕ → V
  | (a, b) => ZFSet.pair (natZ (headTag a)) (if a = 5 then natZ b else ∅)

theorem headEnc_inj {h h' : ℕ × ℕ} (hh : h.1 ≤ 5) (hh' : h'.1 ≤ 5) (hb : h.1 ≠ 5 → h.2 = 0)
    (hb' : h'.1 ≠ 5 → h'.2 = 0) (e : headEnc h = headEnc h') : h = h' := by
  obtain ⟨a, b⟩ := h; obtain ⟨a', b'⟩ := h'
  simp only [headEnc, pair_inj', natZ_inj] at e
  obtain ⟨e1, e2⟩ := e
  have key : ∀ x, x < 6 → ∀ y, y < 6 → headTag x = headTag y → x = y := by decide
  have ha : a = a' := key a (by simp at hh; omega) a' (by simp at hh'; omega) e1
  subst ha
  by_cases h5 : a = 5
  · simp only [h5, if_true, natZ_inj] at e2; subst e2; rfl
  · simp only at hb hb'; rw [hb h5, hb' h5]

theorem tyHead_facts {X : Tm} {h : ℕ × ℕ} (hX : X.tyHead = some h) : h.1 ≤ 5 ∧ (h.1 ≠ 5 → h.2 = 0) := by
  cases X <;> simp [Tm.tyHead] at hX <;> subst hX <;> simp

theorem sigV_dat_entry {d : ℕ} (hd : d < S.length) {ps : RV m} (h : (sigV S).dat m d ps ≠ ∅) :
    ∃ D, S[d]? = some (.data D) := by
  cases he : S[d]? with
  | none => rw [List.getElem?_eq_none_iff] at he; omega
  | some e =>
    cases e with
    | data D => exact ⟨D, rfl⟩
    | defn t A =>
      exfalso; apply h
      have ha := sigUpTo_agree S S.length (k := d + 1) hd
      rw [sigV, ← ha.2.1 m d ps (by omega)]
      simp only [sigUpTo, SigV.set, if_pos rfl, he, entrySem, SigV.empty, if_true]

/-- The head of a typed type former is its syntactic head. -/
theorem codeHead_sem {Ψ : ℕ} {Φ : I} {Γ : Ctx} {X : Tm} {l : ℕ} (hX : SemTy S Ψ Φ Γ X (.univ l))
    {h : ℕ × ℕ} (hh : X.tyHead = some h) {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    codeHead m (sem S X m ρ γ) = headEnc h := by
  obtain ⟨hm, -, hUty, -⟩ := hX.2.2.2 m ρ γ hp
  have hty : TyOK S X m ρ γ := TyCode.of_mem_univ hUty hm
  cases X with
  | pi A B =>
    simp [Tm.tyHead] at hh; subst hh
    rw [sem_pi hty.pi_at.1]; simp [codeHead, headEnc, headTag, tPi, tData]
  | sigma A B =>
    simp [Tm.tyHead] at hh; subst hh
    rw [hty.sigma_data.2.1]; simp [codeHead, headEnc, headTag, tSigma, tData]
  | path A a b =>
    simp [Tm.tyHead] at hh; subst hh
    rw [hty.path_at.2.2.2.2.1]; simp [codeHead, headEnc, headTag, tPath, tData]
  | ipi A =>
    simp [Tm.tyHead] at hh; subst hh
    rw [hty.ipi_at.2.2.1]; simp [codeHead, headEnc, headTag, tIPi, tData]
  | univ k =>
    simp [Tm.tyHead] at hh; subst hh
    rw [sem_univ]; simp [codeHead, headEnc, headTag, tUniv, tData]
  | data d ps =>
    simp [Tm.tyHead] at hh; subst hh
    have hne : sem S (.data d ps) m ρ γ ≠ ∅ := fun he => not_isKV_empty (he ▸ hty.fib.kv)
    obtain ⟨D, hD⟩ := sigV_dat_entry hX.2.1.1 hne
    rw [sem_data_of hD (paramsOK_of_sem_data hD hne)]
    simp [codeHead, headEnc, headTag, shapeOf_dataC, tagZ, dataSD]
  | _ => simp [Tm.tyHead] at hh

theorem sem_EqTm_noConf {Ψ Φ Γ X Y l t u T} (h0 : X.headClash Y = true) (h1 : SemEq S Ψ Φ Γ X Y (.univ l))
    (h2 : SemTy S Ψ Φ Γ t T) (h3 : SemTy S Ψ Φ Γ u T) : SemEq S Ψ Φ Γ t u T := by
  refine ⟨h2, h3, fun m ρ γ hp => ?_⟩
  exfalso
  unfold Tm.headClash at h0
  cases hX : X.tyHead with
  | none => rw [hX] at h0; simp at h0
  | some hx =>
    cases hY : Y.tyHead with
    | none => rw [hX, hY] at h0; simp at h0
    | some hy =>
      rw [hX, hY] at h0
      have e := codeHead_sem h1.1 hX hp
      rw [h1.2.2 m ρ γ hp, codeHead_sem h1.2.1 hY hp] at e
      have fx := tyHead_facts hX; have fy := tyHead_facts hY
      have := headEnc_inj fy.1 fx.1 fy.2 fx.2 e
      subst this; simp at h0

theorem tyOK_of_univ {Ψ : ℕ} {Φ : I} {Γ : Ctx} {X : Tm} {l : ℕ} (hX : SemTy S Ψ Φ Γ X (.univ l))
    {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) : TyOK S X m ρ γ := by
  obtain ⟨hm, -, hUty, -⟩ := hX.2.2.2 m ρ γ hp
  exact TyCode.of_mem_univ hUty hm

/-! ### Π and Σ -/

theorem sem_EqTm_piInjDom {Ψ Φ Γ A A' B B' l} (h : SemEq S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l)) :
    SemEq S Ψ Φ Γ A A' (.univ l) := by
  refine ⟨h.1.piDom, h.2.1.piDom, fun m ρ γ hp => ?_⟩
  have e := h.2.2 m ρ γ hp
  have h1 := (tyOK_of_univ h.1 hp).pi_at.1
  have h2 := (tyOK_of_univ h.2.1 hp).pi_at.1
  rw [sem_pi h1, sem_pi h2] at e
  exact (piC_inj h1 (isKV_famV _ _) h2 (isKV_famV _ _) e).1

theorem sem_EqTm_piInjCod {Ψ Φ Γ A A' B B' a l} (h : SemEq S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l))
    (ha : SemTy S Ψ Φ Γ a A) : SemEq S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l) := by
  have hdom := sem_EqTm_piInjDom h
  refine ⟨sem_HasTy_subst h.1.piCod ha, sem_HasTy_subst h.2.1.piCod (sem_HasTy_conv ha hdom), fun m ρ γ hp => ?_⟩
  have e := h.2.2 m ρ γ hp
  have h1 := (tyOK_of_univ h.1 hp).pi_at.1
  have h2 := (tyOK_of_univ h.2.1 hp).pi_at.1
  rw [sem_pi h1, sem_pi h2] at e
  obtain ⟨eA, eF⟩ := piC_inj h1 (isKV_famV _ _) h2 (isKV_famV _ _) e
  obtain ⟨hamem, hanat, -, -⟩ := ha.2.2.2 m ρ γ hp
  have hamem' : sem S a m ρ γ ∈ El (sem S A' m ρ γ) (Hom.id m) := eA ▸ hamem
  have := congrArg (fun F => apZ (dat F m (Hom.id m)) (sem S a m ρ γ)) eF
  simp only at this
  rw [apZ_dat_famV _ _ _ hamem, apZ_dat_famV _ _ _ hamem'] at this
  rw [sem_inst hanat, sem_inst hanat]
  simpa [IEnv.restr_id, TEnv.restr_id_of_kv hp.kv] using this

theorem sem_EqTm_sigmaInjDom {Ψ Φ Γ A A' B B' l} (h : SemEq S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l)) :
    SemEq S Ψ Φ Γ A A' (.univ l) := by
  refine ⟨h.1.sigmaDom, h.2.1.sigmaDom, fun m ρ γ hp => ?_⟩
  have e := h.2.2 m ρ γ hp
  have h1 := (tyOK_of_univ h.1 hp).sigma_data
  have h2 := (tyOK_of_univ h.2.1 hp).sigma_data
  rw [h1.2.1, h2.2.1] at e
  exact (sigmaC_inj h1.1 (isKV_famV _ _) h2.1 (isKV_famV _ _) e).1

theorem sem_EqTm_sigmaInjCod {Ψ Φ Γ A A' B B' a l} (h : SemEq S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l))
    (ha : SemTy S Ψ Φ Γ a A) : SemEq S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l) := by
  have hdom := sem_EqTm_sigmaInjDom h
  refine ⟨sem_HasTy_subst h.1.sigmaCod ha, sem_HasTy_subst h.2.1.sigmaCod (sem_HasTy_conv ha hdom),
    fun m ρ γ hp => ?_⟩
  have e := h.2.2 m ρ γ hp
  have h1 := (tyOK_of_univ h.1 hp).sigma_data
  have h2 := (tyOK_of_univ h.2.1 hp).sigma_data
  rw [h1.2.1, h2.2.1] at e
  obtain ⟨eA, eF⟩ := sigmaC_inj h1.1 (isKV_famV _ _) h2.1 (isKV_famV _ _) e
  obtain ⟨hamem, hanat, -, -⟩ := ha.2.2.2 m ρ γ hp
  have hamem' : sem S a m ρ γ ∈ El (sem S A' m ρ γ) (Hom.id m) := eA ▸ hamem
  have := congrArg (fun F => apZ (dat F m (Hom.id m)) (sem S a m ρ γ)) eF
  simp only at this
  rw [apZ_dat_famV _ _ _ hamem, apZ_dat_famV _ _ _ hamem'] at this
  rw [sem_inst hanat, sem_inst hanat]
  simpa [IEnv.restr_id, TEnv.restr_id_of_kv hp.kv] using this

/-! ### Path types and `(i : I) → A` -/

theorem path_line_eq {Ψ Φ Γ A A' a a' b b' l} (h : SemEq S Ψ Φ Γ (.path A a b) (.path A' a' b') (.univ l))
    {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    lineV S A m ρ γ = lineV S A' m ρ γ ∧ sem S a m ρ γ = sem S a' m ρ γ ∧ sem S b m ρ γ = sem S b' m ρ γ := by
  have e := h.2.2 m ρ γ hp
  obtain ⟨-, hL1, ha1, hb1, he1, -⟩ := (tyOK_of_univ h.1 hp).path_at
  obtain ⟨-, hL2, ha2, hb2, he2, -⟩ := (tyOK_of_univ h.2.1 hp).path_at
  rw [he1, he2] at e
  exact pathC_inj hL1 ha1 hb1 hL2 ha2 hb2 e

theorem sem_EqTm_pathInjLine {Ψ Φ Γ A A' a a' b b' r l}
    (h : SemEq S Ψ Φ Γ (.path A a b) (.path A' a' b') (.univ l)) (hr : r.Scoped Ψ) :
    SemEq S Ψ Φ Γ (A.dinst r) (A'.dinst r) (.univ l) := by
  refine ⟨sem_HasTy_dsubst h.1.pathLine hr, sem_HasTy_dsubst h.2.1.pathLine hr, fun m ρ γ hp => ?_⟩
  obtain ⟨hN1, -⟩ := (tyOK_of_univ h.1 hp).path_at
  obtain ⟨hN2, -⟩ := (tyOK_of_univ h.2.1 hp).path_at
  rw [sem_dinst, sem_dinst, line_endpt hp.kv hN1, line_endpt hp.kv hN2, (path_line_eq h hp).1]

theorem sem_EqTm_pathInjLeft {Ψ Φ Γ A A' a a' b b' l}
    (h : SemEq S Ψ Φ Γ (.path A a b) (.path A' a' b') (.univ l)) :
    SemEq S Ψ Φ Γ a a' (A.dinst .zero) := by
  have hl := sem_EqTm_pathInjLine h (r := .zero) trivial
  refine ⟨h.1.pathEnd.1, h.2.1.pathEnd.1.retype hl.1.2.1 fun m ρ γ hp => (hl.2.2 m ρ γ hp).symm,
    fun m ρ γ hp => (path_line_eq h hp).2.1⟩

theorem sem_EqTm_pathInjRight {Ψ Φ Γ A A' a a' b b' l}
    (h : SemEq S Ψ Φ Γ (.path A a b) (.path A' a' b') (.univ l)) :
    SemEq S Ψ Φ Γ b b' (A.dinst .one) := by
  have hl := sem_EqTm_pathInjLine h (r := .one) trivial
  refine ⟨h.1.pathEnd.2, h.2.1.pathEnd.2.retype hl.1.2.1 fun m ρ γ hp => (hl.2.2 m ρ γ hp).symm,
    fun m ρ γ hp => (path_line_eq h hp).2.2⟩

theorem sem_EqTm_ipiInj {Ψ Φ Γ A A' r l} (h : SemEq S Ψ Φ Γ (.ipi A) (.ipi A') (.univ l)) (hr : r.Scoped Ψ) :
    SemEq S Ψ Φ Γ (A.dinst r) (A'.dinst r) (.univ l) := by
  refine ⟨sem_HasTy_dsubst (sem_HasTy_ipiLine h.1) hr, sem_HasTy_dsubst (sem_HasTy_ipiLine h.2.1) hr,
    fun m ρ γ hp => ?_⟩
  have e := h.2.2 m ρ γ hp
  obtain ⟨hN1, hL1, he1, -⟩ := (tyOK_of_univ h.1 hp).ipi_at
  obtain ⟨hN2, hL2, he2, -⟩ := (tyOK_of_univ h.2.1 hp).ipi_at
  rw [he1, he2] at e
  rw [sem_dinst, sem_dinst, line_endpt hp.kv hN1, line_endpt hp.kv hN2, ipiC_inj hL1 hL2 e]

/-! ### Inductive types -/

theorem dataC_inj {Θ Θ' : SData m} (h : dataC Θ = dataC Θ') :
    Θ.idx = Θ'.idx ∧ Θ.pv m (Hom.id m) = Θ'.pv m (Hom.id m) := by
  have := congrArg (fun c => shapeOf c (Hom.id m)) h
  simp only [shapeOf_dataC, tagZ_inj, pair_inj', natZ_inj, true_and] at this
  exact ⟨this.1, this.2.1.1⟩

theorem sem_ps_eq_of_data {Ψ Φ Γ d D ps ps' l} (hd : S[d]? = some (.data D))
    (h : SemEq S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l)) {ρ : IEnv m} {γ : ℕ → V}
    (hp : IsPoint S Φ Γ m ρ γ) : sem S ps m ρ γ = sem S ps' m ρ γ := by
  have ne : ∀ {q : Tm}, SemTy S Ψ Φ Γ (.data d q) (.univ l) → sem S (.data d q) m ρ γ ≠ ∅ := fun hq he =>
    not_isKV_empty (he ▸ (tyOK_of_univ hq hp).fib.kv)
  have e := h.2.2 m ρ γ hp
  rw [sem_data_of hd (paramsOK_of_sem_data hd (ne h.1)), sem_data_of hd (paramsOK_of_sem_data hd (ne h.2.1))] at e
  have := (dataC_inj e).2
  simpa [dataSD, psRV, IEnv.restr_id, TEnv.restr_id_of_kv hp.kv] using this

theorem sem_EqTm_dataInjAt {Ψ Φ Γ d} {D : DataDecl} {ps ps' : Tm} {l k : ℕ} {p p' A : Tm}
    (h0 : S[d]? = some (.data D)) (hpl : ps = Tm.ofList ps.toList) (hpl' : ps' = Tm.ofList ps'.toList)
    (h1 : SemEq S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l)) (h2 : ps.toList[k]? = some p)
    (h3 : ps'.toList[k]? = some p') (h4 : SemTy S Ψ Φ Γ p (A.substList (ps.toList.take k).reverse))
    (h5 : SemTy S Ψ Φ Γ p' (A.substList (ps.toList.take k).reverse)) :
    SemEq S Ψ Φ Γ p p' (A.substList (ps.toList.take k).reverse) := by
  refine ⟨h4, h5, fun m ρ γ hp => ?_⟩
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h2
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 h3
  rw [← sem_vnth ps _ _ k hk, ← sem_vnth ps' _ _ k hk', sem_ps_eq_of_data h0 h1 hp]

theorem sem_substList_congr {Φ : I} {Γ : Ctx} (A : Tm) : ∀ (L L' : List Tm), L.length = L'.length →
    (∀ i (hi : i < L.length) (hi' : i < L'.length), ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ →
      sem S L[i] m ρ γ = sem S L'[i] m ρ γ ∧ Natural S L[i] m ρ γ ∧ Natural S L'[i] m ρ γ) →
    ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → sem S (A.substList L) m ρ γ = sem S (A.substList L') m ρ γ := by
  intro L L' hl hL m ρ γ hp
  have hn : ∀ (L0 : List Tm), (∀ i (hi : i < L0.length), Natural S L0[i] m ρ γ) →
      ∀ x, Natural S (L0.getD x (.var (x - L0.length))) m ρ γ := by
    intro L0 h x
    rw [List.getD_eq_getElem?_getD]
    cases hx : L0[x]? with
    | none => exact natural_var S _ _ _
    | some t => obtain ⟨hx', rfl⟩ := List.getElem?_eq_some_iff.1 hx; exact h x hx'
  unfold Tm.substList
  rw [sem_subst S A m ρ γ _ _ (hn L fun i hi => (hL i hi (by omega) m ρ γ hp).2.1),
    sem_subst S A m ρ γ _ _ (hn L' fun i hi => (hL i (by omega) hi m ρ γ hp).2.2)]
  congr 1; funext x
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hx : x < L.length
  · rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem (by omega)]
    exact (hL x hx (by omega) m ρ γ hp).1
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega), hl]

theorem SemTele.nil_inv {Ψ Φ Γ} {ps : Tm} {prev : List Tm} (h : SemTele S Ψ Φ Γ ps [] prev) :
    ps = .tnil ∧ SemWf S Ψ Φ Γ := by
  cases ps <;> simp only [SemTele] at h <;> exact ⟨rfl, h⟩

theorem SemTele.cons_inv {Ψ Φ Γ} {ps A : Tm} {Δ prev : List Tm} (h : SemTele S Ψ Φ Γ ps (A :: Δ) prev) :
    ∃ a as, ps = .tcons a as := by
  cases ps <;> simp only [SemTele] at h <;> exact ⟨_, _, rfl⟩

theorem semEqTele_of_eq {Ψ Φ Γ} : ∀ (Δ : List Tm) (ps ps' : Tm) (prev prev' : List Tm),
    SemTele S Ψ Φ Γ ps Δ prev → SemTele S Ψ Φ Γ ps' Δ prev' → prev.length = prev'.length →
    (∀ i (hi : i < prev.length) (hi' : i < prev'.length), ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ →
      sem S prev[i] m ρ γ = sem S prev'[i] m ρ γ ∧ Natural S prev[i] m ρ γ ∧ Natural S prev'[i] m ρ γ) →
    (∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → sem S ps m ρ γ = sem S ps' m ρ γ) →
    SemEqTele S Ψ Φ Γ ps ps' Δ prev
  | [], ps, ps', prev, prev', h1, h2, _, _, _ => by
    obtain ⟨rfl, hw⟩ := h1.nil_inv
    obtain ⟨rfl, -⟩ := h2.nil_inv
    exact hw
  | A :: Δ, ps, ps', prev, prev', h1, h2, hl, hpv, he => by
    obtain ⟨a, as, rfl⟩ := h1.cons_inv
    obtain ⟨a', as', rfl⟩ := h2.cons_inv
    simp only [SemTele] at h1 h2
    show SemEq S Ψ Φ Γ a a' (A.substList prev) ∧ SemEqTele S Ψ Φ Γ as as' Δ (a :: prev)
    obtain ⟨ha, has⟩ := h1
    obtain ⟨ha', has'⟩ := h2
    have hea : ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → sem S a m ρ γ = sem S a' m ρ γ ∧ sem S as m ρ γ = sem S as' m ρ γ := by
      intro m ρ γ hp
      have := he m ρ γ hp
      simp only [sem, interp] at this
      exact pair_inj.1 this
    refine ⟨⟨ha, ha'.retype ha.2.2.1 fun m ρ γ hp => (sem_substList_congr A prev prev' hl hpv m ρ γ hp).symm,
      fun m ρ γ hp => (hea m ρ γ hp).1⟩, ?_⟩
    refine semEqTele_of_eq Δ as as' (a :: prev) (a' :: prev') has has' (by simp [hl]) (fun i hi hi' m ρ γ hp => ?_)
      fun m ρ γ hp => (hea m ρ γ hp).2
    cases i with
    | zero => exact ⟨(hea m ρ γ hp).1, (ha.2.2.2 m ρ γ hp).2.1, (ha'.2.2.2 m ρ γ hp).2.1⟩
    | succ i => exact hpv i (by simp at hi; omega) (by simp at hi'; omega) m ρ γ hp

theorem sem_EqTele_dataInj {Ψ Φ Γ d D ps ps' l} (h0 : S[d]? = some (.data D))
    (h1 : SemTele S Ψ Φ Γ ps D.params []) (h2 : SemTele S Ψ Φ Γ ps' D.params [])
    (h3 : SemEq S Ψ Φ Γ (.data d ps) (.data d ps') (.univ l)) : SemEqTele S Ψ Φ Γ ps ps' D.params [] :=
  semEqTele_of_eq D.params ps ps' [] [] h1 h2 rfl (fun i hi => absurd hi (by simp))
    fun m ρ γ hp => sem_ps_eq_of_data h0 h3 hp

end

end Model
