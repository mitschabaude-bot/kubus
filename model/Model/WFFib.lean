import Model.UnivHcFib

/-!
# Well-formed codes are fibrant

`WF.fib`: a well-formed code is a lawful fibrant type, and well-formedness is stable under
restriction. Proven by induction on the level (the elements of a universe are codes of lower
level) and on the well-formedness derivation, using the fibrancy theorems of the type formers.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem isKV_univC (l : ℕ) : IsKV m (univC m l) := by
  unfold univC univCode; exact isKV_mkKV _

theorem hcompAt_univC {l : ℕ} {f : Hom k m} {φ : Cof k} {u : Tube k} {u0 : V} (hφ : φ.IsCof)
    (hu : TubeOK (univC m l) f φ u u0) (hu0 : u0 ∈ El (univC m l) f) :
    hcompAt (univC m l) f φ u u0 = univHcF k φ u u0 := by
  rw [hcompAt]
  simp only [univC, univCode, hcG, dat_mkKV, univDatum, quad, π2_pair]
  rw [apZ_hcGraph _ (fun n h r hh => by have := hu.mem n h r hh; rwa [El_univC] at this)
    (by rw [El_univC] at hu0; exact hu0), univHcF_canon hφ]

/-- The universe of level `l` is fibrant, given that its elements are fibrant and closed under
restriction. -/
theorem fib_univC {l : ℕ} (hfib : ∀ k c, WF l k c → Fib c k)
    (hres : ∀ k c, WF l k c → ∀ n (h : Hom n k), WF l n (res h c))
    (hsmall : ∀ k c, c ∈ Vt l → ∀ n (h : Hom n k), res h c ∈ Vt l) : Fib (univC m l) m where
  kv := isKV_univC l
  elKV k f c hc := by rw [El_univC, ZFSet.mem_sep] at hc; exact (hfib k c hc.2).kv
  elRes k f c hc n h := by
    rw [El_univC, ZFSet.mem_sep] at hc ⊢
    exact ⟨hsmall k c hc.1 n h, hres k c hc.2 n h⟩
  hcMem k f φ u u0 hφ hu0 hu := by
    rw [hcompAt_univC hφ hu hu0]
    rw [El_univC, ZFSet.mem_sep] at hu0 ⊢
    have hmem : ∀ n (h : Hom n k) r, (φ.restr h).holds → WF l n (u n h r) ∧ u n h r ∈ Vt l := fun n h r hh => by
      have := hu.mem n h r hh; rw [El_univC, ZFSet.mem_sep] at this; exact ⟨this.2, this.1⟩
    exact ⟨univHcF_small hφ hmem ⟨hu0.2, hu0.1⟩, univHcF_wf hfib hφ hmem hu.coh hu.base ⟨hu0.2, hu0.1⟩⟩
  hcFace k f φ u u0 hφ hu0 hu hh := by
    rw [hcompAt_univC hφ hu hu0, univHcF, if_pos hh]
  hcRes k f φ u u0 hφ hu0 hu n h := by
    have hmem : ∀ n (h : Hom n k) r, (φ.restr h).holds → WF l n (u n h r) ∧ u n h r ∈ Vt l := fun n h r hh => by
      have := hu.mem n h r hh; rw [El_univC, ZFSet.mem_sep] at this; exact ⟨this.2, this.1⟩
    have hu0' : res h u0 ∈ El (univC m l) (f.comp h) := by
      rw [El_univC, ZFSet.mem_sep] at hu0 ⊢; exact ⟨hsmall _ _ hu0.1 _ h, hres _ _ hu0.2 _ h⟩
    rw [hcompAt_univC hφ hu hu0, hcompAt_univC (hφ.restr h) (hu.restr h) hu0',
      univHcF_res hfib hφ hmem hu.coh h]
  trMem n f φ a0 _ _ ha := by
    have e : transpAt (univC m l) f φ a0 = a0 := by
      rw [transpAt]; simp only [univC, univCode, trG_mkKV, univDatum, π1π2π2_quad, univTr]
      rw [El_univC] at ha
      exact apZ_trGraph _ ha
    rw [e]; rw [El_univC] at ha ⊢; exact ha
  trFace n f φ a0 _ _ ha _ := by
    rw [transpAt]; simp only [univC, univCode, trG_mkKV, univDatum, π1π2π2_quad, univTr]
    rw [El_univC] at ha
    exact apZ_trGraph _ ha
  trRes n f φ a0 _ _ ha n' h := by
    have e : ∀ {n} (f : Hom (n + 1) m) φ a0, a0 ∈ El (univC m l) (f.comp (Hom.endpt n (DM.zero n))) →
        transpAt (univC m l) f φ a0 = a0 := by
      intro n f φ a0 ha
      rw [transpAt]; simp only [univC, univCode, trG_mkKV, univDatum, π1π2π2_quad, univTr]
      rw [El_univC] at ha
      exact apZ_trGraph _ ha
    rw [e f φ a0 ha, e _ _ _ (by
      rw [El_univC, ZFSet.mem_sep] at ha ⊢
      exact ⟨hsmall _ _ ha.1 _ h, hres _ _ ha.2 _ h⟩)]

end

end Model

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-- Restriction preserves smallness. -/
theorem res_mem_Vt {l : ℕ} {c : V} (hc : c ∈ Vt l) (h : Hom n k) : res h c ∈ Vt l :=
  res_mem_Vt' (le_of_mem_Vt hc) hc h

/-- Glue types are fibrant. -/
theorem fib_glueC {A : V} {φ : Cof m} {Tp ep : V} (hA : Fib A m) (hφ : φ.IsCof)
    (hTp : Tp = partialKV m φ (fun k f => dat Tp k f)) (hep : ep = partialKV m φ (fun k f => dat ep k f))
    (hT : ∀ k (f : Hom k m), (φ.restr f).holds → Fib (dat Tp k f) k)
    (hTcoh : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (he : ∀ k (f : Hom k m), (φ.restr f).holds → dat ep k f ∈ El (equivCode k (dat Tp k f) (res f A)) (Hom.id k))
    (hecoh : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat ep k f) = dat ep n (f.comp h)) :
    Fib (glueC m A φ Tp ep) m :=
  GlueOK.fib ⟨hA, hφ, hTp, hep, hT, hTcoh, he, hecoh⟩

theorem famOK_of {l : ℕ} {A B : V} (hBkv : IsKV m B)
    (hgraph : ∀ k (f : Hom k m), dat B k f = fnZ (El A f) (apZ (dat B k f)))
    (hfib : ∀ k (f : Hom k m), ∀ a ∈ El A f, Fib (apZ (dat B k f) a) k)
    (hcoh : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
      res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a)) : FamOK A B m :=
  ⟨hBkv, hgraph, hfib, hcoh⟩

/-- Well-formed codes are fibrant, and well-formedness is stable under restriction. -/
theorem wf_props : ∀ l, ∀ m c, WF l m c → Fib c m ∧ ∀ k (h : Hom k m), WF l k (res h c) := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ihl =>
  intro m c hc
  induction hc with
  | empty => exact ⟨fib_emptyC, fun k h => by rw [res_emptyC]; exact WFI.empty⟩
  | @pi m A B hA hBkv hgraph hfam hcoh ihA ihfam =>
    refine ⟨fib_piC ihA.1 ⟨hBkv, hgraph, fun k f a ha => (ihfam k f a ha).1, hcoh⟩, fun k h => ?_⟩
    rw [res_piC]
    refine WFI.pi (ihA.2 k h) (isKV_res _ _) (fun n g => ?_) (fun n g a ha => ?_) (fun n g a ha n' h' => ?_)
    · rw [dat_res, El_res]; exact hgraph n _
    · rw [El_res] at ha; rw [dat_res]; exact hfam n _ a ha
    · rw [El_res] at ha; rw [dat_res, dat_res, hcoh n _ a ha n' h', Hom.comp_assoc]
  | @sigma m A B hA hBkv hgraph hfam hcoh ihA ihfam =>
    refine ⟨fib_sigmaC ihA.1 ⟨hBkv, hgraph, fun k f a ha => (ihfam k f a ha).1, hcoh⟩, fun k h => ?_⟩
    rw [res_sigmaC]
    refine WFI.sigma (ihA.2 k h) (isKV_res _ _) (fun n g => ?_) (fun n g a ha => ?_) (fun n g a ha n' h' => ?_)
    · rw [dat_res, El_res]; exact hgraph n _
    · rw [El_res] at ha; rw [dat_res]; exact hfam n _ a ha
    · rw [El_res] at ha; rw [dat_res, dat_res, hcoh n _ a ha n' h', Hom.comp_assoc]
  | @path m L a0 a1 hL ha0 ha1 ihL =>
    refine ⟨fib_pathC ihL.1 ha0 ha1, fun k h => ?_⟩
    rw [res_pathC]
    refine WFI.path (ihL.2 _ (Hom.lift h)) ?_ ?_
    · rw [El_res, TranspPi.lift_comp_endpt0]
      have := ihL.1.elRes _ _ _ ha0 _ h; exact this
    · rw [El_res, TranspPi.lift_comp_endpt1]
      have := ihL.1.elRes _ _ _ ha1 _ h; exact this
  | @ipi m L hL ihL =>
    exact ⟨fib_ipiC ihL.1, fun k h => by rw [res_ipiC]; exact WFI.ipi (ihL.2 _ (Hom.lift h))⟩
  | @univ m l' hl' =>
    rw [Ucodes_lt m hl']
    have ih := ihl l' hl'
    refine ⟨fib_univC (fun k c hc => (ih k c hc).1) (fun k c hc n h => (ih k c hc).2 n h)
      (fun k c hc n h => res_mem_Vt hc h), fun k h => ?_⟩
    rw [res_univC, ← Ucodes_lt k hl']; exact WFI.univ hl'
  | @glue m A φ Tp ep hA hφ hn hTp hep hT hTcoh he hecoh ihA ihT =>
    refine ⟨fib_glueC ihA.1 hφ hTp hep (fun k f hf => (ihT k f hf).1) hTcoh he hecoh, fun k h => ?_⟩
    rw [res_glueC hTcoh (fun k f hf => (ihT k f hf).1.kv) hφ h]
    split
    · exact hT k h ‹_›
    · rename_i hh
      refine WFI.glue (ihA.2 k h) (hφ.restr h) hh ?_ ?_ (fun n g hg => ?_) (fun n g hg n' g' => ?_)
        (fun n g hg => ?_) (fun n g hg n' g' => ?_)
      · exact res_partialKV_self hTp h
      · exact res_partialKV_self hep h
      · rw [Cof.restr_restr] at hg; rw [dat_res]; exact hT n _ hg
      · rw [Cof.restr_restr] at hg; rw [dat_res, dat_res, hTcoh n _ hg n' g', Hom.comp_assoc]
      · rw [Cof.restr_restr] at hg; rw [dat_res, dat_res, res_res]; exact he n _ hg
      · rw [Cof.restr_restr] at hg; rw [dat_res, dat_res, hecoh n _ hg n' g', Hom.comp_assoc]

/-- Well-formed codes are fibrant. -/
theorem WF.fib {l : ℕ} {c : V} (h : WF l m c) : Fib c m := (wf_props l m c h).1

/-- Well-formedness is stable under restriction. -/
theorem WF.res {l : ℕ} {c : V} (hc : WF l m c) (h : Hom k m) : WF l k (res h c) := (wf_props l m c hc).2 k h

end

end Model

namespace Model

open ZFSet KubusCore

noncomputable section

variable {k m n : ℕ}

/-- Cumulativity of well-formedness. -/
theorem WF.cumul {l : ℕ} {c : V} (h : WF l m c) : WF (l + 1) m c := by
  unfold WF at h ⊢
  induction h with
  | empty => exact WFI.empty
  | pi _ hBkv hgraph _ hcoh ihA ihfam => exact WFI.pi ihA hBkv hgraph ihfam hcoh
  | sigma _ hBkv hgraph _ hcoh ihA ihfam => exact WFI.sigma ihA hBkv hgraph ihfam hcoh
  | path _ ha0 ha1 ihL => exact WFI.path ihL ha0 ha1
  | ipi _ ihL => exact WFI.ipi ihL
  | @univ m l' hl' =>
    rw [Ucodes_lt m hl', ← Ucodes_lt (l := l + 1) m (by omega)]; exact WFI.univ (by omega)
  | glue _ hφ hn hTp hep _ hTcoh he hecoh ihA ihT => exact WFI.glue ihA hφ hn hTp hep ihT hTcoh he hecoh

/-- The universe of level `l` is a small set of level `l + 1`. -/
theorem univC_mem_Vt {l : ℕ} (hl : l < 4) : univC m l ∈ Vt (l + 1) := univC_mem_Vt' hl

theorem wf_univC {l : ℕ} : WF (l + 1) m (univC m l) := by
  unfold WF; rw [← Ucodes_lt m (Nat.lt_succ_self l)]; exact WFI.univ (Nat.lt_succ_self l)

end

end Model
