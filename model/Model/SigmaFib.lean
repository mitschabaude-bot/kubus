import Model.Sigma

/-!
# Σ-types are fibrant
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

theorem El_eq_res_id (c : V) (x : Hom n k) : El c x = El (res x c) (Hom.id n) := by
  rw [El_res, Hom.comp_id]

section hcomp

variable {A B : V} (hA : Fib A m) (hB : FamOK A B m) {f : Hom k m} {φ : Cof k} (hφ : φ.IsCof)
  {u : Tube k} {u0 : V} (hu0 : u0 ∈ El (sigmaC m A B) f) (hu : TubeOK (sigmaC m A B) f φ u u0)

include hA hB hu0 hu in
theorem hcompAt_sigmaC :
    hcompAt (sigmaC m A B) f φ u u0 = hcompSigmaF k (res f A) (res f B) φ (Tube.canon φ u) u0 := by
  rw [hcompAt, hcG_sigmaC, sigmaHc, apZ_hcGraph]
  · intro n h r hh
    have := hu.mem n h r hh
    rwa [El_sigmaC, ← res_res, ← res_res] at this
  · rw [El_sigmaC] at hu0; rwa [res_id (isKV_res _ _), res_id (isKV_res _ _)]

theorem hcompSigmaF_eq (u' : Tube k) :
    hcompSigmaF k (res f A) (res f B) φ u' u0 =
      pairV k (hcompAt A f φ u'.fst (fstV k u0))
        (compF (apZ (dat B (k + 1) (f.comp (Hom.wk k))) (hfillF A f φ u'.fst (fstV k u0)))
          (Hom.id (k + 1)) φ u'.snd (sndV k u0)) := by
  rw [hcompSigmaF, hcompAt_res_id', hfillF_res_id, dat_res]

include hA hB hφ hu0 hu in
theorem fstTube_ok : TubeOK A f φ (Tube.canon φ u).fst (fstV k u0) where
  mem n h r hh := ((sigma_eta hA hB ((hu.canon hφ).mem n h r hh)).2.1)
  coh n h r hh n' g := by
    simp only [Tube.fst]
    rw [← sigma_fst_res hA hB ((hu.canon hφ).mem n h r hh), (hu.canon hφ).coh n h r hh n' g]
  base n h hh := by
    simp only [Tube.fst]; rw [(hu.canon hφ).base n h hh, sigma_fst_res hA hB hu0]

/-- The filler of the first components. -/
abbrev fl (A : V) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) : V :=
  hfillF A f φ (Tube.canon φ u).fst (fstV k u0)

/-- The line of the second components. -/
abbrev Bl (A B : V) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) : V :=
  apZ (dat B (k + 1) (f.comp (Hom.wk k))) (fl A f φ u u0)

include hA hB hφ hu0 hu in
theorem fl_mem : fl A f φ u u0 ∈ El A (f.comp (Hom.wk k)) :=
  hfillF_mem hA hφ (sigma_eta hA hB hu0).2.1 (fstTube_ok hA hB hφ hu0 hu)

include hA hB hφ hu0 hu in
theorem fib_Bl : Fib (Bl A B f φ u u0) (k + 1) := hB.fib _ _ _ (fl_mem hA hB hφ hu0 hu)

include hA hB hφ hu0 hu in
theorem res_Bl (x : Hom n (k + 1)) :
    res x (Bl A B f φ u u0) = apZ (dat B n ((f.comp (Hom.wk k)).comp x)) (res x (fl A f φ u u0)) :=
  hB.coh _ _ _ (fl_mem hA hB hφ hu0 hu) _ x

include hA hB hφ hu0 hu in
theorem El_Bl (x : Hom n (k + 1)) :
    El (Bl A B f φ u u0) x = El (apZ (dat B n ((f.comp (Hom.wk k)).comp x)) (res x (fl A f φ u u0))) (Hom.id n) := by
  rw [El_eq_res_id, res_Bl hA hB hφ hu0 hu]

include hA hB hφ hu0 hu in
theorem sndTube_ok : LineTubeOK (Bl A B f φ u u0) (Hom.id (k + 1)) φ (Tube.canon φ u).snd (sndV k u0) where
  mem n h r hh := by
    rw [Hom.id_comp, El_Bl hA hB hφ hu0 hu, hfillF_face hA hφ (sigma_eta hA hB hu0).2.1
      (fstTube_ok hA hB hφ hu0 hu) h hh r, Hom.comp_assoc, Hom.wk_comp_snoc]
    exact (sigma_eta hA hB ((hu.canon hφ).mem n h r hh)).2.2
  coh n h r hh n' g := by
    simp only [Tube.snd]
    rw [← sigma_snd_res hA hB ((hu.canon hφ).mem n h r hh), (hu.canon hφ).coh n h r hh n' g]
  base n h hh := by
    simp only [Tube.snd]; rw [(hu.canon hφ).base n h hh, sigma_snd_res hA hB hu0]

include hA hB hφ hu0 hu in
theorem snd_base_mem :
    sndV k u0 ∈ El (Bl A B f φ u u0) ((Hom.id (k + 1)).comp (Hom.endpt k (DM.zero k))) := by
  rw [Hom.id_comp, El_Bl hA hB hφ hu0 hu, hfillF_endpt0 hA hφ (sigma_eta hA hB hu0).2.1
    (fstTube_ok hA hB hφ hu0 hu), Hom.comp_assoc, Hom.wk_comp_endpt, Hom.comp_id]
  exact (sigma_eta hA hB hu0).2.2

include hA hB hφ hu0 hu in
theorem hcompSigmaF_mem :
    hcompSigmaF k (res f A) (res f B) φ (Tube.canon φ u) u0 ∈ El (sigmaC m A B) f := by
  rw [hcompSigmaF_eq, mem_sigmaC hA hB]
  have h1 := fstTube_ok hA hB hφ hu0 hu
  have h0 := (sigma_eta hA hB hu0).2.1
  refine ⟨_, hA.hcMem _ _ _ _ _ hφ h0 h1, _, ?_, rfl⟩
  have := compF_mem (fib_Bl hA hB hφ hu0 hu) hφ (snd_base_mem hA hB hφ hu0 hu) (sndTube_ok hA hB hφ hu0 hu)
  rwa [Hom.id_comp, El_Bl hA hB hφ hu0 hu, hfillF_endpt1 hA hφ h0 h1, Hom.comp_assoc,
    Hom.wk_comp_endpt, Hom.comp_id] at this

include hA hB hφ hu0 hu in
theorem hcompSigmaF_face (hh : φ.holds) :
    hcompSigmaF k (res f A) (res f B) φ (Tube.canon φ u) u0 = u k (Hom.id k) (DM.one k) := by
  have hid : (φ.restr (Hom.id k)).holds := by rw [hφ.restr_id]; exact hh
  have h1 := fstTube_ok hA hB hφ hu0 hu
  have h0 := (sigma_eta hA hB hu0).2.1
  rw [hcompSigmaF_eq, hA.hcFace _ _ _ _ _ hφ h0 h1 hh, compF_face (fib_Bl hA hB hφ hu0 hu) hφ
    (snd_base_mem hA hB hφ hu0 hu) (sndTube_ok hA hB hφ hu0 hu) hh]
  simp only [Tube.fst, Tube.snd, tube_canon_eq hid]
  have := hu.mem k (Hom.id k) (DM.one k) hid
  rw [Hom.comp_id] at this
  exact (sigma_eta hA hB this).1.symm

include hA hB hφ hu0 hu in
theorem hcompSigmaF_res (h : Hom n k) :
    res h (hcompSigmaF k (res f A) (res f B) φ (Tube.canon φ u) u0) =
      hcompSigmaF n (res (f.comp h) A) (res (f.comp h) B) (φ.restr h)
        (Tube.canon (φ.restr h) (u.restr h)) (res h u0) := by
  have h1 := fstTube_ok hA hB hφ hu0 hu
  have h0 := (sigma_eta hA hB hu0).2.1
  have hagree : ∀ n' (g : Hom n' n) r, ((φ.restr h).restr g).holds →
      (Tube.canon φ u).restr h n' g r = Tube.canon (φ.restr h) (u.restr h) n' g r := by
    intro n' g r hg
    have hg' : (φ.restr (h.comp g)).holds := by rwa [Cof.restr_restr] at hg
    simp only [Tube.restr, tube_canon_eq hg', tube_canon_eq hg]
  rw [hcompSigmaF_eq, hcompSigmaF_eq, res_pairV]
  congr 1
  · rw [hA.hcRes _ _ _ _ _ hφ h0 h1 n h, sigma_fst_res hA hB hu0]
    apply hcompAt_congr; intro n' g r hg
    exact congrArg (fstV n') (hagree n' g r hg)
  · rw [compF_res (fib_Bl hA hB hφ hu0 hu) hφ (snd_base_mem hA hB hφ hu0 hu) (sndTube_ok hA hB hφ hu0 hu) h,
      Hom.id_comp, ← compF_res_id, res_Bl hA hB hφ hu0 hu, hfillF_natural hA hφ h0 h1,
      Hom.comp_assoc, Hom.wk_comp_lift, ← Hom.comp_assoc, sigma_snd_res hA hB hu0,
      sigma_fst_res hA hB hu0]
    rw [hfillF_congr (u' := (Tube.canon (φ.restr h) (u.restr h)).fst)]
    · apply compF_congr; intro n' g r hg
      exact congrArg (sndV n') (hagree n' g r hg)
    · intro n' g r hg
      exact congrArg (fstV n') (hagree n' g r hg)

end hcomp

end

end Model

/-! ### Transport -/

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

section transp

variable {A B : V} (hA : Fib A m) (hB : FamOK A B m) {f : Hom (n + 1) m} {φ : Cof n} (hφ : φ.IsCof)
  (hc : ConstOn (sigmaC m A B) f φ) {u0 : V} (hu0 : u0 ∈ El (sigmaC m A B) (f.comp (Hom.endpt n (DM.zero n))))

include hA hB hu0 in
theorem transpAt_sigmaC : transpAt (sigmaC m A B) f φ u0 = transpSigmaF n (res f A) (res f B) φ u0 := by
  rw [transpAt, trG_sigmaC]
  show apZ (trGraph n _ _) _ = _
  rw [apZ_trGraph]
  rw [El_sigmaC] at hu0; rwa [res_res, res_res]

theorem transpSigmaF_eq :
    transpSigmaF n (res f A) (res f B) φ u0 =
      pairV n (transpAt A f φ (fstV n u0))
        (transpAt (apZ (dat B (n + 1) f) (transpFillF A f φ (fstV n u0))) (Hom.id (n + 1)) φ (sndV n u0)) := by
  rw [transpSigmaF, transpAt_res_id', transpFillF_res_id, dat_res, Hom.comp_id]

include hA hB hc in
theorem sigma_constAB (h : Hom n' n) (hh : (φ.restr h).holds) (r : DM n') :
    res (f.comp (Hom.snoc h r)) A = res (f.comp (Hom.snoc h (DM.zero n'))) A ∧
    res (f.comp (Hom.snoc h r)) B = res (f.comp (Hom.snoc h (DM.zero n'))) B := by
  have := hc n' h hh r
  rw [res_sigmaC, res_sigmaC] at this
  exact sigmaC_inj (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) (isKV_res _ _) this

include hA hB hc in
theorem sigma_constA : ConstOn A f φ := fun n' h hh r => (sigma_constAB hA hB hc h hh r).1

/-- The transport filler of the first component. -/
abbrev tfa (A : V) (f : Hom (n + 1) m) (φ : Cof n) (u0 : V) : V := transpFillF A f φ (fstV n u0)

/-- The line of the second components. -/
abbrev Bt (A B : V) (f : Hom (n + 1) m) (φ : Cof n) (u0 : V) : V := apZ (dat B (n + 1) f) (tfa A f φ u0)

include hA hB hφ hc hu0 in
theorem tfa_mem : tfa A f φ u0 ∈ El A f :=
  transpFillF_mem hA hφ (sigma_constA hA hB hc) (sigma_eta hA hB hu0).2.1

include hA hB hφ hc hu0 in
theorem res_Bt (x : Hom n' (n + 1)) :
    res x (Bt A B f φ u0) = apZ (dat B n' (f.comp x)) (res x (tfa A f φ u0)) :=
  hB.coh _ _ _ (tfa_mem hA hB hφ hc hu0) _ x

include hA hB hφ hc hu0 in
theorem fib_Bt : Fib (Bt A B f φ u0) (n + 1) := hB.fib _ _ _ (tfa_mem hA hB hφ hc hu0)

include hA hB hφ hc hu0 in
theorem constOn_Bt : ConstOn (Bt A B f φ u0) (Hom.id (n + 1)) φ := by
  intro n' h hh r
  have hfa := sigma_eta hA hB hu0
  rw [Hom.id_comp, Hom.id_comp, res_Bt hA hB hφ hc hu0, res_Bt hA hB hφ hc hu0,
    transpFillF_face hA hφ (sigma_constA hA hB hc) hfa.2.1 h hh r,
    transpFillF_face hA hφ (sigma_constA hA hB hc) hfa.2.1 h hh (DM.zero n')]
  have := congrArg (fun X => dat X n' (Hom.id n')) (sigma_constAB hA hB hc h hh r).2
  simp only [dat_res, Hom.comp_id] at this
  rw [this]

include hA hB hφ hc hu0 in
theorem base_Bt : sndV n u0 ∈ El (Bt A B f φ u0) ((Hom.id (n + 1)).comp (Hom.endpt n (DM.zero n))) := by
  have hfa := sigma_eta hA hB hu0
  rw [Hom.id_comp, El_eq_res_id, res_Bt hA hB hφ hc hu0,
    transpFillF_endpt0 hA hφ (sigma_constA hA hB hc) hfa.2.1]
  exact hfa.2.2

include hA hB hφ hc hu0 in
theorem transpSigmaF_mem :
    transpSigmaF n (res f A) (res f B) φ u0 ∈ El (sigmaC m A B) (f.comp (Hom.endpt n (DM.one n))) := by
  have hfa := sigma_eta hA hB hu0
  rw [transpSigmaF_eq, mem_sigmaC hA hB]
  refine ⟨_, hA.trMem n f φ _ hφ (sigma_constA hA hB hc) hfa.2.1, _, ?_, rfl⟩
  have := (fib_Bt hA hB hφ hc hu0).trMem n (Hom.id _) φ _ hφ (constOn_Bt hA hB hφ hc hu0)
    (base_Bt hA hB hφ hc hu0)
  rwa [Hom.id_comp, El_eq_res_id, res_Bt hA hB hφ hc hu0,
    transpFillF_endpt1 hA hφ (sigma_constA hA hB hc) hfa.2.1] at this

include hA hB hφ hc hu0 in
theorem transpSigmaF_face (hh : φ.holds) : transpSigmaF n (res f A) (res f B) φ u0 = u0 := by
  have hfa := sigma_eta hA hB hu0
  rw [transpSigmaF_eq, hA.trFace n f φ _ hφ (sigma_constA hA hB hc) hfa.2.1 hh,
    (fib_Bt hA hB hφ hc hu0).trFace n (Hom.id _) φ _ hφ (constOn_Bt hA hB hφ hc hu0)
      (base_Bt hA hB hφ hc hu0) hh]
  exact hfa.1.symm

include hA hB hφ hc hu0 in
theorem transpSigmaF_res (h : Hom n' n) :
    res h (transpSigmaF n (res f A) (res f B) φ u0) =
      transpSigmaF n' (res (f.comp (Hom.lift h)) A) (res (f.comp (Hom.lift h)) B) (φ.restr h) (res h u0) := by
  have hfa := sigma_eta hA hB hu0
  rw [transpSigmaF_eq, transpSigmaF_eq, res_pairV,
    hA.trRes n f φ _ hφ (sigma_constA hA hB hc) hfa.2.1 n' h,
    (fib_Bt hA hB hφ hc hu0).trRes n (Hom.id _) φ _ hφ (constOn_Bt hA hB hφ hc hu0)
      (base_Bt hA hB hφ hc hu0) n' h,
    Hom.id_comp, transpAt_eq_res_id (Bt A B f φ u0) (Hom.lift h), res_Bt hA hB hφ hc hu0,
    transpFillF_natural hA hφ (sigma_constA hA hB hc) hfa.2.1, sigma_fst_res hA hB hu0,
    sigma_snd_res hA hB hu0]

end transp

/-- **Σ-types are fibrant**, with the spec's `hcompSigma` and `transpSigma`. -/
theorem fib_sigmaC {A B : V} (hA : Fib A m) (hB : FamOK A B m) : Fib (sigmaC m A B) m where
  kv := isKV_mkKV _
  elKV k f v hv := sigma_elKV hA hB hv
  elRes k f v hv n h := sigma_elRes hA hB hv h
  hcMem k f φ u u0 hφ hu0 hu := by
    rw [hcompAt_sigmaC hA hB hu0 hu]; exact hcompSigmaF_mem hA hB hφ hu0 hu
  hcFace k f φ u u0 hφ hu0 hu hh := by
    rw [hcompAt_sigmaC hA hB hu0 hu]; exact hcompSigmaF_face hA hB hφ hu0 hu hh
  hcRes k f φ u u0 hφ hu0 hu n h := by
    rw [hcompAt_sigmaC hA hB hu0 hu, hcompAt_sigmaC hA hB (sigma_elRes hA hB hu0 h) (hu.restr h),
      hcompSigmaF_res hA hB hφ hu0 hu h]
  trMem n f φ a0 hφ hc ha := by
    rw [transpAt_sigmaC hA hB ha]; exact transpSigmaF_mem hA hB hφ hc ha
  trFace n f φ a0 hφ hc ha hh := by
    rw [transpAt_sigmaC hA hB ha]; exact transpSigmaF_face hA hB hφ hc ha hh
  trRes n f φ a0 hφ hc ha n' h := by
    have ha' : res h a0 ∈ El (sigmaC m A B) ((f.comp (Hom.lift h)).comp (Hom.endpt n' (DM.zero n'))) := by
      have := sigma_elRes hA hB ha h
      rw [Hom.comp_assoc, TranspPi.lift_comp_endpt0, ← Hom.comp_assoc]; exact this
    rw [transpAt_sigmaC hA hB ha, transpAt_sigmaC hA hB ha', transpSigmaF_res hA hB hφ hc ha h]

end

end Model
