import Model.Whnf.Kripke2

/-!
# The binary relation of inductive types: restriction and change of base
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' m : ℕ}

section
variable {k0 : ℕ} {Θ : SData m} (f : Hom k0 m) {d : ℕ} {D : DataDecl}

theorem DR2.isub (hW : WfSig S) {k : ℕ} {g : Hom k k0} {A t t' : Tm}
    (h : DR2 S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t t') (σ : ISub k' k) :
    DR2 S d D (dataMem S Θ f) (dataP2 S Θ f) k' (g.comp σ.hom) (A.isub σ) (t.isub σ) (t'.isub σ) := by
  cases h with
  | intro he hh hc hc' =>
    refine .intro (EqTm.isubS hW he σ) (fun k'' σ' => ?_) (fun k'' σ' w hw k3 ρ => ?_) (fun k'' σ' w hw k3 ρ => ?_)
    · have := hh k'' (σ.comp σ')
      rwa [← ISub.comp_hom, ← Tm.isub_isub, ← Tm.isub_isub, ← Tm.isub_isub] at this
    · rw [Tm.isub_isub] at hw
      have := hc k'' (σ.comp σ') w hw k3 ρ
      simp only [Tm.isub_isub, ISub.comp_hom, ISub.comp_assoc] at this ⊢; exact this
    · rw [Tm.isub_isub] at hw
      have := hc' k'' (σ.comp σ') w hw k3 ρ
      simp only [Tm.isub_isub, ISub.comp_hom, ISub.comp_assoc] at this ⊢; exact this

theorem DR2.rebase {k : ℕ} {f' : Hom k k0} {A t t' : Tm}
    (hr : DR2 S d D (dataMem S Θ f) (dataP2 S Θ f) k f' A t t') :
    ∀ {k1 : ℕ} (h : Hom k1 k0) (g : Hom k k1), f' = h.comp g →
      DR2 S d D (dataMem S Θ (f.comp h)) (dataP2 S Θ (f.comp h)) k g A t t' := by
  refine DR2.rec (motive_1 := fun k f' A t t' _ => ∀ {k1 : ℕ} (h : Hom k1 k0) (g : Hom k k1), f' = h.comp g →
      DR2 S d D (dataMem S Θ (f.comp h)) (dataP2 S Θ (f.comp h)) k g A t t')
    (motive_2 := fun k f' A t t' _ => ∀ {k1 : ℕ} (h : Hom k1 k0) (g : Hom k k1), f' = h.comp g →
      DR2At S d D (dataMem S Θ (f.comp h)) (dataP2 S Θ (f.comp h)) k g A t t') ?_ ?_ ?_ hr
  · intro k f' A t t' he _ _ _ ih ihc ihc' k1 h g e
    exact .intro he (fun k' σ => ih k' σ h (g.comp σ.hom) (by rw [e, Hom.comp_assoc]))
      (fun k' σ w hw k'' ρ => ihc k' σ w hw k'' ρ h (g.comp (σ.comp ρ).hom) (by rw [e, Hom.comp_assoc]))
      (fun k' σ w hw k'' ρ => ihc' k' σ w hw k'' ρ h (g.comp (σ.comp ρ).hom) (by rw [e, Hom.comp_assoc]))
  · intro k f' A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec k1 h g e
    subst e
    refine .con ?_ ?_ heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      (fun j hj hj' hr => ihrec j hj hj' hr h g rfl) (fun j hj hj' hr => ?_)
    · unfold dataMem at hm ⊢; rwa [Hom.comp_assoc]
    · unfold dataMem at hm' ⊢; rwa [Hom.comp_assoc]
    · have := hpt j hj hj' hr; unfold dataP2 at this ⊢; rwa [Hom.comp_assoc]
  · intro k f' A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu iha ihu k1 h g e
    subst e
    refine .hcomp ?_ ?_ heq hH hA hpl ht ht' hs hs' h12 h21 (iha h g rfl)
      (fun k' σ r hr hh => ihu k' σ r hr hh h _ (by rw [Hom.comp_assoc]))
    · unfold dataMem at hm ⊢; rwa [Hom.comp_assoc]
    · unfold dataMem at hm' ⊢; rwa [Hom.comp_assoc]

theorem DR2.unbase {k k1 : ℕ} {h : Hom k1 k0} {g : Hom k k1} {A t t' : Tm}
    (hr : DR2 S d D (dataMem S Θ (f.comp h)) (dataP2 S Θ (f.comp h)) k g A t t') :
    DR2 S d D (dataMem S Θ f) (dataP2 S Θ f) k (h.comp g) A t t' := by
  refine DR2.rec (motive_1 := fun k g A t t' _ => DR2 S d D (dataMem S Θ f) (dataP2 S Θ f) k (h.comp g) A t t')
    (motive_2 := fun k g A t t' _ => DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k (h.comp g) A t t') ?_ ?_ ?_ hr
  · intro k g A t t' he _ _ _ ih ihc ihc'
    refine .intro he (fun k' σ => ?_) (fun k' σ w hw k'' ρ => ?_) (fun k' σ w hw k'' ρ => ?_)
    · have := ih k' σ; simp only at this; rwa [Hom.comp_assoc]
    · have := ihc k' σ w hw k'' ρ; simp only at this; rwa [Hom.comp_assoc]
    · have := ihc' k' σ w hw k'' ρ; simp only at this; rwa [Hom.comp_assoc]
  · intro k g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec
    refine .con ?_ ?_ heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' ihrec (fun j hj hj' hr => ?_)
    · unfold dataMem at hm ⊢; rwa [← Hom.comp_assoc]
    · unfold dataMem at hm' ⊢; rwa [← Hom.comp_assoc]
    · have := hpt j hj hj' hr; unfold dataP2 at this ⊢; rwa [← Hom.comp_assoc]
  · intro k g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu iha ihu
    refine .hcomp ?_ ?_ heq hH hA hpl ht ht' hs hs' h12 h21 iha (fun k' σ r hr hh => ?_)
    · unfold dataMem at hm ⊢; rwa [← Hom.comp_assoc]
    · unfold dataMem at hm' ⊢; rwa [← Hom.comp_assoc]
    · have := ihu k' σ r hr hh; simp only at this; rwa [Hom.comp_assoc]

end

theorem dataP2_base {k0 : ℕ} {Θ : SData m} (f : Hom k0 m) {k1 : ℕ} (h : Hom k1 k0) (g : Hom k k1) {c j : ℕ}
    {pre : List V} {A a a' : Tm} :
    dataP2 S Θ (f.comp h) k g c j pre A a a' ↔ dataP2 S Θ f k (h.comp g) c j pre A a a' := by
  unfold dataP2; rw [Hom.comp_assoc]

variable (hW : WfSig S)
include hW

omit hW in
/-- The argument clause of an inductive type, at a restriction, relative to the restricted base. -/
theorem argRel2_base {Θ : SData m} {k k'' : ℕ} (f : Hom k m) {k' : ℕ} (σ : ISub k' k) {σ' : ISub k'' k'}
    {ps ps' : Tm} (h : argRel2 S Θ f k'' (σ.comp σ') ps ps') : argRel2 S Θ (f.comp σ.hom) k'' σ' ps ps' := by
  intro k3 σ3 c C args args' hC hl hl' hr hrec hpt
  have := h k3 σ3 c C args args' hC hl hl' hr
    (fun j hj hj' hrj => by
      have := DR2.unbase f (hrec j hj hj' hrj)
      rwa [← ISub.hom_comp, ← ISub.comp_assoc] at this)
    (fun j hj hj' hrj => by
      have := (dataP2_base f σ.hom (σ'.comp σ3).hom).1 (hpt j hj hj' hrj)
      rwa [← ISub.hom_comp, ← ISub.comp_assoc] at this)
  rw [ISub.comp_hom, ← ISub.comp_assoc]; exact this

omit hW in
theorem parEntry_base {Θ : SData m} {k k'' : ℕ} (f : Hom k m) {k' : ℕ} (σ : ISub k' k) (σ' : ISub k'' k') (j : ℕ) :
    parEntry Θ (f.comp σ.hom) k'' σ' j = parEntry Θ f k'' (σ.comp σ') j := by
  simp only [parEntry, ISub.hom_comp, Hom.comp_assoc]

omit hW in
/-- The parameter clause of an inductive type, at a restriction, relative to the restricted base. -/
theorem parRel2_base {Θ : SData m} {k k'' : ℕ} (f : Hom k m) {k' : ℕ} (σ : ISub k' k) {σ' : ISub k'' k'}
    {ps ps' : Tm} (h : parRel2 S Θ f k'' (σ.comp σ') ps ps') : parRel2 S Θ (f.comp σ.hom) k'' σ' ps ps' := by
  unfold parRel2 at h ⊢
  rw [show (f.comp σ.hom) = f.comp σ.hom from rfl]
  simp only [parEntry_base f σ σ']
  exact h

theorem kr2_dataC {Θ : SData m} (hX : Fib (dataC Θ) m) : KR2 S m (dataC Θ) := by
  intro k f k' σ T T' t t'
  rw [Comp2_dataC, Comp2_dataC]
  constructor
  · rintro ⟨hb, hall⟩
    refine ⟨?_, fun k'' σ' => ?_⟩
    · have := base_isub hW hb σ; rwa [res_res] at this
    · obtain ⟨ps, ps', h1, h2, hpl, hpl', hcl, hcl', hcd, hcd', hpr⟩ := hall k'' (σ.comp σ')
      exact ⟨ps, ps', by rw [Tm.isub_isub]; exact h1, by rw [Tm.isub_isub]; exact h2, hpl, hpl',
        argRel2_base f σ hcl, argRel2_base f σ hcl', argRel2_base f σ hcd, argRel2_base f σ hcd',
        parRel2_base f σ hpr⟩
  · rintro ⟨he, hmem, -, hdr⟩
    refine ⟨he.isub hW σ, mem_isub hW hX he.1 hmem σ, he.isub hW σ, ?_⟩
    have := DR2.rebase f (DR2.isub f hW hdr σ) σ.hom (Hom.id k') (by rw [Hom.id_comp, Hom.comp_id])
    exact this

/-- The binary relations are Kripke, for every well-formed code. -/
theorem kr2_wf : ∀ l, l ≤ maxLevel → ∀ m X, WF l m X → KR2 S m X := by
  intro l hl
  refine code_ind _ (fun m => kr2_emptyC hW) ?_ ?_ ?_ ?_ ?_ ?_ ?_ l hl
  · intro l m A B hA hB hBf hBw hBn _ _
    exact kr2_piC hW (WF.fib (show WF l m (piC m A B) from WFI.pi hA hB hBf hBw hBn)) (IsKV.ne_empty hA.fib.kv)
  · intro l m A B hA hB hBf hBw hBn _ _
    exact kr2_sigmaC hW (WF.fib (show WF l m (sigmaC m A B) from WFI.sigma hA hB hBf hBw hBn))
      (IsKV.ne_empty hA.fib.kv)
  · intro l m L a0 a1 hL h0 h1 _
    exact kr2_pathC hW (WF.fib (show WF l m (pathC m L a0 a1) from WFI.path hL h0 h1)) (IsKV.ne_empty hL.fib.kv)
  · intro l m L hL _
    exact kr2_ipiC hW (WF.fib (show WF l m (ipiC m L) from WFI.ipi hL)) (IsKV.ne_empty hL.fib.kv)
  · intro m l _ ih; exact kr2_univC hW ih
  · intro l m A φ Tp ep hl hA hφ hn hTp hep hTw hTn hem hen _ ihT
    exact kr2_glueC hW hA.fib.kv hφ hTn hTw
      (WF.fib (show WF l m (glueC m A φ Tp ep) from WFI.glue hA hφ hn hTp hep hTw hTn hem hen)) ihT
  · intro l m Θ hc hw hpw _ _
    exact kr2_dataC hW (WF.fib (show WF l m (dataC Θ) from WFI.data Θ hc hw hpw))

theorem kr2_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : KR2 S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact kr2_wf hW l hl m X hX
  · exact kr2_univC hW fun m' X hX => kr2_wf hW l hl m' X hX

end

end Model.Whnf
