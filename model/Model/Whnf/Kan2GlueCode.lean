import Model.Whnf.Kan2Codes
import Model.Whnf.Kan2GlueTM

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-! ### Glue types -/

omit hW in
theorem face_tr {k1 : ℕ} {φ2 : I} {C : Cof k1} (hf : (ival (idEnv k1) φ2).face = C) {k2 : ℕ} (σ : ISub k2 k1) :
    (ival (idEnv k2) (φ2.subst σ.τ)).holds ↔ (C.restr σ.hom).holds := by
  rw [DM.holds_iff_face_holds, face_isub hf σ]

/-- The components of the normal forms of a type related at a restriction of a Glue code, at the
restrictions where the face does not hold. -/
theorem glueComp {m : ℕ} {A Tp : V} {φ : Cof m} (hAne : A ≠ ∅)
    (ihA : KanP2 S m A) (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KanP2 S k (dat Tp k f))
    {f : Hom k m} {T T' : Tm}
    (hloc : ∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ))
    {k1 : ℕ} (ρ1 : ISub k1 k) (hn1 : ¬ (φ.restr (f.comp ρ1.hom)).holds) {A2 : Tm} {φ2 : I} {T2 e2 : Tm}
    (hR2 : RedT S k1 (T.isub ρ1) (.glue A2 φ2 T2 e2)) :
    KCode S k1 A2 ∧ (ival (idEnv k1) φ2).face = φ.restr (f.comp ρ1.hom) ∧
      ∀ k2 (σ : ISub k2 k1), (ival (idEnv k2) (φ2.subst σ.τ)).holds → KCode S k2 (T2.isub σ) := by
  have h := hloc k1 ρ1
  unfold glueLocT at h
  rw [if_neg hn1] at h
  obtain ⟨A3, φ3, T3, e3, A3', φ3', T3', e3', r3, -, -, -, f3, -, hA3, hfib⟩ := h
  have e := RedW.unique r3.1 hR2.1
  simp only [Tm.glue.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  refine ⟨KCode.of_comp ihA hA3, f3, fun k2 σ hh => ?_⟩
  have hc : (φ.restr (f.comp (ρ1.comp σ).hom)).holds := by
    rw [← ISub.comp_hom, ← Cof.restr_restr]; exact (face_tr f3 σ).1 hh
  exact KCode.of_comp (ihT k2 _ hc) (hfib k2 σ hc).1

theorem kanP2_glueC {l m : ℕ} {A Tp ep : V} {φ : Cof m} (hAw : WF l m A) (hφ : φ.IsCof)
    (hTn : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
    (ihA : KanP2 S m A) (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KanP2 S k (dat Tp k f)) :
    KanP2 S m (glueC m A φ Tp ep) := by
  have hAne : A ≠ ∅ := IsKV.ne_empty hAw.fib.kv
  -- the normal form of a type related at a restriction where the face does not hold
  have nf : ∀ {k : ℕ} {f : Hom k m} {T T' : Tm}, (Comp2 S (glueC m A φ Tp ep) m k f).ty T T' →
      ¬ (φ.restr f).holds →
      (∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ)) ∧
      ∃ A1 φ1 T1 e1 l1, RedT S k T (.glue A1 φ1 T1 e1) ∧ HasTy S k .one [] (.glue A1 φ1 T1 e1) (.univ l1) ∧
        (ival (idEnv k) φ1).face = φ.restr f ∧ φ1.Scoped k := by
    intro k f T T' hT hh
    have hb := Comp2_ty_base hT
    rw [Comp2_glueC_at hφ hTn hTkv f, if_neg hh,
      Comp2_glueC (isKV_res _ _) (isKV_res _ _) (hφ.restr f) hh] at hT
    obtain ⟨-, hloc, -, -⟩ := hT
    have hloc' : ∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ) := fun k' σ => by
      rw [← glueLocT_res hAne]; exact hloc k' σ
    refine ⟨hloc', ?_⟩
    have h0 := hloc' k (ISub.id k)
    unfold glueLocT at h0
    rw [if_neg (by rw [ISub.hom_id, Hom.comp_id]; exact hh)] at h0
    obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', r1, -, s1, -, f1, -, -, -⟩ := h0
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at r1
    obtain ⟨l1, h1 | h1⟩ := hb.2.1.of_tyEq r1.2
    swap; · cases h1
    rw [ISub.hom_id, Hom.comp_id] at f1
    exact ⟨A1, φ1, T1, e1, l1, r1, h1, f1, s1⟩
  -- the induction hypotheses of the Glue lemmas at the normal form
  have ihs : ∀ {k : ℕ} {f : Hom k m} {T T' : Tm} {φ1 : I},
      (∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ)) →
      (ival (idEnv k) φ1).face = φ.restr f → φ1.Scoped k →
      ∀ k1 (ρ1 : ISub k1 k) (A2 : Tm) (φ2 : I) (T2 e2 : Tm), ¬ (ival (idEnv k1) (φ1.subst ρ1.τ)).holds →
        RedT S k1 (T.isub ρ1) (.glue A2 φ2 T2 e2) →
        KCode S k1 A2 ∧ ∀ k2 (σ : ISub k2 k1), (ival (idEnv k2) (φ2.subst σ.τ)).holds → KCode S k2 (T2.isub σ) := by
    intro k f T T' φ1 hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2
    have hn1' : ¬ (φ.restr (f.comp ρ1.hom)).holds := by
      rw [← Cof.restr_restr]; exact fun h => hn1 ((face_tr f1 ρ1).2 h)
    have g := glueComp hW hAne ihA ihT hloc ρ1 hn1' hR2
    exact ⟨g.1, g.2.2⟩
  refine ⟨fun k f T T' hT => ?_, fun k f T T' hT => ?_⟩
  · by_cases hh : (φ.restr f).holds
    · have hT' := hT
      rw [Comp2_glueC_at hφ hTn hTkv f, if_pos hh] at hT'
      exact (ihT k f hh).1 k (Hom.id k) T T' hT'
    have hTT := Comp2_ty_RT2 hT
    obtain ⟨hloc, A1, φ1, T1, e1, l1, hR, hG, f1, s1⟩ := nf hT hh
    exact kanH2_glue hW hTT hR hG
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 => ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).1.hrel hW).1)
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 k2 σ hh2 X X' h1 h2 =>
        ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).2 k2 σ hh2).relH hW h1 h2)
  · by_cases hh : (φ.restr f).holds
    · have hT' := hT
      rw [Comp2_glueC_at hφ hTn hTkv f, if_pos hh] at hT'
      exact (ihT (k + 1) f hh).2 k (Hom.id (k + 1)) T T' hT'
    have hTT := Comp2_ty_RT2 hT
    obtain ⟨hloc, A1, φ1, T1, e1, l1, hR, hG, f1, s1⟩ := nf hT hh
    exact kanT2_glue hW hTT hR hG
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 => (ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).1.hrel hW)
      (fun k1 ρ1 A2 φ2 T2 e2 hn1 hR2 => ⟨fun k2 σ hh2 X X' h1 h2 =>
        ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).2 k2 σ hh2).relH hW h1 h2,
        fun k2 Θ hh2 X X' h1 h2 => ((ihs hloc f1 s1 k1 ρ1 A2 φ2 T2 e2 hn1 hR2).2 (k2 + 1) Θ hh2).relT hW h1 h2⟩)


/-- A syntactic Glue code is Kan when its base and its face fibres are Kan. -/
theorem kanP2_glueT {A T e : Tm} {φ : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hAK : KanP2 S k (semK S k A))
    (hTK : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      KanP2 S k' (semK S k' (T.isub σ))) :
    KanP2 S k (semK S k (.glue A φ T e)) := by
  obtain ⟨hφ, lA, hA, -⟩ := glue_data hW hG
  have hAw : WF lA k (semK S k A) := by
    have hm := mem_of_ty hW hA
    rw [show semK S k (.univ lA) = univC k lA from rfl, El_univC] at hm
    exact (ZFSet.mem_sep.1 hm).2
  have hNat := (cond_of_sem_glue (semK_ne hW hG)).1
  have hTK' : ∀ k' (f : Hom k' k), (Cof.restr (ival (idEnv k) φ).face f).holds →
      KanP2 S k' (dat (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k))) k' f) := by
    intro k' f hf
    have hf' : (Cof.restr (ival (idEnv k) φ).face (ISub.ofHom f).hom).holds := by
      rwa [ISub.ofHom_hom]
    have ht := hTK k' (ISub.ofHom f) ((face_holds_iff hφ _).1 hf')
    rwa [← dat_glue_fiber _ hf', ISub.ofHom_hom] at ht
  rw [semK_glueT hW hG]
  refine kanP2_glueC hW hAw (isCof_ival_face _ _) ?_ ?_ hAK hTK'
  · intro k' f hf n g
    rw [dat_partialKV_holds hf, dat_partialKV_holds (by rw [← Cof.restr_restr]; exact ((isCof_ival_face _ _).restr f).holds_restr hf g)]
    have ht := hNat k' f hf n g
    simpa only [faceVals, IEnv.restr_restr, TEnv.restr_restr] using ht.symm
  · intro k' f hf
    have hf' : (Cof.restr (ival (idEnv k) φ).face (ISub.ofHom f).hom).holds := by
      rwa [ISub.ofHom_hom]
    obtain ⟨lT, hT, -⟩ := glue_fiber_ty hW hG (ISub.ofHom f) ((face_holds_iff hφ _).1 hf')
    have ht := kv_semK_of_univ hW hT
    rwa [← dat_glue_fiber _ hf', ISub.ofHom_hom] at ht


end

end Model.Whnf
