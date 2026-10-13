import Model.Rules.CompLemmas

/-!
# Helpers for the Glue rules
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

/-! ### Equivalences -/

theorem equiv_eq_subst (T A : Tm) :
    Tm.equiv T A = (Tm.equiv (.var 1) (.var 0)).subst (fun | 0 => A | 1 => T | n + 2 => .var n) .var := by
  simp only [Tm.equiv, Tm.isEquiv, Tm.isContr, Tm.fiber, Tm.arrow, Tm.pathC, Tm.subst, Tm.shift, Tm.dshift,
    Tm.ren, Tm.up, Tm.ren_ren]
  simp [Tm.upRen, Tm.ren_ren, Tm.ren]

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

theorem sem_equiv {T A : Tm} {ρ : IEnv m} {γ : ℕ → V} (hT : Natural S T m ρ γ) (hA : Natural S A m ρ γ) :
    sem S (Tm.equiv T A) m ρ γ = equivCode m (sem S T m ρ γ) (sem S A m ρ γ) := by
  have hσ : ∀ x, Natural S ((fun | 0 => A | 1 => T | n + 2 => .var n : ℕ → Tm) x) m ρ γ := by
    intro x; rcases x with _ | _ | x
    · exact hA
    · exact hT
    · exact natural_var S x _ _
  rw [equiv_eq_subst, sem_subst S _ m ρ γ _ _ hσ]
  have e1 : (fun x => sem S ((fun | 0 => A | 1 => T | n + 2 => .var n : ℕ → Tm) x) m ρ γ) =
      TEnv.cons (TEnv.cons γ (sem S T m ρ γ)) (sem S A m ρ γ) := by
    funext x; rcases x with _ | _ | x <;> rfl
  rw [e1]
  unfold equivCode
  rw [show (fun i => ival ρ (I.var i)) = ρ from rfl]
  show interp (cstFn S) univC TyCode _ m ρ _ = _
  rw [interp_congr_pure (cstFn S) (fun _ _ => ∅) univC (fun _ _ => ∅) TyCode (fun _ _ => True) _ (by decide)]
  refine interp_congr_closed _ _ _ _ 2 0 (by decide) m _ _ _ _ (by simp) ?_
  intro x hx
  rcases x with _ | _ | x
  · rfl
  · rfl
  · omega

/-! ### Glue types -/

theorem SemWf.cof {Ψ : ℕ} {Φ : I} {Γ : Ctx} (h : SemWf S Ψ Φ Γ) (φ : I) : SemWf S Ψ (cof Φ φ) Γ :=
  ⟨trivial, h.2.1, fun m ρ γ hp => h.2.2 m ρ γ (isPoint_cof_iff.1 hp).1⟩

/-- The values of a term at the points of the face `φ` below `(ρ, γ)`. -/
def faceVals (S : Sig) (t : Tm) (ρ : IEnv m) (γ : ℕ → V) : (k : ℕ) → Hom k m → V :=
  fun k f => sem S t k (ρ.restr f) (TEnv.restr γ f)

/-- `t` is natural at the points of the face `φ` below `(ρ, γ)`. -/
def FaceNat (S : Sig) (t : Tm) (φ : I) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop :=
  ∀ k (f : Hom k m), (Cof.restr (ival ρ φ).face f).holds → ∀ n (g : Hom n k),
    sem S t n ((ρ.restr f).restr g) (TEnv.restr (TEnv.restr γ f) g) = res g (sem S t k (ρ.restr f) (TEnv.restr γ f))

theorem sem_glue {A T e : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hT : FaceNat S T φ m ρ γ) (he : FaceNat S e φ m ρ γ) :
    sem S (.glue A φ T e) m ρ γ = glueC m (sem S A m ρ γ) (ival ρ φ).face
      (partialKV m (ival ρ φ).face (faceVals S T ρ γ)) (partialKV m (ival ρ φ).face (faceVals S e ρ γ)) := by
  simp only [sem, interp]; exact if_pos fun k f hf n g => ⟨hT k f hf n g, he k f hf n g⟩

theorem cond_of_sem_glue {A T e : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (h : sem S (.glue A φ T e) m ρ γ ≠ ∅) : FaceNat S T φ m ρ γ ∧ FaceNat S e φ m ρ γ := by
  simp only [sem, interp] at h; split at h
  · rename_i hc; exact ⟨fun k f hf n g => (hc k f hf n g).1, fun k f hf n g => (hc k f hf n g).2⟩
  · exact absurd rfl h

/-- The face values of a natural term on a face that holds. -/
theorem faceVals_holds {t : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
    (hh : (ival ρ φ).holds) (ht : FaceNat S t φ m ρ γ) (k : ℕ) (f : Hom k m) :
    faceVals S t ρ γ k f = res f (sem S t m ρ γ) := by
  have hid : (Cof.restr (ival ρ φ).face (Hom.id m)).holds := by
    rw [(isCof_ival_face ρ φ).restr_id]; exact (DM.holds_iff_face_holds _).1 hh
  have := ht m (Hom.id m) hid k f
  simp only [IEnv.restr_id, TEnv.restr_id_of_kv hγ] at this
  exact this

theorem FaceNat.natural_of_holds {t : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
    (hh : (ival ρ φ).holds) (ht : FaceNat S t φ m ρ γ) : Natural S t m ρ γ := by
  intro k f; exact faceVals_holds hγ hh ht k f

/-- The Glue type at a point where its face holds. -/
theorem sem_glue_holds {A T e : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
    (hh : (ival ρ φ).holds) (hT : FaceNat S T φ m ρ γ) (he : FaceNat S e φ m ρ γ)
    (hkv : IsKV m (sem S T m ρ γ)) : sem S (.glue A φ T e) m ρ γ = sem S T m ρ γ := by
  have hhf : Cof.holds (ival ρ φ).face := (DM.holds_iff_face_holds _).1 hh
  have hid : (Cof.restr (ival ρ φ).face (Hom.id m)).holds := by
    rw [(isCof_ival_face ρ φ).restr_id]; exact hhf
  have e1 : dat (partialKV m (ival ρ φ).face (faceVals S T ρ γ)) m (Hom.id m) = sem S T m ρ γ := by
    rw [dat_partialKV, if_pos hid, faceVals, IEnv.restr_id, TEnv.restr_id_of_kv hγ]
  rw [sem_glue hT he, glueC_holds (isCof_ival_face ρ φ) hhf, e1]
  · intro k f hf; rw [e1, dat_partialKV, if_pos hf]; exact faceVals_holds hγ hh hT k f
  · rw [e1]; exact hkv

theorem FaceNat.kv_of_holds {t : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
    (hh : (ival ρ φ).holds) (ht : FaceNat S t φ m ρ γ) : IsKV m (sem S t m ρ γ) := by
  have := ht.natural_of_holds hγ hh m (Hom.id m)
  rw [IEnv.restr_id, TEnv.restr_id_of_kv hγ] at this
  rw [this]; exact isKV_res _ _

theorem FaceNat.restr {t : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (ht : FaceNat S t φ m ρ γ) (g : Hom k m) :
    FaceNat S t φ k (ρ.restr g) (TEnv.restr γ g) := by
  intro n f hf n' h
  rw [face_ival_restr, Cof.restr_restr] at hf
  have := ht n (g.comp f) hf n' h
  simp only [IEnv.restr_restr, TEnv.restr_restr] at this ⊢
  exact this

theorem faceVals_restr (t : Tm) (ρ : IEnv m) (γ : ℕ → V) (g : Hom k m) (n : ℕ) (h : Hom n k) :
    faceVals S t (ρ.restr g) (TEnv.restr γ g) n h = faceVals S t ρ γ n (g.comp h) := by
  simp only [faceVals, IEnv.restr_restr, TEnv.restr_restr]

/-- Coherence of face values. -/
theorem FaceNat.coh {t : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (ht : FaceNat S t φ m ρ γ)
    (k : ℕ) (f : Hom k m) (hf : (Cof.restr (ival ρ φ).face f).holds) (n : ℕ) (h : Hom n k) :
    res h (dat (partialKV m (ival ρ φ).face (faceVals S t ρ γ)) k f) =
      dat (partialKV m (ival ρ φ).face (faceVals S t ρ γ)) n (f.comp h) := by
  have hf' : (Cof.restr (ival ρ φ).face (f.comp h)).holds := by
    rw [← Cof.restr_restr]; exact ((isCof_ival_face ρ φ).restr f).holds_restr hf h
  rw [dat_partialKV, dat_partialKV, if_pos hf, if_pos hf', faceVals, faceVals, ← ht k f hf n h,
    IEnv.restr_restr, TEnv.restr_restr]

theorem FaceNat.kv {t : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (ht : FaceNat S t φ m ρ γ)
    (k : ℕ) (f : Hom k m) (hf : (Cof.restr (ival ρ φ).face f).holds) :
    IsKV k (dat (partialKV m (ival ρ φ).face (faceVals S t ρ γ)) k f) := by
  have := ht k f hf k (Hom.id k)
  rw [IEnv.restr_id, TEnv.restr_id_of_kv (γ := TEnv.restr γ f) (fun x => isKV_res _ _)] at this
  rw [dat_partialKV, if_pos hf, faceVals, this]; exact isKV_res _ _

theorem natural_glue {A T e : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hγ : ∀ x, IsKV m (γ x))
    (hT : FaceNat S T φ m ρ γ) (he : FaceNat S e φ m ρ γ) (hA : Natural S A m ρ γ) :
    Natural S (.glue A φ T e) m ρ γ := by
  intro k g
  rw [sem_glue (hT.restr g) (he.restr g), sem_glue hT he,
    res_glueC (hT.coh) (hT.kv) (isCof_ival_face ρ φ) g, hA k g]
  split
  · rename_i hg
    have hg' : (ival (ρ.restr g) φ).holds := by
      rw [DM.holds_iff_face_holds, face_ival_restr]; exact hg
    have hid : (Cof.restr (ival (ρ.restr g) φ).face (Hom.id k)).holds := by
      rw [(isCof_ival_face _ φ).restr_id]; exact (DM.holds_iff_face_holds _).1 hg'
    rw [glueC_holds (isCof_ival_face _ φ) ((DM.holds_iff_face_holds _).1 hg')
      (fun n f hf => by rw [(hT.restr g).coh k (Hom.id k) hid n f, Hom.id_comp])
      ((hT.restr g).kv k (Hom.id k) hid), dat_partialKV, dat_partialKV, if_pos hid, if_pos hg,
      faceVals_restr, Hom.comp_id]
  · rw [face_ival_restr]
    congr 1
    · simp only [partialKV, res_mkKV, Cof.restr_restr, faceVals_restr]
    · simp only [partialKV, res_mkKV, Cof.restr_restr, faceVals_restr]

/-! ### Smallness of elements -/

theorem below_of_mem_π1 {v z : V} (h : v ∈ π1 z) : Below v z := by
  by_cases hz : ∃ a b, z = ZFSet.pair a b
  · obtain ⟨a, b, rfl⟩ := hz
    rw [π1_pair] at h; exact (Below.of_mem h).trans (below_pair_left _ _)
  · simp only [π1, dif_neg hz] at h; exact absurd h (ZFSet.notMem_empty _)

theorem below_π2 {z : V} (hz : π2 z ≠ ∅) : Below (π2 z) z := by
  by_cases h : ∃ a b, z = ZFSet.pair a b
  · obtain ⟨a, b, rfl⟩ := h; rw [π2_pair]; exact below_pair_right _ _
  · simp only [π2, dif_neg h] at hz; exact absurd rfl hz

theorem below_of_mem_El {c v : V} (hc : IsKV m c) (f : Hom k m) (hv : v ∈ El c f) : Below v c := by
  have h1 : Below v (π2 (dat c k f)) := below_of_mem_π1 hv
  have hne : π2 (dat c k f) ≠ ∅ := by
    intro h; rw [h] at h1
    have : π1 (∅ : V) = ∅ := by simp only [π1]; rw [dif_neg ne_pair_empty]
    simp only [El, h, this] at hv; exact ZFSet.notMem_empty _ hv
  exact (h1.trans (below_π2 hne)).trans (below_dat hc f)

theorem mem_Vt_of_mem_El {l : ℕ} {c v : V} (hc : c ∈ Vt l) (hkv : IsKV m c) (f : Hom k m)
    (hv : v ∈ El c f) : v ∈ Vt l :=
  Vt_below (below_of_mem_El hkv f hv) hc

/-- Equivalence codes of small codes are small. TODO (closure plumbing for `Vt`). -/
theorem equivCode_mem_Vt {l : ℕ} {T A : V} (hT : T ∈ Vt l) (hA : A ∈ Vt l) : equivCode m T A ∈ Vt l := by
  sorry

/-- Glue codes of small components are small. TODO (closure plumbing for `Vt`). -/
theorem glueC_mem_Vt {l : ℕ} {A : V} {φ : Cof m} {Tp ep : V} (hA : A ∈ Vt l)
    (hT : ∀ k (f : Hom k m), (φ.restr f).holds → dat Tp k f ∈ Vt l)
    (he : ∀ k (f : Hom k m), (φ.restr f).holds → dat ep k f ∈ Vt l) : glueC m A φ Tp ep ∈ Vt l := by
  sorry

/-! ### The function of an equivalence -/

/-! ### Glue elements -/

theorem sem_glueEl_holds {e t a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hh : (ival ρ φ).holds)
    (hc : eqFun m (sem S e m ρ γ) (sem S t m ρ γ) = sem S a m ρ γ) :
    sem S (.glueEl φ e t a) m ρ γ = sem S t m ρ γ := by
  simp only [sem, interp] at hc ⊢; rw [if_pos hh, if_pos hc]

theorem sem_glueEl_not {e t a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (hh : ¬ (ival ρ φ).holds)
    (ha : IsKV m (sem S a m ρ γ)) :
    sem S (.glueEl φ e t a) m ρ γ =
      glueV m (ival ρ φ).face (partialKV m (ival ρ φ).face (faceVals S t ρ γ)) (sem S a m ρ γ) := by
  simp only [sem, interp] at ha ⊢; rw [if_neg hh, if_pos ha]; rfl

theorem sem_unglue (φ : I) (e g : Tm) (ρ : IEnv m) (γ : ℕ → V) :
    sem S (.unglue φ e g) m ρ γ = ungAt m (ival ρ φ).face (sem S e m ρ γ) (sem S g m ρ γ) := rfl

theorem holds_iff_face (ρ : IEnv m) (φ : I) : (ival ρ φ).holds ↔ Cof.holds (ival ρ φ).face :=
  DM.holds_iff_face_holds _

theorem sem_glueEl_cases {e t a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (hne : sem S (.glueEl φ e t a) m ρ γ ≠ ∅) :
    ((ival ρ φ).holds ∧ eqFun m (sem S e m ρ γ) (sem S t m ρ γ) = sem S a m ρ γ ∧
        sem S (.glueEl φ e t a) m ρ γ = sem S t m ρ γ) ∨
      (¬ (ival ρ φ).holds ∧ IsKV m (sem S a m ρ γ) ∧ sem S (.glueEl φ e t a) m ρ γ =
        glueV m (ival ρ φ).face (partialKV m (ival ρ φ).face (faceVals S t ρ γ)) (sem S a m ρ γ)) := by
  simp only [sem, interp] at hne ⊢
  split at hne
  · split at hne
    · left; rw [if_pos ‹_›, if_pos ‹_›]; exact ⟨‹_›, ‹_›, rfl⟩
    · exact absurd rfl hne
  · split at hne
    · right; rw [if_neg ‹_›, if_pos ‹_›]; exact ⟨‹_›, ‹_›, rfl⟩
    · exact absurd rfl hne

theorem glueC_ne_univC (A : V) {φ : Cof m} (Tp ep : V) (hn : ¬ φ.holds) (hφ : φ.IsCof) (l : ℕ) :
    glueC m A φ Tp ep ≠ univC m l := by
  intro h
  have := congrArg (codeTag m) h
  rw [codeTag_glueC hn hφ, codeTag_univC] at this
  simp [tGlue, tUniv] at this

/-- Inversion of well-formedness for Glue codes (at a stage where the face fails). -/
theorem WF.glue_inv {l : ℕ} {A : V} {φ : Cof m} {Tp ep : V} (hn : ¬ φ.holds) (hφ : φ.IsCof)
    (h : WF l m (glueC m A φ Tp ep)) : WF l m (Model.res (Hom.id m) A) := by
  generalize hc : glueC m A φ Tp ep = c at h
  have htag : codeTag m c = natZ tGlue := by rw [← hc]; exact codeTag_glueC hn hφ
  unfold WF at h
  cases h with
  | empty => simp [tEmpty, tGlue] at htag
  | pi => simp [tPi, tGlue] at htag
  | sigma => simp [tSigma, tGlue] at htag
  | path => simp [codeTag, pathC, pathDatum, tagZ, tPath, tGlue] at htag
  | ipi => simp [codeTag, ipiC, ipiDatum, tagZ, tIPi, tGlue] at htag
  | univ => rw [Ucodes_lt _ ‹_›, codeTag_univC] at htag; simp [tUniv, tGlue] at htag
  | @glue _ A' φ' Tp' ep' hA' hφ' hn' _ _ _ _ _ _ =>
    have h1 := congrArg (fun c => shapeOf c (Hom.id m)) hc
    simp only at h1
    rw [glueC_shape hn' hφ', glueC_shape hn hφ, tagZ_inj] at h1
    have h2 := (pair_inj'.1 h1.2).1
    rw [res_id (wf_props l m A' hA').1.kv] at h2
    rw [h2]; exact hA'

/-- The unglued component of an element of a Glue type (at a stage where the face fails). -/
theorem glue_elem {A : V} {φ : Cof m} {Tp ep g : V} {l : ℕ} (hn : ¬ φ.holds) (hφ : φ.IsCof)
    (hTp : IsKV m Tp) (hep : IsKV m ep) (hW : WF l m (glueC m A φ Tp ep))
    (hg : g ∈ El (glueC m A φ Tp ep) (Hom.id m)) :
    ∃ tp a, g = glueV m φ tp a ∧ a ∈ El A (Hom.id m) ∧ IsKV m a ∧
      tp = partialKV m φ (fun n g => dat tp n g) ∧
      (∀ n (g : Hom n m), (φ.restr g).holds → dat tp n g ∈ El (dat Tp n g) (Hom.id n)) ∧
      (∀ n (g : Hom n m), (φ.restr g).holds → ∀ n' (h : Hom n' n), Model.res h (dat tp n g) = dat tp n' (g.comp h)) ∧
      (∀ n (g' : Hom n m), (φ.restr g').holds → eqFun n (dat ep n g') (dat tp n g') = Model.res g' a) := by
  rw [El_glueC_id' hn hφ hTp hep, mem_glueElSet] at hg
  obtain ⟨tp, a, h1, ha, h2, h3, h4, h5⟩ := hg
  have hAfib := (WF.glue_inv hn hφ hW).fib
  refine ⟨tp, a, h1, ?_, hAfib.elKV _ _ _ ha, h2, h3, h4, fun n g' hg' => ?_⟩
  · rwa [El_res, Hom.id_comp] at ha
  · rw [h5 n g' hg']

end

end Model
