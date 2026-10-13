import Model.Canon.KanIPi
import Model.Canon.KanSigma
import Model.Canon.KanPath
import Model.Canon.KanDataCon
import Model.Canon.KripkeAll

/-!
# Canonicity: the Kan operations preserve computability

By induction on the code of the type (`tyCode_ind`), one lemma per type former.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The Kan properties of all types whose code is a restriction of `X`. -/
def KanP (S : Sig) (m : ℕ) (X : V) : Prop :=
  (∀ k (f : Hom k m) (A : Tm), (Comp S X m k f).ty A → KanH S k A) ∧
  (∀ k (f : Hom (k + 1) m) (A : Tm), (Comp S X m (k + 1) f).ty A → KanT S k A)

variable (hW : WfSig S)
include hW

theorem kanP_pi (l m : ℕ) (A B : V) (hA : WF l m A) (ihA : KanP S m A)
    (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, KanP S k (apZ (dat B k f) a)) : KanP S m (piC m A B) := by
  have hAne : A ≠ ∅ := IsKV.ne_empty hA.fib.kv
  constructor
  · intro k f T hT
    rw [Comp_piC A B hAne] at hT
    obtain ⟨⟨hTy, -⟩, A1, B1, hE, hall⟩ := hT
    obtain ⟨l1, hpiT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    refine kanH_retype hW hE (kanH_pi hW hpiT fun k' σ a ha => ?_)
    obtain ⟨hA1, hB1⟩ := hall k' σ
    have hael : (Comp S A m k' (f.comp σ.hom)).el (A1.isub σ) a := by rw [Comp_eq_semK hA1]; exact ha
    have hmem : semK S k' a ∈ El A (f.comp σ.hom) := by
      have := (Comp_el_typed hael).2; rwa [El_res, Hom.comp_id] at this
    exact (ihB k' (f.comp σ.hom) (semK S k' a) hmem).1 k' (Hom.id k') _ (hB1 a hael)
  · intro k f T hT
    rw [Comp_piC A B hAne] at hT
    obtain ⟨⟨hTy, -⟩, A1, B1, hE, hall⟩ := hT
    obtain ⟨l1, hpiT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    obtain ⟨l2, e⟩ := tyEq_eq hW hE ⟨l1, hpiT⟩
    refine kanT_retype hW e (kanT_pi hW hpiT (fun k' σ => ?_) fun k' σ w hw => ?_)
    · exact ihA.2 k' (f.comp σ.hom) _ (hall (k' + 1) σ).1
    · obtain ⟨hA1, hB1⟩ := hall (k' + 1) σ
      have hwel : (Comp S A m (k' + 1) (f.comp σ.hom)).el (A1.isub σ) w := by rw [Comp_eq_semK hA1]; exact hw
      have hmem : semK S (k' + 1) w ∈ El A (f.comp σ.hom) := by
        have := (Comp_el_typed hwel).2; rwa [El_res, Hom.comp_id] at this
      exact (ihB (k' + 1) (f.comp σ.hom) (semK S (k' + 1) w) hmem).2 k' (Hom.id (k' + 1)) _ (hB1 w hwel)

/-- The Kan properties of the restrictions of a computable type with a Kripke code. -/
theorem kanAll_of {m' n : ℕ} {X : V} (hX : KR S m' X) (ih : KanP S m' X) {g : Hom n m'} {A : Tm}
    (h : (Comp S X m' n g).ty A) : KanAll S n A :=
  ⟨fun k' ρ => ih.1 k' _ _ ((hX n g k' ρ A A).1 h), fun k' ρ => ih.2 k' _ _ ((hX n g (k' + 1) ρ A A).1 h)⟩

theorem kanP_ipi (m : ℕ) (L : V) (hLne : L ≠ ∅) (hL : KR S (m + 1) L) (ihL : KanP S (m + 1) L) :
    KanP S m (ipiC m L) := by
  constructor
  · intro k f T hT
    rw [Comp_ipiC L hLne] at hT
    obtain ⟨⟨hTy, -⟩, L1, hE, hall⟩ := hT
    obtain ⟨l1, hipiT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    have h0 := hall k (ISub.id k)
    rw [isub_up_id_of_closed (show L1.closedB 0 (k + 1) = true by
      have := closed_of_ty hW hipiT; simpa [Tm.closedB] using this)] at h0
    exact kanH_retype hW hE (kanH_ipi hW hipiT (kanAll_of hW hL ihL h0).1)
  · intro k f T hT
    rw [Comp_ipiC L hLne] at hT
    obtain ⟨⟨hTy, -⟩, L1, hE, hall⟩ := hT
    obtain ⟨l1, hipiT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    obtain ⟨l2, e⟩ := tyEq_eq hW hE ⟨l1, hipiT⟩
    have h0 := hall (k + 1) (ISub.id (k + 1))
    rw [isub_up_id_of_closed (show L1.closedB 0 (k + 1 + 1) = true by
      have := closed_of_ty hW hipiT; simpa [Tm.closedB] using this)] at h0
    exact kanT_retype hW e (kanT_ipi hW hipiT (kanAll_of hW hL ihL h0).2)

theorem kanP_sigma (l m : ℕ) (A B : V) (hA : WF l m A) (ihA : KR S m A ∧ KanP S m A)
    (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, KR S k (apZ (dat B k f) a) ∧ KanP S k (apZ (dat B k f) a)) :
    KanP S m (sigmaC m A B) := by
  have hAne : A ≠ ∅ := IsKV.ne_empty hA.fib.kv
  have mem : ∀ {k} {f : Hom k m} {A1 a : Tm}, (Comp S A m k f).ty A1 → RE S k A1 a →
      (Comp S A m k f).el A1 a ∧ semK S k a ∈ El A f := by
    intro k f A1 a hA1 ha
    have hael : (Comp S A m k f).el A1 a := by rw [Comp_eq_semK hA1]; exact ha
    exact ⟨hael, by have := (Comp_el_typed hael).2; rwa [El_res, Hom.comp_id] at this⟩
  constructor
  · intro k f T hT
    rw [Comp_sigmaC A B hAne] at hT
    obtain ⟨⟨hTy, -⟩, A1, B1, hE, hall⟩ := hT
    obtain ⟨l1, hsigT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    refine kanH_retype hW hE (kanH_sigma hW hsigT (fun k' ρ => ihA.2.1 k' _ _ (hall k' ρ).1) fun k' σ a ha => ?_)
    obtain ⟨hael, hmem⟩ := mem (hall k' σ).1 ha
    exact kanAll_of hW (ihB k' _ _ hmem).1 (ihB k' _ _ hmem).2 ((hall k' σ).2 a hael)
  · intro k f T hT
    rw [Comp_sigmaC A B hAne] at hT
    obtain ⟨⟨hTy, -⟩, A1, B1, hE, hall⟩ := hT
    obtain ⟨l1, hsigT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    obtain ⟨l2, e⟩ := tyEq_eq hW hE ⟨l1, hsigT⟩
    refine kanT_retype hW e (kanT_sigma hW hsigT (fun k' ρ => ihA.2.2 k' _ _ (hall (k' + 1) ρ).1)
      fun k' ρ w hw => ?_)
    obtain ⟨hwel, hmem⟩ := mem (hall (k' + 1) ρ).1 hw
    exact (ihB (k' + 1) _ _ hmem).2.2 k' (Hom.id (k' + 1)) _ ((hall (k' + 1) ρ).2 w hwel)

omit hW in
theorem ISub.up_comp_cons_id (σ : ISub k' k) (r : I) (hr : r.Scoped k') :
    σ.up.comp (ISub.cons r hr (ISub.id k')) = ISub.cons r hr σ := by
  ext i
  rcases i with _ | i
  · rfl
  · show ((σ.τ i).shift).subst (ISub.cons r hr (ISub.id k')).τ = σ.τ i
    rw [I_shift_cons]
    by_cases h : i < k
    · exact ISub.I.subst_scoped_id (σ.sc i h) fun j hj => by simp [ISub.id, hj]
    · rw [σ.hi i (by omega)]; rfl

/-- An endpoint of a path type's line, at a restriction, is computable. -/
theorem path_end_RE {L : V} (hL : KR S (m + 1) L) {f : Hom k m} {L1 b : Tm} (σ : ISub k' k) (r : I)
    (hr : r.Scoped k') (h0 : (Comp S L (m + 1) (k' + 1) ((Hom.lift f).comp σ.up.hom)).ty (L1.isub σ.up))
    (hel : (Comp S L (m + 1) k' ((Hom.lift f).comp (ISub.cons r hr σ).hom)).el ((L1.isub σ.up).dinst r) b) :
    RE S k' ((L1.isub σ.up).dinst r) b := by
  have hty := ty_dinst hW hL h0 r hr
  rw [Hom.comp_assoc, ← ISub.hom_comp, ISub.up_comp_cons_id] at hty
  unfold RE; rw [← Comp_eq_semK hty]; exact hel

theorem kanP_path (m : ℕ) (L a0 a1 : V) (hLne : L ≠ ∅) (hL : KR S (m + 1) L) (ihL : KanP S (m + 1) L) :
    KanP S m (pathC m L a0 a1) := by
  constructor
  · intro k f T hT
    rw [Comp_pathC L a0 a1 hLne] at hT
    obtain ⟨⟨hTy, -⟩, L1, b0, b1, hE, hall⟩ := hT
    obtain ⟨l1, hpathT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    have hc := closed_of_ty hW hpathT
    simp only [Tm.closedB, Bool.and_eq_true] at hc
    obtain ⟨h0, h0a, h0b⟩ := hall k (ISub.id k)
    have ha := path_end_RE hW hL (ISub.id k) .zero trivial h0 h0a
    have hb := path_end_RE hW hL (ISub.id k) .one trivial h0 h0b
    rw [isub_up_id_of_closed hc.1.1, isub_id_of_closed hc.1.2] at ha
    rw [isub_up_id_of_closed hc.1.1, isub_id_of_closed hc.2] at hb
    rw [isub_up_id_of_closed hc.1.1] at h0
    exact kanH_retype hW hE (kanH_path hW hpathT (kanAll_of hW hL ihL h0).1 ha hb)
  · intro k f T hT
    rw [Comp_pathC L a0 a1 hLne] at hT
    obtain ⟨⟨hTy, -⟩, L1, b0, b1, hE, hall⟩ := hT
    obtain ⟨l1, hpathT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    obtain ⟨l2, e⟩ := tyEq_eq hW hE ⟨l1, hpathT⟩
    have hc := closed_of_ty hW hpathT
    simp only [Tm.closedB, Bool.and_eq_true] at hc
    have h0 := (hall (k + 1) (ISub.id (k + 1))).1
    rw [isub_up_id_of_closed hc.1.1] at h0
    exact kanT_retype hW e (kanT_path hW hpathT (kanAll_of hW hL ihL h0)
      (fun k' σ => path_end_RE hW hL σ .zero trivial (hall k' σ).1 (hall k' σ).2.1)
      (fun k' σ => path_end_RE hW hL σ .one trivial (hall k' σ).1 (hall k' σ).2.2))

theorem kanP_data {Θ : SData m} (hΘ : Θ.Good)
    (ih : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre →
      KR S n (Θ.ty c j n g pre) ∧ KanP S n (Θ.ty c j n g pre)) (hKR : KR S m (dataC Θ)) :
    KanP S m (dataC Θ) := by
  constructor
  · intro k f T hT
    exact kanH_data hW hΘ (fun c j n g pre hp => (ih c j n g pre hp).1)
      (fun c j n g pre hp => (ih c j n g pre hp).2) hKR hT
  · intro k f T hT
    have hT' := hT
    rw [Comp_dataC] at hT'
    obtain ⟨⟨hTy, -⟩, ps, hE, hpl, hall⟩ := hT'
    have hTp : (Comp S (dataC Θ) m (k + 1) f).ty (.data Θ.idx ps) := ((cv_dataC hW Θ) (k + 1) f T _ T T).1 hT hE
    obtain ⟨l1, hdT⟩ := ty_of_tyEq hW hTy hE (fun l h => by cases h)
    obtain ⟨l2, e⟩ := tyEq_eq hW hE ⟨l1, hdT⟩
    refine kanT_retype hW e fun φ a hty ha => ?_
    have hcl := closed_of_ty hW hdT
    have hT0 := ty_dinst hW hKR hTp .zero trivial
    have hdr := DR_of_RE hW hT0 ha
    have key := transp_data_DR hW hΘ (fun c j n g pre hp => (ih c j n g pre hp).1)
      (fun c j n g pre hp => (ih c j n g pre hp).2) hKR hTp hall hdr k (ISub.id k) (ISub.id (k + 1))
      (by rw [ISub.hom_id, Hom.comp_id, ISub.id_comp]) ?_ φ ?_
    · have hpc : ps.closedB 0 (k + 1) = true := by simpa [Tm.closedB] using hcl
      rw [isub_id_of_closed hpc, isub_id_of_closed (closed_of_ty hW (Comp_el_typed ha).1)] at key
      exact key
    · have hd0 := minimal_to_spec (HasTy0.dsubst (sigClosed_of_wfSig hW) (Φ := .one) (Γ := [])
        (spec_to_minimal hW hdT) (r := .zero) trivial)
      have hpc : ps.closedB 0 (k + 1) = true := by simpa [Tm.closedB] using hcl
      rw [isub_id_of_closed (closed_of_ty hW hd0), isub_id_of_closed hpc]
      exact TyEq.refl _
    · have hpc : ps.closedB 0 (k + 1) = true := by simpa [Tm.closedB] using hcl
      rw [isub_id_of_closed hpc, isub_id_of_closed (closed_of_ty hW (Comp_el_typed ha).1)]
      exact hty

theorem kanP_empty (m : ℕ) : KanP S m (emptyC m) := by
  constructor
  · intro k f T hT φ u a _ _ ha
    unfold RE at ha; rw [← Comp_eq_semK hT, Comp_emptyC] at ha; exact ha.elim
  · intro k f T hT φ a _ ha
    have h0 := ty_dinst hW (kr_emptyC hW) hT .zero trivial
    unfold RE at ha; rw [← Comp_eq_semK h0, Comp_emptyC] at ha; exact ha.elim

omit hW in
/-- All codes are Kan. Proved in `KanAll.lean`, after the fundamental lemma (which the universe
and Glue cases use on Kan-free terms); until then a hypothesis. -/
def KanOracle (S : Sig) : Prop := ∀ m X, TyCode m X → KanP S m X

variable (hO : KanOracle S)
include hO

/-- Composition in a computable type of a computable tube and base is computable. -/
theorem kan_hcomp {A u a : Tm} {φ : I} (hA : RT S k A)
    (hty : HasTy S k .one [] (.hcomp A φ u a) A)
    (hu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE S k' (A.isub σ) ((u.isub σ.up).dinst r))
    (ha : RE S k A a) : RE S k A (.hcomp A φ u a) :=
  (hO _ _ (tyCode_of_ty hW (Comp_el_typed ha).1)).1 k (Hom.id k) A hA φ u a hty hu ha

/-- Transport along a computable line of a computable element is computable. -/
theorem kan_transp {A a : Tm} {φ : I} {l : ℕ} (hA : RT S (k + 1) A)
    (hty : HasTy S k .one [] (.transp A φ a) (A.dinst .one))
    (ha : RE S k (A.dinst .zero) a) : RE S k (A.dinst .one) (.transp A φ a) := by
  obtain ⟨-, ⟨l, hA' | rfl⟩, -⟩ := Comp_ty_base hA
  · exact (hO _ _ (tyCode_of_univ hW hA')).2 k (Hom.id (k + 1)) A hA φ a hty ha
  · obtain ⟨l0, ⟨hU, -⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
    have hl := gen_univ hU rfl
    exact (hO _ _ ⟨l, by omega, .inr rfl⟩).2 k (Hom.id (k + 1)) _ hA φ a hty ha

/-- Types computable at all restrictions are Kan. -/
theorem kanAll_of_RT {n : ℕ} {A : Tm} (h : ∀ k' (ρ : ISub k' n), RT S k' (A.isub ρ)) : KanAll S n A :=
  ⟨fun k' ρ _ _ _ hty hu ha => kan_hcomp hW hO (h k' ρ) hty hu ha,
    fun k' ρ _ _ hty ha => kan_transp hW hO (l := 0) (h (k' + 1) ρ) hty ha⟩

end

end Model.Canon
