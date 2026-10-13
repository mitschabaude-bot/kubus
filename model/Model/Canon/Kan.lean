import Model.Canon.KanIPi
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

theorem tyEq_eq {A B : Tm} (h : TyEq S k A B) (hB : ∃ l, HasTy S k .one [] B (.univ l)) :
    ∃ l, EqTm S k .one [] A B (.univ l) := by
  rcases h with rfl | h
  · obtain ⟨l, hB⟩ := hB; exact ⟨l, EqTm.refl hB⟩
  · exact h

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

theorem kanP_empty (m : ℕ) : KanP S m (emptyC m) := by
  constructor
  · intro k f T hT φ u a _ _ ha
    unfold RE at ha; rw [← Comp_eq_semK hT, Comp_emptyC] at ha; exact ha.elim
  · intro k f T hT φ a _ ha
    have h0 := ty_dinst hW (kr_emptyC hW) hT .zero trivial
    unfold RE at ha; rw [← Comp_eq_semK h0, Comp_emptyC] at ha; exact ha.elim

theorem kanP_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : KanP S m X := by
  refine (tyCode_ind (fun m X => KR S m X ∧ KanP S m X) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ m X hX).2
  · exact fun m => ⟨kr_emptyC hW, kanP_empty hW m⟩
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact ⟨kr_piC hW (WF.fib (show WF l m (piC m A B) from WFI.pi hA hB hBf hBw hBn)) (IsKV.ne_empty hA.fib.kv),
      kanP_pi hW l m A B hA ihA.2 fun k f a ha => (ihB k f a ha).2⟩
  · sorry
  · sorry
  · intro l m L hL ihL
    exact ⟨kr_ipiC hW (WF.fib (show WF l m (ipiC m L) from WFI.ipi hL)) (IsKV.ne_empty hL.fib.kv),
      kanP_ipi hW m L (IsKV.ne_empty hL.fib.kv) ihL.1 ihL.2⟩
  · sorry
  · sorry
  · sorry

/-- Composition in a computable type of a computable tube and base is computable. -/
theorem kan_hcomp {A u a : Tm} {φ : I} (hA : RT S k A)
    (hty : HasTy S k .one [] (.hcomp A φ u a) A)
    (hu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE S k' (A.isub σ) ((u.isub σ.up).dinst r))
    (ha : RE S k A a) : RE S k A (.hcomp A φ u a) :=
  (kanP_tyCode hW (tyCode_of_ty hW (Comp_el_typed ha).1)).1 k (Hom.id k) A hA φ u a hty hu ha

/-- Transport along a computable line of a computable element is computable. -/
theorem kan_transp {A a : Tm} {φ : I} {l : ℕ} (hA : RT S (k + 1) A)
    (hty : HasTy S k .one [] (.transp A φ a) (A.dinst .one))
    (ha : RE S k (A.dinst .zero) a) : RE S k (A.dinst .one) (.transp A φ a) := by
  obtain ⟨-, ⟨l, hA' | rfl⟩, -⟩ := Comp_ty_base hA
  · exact (kanP_tyCode hW (tyCode_of_univ hW hA')).2 k (Hom.id (k + 1)) A hA φ a hty ha
  · obtain ⟨l0, ⟨hU, -⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
    have hl := gen_univ hU rfl
    exact (kanP_tyCode hW ⟨l, by omega, .inr rfl⟩).2 k (Hom.id (k + 1)) _ hA φ a hty ha

end

end Model.Canon
