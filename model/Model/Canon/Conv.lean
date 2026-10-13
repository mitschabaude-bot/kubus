import Model.Canon.Kripke

/-!
# Canonicity: computability is stable under judgmental equality
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' k'' m : ℕ}

/-- Computability is closed under judgmental equality of types and of elements. -/
def CV (S : Sig) (m : ℕ) (X : V) : Prop :=
  ∀ k (f : Hom k m) (A A' t t' : Tm),
    ((Comp S X m k f).ty A → TyEq S k A A' → (Comp S X m k f).ty A') ∧
    ((Comp S X m k f).el A t → TyEq S k A A' → EqTm S k .one [] t t' A' → (Comp S X m k f).el A' t')

variable (hW : WfSig S)
include hW

/-- The type of a typed closed term is a type. -/
theorem isTyK_of_ty {t A : Tm} (ht : HasTy S k .one [] t A) : IsTyK S k A := by
  obtain ⟨hT, hC⟩ := wf_typed _ S rfl hW
  rcases pre_ty (sigClosed_of_wfSig hW) hT hC (spec_to_minimal hW ht) with ⟨l, h⟩ | ⟨l, rfl, -⟩
  · exact ⟨l, .inl (minimal_to_spec h)⟩
  · exact ⟨l, .inr rfl⟩

/-- A type equal to a type former is typed in a universe. -/
theorem ty_of_tyEq {A B : Tm} (hA : IsTyK S k A) (h : TyEq S k A B) (hB : ∀ l, B ≠ .univ l) :
    ∃ l, HasTy S k .one [] B (.univ l) := by
  rcases h with rfl | ⟨l, e⟩
  · obtain ⟨l, hA | rfl⟩ := hA
    · exact ⟨l, hA⟩
    · exact absurd rfl (hB l)
  · exact ⟨l, HasTy.eqR e⟩

theorem mem_of_eq {X : V} {f : Hom k m} {t t' A : Tm} (h : EqTm S k .one [] t t' A)
    (hm : semK S k t ∈ El (res f X) (Hom.id k)) : semK S k t' ∈ El (res f X) (Hom.id k) := by
  rwa [← semK_eq hW h]

theorem cv_piC {A B : V} (hA : A ≠ ∅) (ihB : ∀ k (f : Hom k m) a, a ∈ El A f → CV S k (apZ (dat B k f) a)) :
    CV S m (piC m A B) := by
  intro k f T T' t t'
  rw [Comp_piC A B hA]
  constructor
  · rintro ⟨⟨hT, hsem⟩, A1, B1, hE, hall⟩ hTT'
    exact ⟨⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, A1, B1, hTT'.symm.trans hW hE, hall⟩
  · rintro ⟨ht, hmem, -, A1, B1, hE, hall⟩ hTT' htt'
    have ht' := HasTy.eqR htt'
    have hE' := hTT'.symm.trans hW hE
    refine ⟨ht', mem_of_eq hW htt' hmem, ht', A1, B1, hE', fun k'' σ' a ha => ?_⟩
    have h1 := hall k'' σ' a ha
    have hamem : semK S k'' a ∈ El A (f.comp ((ISub.id k).comp σ').hom) := by
      have := (Comp_el_typed ha).2; rwa [El_res, Hom.comp_id] at this
    refine ((ihB k'' _ _ hamem) k'' (ISub.id k'').hom _ _ _ _).2 h1 (TyEq.refl _) ?_
    have hf : EqTm S k'' .one [] (t.isub σ') (t'.isub σ') (.pi (A1.isub σ') (B1.isub σ')) := by
      rw [← isub_pi]; exact EqTm.isubS hW (htt'.tyConv hE') σ'
    exact EqTm.app hf (EqTm.refl (Comp_el_typed ha).1)

theorem cv_sigmaC {A B : V} (hA : A ≠ ∅) (ihA : CV S m A)
    (ihB : ∀ k (f : Hom k m) a, a ∈ El A f → CV S k (apZ (dat B k f) a)) :
    CV S m (sigmaC m A B) := by
  intro k f T T' t t'
  rw [Comp_sigmaC A B hA]
  constructor
  · rintro ⟨⟨hT, hsem⟩, A1, B1, hE, hall⟩ hTT'
    exact ⟨⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, A1, B1, hTT'.symm.trans hW hE, hall⟩
  · rintro ⟨ht, hmem, -, A1, B1, hE, hall⟩ hTT' htt'
    have ht' := HasTy.eqR htt'
    have hE' := hTT'.symm.trans hW hE
    refine ⟨ht', mem_of_eq hW htt' hmem, ht', A1, B1, hE', fun k'' σ' => ?_⟩
    obtain ⟨h1, h2⟩ := hall k'' σ'
    have hp : EqTm S k'' .one [] (t.isub σ') (t'.isub σ') (.sigma (A1.isub σ') (B1.isub σ')) := by
      rw [← isub_sigma]; exact EqTm.isubS hW (htt'.tyConv hE') σ'
    have hfst := EqTm.fst hp
    refine ⟨((ihA k'' _ _ _ _ _).2 h1 (TyEq.refl _) hfst), ?_⟩
    have hamem : semK S k'' (.fst (t.isub σ')) ∈ El A (f.comp ((ISub.id k).comp σ').hom) := by
      have := (Comp_el_typed h1).2; rwa [El_res, Hom.comp_id] at this
    obtain ⟨l, hsig⟩ := ty_of_tyEq hW (isTyK_of_ty hW (HasTy.isubS hW ht' σ'))
      (by have := hE'.isub hW σ'; rwa [isub_sigma] at this) (fun l h => by cases h)
    have hB := HasTy.sigmaCod hsig
    have hBeq : EqTm S k'' .one [] ((B1.isub σ').inst (.fst (t.isub σ'))) ((B1.isub σ').inst (.fst (t'.isub σ')))
        (.univ l) := EqTm.subst (EqTm.refl hB) hfst
    dsimp only at h2 ⊢
    rw [← semK_eq hW hfst]
    exact ((ihB k'' _ _ hamem) k'' (ISub.id k'').hom _ _ _ _).2 h2 (.inr ⟨l, hBeq⟩)
      ((EqTm.snd hp).tyConv (.inr ⟨l, hBeq⟩))

theorem cv_pathC {L a0 a1 : V} (hL : L ≠ ∅) (ihL : CV S (m + 1) L) : CV S m (pathC m L a0 a1) := by
  intro k f T T' t t'
  rw [Comp_pathC L a0 a1 hL]
  constructor
  · rintro ⟨⟨hT, hsem⟩, L1, b0, b1, hE, hall⟩ hTT'
    exact ⟨⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, L1, b0, b1, hTT'.symm.trans hW hE, hall⟩
  · rintro ⟨ht, hmem, -, L1, b0, b1, hE, hall⟩ hTT' htt'
    have ht' := HasTy.eqR htt'
    have hE' := hTT'.symm.trans hW hE
    refine ⟨ht', mem_of_eq hW htt' hmem, ht', L1, b0, b1, hE', fun k'' σ' r hr => ?_⟩
    have hp : EqTm S k'' .one [] (t.isub σ') (t'.isub σ') (.path (L1.isub σ'.up) (b0.isub σ') (b1.isub σ')) := by
      rw [← isub_path]; exact EqTm.isubS hW (htt'.tyConv hE') σ'
    exact (ihL _ _ _ _ _ _).2 (hall k'' σ' r hr) (TyEq.refl _) (EqTm.papp hp hr hr (fun _ => rfl))

theorem cv_ipiC {L : V} (hL : L ≠ ∅) (ihL : CV S (m + 1) L) : CV S m (ipiC m L) := by
  intro k f T T' t t'
  rw [Comp_ipiC L hL]
  constructor
  · rintro ⟨⟨hT, hsem⟩, L1, hE, hall⟩ hTT'
    exact ⟨⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, L1, hTT'.symm.trans hW hE, hall⟩
  · rintro ⟨ht, hmem, -, L1, hE, hall⟩ hTT' htt'
    have ht' := HasTy.eqR htt'
    have hE' := hTT'.symm.trans hW hE
    refine ⟨ht', mem_of_eq hW htt' hmem, ht', L1, hE', fun k'' σ' r hr => ?_⟩
    have hp : EqTm S k'' .one [] (t.isub σ') (t'.isub σ') (.ipi (L1.isub σ'.up)) := by
      rw [← isub_ipi]; exact EqTm.isubS hW (htt'.tyConv hE') σ'
    exact (ihL _ _ _ _ _ _).2 (hall k'' σ' r hr) (TyEq.refl _) (EqTm.iapp hp hr hr (fun _ => rfl))

theorem cv_emptyC : CV S m (emptyC m) := by
  intro k f T T' t t'
  rw [Comp_emptyC]
  exact ⟨fun ⟨hT, hsem⟩ hTT' => ⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, fun h => h.elim⟩

theorem cv_univC {l : ℕ} (ih : ∀ m' X, WF l m' X → CV S m' X) : CV S m (univC m l) := by
  intro k f T T' t t'
  rw [Comp_univC]
  constructor
  · rintro ⟨⟨hT, hsem⟩, hE⟩ hTT'
    exact ⟨⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, hTT'.symm.trans hW hE⟩
  · rintro ⟨ht, hmem, hE, hm, hty⟩ hTT' htt'
    have ht' := HasTy.eqR htt'
    have hE' := hTT'.symm.trans hW hE
    have hsem := semK_eq hW htt'
    refine ⟨ht', mem_of_eq hW htt' hmem, hE', hsem ▸ hm, ?_⟩
    have hY : WF l k (semK S k t) := (ZFSet.mem_sep.1 hm).2
    rw [← hsem]
    obtain ⟨l', e⟩ : ∃ l', EqTm S k .one [] t t' (.univ l') := by
      rcases hE' with h | ⟨l', h⟩
      · exact ⟨l, h ▸ htt'⟩
      · exact ⟨l, htt'.conv h⟩
    exact ((ih k _ hY) k (Hom.id k) t t' t t').1 hty (.inr ⟨l', e⟩)

end

end Model.Canon
