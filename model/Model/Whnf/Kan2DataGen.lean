import Model.Whnf.Kan2DataH2

/-!
# The binary composition at inductive types without path constructors: general types

A type related to itself whose normal form is an inductive type is related to that normal form
(`RT2_data_whnf`); composition at such types (`kanH2_data`), from that at the literal types
(`kanH2_lit`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- A type whose normal form is an inductive type: that normal form is typed at the level of the
declaration. -/
theorem data_whnf_ty {T ps : Tm} (hTK : IsTyK S k T) (hR : RedT S k T (.data d ps)) :
    HasTy S k .one [] (.data d ps) (.univ D.level) := by
  obtain ⟨l, hd | hd⟩ := hTK.of_tyEq hR.2
  · obtain ⟨D', hD', hPt⟩ := gen_data_tele (spec_to_minimal hW hd) rfl
    rw [hD] at hD'; cases hD'
    exact minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hPt)
  · cases hd

/-- A type related to itself whose normal form is an inductive type is related to that normal form. -/
theorem RT2_data_whnf {T ps : Tm} (hTT : RT2 S k T T) (hR : RedT S k T (.data d ps)) :
    RT2 S k T (.data d ps) := by
  obtain ⟨-, hTK, -, -, -, -⟩ := Comp2_ty_base hTT
  have hd := data_whnf_ty hW hD hTK hR
  have hsem : semK S k T = dataC (ΘK S D d k ps) := (semK_tyEq hW hR.2).trans (semK_dataT hW hD hd)
  have ihp : ∀ n (g : Hom n k) j t X, vnth ((ΘK S D d k ps).pt n g) j = ZFSet.pair t X → PER2 S n X :=
    fun n g j t X e => per2_wf hW _ (level_le hW hD (K := k)) n _ (ΘK_pt_wf hW hD hd n g j t X e)
  have hTc := closed_of_isTyK hW hTK
  have hT := hTT
  unfold RT2 at hT ⊢
  rw [hsem, Comp2_dataC] at hT ⊢
  obtain ⟨hb, hall, hc, -⟩ := hT
  -- the parameters at the identity
  obtain ⟨ps0, -, h0, -, hpl, -, -, -, d0, -, -⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed hTc] at h0
  obtain rfl : ps0 = ps := by have := RedW.unique h0.1 hR.1; injection this
  -- the parameters' clauses at a restriction
  have hσ : ∀ k' (σ : ISub k' k) ps1, RedT S k' (T.isub σ) (.data d ps1) →
      argRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) ps1 ∧
      argRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ ps1 (ps0.isub σ) ∧
      parRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) ps1 := by
    intro k' σ ps1 h1
    have := hc k (ISub.id k) k' σ ps0 ps1 (by rw [isub_id_of_closed hTc]; exact hR)
      (by rw [ISub.id_comp]; exact h1)
    rw [ISub.id_comp] at this
    exact this
  have hpc : ps0.closedB 0 k = true := by have := closed_of_ty hW hd; simpa [Tm.closedB] using this
  have hdK : IsTyK S k (.data d ps0) := ⟨_, .inl hd⟩
  -- the self-relation of the restricted parameters
  have hself : ∀ k' (σ : ISub k' k),
      argRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) (ps0.isub σ) ∧
      parRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) (ps0.isub σ) := by
    intro k' σ
    obtain ⟨ps1, -, h1, -, -, -, -, -, -, -, -⟩ := hall k' σ
    obtain ⟨-, -, p⟩ := hσ k' σ ps1 h1
    have hT1 : IsTyK S k' (.data d ps1) := (hTK.isub hW σ).of_tyEq h1.2
    refine ⟨?_, parRel2_trans ihp (Hom.id k) σ ?_ p (parRel2_symm ihp (Hom.id k) σ p)⟩
    · have := argRelH_isub _ _ ((argRel2_iff _ (ISub.id k)).1 d0) σ
      rw [ISub.hom_id, Hom.id_comp] at this
      exact (argRel2_iff _ σ).2 this
    · rw [data_len_of hW hT1, data_len_of hW (show IsTyK S k' (.data d (ps0.isub σ)) from hdK.isub hW σ)]
  have hred : ∀ k' (σ : ISub k' k), RedT S k' ((Tm.data d ps0).isub σ) (.data d (ps0.isub σ)) :=
    fun k' σ => ⟨redW_self (step_data d _), TyEq.refl _⟩
  refine ⟨⟨hTK, hdK, hb.2.2.1, ?_, hR.2⟩, fun k' σ => ?_, hc, ?_⟩
  · exact (semK_tyEq hW hR.2).symm.trans hb.2.2.1
  · obtain ⟨ps1, -, h1, -, hl1, -, -, -, d1, -, pr1⟩ := hall k' σ
    obtain ⟨a, b, p⟩ := hσ k' σ ps1 h1
    exact ⟨ps1, ps0.isub σ, h1, hred k' σ, hl1, isList_subst hpl _ _, b, a, d1, (hself k' σ).1,
      parRel2_symm ihp (Hom.id k) σ p⟩
  · intro k' σ k3 σ' p1 p2 h1 h2
    obtain rfl := redT_data_eq (Θ := ΘK S D d k ps0) (show RedT S k' (.data d (ps0.isub σ)) (.data d p1) from h1)
    obtain rfl := redT_data_eq (Θ := ΘK S D d k ps0)
      (show RedT S k3 (.data d (ps0.isub (σ.comp σ'))) (.data d p2) from h2)
    rw [Tm.isub_isub]
    exact ⟨(hself k3 _).1, (hself k3 _).1, (hself k3 _).2⟩

end

end

end Model.Whnf
