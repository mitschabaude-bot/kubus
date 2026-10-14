import Model.Whnf.Kan2DataT

/-!
# The binary Kan operations at the codes of inductive types

Composition at all inductive types, and transport at inductive types without path constructors or
without parameters, at all pairs of types related at a restriction of the code `dataC Θ`, given the
Kan properties of the argument types through the shape of `Θ` (`KanShape`, which follows from those at
the argument types' codes by `kanShape_of`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

section code
variable (hW : WfSig S) {m : ℕ} {Θ : SData m} {D : DataDecl} (hD : S[Θ.idx]? = some (.data D))
  (hKS : KanShape S m Θ)
include hW hD hKS

/-- A type related at a restriction of the code of an inductive type: its relation, its normal form,
and the shapes of the literal types related to its restrictions. -/
theorem dataC_ty {f : Hom k m} {A A' : Tm} (hT : (Comp2 S (dataC Θ) m k f).ty A A') :
    RT2 S k A A' ∧ (∃ ps, RedT S k A (.data Θ.idx ps)) ∧
    ∀ k1 (ρ1 : ISub k1 k) P1, HasTy S k1 .one [] (.data Θ.idx P1) (.univ D.level) →
      RT2 S k1 (.data Θ.idx P1) (A.isub ρ1) → KanShape S k1 (ΘK S D Θ.idx k1 P1) := by
  have hb := Comp2_ty_base hT
  have hTT : RT2 S k A A' := (Comp2_ty_iff hb.1 hb.2.2.2.1).1 hT
  have hAc := closed_of_isTyK hW hb.2.1
  have hT' := hT
  rw [Comp2_dataC] at hT'
  obtain ⟨ps, -, hR, -⟩ := hT'.2.1 k (ISub.id k)
  rw [isub_id_of_closed hAc] at hR
  refine ⟨hTT, ⟨ps, hR⟩, fun k1 ρ1 P1 hP1 hPA => ?_⟩
  have e : dataC (ΘK S D Θ.idx k1 P1) = dataC (Θ.restr (f.comp ρ1.hom)) := by
    rw [← semK_dataT hW hD hP1, ← RT2.semK_eq hW hPA, semK_isubTy hW hb.2.1 ρ1, hb.2.2.2.1, res_res, res_dataC]
  exact KanShape.of_dataC_eq e (hKS.restr _)

/-- Composition at the types related at a restriction of the code of an inductive type. -/
theorem kanH2_dataC {f : Hom k m} {A A' : Tm} (hT : (Comp2 S (dataC Θ) m k f).ty A A') : KanH2 S k A A' := by
  obtain ⟨hTT, ⟨ps, hR⟩, hK⟩ := dataC_ty hW hD hKS hT
  cases hH : D.isHIT
  · exact kanH2_data hW hD hH hTT hR hK
  · exact kanH2_dataHIT hW hD hH hTT hR

/-- Transport along the lines related at a restriction of the code of an inductive type without path
constructors or without parameters. -/
theorem kanT2_dataC (hHp : D.isHIT = false ∨ D.params = []) {f : Hom (k + 1) m} {A A' : Tm}
    (hT : (Comp2 S (dataC Θ) m (k + 1) f).ty A A') : KanT2 S k A A' := by
  obtain ⟨hTT, ⟨ps, hR⟩, hK⟩ := dataC_ty hW hD hKS hT
  exact kanT2_data' hW hD hHp hTT hR fun k1 θ P1 hP1 hPA => hK (k1 + 1) θ P1 hP1 hPA

/-- The binary Kan operations at the code of an inductive type without path constructors or without
parameters. -/
theorem kanP2_dataC (hHp : D.isHIT = false ∨ D.params = []) : KanP2 S m (dataC Θ) :=
  ⟨fun k f A A' hT => kanH2_dataC hW hD hKS hT, fun k f A A' hT => kanT2_dataC hW hD hKS hHp hT⟩

end code

end

end Model.Whnf
