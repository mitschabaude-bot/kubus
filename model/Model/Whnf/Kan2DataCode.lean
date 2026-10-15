import Model.Whnf.Kan2DataHITInd3

/-!
# Binary Kan operations at inductive types' codes

Related inductive types carry Kan of their argument types at related prefixes. Transport at higher
inductive types also uses constructor boundaries and boundary type validity at the declaration index.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- Transport along related lines whose normal forms are an inductive type. -/
theorem kanT2_data' (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hyp : HITHyp2 S (d + 1))
    {T T' ps : Tm} (hTT : RT2 S (k + 1) T T') (hR : RedT S (k + 1) T (.data d ps))
 :
    KanT2 S k T T' := by
  by_cases h0 : D.params = []
  · exact kanT2_data0 hW hD h0 hTT hR
  cases hH : D.isHIT
  · exact kanT2_data hW hD h0 (fun hP  hRL hQ => kanT2_lit hW hD hH h0 hP  hRL hQ) hTT hR
  · exact kanT2_data hW hD h0 (fun hP  hRL hQ => kanT2_litH hW hD hH hyp h0 hP  hRL hQ) hTT hR

section code
variable (hW : WfSig S) {m : ℕ} {Θ : SData m} {D : DataDecl} (hD : S[Θ.idx]? = some (.data D))
include hW hD

/-- A type related at a restriction of the code of an inductive type: its relation, its normal form,
and the shapes of the literal types related to its restrictions. -/
theorem dataC_ty {f : Hom k m} {A A' : Tm} (hT : (Comp2 S (dataC Θ) m k f).ty A A') :
    RT2 S k A A' ∧ (∃ ps, RedT S k A (.data Θ.idx ps)) := by
  have hb := Comp2_ty_base hT
  have hTT : RT2 S k A A' := (Comp2_ty_iff hb.1 hb.2.2.2.1).1 hT
  have hAc := closed_of_isTyK hW hb.2.1
  have hT' := hT
  rw [Comp2_dataC] at hT'
  obtain ⟨ps, -, hR, -⟩ := hT'.2.1 k (ISub.id k)
  rw [isub_id_of_closed hAc] at hR
  exact ⟨hTT, ps, hR⟩

/-- Composition at the types related at a restriction of the code of an inductive type. -/
theorem kanH2_dataC {f : Hom k m} {A A' : Tm} (hT : (Comp2 S (dataC Θ) m k f).ty A A') : KanH2 S k A A' := by
  obtain ⟨hTT, ps, hR⟩ := dataC_ty hW hD hT
  cases hH : D.isHIT
  · exact kanH2_data hW hD hH hTT hR
  · exact kanH2_dataHIT hW hD hH hTT hR

/-- Transport along the lines related at a restriction of the code of an inductive type. -/
theorem kanT2_dataC (hyp : HITHyp2 S (Θ.idx + 1)) {f : Hom (k + 1) m} {A A' : Tm}
    (hT : (Comp2 S (dataC Θ) m (k + 1) f).ty A A') : KanT2 S k A A' := by
  obtain ⟨hTT, ps, hR⟩ := dataC_ty hW hD hT
  exact kanT2_data' hW hD hyp hTT hR

/-- The binary Kan operations at the code of an inductive type. -/
theorem kanP2_dataC (hyp : HITHyp2 S (Θ.idx + 1)) : KanP2 S m (dataC Θ) :=
  ⟨fun k f A A' hT => kanH2_dataC hW hD hT, fun k f A A' hT => kanT2_dataC hW hD hyp hT⟩

end code

end

end Model.Whnf
