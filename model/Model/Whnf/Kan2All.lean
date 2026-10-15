import Model.Whnf.Kan2UnivCode
import Model.Whnf.Kan2GlueCode
import Model.Whnf.Kan2DataCode

/-!
# Binary Kan operations at the type formers' codes

The per-former lemmas use the component Kan evidence carried by the binary relation.
`kanP2_dataC'` recovers a data declaration from a related type and applies its indexed HIT hypotheses.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ} (hW : WfSig S)
include hW

/-! ### Inductive types -/

theorem data_decl {m : ℕ} {Θ : SData m} {f : Hom k m} {A A' : Tm} (hT : (Comp2 S (dataC Θ) m k f).ty A A') :
    ∃ D, S[Θ.idx]? = some (.data D) := by
  have hb := Comp2_ty_base hT
  rw [Comp2_dataC] at hT
  obtain ⟨ps, -, hR, -⟩ := hT.2.1 k (ISub.id k)
  rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
  obtain ⟨l, hd⟩ := ty_of_tyEq hW hb.2.1 hR.2 (fun l h => by cases h)
  obtain ⟨D, hD, -⟩ := gen_data (spec_to_minimal hW hd) rfl
  exact ⟨D, hD⟩

theorem kanP2_dataC' {m : ℕ} {Θ : SData m} (hyp : HITHyp2 S (Θ.idx + 1)) : KanP2 S m (dataC Θ) := by
  refine ⟨fun k f A A' hT => ?_, fun k f A A' hT => ?_⟩
  · obtain ⟨D, hD⟩ := data_decl hW hT
    exact kanH2_dataC hW hD hT
  · obtain ⟨D, hD⟩ := data_decl hW hT
    exact kanT2_dataC hW hD hyp hT


end

end Model.Whnf
