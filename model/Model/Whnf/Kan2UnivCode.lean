import Model.Whnf.Kan2UnivH

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} (hW : WfSig S)
include hW

/-- The universe code is Kan; its elements carry their own Kan operations. -/
theorem kanP2_univC {m l : ℕ} : KanP2 S m (univC m l) := by
  refine ⟨fun k f A A' hT => ?_, fun k f A A' hT => ?_⟩
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_univC] at hT
    have hR := hT.2 k (ISub.id k)
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    exact kanH2_univ hW hTT hR.1
  · have hTT := Comp2_ty_RT2 hT
    have hb := Comp2_ty_base hT
    rw [Comp2_univC] at hT
    have hR := hT.2 (k + 1) (ISub.id (k + 1))
    rw [isub_id_of_closed (closed_of_isTyK hW hb.2.1)] at hR
    exact kanT2_univ hW hTT hR.1



end

end Model.Whnf
