import Model.DataOKProof

/-!
# Well-formed signatures are semantically valid
-/

set_option autoImplicit false

namespace Model

open KubusCore

theorem take_take_eq {S : Sig} {k j : ℕ} (hj : j ≤ k) : (S.take k).take j = S.take j := by
  rw [List.take_take, Nat.min_eq_left hj]

/-- A well-formed signature is semantically valid. -/
theorem sigOK_of_wfSig : ∀ (n : ℕ) (S : Sig), S.length = n → WfSig S → SigOK S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS
    refine ⟨fun k t A hk => ?_, fun k D hk => ?_⟩
    swap
    · have hklt : k < S.length := (List.getElem?_eq_some_iff.1 hk).1
      have hwf := hS.2 k D hk
      have htake : WfSig (S.take k) := by
        refine ⟨fun j t' A' hj => ?_, fun j D' hj => ?_⟩
        · have hjk : j < k := by
            have := (List.getElem?_eq_some_iff.1 hj).1
            simpa [List.length_take, hklt.le] using this
          rw [List.getElem?_take_of_lt hjk] at hj
          have := hS.1 j t' A' hj
          rwa [take_take_eq hjk.le]
        · have hjk : j < k := by
            have := (List.getElem?_eq_some_iff.1 hj).1
            simpa [List.length_take, hklt.le] using this
          rw [List.getElem?_take_of_lt hjk] at hj
          have := hS.2 j D' hj
          rwa [take_take_eq (by omega)]
      have hok : SigOK (S.take k) := ih _ (by rw [← hn, List.length_take]; omega) _ rfl htake
      have hlen : (S.take k).length = k := by simp; omega
      have hd := dataOK_decl (S.take k) hok D (by rw [hlen]; exact hwf)
      rw [hlen] at hd
      unfold DataOK at hd ⊢
      have e1 : sigUpTo (S.take k ++ [Entry.data D]) k = sigUpTo S k := by
        have := sigUpTo_ext (S.take k) D
        rw [hlen] at this
        rw [this, sigV_take hklt.le]
      rwa [e1] at hd
    have hklt : k < S.length := (List.getElem?_eq_some_iff.1 hk).1
    have hwf := hS.1 k t A hk
    have htake : WfSig (S.take k) := by
      refine ⟨fun j t' A' hj => ?_, fun j D' hj => ?_⟩
      · have hjk : j < k := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simpa [List.length_take, hklt.le] using this
        rw [List.getElem?_take_of_lt hjk] at hj
        have := hS.1 j t' A' hj
        rwa [take_take_eq hjk.le]
      · have hjk : j < k := by
          have := (List.getElem?_eq_some_iff.1 hj).1
          simpa [List.length_take, hklt.le] using this
        rw [List.getElem?_take_of_lt hjk] at hj
        have := hS.2 j D' hj
        rwa [take_take_eq (by omega)]
    have hok : SigOK (S.take k) := ih _ (by rw [← hn, List.length_take]; omega) _ rfl htake
    exact ⟨hwf.1, hwf.2.1, sound_ty hok hwf.2.2.2⟩

end Model
