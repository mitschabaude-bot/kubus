import Model.Whnf.PerData

/-!
# The binary relation is a partial equivalence at every code
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig}

variable (hW : WfSig S)
include hW

theorem kr2_per2_wf : ∀ l, l ≤ maxLevel → ∀ m X, WF l m X → KR2 S m X ∧ PER2 S m X := by
  intro l hl
  refine code_ind _ (fun m => ⟨kr2_emptyC hW, per2_emptyC hW⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ l hl
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact ⟨kr2_piC hW (WF.fib (show WF l m (piC m A B) from WFI.pi hA hB hBf hBw hBn)) (IsKV.ne_empty hA.fib.kv),
      per2_piC hW (IsKV.ne_empty hA.fib.kv) ihA.2 fun k f a ha => (ihB k f a ha).2⟩
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact ⟨kr2_sigmaC hW (WF.fib (show WF l m (sigmaC m A B) from WFI.sigma hA hB hBf hBw hBn))
        (IsKV.ne_empty hA.fib.kv),
      per2_sigmaC hW (IsKV.ne_empty hA.fib.kv) ihA.2 fun k f a ha => (ihB k f a ha).2⟩
  · intro l m L a0 a1 hL h0 h1 ihL
    exact ⟨kr2_pathC hW (WF.fib (show WF l m (pathC m L a0 a1) from WFI.path hL h0 h1)) (IsKV.ne_empty hL.fib.kv),
      per2_pathC hW (IsKV.ne_empty hL.fib.kv) ihL.1 ihL.2⟩
  · intro l m L hL ihL
    exact ⟨kr2_ipiC hW (WF.fib (show WF l m (ipiC m L) from WFI.ipi hL)) (IsKV.ne_empty hL.fib.kv),
      per2_ipiC hW (IsKV.ne_empty hL.fib.kv) ihL.1 ihL.2⟩
  · intro m l _ ih
    exact ⟨kr2_univC hW fun m' X hX => (ih m' X hX).1, per2_univC hW fun m' X hX => (ih m' X hX).2⟩
  · intro l m A φ Tp ep hl hA hφ hn hTp hep hTw hTn hem hen ihA ihT
    exact ⟨kr2_glueC hW hA.fib.kv hφ hTn hTw
        (WF.fib (show WF l m (glueC m A φ Tp ep) from WFI.glue hA hφ hn hTp hep hTw hTn hem hen))
        (fun k f hh => (ihT k f hh).1),
      per2_glueC hW hA.fib.kv hφ hTn (fun k f hh => (hTw k f hh).fib.kv) ihA.2 ihA.1 (fun k f hh => (ihT k f hh).2)
        (fun k f hh => (ihT k f hh).1)⟩
  · intro l m Θ hc hw ih
    exact ⟨kr2_dataC hW (WF.fib (show WF l m (dataC Θ) from WFI.data Θ hc hw)), per2_dataC hW fun c j n g pre hp =>
      (ih c j n g pre hp).2⟩

theorem per2_wf (l : ℕ) (hl : l ≤ maxLevel) (m : ℕ) (X : V) (hX : WF l m X) : PER2 S m X :=
  (kr2_per2_wf hW l hl m X hX).2

theorem per2_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : PER2 S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact per2_wf hW l hl m X hX
  · exact per2_univC hW fun m' X hX => per2_wf hW l hl m' X hX

end

end Model.Whnf
