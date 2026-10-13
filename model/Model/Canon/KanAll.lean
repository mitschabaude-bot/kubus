import Model.Canon.KanGlue

/-!
# Canonicity: all codes are Kan

By induction on the code of the type (`tyCode_ind`), one lemma per type former. The universe and
Glue cases use the fundamental lemma on Kan-free terms (or terms whose Kan operations are at types
covered by the induction hypothesis).
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

variable (hW : WfSig S) (hGC : GlueCompat S)
include hW hGC

theorem kanP_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : KanP S m X := by
  refine (tyCode_ind (fun m X => KR S m X ∧ KanP S m X) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ m X hX).2
  · exact fun m => ⟨kr_emptyC hW, kanP_empty hW m⟩
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact ⟨kr_piC hW (WF.fib (show WF l m (piC m A B) from WFI.pi hA hB hBf hBw hBn)) (IsKV.ne_empty hA.fib.kv),
      kanP_pi hW l m A B hA ihA.2 fun k f a ha => (ihB k f a ha).2⟩
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    exact ⟨kr_sigmaC hW (WF.fib (show WF l m (sigmaC m A B) from WFI.sigma hA hB hBf hBw hBn))
      (IsKV.ne_empty hA.fib.kv), kanP_sigma hW l m A B hA ihA ihB⟩
  · intro l m L a0 a1 hL h0 h1 ihL
    exact ⟨kr_pathC hW (WF.fib (show WF l m (pathC m L a0 a1) from WFI.path hL h0 h1)) (IsKV.ne_empty hL.fib.kv),
      kanP_path hW m L a0 a1 (IsKV.ne_empty hL.fib.kv) ihL.1 ihL.2⟩
  · intro l m L hL ihL
    exact ⟨kr_ipiC hW (WF.fib (show WF l m (ipiC m L) from WFI.ipi hL)) (IsKV.ne_empty hL.fib.kv),
      kanP_ipi hW m L (IsKV.ne_empty hL.fib.kv) ihL.1 ihL.2⟩
  · intro m l _ ih
    exact ⟨kr_univC hW fun m' X h => (ih m' X h).1, kanP_univ hW hGC ih⟩
  · intro l m A φ Tp ep hl hAw hφ hn hTpE hepE hTw hTn hem hen ihA ihT
    have hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f) := fun k f hh => (hTw k f hh).fib.kv
    exact ⟨kr_glueC hW hAw.fib.kv hφ hTn hTw hl
      (WF.fib (show WF l m (glueC m A φ Tp ep) from WFI.glue hAw hφ hn hTpE hepE hTw hTn hem hen))
      (fun k f hh => (ihT k f hh).1),
      kanP_glue hW hGC hAw.fib.kv hφ hTn hTkv ihA.1 ihA.2 ihT⟩
  · intro l m Θ hc hw ih
    have hΘ : Θ.Good := { hc with fib := fun c j n g pre hp => (hw c j n g pre hp).fib }
    have hKR := kr_dataC hW hΘ (WF.fib (show WF l m (dataC Θ) from WFI.data Θ hc hw)) (fun c j n g pre hp => (ih c j n g pre hp).1)
    exact ⟨hKR, kanP_data hW hΘ ih hKR⟩

theorem kanOracle : KanOracle S := fun _ _ hX => kanP_tyCode hW hGC hX

end

end Model.Canon
