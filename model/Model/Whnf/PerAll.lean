import Model.Whnf.RC2

/-!
# The binary relation is Kripke, a partial equivalence and closed under local head expansion at every code
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig}

variable (hW : WfSig S)
include hW

theorem kr2_per2_he2_wf : ∀ l, l ≤ maxLevel → ∀ m X, WF l m X → KR2 S m X ∧ PER2 S m X ∧ HE2 S m X ∧ RC2 S m X := by
  intro l hl
  refine code_ind _ (fun m => ⟨kr2_emptyC hW, per2_emptyC hW, he2_emptyC hW, rc2_emptyC hW⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ l hl
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    have hAne := IsKV.ne_empty hA.fib.kv
    have krX := kr2_piC hW (WF.fib (show WF l m (piC m A B) from WFI.pi hA hB hBf hBw hBn)) hAne
    have perB := fun k f a ha => (ihB k f a ha).2.1
    have hBne := fun k f a ha => IsKV.ne_empty (hBw k f a ha).fib.kv
    refine ⟨krX, per2_piC hW hAne ihA.2.1 perB, fun k f T T' t t' => ?_, fun k f T T' B' t t' u' => ?_⟩
    · exact ⟨heTy_piC hAne hW ihA.2.1 krX perB,
        heEl_piC hAne hW ihA.2.1 perB ihA.1 hBne hBn fun k f a ha => (ihB k f a ha).2.2.1⟩
    · exact ⟨rcTy_piC hW hAne, rcEl_piC hW hAne (fun k f a ha => (ihB k f a ha).2.2.2) perB⟩
  · intro l m A B hA hB hBf hBw hBn ihA ihB
    have hAne := IsKV.ne_empty hA.fib.kv
    have krX := kr2_sigmaC hW (WF.fib (show WF l m (sigmaC m A B) from WFI.sigma hA hB hBf hBw hBn)) hAne
    have perB := fun k f a ha => (ihB k f a ha).2.1
    have hBne := fun k f a ha => IsKV.ne_empty (hBw k f a ha).fib.kv
    refine ⟨krX, per2_sigmaC hW hAne ihA.2.1 perB, fun k f T T' t t' => ?_, fun k f T T' B' t t' u' => ?_⟩
    · exact ⟨heTy_sigmaC hAne hW ihA.2.1 krX perB,
        heEl_sigmaC hAne hW ihA.2.1 perB ihA.1 ihA.2.2.1 hBne hBn fun k f a ha => (ihB k f a ha).2.2.1⟩
    · exact ⟨rcTy_sigmaC hW hAne, rcEl_sigmaC hW hAne ihA.2.2.2 ihA.2.1
        (fun k f a ha => (ihB k f a ha).2.2.2) perB⟩
  · intro l m L a0 a1 hL h0 h1 ihL
    have hLne := IsKV.ne_empty hL.fib.kv
    have krX := kr2_pathC hW (WF.fib (show WF l m (pathC m L a0 a1) from WFI.path hL h0 h1)) hLne
    have perX := per2_pathC hW hLne ihL.1 ihL.2.1 (a0 := a0) (a1 := a1)
    refine ⟨krX, perX, fun k f T T' t t' => ?_, fun k f T T' B' t t' u' => ?_⟩
    · exact ⟨heTy_pathC hLne hW ihL.2.1 krX, heEl_pathC hLne hW ihL.2.1 ihL.1 ihL.2.2.1 perX krX⟩
    · exact ⟨rcTy_pathC hW hLne, rcEl_pathC hW hLne ihL.2.2.2 ihL.2.1⟩
  · intro l m L hL ihL
    have hLne := IsKV.ne_empty hL.fib.kv
    have krX := kr2_ipiC hW (WF.fib (show WF l m (ipiC m L) from WFI.ipi hL)) hLne
    refine ⟨krX, per2_ipiC hW hLne ihL.1 ihL.2.1, fun k f T T' t t' => ?_, fun k f T T' B' t t' u' => ?_⟩
    · exact ⟨heTy_ipiC hLne hW ihL.2.1 krX, heEl_ipiC hLne hW ihL.2.1 ihL.1 ihL.2.2.1⟩
    · exact ⟨rcTy_ipiC hW hLne, rcEl_ipiC hW hLne ihL.2.2.2 ihL.2.1⟩
  · intro m l _ ih
    exact ⟨kr2_univC hW fun m' X hX => (ih m' X hX).1, per2_univC hW fun m' X hX => (ih m' X hX).2.1,
      he2_univC hW (fun m' X hX => (ih m' X hX).2.2.1), rc2_univC hW fun m' X hX => (ih m' X hX).2.2.2⟩
  · intro l m A φ Tp ep hl hA hφ hn hTp hep hTw hTn hem hen ihA ihT
    have krX := kr2_glueC hW hA.fib.kv hφ hTn hTw
      (WF.fib (show WF l m (glueC m A φ Tp ep) from WFI.glue hA hφ hn hTp hep hTw hTn hem hen))
      (fun k f hh => (ihT k f hh).1)
    exact ⟨krX,
      per2_glueC hW hA.fib.kv hφ hTn (fun k f hh => (hTw k f hh).fib.kv) ihA.2.1 ihA.1 (fun k f hh => (ihT k f hh).2.1)
        (fun k f hh => (ihT k f hh).1),
      he2_glueC hW hA.fib.kv hφ hTn (fun k f hh => (hTw k f hh).fib.kv) (fun k f hh => (ihT k f hh).2.2.1)
        ihA.2.1 ihA.1 (fun k f hh => (ihT k f hh).2.1) (fun k f hh => (ihT k f hh).1) krX,
      rc2_glueC hW hA.fib.kv hφ hTn (fun k f hh => (hTw k f hh).fib.kv) (fun k f hh => (ihT k f hh).2.2.2)⟩
  · intro l m Θ hc hw hpw ih ihp
    exact ⟨kr2_dataC hW (WF.fib (show WF l m (dataC Θ) from WFI.data Θ hc hw hpw)), per2_dataC hW (fun c j n g pre hp =>
      (ih c j n g pre hp).2.1) (fun n g j t X e => (ihp n g j t X e).2.1), he2_dataC hW (fun h c j pre => perP_tyLook (fun c j n g pre hp =>
      (ih c j n g pre hp).2.1) h c j pre) (fun n g j t X e => (ihp n g j t X e).2.1), rc2_dataC hW⟩

theorem per2_wf (l : ℕ) (hl : l ≤ maxLevel) (m : ℕ) (X : V) (hX : WF l m X) : PER2 S m X :=
  (kr2_per2_he2_wf hW l hl m X hX).2.1

theorem per2_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : PER2 S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact per2_wf hW l hl m X hX
  · exact per2_univC hW fun m' X hX => per2_wf hW l hl m' X hX

theorem he2_wf (l : ℕ) (hl : l ≤ maxLevel) (m : ℕ) (X : V) (hX : WF l m X) : HE2 S m X :=
  (kr2_per2_he2_wf hW l hl m X hX).2.2.1

theorem rc2_wf (l : ℕ) (hl : l ≤ maxLevel) (m : ℕ) (X : V) (hX : WF l m X) : RC2 S m X :=
  (kr2_per2_he2_wf hW l hl m X hX).2.2.2

theorem rc2_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : RC2 S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact rc2_wf hW l hl m X hX
  · exact rc2_univC hW fun m' X hX => rc2_wf hW l hl m' X hX

theorem he2_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : HE2 S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact he2_wf hW l hl m X hX
  · exact he2_univC hW fun m' X hX => he2_wf hW l hl m' X hX

end

end Model.Whnf
