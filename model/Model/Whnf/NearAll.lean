import Model.Whnf.NearData

/-!
# The binary relation is invariant under near terms at every code

`ni2_wf`: by induction on well-formed codes, assuming `NearTy S` (typed closed terms are judgmentally
equal to the closed terms near them). Corollaries for the relations of types (`RT2_near`, `RE2_near`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} (hW : WfSig S) (hN : NearTy S)
include hW hN

theorem ni2_wf : ∀ l, l ≤ maxLevel → ∀ m X, WF l m X → NI2 S m X := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ihl =>
  intro hl m X hX
  induction hX with
  | empty => exact ni2_emptyC hW hN
  | pi hA hB hBf hBw hBn ihA ihB =>
    have hAne := IsKV.ne_empty (show WF l _ _ from hA).fib.kv
    have perA := per2_wf hW l hl _ _ hA
    have perB := fun k f a ha => per2_wf hW l hl _ _ (hBw k f a ha)
    intro k f T T' T'' t t' t''
    exact ⟨fun h hn hT => niTy_piC hW hN hAne perA ihA perB ihB h hn hT,
      fun hTT h hn hu => niEl_piC hW hN hAne perB ihB hTT h hn hu⟩
  | sigma hA hB hBf hBw hBn ihA ihB =>
    have hAne := IsKV.ne_empty (show WF l _ _ from hA).fib.kv
    have perA := per2_wf hW l hl _ _ hA
    have perB := fun k f a ha => per2_wf hW l hl _ _ (hBw k f a ha)
    intro k f T T' T'' t t' t''
    exact ⟨fun h hn hT => niTy_sigmaC hW hN hAne perA ihA perB ihB h hn hT,
      fun hTT h hn hu => niEl_sigmaC hW hN hAne perA ihA perB ihB hTT h hn hu⟩
  | path hL h0 h1 ihL =>
    have hLne := IsKV.ne_empty (show WF l _ _ from hL).fib.kv
    have perL := per2_wf hW l hl _ _ hL
    intro k f T T' T'' t t' t''
    exact ⟨fun h hn hT => niTy_pathC hW hN hLne perL ihL h hn hT,
      fun hTT h hn hu => niEl_pathC hW hN hLne perL ihL hTT h hn hu⟩
  | ipi hL ihL =>
    have hLne := IsKV.ne_empty (show WF l _ _ from hL).fib.kv
    have perL := per2_wf hW l hl _ _ hL
    intro k f T T' T'' t t' t''
    exact ⟨fun h hn hT => niTy_ipiC hW hN hLne perL ihL h hn hT,
      fun hTT h hn hu => niEl_ipiC hW hN hLne perL ihL hTT h hn hu⟩
  | @univ m l' hl' =>
    show NI2 S m (Ucodes l m l')
    rw [Ucodes_lt m hl']
    exact ni2_univC hW hN fun m' X hX => ihl l' hl' (by omega) m' X hX
  | glue hA hφ hn hTp hep hTw hTn hem hen ihA ihT =>
    have perA := per2_wf hW l hl _ _ hA
    have krA := kr2_wf hW l hl _ _ hA
    have perT := fun k f hh => per2_wf hW l hl _ _ (hTw k f hh)
    have krT := fun k f hh => kr2_wf hW l hl _ _ (hTw k f hh)
    intro k f T T' T'' t t' t''
    exact ⟨fun h hn hT => niTy_glueC hW hN perA krA ihA perT krT ihT f (show WF l _ _ from hA).fib.kv hφ hTn
        (fun k f hh => (show WF l _ _ from hTw k f hh).fib.kv) h hn hT,
      fun hTT h hn hu => niEl_glueC hW hN perA krA ihA perT krT ihT f (show WF l _ _ from hA).fib.kv hφ hTn
        (fun k f hh => (show WF l _ _ from hTw k f hh).fib.kv) hTT h hn hu⟩
  | data Θ hc hw hp ih ihp =>
    exact ni2_dataC hW hN (fun c j n g pre hv => per2_wf hW l hl _ _ (hw c j n g pre hv))
      (fun n g j t X e => per2_wf hW l hl _ _ (hp n g j t X e)) ih ihp

theorem ni2_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : NI2 S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact ni2_wf hW hN l hl m X hX
  · exact ni2_univC hW hN fun m' X hX => ni2_wf hW hN l hl m' X hX

/-- A type related to `A'` is related to every typed type near `A'`. -/
theorem RT2_near {k : ℕ} {A A' A'' : Tm} (hX : TyCode k (semK S k A)) (h : RT2 S k A A') (hn : TmNear A' A'')
    (hA : IsTyK S k A'') : RT2 S k A A'' :=
  (ni2_tyCode hW hN hX k (Hom.id k) A A' A'' A A A).1 h hn hA

/-- An element related to `t'` is related to every typed term near `t'`. -/
theorem RE2_near {k : ℕ} {A t t' t'' : Tm} (hAA : RT2 S k A A) (h : RE2 S k A t t') (hn : TmNear t' t'')
    (hu : HasTy S k .one [] t'' A) : RE2 S k A t t'' :=
  (ni2_tyCode hW hN (tyCode_of_ty hW hu) k (Hom.id k) A A A t t' t'').2 hAA h hn hu

end

end Model.Whnf
