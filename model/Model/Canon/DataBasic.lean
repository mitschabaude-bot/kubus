import Model.Canon.GlueBasic

/-!
# Canonicity: inductive types, conversion
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' k'' m : ℕ}

variable (hW : WfSig S)
include hW

/-- Computable elements of an inductive type are closed under judgmental equality. -/
theorem DR.conv {m : ℕ} {d : ℕ} {D : DataDecl} {Mem : (k : ℕ) → Hom k m → Tm → Prop}
    {P : (k : ℕ) → Hom k m → ℕ → ℕ → List V → Tm → Tm → Prop}
    (hMem : ∀ k f t t' A, EqTm S k .one [] t t' A → Mem k f t → Mem k f t')
    {k : ℕ} {f : Hom k m} {A A' t t' : Tm} (h : DR S d D Mem P k f A t) (hA : TyEq S k A A')
    (ht : EqTm S k .one [] t t' A') : DR S d D Mem P k f A' t' := by
  cases h with
  | con hm hC hrs hsc hpl hAeq he hlen hrec hpt =>
    exact DR.con (hMem _ _ _ _ _ (ht.tyConv hA.symm) hm) hC hrs hsc hpl (hA.symm.trans hW hAeq)
      (EqTm.trans (EqTm.symm ht) (he.tyConv hA)) hlen hrec hpt
  | hcomp hm hH hsc hn hpl hAeq he ha hu =>
    exact DR.hcomp (hMem _ _ _ _ _ (ht.tyConv hA.symm) hm) hH hsc hn hpl (hA.symm.trans hW hAeq)
      (EqTm.trans (EqTm.symm ht) (he.tyConv hA)) ha hu

theorem cv_dataC (Θ : SData m) : CV S m (dataC Θ) := by
  intro k f T T' t t'
  rw [Comp_dataC]
  constructor
  · rintro ⟨⟨hT, hsem⟩, ps, hE, rest⟩ hTT'
    exact ⟨⟨hT.of_tyEq hTT', (semK_tyEq hW hTT') ▸ hsem⟩, ps, hTT'.symm.trans hW hE, rest⟩
  · rintro ⟨ht, hmem, -, hdr⟩ hTT' htt'
    have ht' := HasTy.eqR htt'
    refine ⟨ht', mem_of_eq hW htt' hmem, ht', hdr.conv hW (fun k f t t' A e hm => ?_) hTT' htt'⟩
    unfold dataMem at hm ⊢; rwa [← semK_eq hW e]

/-- Computability is closed under judgmental equality, for every well-formed code. -/
theorem cv_wf : ∀ l, l ≤ maxLevel → ∀ m X, WF l m X → CV S m X := by
  refine code_ind _ (fun m => cv_emptyC hW) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro l m A B hA _ _ _ _ _ ihB; exact cv_piC hW (IsKV.ne_empty hA.fib.kv) ihB
  · intro l m A B hA _ _ _ _ ihA ihB; exact cv_sigmaC hW (IsKV.ne_empty hA.fib.kv) ihA ihB
  · intro l m L a0 a1 hL _ _ ihL; exact cv_pathC hW (IsKV.ne_empty hL.fib.kv) ihL
  · intro l m L hL ihL; exact cv_ipiC hW (IsKV.ne_empty hL.fib.kv) ihL
  · intro m l _ ih; exact cv_univC hW ih
  · intro l m A φ Tp ep _ hA hφ _ _ _ hTw hTn _ _ ihA ihT
    exact cv_glueC hW hA.fib.kv hφ hTn (fun k f hh => (hTw k f hh).fib.kv) ihA ihT
  · intro l m Θ _ _ _ _ _; exact cv_dataC hW Θ

theorem cv_tyCode {m : ℕ} {X : V} (hX : TyCode m X) : CV S m X := by
  obtain ⟨l, hl, (⟨hX, -⟩ | rfl)⟩ := hX
  · exact cv_wf hW l hl m X hX
  · exact cv_univC hW fun m' X hX => cv_wf hW l hl m' X hX

end

end Model.Canon
