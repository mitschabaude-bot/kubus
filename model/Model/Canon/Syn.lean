import Model.Canon.Induct

/-!
# Canonicity: syntactic lemmas on closed terms

Type equality (`TyEq`) is an equivalence stable under interval substitution; the identity
substitution is the identity up to judgmental equality.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' : ℕ}

variable (hW : WfSig S)
include hW

theorem lvl_of_eq {A B : Tm} {l : ℕ} (h : EqTm S k .one [] A B (.univ l)) : l ≤ maxLevel := by
  obtain ⟨hT, hC⟩ := wf_typed _ S rfl hW
  exact (pre_eq (sigClosed_of_wfSig hW) hT hC (spec_to_minimal_eq hW h)).2.2.lvl

theorem lvl_of_ty {A : Tm} {l : ℕ} (h : HasTy S k .one [] A (.univ l)) : l ≤ maxLevel := by
  obtain ⟨hT, hC⟩ := wf_typed _ S rfl hW
  exact (pre_ty (sigClosed_of_wfSig hW) hT hC (spec_to_minimal hW h)).lvl

omit hW in
theorem _root_.KubusCore.EqTm.cumulTo {A B : Tm} {l l' : ℕ} (h : EqTm S k .one [] A B (.univ l)) (hl : l ≤ l')
    (hl' : l' ≤ maxLevel) : EqTm S k .one [] A B (.univ l') := by
  induction l', hl using Nat.le_induction with
  | base => exact h
  | succ n hn ih => exact EqTm.cumul hl' (ih (by omega))

omit hW in
theorem _root_.KubusCore.HasTy.cumulTo {A : Tm} {l l' : ℕ} (h : HasTy S k .one [] A (.univ l)) (hl : l ≤ l')
    (hl' : l' ≤ maxLevel) : HasTy S k .one [] A (.univ l') := by
  induction l', hl using Nat.le_induction with
  | base => exact h
  | succ n hn ih => exact HasTy.cumul hl' (ih (by omega))

omit hW in
theorem TyEq.refl (A : Tm) : TyEq S k A A := .inl rfl

omit hW in
theorem TyEq.symm {A B : Tm} : TyEq S k A B → TyEq S k B A
  | .inl h => .inl h.symm
  | .inr ⟨l, h⟩ => .inr ⟨l, EqTm.symm h⟩

theorem TyEq.trans {A B C : Tm} : TyEq S k A B → TyEq S k B C → TyEq S k A C
  | .inl h, h' => h ▸ h'
  | .inr h, .inl h' => h' ▸ .inr h
  | .inr ⟨l, h⟩, .inr ⟨l', h'⟩ =>
    .inr ⟨max l l', EqTm.trans (h.cumulTo (le_max_left _ _) (max_le (lvl_of_eq hW h) (lvl_of_eq hW h')))
      (h'.cumulTo (le_max_right _ _) (max_le (lvl_of_eq hW h) (lvl_of_eq hW h')))⟩

omit hW in
theorem _root_.KubusCore.HasTy.tyConv {t A B : Tm} (h : HasTy S k .one [] t A) : TyEq S k A B → HasTy S k .one [] t B
  | .inl e => e ▸ h
  | .inr ⟨_, e⟩ => HasTy.conv h e

omit hW in
theorem _root_.KubusCore.EqTm.tyConv {t u A B : Tm} (h : EqTm S k .one [] t u A) : TyEq S k A B → EqTm S k .one [] t u B
  | .inl e => e ▸ h
  | .inr ⟨_, e⟩ => EqTm.conv h e

theorem TyEq.isub {A B : Tm} (σ : ISub k' k) : TyEq S k A B → TyEq S k' (A.isub σ) (B.isub σ)
  | .inl e => .inl (e ▸ rfl)
  | .inr ⟨l, e⟩ => .inr ⟨l, EqTm.isubS hW e σ⟩

/-- The identity substitution is the identity, up to judgmental equality. -/
theorem isub_id_eq {t A : Tm} (ht : HasTy S k .one [] t A) :
    EqTm S k .one [] (t.isub (ISub.id k)) t (A.isub (ISub.id k)) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW ht
  have hw : Wf0 S k .one [] := Wf0.nil trivial
  have k1 : TySub S k .one [] k .one [] Tm.var (ISub.id k).τ :=
    ⟨(ISub.id k).sc, trivial, I.entails_refl _, fun x A h => by simp [Ctx.lookup] at h, hw⟩
  have k2 : TySub S k .one [] k .one [] Tm.var I.var :=
    ⟨fun i hi => by simp [I.Scoped, hi], trivial, I.entails_refl _, fun x A h => by simp [Ctx.lookup] at h, hw⟩
  have kE : EqSub S k [] k .one [] Tm.var (ISub.id k).τ Tm.var I.var :=
    ⟨fun x A h => by simp [Ctx.lookup] at h, fun i hi => by simp [ISub.id, hi]; intro ρ; rfl⟩
  have := minimal_to_spec_eq ((sub_ty hS h0).2.2 k1 k2 kE)
  rwa [subst_var] at this

theorem tyEq_isub_id {A : Tm} (hA : IsTyK S k A) : TyEq S k (A.isub (ISub.id k)) A := by
  obtain ⟨l, hA | rfl⟩ := hA
  · exact .inr ⟨l, isub_id_eq hW hA⟩
  · exact .inl rfl

theorem IsTyK.isub {A : Tm} (hA : IsTyK S k A) (σ : ISub k' k) : IsTyK S k' (A.isub σ) := by
  obtain ⟨l, hA | rfl⟩ := hA
  · exact ⟨l, .inl (HasTy.isubS hW hA σ)⟩
  · exact ⟨l, .inr rfl⟩

omit hW in
theorem IsTyK.of_tyEq {A B : Tm} (hA : IsTyK S k A) : TyEq S k A B → IsTyK S k B
  | .inl e => e ▸ hA
  | .inr ⟨l, e⟩ => ⟨l, .inl (HasTy.eqR e)⟩

/-- Judgmentally equal closed terms have the same value. -/
theorem semK_eq {t u A : Tm} (h : EqTm S k .one [] t u A) : semK S k t = semK S k u :=
  (sound_eq (sigOK_of_wfSig _ S rfl hW) h).2.2 k (idEnv k) (γ0 k) (isPoint_idEnv S k)

theorem semK_tyEq {A B : Tm} : TyEq S k A B → semK S k A = semK S k B
  | .inl e => e ▸ rfl
  | .inr ⟨_, e⟩ => semK_eq hW e

end

end Model.Canon
