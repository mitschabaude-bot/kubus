import Model.Whnf.CSub2

/-!
# Closed expansion and reduction lemmas
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

omit hW in
theorem isub_lam (A1 b : Tm) (σ : ISub k' k) : (Tm.lam A1 b).isub σ = .lam (A1.isub σ) (b.isub σ) := by
  simp only [Tm.isub, Tm.subst, up_var]

/-- β-reduction of a closed application, at every restriction. -/
theorem stable_beta {X A1 b a : Tm} (hty : HasTy S k .one [] (.app (.lam A1 b) a) X) :
    StableE S k X (.app (.lam A1 b) a) (b.inst a) := by
  intro k' σ
  have hσ := HasTy.isubS hW hty σ
  rw [isub_app, isub_lam] at hσ ⊢
  rw [isub_inst]
  exact ⟨.step (by simp [step]) (.refl _), EqTm.piBeta hσ⟩

/-- Expansion on both sides, at the level of `RE2`. -/
theorem RE2.expand2 {A t t' u u' : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A) (hs : StableE S k A t u) (hs' : StableE S k A t' u') (h : RE2 S k A u u') :
    RE2 S k A t t' :=
  el_expandS2 hW (RE2.tyCode hW h) hAA ht ht' (RE2.typed h).1 hs hs' h

/-- Reduction on the right, at the level of `RE2`. -/
theorem RE2.reduceR {A t t' u' : Tm} (hAA : RT2 S k A A) (h : RE2 S k A t t') (hs : StableE S k A t' u')
    (hu : HasTy S k .one [] u' A) : RE2 S k A t u' :=
  el_reduceSR hW (RE2.tyCode hW h) hAA h hs hu

/-- Reduction on the left, at the level of `RE2`. -/
theorem RE2.reduceL {A t t' u : Tm} (hAA : RT2 S k A A) (h : RE2 S k A t t') (hs : StableE S k A t u)
    (hu : HasTy S k .one [] u A) : RE2 S k A u t' :=
  el_reduceSL hW (RE2.tyCode hW h) hAA h hs hu

/-- Expansion on the right, at the level of `RE2`. -/
theorem RE2.expandR {A t t' u' : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A) (hs : StableE S k A t' u') (h : RE2 S k A t u') : RE2 S k A t t' :=
  el_expandSR hW (RE2.tyCode hW h) hAA ht ht' hs h

theorem stable_fstBeta {X a b : Tm} (hty : HasTy S k .one [] (.fst (.pair a b)) X) :
    StableE S k X (.fst (.pair a b)) a := fun k' σ => by
  have hσ : HasTy S k' .one [] (.fst (.pair (a.isub σ) (b.isub σ))) (X.isub σ) := HasTy.isubS hW hty σ
  show Red S (.fst (.pair (a.isub σ) (b.isub σ))) _ ∧ _
  exact ⟨.step (by simp [step]) (.refl _), EqTm.fstBeta hσ⟩

theorem stable_sndBeta {X a b : Tm} (hty : HasTy S k .one [] (.snd (.pair a b)) X) :
    StableE S k X (.snd (.pair a b)) b := fun k' σ => by
  have hσ : HasTy S k' .one [] (.snd (.pair (a.isub σ) (b.isub σ))) (X.isub σ) := HasTy.isubS hW hty σ
  show Red S (.snd (.pair (a.isub σ) (b.isub σ))) _ ∧ _
  exact ⟨.step (by simp [step]) (.refl _), EqTm.sndBeta hσ⟩

omit hW in
theorem isub_plam (t : Tm) (σ : ISub k' k) : (Tm.plam t).isub σ = .plam (t.isub σ.up) := rfl

theorem stable_pathBeta {X t : Tm} {r : I} (hty : HasTy S k .one [] (.papp (.plam t) r) X) :
    StableE S k X (.papp (.plam t) r) (t.dinst r) := by
  intro k' σ
  have hσ := HasTy.isubS hW hty σ
  rw [isub_papp, isub_plam] at hσ ⊢
  rw [isub_dinst]
  exact ⟨.step (by simp [step]) (.refl _), EqTm.pathBeta hσ⟩

/-- Expansion on the left, at the level of `RE2`. -/
theorem RE2.expandL {A t t' u : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A) (hs : StableE S k A t u) (h : RE2 S k A u t') : RE2 S k A t t' :=
  el_expandS hW (RE2.tyCode hW h) hAA ht ht' hs h

/-- Head expansion with a reduct chosen at each restriction. -/
theorem RE2.expandH {A t t' : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A) (ht' : HasTy S k .one [] t' A)
    (h : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (A.isub σ) ∧
      RE2 S k' (A.isub σ) u (t'.isub σ)) : RE2 S k A t t' := by
  have hb := Comp2_ty_base hAA
  refine (he2_tyCode hW (tyCode_of_ty hW ht) k (Hom.id k) A A t t').2 hAA ht ht' fun k' σ => ?_
  obtain ⟨u, h1, h2, h3⟩ := h k' σ
  refine ⟨u, h1, h2, ?_⟩
  rw [Hom.id_comp, Comp2_eq_res hb.1, ← semK_isubTy hW hb.2.1 σ]
  exact h3

omit hW in
/-- The disjunction property of faces at the generic point of a stage. -/
theorem ent_or_cases {φ ψ : I} (hφ : φ.Scoped k) (hψ : ψ.Scoped k) (h : I.Entails .one (.or φ ψ)) :
    I.Entails .one φ ∨ I.Entails .one ψ := by
  have hh := entails_holds h (ρ := idEnv k) (by rw [ival_one]; rfl)
  rcases holds_or hh with h1 | h1
  · exact .inl (entails_of_holds hφ h1)
  · exact .inr (entails_of_holds hψ h1)

omit hW in
theorem ent_one_subst {φ : I} (h : I.Entails .one φ) (τ : ℕ → I) : I.Entails .one (φ.subst τ) :=
  ent_subst h τ

theorem stable_splitL {X t u : Tm} {φ ψ : I} (hφ : I.Entails .one φ)
    (hsp : HasTy S k .one [] (.split φ t ψ u) X) : StableE S k X (.split φ t ψ u) t := by
  intro k' σ
  have hσ : HasTy S k' .one [] (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) (X.isub σ) :=
    HasTy.isubS hW hsp σ
  have hφσ := ent_one_subst hφ σ.τ
  refine ⟨.step ?_ (.refl _), EqTm.splitL hφσ hσ⟩
  show step S (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) = some (t.isub σ)
  simp only [step, show I.entails .one (φ.subst σ.τ) = true from hφσ, if_true]

omit hW in
theorem eta_body (f a : Tm) (γ : ℕ → Tm) (τ : ℕ → I) (σ : ISub k' k) :
    (((Tm.app f.shift (.var 0)).subst (Tm.up γ) τ).isub σ).inst a = .app ((f.subst γ τ).isub σ) a := by
  rw [subst_up_isub_inst, subst_isub2]
  simp only [Tm.subst, shift_consT]
  rfl

omit hW in
theorem peta_body (p : Tm) (γ : ℕ → Tm) (τ : ℕ → I) (σ : ISub k' k) (r : I) :
    (((Tm.papp p.dshift (.var 0)).subst (dupS γ) (I.up τ)).isub σ.up).dinst r =
      .papp ((p.subst γ τ).isub σ) r := by
  have e : ((Tm.papp p.dshift (.var 0)).subst (dupS γ) (I.up τ)).isub σ.up =
      (Tm.papp p.dshift (.var 0)).subst (dupS fun x => (γ x).isub σ) (I.up fun i => (τ i).subst σ.τ) := by
    simp only [Tm.isub, subst_subst, ISub.up]
    apply subst_congr
    · intro x; exact isub_dshift (γ x) σ
    · intro i; exact I_up_comp _ _ i
  rw [e, dup_dinst, subst_isub2]
  simp only [Tm.subst, dshift_consI]
  rfl

/-- A system is related to `x` if each branch is, wherever its face holds. -/
theorem RE2_split_l {A x t u : Tm} {φ ψ : I} (hφ : φ.Scoped k) (hψ : ψ.Scoped k)
    (hor : I.Entails .one (.or φ ψ)) (hAA : RT2 S k A A) (hsp : HasTy S k .one [] (.split φ t ψ u) A)
    (hx : HasTy S k .one [] x A)
    (ht : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → RE2 S k' (A.isub σ) (t.isub σ) (x.isub σ))
    (hu : ∀ k' (σ : ISub k' k), I.Entails .one (ψ.subst σ.τ) → RE2 S k' (A.isub σ) (u.isub σ) (x.isub σ)) :
    RE2 S k A (.split φ t ψ u) x := by
  refine RE2.expandH hW hAA hsp hx fun k' σ => ?_
  have hσ : HasTy S k' .one [] (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) (A.isub σ) :=
    HasTy.isubS hW hsp σ
  show ∃ u', Red S (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) u' ∧ _
  by_cases hφσ : I.Entails .one (φ.subst σ.τ)
  · refine ⟨t.isub σ, .step ?_ (.refl _), EqTm.splitL hφσ hσ, ht k' σ hφσ⟩
    simp only [step, show I.entails .one (φ.subst σ.τ) = true from hφσ, if_true]
  · have hψσ : I.Entails .one (ψ.subst σ.τ) := by
      rcases ent_or_cases (I.scoped_subst hφ σ.sc) (I.scoped_subst hψ σ.sc) (ent_one_subst hor σ.τ) with h | h
      · exact absurd h hφσ
      · exact h
    refine ⟨u.isub σ, .step ?_ (.refl _), EqTm.splitR hψσ hσ, hu k' σ hψσ⟩
    have hf : I.entails .one (φ.subst σ.τ) = false := by
      cases e : I.entails .one (φ.subst σ.τ)
      · rfl
      · exact absurd e hφσ
    simp only [step, hf, show I.entails .one (ψ.subst σ.τ) = true from hψσ, if_true, Bool.false_eq_true, if_false]

theorem RE2_split_r {A x t u : Tm} {φ ψ : I} (hφ : φ.Scoped k) (hψ : ψ.Scoped k)
    (hor : I.Entails .one (.or φ ψ)) (hAA : RT2 S k A A) (hsp : HasTy S k .one [] (.split φ t ψ u) A)
    (hx : HasTy S k .one [] x A)
    (ht : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → RE2 S k' (A.isub σ) (x.isub σ) (t.isub σ))
    (hu : ∀ k' (σ : ISub k' k), I.Entails .one (ψ.subst σ.τ) → RE2 S k' (A.isub σ) (x.isub σ) (u.isub σ)) :
    RE2 S k A x (.split φ t ψ u) := by
  have hX := tyCode_of_ty hW hx
  refine RE2.symm hW hAA (RE2_split_l hW hφ hψ hor hAA hsp hx (fun k' σ h => ?_) (fun k' σ h => ?_))
  · exact RE2.symm hW (RT2.isub hW hX hAA σ) (ht k' σ h)
  · exact RE2.symm hW (RT2.isub hW hX hAA σ) (hu k' σ h)

omit hW in
theorem ent_comp {k'' : ℕ} {φ : I} {ρ : ISub k' k} {ρ' : ISub k'' k'} (h : I.Entails .one (φ.subst ρ.τ)) :
    I.Entails .one (φ.subst (ρ.comp ρ').τ) := by
  have := ent_one_subst h ρ'.τ
  rw [I_subst_subst] at this; exact this

omit hW in
theorem ent_comp_inv {k'' : ℕ} {φ : I} {ρ : ISub k' k} {ρ' : ISub k'' k'} (h : I.Entails .one ((φ.subst ρ.τ).subst ρ'.τ)) :
    I.Entails .one (φ.subst (ρ.comp ρ').τ) := by
  rw [I_subst_subst] at h; exact h

omit hW in
theorem tyHead_subst {X : Tm} {h : ℕ × ℕ} (hX : X.tyHead = some h) (γ : ℕ → Tm) (τ : ℕ → I) :
    (X.subst γ τ).tyHead = some h := by
  cases X <;> simp_all [Tm.tyHead, Tm.subst]

/-- Judgmentally equal closed types have the same head. -/
theorem tyHead_eq_of_eq {X Y : Tm} {l : ℕ} {hx hy : ℕ × ℕ} (hX : X.tyHead = some hx) (hY : Y.tyHead = some hy)
    (he : EqTm S k .one [] X Y (.univ l)) : hx = hy := by
  have hok := sigOK_of_wfSig _ S rfl hW
  have hs := sound_eq hok he
  have hp := isPoint_idEnv S k
  have e := codeHead_sem hs.1 hX hp
  rw [hs.2.2 k (idEnv k) (γ0 k) hp, codeHead_sem hs.2.1 hY hp] at e
  have fx := tyHead_facts hX; have fy := tyHead_facts hY
  exact (headEnc_inj fy.1 fx.1 fy.2 fx.2 e).symm

omit hW in
theorem closed0_subst {t : Tm} (h : t.closedB 0 0 = true) (γ : ℕ → Tm) (τ : ℕ → I) : t.subst γ τ = t :=
  closed_subst_id h (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => absurd hi (Nat.not_lt_zero _))

theorem stable_delta {i : ℕ} {t A : Tm} (hd : S[i]? = some (.defn t A)) (hty : HasTy S k .one [] (.const i) A) :
    StableE S k A (.const i) t := by
  obtain ⟨htc, hAc, -, -⟩ := hW.1 i t A hd
  intro k' σ
  have hσ := HasTy.isubS hW hty σ
  have ht : t.isub σ = t := closed0_subst htc _ _
  have hA : A.isub σ = A := closed0_subst hAc _ _
  rw [hA] at hσ
  show Red S (.const i) (t.isub σ) ∧ EqTm S k' .one [] (.const i) (t.isub σ) (A.isub σ)
  rw [ht, hA]
  exact ⟨.step (by simp [step, hd]) (.refl _), EqTm.delta hσ hd⟩

end

end Model.Whnf
