import Model.Whnf.Kan2Comp

/-!
# The binary composition at Σ-types: second projections
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- The first projection of a composition whose face holds, stably. -/
theorem stable_fst_hcompFace {X Y T u a : Tm} {φ : I} (h : I.Entails .one φ)
    (hty : HasTy S k .one [] (.hcomp T φ u a) T) (hT : TyEq S k T (.sigma X Y)) :
    StableE S k X (.fst (.hcomp T φ u a)) (.fst (u.dinst .one)) := by
  intro k' σ
  have hσ : I.Entails .one (φ.subst σ.τ) := by have := ent_subst h σ.τ; simpa [I.subst] using this
  have hty' : HasTy S k' .one [] (.hcomp (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ)) (T.isub σ) :=
    HasTy.isubS hW hty σ
  have e := hT.isub hW σ
  rw [isub_sigma] at e
  have e1 : (u.dinst .one).isub σ = (u.isub σ.up).dinst .one := by rw [isub_dinst]; rfl
  show Red S (.fst (.hcomp (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ))) (.fst ((u.dinst .one).isub σ)) ∧
    EqTm S k' .one [] (.fst (.hcomp (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ))) (.fst ((u.dinst .one).isub σ))
      (X.isub σ)
  rw [e1]
  exact ⟨red_fst (.step (step_hcomp_face hσ) (.refl _)), EqTm.fst ((EqTm.hcompFace hσ hty').tyConv e)⟩

/-- The second projections of compositions in Σ-types. -/
theorem kanH2_sigma_snd {T T' : Tm} (hTT : RT2 S k T T') (hP : SigmaStr S k T T')
    (hIHA : ∀ k1 (ρ1 : ISub k1 k) A1 B1, RedT S k1 (T.isub ρ1) (.sigma A1 B1) →
      ∀ k2 (ρ2 : ISub k2 k1) X X', RT2 S k2 (A1.isub ρ2) X → RT2 S k2 X X' → KanH2 S k2 X X')
    (hIHBH : ∀ k1 (ρ1 : ISub k1 k) A1 B1, RedT S k1 (T.isub ρ1) (.sigma A1 B1) → ∀ b, RE2 S k1 A1 b b →
      ∀ k2 (ρ2 : ISub k2 k1) X X', RT2 S k2 ((B1.inst b).isub ρ2) X → RT2 S k2 X X' → KanH2 S k2 X X')
    (hIHBT : ∀ k1 (ρ1 : ISub k1 k) A1 B1, RedT S k1 (T.isub ρ1) (.sigma A1 B1) → ∀ b, RE2 S k1 A1 b b →
      ∀ k2 (ρ2 : ISub (k2 + 1) k1) X X', RT2 S (k2 + 1) ((B1.inst b).isub ρ2) X → RT2 S (k2 + 1) X X' →
        KanT2 S k2 X X')
    {φ φ' : I} {u u' a0 a0' : Tm} (hty : HasTy S k .one [] (.hcomp T φ u a0) T)
    (hty' : HasTy S k .one [] (.hcomp T' φ' u' a0') T)
    (heq : EqTm S k .one [] (.hcomp T φ u a0) (.hcomp T' φ' u' a0') T)
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' T.dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k T φ u u') (ha0 : RE2 S k T a0 a0')
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) ((u.isub σ.up).dinst .zero) (a0'.isub σ))
    (hbd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (a0.isub σ) ((u'.isub σ.up).dinst .zero))
    {A1 B1 : Tm} (hR : RedT S k T (.sigma A1 B1)) :
    RE2 S k (B1.inst (.fst (.hcomp T φ u a0))) (.snd (.hcomp T φ u a0)) (.snd (.hcomp T' φ' u' a0')) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l0, ⟨-, hφs, hum, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hφs' : φ'.Scoped k := by
    obtain ⟨l1, ⟨-, h, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl; exact h
  have hTK : IsTyK S k T := isTyK_of_ty hW hty
  have hTc : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTK)
  have hXT : TyCode k (semK S k T) := tyCode_of_ty hW hty
  have hTs : RT2 S k T T := RT2.refl hW hXT hTT
  have hTσ : ∀ k3 (σ : ISub k3 k), RT2 S k3 (T.isub σ) (T.isub σ) := fun k3 σ => RT2.isub hW hXT hTs σ
  have hsigTy : ∀ k' (ρ : ISub k' k) A B, RedT S k' (T.isub ρ) (.sigma A B) →
      ∃ l, HasTy S k' .one [] (.sigma A B) (.univ l) := fun k' ρ A B h => sigmaW_typed hW (hTK.isub hW ρ) h
  have hsigTy' : ∀ k' (ρ : ISub k' k) A B, RedT S k' (T'.isub ρ) (.sigma A B) →
      ∃ l, HasTy S k' .one [] (.sigma A B) (.univ l) := fun k' ρ A B h =>
    sigmaW_typed hW ((Comp2_ty_base hTT).2.2.1.isub hW ρ) h
  have hXdom : ∀ k' (ρ : ISub k' k) A B, RedT S k' (T.isub ρ) (.sigma A B) → ∀ k'' (ρ' : ISub k'' k'),
      TyCode k'' (semK S k'' (A.isub ρ')) := fun k' ρ A B h k'' ρ' => by
    obtain ⟨l, hs⟩ := hsigTy k' ρ A B h
    exact tyCode_of_univ hW (HasTy.isubS hW (HasTy.sigmaDom hs) ρ')
  have hIHA' : ∀ k' (ρ : ISub k' k) A1 B1, RedT S k' (T.isub ρ) (.sigma A1 B1) →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' (A1.isub ρ') X' → KanH2 S k'' (A1.isub ρ') X' :=
    fun k' ρ A1 B1 h k'' ρ' X' hX' =>
      hIHA k' ρ A1 B1 h k'' ρ' _ X' (RT2.refl hW (hXdom k' ρ A1 B1 h k'' ρ') hX') hX'
  -- the self-related data
  have hum' : HasTy S (k + 1) (cof .one φ).shift [] u T.dshift := minimal_to_spec hum
  have htubes : Tube2 S k T φ u u := fun k3 σ r r' hr hr' hE hh =>
    RE2.trans hW (hTσ k3 σ) (htube k3 σ r r' hr hr' hE hh)
      (RE2.symm hW (hTσ k3 σ) (htube k3 σ r' r' hr' hr' (I_eq_refl _) hh))
  have ha0s : RE2 S k T a0 a0 := RE2.trans hW hTs ha0 (RE2.symm hW hTs ha0)
  have hbds : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) ((u.isub σ.up).dinst .zero) (a0.isub σ) := fun k' σ hh =>
    RE2.trans hW (hTσ k' σ) (hbd k' σ hh) (RE2.symm hW (hTσ k' σ) (RE2.isub hW ha0 σ))
  have hbds' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (a0.isub σ) ((u.isub σ.up).dinst .zero) := fun k' σ hh =>
    RE2.symm hW (hTσ k' σ) (hbds k' σ hh)
  have FSTb := kanH2_sigma_fst hW hP hIHA' hty hty' heq hteq h12 h21 htube ha0 hbd hbd' hR
  have FST := FSTb.1
  obtain ⟨lsig, hsig⟩ := sigmaW_typed hW hTK hR
  have hPs : SigmaStr S k T T := SigmaStr_of hW hTs hR hsig
  have FSTs := (kanH2_sigma_fst hW hPs hIHA' hty hty (EqTm.refl hty) (EqTm.refl hum') (ent_refl _) (ent_refl _)
    htubes ha0s hbds hbds' hR).2
  -- the normal forms of the restrictions
  choose A2 B2 A2' B2' hw using hP.whnf
  have hR0 : RedT S k (T.isub (ISub.id k)) (.sigma A1 B1) := by rw [hTc]; exact hR
  obtain ⟨hA1e, hB1e⟩ : A2 k (ISub.id k) = A1 ∧ B2 k (ISub.id k) = B1 := by
    have := RedW.unique (hw k (ISub.id k)).1.1 hR0.1; injection this; constructor <;> assumption
  have hXA : ∀ k3 (σ : ISub k3 k), TyCode k3 (semK S k3 (A2 k3 σ)) := fun k3 σ => by
    obtain ⟨l, h⟩ := hsigTy k3 σ _ _ (hw k3 σ).1
    exact tyCode_of_univ hW (HasTy.sigmaDom h)
  have hBpt : ∀ k3 (σ : ISub k3 k) a, HasTy S k3 .one [] a (A2 k3 σ) →
      TyCode k3 (semK S k3 ((B2 k3 σ).inst a)) := fun k3 σ a ha => by
    obtain ⟨l, hpi⟩ := hsigTy k3 σ _ _ (hw k3 σ).1
    exact tyCode_of_univ hW (minimal_to_spec (HasTy0.subst hS
      (HasTy0.sigmaCod hS (spec_to_minimal hW hpi)) (spec_to_minimal hW ha)))
  have G3 : ∀ k1 (σ1 : ISub k1 k) k2 (θ : ISub k2 k1) (σ2 : ISub k2 k), σ1.comp θ = σ2 →
      RT2 S k2 ((A2 k1 σ1).isub θ) (A2 k2 σ2) ∧ ∀ a a', RE2 S k2 ((A2 k1 σ1).isub θ) a a' →
        RT2 S k2 (((B2 k1 σ1).isub θ).inst a) ((B2 k2 σ2).inst a') := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact hP.coh k1 σ1 k2 θ _ _ _ _ (hw k1 σ1).1 (hw k2 _).1
  have G3' : ∀ k1 (σ1 : ISub k1 k) k2 (θ : ISub k2 k1) (σ2 : ISub k2 k), σ1.comp θ = σ2 →
      RT2 S k2 ((A2' k1 σ1).isub θ) (A2' k2 σ2) ∧ ∀ a a', RE2 S k2 ((A2' k1 σ1).isub θ) a a' →
        RT2 S k2 (((B2' k1 σ1).isub θ).inst a) ((B2' k2 σ2).inst a') := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact hP.coh' k1 σ1 k2 θ _ _ _ _ (hw k1 σ1).2.1 (hw k2 _).2.1
  have CohId : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A2 k' ρ) ∧ ∀ a a', RE2 S k' (A1.isub ρ) a a' →
      RT2 S k' ((B1.isub ρ).inst a) ((B2 k' ρ).inst a') := by
    intro k' ρ; rw [← hA1e, ← hB1e]; exact G3 k (ISub.id k) k' ρ ρ (ISub.id_comp ρ)
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hXA1ρ : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' (A1.isub ρ)) := fun k' ρ =>
    RT2.tyCode_l hW (CohId k' ρ).1 (hXA _ _)
  have hA1ρ : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A1.isub ρ) := fun k' ρ =>
    RT2.refl hW (hXA1ρ k' ρ) (CohId k' ρ).1
  have Fρ : ∀ k' (ρ : ISub k' k), RE2 S k' (A1.isub ρ) ((Tm.fst (.hcomp T φ u a0)).isub ρ)
      ((Tm.fst (.hcomp T' φ' u' a0')).isub ρ) := fun k' ρ => RE2.isub hW FST ρ
  have Fs : ∀ k' (ρ : ISub k' k), RE2 S k' (A1.isub ρ) ((Tm.fst (.hcomp T φ u a0)).isub ρ)
      ((Tm.fst (.hcomp T φ u a0)).isub ρ) := fun k' ρ =>
    RE2.trans hW (hA1ρ k' ρ) (Fρ k' ρ) (RE2.symm hW (hA1ρ k' ρ) (Fρ k' ρ))
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ))
      (T.isub ρ) := fun k' ρ => HasTy.isubS hW hty ρ
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.hcomp (T'.isub ρ) (φ'.subst ρ.τ) (u'.isub ρ.up)
      (a0'.isub ρ)) (T'.isub ρ) := fun k' ρ => (HasTy.isubS hW hty' ρ).tyConv (hP.tyEq.isub hW ρ)
  have eTs : ∀ k' (ρ : ISub k' k), TyEq S k' (T.isub ρ) (.sigma (A1.isub ρ) (B1.isub ρ)) := fun k' ρ => by
    have := hR.2.isub hW ρ; rwa [isub_sigma] at this
  -- the first projection of a restricted composition, against its normal form
  have fstRel : ∀ k' (ρ : ISub k' k), ¬ I.Entails .one (φ.subst ρ.τ) →
      RE2 S k' (A1.isub ρ) ((Tm.fst (.hcomp T φ u a0)).isub ρ)
        (.hcomp (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))) := by
    intro k' ρ hf
    have htH := (HasTy.eqR (fst_hcomp_sigma hW hf (hρT k' ρ) (hw k' ρ).1).2).tyConv (TyEq.symm (tyB (CohId k' ρ).1))
    refine RE2.expandH hW (hA1ρ k' ρ) (RE2.typed (Fs k' ρ)).1 htH fun k'' ρ' => ?_
    have e : ((Tm.fst (.hcomp T φ u a0)).isub ρ).isub ρ' = Tm.fst (.hcomp (T.isub (ρ.comp ρ'))
        (φ.subst (ρ.comp ρ').τ) (u.isub (ρ.comp ρ').up) (a0.isub (ρ.comp ρ'))) := by rw [Tm.isub_isub]; rfl
    have X := FSTs k' ρ k'' ρ' _ _ _ _ (hw k' ρ).1 (hw k'' (ρ.comp ρ')).1
    rw [if_neg hf] at X
    rw [e, Tm.isub_isub A1]
    by_cases hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ)
    · rw [if_pos hf2] at X
      exact ⟨_, red_fst (.step (step_hcomp_face hf2) (.refl _)),
        EqTm.fst ((EqTm.hcompFace hf2 (hρT _ _)).tyConv (eTs _ _)), RE2.symm hW (hA1ρ _ _) X⟩
    · rw [if_neg hf2] at X
      obtain ⟨a, b⟩ := fst_hcomp_sigma hW hf2 (hρT _ _) (hw _ _).1
      exact ⟨_, a, b.tyConv (TyEq.symm (tyB (CohId _ _).1)), RE2.symm hW (hA1ρ _ _) X⟩
  -- relations of the domains and codomains at restrictions
  have hXA' : ∀ k3 (σ : ISub k3 k), TyCode k3 (semK S k3 (A2' k3 σ)) := fun k3 σ =>
    RT2.tyCode_r hW (hw k3 σ).2.2.1 (hXA k3 σ)
  have hBpt' : ∀ k3 (σ : ISub k3 k) a, HasTy S k3 .one [] a (A2' k3 σ) →
      TyCode k3 (semK S k3 ((B2' k3 σ).inst a)) := fun k3 σ a ha => by
    obtain ⟨l, hpi⟩ := hsigTy' k3 σ _ _ (hw k3 σ).2.1
    exact tyCode_of_univ hW (minimal_to_spec (HasTy0.subst hS
      (HasTy0.sigmaCod hS (spec_to_minimal hW hpi)) (spec_to_minimal hW ha)))
  have toA : ∀ k1 (σ1 : ISub k1 k) k3 (θ : ISub k3 k1) (σ : ISub k3 k), σ1.comp θ = σ → ∀ {a b : Tm},
      RE2 S k3 (A2 k3 σ) a b → RE2 S k3 ((A2 k1 σ1).isub θ) a b := fun k1 σ1 k3 θ σ e a b h =>
    RE2.conv' hW (G3 k1 σ1 k3 θ σ e).1 h (RT2.tyCode_l hW (G3 k1 σ1 k3 θ σ e).1 (hXA _ _))
  have Ael : ∀ k3 (σ : ISub k3 k) f f', RE2 S k3 (T.isub σ) f f' → RE2 S k3 (A2 k3 σ) (.fst f) (.fst f') :=
    fun k3 σ f f' h => (hP.elim k3 σ _ _ f f' (hw k3 σ).1 h).1
  have Bel : ∀ k3 (σ : ISub k3 k) f f', RE2 S k3 (T.isub σ) f f' →
      RE2 S k3 ((B2 k3 σ).inst (.fst f)) (.snd f) (.snd f') :=
    fun k3 σ f f' h => (hP.elim k3 σ _ _ f f' (hw k3 σ).1 h).2
  -- codomains at related arguments, across restrictions
  have Brel : ∀ k1 (σ1 : ISub k1 k) k3 (θ : ISub k3 k1) (σ : ISub k3 k), σ1.comp θ = σ → ∀ a a',
      RE2 S k3 ((A2 k1 σ1).isub θ) a a' → RT2 S k3 (((B2 k1 σ1).isub θ).inst a) ((B2 k3 σ).inst a') := by
    intro k1 σ1 k3 θ σ e a a' h
    exact (G3 k1 σ1 k3 θ σ e).2 a a' h
  -- the first components of the restricted compositions
  have parts : ∀ k' (ρ : ISub k' k), _ := fun k' ρ =>
    hcomp_sigma_parts hS (spec_to_minimal hW (HasTy.eqR (eq_hcomp_ty hW (hρT k' ρ) (hw k' ρ).1.2)))
  have parts' : ∀ k' (ρ : ISub k' k), _ := fun k' ρ =>
    hcomp_sigma_parts hS (spec_to_minimal hW (HasTy.eqR (eq_hcomp_ty hW (hρT' k' ρ) (hw k' ρ).2.1.2)))
  -- the self-related data of the first components, at a restriction
  have Sφ : ∀ k' (ρ : ISub k' k), (φ.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hφs ρ.sc
  have SAA : ∀ k' (ρ : ISub k' k), RT2 S k' (A2 k' ρ) (A2 k' ρ) := fun k' ρ =>
    RT2.refl hW (hXA k' ρ) (hw k' ρ).2.2.1
  have SK : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k'), KanH2 S k3 ((A2 k' ρ).isub τ) ((A2 k' ρ).isub τ) :=
    fun k' ρ k3 τ => hIHA' k' ρ _ _ (hw k' ρ).1 k3 τ _ (RT2.isub hW (hXA k' ρ) (SAA k' ρ) τ)
  have fstup : ∀ (w : Tm) k' (ρ : ISub k' k) k3 (σ : ISub k3 k') (x : I),
      ((Tm.fst (w.isub ρ.up)).isub σ.up).dinst x = .fst ((w.isub (ρ.comp σ).up).dinst x) := by
    intro w k' ρ k3 σ x
    show Tm.fst (((w.isub ρ.up).isub σ.up).dinst x) = _
    rw [Tm.isub_isub, ← ISub.up_comp]
  have fsta : ∀ (w : Tm) k' (ρ : ISub k' k) k3 (σ : ISub k3 k'),
      (Tm.fst (w.isub ρ)).isub σ = .fst (w.isub (ρ.comp σ)) := by
    intro w k' ρ k3 σ
    show Tm.fst ((w.isub ρ).isub σ) = _
    rw [Tm.isub_isub]
  have STube : ∀ k' (ρ : ISub k' k), Tube2 S k' (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up))
      (.fst (u.isub ρ.up)) := by
    intro k' ρ k3 σ r r' hr hr' hE hh
    rw [fstup, fstup]
    exact toA k' ρ k3 σ _ rfl (Ael k3 _ _ _ (htubes k3 (ρ.comp σ) r r' hr hr' hE (by rw [I_subst_comp]; exact hh)))
  have Sv0 : ∀ k' (ρ : ISub k' k), RE2 S k' (A2 k' ρ) (.fst (a0.isub ρ)) (.fst (a0.isub ρ)) := fun k' ρ =>
    Ael k' ρ _ _ (RE2.isub hW ha0s ρ)
  have Sbd : ∀ k' (ρ : ISub k' k) k3 (σ : ISub k3 k'), (ival (idEnv k3) ((φ.subst ρ.τ).subst σ.τ)).holds →
      RE2 S k3 ((A2 k' ρ).isub σ) (((Tm.fst (u.isub ρ.up)).isub σ.up).dinst .zero) ((Tm.fst (a0.isub ρ)).isub σ) := by
    intro k' ρ k3 σ hh
    rw [fstup, fsta]
    exact toA k' ρ k3 σ _ rfl (Ael k3 _ _ _ (hbds k3 (ρ.comp σ) (by rw [I_subst_comp]; exact hh)))
  have Sbd' : ∀ k' (ρ : ISub k' k) k3 (σ : ISub k3 k'), (ival (idEnv k3) ((φ.subst ρ.τ).subst σ.τ)).holds →
      RE2 S k3 ((A2 k' ρ).isub σ) ((Tm.fst (a0.isub ρ)).isub σ) (((Tm.fst (u.isub ρ.up)).isub σ.up).dinst .zero) := by
    intro k' ρ k3 σ hh
    rw [fstup, fsta]
    exact toA k' ρ k3 σ _ rfl (Ael k3 _ _ _ (hbds' k3 (ρ.comp σ) (by rw [I_subst_comp]; exact hh)))
  have STy : ∀ k' (ρ : ISub k' k), HasTy S (k' + 1) .one []
      (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))) (A2 k' ρ).dshift := fun k' ρ =>
    minimal_to_spec (parts k' ρ).2.1
  have Steq : ∀ k' (ρ : ISub k' k), EqTm S (k' + 1) (cof .one (φ.subst ρ.τ)).shift [] (.fst (u.isub ρ.up))
      (.fst (u.isub ρ.up)) (A2 k' ρ).dshift := fun k' ρ => EqTm.refl (minimal_to_spec (parts k' ρ).2.2.1)
  have SFrel : ∀ k' (ρ : ISub k' k) k3 (σ σ' : ISub k3 (k' + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k3 ((A2 k' ρ).dshift.isub σ)
        ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub σ)
        ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub σ') :=
    fun k' ρ k3 σ σ' et e0 => hfill_rel hW (Sφ k' ρ) (SK k' ρ) (SAA k' ρ) (TyEq.refl _) (Steq k' ρ) (STy k' ρ)
      (STy k' ρ) (EqTm.refl (STy k' ρ)) (ent_refl _) (ent_refl _) (STube k' ρ) (Sv0 k' ρ) (Sbd k' ρ) (Sbd' k' ρ)
      σ σ' et e0
  -- the cross-related data of the first components, at a restriction of a restriction
  have fstu1 : ∀ (w : Tm) k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'),
      (Tm.fst (w.isub ρ.up)).isub ρ'.up = .fst (w.isub (ρ.comp ρ').up) := by
    intro w k' ρ k'' ρ'
    show Tm.fst ((w.isub ρ.up).isub ρ'.up) = _
    rw [Tm.isub_isub, ← ISub.up_comp]
  have Arel0 : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), RT2 S k'' ((A2 k' ρ).isub ρ') (A2' k'' (ρ.comp ρ')) := by
    intro k' ρ k'' ρ'
    have g1 := (G3 k' ρ k'' ρ' (ρ.comp ρ') rfl).1
    exact RT2.trans hW (RT2.tyCode_l hW g1 (hXA _ _)) g1 (hw k'' (ρ.comp ρ')).2.2.1
  have Arel : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') k3 (τ : ISub k3 k''),
      RT2 S k3 (((A2 k' ρ).isub ρ').isub τ) ((A2' k'' (ρ.comp ρ')).isub τ) := by
    intro k' ρ k'' ρ' k3 τ
    have e : ρ.comp (ρ'.comp τ) = (ρ.comp ρ').comp τ := (ISub.comp_assoc _ _ _).symm
    have g1 := (G3 k' ρ k3 (ρ'.comp τ) ((ρ.comp ρ').comp τ) e).1
    have g2 := (G3' k'' (ρ.comp ρ') k3 τ _ rfl).1
    rw [Tm.isub_isub]
    have m := (hw k3 ((ρ.comp ρ').comp τ)).2.2.1
    exact RT2.trans hW (RT2.tyCode_l hW g1 (hXA _ _)) g1
      (RT2.trans hW (hXA _ _) m (RT2.symm hW (RT2.tyCode_l hW g2 (hXA' _ _)) g2))
  have XK : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') k3 (τ : ISub k3 k''),
      KanH2 S k3 (((A2 k' ρ).isub ρ').isub τ) ((A2' k'' (ρ.comp ρ')).isub τ) := by
    intro k' ρ k'' ρ' k3 τ
    refine hIHA k' ρ _ _ (hw k' ρ).1 k3 (ρ'.comp τ) _ _ ?_ (Arel k' ρ k'' ρ' k3 τ)
    rw [Tm.isub_isub]; exact RT2.isub hW (hXA k' ρ) (SAA k' ρ) _
  have XAA : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), RT2 S k'' ((A2 k' ρ).isub ρ') ((A2 k' ρ).isub ρ') :=
    fun k' ρ k'' ρ' => RT2.isub hW (hXA _ _) (SAA _ _) ρ'
  have XTA : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), TyEq S k'' ((A2 k' ρ).isub ρ') (A2' k'' (ρ.comp ρ')) :=
    fun k' ρ k'' ρ' => tyB (Arel0 k' ρ k'' ρ')
  have Xteq : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), EqTm S (k'' + 1) (cof .one (φ.subst (ρ.comp ρ').τ)).shift []
      (.fst (u.isub (ρ.comp ρ').up)) (.fst (u'.isub (ρ.comp ρ').up)) ((A2 k' ρ).isub ρ').dshift := by
    intro k' ρ k'' ρ'
    have hfσ := EqTm.cofIsub hW hφs hteq (ρ.comp ρ')
    rw [isub_dshift] at hfσ
    obtain ⟨lσ, hσ⟩ := hsigTy k'' (ρ.comp ρ') _ _ (hw k'' (ρ.comp ρ')).1
    have e := eqCof_fst hW (Sφ _ _) hfσ (hw k'' (ρ.comp ρ')).1.2 hσ
    rw [dshift_eq_isub_closed (closed_of_ty hW (HasTy.sigmaDom hσ))] at e
    exact EqTm.cofConv (Sφ _ _) e (TyEq.symm (tyB (G3 k' ρ k'' ρ' (ρ.comp ρ') rfl).1))
  have XTyL : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), HasTy S (k'' + 1) .one []
      (Tm.hfill ((A2 k' ρ).isub ρ') (φ.subst (ρ.comp ρ').τ) (.fst (u.isub (ρ.comp ρ').up)) (.fst (a0.isub (ρ.comp ρ'))))
      ((A2 k' ρ).isub ρ').dshift := by
    intro k' ρ k'' ρ'
    have h := HasTy.isubS hW (STy k' ρ) ρ'.up
    rw [isub_hfill, isub_dshift, fstu1, fsta, ← I_subst_comp] at h
    exact h
  have XTyR : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), HasTy S (k'' + 1) .one []
      (Tm.hfill (A2' k'' (ρ.comp ρ')) (φ'.subst (ρ.comp ρ').τ) (.fst (u'.isub (ρ.comp ρ').up))
        (.fst (a0'.isub (ρ.comp ρ')))) ((A2 k' ρ).isub ρ').dshift := fun k' ρ k'' ρ' =>
    (minimal_to_spec (parts' k'' (ρ.comp ρ')).2.1).tyConv
      (TyEq.symm (tyB (RT2.dshift hW (RT2.tyCode_l hW (Arel0 k' ρ k'' ρ') (hXA' _ _)) (Arel0 k' ρ k'' ρ'))))
  have Xtube : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), Tube2 S k'' ((A2 k' ρ).isub ρ') (φ.subst (ρ.comp ρ').τ)
      (.fst (u.isub (ρ.comp ρ').up)) (.fst (u'.isub (ρ.comp ρ').up)) := by
    intro k' ρ k'' ρ' k3 σ r r' hr hr' hE hh
    rw [fstup, fstup, Tm.isub_isub]
    have e : ρ.comp (ρ'.comp σ) = (ρ.comp ρ').comp σ := (ISub.comp_assoc _ _ _).symm
    exact toA k' ρ k3 (ρ'.comp σ) _ e (Ael k3 _ _ _ (htube k3 ((ρ.comp ρ').comp σ) r r' hr hr' hE
      (by rw [I_subst_comp]; exact hh)))
  have Xv0 : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), RE2 S k'' ((A2 k' ρ).isub ρ') (.fst (a0.isub (ρ.comp ρ')))
      (.fst (a0'.isub (ρ.comp ρ'))) := fun k' ρ k'' ρ' =>
    toA k' ρ k'' ρ' _ rfl (Ael k'' _ _ _ (RE2.isub hW ha0 _))
  have Xbd : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') k3 (σ : ISub k3 k''),
      (ival (idEnv k3) ((φ.subst (ρ.comp ρ').τ).subst σ.τ)).holds →
      RE2 S k3 (((A2 k' ρ).isub ρ').isub σ) (((Tm.fst (u.isub (ρ.comp ρ').up)).isub σ.up).dinst .zero)
        ((Tm.fst (a0'.isub (ρ.comp ρ'))).isub σ) := by
    intro k' ρ k'' ρ' k3 σ hh
    rw [fstup, fsta, Tm.isub_isub]
    have e : ρ.comp (ρ'.comp σ) = (ρ.comp ρ').comp σ := (ISub.comp_assoc _ _ _).symm
    exact toA k' ρ k3 (ρ'.comp σ) _ e (Ael k3 _ _ _ (hbd k3 _ (by rw [I_subst_comp]; exact hh)))
  have Xbd' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') k3 (σ : ISub k3 k''),
      (ival (idEnv k3) ((φ.subst (ρ.comp ρ').τ).subst σ.τ)).holds →
      RE2 S k3 (((A2 k' ρ).isub ρ').isub σ) ((Tm.fst (a0.isub (ρ.comp ρ'))).isub σ)
        (((Tm.fst (u'.isub (ρ.comp ρ').up)).isub σ.up).dinst .zero) := by
    intro k' ρ k'' ρ' k3 σ hh
    rw [fstup, fsta, Tm.isub_isub]
    have e : ρ.comp (ρ'.comp σ) = (ρ.comp ρ').comp σ := (ISub.comp_assoc _ _ _).symm
    exact toA k' ρ k3 (ρ'.comp σ) _ e (Ael k3 _ _ _ (hbd' k3 _ (by rw [I_subst_comp]; exact hh)))
  have XeqF : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), EqTm S (k'' + 1) .one []
      (Tm.hfill ((A2 k' ρ).isub ρ') (φ.subst (ρ.comp ρ').τ) (.fst (u.isub (ρ.comp ρ').up)) (.fst (a0.isub (ρ.comp ρ'))))
      (Tm.hfill (A2' k'' (ρ.comp ρ')) (φ'.subst (ρ.comp ρ').τ) (.fst (u'.isub (ρ.comp ρ').up))
        (.fst (a0'.isub (ρ.comp ρ')))) ((A2 k' ρ).isub ρ').dshift := by
    intro k' ρ k'' ρ'
    have hAA : (A2 k' ρ).isub ρ' = A2' k'' (ρ.comp ρ') ∨
        ∃ l, EqTm0 S k'' .one [] ((A2 k' ρ).isub ρ') (A2' k'' (ρ.comp ρ')) (.univ l) := by
      rcases XTA k' ρ k'' ρ' with e | ⟨l, e⟩
      · exact .inl e
      · exact .inr ⟨l, spec_to_minimal_eq hW e⟩
    exact minimal_to_spec_eq (hfill_cong hW (spec_to_minimal hW (XTyL k' ρ k'' ρ')) (spec_to_minimal hW (XTyR k' ρ k'' ρ'))
      hAA (spec_to_minimal_eq hW (Xteq k' ρ k'' ρ')) (spec_to_minimal_eq hW (RE2.typed (Xv0 k' ρ k'' ρ')).2.2)
      (ent_subst h12 _) (ent_subst h21 _))
  have XFrel : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') k3 (σ σ' : ISub k3 (k'' + 1)), σ.tail = σ'.tail →
      I.Eq (σ.τ 0) (σ'.τ 0) → RE2 S k3 (((A2 k' ρ).isub ρ').dshift.isub σ)
        ((Tm.hfill ((A2 k' ρ).isub ρ') (φ.subst (ρ.comp ρ').τ) (.fst (u.isub (ρ.comp ρ').up))
          (.fst (a0.isub (ρ.comp ρ')))).isub σ)
        ((Tm.hfill (A2' k'' (ρ.comp ρ')) (φ'.subst (ρ.comp ρ').τ) (.fst (u'.isub (ρ.comp ρ').up))
          (.fst (a0'.isub (ρ.comp ρ')))).isub σ') :=
    fun k' ρ k'' ρ' k3 σ σ' et e0 => hfill_rel hW (Sφ k'' (ρ.comp ρ')) (XK k' ρ k'' ρ') (XAA k' ρ k'' ρ')
      (XTA k' ρ k'' ρ') (Xteq k' ρ k'' ρ') (XTyL k' ρ k'' ρ') (XTyR k' ρ k'' ρ') (XeqF k' ρ k'' ρ')
      (ent_subst h12 _) (ent_subst h21 _) (Xtube k' ρ k'' ρ') (Xv0 k' ρ k'' ρ') (Xbd k' ρ k'' ρ') (Xbd' k' ρ k'' ρ')
      σ σ' et e0
  -- the codomains at related arguments
  have BW : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') a b, RE2 S k3 ((A2 k' ρ).isub τ) a b →
      RT2 S k3 (((B2 k' ρ).isub τ).inst a) ((B2 k3 (ρ.comp τ)).inst b) :=
    fun k' ρ k3 τ a b h => (G3 k' ρ k3 τ _ rfl).2 a b h
  have BL : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') a b, RE2 S k3 ((A2 k' ρ).isub τ) a b →
      RT2 S k3 (((B2 k' ρ).isub τ).inst a) (((B2 k' ρ).isub τ).inst b) := by
    intro k' ρ k3 τ a b h
    have g := (G3 k' ρ k3 τ _ rfl)
    have hX := RT2.tyCode_l hW g.1 (hXA _ _)
    have hbb := RE2.trans hW (RT2.refl hW hX g.1) (RE2.symm hW (RT2.refl hW hX g.1) h) h
    have c1 := g.2 a b h
    have c2 := g.2 b b hbb
    have u2 := hBpt k3 _ _ (RE2.typed (RE2.conv hW g.1 hbb)).1
    exact RT2.trans hW (RT2.tyCode_l hW c1 u2) c1 (RT2.symm hW (RT2.tyCode_l hW c2 u2) c2)
  have BX : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') k3 (τ : ISub k3 k'') a b,
      RE2 S k3 ((A2 k' ρ).isub (ρ'.comp τ)) a b →
      RT2 S k3 (((B2 k' ρ).isub (ρ'.comp τ)).inst a) (((B2' k'' (ρ.comp ρ')).isub τ).inst b) := by
    intro k' ρ k'' ρ' k3 τ a b h
    have e : ρ.comp (ρ'.comp τ) = (ρ.comp ρ').comp τ := (ISub.comp_assoc _ _ _).symm
    have g := G3 k' ρ k3 (ρ'.comp τ) _ e
    have hX := RT2.tyCode_l hW g.1 (hXA _ _)
    have hbb := RE2.conv hW g.1 (RE2.trans hW (RT2.refl hW hX g.1) (RE2.symm hW (RT2.refl hW hX g.1) h) h)
    have c1 := g.2 a b h
    have c2 := (hw k3 ((ρ.comp ρ').comp τ)).2.2.2 b b hbb
    have g' := G3' k'' (ρ.comp ρ') k3 τ _ rfl
    have hX' := RT2.tyCode_l hW g'.1 (hXA' _ _)
    have hbb' := RE2.conv' hW g'.1 (RE2.conv hW (hw k3 ((ρ.comp ρ').comp τ)).2.2.1 hbb) hX'
    have c3 := g'.2 b b hbb'
    have u2 := hBpt k3 _ _ (RE2.typed hbb).1
    have u3 := hBpt' k3 _ _ (RE2.typed (RE2.conv hW g'.1 hbb')).1
    exact RT2.trans hW (RT2.tyCode_l hW c1 u2) c1 (RT2.trans hW u2 c2 (RT2.symm hW (RT2.tyCode_l hW c3 u3) c3))
  -- the lines of the second projections
  have CptL : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') k3 (τ : ISub k3 k'') (y : I) (hy : y.Scoped k3),
      (((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))).isub ρ'.up).isub (ISub.cons y hy τ) =
        ((B2 k' ρ).isub (ρ'.comp τ)).inst ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub (ISub.cons y hy (ρ'.comp τ))) := by
    intro k' ρ k'' ρ' k3 τ y hy
    rw [Tm.isub_isub, ISub.up_comp_cons, isub_inst, dshift_isub_cons]
  have CptR : ∀ k'' (σ : ISub k'' k) k3 (τ : ISub k3 k'') (y : I) (hy : y.Scoped k3),
      ((B2' k'' σ).dshift.inst (Tm.hfill (A2' k'' σ) (φ'.subst σ.τ) (.fst (u'.isub σ.up)) (.fst (a0'.isub σ)))).isub
        (ISub.cons y hy τ) = ((B2' k'' σ).isub τ).inst
        ((Tm.hfill (A2' k'' σ) (φ'.subst σ.τ) (.fst (u'.isub σ.up)) (.fst (a0'.isub σ))).isub (ISub.cons y hy τ)) := by
    intro k'' σ k3 τ y hy
    rw [isub_inst, dshift_isub_cons]
  have FLeq : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub ρ'.up =
      Tm.hfill ((A2 k' ρ).isub ρ') (φ.subst (ρ.comp ρ').τ) (.fst (u.isub (ρ.comp ρ').up)) (.fst (a0.isub (ρ.comp ρ'))) := by
    intro k' ρ k'' ρ'
    rw [isub_hfill, fstu1, fsta, ← I_subst_comp]
  -- the reductions of the second projections
  have Fs' : ∀ k' (ρ : ISub k' k), RE2 S k' (A1.isub ρ) ((Tm.fst (.hcomp T' φ' u' a0')).isub ρ)
      ((Tm.fst (.hcomp T' φ' u' a0')).isub ρ) := fun k' ρ =>
    RE2.trans hW (hA1ρ k' ρ) (RE2.symm hW (hA1ρ k' ρ) (Fρ k' ρ)) (Fρ k' ρ)
  have B1rel : ∀ k' (ρ : ISub k' k) a a', RE2 S k' (A1.isub ρ) a a' →
      RT2 S k' ((B1.isub ρ).inst a) ((B1.isub ρ).inst a') := by
    intro k' ρ a a' h
    have h' := RE2.trans hW (hA1ρ k' ρ) (RE2.symm hW (hA1ρ k' ρ) h) h
    have c1 := (CohId k' ρ).2 a a' h
    have c2 := (CohId k' ρ).2 a' a' h'
    have u2 := hBpt k' _ _ (RE2.typed (RE2.conv hW (CohId k' ρ).1 h)).2.1
    exact RT2.trans hW (RT2.tyCode_l hW c1 u2) c1 (RT2.symm hW (RT2.tyCode_l hW c2 u2) c2)
  have eTs' : ∀ k' (ρ : ISub k' k), TyEq S k' (T'.isub ρ) (.sigma (A1.isub ρ) (B1.isub ρ)) := fun k' ρ => by
    have := (TyEq.trans hW (TyEq.symm hP.tyEq) hR.2).isub hW ρ; rwa [isub_sigma] at this
  have sndL : ∀ k' (ρ : ISub k' k), ¬ I.Entails .one (φ.subst ρ.τ) →
      Red S ((Tm.snd (.hcomp T φ u a0)).isub ρ)
        (Tm.comp ((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))) (φ.subst ρ.τ) (.snd (u.isub ρ.up)) (.snd (a0.isub ρ))) ∧
      EqTm S k' .one [] ((Tm.snd (.hcomp T φ u a0)).isub ρ)
        (Tm.comp ((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))) (φ.subst ρ.τ) (.snd (u.isub ρ.up)) (.snd (a0.isub ρ)))
        ((B1.inst (.fst (.hcomp T φ u a0))).isub ρ) := by
    intro k' ρ hf
    obtain ⟨a, b⟩ := snd_hcomp_sigma hW hf (hρT k' ρ) (hw k' ρ).1
    refine ⟨a, b.tyConv ?_⟩
    rw [isub_inst]; exact TyEq.symm (tyB ((CohId k' ρ).2 _ _ (Fs k' ρ)))
  have sndR : ∀ k' (ρ : ISub k' k), ¬ I.Entails .one (φ'.subst ρ.τ) →
      Red S ((Tm.snd (.hcomp T' φ' u' a0')).isub ρ)
        (Tm.comp ((B2' k' ρ).dshift.inst (Tm.hfill (A2' k' ρ) (φ'.subst ρ.τ) (.fst (u'.isub ρ.up)) (.fst (a0'.isub ρ)))) (φ'.subst ρ.τ) (.snd (u'.isub ρ.up)) (.snd (a0'.isub ρ))) ∧
      EqTm S k' .one [] ((Tm.snd (.hcomp T' φ' u' a0')).isub ρ)
        (Tm.comp ((B2' k' ρ).dshift.inst (Tm.hfill (A2' k' ρ) (φ'.subst ρ.τ) (.fst (u'.isub ρ.up)) (.fst (a0'.isub ρ)))) (φ'.subst ρ.τ) (.snd (u'.isub ρ.up)) (.snd (a0'.isub ρ)))
        ((B1.inst (.fst (.hcomp T φ u a0))).isub ρ) := by
    intro k' ρ hf
    obtain ⟨a, b⟩ := snd_hcomp_sigma hW hf (hρT' k' ρ) (hw k' ρ).2.1
    refine ⟨a, b.tyConv ?_⟩
    rw [isub_inst]
    have c1 := (CohId k' ρ).2 _ _ (Fρ k' ρ)
    have c2 := (hw k' ρ).2.2.2 _ _ (RE2.conv hW (CohId k' ρ).1 (Fs' k' ρ))
    exact TyEq.symm (TyEq.trans hW (tyB c1) (tyB c2))
  have faceL : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst ρ.τ) →
      Red S ((Tm.snd (.hcomp T φ u a0)).isub ρ) (.snd ((u.isub ρ.up).dinst .one)) ∧
      EqTm S k' .one [] ((Tm.snd (.hcomp T φ u a0)).isub ρ) (.snd ((u.isub ρ.up).dinst .one))
        ((B1.inst (.fst (.hcomp T φ u a0))).isub ρ) := by
    intro k' ρ hf
    refine ⟨red_snd (.step (step_hcomp_face hf) (.refl _)), ?_⟩
    rw [isub_inst]; exact EqTm.snd ((EqTm.hcompFace hf (hρT k' ρ)).tyConv (eTs k' ρ))
  have faceR : ∀ k' (ρ : ISub k' k), I.Entails .one (φ'.subst ρ.τ) →
      Red S ((Tm.snd (.hcomp T' φ' u' a0')).isub ρ) (.snd ((u'.isub ρ.up).dinst .one)) ∧
      EqTm S k' .one [] ((Tm.snd (.hcomp T' φ' u' a0')).isub ρ) (.snd ((u'.isub ρ.up).dinst .one))
        ((B1.inst (.fst (.hcomp T φ u a0))).isub ρ) := by
    intro k' ρ hf
    refine ⟨red_snd (.step (step_hcomp_face hf) (.refl _)), ?_⟩
    rw [isub_inst]
    exact (EqTm.snd ((EqTm.hcompFace hf (hρT' k' ρ)).tyConv (eTs' k' ρ))).tyConv
      (TyEq.symm (tyB (B1rel k' ρ _ _ (Fρ k' ρ))))
  have sndu1 : ∀ (w : Tm) k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'),
      (Tm.snd (w.isub ρ.up)).isub ρ'.up = .snd (w.isub (ρ.comp ρ').up) := by
    intro w k' ρ k'' ρ'
    show Tm.snd ((w.isub ρ.up).isub ρ'.up) = _
    rw [Tm.isub_isub, ← ISub.up_comp]
  have snda : ∀ (w : Tm) k' (ρ : ISub k' k) k3 (σ : ISub k3 k'),
      (Tm.snd (w.isub ρ)).isub σ = .snd (w.isub (ρ.comp σ)) := by
    intro w k' ρ k3 σ
    show Tm.snd ((w.isub ρ).isub σ) = _
    rw [Tm.isub_isub]
  have sndup : ∀ (w : Tm) k' (ρ : ISub k' k) k3 (σ : ISub k3 k') (x : I),
      ((Tm.snd (w.isub ρ.up)).isub σ.up).dinst x = .snd ((w.isub (ρ.comp σ).up).dinst x) := by
    intro w k' ρ k3 σ x
    show Tm.snd (((w.isub ρ.up).isub σ.up).dinst x) = _
    rw [Tm.isub_isub, ← ISub.up_comp]
  -- the composition of the second projections, where the face does not hold
  have compC : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RE2 S k'' ((B1.inst (.fst (.hcomp T φ u a0))).isub (ρ.comp ρ'))
        (Tm.comp (((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))).isub ρ'.up) (φ.subst (ρ.comp ρ').τ) (.snd (u.isub (ρ.comp ρ').up))
          (.snd (a0.isub (ρ.comp ρ'))))
        (Tm.comp ((B2' k'' (ρ.comp ρ')).dshift.inst (Tm.hfill (A2' k'' (ρ.comp ρ')) (φ'.subst (ρ.comp ρ').τ) (.fst (u'.isub (ρ.comp ρ').up)) (.fst (a0'.isub (ρ.comp ρ'))))) (φ'.subst (ρ.comp ρ').τ) (.snd (u'.isub (ρ.comp ρ').up))
          (.snd (a0'.isub (ρ.comp ρ')))) := by
    intro k' ρ k'' ρ' hf2
    have hf : ¬ I.Entails .one (φ.subst ρ.τ) := fun h => hf2 (ent_comp h)
    have hf2' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hf2 (ent_trans h (ent_subst h21 _))
    have e1 : (((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))).isub ρ'.up).dinst .one =
        ((B2 k' ρ).isub ρ').inst ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub (ISub.cons .one trivial ρ')) := by
      rw [isub_up_dinst _ ρ' .one trivial, isub_inst, dshift_isub_cons]
    have conv1 : RT2 S k'' ((((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))).isub ρ'.up).dinst .one)
        ((B1.inst (.fst (.hcomp T φ u a0))).isub (ρ.comp ρ')) := by
      rw [e1, isub_inst]
      have htH : HasTy S k' .one [] (Tm.hcomp (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))) (A2 k' ρ) := minimal_to_spec (parts k' ρ).1
      have r1 := hfill_one_pt hW (Sφ k' ρ) (hXA k' ρ) (SAA k' ρ) (SK k' ρ) htH (STy k' ρ) (STube k' ρ) (Sv0 k' ρ)
        (Sbd k' ρ) ρ'
      have r2 := RE2.isub hW (fstRel k' ρ hf) ρ'
      rw [Tm.isub_isub A1, Tm.isub_isub (Tm.fst _)] at r2
      have g := (G3 k' ρ k'' ρ' (ρ.comp ρ') rfl).1
      have cA := (CohId k'' (ρ.comp ρ')).1
      have hXL := RT2.tyCode_l hW g (hXA _ _)
      have r2' := RE2.conv' hW (RT2.trans hW hXL g (RT2.symm hW (hXA1ρ _ _) cA)) r2 hXL
      have hLL := XAA k' ρ k'' ρ'
      have R1 := RE2.trans hW hLL r1 (RE2.symm hW hLL r2')
      have c1 := BW k' ρ k'' ρ' _ _ R1
      have c2 := (CohId k'' (ρ.comp ρ')).2 _ _ (Fs k'' (ρ.comp ρ'))
      have u2 := hBpt k'' _ _ (RE2.typed (RE2.conv hW g R1)).2.1
      exact RT2.trans hW (RT2.tyCode_l hW c1 u2) c1 (RT2.symm hW (RT2.tyCode_l hW c2 u2) c2)
    have eT := TyEq.symm (tyB conv1)
    have EL := EqTm.isubS hW (sndL k' ρ hf).2 ρ'
    rw [Tm.isub_isub (Tm.snd _), Tm.isub_isub (B1.inst _), comp_isub, ← I_subst_comp, sndu1, snda] at EL
    have ER := (sndR k'' (ρ.comp ρ') hf2').2
    have EM := EqTm.isubS hW (EqTm.snd (heq.tyConv hR.2)) (ρ.comp ρ')
    have Eall := (EL.symm.trans EM).trans ER
    refine RE2.conv hW conv1 (comp2 hW ?_ ?_ ?_ ?_ (HasTy.eqR EL |>.tyConv eT) ((HasTy.eqR ER).tyConv eT) (Eall.tyConv eT) ?_
      (ent_subst h12 _) (ent_subst h21 _) ?_ ?_ ?_ ?_)
    · -- robustness across the two sides
      intro k3 τ y y' hy hy' hE
      rw [CptL, CptR]
      apply BX k' ρ k'' ρ' k3 τ
      have X := XFrel k' ρ k'' ρ' k3 (ISub.cons y hy τ) (ISub.cons y' hy' τ) rfl hE
      rw [dshift_isub_cons, Tm.isub_isub, ← FLeq, Tm.isub_isub (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))), ISub.up_comp_cons] at X
      exact X
    · -- robustness of the left line
      intro k3 τ y y' hy hy' hE
      rw [CptL, CptL]
      apply BL k' ρ k3 (ρ'.comp τ)
      have X := SFrel k' ρ k3 (ISub.cons y hy (ρ'.comp τ)) (ISub.cons y' hy' (ρ'.comp τ)) rfl hE
      rw [dshift_isub_cons] at X
      exact X
    · -- transport along the restrictions of the left line
      intro k3 Θ X' hX'
      have hwk : (ISub.wk k').comp (ρ'.up.comp Θ) = (ρ'.up.comp Θ).tail := by
        ext i
        by_cases hi : i < k'
        · simp [ISub.wk, ISub.comp, ISub.tail, hi, I.subst]
        · show (if i < k' then I.var (i + 1) else .zero).subst (ρ'.up.comp Θ).τ = (ρ'.up.comp Θ).τ (i + 1)
          rw [if_neg hi, (ρ'.up.comp Θ).hi (i + 1) (by omega)]; rfl
      have idt : (ISub.id (k' + 1)).tail = ISub.wk k' := by
        ext i
        show (if i + 1 < k' + 1 then I.var (i + 1) else .zero) = (if i < k' then .var (i + 1) else .zero)
        by_cases h : i < k' <;> simp [h]
      have eC : (((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))).isub ρ'.up).isub Θ =
          ((B2 k' ρ).isub (ρ'.up.comp Θ).tail).inst ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub (ρ'.up.comp Θ)) := by
        rw [Tm.isub_isub, isub_inst, dshift_isub_tail]
      rw [eC] at hX' ⊢
      have e1 : (ρ.comp (ISub.wk k')).comp (ρ'.up.comp Θ) = ρ.comp (ρ'.up.comp Θ).tail := by
        rw [ISub.comp_assoc, hwk]
      have hFcl := closed_of_ty hW (STy k' ρ)
      have hF0 := SFrel k' ρ (k' + 1) (ISub.id (k' + 1)) (ISub.id (k' + 1)) rfl (I_eq_refl _)
      rw [dshift_isub_tail, idt, isub_id_of_closed hFcl] at hF0
      have g := G3 k' ρ (k' + 1) (ISub.wk k') (ρ.comp (ISub.wk k')) rfl
      have hFF := RE2.conv hW g.1 hF0
      refine hIHBT (k' + 1) (ρ.comp (ISub.wk k')) _ _ (hw _ _).1 _ hFF k3 (ρ'.up.comp Θ) _ X' ?_ hX'
      rw [isub_inst]
      have ga := G3 (k' + 1) (ρ.comp (ISub.wk k')) (k3 + 1) (ρ'.up.comp Θ) _ rfl
      have gb := G3 k' ρ (k3 + 1) (ρ'.up.comp Θ).tail _ e1.symm
      have hFΘ : RE2 S (k3 + 1) ((A2 k' ρ).isub (ρ'.up.comp Θ).tail) ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub (ρ'.up.comp Θ))
          ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub (ρ'.up.comp Θ)) := by
        have := SFrel k' ρ (k3 + 1) (ρ'.up.comp Θ) (ρ'.up.comp Θ) rfl (I_eq_refl _)
        rwa [dshift_isub_tail] at this
      have hFΘ' := RE2.conv' hW ga.1 (RE2.conv hW gb.1 hFΘ) (RT2.tyCode_l hW ga.1 (hXA _ _))
      have c1 := ga.2 _ _ hFΘ'
      have c2 := gb.2 _ _ hFΘ
      have u2 := hBpt (k3 + 1) _ _ (RE2.typed (RE2.conv hW gb.1 hFΘ)).1
      exact RT2.trans hW (RT2.tyCode_l hW c1 u2) c1 (RT2.symm hW (RT2.tyCode_l hW c2 u2) c2)
    · -- composition at the end of the left line
      intro X' hX'
      have e1 : (((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))).isub ρ'.up).dinst .one =
          ((B2 k' ρ).isub ρ').inst ((Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))).isub (ISub.cons .one trivial ρ')) := by
        rw [isub_up_dinst _ ρ' .one trivial, isub_inst, dshift_isub_cons]
      rw [e1] at hX' ⊢
      obtain ⟨ls, hs⟩ := hsigTy k' ρ _ _ (hw k' ρ).1
      have hAcl := closed_of_ty hW (HasTy.sigmaDom hs)
      have hKA : KanH2 S k' (A2 k' ρ) (A2 k' ρ) :=
        hIHA k' ρ _ _ (hw k' ρ).1 k' (ISub.id k') _ _ (by rw [isub_id_of_closed hAcl]; exact SAA k' ρ) (SAA k' ρ)
      have htH : HasTy S k' .one [] (Tm.hcomp (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ))) (A2 k' ρ) := minimal_to_spec (parts k' ρ).1
      have hHH := hKA _ _ _ _ _ _ htH htH (EqTm.refl htH) (Steq k' ρ) (ent_refl _) (ent_refl _) (STube k' ρ)
        (Sv0 k' ρ) (Sbd k' ρ) (Sbd' k' ρ)
      refine hIHBH k' ρ _ _ (hw k' ρ).1 _ hHH k'' ρ' _ X' ?_ hX'
      rw [isub_inst]
      apply BL k' ρ k'' ρ'
      exact RE2.symm hW (RT2.isub hW (hXA _ _) (SAA _ _) _)
        (hfill_one_pt hW (Sφ k' ρ) (hXA k' ρ) (SAA k' ρ) (SK k' ρ) htH (STy k' ρ) (STube k' ρ) (Sv0 k' ρ)
          (Sbd k' ρ) ρ')
    · -- the judgmental equality of the tubes
      have hfσ := EqTm.cofIsub hW hφs hteq (ρ.comp ρ')
      rw [isub_dshift] at hfσ
      obtain ⟨ls, hs⟩ := hsigTy k' ρ _ _ (hw k' ρ).1
      have hsL := HasTy.isubS hW hs ρ'
      rw [isub_sigma] at hsL
      have hcl := closed_of_ty hW hsL
      simp only [Tm.closedB, Bool.and_eq_true] at hcl
      have eS : TyEq S k'' (T.isub (ρ.comp ρ')) (.sigma ((A2 k' ρ).isub ρ') ((B2 k' ρ).isub ρ')) := by
        have := (hw k' ρ).1.2.isub hW ρ'
        rwa [Tm.isub_isub, isub_sigma] at this
      have h1 := EqTm.cofConv (Sφ k'' (ρ.comp ρ')) hfσ eS
      rw [← dshift_eq_isub_closed (closed_of_ty hW hsL), isub_sigma] at h1
      have h2 := EqTm.snd h1
      have hfu := EqTm.cofIsub hW (Sφ k' ρ) (minimal_to_spec_eq (parts k' ρ).2.2.2.1) ρ'
      rw [FLeq, fstu1, isub_dshift, ← I_subst_comp, ← dshift_eq_isub_closed hcl.1] at hfu
      have hsW := HasTy.isubS hW hsL (ISub.wk k'')
      rw [isub_sigma] at hsW
      have hscX : (cof .one (φ.subst (ρ.comp ρ').τ)).shift.Scoped (k'' + 1) :=
        KubusCore.I.scoped_shift ⟨trivial, Sφ k'' (ρ.comp ρ')⟩
      have hB := HasTy0.restrict hscX (ent_one _) (HasTy0.sigmaCod hS (spec_to_minimal hW hsW))
      have ic := HasTy0.inst_congr hS hB (spec_to_minimal hW (HasTy.eqR hfu.symm))
        (spec_to_minimal hW (HasTy.eqR hfu)) (spec_to_minimal_eq hW hfu)
      have h3 := minimal_to_spec_eq (EqTm0.conv (spec_to_minimal_eq hW h2) (EqTm0.symm ic))
      rw [isub_inst, isub_dshift, FLeq, ← dshift_eq_isub_closed hcl.2]
      exact h3
    · -- the tubes
      intro k3 σ r r' hr hr' hE hh
      have e : (ρ.comp ρ').comp σ = ρ.comp (ρ'.comp σ) := ISub.comp_assoc _ _ _
      rw [CptL, sndup, sndup, e]
      have hh' : (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp σ)).τ)).holds := by
        rw [← e, I_subst_comp]; exact hh
      have el := Bel k3 _ _ _ (htube k3 (ρ.comp (ρ'.comp σ)) r r' hr hr' hE hh')
      have fp := hfill_face_pt hW (Sφ k' ρ) (hXA k' ρ) (SAA k' ρ) (STy k' ρ) (STube k' ρ) (ρ'.comp σ) r hr
        (by rw [← I_subst_comp]; exact hh')
      rw [fstup] at fp
      have c := BW k' ρ k3 (ρ'.comp σ) _ _ fp
      exact RE2.conv' hW c el (RT2.tyCode_l hW c (RE2.tyCode hW el))
    · -- the bases
      rw [isub_up_dinst _ ρ' .zero trivial, isub_inst, dshift_isub_cons]
      have el := Bel k'' (ρ.comp ρ') _ _ (RE2.isub hW ha0 (ρ.comp ρ'))
      have zp := hfill_zero_pt hW (Sφ k' ρ) (hXA k' ρ) (SAA k' ρ) (STy k' ρ) (STube k' ρ) (Sv0 k' ρ) (Sbd k' ρ) ρ'
      rw [fsta] at zp
      have c := BW k' ρ k'' ρ' _ _ zp
      exact RE2.conv' hW c el (RT2.tyCode_l hW c (RE2.tyCode hW el))
    · -- the boundary, on the left
      intro k3 σ hh
      have e : (ρ.comp ρ').comp σ = ρ.comp (ρ'.comp σ) := ISub.comp_assoc _ _ _
      rw [CptL, sndup, snda, e]
      have hh' : (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp σ)).τ)).holds := by
        rw [← e, I_subst_comp]; exact hh
      have hh2 : (ival (idEnv k3) ((φ.subst ρ.τ).subst (ρ'.comp σ).τ)).holds := by
        rw [← I_subst_comp]; exact hh'
      have el := Bel k3 _ _ _ (hbd k3 _ hh')
      have zp := hfill_zero_pt hW (Sφ k' ρ) (hXA k' ρ) (SAA k' ρ) (STy k' ρ) (STube k' ρ) (Sv0 k' ρ) (Sbd k' ρ)
        (ρ'.comp σ)
      have sb := Sbd k' ρ k3 (ρ'.comp σ) hh2
      rw [fstup, fsta] at sb
      rw [fsta] at zp
      have hAs := RT2.isub hW (hXA _ _) (SAA k' ρ) (ρ'.comp σ)
      have c := BW k' ρ k3 (ρ'.comp σ) _ _ (RE2.trans hW hAs zp (RE2.symm hW hAs sb))
      exact RE2.conv' hW c el (RT2.tyCode_l hW c (RE2.tyCode hW el))
    · -- the boundary, on the right
      intro k3 σ hh
      have e : (ρ.comp ρ').comp σ = ρ.comp (ρ'.comp σ) := ISub.comp_assoc _ _ _
      rw [CptL, sndup, snda, e]
      have hh' : (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp σ)).τ)).holds := by
        rw [← e, I_subst_comp]; exact hh
      have el := Bel k3 _ _ _ (hbd' k3 _ hh')
      have zp := hfill_zero_pt hW (Sφ k' ρ) (hXA k' ρ) (SAA k' ρ) (STy k' ρ) (STube k' ρ) (Sv0 k' ρ) (Sbd k' ρ)
        (ρ'.comp σ)
      rw [fsta] at zp
      have c := BW k' ρ k3 (ρ'.comp σ) _ _ zp
      exact RE2.conv' hW c el (RT2.tyCode_l hW c (RE2.tyCode hW el))
  -- the second projections where the face holds
  have faceFst : ∀ k3 (σ : ISub k3 k), I.Entails .one (φ.subst σ.τ) →
      RE2 S k3 (A1.isub σ) ((Tm.fst (.hcomp T φ u a0)).isub σ) (.fst ((u.isub σ.up).dinst .one)) := by
    intro k3 σ hf
    have hs := stable_fst_hcompFace hW hf (hρT k3 σ) (eTs k3 σ)
    have ht1 := HasTy.eqR (EqTm.fst ((EqTm.hcompFace hf (hρT k3 σ)).tyConv (eTs k3 σ)))
    exact RE2.reduceR hW (hA1ρ k3 σ) (Fs k3 σ) hs ht1
  have faceRel : ∀ k3 (σ : ISub k3 k), I.Entails .one (φ.subst σ.τ) →
      RE2 S k3 ((B1.inst (.fst (.hcomp T φ u a0))).isub σ) (.snd ((u.isub σ.up).dinst .one))
        (.snd ((u'.isub σ.up).dinst .one)) := by
    intro k3 σ hf
    have hh := (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 hf
    have el := Bel k3 σ _ _ (htube k3 σ .one .one trivial trivial (I_eq_refl _) hh)
    have c := (CohId k3 σ).2 _ _ (faceFst k3 σ hf)
    rw [isub_inst]
    exact RE2.conv' hW c el (RT2.tyCode_l hW c (RE2.tyCode hW el))
  -- the expansion
  have ht0 : HasTy S k .one [] (.snd (.hcomp T φ u a0)) (B1.inst (.fst (.hcomp T φ u a0))) :=
    HasTy.snd (hty.tyConv hR.2)
  have hX := tyCode_of_ty hW ht0
  have hB1c : B1.isub (ISub.id k) = B1 := by
    have hcl := closed_of_ty hW hsig
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    exact isub_id_of_closed hcl.2
  have hfc : (Tm.fst (.hcomp T φ u a0)).isub (ISub.id k) = Tm.fst (.hcomp T φ u a0) :=
    isub_id_of_closed (closed_of_ty hW (RE2.typed FST).1)
  have hfc' : (Tm.fst (.hcomp T' φ' u' a0')).isub (ISub.id k) = Tm.fst (.hcomp T' φ' u' a0') :=
    isub_id_of_closed (closed_of_ty hW (RE2.typed FST).2.1)
  have hYY : RT2 S k (B1.inst (.fst (.hcomp T φ u a0))) (B1.inst (.fst (.hcomp T φ u a0))) := by
    have := (CohId k (ISub.id k)).2 _ _ (Fs k (ISub.id k))
    rw [hB1c, hfc] at this
    exact RT2.refl hW hX this
  have hB1f : RT2 S k (B1.inst (.fst (.hcomp T φ u a0))) (B1.inst (.fst (.hcomp T' φ' u' a0'))) := by
    have := B1rel k (ISub.id k) _ _ (Fρ k (ISub.id k))
    rwa [hB1c, hfc, hfc'] at this
  have ht' : HasTy S k .one [] (.snd (.hcomp T' φ' u' a0')) (B1.inst (.fst (.hcomp T φ u a0))) :=
    (HasTy.snd (hty'.tyConv hR.2)).tyConv (TyEq.symm (tyB hB1f))
  refine RE2.expandBoth hW hX hYY ht0 ht'
    (fun k' ρ => if I.Entails .one (φ.subst ρ.τ) then Tm.snd ((u.isub ρ.up).dinst .one)
      else Tm.comp ((B2 k' ρ).dshift.inst (Tm.hfill (A2 k' ρ) (φ.subst ρ.τ) (.fst (u.isub ρ.up)) (.fst (a0.isub ρ)))) (φ.subst ρ.τ) (.snd (u.isub ρ.up)) (.snd (a0.isub ρ)))
    (fun k' ρ => if I.Entails .one (φ'.subst ρ.τ) then Tm.snd ((u'.isub ρ.up).dinst .one)
      else Tm.comp ((B2' k' ρ).dshift.inst (Tm.hfill (A2' k' ρ) (φ'.subst ρ.τ) (.fst (u'.isub ρ.up)) (.fst (a0'.isub ρ)))) (φ'.subst ρ.τ) (.snd (u'.isub ρ.up)) (.snd (a0'.isub ρ)))
    (fun k' ρ => ?_) (fun k' ρ => ?_) (fun k' ρ k'' ρ' => ?_)
  · by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · simp only [if_pos hf]; exact faceL k' ρ hf
    · simp only [if_neg hf]; exact sndL k' ρ hf
  · by_cases hf : I.Entails .one (φ'.subst ρ.τ)
    · simp only [if_pos hf]; exact faceR k' ρ hf
    · simp only [if_neg hf]; exact sndR k' ρ hf
  · by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · have hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ) := ent_comp hf
      have hf2' : I.Entails .one (φ'.subst (ρ.comp ρ').τ) := ent_trans hf2 (ent_subst h12 _)
      simp only [if_pos hf, if_pos hf2']
      rw [show (Tm.snd ((u.isub ρ.up).dinst .one)).isub ρ' = .snd ((u.isub (ρ.comp ρ').up).dinst .one) by
        show Tm.snd (((u.isub ρ.up).dinst .one).isub ρ') = _; rw [up_dinst_one_isub]]
      exact faceRel k'' _ hf2
    · simp only [if_neg hf]
      rw [comp_isub, ← I_subst_comp, sndu1, snda]
      by_cases hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ)
      · simp only [if_pos (ent_trans hf2 (ent_subst h12 _))]
        have hcT := HasTy.isubS hW (HasTy.eqR (sndL k' ρ hf).2) ρ'
        rw [Tm.isub_isub (B1.inst _), comp_isub, ← I_subst_comp, sndu1, snda, comp_eq] at hcT
        have hYσ := RT2.isub hW hX hYY (ρ.comp ρ')
        have e0 := faceRel k'' (ρ.comp ρ') hf2
        have hh2 := (holds_iff_entails (I.scoped_subst hφs (ρ.comp ρ').sc)).2 hf2
        have t2 := hcomp_tube_typed' hW hcT .one trivial hh2
        rw [compTube_d1] at t2
        have s1 := stable_hcompFace hW hf2 hcT
        rw [compTube_d1] at s1
        have s2 := stable_transpFace hW (ent_refl .one) t2
        have e1 := RE2.expandL hW hYσ t2 (RE2.typed e0).2.1 s2 e0
        rw [comp_eq]
        exact RE2.expandL hW hYσ hcT (RE2.typed e0).2.1 s1 e1
      · have hf2' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hf2 (ent_trans h (ent_subst h21 _))
        simp only [if_neg hf2']
        exact compC k' ρ k'' ρ' hf2

end

end Model.Whnf
