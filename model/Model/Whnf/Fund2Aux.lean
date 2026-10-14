import Model.Whnf.Fund2Hyp

/-!
# Auxiliary lemmas for the binary fundamental lemma

Transfer of related elements along chains of type equations (`ElTr2`), the computation rules whose
closed instances come from the Kan oracle, `transpU` (a stable step), and Glue η from the validity of
the Glue type alone.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-! ### Transfer along type equations -/

omit hW in
theorem ElTr2.refl (X : Tm) : ElTr2 S Ψ Φ Γ X X := fun _ _ _ _ h => h

omit hW in
theorem ElTr2.trans {X Y Z : Tm} (h1 : ElTr2 S Ψ Φ Γ X Y) (h2 : ElTr2 S Ψ Φ Γ Y Z) : ElTr2 S Ψ Φ Γ X Z :=
  fun k c x y h => h2 k c x y (h1 k c x y h)

theorem ElTr2.of_valid {X Y : Tm} {m : ℕ} (h : Valid2 S Ψ Φ Γ X Y (.univ m)) : ElTr2 S Ψ Φ Γ X Y :=
  fun k c _ _ hxy => RE2.conv hW (h.ty hW (c.diagL hW)) hxy

omit hW in
theorem ElTr2.restrict {Φ' : I} {X Y : Tm} (he : I.Entails Φ' Φ) (h : ElTr2 S Ψ Φ Γ X Y) :
    ElTr2 S Ψ Φ' Γ X Y :=
  fun k c x y hxy => h k (c.restrictTo he) x y hxy

theorem RE2_cumul {l : ℕ} (hl : l + 1 ≤ maxLevel) {T T' : Tm} (h : RE2 S k (.univ l) T T') :
    RE2 S k (.univ (l + 1)) T T' := by
  obtain ⟨he, hm, hrt⟩ := (RE2_univ_iff hW).1 h
  refine (RE2_univ_iff hW).2 ⟨⟨HasTy.cumul hl he.1, HasTy.cumul hl he.2.1, EqTm.cumul hl he.2.2⟩, ?_, hrt⟩
  have hm' := ZFSet.mem_sep.1 hm
  exact ZFSet.mem_sep.2 ⟨Vt_subset_succ l (by unfold maxLevel at hl; omega) hm'.1, hm'.2.cumul⟩

theorem ElTr2.cumul {l : ℕ} (hl : l + 1 ≤ maxLevel) : ElTr2 S Ψ Φ Γ (.univ l) (.univ (l + 1)) :=
  fun _ _ _ _ h => RE2_cumul hW hl h

omit hW in
/-- Converting the type of a valid equation along a transfer, given the relation of the target type. -/
theorem valid_conv_tr {t u X Y : Tm} (h : Valid2 S Ψ Φ Γ t u X) (htr : ElTr2 S Ψ Φ Γ X Y)
    (hY : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L Y) (c.R Y)) : Valid2 S Ψ Φ Γ t u Y :=
  fun k c => ⟨hY k c, htr k c _ _ (h k c).2⟩

/-- The type of a valid equation, as a valid type. -/
theorem valid_ty_of {t u A : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ t u A) (hA : HasTy0 S Ψ Φ Γ A (.univ l)) :
    Valid2 S Ψ Φ Γ A A (.univ l) :=
  valid_univ_of hW hA hA (EqTm0.refl hA) fun k c => (h k c).1

/-! ### `transpU` -/

theorem stable_transpU {X a : Tm} {l : ℕ} {φ : I} (hty : HasTy S k .one [] (.transp (.univ l) φ a) X) :
    StableE S k X (.transp (.univ l) φ a) a := by
  intro k' σ
  have hσ : HasTy S k' .one [] (.transp (.univ l) (φ.subst σ.τ) (a.isub σ)) (X.isub σ) := HasTy.isubS hW hty σ
  show Red S (.transp (.univ l) (φ.subst σ.τ) (a.isub σ)) _ ∧ _
  refine ⟨.step ?_ (.refl _), EqTm.transpU hσ⟩
  by_cases h : I.Entails .one (φ.subst σ.τ)
  · exact step_transp_face h
  · exact step_transp_univ h

theorem valid_transpU {a T : Tm} {l : ℕ} {φ : I}
    (h : Valid2 S Ψ Φ Γ (.transp (.univ l) φ a) (.transp (.univ l) φ a) T)
    (hty : HasTy0 S Ψ Φ Γ (.transp (.univ l) φ a) T) (hu : HasTy0 S Ψ Φ Γ a T) :
    Valid2 S Ψ Φ Γ (.transp (.univ l) φ a) a T :=
  valid_redR hW h hu fun k c => stable_transpU hW (c.tyR' hW hty)

/-! ### Glue η from the validity of the Glue type -/

/-- `glueEta`, with the equivalence related through the Glue type's relation (`valid_glueEta` asks for
the validity of the equivalence itself). -/
theorem valid_glueEta_ty {A T e g : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) (.univ l))
    (he0 : HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (hg : Valid2 S Ψ Φ Γ g g (.glue A φ T e)) (hty : HasTy0 S Ψ Φ Γ g (.glue A φ T e))
    (hu : HasTy0 S Ψ Φ Γ (.glueEl φ e g (.unglue φ e g)) (.glue A φ T e)) :
    Valid2 S Ψ Φ Γ g (.glueEl φ e g (.unglue φ e g)) (.glue A φ T e) := by
  intro k c
  refine ⟨(hg k c).1, ?_⟩
  have hφL := I.scoped_subst hφ c.σ.sc
  have hφR := I.scoped_subst hφ c.σ'.sc
  have hgr := (hg k c).2
  have hGt : HasTy S k .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.univ l) :=
    (RE2.typed (hG k c).2).1
  have hGtR : HasTy S k .one [] (.glue (c.R A) (φ.subst c.σ'.τ) (c.R T) (c.R e)) (.univ l) :=
    (RE2.typed (hG k c).2).2.1
  have hGG : RT2 S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) :=
    hG.ty hW (c.diagL hW)
  have e12 : I.Entails (φ.subst c.σ.τ) (φ.subst c.σ'.τ) := eq_ent (c.ieq_subst (I_eq_refl φ))
  have e21 : I.Entails (φ.subst c.σ'.τ) (φ.subst c.σ.τ) := eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ)))
  have hηR : HasTy S k .one [] (.glueEl (φ.subst c.σ'.τ) (c.R e) (c.R g) (.unglue (φ.subst c.σ'.τ) (c.R e) (c.R g)))
      (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := c.tyR' hW hu
  by_cases hh : (ival (idEnv k) (φ.subst c.σ.τ)).holds
  · have hφe := (holds_iff_entails hφL).1 hh
    exact RE2.expandR hW hGG (c.ty hW hty) hηR (stable_glueEl hW hηR (ent_trans hφe e12)) hgr
  · have hn : ¬ I.Entails .one (φ.subst c.σ.τ) := fun h => hh ((holds_iff_entails hφL).2 h)
    have hnR : ¬ I.Entails .one (φ.subst c.σ'.τ) := fun h => hn (ent_trans h e21)
    have hinv := RT2_glue_inv hW hGt hGt hn hn hGG
    have hinvLR := RT2_glue_inv hW hGt hGtR hn hnR (hG.ty hW c)
    have hXA : TyCode k (semK S k (c.L A)) := tyCode_of_univ hW (glue_data hW hGt).2.choose_spec.1
    have hXG : TyCode k (semK S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e))) := tyCode_of_univ hW hGt
    have hyy := (perK hW hXG).reflEl' hGG hgr
    have ee' : EqTm S k (cof .one (φ.subst c.σ.τ)) [] (c.R e) (c.L e) (Tm.equiv (c.L T) (c.L A)) := by
      have := c.eqCof hW hφL (EqTm0.refl he0)
      rw [show c.L (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) from equiv_subst (σ := c.γ) (τ := c.σ.τ) T A] at this
      exact this.symm
    have hyη : EqTm S k .one [] (c.R g)
        (.glueEl (φ.subst c.σ'.τ) (c.R e) (c.R g) (.unglue (φ.subst c.σ'.τ) (c.R e) (c.R g)))
        (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) :=
      (RE2.typed hgr).2.2.symm.trans (c.eq hW (EqTm0.glueEta hty))
    exact RE2.trans hW hGG hgr (RE2_glue_eta hW hGt hh hyy hyη hφR e12 e21 ee'
      (fun k' σ => RT2.isub hW hXA hinv.1 σ) (fun k' σ hh' => (hinv.2 k' σ hh').1)
      (fun k' σ hh' => (hinvLR.2 k' σ hh').2))

/-! ### Inverted typings

The fundamental lemma inverts the typings of systems, compositions, transports and Glue terms within
its induction (the conversions and restrictions above the rule are sub-derivations). These are the
facts it extracts, with their closure under conversion, restriction and cumulativity. -/

/-- The inverted typing of a system. -/
def SplitInv (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (φ : I) (t : Tm) (ψ : I) (u T : Tm) : Prop :=
  φ.Scoped Ψ ∧ ψ.Scoped Ψ ∧ I.Entails Φ (.or φ ψ) ∧ Valid2 S Ψ (cof Φ φ) Γ t t T ∧
    Valid2 S Ψ (cof Φ ψ) Γ u u T ∧ Valid2 S Ψ (cof (cof Φ φ) ψ) Γ t u T

theorem SplitInv.conv {φ ψ : I} {t u T T' : Tm} {m : ℕ} (h : SplitInv S Ψ Φ Γ φ t ψ u T)
    (hT : Valid2 S Ψ Φ Γ T T' (.univ m)) : SplitInv S Ψ Φ Γ φ t ψ u T' :=
  ⟨h.1, h.2.1, h.2.2.1, valid_conv hW h.2.2.2.1 (valid_restrict hW (ent_and_left _ _) hT),
    valid_conv hW h.2.2.2.2.1 (valid_restrict hW (ent_and_left _ _) hT),
    valid_conv hW h.2.2.2.2.2 (valid_restrict hW (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hT)⟩

theorem SplitInv.restrict {Φ' φ ψ : I} {t u T : Tm} (he : I.Entails Φ' Φ) (h : SplitInv S Ψ Φ Γ φ t ψ u T) :
    SplitInv S Ψ Φ' Γ φ t ψ u T :=
  ⟨h.1, h.2.1, ent_trans he h.2.2.1, valid_restrict hW (ent_and_mono he (ent_refl _)) h.2.2.2.1,
    valid_restrict hW (ent_and_mono he (ent_refl _)) h.2.2.2.2.1,
    valid_restrict hW (ent_and_mono (ent_and_mono he (ent_refl _)) (ent_refl _)) h.2.2.2.2.2⟩

theorem SplitInv.cumul {φ ψ : I} {t u : Tm} {l : ℕ} (hl : l + 1 ≤ maxLevel)
    (h : SplitInv S Ψ Φ Γ φ t ψ u (.univ l)) : SplitInv S Ψ Φ Γ φ t ψ u (.univ (l + 1)) :=
  ⟨h.1, h.2.1, h.2.2.1, valid_cumul hW hl h.2.2.2.1, valid_cumul hW hl h.2.2.2.2.1, valid_cumul hW hl h.2.2.2.2.2⟩

/-- The inverted typing of a composition at `T`. -/
def HcompInv (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (A : Tm) (φ : I) (u a T : Tm) : Prop :=
  ∃ l, φ.Scoped Ψ ∧ Valid2 S Ψ Φ Γ A A (.univ l) ∧ Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u u A.dshift ∧
    Valid2 S Ψ Φ Γ a a A ∧ Valid2 S Ψ (cof Φ φ) Γ (u.dinst .zero) a A ∧ ElTr2 S Ψ Φ Γ A T ∧
    HasTy0 S Ψ Φ Γ A (.univ l) ∧ HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift ∧ HasTy0 S Ψ Φ Γ a A ∧
    EqTm0 S Ψ (cof Φ φ) Γ (u.dinst .zero) a A

theorem HcompInv.conv {A u a T T' : Tm} {φ : I} {m : ℕ} (h : HcompInv S Ψ Φ Γ A φ u a T)
    (hT : Valid2 S Ψ Φ Γ T T' (.univ m)) : HcompInv S Ψ Φ Γ A φ u a T' := by
  obtain ⟨l, h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨l, h0, h1, h2, h3, h4, h5.trans (ElTr2.of_valid hW hT), h6⟩

theorem HcompInv.restrict {Φ' φ : I} {A u a T : Tm} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (h : HcompInv S Ψ Φ Γ A φ u a T) : HcompInv S Ψ Φ' Γ A φ u a T := by
  obtain ⟨l, h0, h1, h2, h3, h4, h5, t1, t2, t3, t4⟩ := h
  have hs' : (cof Φ' φ).Scoped Ψ := ⟨hs, h0⟩
  have he' : I.Entails (cof Φ' φ) (cof Φ φ) := ent_and_mono he (ent_refl _)
  exact ⟨l, h0, valid_restrict hW he h1, valid_restrict hW (ent_shift he') h2,
    valid_restrict hW he h3, valid_restrict hW he' h4, h5.restrict he, HasTy0.restrict hs he t1,
    HasTy0.restrict (KubusCore.I.scoped_shift hs') (ent_shift he') t2, HasTy0.restrict hs he t3,
    EqTm0.restrict hs' he' t4⟩

theorem HcompInv.cumul {A u a : Tm} {φ : I} {l : ℕ} (hl : l + 1 ≤ maxLevel)
    (h : HcompInv S Ψ Φ Γ A φ u a (.univ l)) : HcompInv S Ψ Φ Γ A φ u a (.univ (l + 1)) := by
  obtain ⟨l', h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨l', h0, h1, h2, h3, h4, h5.trans (ElTr2.cumul hW hl), h6⟩

/-- The inverted typing of a transport at `T`. -/
def TranspInv (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (A : Tm) (φ : I) (a T : Tm) : Prop :=
  ∃ l, φ.Scoped Ψ ∧ Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A (.univ l) ∧
    Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l) ∧
    Valid2 S Ψ Φ Γ a a (A.dinst .zero) ∧ ElTr2 S Ψ Φ Γ (A.dinst .one) T ∧
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (.univ l) ∧
    EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l) ∧ HasTy0 S Ψ Φ Γ a (A.dinst .zero)

theorem TranspInv.conv {A a T T' : Tm} {φ : I} {m : ℕ} (h : TranspInv S Ψ Φ Γ A φ a T)
    (hT : Valid2 S Ψ Φ Γ T T' (.univ m)) : TranspInv S Ψ Φ Γ A φ a T' := by
  obtain ⟨l, h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨l, h0, h1, h2, h3, h4.trans (ElTr2.of_valid hW hT), h5⟩

theorem TranspInv.restrict {Φ' φ : I} {A a T : Tm} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (h : TranspInv S Ψ Φ Γ A φ a T) : TranspInv S Ψ Φ' Γ A φ a T := by
  obtain ⟨l, h0, h1, h2, h3, h4, t1, t2, t3⟩ := h
  have hs' : (cof Φ' φ).Scoped Ψ := ⟨hs, h0⟩
  have he' : I.Entails (cof Φ' φ) (cof Φ φ) := ent_and_mono he (ent_refl _)
  exact ⟨l, h0, valid_restrict hW (ent_shift he) h1,
    valid_restrict hW (ent_shift he') h2, valid_restrict hW he h3, h4.restrict he,
    HasTy0.restrict (KubusCore.I.scoped_shift hs) (ent_shift he) t1,
    EqTm0.restrict (KubusCore.I.scoped_shift hs') (ent_shift he') t2, HasTy0.restrict hs he t3⟩

theorem TranspInv.cumul {A a : Tm} {φ : I} {l : ℕ} (hl : l + 1 ≤ maxLevel)
    (h : TranspInv S Ψ Φ Γ A φ a (.univ l)) : TranspInv S Ψ Φ Γ A φ a (.univ (l + 1)) := by
  obtain ⟨l', h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨l', h0, h1, h2, h3, h4.trans (ElTr2.cumul hW hl), h5⟩

/-- The inverted typing of a Glue introduction at `G`. -/
def GlueElInv (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (φ : I) (e t a G : Tm) : Prop :=
  ∃ A T l, φ.Scoped Ψ ∧ HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e) ∧
    HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l) ∧
    HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A) ∧ Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A) ∧
    Valid2 S Ψ (cof Φ φ) Γ t t T ∧ Valid2 S Ψ Φ Γ a a A ∧ Valid2 S Ψ (cof Φ φ) Γ (.app (.fst e) t) a A ∧
    ElTr2 S Ψ Φ Γ (.glue A φ T e) G

theorem GlueElInv.conv {φ : I} {e t a G G' : Tm} {m : ℕ} (h : GlueElInv S Ψ Φ Γ φ e t a G)
    (hG : Valid2 S Ψ Φ Γ G G' (.univ m)) : GlueElInv S Ψ Φ Γ φ e t a G' := by
  obtain ⟨A, T, l, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨A, T, l, h0, h1, h2, h3, h4, h5, h6, h7, h8.trans (ElTr2.of_valid hW hG)⟩

theorem GlueElInv.restrict {Φ' φ : I} {e t a G : Tm} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (h : GlueElInv S Ψ Φ Γ φ e t a G) : GlueElInv S Ψ Φ' Γ φ e t a G := by
  obtain ⟨A, T, l, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hs' : (cof Φ' φ).Scoped Ψ := ⟨hs, h0⟩
  have he' : I.Entails (cof Φ' φ) (cof Φ φ) := ent_and_mono he (ent_refl _)
  exact ⟨A, T, l, h0, HasTy0.restrict hs he h1, HasTy0.restrict hs he h2, HasTy0.restrict hs' he' h3,
    valid_restrict hW he' h4, valid_restrict hW he' h5, valid_restrict hW he h6, valid_restrict hW he' h7,
    h8.restrict he⟩

theorem GlueElInv.cumul {φ : I} {e t a : Tm} {l : ℕ} (hl : l + 1 ≤ maxLevel)
    (h : GlueElInv S Ψ Φ Γ φ e t a (.univ l)) : GlueElInv S Ψ Φ Γ φ e t a (.univ (l + 1)) := by
  obtain ⟨A, T, l', h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨A, T, l', h0, h1, h2, h3, h4, h5, h6, h7, h8.trans (ElTr2.cumul hW hl)⟩

/-- The inverted typing of an `unglue` at `G`, with that of its argument if it is a Glue
introduction. -/
def UnglueInv (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (φ : I) (e g G : Tm) : Prop :=
  ∃ A T l, φ.Scoped Ψ ∧ HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l) ∧ HasTy0 S Ψ Φ Γ A (.univ l) ∧
    HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A) ∧ Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A) ∧
    Valid2 S Ψ Φ Γ A A (.univ l) ∧ ElTr2 S Ψ Φ Γ A G ∧
    ∀ t a, g = .glueEl φ e t a → GlueElInv S Ψ Φ Γ φ e t a (.glue A φ T e)

theorem UnglueInv.conv {φ : I} {e g G G' : Tm} {m : ℕ} (h : UnglueInv S Ψ Φ Γ φ e g G)
    (hG : Valid2 S Ψ Φ Γ G G' (.univ m)) : UnglueInv S Ψ Φ Γ φ e g G' := by
  obtain ⟨A, T, l, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨A, T, l, h0, h1, h2, h3, h4, h5, h6.trans (ElTr2.of_valid hW hG), h7⟩

theorem UnglueInv.restrict {Φ' φ : I} {e g G : Tm} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (h : UnglueInv S Ψ Φ Γ φ e g G) : UnglueInv S Ψ Φ' Γ φ e g G := by
  obtain ⟨A, T, l, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hs' : (cof Φ' φ).Scoped Ψ := ⟨hs, h0⟩
  have he' : I.Entails (cof Φ' φ) (cof Φ φ) := ent_and_mono he (ent_refl _)
  exact ⟨A, T, l, h0, HasTy0.restrict hs he h1, HasTy0.restrict hs he h2, HasTy0.restrict hs' he' h3,
    valid_restrict hW he' h4, valid_restrict hW he h5, h6.restrict he,
    fun t a hg => (h7 t a hg).restrict hW hs he⟩

theorem UnglueInv.cumul {φ : I} {e g : Tm} {l : ℕ} (hl : l + 1 ≤ maxLevel)
    (h : UnglueInv S Ψ Φ Γ φ e g (.univ l)) : UnglueInv S Ψ Φ Γ φ e g (.univ (l + 1)) := by
  obtain ⟨A, T, l', h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨A, T, l', h0, h1, h2, h3, h4, h5, h6.trans (ElTr2.cumul hW hl), h7⟩

omit hW in
/-- The type of an element of a Glue type is typed, with its face scoped and its equivalence typed. -/
theorem glue_ty_of_el (hW : WfSig S) {g A T e : Tm} {φ : I} (h : HasTy0 S Ψ Φ Γ g (.glue A φ T e)) :
    ∃ l, HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l) ∧ φ.Scoped Ψ ∧ HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A) := by
  rcases pre_ty (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 h with ⟨l, h'⟩ | ⟨l, he, -⟩
  · obtain ⟨_, ⟨-, hφ, -, he0⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) h' rfl
    exact ⟨l, h', hφ, he0⟩
  · cases he

/-! ### Computation rules from the oracle -/

/-- The inverted formation of a Glue type, with validity of its components. -/
def GlueTyInv (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (A : Tm) (φ : I) (T e : Tm) : Prop :=
  ∃ l, φ.Scoped Ψ ∧ Valid2 S Ψ Φ Γ A A (.univ l) ∧ Valid2 S Ψ (cof Φ φ) Γ T T (.univ l) ∧
    Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A) ∧ HasTy0 S Ψ Φ Γ A (.univ l) ∧
    HasTy0 S Ψ (cof Φ φ) Γ T (.univ l) ∧ HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A)

theorem GlueTyInv.restrict {Φ' φ : I} {A T e : Tm} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (h : GlueTyInv S Ψ Φ Γ A φ T e) : GlueTyInv S Ψ Φ' Γ A φ T e := by
  obtain ⟨l, h0, h1, h2, h3, t1, t2, t3⟩ := h
  have hs' : (cof Φ' φ).Scoped Ψ := ⟨hs, h0⟩
  have he' : I.Entails (cof Φ' φ) (cof Φ φ) := ent_and_mono he (ent_refl _)
  exact ⟨l, h0, valid_restrict hW he h1, valid_restrict hW he' h2, valid_restrict hW he' h3,
    HasTy0.restrict hs he t1, HasTy0.restrict hs' he' t2, HasTy0.restrict hs' he' t3⟩

end

end Model.Whnf
