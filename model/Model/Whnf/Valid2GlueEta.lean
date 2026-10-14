import Model.Whnf.Valid2Glue

/-!
# Semantic validity of the Glue computation rules: `unglueFace`, `glueBeta`, `glueEta`
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- Glue eta at one stage: an element of a Glue type whose face does not hold is related to the Glue
introduction of itself and its `unglue`, for agreeing annotations. -/
theorem RE2_glue_eta {A T e e' y : Tm} {φ φ' : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hn : ¬ (ival (idEnv k) φ).holds)
    (hyy : RE2 S k (.glue A φ T e) y y)
    (hyη : EqTm S k .one [] y (.glueEl φ' e' y (.unglue φ' e' y)) (.glue A φ T e))
    (hφ' : φ'.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ee' : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A))
    (hAA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A.isub σ))
    (hTT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ))
    (hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)) :
    RE2 S k (.glue A φ T e) y (.glueEl φ' e' y (.unglue φ' e' y)) := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  have hyE := RE2.typed hyy
  have hu : HasTy S k .one [] (.unglue φ e y) A := unglue_ty hW hGK ⟨lA, hA0, he0⟩ hyE.1
  have hη := HasTy.eqR hyη
  obtain ⟨l2, hG2, eG2⟩ := glue_annot_eq hW hG hφ' h12 h21 ee'
  have hy2 : HasTy S k .one [] y (.glue A φ' T e') := hyE.1.conv eG2
  have c21 : I.Entails (cof .one φ') (cof .one φ) :=
    ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) h21)
  have he0' : HasTy S k (cof .one φ') [] e' (Tm.equiv T A) :=
    HasTy.restrict (show (cof .one φ').Scoped k from ⟨trivial, hφ'⟩) c21 (HasTy.eqL ee')
  have hu' : HasTy S k .one [] (.unglue φ' e' y) A := unglue_ty hW ⟨l2, .inl hG2⟩ ⟨lA, hA0, he0'⟩ hy2
  have hΦ : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  have hUA := RE2_unglue_and hW hG hn hyy hu hu' hφ' h12 h21 ee' hAA hTT hE
  have hent : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → I.Entails .one (φ.subst σ.τ) :=
    fun σ hh => (holds_iff_entails (I.scoped_subst hφs σ.sc)).1 hh
  have hne : ∀ {k'} (σ : ISub k' k), ¬ (ival (idEnv k') (φ.subst σ.τ)).holds → ¬ I.Entails .one (φ.subst σ.τ) :=
    fun σ hh h => hh ((holds_iff_entails (I.scoped_subst hφs σ.sc)).2 h)
  have hXA : ∀ k' (σ : ISub k' k), TyCode k' (semK S k' (A.isub σ)) := fun k' σ =>
    tyCode_of_univ hW (HasTy.isubS hW hA0 σ)
  have hησ : ∀ {k'} (σ : ISub k' k), HasTy S k' .one []
      (.glueEl (φ'.subst σ.τ) (e'.isub σ) (y.isub σ) ((Tm.unglue φ' e' y).isub σ)) ((Tm.glue A φ T e).isub σ) :=
    fun σ => HasTy.isubS hW hη σ
  have ee'σ : ∀ {k'} (σ : ISub k' k), EqTm S k' (cof .one (φ.subst σ.τ)) [] (e'.isub σ) (e.isub σ)
      (Tm.equiv (T.isub σ) (A.isub σ)) := fun σ => by
    have := EqTm.isubF hW hΦ ee' σ; rwa [isub_equiv] at this
  have hyy' := hyy
  unfold RE2 at hyy'
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
    at hyy'
  obtain ⟨-, hmem, -, hmain, hcoh, -⟩ := hyy'
  -- the fiber relation at the Glue type, as a relation at the fiber type
  have fib : ∀ {k'} (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) {x z : Tm},
      (Comp2 S (dat (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k))) k' ((Hom.id k).comp σ.hom))
        k' k' (Hom.id k')).el ((Tm.glue A φ T e).isub σ) x z → RE2 S k' (T.isub σ) x z := by
    intro k' σ hh x z h
    rw [Hom.id_comp, dat_glue_fiber σ ((face_holds_iff hφs σ).2 hh)] at h
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh
    have hX := tyCode_of_univ hW hTσ
    have hGσ : IsTyK S k' ((Tm.glue A φ T e).isub σ) := ⟨l, .inl (HasTy.isubS hW hG σ)⟩
    have hfc : TyEq S k' ((Tm.glue A φ T e).isub σ) (T.isub σ) := by
      rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ (hent σ hh)
    have hTG : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
      refine ty_expandSR hW hX (hGσ.of_tyEq hfc) hGσ ?_ (hTT k' σ hh)
      rw [isub_glue] at hGσ ⊢
      exact stable_glue hW hGσ (hent σ hh)
    have P := per2_tyCode hW hX k' (Hom.id k')
    exact P.conv (P.symTy hTG) h
  -- `y` with itself in the fiber, where the face holds
  have fibY : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (y.isub σ) (y.isub σ) := fun σ hh => fib σ hh (by
    have := hmain _ σ; unfold glueLocE at this
    rwa [if_pos (by rw [Hom.id_comp]; exact (face_holds_iff hφs σ).2 hh)] at this)
  -- the relation at a stage where the face holds
  have faceη : ∀ {k'} (σ : ISub k' k) (hh : (Cof.restr (ival (idEnv k) φ).face ((Hom.id k).comp σ.hom)).holds),
      (Comp2 S (dat (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k))) k' ((Hom.id k).comp σ.hom))
        k' k' (Hom.id k')).el ((Tm.glue A φ T e).isub σ) (y.isub σ)
        ((Tm.glueEl φ' e' y (.unglue φ' e' y)).isub σ) := by
    intro k' σ hh
    have hfy := hmain k' σ
    unfold glueLocE at hfy; rw [if_pos hh] at hfy
    rw [Hom.id_comp] at hh hfy ⊢
    rw [dat_glue_fiber σ hh] at hfy ⊢
    have hh' := (face_holds_iff hφs σ).1 hh
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh'
    have hX := tyCode_of_univ hW hTσ
    have hGσ : IsTyK S k' ((Tm.glue A φ T e).isub σ) := ⟨l, .inl (HasTy.isubS hW hG σ)⟩
    have hface : TyEq S k' ((Tm.glue A φ T e).isub σ) (T.isub σ) := by
      rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ (hent σ hh')
    have hTG : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
      refine ty_expandSR hW hX (hGσ.of_tyEq hface) hGσ ?_ (hTT k' σ hh')
      rw [isub_glue] at hGσ ⊢
      exact stable_glue hW hGσ (hent σ hh')
    have hGGT := (per2_tyCode hW hX k' (Hom.id k')).reflTy' hTG
    rw [isub_glueEl]
    exact el_expandSR hW hX hGGT (HasTy.isubS hW hyE.1 σ) (hησ σ)
      (stable_glueEl hW (hησ σ) (ent_trans (hent σ hh') (ent_subst h12 σ.τ))) hfy
  -- the right `unglue`, related to the image of the fiber where the face holds
  have hatη : ∀ {k'} (τ : ISub k' k), (ival (idEnv k') (φ.subst τ.τ)).holds →
      RE2 S k' (A.isub τ) ((Tm.unglue φ' e' y).isub τ) (.app (.fst (e.isub τ)) (y.isub τ)) := by
    intro k' τ hh
    have hφ'e : I.Entails .one (φ'.subst τ.τ) := ent_trans (hent τ hh) (ent_subst h12 τ.τ)
    have hgτ : HasTy S k' .one [] (y.isub τ) (.glue (A.isub τ) (φ'.subst τ.τ) (T.isub τ) (e'.isub τ)) := by
      have := HasTy.isubS hW hy2 τ; rwa [isub_glue] at this
    have heτ : HasTy S k' .one [] (e'.isub τ) (Tm.equiv (T.isub τ) (A.isub τ)) := by
      have := face_ty hW hφs (HasTy.eqL ee') τ hh; rwa [isub_equiv] at this
    have hs := stable_unglueFace hW hφ'e (HasTy.isubS hW hu' τ) hgτ (HasTy.isubS hW hA0 τ) heτ (TyEq.refl _)
    have happ := RE2.symm hW (hAA k' τ) (RE2_equiv_app hW (hE k' τ hh) (fibY τ hh))
    exact RE2.expandL hW (hAA k' τ) (HasTy.isubS hW hu' τ) (RE2.typed happ).2.1 hs happ
  unfold RE2
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
  refine ⟨⟨hyE.1, hη, hyη⟩, hmem, ⟨hyE.1, hη, hyη⟩, fun k' σ => ?_, hcoh, ?_⟩
  · unfold glueLocE
    split_ifs with hh
    · exact faceη σ hh
    have hh' : ¬ (ival (idEnv k') (φ.subst σ.τ)).holds := fun h => hh (by
      rw [Hom.id_comp]; exact (face_holds_iff hφs σ).2 h)
    have hfy := hmain k' σ
    unfold glueLocE at hfy; rw [if_neg hh] at hfy
    obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', q1, q1', q2, q2', ee0, ee0', ha0, hfibs⟩ :=
      hfy
    have eq1 := RedW.unique r1.1 (by rw [isub_glue]; exact (redT_glue_self (S := S) (k := k') (hne σ hh')).1)
    simp only [Tm.glue.injEq] at eq1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := eq1
    have hne' : ¬ I.Entails .one (φ'.subst σ.τ) := fun h => hne σ hh' (ent_trans h (ent_subst h21 σ.τ))
    rw [isub_glueEl]
    refine ⟨_, _, _, _, ψ, e0, t0, a0, _, _, _, _, r1, rg, redE_glueEl_self hne' (hησ σ), q1, q1',
      ent_subst h21 σ.τ, ent_subst h12 σ.τ, ee0, ee'σ σ, ?_, fun k'' σ' hh2 => ?_⟩
    · rw [Hom.id_comp, Comp2_res_el hW hA0]
      exact hUA.2 k' σ hh' ψ e0 t0 a0 rg.1
    · have hh2' : (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds := by
        rw [Hom.id_comp] at hh2; exact (face_holds_iff hφs _).1 hh2
      refine ⟨?_, hfibs k'' σ' hh2 |>.2.1, ?_⟩
      · have hc := (hcoh k' σ hh _ rg.1 k'' σ').1 hh2 ψ e0 t0 a0 rfl
        have := fib (σ.comp σ') hh2' hc
        rw [Hom.id_comp, dat_glue_fiber (σ.comp σ') ((face_holds_iff hφs _).2 hh2'), Tm.isub_isub, Tm.isub_isub]
        exact this
      · rw [Hom.id_comp, Comp2_res_el hW hA0, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
        exact hatη (σ.comp σ') hh2'
  · -- the coherence of the Glue introduction
    intro k' σ hnσ w hw k'' ρ
    have hh' : ¬ (ival (idEnv k') (φ.subst σ.τ)).holds := fun h => hnσ (by
      rw [Hom.id_comp]; exact (face_holds_iff hφs σ).2 h)
    have hne' : ¬ I.Entails .one (φ'.subst σ.τ) := fun h => hne σ hh' (ent_trans h (ent_subst h21 σ.τ))
    rw [isub_glueEl] at hw
    obtain rfl := RedW.unique hw (redE_glueEl_self hne' (hησ σ)).1
    refine ⟨fun hh ψ0 e00 t00 a00 hwe => ?_, fun hh => ?_⟩
    · simp only [Tm.glueEl.injEq] at hwe
      obtain ⟨-, -, rfl, -⟩ := hwe
      rw [Tm.isub_isub]
      exact faceη (σ.comp ρ) hh
    · have hτ : ¬ (ival (idEnv k'') (φ.subst (σ.comp ρ).τ)).holds := fun h => hh (by
        rw [Hom.id_comp]; exact (face_holds_iff hφs _).2 h)
      have hneτ : ¬ I.Entails .one (φ'.subst (σ.comp ρ).τ) :=
        fun h => hne _ hτ (ent_trans h (ent_subst h21 _))
      rw [show (Tm.glueEl (φ'.subst σ.τ) (e'.isub σ) (y.isub σ) ((Tm.unglue φ' e' y).isub σ)).isub ρ =
        (Tm.glueEl φ' e' y (.unglue φ' e' y)).isub (σ.comp ρ) by
          show Tm.glueEl ((φ'.subst σ.τ).subst ρ.τ) ((e'.isub σ).isub ρ) ((y.isub σ).isub ρ)
            (((Tm.unglue φ' e' y).isub σ).isub ρ) = _
          rw [← I_subst_comp, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; rfl]
      unfold glueLocE
      rw [if_neg hh, isub_glueEl]
      have r1 : RedT S k'' ((Tm.glue A φ T e).isub (σ.comp ρ)) (.glue (A.isub (σ.comp ρ)) (φ.subst (σ.comp ρ).τ)
          (T.isub (σ.comp ρ)) (e.isub (σ.comp ρ))) := by
        rw [isub_glue]; exact redT_glue_self (S := S) (k := k'') (hne _ hτ)
      have rη := redE_glueEl_self hneτ (hησ (σ.comp ρ))
      -- the right `unglue` with itself, from the base of `y`'s normal form at this stage
      have hfy := hmain k'' (σ.comp ρ)
      unfold glueLocE at hfy; rw [if_neg hh] at hfy
      obtain ⟨-, -, -, -, ψ, e0, t0, a0, -, -, -, -, -, rg, -⟩ := hfy
      have hb := hUA.2 k'' (σ.comp ρ) hτ ψ e0 t0 a0 rg.1
      have hbb := (perK hW (hXA k'' (σ.comp ρ))).reflEl' (hAA k'' (σ.comp ρ)) hb
      refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, r1, rη, rη, ent_subst h21 _, ent_subst h12 _,
        ent_subst h21 _, ent_subst h12 _, ee'σ _, ee'σ _, ?_, fun k3 σ3 hh3 => ?_⟩
      · rw [Hom.id_comp, Comp2_res_el hW hA0]; exact hbb
      · have hh3' : (ival (idEnv k3) (φ.subst ((σ.comp ρ).comp σ3).τ)).holds := by
          rw [Hom.id_comp] at hh3; exact (face_holds_iff hφs _).1 hh3
        have hft := fibY ((σ.comp ρ).comp σ3) hh3'
        have hat := hatη ((σ.comp ρ).comp σ3) hh3'
        refine ⟨?_, ?_, ?_⟩
        · rw [Hom.id_comp, dat_glue_fiber _ ((face_holds_iff hφs _).2 hh3'), Tm.isub_isub, Tm.isub_isub]
          exact hft
        · rw [Hom.id_comp, Comp2_res_el hW hA0, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
          exact hat
        · rw [Hom.id_comp, Comp2_res_el hW hA0, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
          exact hat

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem valid_unglueFace {A T e g : Tm} {φ : I} {l : ℕ} (hφ0 : I.Entails Φ φ)
    (h : Valid2 S Ψ Φ Γ (.unglue φ e g) (.unglue φ e g) A) (hty : HasTy0 S Ψ Φ Γ (.unglue φ e g) A)
    (hg : HasTy0 S Ψ Φ Γ g (.glue A φ T e)) (hA : HasTy0 S Ψ Φ Γ A (.univ l))
    (he : HasTy0 S Ψ Φ Γ e (Tm.equiv T A)) (hu : HasTy0 S Ψ Φ Γ (.app (.fst e) g) A) :
    Valid2 S Ψ Φ Γ (.unglue φ e g) (.app (.fst e) g) A := by
  refine valid_redR hW h hu fun k c => ?_
  have hφe : I.Entails .one (φ.subst c.σ'.τ) := ent_trans c.face' (ent_subst hφ0 c.σ'.τ)
  have heR : HasTy S k .one [] (c.R e) (Tm.equiv (c.R T) (c.R A)) := by
    have := c.tyR hW he
    rwa [show c.R (Tm.equiv T A) = Tm.equiv (c.R T) (c.R A) from equiv_subst (σ := c.γ') (τ := c.σ'.τ) T A] at this
  exact stable_unglueFace hW hφe (c.tyR' hW hty) (c.tyR hW hg) (c.tyR hW hA) heR (.inr ⟨l, c.eqLR hW hA⟩)

/-- `glueBeta` at one related substitution: the left redex reduces, at each restriction, to a term related
to the right instance of the base. -/
theorem glueBeta_at {A T e t a : Tm} {φ : I} {l : ℕ}
    (he : Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A))
    (ht : Valid2 S Ψ (cof Φ φ) Γ t t T) (ha : Valid2 S Ψ Φ Γ a a A)
    (hat : Valid2 S Ψ (cof Φ φ) Γ (.app (.fst e) t) a A)
    (hg : HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e)) (he0 : HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (hA0 : HasTy0 S Ψ Φ Γ A (.univ l)) (hty : HasTy0 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) A)
    (hcoh : EqTm0 S Ψ (cof Φ φ) Γ a (.app (.fst e) t) A)
    (c : CSub2 S Ψ Φ Γ k) :
    ∃ u, Red S (c.L (.unglue φ e (.glueEl φ e t a))) u ∧
      EqTm S k .one [] (c.L (.unglue φ e (.glueEl φ e t a))) u (c.L A) ∧ RE2 S k (c.L A) u (c.R a) := by
  have hgL : HasTy S k .one [] (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a))
      (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := c.ty hW hg
  have hu : HasTy S k .one [] (.unglue (φ.subst c.σ.τ) (c.L e) (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a)))
      (c.L A) := c.ty hW hty
  have haa := (ha k c).2
  have hAA : RT2 S k (c.L A) (c.L A) := ha.tyLL hW c
  by_cases hφe : I.Entails .one (φ.subst c.σ.τ)
  · -- the face holds: `unglue` is the application of the equivalence
    have eqv : c.L (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) := equiv_subst (σ := c.γ) (τ := c.σ.τ) T A
    have heL : HasTy S k .one [] (c.L e) (Tm.equiv (c.L T) (c.L A)) := eqv ▸ (c.cof hφe).ty hW he0
    have hred : Red S (.unglue (φ.subst c.σ.τ) (c.L e) (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a)))
        (.app (.fst (c.L e)) (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a))) :=
      .step (by simp [step, show I.entails .one (φ.subst c.σ.τ) = true from hφe]) (.refl _)
    refine ⟨_, hred, EqTm.unglueFace hφe hgL (c.ty hW hA0) heL, ?_⟩
    have hGK : IsTyK S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := isTyK_of_ty hW hgL
    have hface := glue_face_tyEq hW hGK hφe
    have htt := (ht k ((c.cof hφe).diagL hW)).2
    have hTT : RT2 S k (c.L T) (c.L T) := ht.tyLL hW ((c.cof hφe).diagL hW)
    have hgT : RE2 S k (c.L T) (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a)) (c.L t) :=
      RE2.expandL hW hTT (hgL.tyConv hface) (RE2.typed htt).1 (stable_glueEl hW (hgL.tyConv hface) hφe) htt
    have hee := (he k ((c.cof hφe).diagL hW)).2
    have hee' : RE2 S k (Tm.equiv (c.L T) (c.L A)) (c.L e) (c.L e) := eqv ▸ hee
    have happ := RE2_equiv_app hW hee' hgT
    have h2 : RE2 S k (c.L A) (.app (.fst (c.L e)) (c.L t)) (c.L a) := (hat k ((c.cof hφe).diagL hW)).2
    exact RE2.trans hW hAA happ (RE2.trans hW hAA h2 haa)
  · refine ⟨c.L a, red_unglue_base hφe (redE_glueEl_self (S := S) hφe hgL).1,
      EqTm.glueBeta hu (RE2.typed haa).1 (by
        have hφ := scoped_cof_right (scoped_of_eq hcoh)
        exact minimal_to_spec_eq ((sub_eq (sigClosed_of_wfSig hW) hcoh).2
          (c.tySubLCof hW (I.scoped_subst hφ c.σ.sc)))), haa⟩

theorem valid_glueBeta {A T e t a : Tm} {φ : I} {l : ℕ}
    (he : Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A))
    (ht : Valid2 S Ψ (cof Φ φ) Γ t t T) (ha : Valid2 S Ψ Φ Γ a a A)
    (hat : Valid2 S Ψ (cof Φ φ) Γ (.app (.fst e) t) a A)
    (hg : HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e)) (he0 : HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (hA0 : HasTy0 S Ψ Φ Γ A (.univ l)) (hty : HasTy0 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) A)
    (hcoh : EqTm0 S Ψ (cof Φ φ) Γ a (.app (.fst e) t) A) :
    Valid2 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) a A := by
  intro k c
  refine ⟨(ha k c).1, RE2.expandH hW (ha.tyLL hW c) (c.ty hW hty) (RE2.typed (ha k c).2).2.1 fun k' σ => ?_⟩
  have := glueBeta_at hW he ht ha hat hg he0 hA0 hty hcoh (c.restr hW σ)
  rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at this

theorem valid_glueEta {A T e g : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) (.univ l))
    (he0 : HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A)) (he : Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A))
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
    have hinv := RT2_glue_inv hW hGt hGt hn hn hGG
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
    refine RE2.trans hW hGG hgr (RE2_glue_eta hW hGt hh hyy hyη hφR e12 e21 ee'
      (fun k' σ => RT2.isub hW hXA hinv.1 σ) (fun k' σ hh' => (hinv.2 k' σ hh').1) (fun k' σ hh' => ?_))
    have h' := holds_restr hh' hφ
    have := (he k' ((c.restr hW σ).cof h')).2
    have e1 : ((c.restr hW σ).cof h').L (Tm.equiv T A) = Tm.equiv ((c.L T).isub σ) ((c.L A).isub σ) := by
      show (c.restr hW σ).L (Tm.equiv T A) = _
      rw [CSub2.restr_L]
      show ((Tm.equiv T A).subst c.γ c.σ.τ).isub σ = _
      rw [equiv_subst, isub_equiv]
    rw [e1] at this
    exact (CSub2.restr_L hW c σ e ▸ CSub2.restr_R hW c σ e ▸ this)

end

end Model.Whnf
