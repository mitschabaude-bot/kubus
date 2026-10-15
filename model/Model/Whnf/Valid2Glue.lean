import Model.Whnf.Valid2
import Model.Whnf.Glue2Closed
import Model.Whnf.Kan2GlueCode

/-!
# Semantic validity of the Glue rules
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- Kan of the face fibres of a valid Glue component. -/
theorem Valid2.faceKan {T T' : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hT : Valid2 S Ψ (cof Φ φ) Γ T T' (.univ l)) (c : CSub2 S Ψ Φ Γ k)
    (σ : ISub k' k) (hh : (ival (idEnv k') ((φ.subst c.σ.τ).subst σ.τ)).holds) :
    KanP2 S k' (semK S k' ((c.L T).isub σ)) := by
  have h' := holds_restr hh hφ
  have hk := hT.kanV hW k' ((c.restr hW σ).cof h')
  exact CSub2.restr_L hW c σ T ▸ hk

/-- The Glue formation rule carries Kan of its base and face fibres. -/
theorem kanV_glue {A A' T T' e : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hA : Valid2 S Ψ Φ Γ A A' (.univ l)) (hT : Valid2 S Ψ (cof Φ φ) Γ T T' (.univ l))
    (hty : HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l)) : KanV S Ψ Φ Γ (.glue A φ T e) := by
  intro k c
  exact kanP2_glueT hW (c.ty hW hty) (hA.kanV hW k c)
    (fun k' σ hh => hT.faceKan hW hφ c σ hh)

/-- The Glue formation rule, given the self-relation of the right equivalence where the face holds. -/
theorem valid_glue_core {A A' T T' e e' : Tm} {φ φ' : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hA : Valid2 S Ψ Φ Γ A A' (.univ l)) (hT : Valid2 S Ψ (cof Φ φ) Γ T T' (.univ l))
    (he : Valid2 S Ψ (cof Φ φ) Γ e e' (Tm.equiv T A))
    (hER : ∀ k (c : CSub2 S Ψ Φ Γ k), ¬ (ival (idEnv k) (φ.subst c.σ.τ)).holds → ∀ k' (σ : ISub k' k),
      (ival (idEnv k') ((φ.subst c.σ.τ).subst σ.τ)).holds →
      RE2 S k' (Tm.equiv ((c.R T').isub σ) ((c.R A').isub σ)) ((c.R e').isub σ) ((c.R e').isub σ))
    (hty : HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l)) (hty' : HasTy0 S Ψ Φ Γ (.glue A' φ' T' e') (.univ l))
    (heq : EqTm0 S Ψ Φ Γ (.glue A φ T e) (.glue A' φ' T' e') (.univ l)) :
    Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A' φ' T' e') (.univ l) := by
  have hee := valid_trans hW he (valid_symm hW he)
  refine valid_univ_of hW hty hty' heq (fun k c => ?_) (kanV_glue hW hφ hA hT hty)
  have hG : HasTy S k .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.univ l) := c.ty hW hty
  have hG' : HasTy S k .one [] (.glue (c.R A') (φ'.subst c.σ'.τ) (c.R T') (c.R e')) (.univ l) := c.tyR hW hty'
  have heqc : EqTm S k .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e))
      (.glue (c.R A') (φ'.subst c.σ'.τ) (c.R T') (c.R e')) (.univ l) := c.eq hW heq
  have hφL := I.scoped_subst hφ c.σ.sc
  have e12 : I.Entails (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) :=
    ent_trans (ent_subst h12 c.σ.τ) (eq_ent (c.ieq_subst (I_eq_refl φ')))
  have e21 : I.Entails (φ'.subst c.σ'.τ) (φ.subst c.σ.τ) :=
    ent_trans (eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ')))) (ent_subst h21 c.σ.τ)
  by_cases hh : (ival (idEnv k) (φ.subst c.σ.τ)).holds
  · -- the face holds: both sides are their fibers
    have hφe := (holds_iff_entails hφL).1 hh
    have hTT := RE2_univ_ty hW (hT k (c.cof hφe)).2
    have hGK : IsTyK S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := ⟨l, .inl hG⟩
    have hG'K : IsTyK S k (.glue (c.R A') (φ'.subst c.σ'.τ) (c.R T') (c.R e')) := ⟨l, .inl hG'⟩
    exact RT2.expand2 hW (tyCode_of_univ hW hG) hGK hG'K (hGK.of_tyEq (glue_face_tyEq hW hGK hφe))
      (stable_glue hW hGK hφe) (stable_glue hW hG'K (ent_trans hφe e12)) hTT
  · refine RT2_glue_intro hW hG hG' heqc hh e12 e21 (fun k' σ => hA.tyRestr hW c σ)
      (fun k' σ hh' => ?_) (fun k' σ hh' => ?_) (fun k' σ hh' => ?_) (hER k c hh) (hA.kanV hW k c) (fun k' σ hh' => hT.faceKan hW hφ c σ hh')
    · have h' := holds_restr hh' hφ
      have := RE2_univ_ty hW (hT k' ((c.restr hW σ).cof h')).2
      exact (CSub2.restr_L hW c σ T ▸ CSub2.restr_R hW c σ T' ▸ this)
    · have h' := holds_restr hh' hφ
      have := (he k' ((c.restr hW σ).cof h')).2
      have e1 : ((c.restr hW σ).cof h').L (Tm.equiv T A) = Tm.equiv ((c.L T).isub σ) ((c.L A).isub σ) := by
        show (c.restr hW σ).L (Tm.equiv T A) = _
        rw [CSub2.restr_L]
        show ((Tm.equiv T A).subst c.γ c.σ.τ).isub σ = _
        rw [equiv_subst, isub_equiv]
      rw [e1] at this
      exact (CSub2.restr_L hW c σ e ▸ CSub2.restr_R hW c σ e' ▸ this)
    · have h' := holds_restr hh' hφ
      have := (hee k' (((c.restr hW σ).cof h').diagL hW)).2
      have e1 : (((c.restr hW σ).cof h').diagL hW).L (Tm.equiv T A) =
          Tm.equiv ((c.L T).isub σ) ((c.L A).isub σ) := by
        show (c.restr hW σ).L (Tm.equiv T A) = _
        rw [CSub2.restr_L]
        show ((Tm.equiv T A).subst c.γ c.σ.τ).isub σ = _
        rw [equiv_subst, isub_equiv]
      rw [e1] at this
      exact (CSub2.restr_L hW c σ e ▸ this)


theorem valid_glue {A T e : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hA : Valid2 S Ψ Φ Γ A A (.univ l)) (hT : Valid2 S Ψ (cof Φ φ) Γ T T (.univ l))
    (he : Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A)) (hty : HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l)) :
    Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) (.univ l) := by
  refine valid_glue_core hW hφ (ent_refl _) (ent_refl _) hA hT he (fun k c hh k' σ hh' => ?_) hty hty (EqTm0.refl hty)
  have h' := holds_restr hh' hφ
  have := (he k' (((c.restr hW σ).cof h').diagR hW)).2
  have e1 : (((c.restr hW σ).cof h').diagR hW).L (Tm.equiv T A) = Tm.equiv ((c.R T).isub σ) ((c.R A).isub σ) := by
    show (c.restr hW σ).R (Tm.equiv T A) = _
    rw [CSub2.restr_R]
    show ((Tm.equiv T A).subst c.γ' c.σ'.τ).isub σ = _
    rw [equiv_subst, isub_equiv]
  rw [e1] at this
  exact (CSub2.restr_R hW c σ e ▸ this)

theorem valid_glue_eq {A A' T T' e e' : Tm} {φ φ' : I} {l : ℕ} (hφ : φ.Scoped Ψ) (hφ' : φ'.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hA : Valid2 S Ψ Φ Γ A A' (.univ l)) (hT : Valid2 S Ψ (cof Φ φ) Γ T T' (.univ l))
    (he : Valid2 S Ψ (cof Φ φ) Γ e e' (Tm.equiv T A))
    (hGR : Valid2 S Ψ Φ Γ (.glue A' φ' T' e') (.glue A' φ' T' e') (.univ l))
    (hty : HasTy0 S Ψ Φ Γ (.glue A φ T e) (.univ l)) (hty' : HasTy0 S Ψ Φ Γ (.glue A' φ' T' e') (.univ l))
    (heq : EqTm0 S Ψ Φ Γ (.glue A φ T e) (.glue A' φ' T' e') (.univ l)) :
    Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A' φ' T' e') (.univ l) := by
  refine valid_glue_core hW hφ h12 h21 hA hT he (fun k c hh k' σ hh' => ?_) hty hty' heq
  have hG' : HasTy S k .one [] (.glue (c.R A') (φ'.subst c.σ'.τ) (c.R T') (c.R e')) (.univ l) := c.tyR hW hty'
  have hφL := I.scoped_subst hφ c.σ.sc
  have hφR := I.scoped_subst hφ' c.σ'.sc
  have e21 : I.Entails (φ'.subst c.σ'.τ) (φ.subst c.σ.τ) :=
    ent_trans (eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ')))) (ent_subst h21 c.σ.τ)
  have e12 : I.Entails (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) :=
    ent_trans (ent_subst h12 c.σ.τ) (eq_ent (c.ieq_subst (I_eq_refl φ')))
  have hn' : ¬ I.Entails .one (φ'.subst c.σ'.τ) := fun h => hh ((holds_iff_entails hφL).2 (ent_trans h e21))
  have hself : RT2 S k (.glue (c.R A') (φ'.subst c.σ'.τ) (c.R T') (c.R e'))
      (.glue (c.R A') (φ'.subst c.σ'.τ) (c.R T') (c.R e')) := hGR.ty hW (c.diagR hW)
  have hR := (RT2_glue_inv hW hG' hG' hn' hn' hself).2 k' σ
  refine (hR ?_).2
  have h1 := (holds_iff_entails (I.scoped_subst hφL σ.sc)).1 hh'
  exact (holds_iff_entails (I.scoped_subst hφR σ.sc)).2 (ent_trans h1 (ent_subst e12 σ.τ))


theorem valid_glueEl_core {A T e e' t t' a a' : Tm} {φ φ' : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hG : Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) (.univ l))
    (hee : EqTm0 S Ψ (cof Φ φ) Γ e' e (Tm.equiv T A))
    (ht : Valid2 S Ψ (cof Φ φ) Γ t t' T) (ha : Valid2 S Ψ Φ Γ a a' A)
    (hat : ∀ k (c : CSub2 S Ψ Φ Γ k), ¬ (ival (idEnv k) (φ.subst c.σ.τ)).holds → ∀ k' (σ : ISub k' k),
      (ival (idEnv k') ((φ.subst c.σ.τ).subst σ.τ)).holds →
      RE2 S k' ((c.L A).isub σ) ((c.L a).isub σ) (.app (.fst ((c.L e).isub σ)) ((c.L t).isub σ)))
    (hat' : ∀ k (c : CSub2 S Ψ Φ Γ k), ¬ (ival (idEnv k) (φ.subst c.σ.τ)).holds → ∀ k' (σ : ISub k' k),
      (ival (idEnv k') ((φ.subst c.σ.τ).subst σ.τ)).holds →
      RE2 S k' ((c.L A).isub σ) ((c.R a').isub σ) (.app (.fst ((c.L e).isub σ)) ((c.R t').isub σ)))
    (hty : HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e))
    (hty' : HasTy0 S Ψ Φ Γ (.glueEl φ' e' t' a') (.glue A φ T e))
    (heq : EqTm0 S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ' e' t' a') (.glue A φ T e)) :
    Valid2 S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ' e' t' a') (.glue A φ T e) := by
  intro k c
  refine ⟨hG.ty hW c, ?_⟩
  have hGt : HasTy S k .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.univ l) := (RE2.typed (hG k c).2).1
  have hgL : HasTy S k .one [] (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a))
      (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := c.ty hW hty
  have hgR : HasTy S k .one [] (.glueEl (φ'.subst c.σ'.τ) (c.R e') (c.R t') (c.R a'))
      (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := c.tyR' hW hty'
  have hφL := I.scoped_subst hφ c.σ.sc
  have e12 : I.Entails (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) :=
    ent_trans (ent_subst h12 c.σ.τ) (eq_ent (c.ieq_subst (I_eq_refl φ')))
  have e21 : I.Entails (φ'.subst c.σ'.τ) (φ.subst c.σ.τ) :=
    ent_trans (eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ')))) (ent_subst h21 c.σ.τ)
  have hGG : RT2 S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) :=
    hG.ty hW (c.diagL hW)
  by_cases hh : (ival (idEnv k) (φ.subst c.σ.τ)).holds
  · -- the face holds: both sides are their fibers
    have hφe := (holds_iff_entails hφL).1 hh
    have htr := (ht k (c.cof hφe))
    have hTT : RT2 S k (c.L T) (c.L T) := ht.tyLL hW (c.cof hφe)
    have hfib := RE2_glue_of_fiber hW hGt hφe hTT htr.2
    exact RE2.expand2 hW hGG hgL hgR (stable_glueEl hW hgL hφe) (stable_glueEl hW hgR (ent_trans hφe e12)) hfib
  · have hn : ¬ I.Entails .one (φ.subst c.σ.τ) := fun h => hh ((holds_iff_entails hφL).2 h)
    have hinv := RT2_glue_inv hW hGt hGt hn hn hGG
    have hXA : TyCode k (semK S k (c.L A)) := RE2.tyCode hW (ha k c).2
    have hAA : RT2 S k (c.L A) (c.L A) := hinv.1
    refine RE2_glueEl_intro hW hGt hh ⟨hgL, hgR, c.eq hW heq⟩ e12 e21 ?_ hGG
      (fun k' σ => RT2.isub hW hXA hAA σ) (fun k' σ hh' => (hinv.2 k' σ hh').1) (fun k' σ => ?_)
      (fun k' σ hh' => ?_) (fun k' σ hh' => ?_) (fun k' σ hh' => ?_)
    · -- the equivalences agree under the face
      have := c.eqCof hW hφL (EqTm0.symm hee)
      have e1 : c.L (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) := equiv_subst (σ := c.γ) (τ := c.σ.τ) T A
      rw [e1] at this
      exact this.symm
    · have := (ha k' (c.restr hW σ)).2
      rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at this
    · have h' := holds_restr hh' hφ
      have := (ht k' ((c.restr hW σ).cof h')).2
      exact (CSub2.restr_L hW c σ T ▸ CSub2.restr_L hW c σ t ▸ CSub2.restr_R hW c σ t' ▸ this)
    · exact hat k c hh k' σ hh'
    · exact hat' k c hh k' σ hh'

/-- The base and fiber agreement of a Glue introduction, from the validity of that agreement. -/
theorem glue_hat_of_valid {A T e t a : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) (.univ l))
    (hat : Valid2 S Ψ (cof Φ φ) Γ (.app (.fst e) t) a A) :
    ∀ k (c : CSub2 S Ψ Φ Γ k), ¬ (ival (idEnv k) (φ.subst c.σ.τ)).holds → ∀ k' (σ : ISub k' k),
      (ival (idEnv k') ((φ.subst c.σ.τ).subst σ.τ)).holds →
      RE2 S k' ((c.L A).isub σ) ((c.L a).isub σ) (.app (.fst ((c.L e).isub σ)) ((c.L t).isub σ)) := by
  intro k c hh k' σ hh'
  have h' := holds_restr hh' hφ
  have := (hat k' (((c.restr hW σ).cof h').diagL hW)).2
  have hAσ := (hat.tyLL hW (((c.restr hW σ).cof h').diagL hW))
  have := RE2.symm hW hAσ this
  exact (CSub2.restr_L hW c σ A ▸ CSub2.restr_L hW c σ a ▸
    (show (((c.restr hW σ).cof h').diagL hW).L (.app (.fst e) t) = .app (.fst ((c.L e).isub σ)) ((c.L t).isub σ) by
      show (c.restr hW σ).L (.app (.fst e) t) = _
      rw [CSub2.restr_L]; rfl) ▸ this)

theorem valid_glueEl {A T e t a : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hG : Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) (.univ l))
    (he0 : HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (ht : Valid2 S Ψ (cof Φ φ) Γ t t T) (ha : Valid2 S Ψ Φ Γ a a A)
    (hat : Valid2 S Ψ (cof Φ φ) Γ (.app (.fst e) t) a A) (hty : HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e)) :
    Valid2 S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ e t a) (.glue A φ T e) := by
  have hat0 := glue_hat_of_valid hW hφ hG hat
  refine valid_glueEl_core hW hφ (ent_refl _) (ent_refl _) hG (EqTm0.refl he0) ht ha hat0 (fun k c hh k' σ hh' => ?_)
    hty hty (EqTm0.refl hty)
  -- the right instance of `a`, related to the left instance of the fiber image
  have h1 := hat0 k c hh k' σ hh'
  have hφL := I.scoped_subst hφ c.σ.sc
  have hGt : HasTy S k .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.univ l) := (RE2.typed (hG k c).2).1
  have hn : ¬ I.Entails .one (φ.subst c.σ.τ) := fun h => hh ((holds_iff_entails hφL).2 h)
  have hinv := RT2_glue_inv hW hGt hGt hn hn (hG.ty hW (c.diagL hW))
  have hXA : TyCode k (semK S k (c.L A)) := RE2.tyCode hW (ha k c).2
  have hAσ : RT2 S k' ((c.L A).isub σ) ((c.L A).isub σ) := RT2.isub hW hXA hinv.1 σ
  have h' := holds_restr hh' hφ
  have haσ : RE2 S k' ((c.L A).isub σ) ((c.L a).isub σ) ((c.R a).isub σ) := by
    have := (ha k' (c.restr hW σ)).2
    rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at this
  have htσ : RE2 S k' ((c.L T).isub σ) ((c.L t).isub σ) ((c.R t).isub σ) := by
    have := (ht k' ((c.restr hW σ).cof h')).2
    exact (CSub2.restr_L hW c σ T ▸ CSub2.restr_L hW c σ t ▸ CSub2.restr_R hW c σ t ▸ this)
  have h3 := RE2_equiv_app hW (hinv.2 k' σ hh').2 htσ
  exact RE2.trans hW hAσ (RE2.symm hW hAσ haσ) (RE2.trans hW hAσ h1 h3)

theorem valid_glueEl_eq {A T e e' t t' a a' : Tm} {φ φ' : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hG : Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) (.univ l))
    (hee : EqTm0 S Ψ (cof Φ φ) Γ e e' (Tm.equiv T A))
    (ht : Valid2 S Ψ (cof Φ φ) Γ t t' T) (ha : Valid2 S Ψ Φ Γ a a' A)
    (hg : Valid2 S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ e t a) (.glue A φ T e))
    (hg' : Valid2 S Ψ Φ Γ (.glueEl φ' e' t' a') (.glueEl φ' e' t' a') (.glue A φ T e))
    (hty : HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e))
    (hty' : HasTy0 S Ψ Φ Γ (.glueEl φ' e' t' a') (.glue A φ T e))
    (heq : EqTm0 S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ' e' t' a') (.glue A φ T e)) :
    Valid2 S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ' e' t' a') (.glue A φ T e) := by
  refine valid_glueEl_core hW hφ h12 h21 hG (EqTm0.symm hee) ht ha (fun k c hh k' σ hh' => ?_)
    (fun k c hh k' σ hh' => ?_) hty hty' heq
  all_goals
    have hφL := I.scoped_subst hφ c.σ.sc
    have hGt : HasTy S k .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.univ l) :=
      (RE2.typed (hG k c).2).1
    have hn : ¬ I.Entails .one (φ.subst c.σ.τ) := fun h => hh ((holds_iff_entails hφL).2 h)
    have e12 : I.Entails (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) :=
      ent_trans (ent_subst h12 c.σ.τ) (eq_ent (c.ieq_subst (I_eq_refl φ')))
    have e21 : I.Entails (φ'.subst c.σ'.τ) (φ.subst c.σ.τ) :=
      ent_trans (eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ')))) (ent_subst h21 c.σ.τ)
  · have hnR : ¬ I.Entails .one (φ.subst c.σ'.τ) :=
      fun h => hn (ent_trans h (eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ)))))
    exact (RE2_glueEl_base hW hGt hh (hg k c).2 (redE_glueEl_self (S := S) hn (c.ty hW hty)).1
      (redE_glueEl_self (S := S) hnR (c.tyR' hW hty)).1 k' σ hh').1
  · have hnL : ¬ I.Entails .one (φ'.subst c.σ.τ) := fun h => hn (ent_trans h (ent_subst h21 _))
    have hn' : ¬ I.Entails .one (φ'.subst c.σ'.τ) := fun h => hn (ent_trans h e21)
    exact (RE2_glueEl_base hW hGt hh (hg' k c).2 (redE_glueEl_self (S := S) hnL (c.ty hW hty')).1
      (redE_glueEl_self (S := S) hn' (c.tyR' hW hty')).1 k' σ hh').2


theorem valid_unglue_core {A T e e' g g' : Tm} {φ φ' : I} (hφ : φ.Scoped Ψ) (hφ' : φ'.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hAty : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L A) (c.R A))
    (hee : EqTm0 S Ψ (cof Φ φ) Γ e e' (Tm.equiv T A)) (he : Valid2 S Ψ (cof Φ φ) Γ e e' (Tm.equiv T A))
    (hg : Valid2 S Ψ Φ Γ g g' (.glue A φ T e))
    (hty : HasTy0 S Ψ Φ Γ (.unglue φ e g) A) (hty' : HasTy0 S Ψ Φ Γ (.unglue φ' e' g') A)
    (heq : EqTm0 S Ψ Φ Γ (.unglue φ e g) (.unglue φ' e' g') A) :
    Valid2 S Ψ Φ Γ (.unglue φ e g) (.unglue φ' e' g') A := by
  intro k c
  refine ⟨hAty k c, ?_⟩
  have hφL := I.scoped_subst hφ c.σ.sc
  have hgr := (hg k c).2
  have hgE := RE2.typed hgr
  obtain ⟨lG, hGt⟩ := ty_of_tyEq hW (isTyK_of_ty hW hgE.1) (TyEq.refl _) (fun l h => by cases h)
  change HasTy S k .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.univ lG) at hGt
  have e12 : I.Entails (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) :=
    ent_trans (ent_subst h12 c.σ.τ) (eq_ent (c.ieq_subst (I_eq_refl φ')))
  have e21 : I.Entails (φ'.subst c.σ'.τ) (φ.subst c.σ.τ) :=
    ent_trans (eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ')))) (ent_subst h21 c.σ.τ)
  have hu : HasTy S k .one [] (.unglue (φ.subst c.σ.τ) (c.L e) (c.L g)) (c.L A) := c.ty hW hty
  have hu' : HasTy S k .one [] (.unglue (φ'.subst c.σ'.τ) (c.R e') (c.R g')) (c.L A) := c.tyR' hW hty'
  obtain ⟨-, lA, hAL, heT⟩ := glue_data hW hGt
  have hAA : RT2 S k (c.L A) (c.L A) := hAty k (c.diagL hW)
  have hXA : TyCode k (semK S k (c.L A)) := tyCode_of_univ hW hAL
  have hGG : RT2 S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) :=
    RT2.refl hW (RE2.tyCode hW hgr) (hg k c).1
  have hφR := I.scoped_subst hφ' c.σ'.sc
  -- the right equivalence agrees with the left one under the face
  have ee' : EqTm S k (cof .one (φ.subst c.σ.τ)) [] (c.R e') (c.L e) (Tm.equiv (c.L T) (c.L A)) := by
    have := c.eqCof hW hφL hee
    rw [show c.L (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) from equiv_subst (σ := c.γ) (τ := c.σ.τ) T A] at this
    exact this.symm
  by_cases hh : (ival (idEnv k) (φ.subst c.σ.τ)).holds
  · have hφe := (holds_iff_entails hφL).1 hh
    have hφe' := ent_trans hφe e12
    have heR := (he k (c.cof hφe)).2
    have e1 : (c.cof hφe).L (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) := by
      show Tm.subst c.γ c.σ.τ (Tm.equiv T A) = _
      exact equiv_subst _ _ T A
    rw [e1] at heR
    have heL : HasTy S k .one [] (c.L e) (Tm.equiv (c.L T) (c.L A)) :=
      HasTy.restrict (Φ := cof .one (φ.subst c.σ.τ)) trivial (ent_and_intro (ent_refl _) hφe) heT
    have heR' : HasTy S k .one [] (c.R e') (Tm.equiv (c.L T) (c.L A)) :=
      HasTy.restrict (Φ := cof .one (φ.subst c.σ.τ)) trivial (ent_and_intro (ent_refl _) hφe) (HasTy.eqL ee')
    -- the elements, at the fiber
    have hGK : IsTyK S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := ⟨lG, .inl hGt⟩
    have hTK : IsTyK S k (c.L T) := hGK.of_tyEq (glue_face_tyEq hW hGK hφe)
    have hXG := tyCode_of_univ hW hGt
    have hGT : (Comp2 S (semK S k (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e))) k k (Hom.id k)).ty
        (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (c.L T) :=
      ty_reduceSR hW hXG hGG (stable_glue hW hGK hφe) hTK
    have hgT : RE2 S k (c.L T) (c.L g) (c.R g') := by
      have := (per2_tyCode hW hXG k (Hom.id k)).conv hGT hgr
      unfold RE2; rwa [← semK_tyEq hW (glue_face_tyEq hW hGK hφe)]
    have happ := RE2_equiv_app hW heR hgT
    -- the right side's element at the Glue type of its own annotations
    obtain ⟨l2, hG2, eG2⟩ := glue_annot_eq hW hGt hφR e12 e21 ee'
    have hg2 : HasTy S k .one [] (c.R g') (.glue (c.L A) (φ'.subst c.σ'.τ) (c.L T) (c.R e')) := hgE.2.1.conv eG2
    exact RE2.expand2 hW hAA hu hu' (stable_unglueFace hW hφe hu hgE.1 hAL heL (TyEq.refl _))
      (stable_unglueFace hW hφe' hu' hg2 hAL heR' (TyEq.refl _)) happ
  · have hinv := RT2_glue_inv hW hGt hGt (fun h => hh ((holds_iff_entails hφL).2 h))
      (fun h => hh ((holds_iff_entails hφL).2 h)) hGG
    refine RE2_unglue hW hGt hh hgr hu hu' hφR e12 e21 ee' (fun k' σ => RT2.isub hW hXA hAA σ)
      (fun k' σ hh' => (hinv.2 k' σ hh').1) (fun k' σ hh' => ?_)
    have h' := holds_restr hh' hφ
    have := (he k' ((c.restr hW σ).cof h')).2
    have e1 : ((c.restr hW σ).cof h').L (Tm.equiv T A) = Tm.equiv ((c.L T).isub σ) ((c.L A).isub σ) := by
      show (c.restr hW σ).L (Tm.equiv T A) = _
      rw [CSub2.restr_L]
      show ((Tm.equiv T A).subst c.γ c.σ.τ).isub σ = _
      rw [equiv_subst, isub_equiv]
    rw [e1] at this
    exact (CSub2.restr_L hW c σ e ▸ CSub2.restr_R hW c σ e' ▸ this)


theorem valid_unglue {A T e g : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hA : Valid2 S Ψ Φ Γ A A (.univ l)) (he0 : HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (he : Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A)) (hg : Valid2 S Ψ Φ Γ g g (.glue A φ T e))
    (hty : HasTy0 S Ψ Φ Γ (.unglue φ e g) A) :
    Valid2 S Ψ Φ Γ (.unglue φ e g) (.unglue φ e g) A :=
  valid_unglue_core hW hφ hφ (ent_refl _) (ent_refl _) (fun k c => hA.ty hW c) (EqTm0.refl he0) he hg hty hty
    (EqTm0.refl hty)

theorem valid_unglue_eq {A T e e' g g' : Tm} {φ φ' : I} (hφ : φ.Scoped Ψ) (hφ' : φ'.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (hu : Valid2 S Ψ Φ Γ (.unglue φ e g) (.unglue φ e g) A)
    (hee : EqTm0 S Ψ (cof Φ φ) Γ e e' (Tm.equiv T A)) (he : Valid2 S Ψ (cof Φ φ) Γ e e' (Tm.equiv T A))
    (hg : Valid2 S Ψ Φ Γ g g' (.glue A φ T e))
    (hty : HasTy0 S Ψ Φ Γ (.unglue φ e g) A) (hty' : HasTy0 S Ψ Φ Γ (.unglue φ' e' g') A)
    (heq : EqTm0 S Ψ Φ Γ (.unglue φ e g) (.unglue φ' e' g') A) :
    Valid2 S Ψ Φ Γ (.unglue φ e g) (.unglue φ' e' g') A :=
  valid_unglue_core hW hφ hφ' h12 h21 (fun k c => (hu k c).1) hee he hg hty hty' heq

theorem valid_glueFace {A T e G : Tm} {φ : I} (hφ0 : I.Entails Φ φ)
    (h : Valid2 S Ψ Φ Γ (.glue A φ T e) (.glue A φ T e) G) (hty : HasTy0 S Ψ Φ Γ (.glue A φ T e) G)
    (hu : HasTy0 S Ψ Φ Γ T G) : Valid2 S Ψ Φ Γ (.glue A φ T e) T G := by
  refine valid_redR hW h hu fun k c => ?_
  have hφe : I.Entails .one (φ.subst c.σ'.τ) := ent_trans c.face' (ent_subst hφ0 c.σ'.τ)
  intro k' σ
  have hσ : I.Entails .one ((φ.subst c.σ'.τ).subst σ.τ) := by have := ent_subst hφe σ.τ; simpa [I.subst] using this
  have hty' := HasTy.isubS hW (c.tyR' hW hty) σ
  change HasTy S k' .one [] (.glue ((c.R A).isub σ) ((φ.subst c.σ'.τ).subst σ.τ) ((c.R T).isub σ) ((c.R e).isub σ)) _
    at hty'
  show Red S (.glue ((c.R A).isub σ) ((φ.subst c.σ'.τ).subst σ.τ) ((c.R T).isub σ) ((c.R e).isub σ)) _ ∧ _
  exact ⟨.step (by simp [step, show I.entails .one ((φ.subst c.σ'.τ).subst σ.τ) = true from hσ]) (.refl _),
    EqTm.glueFace hσ hty'⟩

theorem valid_glueElFace {e t a G : Tm} {φ : I} (hφ0 : I.Entails Φ φ)
    (h : Valid2 S Ψ Φ Γ (.glueEl φ e t a) (.glueEl φ e t a) G) (hty : HasTy0 S Ψ Φ Γ (.glueEl φ e t a) G)
    (hu : HasTy0 S Ψ Φ Γ t G) : Valid2 S Ψ Φ Γ (.glueEl φ e t a) t G :=
  valid_redR hW h hu fun k c => stable_glueEl hW (c.tyR' hW hty) (ent_trans c.face' (ent_subst hφ0 c.σ'.τ))

end

end Model.Whnf
