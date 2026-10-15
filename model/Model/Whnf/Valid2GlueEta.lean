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
