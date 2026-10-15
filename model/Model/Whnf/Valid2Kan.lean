import Model.Whnf.Kan2Univ
import Model.Whnf.Valid2

/-!
# Semantic validity of the Kan rules

The validity of `transp` and `hcomp` (formation and congruence), parametrized by the Kan property of
the instances of the line or type (`KanT2`, `KanH2`), so that the lemmas also apply where the Kan
property is only known for some types (lower levels). The face rules hold outright. A computation
rule is valid once its closed instances are: a self-related redex is related to its contractum
(`RedexOK`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-- A closed redex, related to itself, is related to its contractum. -/
def RedexOK (S : Sig) (k : ℕ) (X x y : Tm) : Prop :=
  RE2 S k X x x → HasTy S k .one [] y X → RE2 S k X x y

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- A computation rule whose closed instances are valid. -/
theorem valid_redex {t u T : Tm} (h : Valid2 S Ψ Φ Γ t t T) (hu : HasTy0 S Ψ Φ Γ u T)
    (hr : ∀ k (c : CSub2 S Ψ Φ Γ k), RedexOK S k (c.L T) (c.R t) (c.R u)) : Valid2 S Ψ Φ Γ t u T := by
  intro k c
  refine ⟨(h k c).1, ?_⟩
  exact RE2.trans hW (h.tyLL hW c) (h k c).2 (hr k c (h.right hW c) (c.tyR' hW hu))

theorem valid_transpFace {A a T : Tm} {φ : I} (hφ0 : I.Entails Φ φ)
    (h : Valid2 S Ψ Φ Γ (.transp A φ a) (.transp A φ a) T) (hty : HasTy0 S Ψ Φ Γ (.transp A φ a) T)
    (hu : HasTy0 S Ψ Φ Γ a T) : Valid2 S Ψ Φ Γ (.transp A φ a) a T :=
  valid_redR hW h hu fun k c => stable_transpFace hW (ent_trans c.face' (ent_subst hφ0 c.σ'.τ)) (c.tyR' hW hty)

theorem valid_hcompFace {A u a T : Tm} {φ : I} (hφ0 : I.Entails Φ φ)
    (h : Valid2 S Ψ Φ Γ (.hcomp A φ u a) (.hcomp A φ u a) T) (hty : HasTy0 S Ψ Φ Γ (.hcomp A φ u a) T)
    (hu : HasTy0 S Ψ Φ Γ (u.dinst .one) T) : Valid2 S Ψ Φ Γ (.hcomp A φ u a) (u.dinst .one) T := by
  refine valid_redR hW h hu fun k c => ?_
  have := stable_hcompFace hW (ent_trans c.face' (ent_subst hφ0 c.σ'.τ)) (c.tyR' hW hty)
  simp only [CSub2.R, dinst_subst] at this ⊢
  exact this

theorem CSub2.L_dinst (c : CSub2 S Ψ Φ Γ k) (A : Tm) (r : I) :
    c.L (A.dinst r) = ((c.up hW).L A).dinst (r.subst c.σ.τ) := by
  simp only [CSub2.L]; rw [dinst_subst]; rfl

theorem CSub2.R_dinst (c : CSub2 S Ψ Φ Γ k) (A : Tm) (r : I) :
    c.R (A.dinst r) = ((c.up hW).R A).dinst (r.subst c.σ'.τ) := by
  simp only [CSub2.R]; rw [dinst_subst]; rfl

/-- A valid line gives robustly related lines at every related substitution. -/
theorem lineRob_of_valid {A A' : Tm} {l : ℕ} (hA : Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A' (.univ l))
    (c : CSub2 S Ψ Φ Γ k) : LineRob S k ((c.up hW).L A) ((c.up hW).R A') := by
  intro k' τ r r' hr hr' hE
  have := hA.ty hW ((c.restr hW τ).cons r r' hr hr' hE)
  rwa [CSub2.cons_restr_L, CSub2.cons_restr_R, isub_up_dinst, isub_up_dinst] at this

/-- Judgmentally equal terms under an interval binder and an extended face, at the two instances. -/
theorem CSub2.eqCofUp (c : CSub2 S Ψ Φ Γ k) {φ : I} (hφ : (φ.subst c.σ.τ).Scoped k) {t u A : Tm}
    (h : EqTm0 S (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift t u A) :
    EqTm S (k + 1) (KubusCore.cof .one (φ.subst c.σ.τ)).shift [] ((c.up hW).L t) ((c.up hW).R u)
      ((c.up hW).L A) := by
  have hS := sigClosed_of_wfSig hW
  have e1 := minimal_to_spec_eq ((sub_eq hS h).2 ((c.tySubLCof hW hφ).dup hS))
  have hes : EqSub S Ψ Γ k (KubusCore.cof .one (φ.subst c.σ.τ)) [] c.γ c.σ.τ c.γ' c.σ'.τ :=
    ⟨fun x A hx => EqTm0.restrict ⟨trivial, hφ⟩ (ent_and_left _ _) ((c.eqSub hW).1 x A hx), (c.eqSub hW).2⟩
  exact e1.trans (minimal_to_spec_eq ((sub_ty hS (presup hW h).2).2.2 ((c.tySubLCof hW hφ).dup hS)
    ((c.tySubRCof hW hφ).dup hS) (hes.dup hS)))

theorem CSub2.up_L_const (c : CSub2 S Ψ Φ Γ k) (A : Tm) (σ : ISub k' k) (r : I) :
    ((((c.up hW).L (A.dinst .zero).dshift)).isub σ.up).dinst r = ((c.up hW).L A).isub (ISub.cons .zero trivial σ) := by
  show (((A.dinst .zero).dshift.subst (dupS c.γ) (I.up c.σ.τ)).isub σ.up).dinst r = _
  rw [dshift_dup_subst, isub_dshift, dshift_dinst, ← isub_up_dinst _ σ .zero trivial]
  show (c.L (A.dinst .zero)).isub σ = _
  rw [CSub2.L_dinst hW, isub_dinst]; rfl

/-- The constancy of a line where a face holds, from the validity of its constancy equation. -/
theorem lineConst_of_valid {A : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hC : Valid2 S (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (c : CSub2 S Ψ Φ Γ k) : LineConst S k ((c.up hW).L A) (φ.subst c.σ.τ) := by
  intro k' σ r hr hh
  have h' := holds_restr hh hφ
  have := hC.ty hW ((((c.restr hW σ).cof h').diagL hW).cons r r hr hr (I_eq_refl _))
  change RT2 S k' (((c.restr hW σ).cons r r hr hr (I_eq_refl _)).L A)
    (((c.restr hW σ).cons r r hr hr (I_eq_refl _)).L (A.dinst .zero).dshift) at this
  rwa [CSub2.cons_restr_L, CSub2.cons_restr_L, isub_up_dinst, CSub2.up_L_const] at this

theorem CSub2.L_cons (c : CSub2 S Ψ Φ Γ k) (A : Tm) (r r' : I) (hr : r.Scoped k) (hr' : r'.Scoped k)
    (he : I.Eq r r') : (c.cons r r' hr hr' he).L A = ((c.up hW).L A).dinst r := by
  simp only [CSub2.L, CSub2.cons, CSub2.up]
  exact (dup_dinst A c.γ c.σ.τ r).symm

theorem CSub2.R_cons (c : CSub2 S Ψ Φ Γ k) (A : Tm) (r r' : I) (hr : r.Scoped k) (hr' : r'.Scoped k)
    (he : I.Eq r r') : (c.cons r r' hr hr' he).R A = ((c.up hW).R A).dinst r' := by
  simp only [CSub2.R, CSub2.cons, CSub2.up]
  exact (dup_dinst A c.γ' c.σ'.τ r').symm

omit hW in
theorem CSub2.ent_LR (c : CSub2 S Ψ Φ Γ k) {φ φ' : I} (h12 : I.Entails φ φ') :
    I.Entails (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) :=
  ent_trans (ent_subst h12 c.σ.τ) (eq_ent (c.ieq_subst (I_eq_refl φ')))

omit hW in
theorem CSub2.ent_RL (c : CSub2 S Ψ Φ Γ k) {φ φ' : I} (h21 : I.Entails φ' φ) :
    I.Entails (φ'.subst c.σ'.τ) (φ.subst c.σ.τ) :=
  ent_trans (eq_ent (I_eq_symm (c.ieq_subst (I_eq_refl φ')))) (ent_subst h21 c.σ.τ)

/-- The type premise supplies its own composition operations. -/
theorem Valid2.kanH {A A' : Tm} {l : ℕ} (hA : Valid2 S Ψ Φ Γ A A' (.univ l))
    (c : CSub2 S Ψ Φ Γ k) : KanH2 S k (c.L A) (c.R A') :=
  (hA.kanV hW k c).1 k (Hom.id k) _ _ (hA.ty hW c)

/-- The line premise supplies its own transport operations. -/
theorem Valid2.kanT {A A' : Tm} {l : ℕ} (hA : Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A' (.univ l))
    (c : CSub2 S Ψ Φ Γ k) : KanT2 S k ((c.up hW).L A) ((c.up hW).R A') :=
  (hA.kanV hW (k + 1) (c.up hW)).2 k (Hom.id (k + 1)) _ _ (hA.ty hW (c.up hW))

/-- Transport (formation and congruence), given the Kan property of the instances of the lines. -/
theorem valid_transp {A A' a a' : Tm} {φ φ' : I} {l l' : ℕ} (hφ : φ.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hA : Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A' (.univ l))
    (hC : Valid2 S (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l'))
    (ha : Valid2 S Ψ Φ Γ a a' (A.dinst .zero))
    (hty : HasTy0 S Ψ Φ Γ (.transp A φ a) (A.dinst .one)) (hty' : HasTy0 S Ψ Φ Γ (.transp A' φ' a') (A.dinst .one))
    (heq : EqTm0 S Ψ Φ Γ (.transp A φ a) (.transp A' φ' a') (A.dinst .one)) :
    Valid2 S Ψ Φ Γ (.transp A φ a) (.transp A' φ' a') (A.dinst .one) := by
  intro k c
  have hT := hA.tySelf hW (c.cons .one .one trivial trivial (I_eq_refl _))
  rw [CSub2.L_cons hW, CSub2.R_cons hW] at hT
  refine ⟨by rw [CSub2.L_dinst hW, CSub2.R_dinst hW]; exact hT, ?_⟩
  have h := hA.kanT hW c (lineRob_of_valid hW hA c) (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) (c.L a) (c.R a')
    (lineConst_of_valid hW hφ hC c) (by have := c.ty hW hty; rwa [CSub2.L_dinst hW] at this)
    (by have := c.tyR' hW hty'; rwa [CSub2.L_dinst hW] at this)
    (by have := c.eq hW heq; rwa [CSub2.L_dinst hW] at this) (c.ent_LR h12) (c.ent_RL h21)
    (by have := (ha k c).2; rwa [CSub2.L_dinst hW] at this)
  rw [CSub2.L_dinst hW]; exact h

theorem CSub2.L_dshift_dinst (c : CSub2 S Ψ Φ Γ k) (A : Tm) (r : I) :
    ((c.up hW).L A.dshift).dinst r = (c.L A).dshift.dinst r := by
  show (A.dshift.subst (dupS c.γ) (I.up c.σ.τ)).dinst r = _
  rw [dshift_dup_subst]

/-- Composition (formation and congruence), given the Kan property of the instances of the types. -/
theorem valid_hcomp {A A' u u' a a' : Tm} {φ φ' : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hA : Valid2 S Ψ Φ Γ A A' (.univ l))
    (hu : Valid2 S (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift u u' A.dshift)
    (ha : Valid2 S Ψ Φ Γ a a' A)
    (hu0 : Valid2 S Ψ (KubusCore.cof Φ φ) Γ (u.dinst .zero) a A)
    (hu0' : Valid2 S Ψ (KubusCore.cof Φ φ) Γ (u'.dinst .zero) a' A)
    (hty : HasTy0 S Ψ Φ Γ (.hcomp A φ u a) A) (hty' : HasTy0 S Ψ Φ Γ (.hcomp A' φ' u' a') A)
    (heq : EqTm0 S Ψ Φ Γ (.hcomp A φ u a) (.hcomp A' φ' u' a') A)
    (huu : EqTm0 S (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift u u' A.dshift) :
    Valid2 S Ψ Φ Γ (.hcomp A φ u a) (.hcomp A' φ' u' a') A := by
  intro k c
  refine ⟨hA.tySelf hW c, ?_⟩
  have hφL := I.scoped_subst hφ c.σ.sc
  have hu0R := valid_symm hW hu0'
  have hXA : TyCode k (semK S k (c.L A)) := tyCode_of_univ hW (RE2.typed (hA k c).2).1
  have hAA : RT2 S k (c.L A) (c.L A) := RT2.refl hW hXA (hA.tySelf hW c)
  refine hA.kanH hW c (φ.subst c.σ.τ) (φ'.subst c.σ'.τ) ((c.up hW).L u) ((c.up hW).R u') (c.L a) (c.R a')
    (c.ty hW hty) (c.tyR' hW hty') (c.eq hW heq) ?_ (c.ent_LR h12) (c.ent_RL h21) ?_ (ha k c).2 ?_ ?_
  · have := c.eqCofUp hW hφL huu
    have e : (c.up hW).L A.dshift = (c.L A).dshift := dshift_dup_subst A c.γ c.σ.τ
    rwa [e] at this
  · intro k' σ r r' hr hr' hE hh
    have h' := holds_restr hh hφ
    have := (hu k' (((c.restr hW σ).cof h').cons r r' hr hr' hE)).2
    change RE2 S k' (((c.restr hW σ).cons r r hr hr (I_eq_refl _)).L A.dshift)
      (((c.restr hW σ).cons r r' hr hr' hE).L u) (((c.restr hW σ).cons r r' hr hr' hE).R u') at this
    rwa [CSub2.cons_restr_L, CSub2.cons_restr_L, CSub2.cons_restr_R, ← CSub2.up_restr_L,
      CSub2.L_dshift_dinst, CSub2.restr_L, dshift_dinst] at this
  · intro k' σ hh
    have h' := holds_restr hh hφ
    have e1 := (hu0 k' ((c.restr hW σ).cof h')).2
    have e2 := (ha.right hW (c.restr hW σ))
    change RE2 S k' ((c.restr hW σ).L A) ((c.restr hW σ).L (u.dinst .zero)) ((c.restr hW σ).R a) at e1
    rw [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at e1
    rw [CSub2.restr_L, CSub2.restr_R, CSub2.restr_R] at e2
    have hAσ := RT2.isub hW hXA hAA σ
    rw [CSub2.L_dinst hW, isub_dinst] at e1
    exact RE2.trans hW hAσ e1 e2
  · intro k' σ hh
    have h' := holds_restr hh hφ
    have e1 := (ha k' (c.restr hW σ)).2
    have e2 := hu0R.right hW ((c.restr hW σ).cof h')
    change RE2 S k' ((c.restr hW σ).L A) ((c.restr hW σ).R a') ((c.restr hW σ).R (u'.dinst .zero)) at e2
    rw [CSub2.restr_L, CSub2.restr_R, CSub2.restr_R] at e2
    rw [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at e1
    have hAσ := RT2.isub hW hXA hAA σ
    rw [CSub2.R_dinst hW, isub_dinst] at e2
    exact RE2.trans hW hAσ e1 e2

end

end Model.Whnf
