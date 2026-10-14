import Model.Whnf.Kan2GlueTG

/-!
# Binary Kan lemma: transport along related lines whose normal forms are Glue types

`kanT2_glue`: at every restriction the transports reduce, to the start where the face holds, to a transport
in the fibre where the face of the Glue line holds along the whole line, and otherwise to the contractum
`transpGlueWith` at the Glue normal form. The reducts are related across restrictions by `TGD2.final`,
`TGD2.bdryψ`, `TGD2.bdryδ` and the Kan properties of the fibres.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' : ℕ}

theorem ent_one_forall0 {φ : I} (h : I.Entails .one φ) : I.Entails .one φ.forall0 :=
  entails_iff.2 fun ρ hρ _ => (forall0_sem hρ φ).2 (entails_iff.1 h _ (consAsg_k3 (by decide) hρ) rfl)

theorem tgw_isub (δ : I) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (σ : ISub k' k) :
    (Tm.transpGlueWith δ A φ T e ψ u0).isub σ =
      Tm.transpGlueWith (δ.subst σ.τ) (A.isub σ.up) (φ.subst σ.up.τ) (T.isub σ.up) (e.isub σ.up) (ψ.subst σ.τ)
        (u0.isub σ) := by
  rw [transpGlueWith_eq, transpGlueWith_eq, isub_glueEl, isub_fst, (tg_isub A φ T e ψ u0 δ σ).2.2.2.2.1,
    (tg_isub A φ T e ψ u0 δ σ).2.2.2.2.2, I_phi1_isub, dinst_isub_end _ (.inr rfl)]

theorem step_transp_glue {A T e a : Tm} {φ ψ : I} (hn : ¬ I.Entails .one ψ)
    (hw : step S (.glue A φ T e) = none) :
    step S (.transp (.glue A φ T e) ψ a) = some (Tm.transpGlueWith φ.forall0 A φ T e ψ a) := by
  have hn' : I.entails .one ψ = false := by simpa [I.Entails] using hn
  rw [step]; simp only [hn', Bool.false_eq_true, ↓reduceIte, hw]

variable (hW : WfSig S)
include hW

/-- A transport along a line with a Glue normal form reduces to `transpGlueWith`. -/
theorem red_transp_glue {X A1 T1 e1 a : Tm} {φ1 ψ : I} {l1 : ℕ}
    (hty : HasTy S k .one [] (.transp X ψ a) (X.dinst .one))
    (hR : RedT S (k + 1) X (.glue A1 φ1 T1 e1)) (hG1 : HasTy S (k + 1) .one [] (.glue A1 φ1 T1 e1) (.univ l1))
    (hn : ¬ I.Entails .one ψ) :
    Red S (.transp X ψ a) (Tm.transpGlueWith φ1.forall0 A1 φ1 T1 e1 ψ a) ∧
      EqTm S k .one [] (.transp X ψ a) (Tm.transpGlueWith φ1.forall0 A1 φ1 T1 e1 ψ a) (X.dinst .one) := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG1
  have e1 := eq_transp_ty hW hty hR.2
  have e2 := EqTm.transpGlue (HasTy.eqR e1) hA0 he0 (forall0_scoped hφs) (ent_refl _) (ent_refl _)
  exact ⟨(red_transp_ty hn hR.1.1).trans (.step (step_transp_glue hn hR.1.2) (.refl _)), e1.trans e2⟩


/-- Line robustness along related lines. -/
theorem LineRob.transport {W X W' X' : Tm} {l l' : ℕ} (hWt : HasTy S (k + 1) .one [] W (.univ l))
    (hW't : HasTy S (k + 1) .one [] W' (.univ l')) (hWX : RT2 S (k + 1) W X) (hW'X' : RT2 S (k + 1) W' X')
    (h : LineRob S k X X') : LineRob S k W W' := fun k3 τ r r' hr hr' he => by
  have a := RT2.isub hW (tyCode_of_univ hW hWt) hWX (ISub.cons r hr τ)
  have c := RT2.isub hW (tyCode_of_univ hW hW't) hW'X' (ISub.cons r' hr' τ)
  have b := h k3 τ r r' hr hr' he
  have tW := tyCode_of_univ hW (HasTy.isubS hW hWt (ISub.cons r hr τ))
  have tX := RT2.tyCode_r hW a tW
  have tX' := RT2.tyCode_r hW b tX
  exact RT2.trans hW tW a (RT2.trans hW tX b (RT2.symm hW (RT2.tyCode_l hW c tX') c))

/-- Constancy along related lines. -/
theorem LineConst.transport {W X : Tm} {ψ : I} {l : ℕ} (hWt : HasTy S (k + 1) .one [] W (.univ l))
    (hWX : RT2 S (k + 1) W X) (h : LineConst S k X ψ) : LineConst S k W ψ := fun k3 τ r hr hh => by
  have a := RT2.isub hW (tyCode_of_univ hW hWt) hWX (ISub.cons r hr τ)
  have c := RT2.isub hW (tyCode_of_univ hW hWt) hWX (ISub.cons .zero trivial τ)
  have b := h k3 τ r hr hh
  have tW := tyCode_of_univ hW (HasTy.isubS hW hWt (ISub.cons r hr τ))
  have tX := RT2.tyCode_r hW a tW
  have tX' := RT2.tyCode_r hW b tX
  exact RT2.trans hW tW a (RT2.trans hW tX b (RT2.symm hW (RT2.tyCode_l hW c tX') c))

end

end Model.Whnf
