import Model.Whnf.Kan2ElimT

/-!
# The binary transport at Π-types
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
theorem step_transp_pi {A B a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.transp (.pi A B) φ a) = some (Tm.transpPi A B φ a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

/-- An application of a transport along a line of Π-types whose face does not hold. -/
theorem app_transp_pi {T A2 B2 a0 v : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hR : RedT S (k + 1) T (.pi A2 B2))
    (hv : HasTy S k .one [] v (A2.dinst .one)) :
    Red S (.app (.transp T φ a0) v)
      (.transp (B2.inst (.transp (A2.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
        v.dshift)) φ (.app a0 (.transp (A2.dsubst negI) φ v))) ∧
    EqTm S k .one [] (.app (.transp T φ a0) v)
      (.transp (B2.inst (.transp (A2.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
        v.dshift)) φ (.app a0 (.transp (A2.dsubst negI) φ v))) ((B2.dinst .one).inst v) := by
  have e1 := eq_transp_ty hW hty hR.2
  have e2 := EqTm.transpPi (HasTy.eqR e1)
  have hT1 : TyEq S k (T.dinst .one) (.pi (A2.dinst .one) (B2.dinst .one)) := by
    have := tyEq_dinst hW hR.2 (r := .one) trivial; rwa [pi_dinst] at this
  have e3 := (e1.trans e2).tyConv hT1
  have e4 : EqTm S k .one [] (.app (.transp T φ a0) v) (.app (Tm.transpPi A2 B2 φ a0) v) ((B2.dinst .one).inst v) :=
    EqTm.app e3 (EqTm.refl hv)
  have hbody : (Tm.transp (B2.subst (consT (wT A2 φ) wkS) I.var) φ (.app a0.shift (w0T A2 φ))).inst v =
      .transp (B2.inst (.transp (A2.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
        v.dshift)) φ (.app a0 (.transp (A2.dsubst negI) φ v)) := by
    rw [transpPi_body_inst, wT_inst, w0T_inst]
  have e5 : EqTm S k .one [] (.app (Tm.transpPi A2 B2 φ a0) v)
      ((Tm.transp (B2.subst (consT (wT A2 φ) wkS) I.var) φ (.app a0.shift (w0T A2 φ))).inst v)
      ((B2.dinst .one).inst v) := EqTm.piBeta (HasTy.eqR e4)
  rw [hbody] at e5
  refine ⟨(red_app v ((red_transp_ty hn hR.1.1).trans (.step (step_transp_pi hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rw [← hbody]
  rfl

/-- An application of a transport whose face holds. -/
theorem app_transp_face {T A2 B2 a0 v : Tm} {φ : I} (h : I.Entails .one φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hT1 : TyEq S k (T.dinst .one) (.pi A2 B2))
    (hv : HasTy S k .one [] v A2) :
    Red S (.app (.transp T φ a0) v) (.app a0 v) ∧ EqTm S k .one [] (.app (.transp T φ a0) v) (.app a0 v) (B2.inst v) :=
  ⟨red_app v (.step (step_transp_face h) (.refl _)), EqTm.app ((EqTm.transpFace h hty).tyConv hT1) (EqTm.refl hv)⟩


/-- The Π-type a type reduces to is typed. -/
theorem piW_typed {X A B : Tm} (hX : IsTyK S k X) (hR : RedT S k X (.pi A B)) :
    ∃ l, HasTy S k .one [] (.pi A B) (.univ l) :=
  ty_of_tyEq hW hX hR.2 (fun l h => by cases h)

/-- The normal forms of related types whose normal forms are Π-types are related componentwise. -/
theorem piW_rel {X Y A B A' B' : Tm} (h : RT2 S k X Y) (hX : RedT S k X (.pi A B)) (hY : RedT S k Y (.pi A' B')) :
    RT2 S k A A' ∧ ∀ a a', RE2 S k A a a' → RT2 S k (B.inst a) (B'.inst a') := by
  obtain ⟨l, hpi⟩ := piW_typed hW (Comp2_ty_base h).2.1 hX
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := (PiStr_of hW h hX hpi).whnf k (ISub.id k)
  have hXc := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base h).2.1)
  have hYc := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base h).2.2.1)
  rw [hXc] at h1; rw [hYc] at h2
  obtain ⟨rfl, rfl⟩ : A1 = A ∧ B1 = B := by
    have := RedW.unique h1.1 hX.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1' = A' ∧ B1' = B' := by
    have := RedW.unique h2.1 hY.1; injection this; constructor <;> assumption
  exact ⟨h3, h4⟩

/-- The normal form of a type whose normal form is a Π-type, restricted, is related to the normal form
of the restriction. -/
theorem piW_coh {X X' A B A2 B2 : Tm} (h : RT2 S k X X') (hX : RedT S k X (.pi A B)) (ρ : ISub k' k)
    (hXρ : RedT S k' (X.isub ρ) (.pi A2 B2)) :
    RT2 S k' (A.isub ρ) A2 ∧ ∀ a a', RE2 S k' (A.isub ρ) a a' → RT2 S k' ((B.isub ρ).inst a) (B2.inst a') := by
  obtain ⟨l, hpi⟩ := piW_typed hW (Comp2_ty_base h).2.1 hX
  have hXc := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base h).2.1)
  exact (PiStr_of hW h hX hpi).coh k (ISub.id k) k' ρ A B A2 B2 (by rw [hXc]; exact hX)
    (by rw [ISub.id_comp]; exact hXρ)

/-- Transport along related lines of Π-types, applied to related arguments. -/
theorem kanT2_pi_core {T T' : Tm} (hTT' : RT2 S (k + 1) T T') (hP : PiStr S (k + 1) T T')
    (hLR : LineRob S k T T')
    (hIHA : ∀ k1 (ρ : ISub k1 (k + 1)) A1 B1, RedT S k1 (T.isub ρ) (.pi A1 B1) →
      ∀ k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) (A1.isub ρ') X' → KanT2 S k2 (A1.isub ρ') X')
    (hIHB : ∀ k1 (ρ : ISub k1 (k + 1)) A1 B1, RedT S k1 (T.isub ρ) (.pi A1 B1) → ∀ b, RE2 S k1 A1 b b →
      ∀ k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) ((B1.inst b).isub ρ') X' → KanT2 S k2 ((B1.inst b).isub ρ') X')
    {φ φ' : I} {a0 a0' : Tm} (hC : LineConst S k T φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one))
    (hty' : HasTy S k .one [] (.transp T' φ' a0') (T.dinst .one))
    (heq : EqTm S k .one [] (.transp T φ a0) (.transp T' φ' a0') (T.dinst .one))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (ha0 : RE2 S k (T.dinst .zero) a0 a0')
    {A1 B1 : Tm} (hR1 : RedT S k (T.dinst .one) (.pi A1 B1)) {v v' : Tm} (hv : RE2 S k A1 v v') :
    RE2 S k (B1.inst v) (.app (.transp T φ a0) v) (.app (.transp T' φ' a0') v') := by
  sorry

end

end Model.Whnf
