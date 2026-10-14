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

attribute [local instance] Classical.propDecidable

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


/-- Related lines are related at their points. -/
theorem RT2.dinstE {X Y : Tm} (hX : TyCode (k + 1) (semK S (k + 1) X)) (h : RT2 S (k + 1) X Y) {d : I}
    (hd : d.Scoped k) : RT2 S k (X.dinst d) (Y.dinst d) := by
  have hb := Comp2_ty_base h
  have := RT2.isub hW hX h (ISub.cons d hd (ISub.id k))
  rwa [isub_cons_id_of_closed (closed_of_isTyK hW hb.2.1), isub_cons_id_of_closed (closed_of_isTyK hW hb.2.2.1)]
    at this

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


/-- Transport along related lines whose normal forms are Glue types. -/
theorem kanT2_glue {T T' A Tf e : Tm} {φ : I} {l : ℕ} (hTT : RT2 S (k + 1) T T')
    (hR : RedT S (k + 1) T (.glue A φ Tf e)) (hG : HasTy S (k + 1) .one [] (.glue A φ Tf e) (.univ l))
    (hIHA : ∀ k1 (ρ1 : ISub k1 (k + 1)) A1 φ1 T1 e1, RedT S k1 (T.isub ρ1) (.glue A1 φ1 T1 e1) →
      KHRel S k1 A1 ∧ KTRel S k1 A1)
    (hIHT : ∀ k1 (ρ1 : ISub k1 (k + 1)) A1 φ1 T1 e1, RedT S k1 (T.isub ρ1) (.glue A1 φ1 T1 e1) →
      (∀ k2 (σ : ISub k2 k1), (ival (idEnv k2) (φ1.subst σ.τ)).holds → ∀ X X', RT2 S k2 (T1.isub σ) X →
        RT2 S k2 X X' → KanH2 S k2 X X') ∧
      (∀ k2 (Θ : ISub (k2 + 1) k1), (ival (idEnv (k2 + 1)) (φ1.subst Θ.τ)).holds → ∀ X X',
        RT2 S (k2 + 1) (T1.isub Θ) X → RT2 S (k2 + 1) X X' → KanT2 S k2 X X')) :
    KanT2 S k T T' := by
  intro hLR ψ ψ' a0 a0' hC hty hty' heq h12 h21 ha0
  obtain ⟨l0, ⟨hTl, hψs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hXT0 : TyCode (k + 1) (semK S (k + 1) T) := tyCode_of_univ hW hTl'
  have hTTd : RT2 S (k + 1) T T := RT2.refl hW hXT0 hTT
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hT0 : ∀ k3 (τ : ISub k3 k), (T.dinst .zero).isub τ = T.isub (ISub.cons .zero trivial τ) := fun k3 τ => by
    rw [isub_dinst]; exact isub_up_dinst T τ .zero trivial
  have hT1 : ∀ k3 (τ : ISub k3 k), (T.dinst .one).isub τ = T.isub (ISub.cons .one trivial τ) := fun k3 τ => by
    rw [isub_dinst]; exact isub_up_dinst T τ .one trivial
  have hXT : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (T.isub σ)) := fun k3 σ =>
    tyCode_of_univ hW (HasTy.isubS hW hTl' σ)
  have hTτ : ∀ {k3 : ℕ} (σ : ISub k3 (k + 1)), RT2 S k3 (T.isub σ) (T.isub σ) := fun σ => RT2.isub hW hXT0 hTTd σ
  have hTτ' : ∀ {k3 : ℕ} (σ : ISub k3 (k + 1)), RT2 S k3 (T.isub σ) (T'.isub σ) := fun σ => RT2.isub hW hXT0 hTT σ
  have hT'τ : ∀ {k3 : ℕ} (σ : ISub k3 (k + 1)), RT2 S k3 (T'.isub σ) (T'.isub σ) := fun σ =>
    RT2.refl' hW (hXT _ σ) (hTτ' σ)
  have hn : ¬ I.Entails .one φ := fun h => by
    have := hR.1.2; simp [IsWhnf, step, show I.entails .one φ = true from h] at this
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hw := fun k3 (σ : ISub k3 (k + 1)) (hh : ¬ (ival (idEnv k3) (φ.subst σ.τ)).holds) =>
    glue_whnf_pair hW hTT hR hG hn σ hh
  choose A1 φ1 T1 e1 A1' φ1' T1' e1' l1 l1' hw using hw
  have hX : TyCode k (semK S k (T.dinst .one)) := by
    have := hXT k (ISub.cons .one trivial (ISub.id k)); rwa [isub_cons_id_of_closed hTc] at this
  have hYY : RT2 S k (T.dinst .one) (T.dinst .one) := by
    have := hTτ (ISub.cons .one trivial (ISub.id k)); rwa [isub_cons_id_of_closed hTc] at this
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T.isub ρ.up) (ψ.subst ρ.τ) (a0.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty ρ; rwa [isub_dinst] at this
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T'.isub ρ.up) (ψ'.subst ρ.τ) (a0'.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty' ρ; rwa [isub_dinst] at this
  have eT1 : ∀ k' (ρ : ISub k' k), TyEq S k' ((T.isub ρ.up).dinst .one) ((T'.isub ρ.up).dinst .one) := fun k' ρ => by
    have := (tyEq_dinst hW (Comp2_ty_base hTT).2.2.2.2.2 (r := .one) trivial).isub hW ρ
    rwa [isub_dinst, isub_dinst] at this
  -- the reducts at the restrictions
  have hu : ∀ k4 (κ : ISub k4 k), Red S ((Tm.transp T ψ a0).isub κ)
      (if I.Entails .one (ψ.subst κ.τ) then a0.isub κ
        else if hf : (ival (idEnv (k4 + 1)) (φ.subst κ.up.τ)).holds then .transp (T.isub κ.up) (ψ.subst κ.τ) (a0.isub κ)
        else Tm.transpGlueWith (φ1 (k4 + 1) κ.up hf).forall0 (A1 (k4 + 1) κ.up hf) (φ1 (k4 + 1) κ.up hf)
          (T1 (k4 + 1) κ.up hf) (e1 (k4 + 1) κ.up hf) (ψ.subst κ.τ) (a0.isub κ)) ∧
      EqTm S k4 .one [] ((Tm.transp T ψ a0).isub κ)
      (if I.Entails .one (ψ.subst κ.τ) then a0.isub κ
        else if hf : (ival (idEnv (k4 + 1)) (φ.subst κ.up.τ)).holds then .transp (T.isub κ.up) (ψ.subst κ.τ) (a0.isub κ)
        else Tm.transpGlueWith (φ1 (k4 + 1) κ.up hf).forall0 (A1 (k4 + 1) κ.up hf) (φ1 (k4 + 1) κ.up hf)
          (T1 (k4 + 1) κ.up hf) (e1 (k4 + 1) κ.up hf) (ψ.subst κ.τ) (a0.isub κ))
      ((T.dinst .one).isub κ) := by
    intro k4 κ
    show Red S (.transp (T.isub κ.up) (ψ.subst κ.τ) (a0.isub κ)) _ ∧ EqTm S k4 .one [] _ _ _
    rw [isub_dinst]
    split_ifs with hψ hf
    · exact ⟨.step (step_transp_face hψ) (.refl _), EqTm.transpFace hψ (hρT k4 κ)⟩
    · exact ⟨.refl _, EqTm.refl (hρT k4 κ)⟩
    · exact red_transp_glue hW (hρT k4 κ) (hw (k4 + 1) κ.up hf).1 (hw (k4 + 1) κ.up hf).2.2.1 hψ
  have hu' : ∀ k4 (κ : ISub k4 k), Red S ((Tm.transp T' ψ' a0').isub κ)
      (if I.Entails .one (ψ'.subst κ.τ) then a0'.isub κ
        else if hf : (ival (idEnv (k4 + 1)) (φ.subst κ.up.τ)).holds then .transp (T'.isub κ.up) (ψ'.subst κ.τ) (a0'.isub κ)
        else Tm.transpGlueWith (φ1' (k4 + 1) κ.up hf).forall0 (A1' (k4 + 1) κ.up hf) (φ1' (k4 + 1) κ.up hf)
          (T1' (k4 + 1) κ.up hf) (e1' (k4 + 1) κ.up hf) (ψ'.subst κ.τ) (a0'.isub κ)) ∧
      EqTm S k4 .one [] ((Tm.transp T' ψ' a0').isub κ)
      (if I.Entails .one (ψ'.subst κ.τ) then a0'.isub κ
        else if hf : (ival (idEnv (k4 + 1)) (φ.subst κ.up.τ)).holds then .transp (T'.isub κ.up) (ψ'.subst κ.τ) (a0'.isub κ)
        else Tm.transpGlueWith (φ1' (k4 + 1) κ.up hf).forall0 (A1' (k4 + 1) κ.up hf) (φ1' (k4 + 1) κ.up hf)
          (T1' (k4 + 1) κ.up hf) (e1' (k4 + 1) κ.up hf) (ψ'.subst κ.τ) (a0'.isub κ))
      ((T.dinst .one).isub κ) := by
    intro k4 κ
    show Red S (.transp (T'.isub κ.up) (ψ'.subst κ.τ) (a0'.isub κ)) _ ∧ EqTm S k4 .one [] _ _ _
    rw [isub_dinst]
    split_ifs with hψ hf
    · exact ⟨.step (step_transp_face hψ) (.refl _), EqTm.transpFace hψ (hρT' k4 κ)⟩
    · exact ⟨.refl _, EqTm.refl (hρT' k4 κ)⟩
    · have r := red_transp_glue hW ((hρT' k4 κ).tyConv (eT1 k4 κ)) (hw (k4 + 1) κ.up hf).2.1
        (hw (k4 + 1) κ.up hf).2.2.2.1 hψ
      exact ⟨r.1, r.2.tyConv (TyEq.symm (eT1 k4 κ))⟩
  refine RE2.expandBoth hW hX hYY hty hty' _ _ hu hu' (fun k4 κ k5 κ' => ?_)
  dsimp only
  rw [hT1]
  have hτ0 : ∀ {x : I}, x.subst (κ.comp κ').τ = (x.subst κ.τ).subst κ'.τ := fun {x} => I_subst_comp x κ κ'
  have hbase2 : RE2 S k5 (T.isub (ISub.cons .zero trivial (κ.comp κ'))) (a0.isub (κ.comp κ')) (a0'.isub (κ.comp κ')) := by
    have := RE2.isub hW ha0 (κ.comp κ'); rwa [hT0] at this
  have hψs2 := I.scoped_subst hψs (κ.comp κ').sc
  have face2 : (ival (idEnv k5) (ψ.subst (κ.comp κ').τ)).holds →
      RE2 S k5 (T.isub (ISub.cons .one trivial (κ.comp κ'))) (a0.isub (κ.comp κ')) (a0'.isub (κ.comp κ')) :=
    fun hh => RE2.conv hW (RT2.symm hW (hXT _ _) (hC k5 (κ.comp κ') .one trivial hh)) hbase2
  have hLRL : LineRob S k T T := fun k6 τ y y' hy hy' hE => by
    have b := hLR k6 τ y y' hy hy' hE
    have b' := hLR k6 τ y' y' hy' hy' (I_eq_refl _)
    exact RT2.trans hW (hXT _ _) b (RT2.symm hW (hXT _ _) b')
  have hT1Θ : ∀ {k6 : ℕ} (θ : ISub k6 k), (T.isub θ.up).dinst .one = T.isub (ISub.cons .one trivial θ) :=
    fun θ => isub_up_dinst T θ .one trivial
  by_cases hψ : I.Entails .one (ψ.subst κ.τ)
  · -- the face holds: the starts
    have hψ2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := by rw [hτ0]; exact ent_one_subst hψ _
    have hψ2' : I.Entails .one (ψ'.subst (κ.comp κ').τ) := ent_trans hψ2 (ent_subst h12 _)
    rw [if_pos hψ, if_pos hψ2', Tm.isub_isub]
    exact face2 ((holds_iff_entails hψs2).2 hψ2)
  rw [if_neg hψ]
  have Θe : (κ.comp κ').up = κ.up.comp κ'.up := ISub.up_comp κ κ'
  have heqΘ : EqTm S k5 .one [] (.transp (T.isub (κ.comp κ').up) (ψ.subst (κ.comp κ').τ) (a0.isub (κ.comp κ')))
      (.transp (T'.isub (κ.comp κ').up) (ψ'.subst (κ.comp κ').τ) (a0'.isub (κ.comp κ')))
      ((T.isub (κ.comp κ').up).dinst .one) := by
    have := EqTm.isubS hW heq (κ.comp κ'); rwa [transp_isub, transp_isub, isub_dinst] at this
  by_cases hf : (ival (idEnv (k4 + 1)) (φ.subst κ.up.τ)).holds
  · -- the face of the Glue line holds along the line: transports in the fibres
    rw [dif_pos hf]
    have hfτ : (ival (idEnv (k5 + 1)) (φ.subst (κ.comp κ').up.τ)).holds := by
      rw [Θe]; exact Model.Canon.holds_restr hφs κ.up κ'.up hf
    have eLeft : (Tm.transp (T.isub κ.up) (ψ.subst κ.τ) (a0.isub κ)).isub κ' =
        .transp (T.isub (κ.comp κ').up) (ψ.subst (κ.comp κ').τ) (a0.isub (κ.comp κ')) := by
      rw [transp_isub, Tm.isub_isub, ← Θe, ← hτ0, Tm.isub_isub]
    rw [eLeft]
    have htyL := hρT k5 (κ.comp κ')
    rw [hT1Θ] at htyL
    by_cases hψ2' : I.Entails .one (ψ'.subst (κ.comp κ').τ)
    · have hψ2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := ent_trans hψ2' (ent_subst h21 _)
      rw [if_pos hψ2']
      have r := face2 ((holds_iff_entails hψs2).2 hψ2)
      exact RE2.expandL hW (hTτ _) htyL (RE2.typed r).2.1 (stable_transpFace hW hψ2 htyL) r
    rw [if_neg hψ2', dif_pos hfτ]
    have hR0 : RedT S (k + 1) (T.isub (ISub.id (k + 1))) (.glue A φ Tf e) := by rw [isub_id_of_closed hTc]; exact hR
    have hGΘ := HasTy.isubS hW hG (κ.comp κ').up
    rw [isub_glue] at hGΘ
    have hGT := (RT2_glue_whnf hW hG hn hTTd hR).1
    have invG := RT2_glueW_inv hW hG hG hn hn (RT2_glue_whnf hW hG hn hTTd hR).2 (redT_glue_self hn) (redT_glue_self hn)
    have hfe := (holds_iff_entails (I.scoped_subst hφs (κ.comp κ').up.sc)).1 hfτ
    have hTfX : TyCode (k5 + 1) (semK S (k5 + 1) (Tf.isub (κ.comp κ').up)) :=
      tyCode_of_univ hW (glue_fiber_ty hW hG (κ.comp κ').up hfτ).choose_spec.1
    have hGTΘ := RT2.isub hW (tyCode_of_univ hW hG) hGT (κ.comp κ').up
    rw [isub_glue] at hGTΘ
    have hTfT : RT2 S (k5 + 1) (Tf.isub (κ.comp κ').up) (T.isub (κ.comp κ').up) :=
      RT2.trans hW hTfX (RT2_glue_fib0 hW hGΘ hfe (invG.2 _ (κ.comp κ').up hfτ).1) hGTΘ
    have K := (hIHT (k + 1) (ISub.id (k + 1)) A φ Tf e hR0).2 k5 (κ.comp κ').up hfτ _ _ hTfT (hTτ' _)
    have ha0Θ : RE2 S k5 ((T.isub (κ.comp κ').up).dinst .zero) (a0.isub (κ.comp κ')) (a0'.isub (κ.comp κ')) := by
      have := RE2.isub hW ha0 (κ.comp κ'); rwa [isub_dinst] at this
    have r := K (hLR.isub (κ.comp κ')) _ _ _ _ (hC.isub (κ.comp κ')) (hρT k5 (κ.comp κ')) (hρT' k5 (κ.comp κ'))
      heqΘ (ent_subst h12 _) (ent_subst h21 _) ha0Θ
    rwa [hT1Θ] at r
  -- the face of the Glue line does not hold along the line: the contractum at the Glue normal form
  rw [dif_neg hf]
  have hwκ := hw (k4 + 1) κ.up hf
  have hWt := hwκ.2.2.1
  have hnκ := hwκ.2.2.2.2.1
  have hWc := tyCode_of_univ hW hWt
  have hWT := (RT2_glue_whnf hW hWt hnκ (hTτ κ.up) hwκ.1).1
  have hWW := (RT2_glue_whnf hW hWt hnκ (hTτ κ.up) hwκ.1).2
  have invW := RT2_glueW_inv hW hWt hWt hnκ hnκ hWW (redT_glue_self hnκ) (redT_glue_self hnκ)
  obtain ⟨hφ1s, -⟩ := glue_data hW hWt
  have rGGκ := LineRob.transport hW hWt hWt hWT hWT (hLRL.isub κ)
  have cGκ := LineConst.transport hW hWt hWT (hC.isub κ)
  have htyκ := (HasTy.eqR (eq_transp_ty hW (hρT k4 κ) hwκ.1.2)).tyConv (tyEq_dinst hW hwκ.1.2 (r := .one) trivial)
  obtain ⟨lW, ⟨hW0, -, hconstW, -⟩, -⟩ := gen_transpF (spec_to_minimal hW htyκ) rfl
  have ha0κ : RE2 S k4 ((T.isub κ.up).dinst .zero) (a0.isub κ) (a0'.isub κ) := by
    have := RE2.isub hW ha0 κ; rwa [isub_dinst] at this
  have hW0T : RT2 S k4 ((Tm.glue (A1 (k4 + 1) κ.up hf) (φ1 (k4 + 1) κ.up hf) (T1 (k4 + 1) κ.up hf)
      (e1 (k4 + 1) κ.up hf)).dinst .zero) ((T.isub κ.up).dinst .zero) := by
    have := RT2.isub hW hWc hWT (ISub.cons .zero trivial (ISub.id k4))
    rwa [isub_cons_id_of_closed (closed_of_ty hW hWt), isub_cons_id_of_closed (closed_of_isTyK hW
      (Comp2_ty_base hWT).2.2.1)] at this
  have ha0W := RE2.conv hW (RT2.symm hW (RT2.tyCode_l hW hW0T (RE2.tyCode hW ha0κ)) hW0T) ha0κ
  have hty'κ : HasTy S k4 .one [] (.transp (.glue (A1 (k4 + 1) κ.up hf) (φ1 (k4 + 1) κ.up hf) (T1 (k4 + 1) κ.up hf)
      (e1 (k4 + 1) κ.up hf)) (ψ.subst κ.τ) (a0'.isub κ)) ((Tm.glue (A1 (k4 + 1) κ.up hf) (φ1 (k4 + 1) κ.up hf)
      (T1 (k4 + 1) κ.up hf) (e1 (k4 + 1) κ.up hf)).dinst .one) :=
    minimal_to_spec (HasTy0.transp hW0 (I.scoped_subst hψs κ.sc) hconstW (spec_to_minimal hW (RE2.typed ha0W).2.1))
  have heqκ := eqTm_transp_of hW htyκ hty'κ (TyEq.refl _) (ent_refl _) (ent_refl _) (RE2.typed ha0W).2.2
  have IA := hIHA (k4 + 1) κ.up _ _ _ _ hwκ.1
  have IT := hIHT (k4 + 1) κ.up _ _ _ _ hwκ.1
  have Dκ := TGD2_mk hW hWt hnκ hWt hnκ rGGκ rGGκ IA.1 IA.2 IT.1 IT.2 (forall0_scoped hφ1s) (ent_refl _)
    (ent_refl _) (forall0_scoped hφ1s) (ent_refl _) (ent_refl _) htyκ hty'κ heqκ (ent_refl _) (ent_refl _) cGκ ha0W
  have D2 := Dκ.isub hW κ'
  rw [Tm.isub_isub a0, Tm.isub_isub a0', ← hτ0] at D2
  rw [tgw_isub, Tm.isub_isub a0, ← hτ0]
  -- the restricted Glue normal form against the line
  have hWT1 : RT2 S k5 ((Tm.glue ((A1 (k4 + 1) κ.up hf).isub κ'.up) ((φ1 (k4 + 1) κ.up hf).subst κ'.up.τ)
      ((T1 (k4 + 1) κ.up hf).isub κ'.up) ((e1 (k4 + 1) κ.up hf).isub κ'.up)).dinst .one)
      (T.isub (ISub.cons .one trivial (κ.comp κ'))) := by
    have := RT2.isub hW hWc hWT (ISub.cons .one trivial κ')
    rw [Tm.isub_isub, ISub.up_comp_cons, ← isub_up_dinst _ _ .one trivial, isub_glue] at this
    exact this
  by_cases hψ2' : I.Entails .one (ψ'.subst (κ.comp κ').τ)
  · -- the face of the transport holds at the further restriction
    have hψ2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := ent_trans hψ2' (ent_subst h21 _)
    rw [if_pos hψ2']
    exact RE2.conv hW hWT1 (D2.bdryψ hW ((holds_iff_entails hψs2).2 hψ2))
  rw [if_neg hψ2']
  -- the faces of the Glue lines at the further restriction
  have eφ : ∀ {x : I}, (x.subst κ.up.τ).subst κ'.up.τ = x.subst (κ.comp κ').up.τ := fun {x} => by
    rw [Θe, I_subst_comp]
  have φ1e : I.Entails ((φ1 (k4 + 1) κ.up hf).subst κ'.up.τ) (φ.subst (κ.comp κ').up.τ) := by
    rw [← eφ]; exact ent_subst hwκ.2.2.2.2.2.2.1 _
  have φ1e' : I.Entails (φ.subst (κ.comp κ').up.τ) ((φ1 (k4 + 1) κ.up hf).subst κ'.up.τ) := by
    rw [← eφ]; exact ent_subst hwκ.2.2.2.2.2.2.2 _
  have hφτs := I.scoped_subst hφs (κ.comp κ').up.sc
  have hφ1τs := I.scoped_subst hφ1s κ'.up.sc
  by_cases hfτ : (ival (idEnv (k5 + 1)) (φ.subst (κ.comp κ').up.τ)).holds
  · -- the face of the Glue line holds along the further restricted line
    rw [dif_pos hfτ]
    have hφ1τ : I.Entails .one ((φ1 (k4 + 1) κ.up hf).subst κ'.up.τ) :=
      ent_trans ((holds_iff_entails hφτs).1 hfτ) φ1e'
    have hφ1τh := (holds_iff_entails hφ1τs).2 hφ1τ
    have hδ2 : (ival (idEnv k5) ((φ1 (k4 + 1) κ.up hf).forall0.subst κ'.τ)).holds :=
      (holds_iff_entails (I.scoped_subst (forall0_scoped hφ1s) κ'.sc)).2
        (ent_trans (ent_one_forall0 hφ1τ) (forall0_subst _ κ'.τ).2)
    have x := D2.bdryδ hW hδ2
    obtain ⟨lX, hXt, -⟩ := glue_fiber_ty hW hWt κ'.up hφ1τh
    have hXc := tyCode_of_univ hW hXt
    have hXX := (invW.2 _ κ'.up hφ1τh).1
    have hW2t := HasTy.isubS hW hWt κ'.up
    rw [isub_glue] at hW2t
    have hXW := RT2_glue_fib0 hW hW2t hφ1τ hXX
    have hW2T := RT2.isub hW hWc hWT κ'.up
    rw [Tm.isub_isub, ← Θe, isub_glue] at hW2T
    have hXT := RT2.trans hW hXc hXW hW2T
    have hXX' := RT2.trans hW hXc hXT (hTτ' _)
    obtain ⟨l0', ⟨hT'l, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
    have hX't := HasTy.isubS hW (minimal_to_spec hT'l) (κ.comp κ').up
    have K := IT.2 k5 κ'.up hφ1τh _ _ hXX hXX'
    have LR := LineRob.transport hW hXt hX't hXT (hT'τ _) (hLR.isub (κ.comp κ'))
    have LC := LineConst.transport hW hXt hXT (hC.isub (κ.comp κ'))
    have eXT := (Comp2_ty_base hXT).2.2.2.2.2
    have eXW := (Comp2_ty_base hXW).2.2.2.2.2
    have htyX := (RE2.typed x).2.1.tyConv (tyEq_dinst hW (TyEq.symm eXW) (r := .one) trivial)
    have htyX' := (hρT' k5 (κ.comp κ')).tyConv (tyEq_dinst hW (TyEq.symm eXT) (r := .one) trivial)
    have hX0T := RT2.dinstE hW hXc hXT (d := .zero) trivial
    have hX1T := RT2.dinstE hW hXc hXT (d := .one) trivial
    rw [isub_up_dinst T (κ.comp κ') .zero trivial] at hX0T
    rw [isub_up_dinst T (κ.comp κ') .one trivial] at hX1T
    have ha0X := RE2.conv hW (RT2.symm hW (RT2.tyCode_l hW hX0T (RE2.tyCode hW hbase2)) hX0T) hbase2
    have heqX := eqTm_transp_of hW htyX htyX' (Comp2_ty_base hXX').2.2.2.2.2 (ent_subst h12 _) (ent_subst h21 _)
      (RE2.typed ha0X).2.2
    have r := K LR _ _ _ _ LC htyX htyX' heqX (ent_subst h12 _) (ent_subst h21 _) ha0X
    exact RE2.trans hW (hTτ _) (RE2.conv hW hWT1 x) (RE2.conv hW hX1T r)
  · rw [dif_neg hfτ]
    have hwτ := hw (k5 + 1) (κ.comp κ').up hfτ
    have hW't := hwτ.2.2.2.1
    have hn'τ := hwτ.2.2.2.2.2.1
    have hW'T' := (RT2_glue_whnf hW hW't hn'τ (hT'τ _) hwτ.2.1).1
    have hW2t := HasTy.isubS hW hWt κ'.up
    rw [isub_glue] at hW2t
    have hn2 : ¬ I.Entails .one ((φ1 (k4 + 1) κ.up hf).subst κ'.up.τ) := fun h =>
      hfτ ((holds_iff_entails hφτs).2 (ent_trans h φ1e))
    have hW2T := RT2.isub hW hWc hWT κ'.up
    rw [Tm.isub_isub, ← Θe, isub_glue] at hW2T
    have rG := LineRob.transport hW hW2t hW't hW2T hW'T' (hLR.isub (κ.comp κ'))
    have rGG := LineRob.transport hW hW2t hW2t hW2T hW2T (hLRL.isub (κ.comp κ'))
    have eW2T := (Comp2_ty_base hW2T).2.2.2.2.2
    have eW2T1 := tyEq_dinst hW eW2T (r := .one) trivial
    have h1 := (hρT' k5 (κ.comp κ')).tyConv (eT1 k5 (κ.comp κ'))
    have eR := eq_transp_ty hW h1 hwτ.2.1.2
    have eL := eq_transp_ty hW (hρT k5 (κ.comp κ')) (TyEq.symm eW2T)
    have hty'5 := (HasTy.eqR eR).tyConv ((TyEq.symm (eT1 k5 (κ.comp κ'))).trans hW (TyEq.symm eW2T1))
    have heq5 := ((eL.symm.trans heqΘ).trans (eR.tyConv (TyEq.symm (eT1 k5 (κ.comp κ'))))).tyConv
      (TyEq.symm eW2T1)
    have D5 := TGD2_mk hW hW2t hn2 hW't hn'τ rG rGG D2.kAR D2.kATR D2.kTR D2.kTTR D2.hδs D2.hδ1 D2.hδ2
      (forall0_scoped (glue_data hW hW't).1) (ent_refl _) (ent_refl _) D2.hty hty'5 heq5 (ent_subst h12 _)
      (ent_subst h21 _) D2.cG D2.ha0
    exact RE2.conv hW hWT1 (D5.final hW)

end

end Model.Whnf
