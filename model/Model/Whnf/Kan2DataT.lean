import Model.Whnf.Kan2DataTInd

/-!
# Transport along related lines whose normal forms are inductive types without path constructors

At every restriction, transport along a line reduces its line to its normal form `data d P1` (a literal
line), where `kanT2_lit` applies; the restricted lines are robustly related through the normal forms
of the restrictions of the lines (`kanT2_data`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

section gen
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  (hp : D.params ≠ [])
include hW hD hH hp

/-- Transport along related lines whose normal forms are an inductive type without path constructors
(with parameters). The Kan properties of the argument types are required at the literal lines related
to the restrictions of `T`. -/
theorem kanT2_data {T T' ps : Tm} (hTT : RT2 S (k + 1) T T') (hR : RedT S (k + 1) T (.data d ps))
    (hK : ∀ k1 (θ : ISub (k1 + 1) (k + 1)) P1, HasTy S (k1 + 1) .one [] (.data d P1) (.univ D.level) →
      RT2 S (k1 + 1) (.data d P1) (T.isub θ) →
      ∀ c j n (g : Hom n (k1 + 1)) pre, (ΘK S D d (k1 + 1) P1).PtValid c n g pre →
        KanP2 S n ((ΘK S D d (k1 + 1) P1).ty c j n g pre)) :
    KanT2 S k T T' := by
  intro hLR φ φ' a0 a0' hC hty hty' heq h12 h21 ha0
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hXT0 : TyCode (k + 1) (semK S (k + 1) T) := tyCode_of_univ hW hTl'
  have hTTd : RT2 S (k + 1) T T := RT2.refl hW hXT0 hTT
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hw := fun k3 (σ : ISub k3 (k + 1)) => data_whnf_pair hW hD hTT hR σ
  choose P1 P1' hw using hw
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
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
  have hTK : ∀ {k3 : ℕ} (σ : ISub k3 (k + 1)), IsTyK S k3 (T.isub σ) := fun σ => ⟨l0, .inl (HasTy.isubS hW hTl' σ)⟩
  -- the normal forms, as literal lines, against the lines
  have NP : ∀ k3 (σ : ISub k3 (k + 1)) k6 (θ : ISub k6 k3),
      RT2 S k6 (.data d ((P1 k3 σ).isub θ)) (T.isub (σ.comp θ)) := by
    intro k3 σ k6 θ
    have h := RT2.isub hW (hXT k3 σ) (RT2_data_whnf hW hD (hTτ σ) (hw k3 σ).1) θ
    rw [Tm.isub_isub] at h
    exact RT2.symm hW (hXT _ _) h
  have NQ : ∀ k3 (σ : ISub k3 (k + 1)) k6 (θ : ISub k6 k3),
      RT2 S k6 (.data d ((P1' k3 σ).isub θ)) (T'.isub (σ.comp θ)) := by
    intro k3 σ k6 θ
    have hX' : TyCode k3 (semK S k3 (T'.isub σ)) := RT2.tyCode_r hW (hTτ' σ) (hXT k3 σ)
    have h := RT2.isub hW hX' (RT2_data_whnf hW hD (hT'τ σ) (hw k3 σ).2) θ
    rw [Tm.isub_isub] at h
    exact RT2.symm hW (RT2.tyCode_r hW (RT2.isub hW (hXT k3 σ) (hTτ' σ) θ) (by
      have := hXT _ (σ.comp θ); rwa [← Tm.isub_isub] at this) |> fun h0 => by rw [Tm.isub_isub] at h0; exact h0) h
  -- the self-robustness of the line
  have hLRL : LineRob S k T T := fun k6 τ y y' hy hy' hE => by
    have b := hLR k6 τ y y' hy hy' hE
    have b' := hLR k6 τ y' y' hy' hy' (I_eq_refl _)
    exact RT2.trans hW (hXT _ _) b (RT2.symm hW (hXT _ _) b')
  have eUp : ∀ {k4 k5 k6 : ℕ} (κ : ISub k4 k) (κ' : ISub k5 k4) (y : I) (hy : y.Scoped k6) (τ : ISub k6 k5),
      κ.up.comp (κ'.up.comp (ISub.cons y hy τ)) = ISub.cons y hy (κ.comp (κ'.comp τ)) := by
    intro k4 k5 k6 κ κ' y hy τ; rw [ISub.up_comp_cons, ISub.up_comp_cons]
  have eUp' : ∀ {k4 k5 k6 : ℕ} (κ : ISub k4 k) (κ' : ISub k5 k4) (y : I) (hy : y.Scoped k6) (τ : ISub k6 k5),
      (κ.comp κ').up.comp (ISub.cons y hy τ) = ISub.cons y hy (κ.comp (κ'.comp τ)) := by
    intro k4 k5 k6 κ κ' y hy τ; rw [ISub.up_comp_cons, ISub.comp_assoc]
  -- the restricted normal forms are robustly related
  have RobPQ : ∀ {k4 k5 : ℕ} (κ : ISub k4 k) (κ' : ISub k5 k4),
      Rob S d k5 ((P1 (k4 + 1) κ.up).isub κ'.up) (P1' (k5 + 1) (κ.comp κ').up) := by
    intro k4 k5 κ κ' k6 τ y y' hy hy' hE
    have a := NP (k4 + 1) κ.up k6 (κ'.up.comp (ISub.cons y hy τ))
    have c := NQ (k5 + 1) (κ.comp κ').up k6 (ISub.cons y' hy' τ)
    rw [eUp] at a
    rw [eUp'] at c
    have b := hLR k6 (κ.comp (κ'.comp τ)) y y' hy hy' hE
    rw [Tm.isub_isub]
    exact RT2.trans hW (RT2.tyCode_l hW a (hXT _ _)) a
      (RT2.trans hW (hXT _ _) b (RT2.symm hW (RT2.tyCode_l hW c (RT2.tyCode_r hW b (hXT _ _))) c))
  have RobPP : ∀ {k4 k5 : ℕ} (κ : ISub k4 k) (κ' : ISub k5 k4),
      Rob S d k5 ((P1 (k4 + 1) κ.up).isub κ'.up) ((P1 (k4 + 1) κ.up).isub κ'.up) := by
    intro k4 k5 κ κ' k6 τ y y' hy hy' hE
    have a := NP (k4 + 1) κ.up k6 (κ'.up.comp (ISub.cons y hy τ))
    have c := NP (k4 + 1) κ.up k6 (κ'.up.comp (ISub.cons y' hy' τ))
    rw [eUp] at a c
    have b := hLRL k6 (κ.comp (κ'.comp τ)) y y' hy hy' hE
    rw [Tm.isub_isub, Tm.isub_isub]
    exact RT2.trans hW (RT2.tyCode_l hW a (hXT _ _)) a (RT2.trans hW (hXT _ _) b (RT2.symm hW
      (RT2.tyCode_l hW c (hXT _ _)) c))
  -- typings
  have hX : TyCode k (semK S k (T.dinst .one)) := by
    have := hXT k (ISub.cons .one trivial (ISub.id k)); rwa [isub_cons_id_of_closed hTc] at this
  have hYY : RT2 S k (T.dinst .one) (T.dinst .one) := by
    have := hTτ (ISub.cons .one trivial (ISub.id k)); rwa [isub_cons_id_of_closed hTc] at this
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty ρ; rwa [isub_dinst] at this
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty' ρ; rwa [isub_dinst] at this
  have eT1 : ∀ k' (ρ : ISub k' k), TyEq S k' ((T.isub ρ.up).dinst .one) ((T'.isub ρ.up).dinst .one) := fun k' ρ => by
    have := (tyEq_dinst hW (Comp2_ty_base hTT).2.2.2.2.2 (r := .one) trivial).isub hW ρ
    rwa [isub_dinst, isub_dinst] at this
  -- the reducts at the restrictions
  have hu : ∀ k4 (κ : ISub k4 k), Red S ((Tm.transp T φ a0).isub κ)
      (if I.Entails .one (φ.subst κ.τ) then a0.isub κ else .transp (.data d (P1 (k4 + 1) κ.up)) (φ.subst κ.τ) (a0.isub κ)) ∧
      EqTm S k4 .one [] ((Tm.transp T φ a0).isub κ)
      (if I.Entails .one (φ.subst κ.τ) then a0.isub κ else .transp (.data d (P1 (k4 + 1) κ.up)) (φ.subst κ.τ) (a0.isub κ))
      ((T.dinst .one).isub κ) := by
    intro k4 κ
    show Red S (.transp (T.isub κ.up) (φ.subst κ.τ) (a0.isub κ)) _ ∧ EqTm S k4 .one [] _ _ _
    rw [isub_dinst]
    split_ifs with hf
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (hρT k4 κ)⟩
    · exact ⟨red_transp_ty hf (hw (k4 + 1) κ.up).1.1.1, eq_transp_ty hW (hρT k4 κ) (hw (k4 + 1) κ.up).1.2⟩
  have hu' : ∀ k4 (κ : ISub k4 k), Red S ((Tm.transp T' φ' a0').isub κ)
      (if I.Entails .one (φ'.subst κ.τ) then a0'.isub κ else .transp (.data d (P1' (k4 + 1) κ.up)) (φ'.subst κ.τ) (a0'.isub κ)) ∧
      EqTm S k4 .one [] ((Tm.transp T' φ' a0').isub κ)
      (if I.Entails .one (φ'.subst κ.τ) then a0'.isub κ else .transp (.data d (P1' (k4 + 1) κ.up)) (φ'.subst κ.τ) (a0'.isub κ))
      ((T.dinst .one).isub κ) := by
    intro k4 κ
    show Red S (.transp (T'.isub κ.up) (φ'.subst κ.τ) (a0'.isub κ)) _ ∧ EqTm S k4 .one [] _ _ _
    rw [isub_dinst]
    split_ifs with hf
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (hρT' k4 κ)⟩
    · have e1 := eq_transp_ty hW ((hρT' k4 κ).tyConv (eT1 k4 κ)) (hw (k4 + 1) κ.up).2.2
      exact ⟨red_transp_ty hf (hw (k4 + 1) κ.up).2.1.1, e1.tyConv (TyEq.symm (eT1 k4 κ))⟩
  refine RE2.expandBoth hW hX hYY hty hty' _ _ hu hu' (fun k4 κ k5 κ' => ?_)
  dsimp only
  rw [hT1]
  have hτ0 : ∀ {x : I}, x.subst (κ.comp κ').τ = (x.subst κ.τ).subst κ'.τ := fun {x} => I_subst_comp x κ κ'
  have hbase2 : RE2 S k5 (T.isub (ISub.cons .zero trivial (κ.comp κ'))) (a0.isub (κ.comp κ')) (a0'.isub (κ.comp κ')) := by
    have := RE2.isub hW ha0 (κ.comp κ'); rwa [hT0] at this
  have hφs2 := I.scoped_subst hφs (κ.comp κ').sc
  have face2 : (ival (idEnv k5) (φ.subst (κ.comp κ').τ)).holds →
      RE2 S k5 (T.isub (ISub.cons .one trivial (κ.comp κ'))) (a0.isub (κ.comp κ')) (a0'.isub (κ.comp κ')) :=
    fun hh => RE2.conv hW (RT2.symm hW (hXT _ _) (hC k5 (κ.comp κ') .one trivial hh)) hbase2
  have eLeft : (Tm.transp (.data d (P1 (k4 + 1) κ.up)) (φ.subst κ.τ) (a0.isub κ)).isub κ' =
      .transp (.data d ((P1 (k4 + 1) κ.up).isub κ'.up)) (φ.subst (κ.comp κ').τ) (a0.isub (κ.comp κ')) := by
    show Tm.transp (Tm.data d ((P1 (k4 + 1) κ.up).isub κ'.up)) ((φ.subst κ.τ).subst κ'.τ) ((a0.isub κ).isub κ') = _
    rw [← hτ0, Tm.isub_isub]
  by_cases hf : I.Entails .one (φ.subst κ.τ)
  · -- the face holds: the bases
    have hf2 : I.Entails .one (φ.subst (κ.comp κ').τ) := by rw [hτ0]; exact ent_one_subst hf _
    have hf2' : I.Entails .one (φ'.subst (κ.comp κ').τ) := ent_trans hf2 (ent_subst h12 _)
    rw [if_pos hf, if_pos hf2', Tm.isub_isub]
    exact face2 ((holds_iff_entails hφs2).2 hf2)
  -- the left reduct, restricted, and its typing
  have htyL := HasTy.isubS hW (HasTy.eqR (hu k4 κ).2) κ'
  rw [if_neg hf, eLeft, Tm.isub_isub, hT1] at htyL
  rw [if_neg hf, eLeft]
  by_cases hf2' : I.Entails .one (φ'.subst (κ.comp κ').τ)
  · -- the face holds at the further restriction
    have hf2 : I.Entails .one (φ.subst (κ.comp κ').τ) := ent_trans hf2' (ent_subst h21 _)
    rw [if_pos hf2']
    have hst := stable_transpFace hW hf2 htyL
    have r := face2 ((holds_iff_entails hφs2).2 hf2)
    exact RE2.expandL hW (hTτ _) htyL (RE2.typed r).2.1 hst r
  rw [if_neg hf2']
  -- the face holds at neither: transport along the literal lines
  have hP := HasTy.isubS hW (data_whnf_ty hW hD (hTK κ.up) (hw (k4 + 1) κ.up).1) κ'.up
  have hPT : RT2 S (k5 + 1) (.data d ((P1 (k4 + 1) κ.up).isub κ'.up)) (T.isub (κ.comp κ').up) := by
    have := NP (k4 + 1) κ.up (k5 + 1) κ'.up; rwa [← ISub.up_comp] at this
  have K := kanT2_lit hW hD hH hp hP (hK k5 (κ.comp κ').up _ hP hPT) (RobPP κ κ') (RobPQ κ κ')
  have hPc : (Tm.data d ((P1 (k4 + 1) κ.up).isub κ'.up)).closedB 0 (k5 + 1) = true := closed_of_ty hW hP
  have eP : ∀ (r : I) (hr : r.Scoped k5),
      RT2 S k5 ((Tm.data d ((P1 (k4 + 1) κ.up).isub κ'.up)).dinst r) (T.isub (ISub.cons r hr (κ.comp κ'))) := by
    intro r hr
    have a := NP (k4 + 1) κ.up k5 (κ'.up.comp (ISub.cons r hr (ISub.id k5)))
    rw [eUp, ISub.comp_id] at a
    rw [← isub_cons_id_of_closed hPc r hr]
    show RT2 S k5 (Tm.data d (((P1 (k4 + 1) κ.up).isub κ'.up).isub _)) _
    rw [Tm.isub_isub]; exact a
  have LCP : LineConst S k5 (.data d ((P1 (k4 + 1) κ.up).isub κ'.up)) (φ.subst (κ.comp κ').τ) := by
    intro k6 τ r hr hh
    have a := NP (k4 + 1) κ.up k6 (κ'.up.comp (ISub.cons r hr τ))
    have c := NP (k4 + 1) κ.up k6 (κ'.up.comp (ISub.cons .zero trivial τ))
    rw [eUp] at a c
    have hh' : (ival (idEnv k6) (φ.subst (κ.comp (κ'.comp τ)).τ)).holds := by
      rw [← ISub.comp_assoc, I_subst_comp]; exact hh
    have b := hC k6 (κ.comp (κ'.comp τ)) r hr hh'
    show RT2 S k6 (Tm.data d (((P1 (k4 + 1) κ.up).isub κ'.up).isub _)) (Tm.data d (((P1 (k4 + 1) κ.up).isub κ'.up).isub _))
    rw [Tm.isub_isub, Tm.isub_isub]
    exact RT2.trans hW (RT2.tyCode_l hW a (hXT _ _)) a
      (RT2.trans hW (hXT _ _) b (RT2.symm hW (RT2.tyCode_l hW c (hXT _ _)) c))
  have hX1 : TyCode k5 (semK S k5 ((Tm.data d ((P1 (k4 + 1) κ.up).isub κ'.up)).dinst .one)) :=
    RT2.tyCode_l hW (eP .one trivial) (hXT _ _)
  have hX0 : TyCode k5 (semK S k5 ((Tm.data d ((P1 (k4 + 1) κ.up).isub κ'.up)).dinst .zero)) :=
    RT2.tyCode_l hW (eP .zero trivial) (hXT _ _)
  have htyL' := htyL.tyConv (TyEq.symm (tyB (eP .one trivial)))
  have htyR := HasTy.eqR (hu' k5 (κ.comp κ')).2
  rw [if_neg hf2', hT1] at htyR
  have htyR' := htyR.tyConv (TyEq.symm (tyB (eP .one trivial)))
  have hbaseP := RE2.conv hW (RT2.symm hW hX0 (eP .zero trivial)) hbase2
  have ePQ : TyEq S (k5 + 1) (.data d ((P1 (k4 + 1) κ.up).isub κ'.up)) (.data d (P1' (k5 + 1) (κ.comp κ').up)) := by
    have := RobPQ κ κ' (k5 + 1) (ISub.id k5).up.tail (.var 0) (.var 0) (show 0 < k5 + 1 by omega)
      (show 0 < k5 + 1 by omega) (I_eq_refl _)
    rw [ISub.cons_var0_up_tail] at this
    have hQc : (Tm.data d (P1' (k5 + 1) (κ.comp κ').up)).closedB 0 (k5 + 1) = true :=
      closed_of_isTyK hW (Comp2_ty_base (RT2_data_whnf hW hD (hT'τ _) (hw (k5 + 1) (κ.comp κ').up).2)).2.2.1
    have e1 := isub_up_id_of_closed hPc
    have e2 := isub_up_id_of_closed hQc
    exact tyB (by
      show RT2 S (k5 + 1) (Tm.data d ((P1 (k4 + 1) κ.up).isub κ'.up)) (Tm.data d (P1' (k5 + 1) (κ.comp κ').up))
      rw [← e1, ← e2]; exact this)
  have heqLR := eqTm_transp_of hW htyL' htyR' ePQ (ent_subst h12 _) (ent_subst h21 _) (RE2.typed hbaseP).2.2
  have r := K (RobPQ κ κ') _ _ _ _ LCP htyL' htyR' heqLR (ent_subst h12 _) (ent_subst h21 _) hbaseP
  exact RE2.conv hW (eP .one trivial) r

end gen

/-- Transport along related lines whose normal forms are an inductive type without path constructors, or
without parameters. -/
theorem kanT2_data' (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
    (hHp : D.isHIT = false ∨ D.params = []) {T T' ps : Tm} (hTT : RT2 S (k + 1) T T')
    (hR : RedT S (k + 1) T (.data d ps))
    (hK : ∀ k1 (θ : ISub (k1 + 1) (k + 1)) P1, HasTy S (k1 + 1) .one [] (.data d P1) (.univ D.level) →
      RT2 S (k1 + 1) (.data d P1) (T.isub θ) →
      ∀ c j n (g : Hom n (k1 + 1)) pre, (ΘK S D d (k1 + 1) P1).PtValid c n g pre →
        KanP2 S n ((ΘK S D d (k1 + 1) P1).ty c j n g pre)) :
    KanT2 S k T T' := by
  by_cases h0 : D.params = []
  · exact kanT2_data0 hW hD h0 hTT hR
  · exact kanT2_data hW hD (hHp.resolve_right h0) h0 hTT hR hK

end

end Model.Whnf
