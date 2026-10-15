import Model.Whnf.Kan2DataHITInd2

/-!
# Transport along lines of higher inductive types: the induction

The intro case of the induction (`tm1_mainH`): the transports of related elements are related, by expansion at
each restriction to the contracta of the transports of their normal forms. Across restrictions, a
restricted normal form is a normal form, a constructor at a boundary (whose contractum is related to the
contractum of the boundary term's normal form by `bnd_transp`), or a composition whose face holds (by the
`TR` part of the motive at its tube).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

section ind
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hyp : HITHyp2 S (d + 1)) (hp : D.params ≠ []) {K : ℕ} {P : Tm} (hP : HasTy S (K + 1) .one [] (.data d P) (.univ D.level))

  (hRL : Rob S d K P P)
include hW hD hH hyp hp hP  hRL

/-- The intro case: transport of related elements, from the contracta of their normal forms at all
restrictions. -/
theorem tm1_mainH {k1 : ℕ} {g : Hom k1 K} {A x x' : Tm}
    (ih : ∀ k' (σ : ISub k' k1), TM2H S d D K P k' (g.comp σ.hom) (A.isub σ) (x.isub σ) (x'.isub σ))
    (ihc : ∀ k' (σ : ISub k' k1) w, RedW S (x.isub σ) w → ∀ k'' (ρ' : ISub k'' k'),
      TM2H S d D K P k'' (g.comp (σ.comp ρ').hom) (A.isub (σ.comp ρ')) (w.isub ρ') (x.isub (σ.comp ρ'))) :
    TM1 S d K P k1 g A x x' := by
  intro ρ hg hAe Q hQ k3 σ y y' hy hy' hE h0 LR ψ ψ' LC hty hty' heq h12 h21 hbase
  subst hg hAe
  have hdD := dataD_eq hW hD
  have hPc := data_closed hW hD hP
  have hPP1 := PP1 hW hD hp hP  hRL
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  obtain ⟨-, ⟨-, hψs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hψs' : ψ'.Scoped k3 := (gen_transpF (spec_to_minimal hW hty') rfl).choose_spec.1.2.1
  -- the line, its restrictions and their ends
  -- the restrictions of the line
  have eL : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I),
      (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst r).isub κ =
        ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst
          (r.subst κ.τ) := by
    intro k4 κ r; rw [isub_dinst, line_isub_up]
  have eL' : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I),
      (((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)).dinst r).isub κ =
        ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst
          (r.subst κ.τ) := by
    intro k4 κ r; rw [isub_dinst, line_isub_up]
  -- the bases at a restriction, at the start of the restricted line
  have hb : ∀ {k4 : ℕ} (κ : ISub k4 k3), RE2 S k4 (.data d (P.isub (ISub.cons
      ((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ)
      (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) ((ρ.comp σ).comp κ))))
      (x.isub (σ.comp κ)) (x'.isub (σ.comp κ)) := by
    intro k4 κ
    have h := RE2.isub hW hbase κ
    rw [eL, Tm.isub_isub, Tm.isub_isub, show I.subst κ.τ I.zero = I.zero from rfl,
      lineP_dinst hW hD hp hP  hRL _ _ _ .zero trivial] at h
    exact h
  -- the normal forms of the bases
  have hw := fun k4 (κ : ISub k4 k3) => whnf_data hW hD hH hyp hP hPP1 _ (hb κ)
  choose W hWr hWF hWW hWx using hw
  have hw' := fun k4 (κ : ISub k4 k3) => whnf_data hW hD hH hyp hP hPP1 _
    (RE2.symm hW (hRL k4 _ _ _ (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc)
      (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) (I_eq_refl _)) (hb κ))
  choose W' hWr' hWF' hWW' hWx' using hw'
  -- the ends of the restricted lines
  have hPend : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I) (hr0 : r.Scoped k4),
      ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r =
        .data d (P.isub (ISub.cons ((y.subst κ.up.τ).subst (ISub.cons r hr0 (ISub.id k4)).τ)
          (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons r hr0 (ISub.id k4)).sc) ((ρ.comp σ).comp κ))) :=
    fun κ r hr0 => lineP_dinst hW hD hp hP  hRL _ _ _ r hr0
  have hQc : ∀ {k4 : ℕ} (θ : ISub k4 (K + 1)), (Tm.data d (Q.isub θ)).closedB 0 k4 = true := by
    intro k4 θ
    have := closed_of_isTyK hW (Comp2_ty_base (hQ k4 θ.tail (θ.τ 0) (θ.τ 0) (θ.sc 0 (by omega)) (θ.sc 0 (by omega))
      (I_eq_refl _))).2.2.1
    rwa [ISub.cons_tail] at this
  have hQend : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I) (hr0 : r.Scoped k4),
      ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r =
        .data d (Q.isub (ISub.cons ((y'.subst κ.up.τ).subst (ISub.cons r hr0 (ISub.id k4)).τ)
          (I.scoped_subst (I.scoped_subst hy' κ.up.sc) (ISub.cons r hr0 (ISub.id k4)).sc) ((ρ.comp σ).comp κ))) := by
    intro k4 κ r hr0
    show (Tm.data d (Q.isub _)).dinst r = _
    rw [← isub_cons_id_of_closed (hQc _) r hr0]
    show Tm.data d ((Q.isub _).isub _) = _
    rw [Tm.isub_isub, line_comp, ISub.comp_id]
  -- the ends of the right line are those of the left line
  have hLR : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I) (hr0 : r.Scoped k4),
      RT2 S k4 (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r)
        (((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r) := by
    intro k4 κ r hr0
    rw [hPend κ r hr0, hQend κ r hr0]
    exact hQ k4 _ _ _ _ _ (I_eq_subst (I_eq_subst hE _) _)
  -- the typings at a restriction
  have htyκ : ∀ {k4 : ℕ} (κ : ISub k4 k3), HasTy S k4 .one []
      (.transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ.subst κ.τ) (x.isub (σ.comp κ)))
      (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .one) := by
    intro k4 κ
    have h := HasTy.isubS hW hty κ
    have e : (Tm.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ)).isub κ =
        .transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ.subst κ.τ) (x.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d P).isub _).isub κ.up) _ ((x.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one] at h
    exact h
  have htyκ' : ∀ {k4 : ℕ} (κ : ISub k4 k3), HasTy S k4 .one []
      (.transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ'.subst κ.τ) (x'.isub (σ.comp κ)))
      (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .one) := by
    intro k4 κ
    have h := HasTy.isubS hW hty' κ
    have e : (Tm.transp ((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) ψ' (x'.isub σ)).isub κ =
        .transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ'.subst κ.τ) (x'.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d Q).isub _).isub κ.up) _ ((x'.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one] at h
    exact h
  have heqκ : ∀ {k4 : ℕ} (κ : ISub k4 k3), EqTm S k4 .one []
      (.transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ.subst κ.τ) (x.isub (σ.comp κ)))
      (.transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ'.subst κ.τ) (x'.isub (σ.comp κ)))
      (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .one) := by
    intro k4 κ
    have h := EqTm.isubS hW heq κ
    have e : (Tm.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ)).isub κ =
        .transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ.subst κ.τ) (x.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d P).isub _).isub κ.up) _ ((x.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    have e' : (Tm.transp ((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) ψ' (x'.isub σ)).isub κ =
        .transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ'.subst κ.τ) (x'.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d Q).isub _).isub κ.up) _ ((x'.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, e', eL κ .one] at h
    exact h
  -- the end of the line is related to itself
  have hcL : ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).closedB 0 (k3 + 1) = true :=
    closed_of_ty hW (HasTy.isubS hW hP _)
  have hX : TyCode k3 (semK S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one)) :=
    tyCode_of_ty hW hty
  have hAA : RT2 S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one)
      (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one) := by
    have h := LR k3 (ISub.id k3) .one .one trivial trivial (I_eq_refl _)
    rw [isub_cons_id_of_closed hcL] at h
    exact RT2.refl hW hX h
  refine RE2.expandBoth hW hX hAA hty hty'
    (fun k4 κ => if I.Entails .one (ψ.subst κ.τ) then x.isub (σ.comp κ) else
      tRedF d D (P.isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ.subst κ.τ) (W k4 κ))
    (fun k4 κ => if I.Entails .one (ψ'.subst κ.τ) then x'.isub (σ.comp κ) else
      tRedF d D (Q.isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ'.subst κ.τ) (W' k4 κ))
    (fun k4 κ => ?_) (fun k4 κ => ?_) (fun k4 κ k5 κ' => ?_)
  · -- the left reducts
    have e : (Tm.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ)).isub κ =
        .transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ.subst κ.τ) (x.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d P).isub _).isub κ.up) _ ((x.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one]
    dsimp only
    split_ifs with hf
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (htyκ κ)⟩
    · have eb := (hWr k4 κ).2
      rw [← hPend κ .zero trivial] at eb
      obtain ⟨r1, e1, -⟩ := tred_red hW hD hp hH (PL := P.isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc)
        ((ρ.comp σ).comp κ).up.tail)) hf (hWF k4 κ) (hWr k4 κ).1 (htyκ κ) eb
      exact ⟨r1, e1⟩
  · -- the right reducts
    have e : (Tm.transp ((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) ψ' (x'.isub σ)).isub κ =
        .transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ'.subst κ.τ) (x'.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d Q).isub _).isub κ.up) _ ((x'.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one]
    dsimp only
    split_ifs with hf
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (htyκ' κ)⟩
    · have r0 := hLR κ .zero trivial
      have r1 := hLR κ .one trivial
      have eb := (hWr' k4 κ).2
      rw [← hPend κ .zero trivial] at eb
      have eb' := eb.tyConv (tyB r0)
      have hty1 := (htyκ' κ).tyConv (tyB r1)
      obtain ⟨r2, e2, -⟩ := tred_red hW hD hp hH (PL := Q.isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc)
        ((ρ.comp σ).comp κ).up.tail)) hf (hWF' k4 κ) (hWr' k4 κ).1 hty1 eb'
      exact ⟨r2, e2.tyConv (TyEq.symm (tyB r1))⟩
  · -- the reducts across restrictions
    have hPl : IsList P := tele_isList (gen_data_tele (spec_to_minimal hW hP) rfl).choose_spec.2
    have hPlen : P.toList.length = D.params.length := by
      have := data_len_of hW (⟨_, .inl hP⟩ : IsTyK S (K + 1) (.data d P)); rwa [hdD] at this
    have eY : (y.subst κ.up.τ).subst κ'.up.τ = y.subst (κ.comp κ').up.τ := by rw [← I_subst_comp, ISub.up_comp]
    have eψ : (ψ.subst κ.τ).subst κ'.τ = ψ.subst (κ.comp κ').τ := (I_subst_comp ψ κ κ').symm
    have eT : ((ρ.comp σ).comp κ).comp κ' = (ρ.comp σ).comp (κ.comp κ') := ISub.comp_assoc _ _ _
    have ex : (x.isub (σ.comp κ)).isub κ' = x.isub (σ.comp (κ.comp κ')) := by rw [Tm.isub_isub, ISub.comp_assoc]
    have eLine : (P.isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).isub κ'.up =
        P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
          ((ρ.comp σ).comp (κ.comp κ')).up.tail) := by
      rw [line_isub_up]; congr 2 <;> simp only [eY, eT]
    -- the line at the points of a restriction
    have hLpt : ∀ {k6 : ℕ} (κ3 : ISub k6 k3) (r : I) (hr0 : r.Scoped k6),
        ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).isub (ISub.cons r hr0 κ3) =
          ((Tm.data d P).isub (ISub.cons (y.subst κ3.up.τ) (I.scoped_subst hy κ3.up.sc) ((ρ.comp σ).comp κ3).up.tail)).dinst r := by
      intro k6 κ3 r hr0
      rw [← isub_up_dinst _ κ3 r hr0, line_isub_up]
    have hXL : ∀ {k6 : ℕ} (θ : ISub k6 (K + 1)), TyCode k6 (semK S k6 (.data d (P.isub θ))) := fun θ =>
      tyCode_of_univ hW (HasTy.isubS hW hP θ)
    -- the start and the end of the line where the face holds
    have hconst : ∀ {k6 : ℕ} (κ3 : ISub k6 k3), I.Entails .one (ψ.subst κ3.τ) →
        RT2 S k6 (((Tm.data d P).isub (ISub.cons (y.subst κ3.up.τ) (I.scoped_subst hy κ3.up.sc) ((ρ.comp σ).comp κ3).up.tail)).dinst .zero)
          (((Tm.data d P).isub (ISub.cons (y.subst κ3.up.τ) (I.scoped_subst hy κ3.up.sc) ((ρ.comp σ).comp κ3).up.tail)).dinst .one) := by
      intro k6 κ3 hf3
      have c1 := LC k6 κ3 .one trivial ((holds_iff_entails (I.scoped_subst hψs κ3.sc)).2 hf3)
      rw [hLpt, hLpt, hPend κ3 .one trivial, hPend κ3 .zero trivial] at c1
      rw [hPend κ3 .zero trivial, hPend κ3 .one trivial]
      exact RT2.symm hW (hXL _) c1
    rw [eL (κ.comp κ') .one]
    dsimp only
    by_cases hf : I.Entails .one (ψ.subst κ.τ)
    · -- the face holds: the bases
      have hf2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := by rw [← eψ]; exact ent_one_subst hf _
      have hf2' : I.Entails .one (ψ'.subst (κ.comp κ').τ) := ent_trans hf2 (ent_subst h12 _)
      rw [if_pos hf, if_pos hf2', ex]
      have h := hb (κ.comp κ')
      rw [← hPend (κ.comp κ') .zero trivial] at h
      exact RE2.conv hW (hconst _ hf2) h
    -- the face does not hold: the left reduct, restricted
    -- the face does not hold: the left reduct, restricted
    have hPLl : ∀ {k6 : ℕ} (θ : ISub k6 (K + 1)), IsList (P.isub θ) := fun θ => isList_subst hPl _ _
    have hPLlen : ∀ {k6 : ℕ} (θ : ISub k6 (K + 1)), (P.isub θ).toList.length = D.params.length := fun θ => by
      show (P.subst Tm.var θ.τ).toList.length = _
      rw [toList_subst hPl]; simp [hPlen]
    rw [if_neg hf, tRedF_isub hW hD (hPLl _) (hPLlen _) (hWF k4 κ) κ', eLine, eψ]
    have hPθ2 := HasTy.isubS hW hP (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
      ((ρ.comp σ).comp (κ.comp κ')).up.tail)
    -- the restricted normal form of the left base, against the left base at the restriction
    have R0 : RE2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero) ((W k4 κ).isub κ') (x.isub (σ.comp (κ.comp κ'))) := by
      have r0 := RE2.isub hW (hWx k4 κ) κ'
      rw [ex] at r0
      rw [show (Tm.data d (P.isub (ISub.cons ((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ)
          (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) ((ρ.comp σ).comp κ)))).isub κ' =
          .data d (P.isub (ISub.cons (((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ).subst κ'.τ)
            (I.scoped_subst (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) κ'.sc)
            ((ρ.comp σ).comp (κ.comp κ')))) by
        show Tm.data d ((P.isub _).isub _) = _; rw [Tm.isub_isub, ISub.cons_comp, eT]] at r0
      rw [hPend (κ.comp κ') .zero trivial]
      refine RE2.conv hW (hRL k5 _ _ _ _ _ ?_) r0
      exact I_eq_trans (I_eq_subst (ieq_zero_up h0 κ) κ'.τ) (I_eq_symm (ieq_zero_up h0 (κ.comp κ')))
    have hA0 : RT2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero)
        (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero) := by
      rw [hPend (κ.comp κ') .zero trivial]; exact hRL k5 _ _ _ _ _ (I_eq_refl _)
    have LC2 : LineConst S k5 (.data d (P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail))) (ψ.subst (κ.comp κ').τ) := by
      have := LineConst.isub LC (κ.comp κ'); rwa [line_isub_up] at this
    have eA : ∀ (σ2 : ISub k5 k1), (Tm.data d ((P.dinst .zero).isub ρ)).isub σ2 = Tm.data d ((P.dinst .zero).isub (ρ.comp σ2)) :=
      fun σ2 => by show Tm.data d (((P.dinst .zero).isub ρ).isub σ2) = _; rw [Tm.isub_isub]
    have eT3 : (ρ.comp σ).comp (κ.comp κ') = ρ.comp (σ.comp (κ.comp κ')) := ISub.comp_assoc _ _ _
    -- the start of the line, against the type of the bases
    have hAeq : TyEq S k5 (.data d (P.isub (ISub.cons ((y.subst (κ.comp κ').up.τ).subst (ISub.cons .zero trivial (ISub.id k5)).τ)
        (I.scoped_subst (I.scoped_subst hy (κ.comp κ').up.sc) (ISub.cons .zero trivial (ISub.id k5)).sc)
        ((ρ.comp σ).comp (κ.comp κ')))))
        ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp (κ.comp κ'))) := by
      rw [eA, P0_isub hW hD hp hP  hRL, ← eT3]
      exact tyB (hRL k5 _ _ _ _ _ (ieq_zero_up h0 (κ.comp κ')))
    have hA1 : RT2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .one)
        (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .one) := by
      rw [hPend (κ.comp κ') .one trivial]; exact hRL k5 _ _ _ _ _ (I_eq_refl _)
    -- the normal form of the restricted normal form
    have R0P := R0
    rw [hPend (κ.comp κ') .zero trivial] at R0P
    obtain ⟨V, hVr, hVF, hVV, hVW⟩ := whnf_data hW hD hH hyp hP hPP1 _ R0P
    -- the typings at the further restriction
    have e0 := (RE2.typed R0).2.2.symm
    have rb := transp_rebase hW (htyκ (κ.comp κ')) e0
    have LCm := LC2
    have htyA := rb.1
    have htyB := htyκ (κ.comp κ')
    have htyB' := htyκ' (κ.comp κ')
    have heqAB := rb.2.symm
    have heqm := heqκ (κ.comp κ')
    rw [eT3] at LCm htyA htyB htyB' heqAB heqm
    -- (R2) the contracta of the normal form of the restricted normal form and of the base
    have T2 := (ihc k4 (σ.comp κ) (W k4 κ) (hWr k4 κ).1 k5 κ').1
    rw [ISub.comp_assoc σ κ κ'] at T2
    have R2 := T2 (ρ.comp (σ.comp (κ.comp κ'))) (by simp only [ISub.hom_comp]) (eA _) P hRL _ _
      (I.scoped_subst hy (κ.comp κ').up.sc) (I.scoped_subst hy (κ.comp κ').up.sc) (I_eq_refl _) (ieq_zero_up h0 (κ.comp κ'))
      (ψ.subst (κ.comp κ').τ) (ψ.subst (κ.comp κ').τ) (I.scoped_subst hψs (κ.comp κ').sc) (ent_refl _) (ent_refl _) LCm
      htyA htyB heqAB V (W k5 (κ.comp κ')) ⟨hVr.1, hVr.2.tyConv hAeq⟩
      ⟨(hWr k5 (κ.comp κ')).1, (hWr k5 (κ.comp κ')).2.tyConv hAeq⟩
    -- (R3) the contracta of the bases at the further restriction
    have R3 := (ih k5 (σ.comp (κ.comp κ'))).1 (ρ.comp (σ.comp (κ.comp κ'))) (by simp only [ISub.hom_comp]) (eA _) Q hQ _ _
      (I.scoped_subst hy (κ.comp κ').up.sc) (I.scoped_subst hy' (κ.comp κ').up.sc) (I_eq_subst hE _)
      (ieq_zero_up h0 (κ.comp κ')) (ψ.subst (κ.comp κ').τ) (ψ'.subst (κ.comp κ').τ) (I.scoped_subst hψs (κ.comp κ').sc)
      (ent_subst h12 _) (ent_subst h21 _) LCm htyB htyB' heqm (W k5 (κ.comp κ')) (W' k5 (κ.comp κ'))
      ⟨(hWr k5 (κ.comp κ')).1, (hWr k5 (κ.comp κ')).2.tyConv hAeq⟩
      ⟨(hWr' k5 (κ.comp κ')).1, (hWr' k5 (κ.comp κ')).2.tyConv hAeq⟩
    rw [← eT3] at R2 R3
    -- the node at κ
    have hnode := DR2.at_id hW (Θ := ΘK S D d (K + 1) P) ((RE2_dataLit_iff hW hD hP _).1 (hb κ)).2
    have eA4 : (Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp κ) = Tm.data d ((P.dinst .zero).isub (ρ.comp (σ.comp κ))) := by
      show Tm.data d (((P.dinst .zero).isub ρ).isub _) = _; rw [Tm.isub_isub]
    have hAκ : TyEq S k4 (.data d (P.isub (ISub.cons ((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ)
        (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) ((ρ.comp σ).comp κ))))
        ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp κ)) := by
      rw [eA4, P0_isub hW hD hp hP  hRL, ← ISub.comp_assoc]
      exact tyB (hRL k4 _ _ _ _ _ (ieq_zero_up h0 κ))
    have hRT : RedT S k4 ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp κ))
        (.data d ((P.dinst .zero).isub (ρ.comp (σ.comp κ)))) := by
      rw [eA4]; exact ⟨redW_self (step_data d _), TyEq.refl _⟩
    have LCκ : LineConst S k4 ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc)
        ((ρ.comp σ).comp κ).up.tail)) (ψ.subst κ.τ) := by
      have := LineConst.isub LC κ; rwa [line_isub_up] at this
    rcases hWF k4 κ with ⟨c, C, q, Z, rs, hC, hWe, hZl, hfb⟩ | ⟨qs, χ, u, a, hWe, hχ⟩
    · -- a constructor
      rcases DR2At_cases hW hD hP hPP1 _ hnode with
        ⟨c0, C0, q0, Z0, rs0, q0', Z0', rs0', hC0, hZ0l, hZ0'l, hr0, hr0', hrs0l, -, -, -, -, hZ0⟩ |
        ⟨_, _, _, _, _, _, _, _, -, hr0, -⟩
      swap
      · have := RedW.unique hr0.1 (hWr k4 κ).1; rw [hWe] at this; cases this
      have e1 := RedW.unique (hWr k4 κ).1 hr0.1
      rw [hWe] at e1
      simp only [Tm.con.injEq] at e1
      obtain ⟨-, rfl, rfl, eZ, rfl⟩ := e1
      have eZ1 := congrArg Tm.toList eZ
      simp only [toList_ofList] at eZ1
      subst eZ1
      rw [hC] at hC0; cases hC0
      -- the transports of the recursive arguments, with themselves
      have hch := ((ih k4 (σ.comp κ)).2 _ hRT).1 c C q Z rs q0' Z0' rs0' hC ⟨hr0.1, hr0.2.tyConv hAκ⟩
        ⟨hr0'.1, hr0'.2.tyConv hAκ⟩
      -- the data of the transport of the normal form at κ, and at κκ'
      have hZs : ∀ i (hi : i < C.args.length), RE2 S k4 ((C.argTy d D.params.length i).substList ((Z.take i).reverse ++
          ((P.isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .zero).toList.reverse))
          (Z.getD i .abort) (Z.getD i .abort) := by
        rw [line_dinst hW hD hp hP  hRL _ _ _ .zero trivial]
        exact fun i hi => (args_self hW hD hP hPP1 _ hC hZl hZ0'l hZ0 i hi).2.1
      have htcon : HasTy S k4 .one [] (.transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc)
          ((ρ.comp σ).comp κ).up.tail)) (ψ.subst κ.τ) (.con d c q (Tm.ofList Z) rs))
          (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .one) := by
        have eb := (hWr k4 κ).2
        rw [hWe, ← hPend κ .zero trivial] at eb
        exact (transp_rebase hW (htyκ κ) eb).1
      have TCκ := tc_node hW hD hH hp hP  hRL hyp ((ρ.comp σ).comp κ) (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc)
        (ieq_zero_up h0 κ) (I.scoped_subst hψs κ.sc) LCκ hC hZl htcon hZs (fun j hj hrj => by
          have := (hch j hj (by omega) hrj).2.1
          rwa [← ISub.hom_comp, ← ISub.comp_assoc] at this)
      have TCκκ' := TCκ.isubH hH hyp (forall2_ieq_refl rs) κ'
      rw [eLine, eψ] at TCκκ'
      rw [hWe, isub_conT, tRedF_con d D _ _ hC]
      rw [hWe, isub_conT] at R0 hVr hVW
      by_cases hf2' : I.Entails .one (ψ'.subst (κ.comp κ').τ)
      · -- the face holds at the further restriction
        rw [if_pos hf2']
        have hf2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := ent_trans hf2' (ent_subst h21 _)
        have FACE := TCκκ'.tcon_faceH hH hyp hf2
        have hc := hconst (κ.comp κ') hf2
        have R0' := RE2.conv hW hc R0
        have hb2 := hb (κ.comp κ')
        rw [← hPend (κ.comp κ') .zero trivial] at hb2
        have hb2' := RE2.conv hW hc hb2
        have hA1' := RT2.refl' hW (RE2.tyCode hW R0) hc
        exact RE2.trans hW hA1' FACE (RE2.trans hW hA1' R0' hb2')
      · -- the face does not hold at the further restriction
        rw [if_neg hf2']
        have hf2n : ¬ I.Entails .one (ψ.subst (κ.comp κ').τ) := fun h => hf2' (ent_trans h (ent_subst h12 _))
        -- (R1) the contractum of the restricted normal form, against that of its normal form
        have R1 : RE2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
            ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .one)
            (tConR d D c C (P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
              ((ρ.comp σ).comp (κ.comp κ')).up.tail)) (ψ.subst (κ.comp κ').τ) (Z.map (·.isub κ')) (rs.map (·.subst κ'.τ)))
            (tRedF d D (P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
              ((ρ.comp σ).comp (κ.comp κ')).up.tail)) (ψ.subst (κ.comp κ').τ) V) := by
          cases hfb' : firstBnd C.bnd (rs.map (·.subst κ'.τ)) with
          | none =>
            obtain rfl := RedW.unique hVr.1 (redW_self (step_con_none hD hC _ _ hfb'))
            rw [tRedF_con d D _ _ hC] at R2 ⊢
            exact RE2.trans hW hA1 R2 (RE2.symm hW hA1 R2)
          | some b =>
            obtain ⟨kb, ψb, hbb, hent⟩ := firstBnd_spec hfb'
            obtain ⟨-, hbc, hsimple, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψb b hbb
            have hrsl' : (rs.map (·.subst κ'.τ)).length = C.dims := by simp [hrs0l]
            have BIb : BI S d D c C (rs.map (·.subst κ'.τ)) b := fun {_} => BI_top hW hD hH hyp hC hrsl' hbb hent
            obtain ⟨-, ⟨-, -, -, hbc0⟩, -⟩ := gen_transpF (spec_to_minimal hW TCκκ'.hty) rfl
            have hcκ := minimal_to_spec hbc0
            have hd0κ : HasTy S k5 .one [] (.data d ((P.isub (ISub.cons (y.subst (κ.comp κ').up.τ)
                (I.scoped_subst hy (κ.comp κ').up.sc) ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero)) (.univ D.level) := by
              rw [line_dinst hW hD hp hP  hRL _ _ _ .zero trivial]; exact HasTy.isubS hW hP _
            have hqL := (con_inv hW hD hC hcκ hd0κ).2.2.2.2.2.2.2.2.1
            have econ := EqTm.conBnd hD hC hbb hent hqL (by rw [toList_ofList]) hcκ
            rw [toList_ofList] at econ
            have htyb := (transp_rebase hW TCκκ'.hty econ).1
            have BTr := bnd_transp hW hD hH hyp c C hC b hsimple hbc TCκκ' BIb htyb
            obtain ⟨hcO, hO⟩ := TCκκ'.outs_inst
            obtain ⟨hd1, s1, -, -, -⟩ := TCκκ'.end_data
            have CB := hyp.conBnd (by omega) hD hH hC hbb hent hd1 s1 (tOuts_length _ _ _ _ _ _) hcO hO
            have TT := RE2.trans hW s1 CB (RE2.symm hW s1 BTr)
            -- the transport of the boundary term against the contractum of its normal form
            have s2 : step S (.con d c (q.isub κ') (Tm.ofList (Z.map (·.isub κ'))) (rs.map (·.subst κ'.τ))) =
                some (Ctor.bndAt b (q.isub κ').toList (Z.map (·.isub κ')) (rs.map (·.subst κ'.τ))) := by
              rw [step_con_some hD hC _ _ hfb', toList_ofList]
            have hRb := red_redW (.step s2 (.refl _)) hVr.1
            have eV := econ.symm.trans (hVr.2.tyConv (by rw [← hPend (κ.comp κ') .zero trivial]; exact TyEq.refl _))
            obtain ⟨rV, eVt, wV⟩ := tred_red hW hD hp hH hf2n hVF hRb htyb eV
            have selfT := RE2.trans hW s1 BTr (RE2.symm hW s1 BTr)
            have selfV := RE2.trans hW hA1 R2 (RE2.symm hW hA1 R2)
            have RW := RE2_whnf hW hD hP hPP1 (ISub.cons ((y.subst (κ.comp κ').up.τ).subst (ISub.cons .one trivial (ISub.id k5)).τ)
              (I.scoped_subst (I.scoped_subst hy (κ.comp κ').up.sc) (ISub.cons .one trivial (ISub.id k5)).sc)
              ((ρ.comp σ).comp (κ.comp κ'))) (by rw [← hPend (κ.comp κ') .one trivial]; exact selfT)
              (by rw [← hPend (κ.comp κ') .one trivial]; exact ⟨⟨rV, wV⟩, eVt⟩)
              (by rw [← hPend (κ.comp κ') .one trivial]; exact selfV)
            rw [← hPend (κ.comp κ') .one trivial] at RW
            exact RE2.trans hW hA1 TT (RE2.symm hW hA1 RW)
        exact RE2.trans hW hA1 R1 (RE2.trans hW hA1 R2 R3)
    · -- a composition
      rcases DR2At_cases hW hD hP hPP1 _ hnode with
        ⟨_, _, _, _, _, _, _, _, -, -, -, hr0, -⟩ |
        ⟨qs0, χ0, u0, a0, qs0', χ0', u0', a0', -, hr0, hr0', -, -, -, -, haa0, hu0⟩
      · have := RedW.unique hr0.1 (hWr k4 κ).1; rw [hWe] at this; cases this
      have e1 := RedW.unique (hWr k4 κ).1 hr0.1
      rw [hWe] at e1
      simp only [Tm.hcomp.injEq] at e1
      obtain ⟨-, rfl, rfl, rfl⟩ := e1
      have eWκ : (W k4 κ).isub κ' = .hcomp (.data d (qs.isub κ')) (χ.subst κ'.τ) (u.isub κ'.up) (a.isub κ') := by
        rw [hWe]; rfl
      rw [eWκ, tRedF_hcomp]
      rw [eWκ] at R0 hVr hVW rb
      by_cases hf2' : I.Entails .one (ψ'.subst (κ.comp κ').τ)
      · -- the face holds at the further restriction
        rw [if_pos hf2']
        have hf2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := ent_trans hf2' (ent_subst h21 _)
        have hTl : ∀ {k6 : ℕ} (θ : ISub k6 (K + 1)), RT2 S k6 (.data d (P.isub θ)) (.data d (P.isub θ)) :=
          fun θ => RT2.isub hW (tyCode_of_univ hW hP) hPP1 θ
        have hU : ∀ k6 (σ' : ISub k6 k5) (r : I), r.Scoped k6 → (ival (idEnv k6) ((χ.subst κ'.τ).subst σ'.τ)).holds →
            RE2 S k6 ((((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
              ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero).isub σ')
              (((u.isub κ'.up).isub σ'.up).dinst r) (((u.isub κ'.up).isub σ'.up).dinst r) := by
          intro k6 σ' r hr0 hh
          rw [← I_subst_comp] at hh
          have h1 := hu0 k6 (κ'.comp σ') r hr0 hh
          have hs1 := RE2.trans hW (hTl _) h1 (RE2.symm hW (hTl _) h1)
          rw [Tm.isub_isub, ← ISub.up_comp, isub_dinst, show I.subst σ'.τ I.zero = I.zero from rfl, line_isub_up,
            lineP_dinst hW hD hp hP  hRL _ _ _ .zero trivial]
          rw [ISub.cons_comp] at hs1
          simp only [ISub.comp_assoc] at hs1 ⊢
          refine RE2.conv hW (hRL k6 _ _ _ _ _ ?_) hs1
          exact I_eq_trans (I_eq_subst (ieq_zero_up h0 κ) _) (I_eq_symm (ieq_zero_up (ieq_zero_up h0 (κ.comp κ')) σ'))
        have hA : RE2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
            ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero) (a.isub κ') (a.isub κ') := by
          have hs1 := RE2.isub hW (RE2.trans hW (hTl _) haa0 (RE2.symm hW (hTl _) haa0)) κ'
          rw [show (Tm.data d (P.isub (ISub.cons ((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ)
              (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) ((ρ.comp σ).comp κ)))).isub κ' =
              .data d (P.isub (ISub.cons (((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ).subst κ'.τ)
                (I.scoped_subst (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) κ'.sc)
                ((ρ.comp σ).comp (κ.comp κ')))) by
            show Tm.data d ((P.isub _).isub _) = _; rw [Tm.isub_isub, ISub.cons_comp, eT]] at hs1
          rw [hPend (κ.comp κ') .zero trivial]
          refine RE2.conv hW (hRL k5 _ _ _ _ _ ?_) hs1
          exact I_eq_trans (I_eq_subst (ieq_zero_up h0 κ) κ'.τ) (I_eq_symm (ieq_zero_up h0 (κ.comp κ')))
        have FACE := hcomp_faceH hW hD hH hp hP  hRL ((ρ.comp σ).comp (κ.comp κ')) (y.subst (κ.comp κ').up.τ)
          (I.scoped_subst hy (κ.comp κ').up.sc) (I.scoped_subst hψs (κ.comp κ').sc) hf2 LC2 rb.1 hU hA
        have hc := hconst (κ.comp κ') hf2
        have R0' := RE2.conv hW hc R0
        have hb2 := hb (κ.comp κ')
        rw [← hPend (κ.comp κ') .zero trivial] at hb2
        have hb2' := RE2.conv hW hc hb2
        have hA1' := RT2.refl' hW (RE2.tyCode hW R0) hc
        exact RE2.trans hW hA1' FACE (RE2.trans hW hA1' R0' hb2')
      · -- the face does not hold at the further restriction
        rw [if_neg hf2']
        have hf2n : ¬ I.Entails .one (ψ.subst (κ.comp κ').τ) := fun h => hf2' (ent_trans h (ent_subst h12 _))
        have R1 : RE2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
            ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .one)
            (tHc d (P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
              ((ρ.comp σ).comp (κ.comp κ')).up.tail)) (ψ.subst (κ.comp κ').τ) (χ.subst κ'.τ) (u.isub κ'.up) (a.isub κ'))
            (tRedF d D (P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
              ((ρ.comp σ).comp (κ.comp κ')).up.tail)) (ψ.subst (κ.comp κ').τ) V) := by
          by_cases hχ' : I.Entails .one (χ.subst κ'.τ)
          · -- the composition's face holds: the end of its tube
            have hd0κ : HasTy S k5 .one [] (.data d ((P.isub (ISub.cons (y.subst (κ.comp κ').up.τ)
                (I.scoped_subst hy (κ.comp κ').up.sc) ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero)) (.univ D.level) := by
              rw [line_dinst hW hD hp hP  hRL _ _ _ .zero trivial]; exact HasTy.isubS hW hP _
            have hb0 := (hcomp_data_retype hW ((RE2.typed R0).1 : HasTy S k5 .one [] _
              (.data d ((P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
                ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero))) hd0κ).1
            have eH := transpHcomp_eq (D := D) hD hp hH hb0 rb.1
            have htyH : HasTy S k5 .one [] (.hcomp _ (χ.subst κ'.τ) _ _) _ := HasTy.eqR eH
            have hst := stable_hcompFace hW hχ' htyH
            rw [transp_skip_dinst] at hst
            have hχs1 : (χ.subst κ'.τ).Scoped k5 := (gen_hcomp (spec_to_minimal hW htyH) rfl).choose_spec.1.2.1
            have hh : (ival (idEnv k5) (χ.subst κ'.τ)).holds := (holds_iff_entails hχs1).2 hχ'
            have htyT := hcomp_tube_typed' hW htyH .one trivial hh
            rw [transp_skip_dinst] at htyT
            have hRWu : RedW S ((u.isub κ'.up).dinst .one) V := red_redW (.step (step_hcomp_face hχ') (.refl _)) hVr.1
            have huc : ((u.isub κ'.up).dinst .one).closedB 0 k5 = true :=
              closed_ty (gen_transpF (spec_to_minimal hW htyT) rfl).choose_spec.1.2.2.2
            have TRt := ((((ih k4 (σ.comp κ)).2 _ hRT).2 qs0 χ u a qs0' χ0' u0' a0' ⟨hr0.1, hr0.2.tyConv hAκ⟩
              ⟨hr0'.1, hr0'.2.tyConv hAκ⟩).2 k5 κ' .one trivial hh).2.2
            have T1 := TRt (ρ.comp (σ.comp (κ.comp κ'))) (by simp only [ISub.hom_comp, Hom.comp_assoc])
              (by show Tm.data d (((P.dinst .zero).isub _).isub κ') = _; rw [Tm.isub_isub, ISub.comp_assoc, ISub.comp_assoc])
              k5 (ISub.id k5) (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc) (ieq_zero_up h0 (κ.comp κ'))
              (ψ.subst (κ.comp κ').τ) (I.scoped_subst hψs (κ.comp κ').sc) hf2n (by rw [ISub.comp_id]; exact LCm)
              (by rw [ISub.comp_id, isub_id_of_closed huc, ← eT3]; exact htyT) V
              (by rw [isub_id_of_closed huc]; exact hRWu)
            rw [ISub.comp_id, isub_id_of_closed huc, ← eT3] at T1
            exact RE2.expandL hW hA1 htyH (RE2.typed R2).1 hst T1
          · -- the composition is normal
            obtain rfl := RedW.unique hVr.1 (redW_self (step_hcomp_HIT hD hH hχ'))
            rw [tRedF_hcomp] at R2
            exact RE2.trans hW hA1 R2 (RE2.symm hW hA1 R2)
        exact RE2.trans hW hA1 R1 (RE2.trans hW hA1 R2 R3)

/-- The intro case: the motive, from the contracta of the normal forms at all restrictions. -/
theorem tm1_introH {k1 : ℕ} {g : Hom k1 K} {A x x' : Tm}
    (hxx : ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d ((P.dinst .zero).isub ρ) → RE2 S k1 A x x')
    (ih : ∀ k' (σ : ISub k' k1), TM2H S d D K P k' (g.comp σ.hom) (A.isub σ) (x.isub σ) (x'.isub σ))
    (ihc : ∀ k' (σ : ISub k' k1) w, RedW S (x.isub σ) w → ∀ k'' (ρ' : ISub k'' k'),
      TM2H S d D K P k'' (g.comp (σ.comp ρ').hom) (A.isub (σ.comp ρ')) (w.isub ρ') (x.isub (σ.comp ρ'))) :
    TM1H S d D K P k1 g A x x' := by
  have T := tm1_mainH hW hD hH hyp hp hP  hRL ih ihc
  have hPP1 := PP1 hW hD hp hP  hRL
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the relation of the elements at a restriction, at the start of a line
  have hrel0 : ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d ((P.dinst .zero).isub ρ) → ∀ k3 (σ : ISub k3 k1) (y : I)
      (hy : y.Scoped (k3 + 1)), I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero →
      RE2 S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .zero) (x.isub σ) (x'.isub σ) := by
    intro ρ hg hAe k3 σ y hy h0
    have h := RE2.isub hW (hxx ρ hg hAe) σ
    rw [hAe, show (Tm.data d ((P.dinst .zero).isub ρ)).isub σ = .data d (P.isub (ISub.cons .zero trivial (ρ.comp σ))) by
      show Tm.data d (((P.dinst .zero).isub ρ).isub σ) = _
      rw [Tm.isub_isub, P0_isub hW hD hp hP  hRL]] at h
    rw [lineP_dinst hW hD hp hP  hRL _ _ _ .zero trivial]
    exact RE2.conv hW (hRL k3 _ _ _ _ _ (I_eq_symm h0)) h
  refine ⟨T, ?_, ?_⟩
  · -- the transports of the left element, along the lines at `I.Eq`-equal points
    intro ρ hg hAe k3 σ y y' hy hy' hE h0 hLR φ φ' hLC hty hty' heq h12 h21 hbase
    have h0' : I.Eq (y'.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero := I_eq_trans (I_eq_subst (I_eq_symm hE) _) h0
    have r0 := hrel0 ρ hg hAe k3 σ y hy h0
    have r0' := hrel0 ρ hg hAe k3 σ y' hy' h0'
    obtain ⟨_, ⟨hLt, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
    obtain ⟨_, ⟨hLt', hφs', -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
    have hcL := closed_ty hLt
    have hcL' := closed_ty hLt'
    have e11 : RT2 S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one)
        (((Tm.data d P).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)).dinst .one) := by
      have := hLR k3 (ISub.id k3) .one .one trivial trivial (I_eq_refl _)
      rwa [isub_cons_id_of_closed hcL, isub_cons_id_of_closed hcL'] at this
    have e00 : RT2 S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .zero)
        (((Tm.data d P).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)).dinst .zero) := by
      have := hLR k3 (ISub.id k3) .zero .zero trivial trivial (I_eq_refl _)
      rwa [isub_cons_id_of_closed hcL, isub_cons_id_of_closed hcL'] at this
    have eLL : TyEq S (k3 + 1) ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail))
        ((Tm.data d P).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) := by
      have := hLR (k3 + 1) (ISub.id k3).up.tail (.var 0) (.var 0) (show 0 < k3 + 1 by omega) (show 0 < k3 + 1 by omega)
        (I_eq_refl _)
      rw [ISub.cons_var0_up_tail, isub_up_id_of_closed hcL, isub_up_id_of_closed hcL'] at this
      exact tyB this
    have htyX' := transp_retarget hW (hty'.tyConv (tyB e11)) (RE2.typed r0').2.1
    have htyX'1 := htyX'.tyConv (TyEq.symm (tyB e11))
    have K1 := T ρ hg hAe P hRL k3 σ y y' hy hy' hE h0
    have R1 := K1 hLR φ φ' hLC hty htyX'1 (eqTm_transp_of hW hty htyX'1 eLL h12 h21 (RE2.typed r0).2.2) h12 h21 r0
    have K2 := T ρ hg hAe P hRL k3 σ y' y' hy' hy' (I_eq_refl _) h0'
    have hLR' : LineRob S k3 ((Tm.data d P).isub (ISub.cons y' hy' (ρ.comp σ).up.tail))
        ((Tm.data d P).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) :=
      fun k4 τ z z' hz hz' hEz => Rob.line hRL (ρ.comp σ) y' y' hy' hy' (I_eq_refl _) k4 τ z z' hz hz' hEz
    have hLC' := LineConst.transfer hW (minimal_to_spec hLt) (minimal_to_spec hLt') hφs hφs' h21 hLC hLR
    have hty'1 := hty'.tyConv (tyB e11)
    have htyX'2 := htyX'
    have R2 := K2 hLR' φ' φ' hLC' hty'1 htyX'2 (eqTm_transp_of hW hty'1 htyX'2 (TyEq.refl _) (ent_refl _) (ent_refl _)
      (RE2.typed r0').2.2) (ent_refl _) (ent_refl _) r0'
    have hX1 := RE2.tyCode hW R1
    have R2' := RE2.conv hW (RT2.symm hW hX1 e11) R2
    have hA1 := RT2.refl hW hX1 e11
    exact RE2.trans hW hA1 R1 (RE2.symm hW hA1 R2')
  · -- the transport of the left element, against the contractum of its normal form
    intro ρ hg hAe k3 σ y hy h0 ψ hψs hψ LC hty w hw
    have r0 := hrel0 ρ hg hAe k3 σ y hy h0
    have eL0 := lineP_dinst hW hD hp hP  hRL (ρ.comp σ) y hy .zero trivial
    have eL1 := lineP_dinst hW hD hp hP  hRL (ρ.comp σ) y hy .one trivial
    have r0P := r0
    rw [eL0] at r0P
    obtain ⟨W, hWr, hWF, -, -⟩ := whnf_data hW hD hH hyp hP hPP1 _ r0P
    obtain rfl := RedW.unique hw hWr.1
    have hTT := RT2.isub hW (tyCode_of_univ hW hP) hPP1 (ISub.cons (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ)
      (I.scoped_subst hy (ISub.cons .zero trivial (ISub.id k3)).sc) (ρ.comp σ))
    obtain ⟨W', hWr', -, -, -⟩ := whnf_data hW hD hH hyp hP hPP1 _ (RE2.symm hW hTT r0P)
    have eW : EqTm S k3 .one [] (x.isub σ) w (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .zero) := by
      rw [eL0]; exact hWr.2
    obtain ⟨rr, ee, ww⟩ := tred_red hW hD hp hH (PL := P.isub (ISub.cons y hy (ρ.comp σ).up.tail)) hψ hWF hw hty eW
    -- the transport, related to itself
    have htyX' := transp_retarget hW hty ((RE2.typed r0).2.1)
    have R := T ρ hg hAe P hRL k3 σ y y hy hy (I_eq_refl _) h0
      (fun k4 τ z z' hz hz' hEz => Rob.line hRL (ρ.comp σ) y y hy hy (I_eq_refl _) k4 τ z z' hz hz' hEz) ψ ψ LC hty htyX'
      (eqTm_transp_of hW hty htyX' (TyEq.refl _) (ent_refl _) (ent_refl _) (RE2.typed r0).2.2) (ent_refl _) (ent_refl _) r0
    have hA1 : RT2 S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one)
        (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one) := by
      rw [eL1]; exact hRL k3 _ _ _ _ _ (I_eq_refl _)
    have selfT := RE2.trans hW hA1 R (RE2.symm hW hA1 R)
    -- the contractum, related to itself
    have hAeq : TyEq S k3 (.data d (P.isub (ISub.cons (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ)
        (I.scoped_subst hy (ISub.cons .zero trivial (ISub.id k3)).sc) (ρ.comp σ)))) (A.isub σ) := by
      rw [hAe, show (Tm.data d ((P.dinst .zero).isub ρ)).isub σ = .data d (P.isub (ISub.cons .zero trivial (ρ.comp σ))) by
        show Tm.data d (((P.dinst .zero).isub ρ).isub σ) = _
        rw [Tm.isub_isub, P0_isub hW hD hp hP  hRL]]
      exact tyB (hRL k3 _ _ _ _ _ h0)
    have C := (ih k3 σ).1 (ρ.comp σ) (by rw [hg, ISub.hom_comp])
      (by rw [hAe]; show Tm.data d (((P.dinst .zero).isub ρ).isub σ) = _; rw [Tm.isub_isub]) P hRL y y hy hy (I_eq_refl _) h0
      ψ ψ hψs (ent_refl _) (ent_refl _) LC hty htyX'
      (eqTm_transp_of hW hty htyX' (TyEq.refl _) (ent_refl _) (ent_refl _) (RE2.typed r0).2.2) w W'
      ⟨hWr.1, hWr.2.tyConv hAeq⟩ ⟨hWr'.1, hWr'.2.tyConv hAeq⟩
    have selfC := RE2.trans hW hA1 C (RE2.symm hW hA1 C)
    have RW := RE2_whnf hW hD hP hPP1 (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k3)).τ)
      (I.scoped_subst hy (ISub.cons .one trivial (ISub.id k3)).sc) (ρ.comp σ)) (by rw [← eL1]; exact selfT)
      (by rw [← eL1]; exact ⟨⟨rr, ww⟩, ee⟩) (by rw [← eL1]; exact selfC)
    rw [← eL1] at RW
    exact RE2.symm hW hA1 RW

/-- Transport of related elements of the start of the line, by induction on their relation. -/
theorem transp_DR2H : ∀ {k1 : ℕ} {g : Hom k1 K} {A x x' : Tm},
    DR2 S d (dataD S d) (dataMem S (ΘK S D d K (P.dinst .zero)) (Hom.id K))
      (dataP2 S (ΘK S D d K (P.dinst .zero)) (Hom.id K)) k1 g A x x' →
    TM1H S d D K P k1 g A x x' := by
  have hP0 := P0_ty hW hD hp hP  hRL
  intro k1 g A x x' h
  refine DR2.rec (motive_1 := fun k1 g A x x' _ => TM1H S d D K P k1 g A x x')
    (motive_2 := fun k1 g A y y' _ => TM2H S d D K P k1 g A y y') ?_ ?_ ?_ h
  · intro k1 g A x x' he hst hc hc' ih ihc _
    refine tm1_introH hW hD hH hyp hp hP  hRL (fun ρ hg hAe => ?_) ih ihc
    subst hg hAe
    exact (RE2_dataLit_iff hW hD hP0 ρ).2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, .intro he hst hc hc'⟩
  · intro k1 g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec
    exact tm2_conH hW hD hH hyp hp hP  hRL
      (DR2At.con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt) hC hA ht ht' hrs hrs' hreq hl hl'
      ihrec
  · intro k1 g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH' hA hpl ht ht' hs hs' h12 h21 ha hu iha ihu
    exact tm2_hcompH hW hD hH hp hP  hRL
      (DR2At.hcomp hm hm' heq hH' hA hpl ht ht' hs hs' h12 h21 ha hu) hA ht ht' iha ihu

/-- Transport along a literal line of a higher inductive type, against a robustly related literal line. -/
theorem kanT2_litH {Q : Tm} (hQ : Rob S d K P Q) : KanT2 S K (.data d P) (.data d Q) := by
  intro hLR φ φ' a a' hLC hty hty' heq h12 h21 ha
  have hP0 := P0_ty hW hD hp hP  hRL
  have hP0c : (P.dinst .zero).closedB 0 K = true := data_closed hW hD hP0
  have hac := closed_of_ty hW (RE2.typed ha).1
  have hac' := closed_of_ty hW (RE2.typed ha).2.1
  have ha' : RE2 S K (.data d ((P.dinst .zero).isub (ISub.id K))) a a' := by
    rw [isub_id_of_closed hP0c]; exact ha
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP0 (ISub.id K)).1 ha'
  have T := (transp_DR2H hW hD hH hyp hp hP  hRL hdr).1 (ISub.id K) rfl rfl Q hQ K (ISub.id K) (.var 0) (.var 0)
    (show 0 < K + 1 by omega) (show 0 < K + 1 by omega) (I_eq_refl _) (I_eq_refl _)
  have hQc : (Tm.data d Q).closedB 0 (K + 1) = true := by
    obtain ⟨l', ⟨hLt', -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
    exact closed_ty hLt'
  rw [ISub.comp_id, ISub.cons_var0_up_tail, isub_up_id_of_closed (show (Tm.data d P).closedB 0 (K + 1) = true from
    closed_of_ty hW hP), isub_up_id_of_closed hQc, isub_id_of_closed hac, isub_id_of_closed hac'] at T
  exact T hLR φ φ' hLC hty hty' heq h12 h21 ha

end ind

end

end Model.Whnf
