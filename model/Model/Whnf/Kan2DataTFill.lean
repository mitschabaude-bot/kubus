import Model.Whnf.Kan2DataT0

/-!
# Transport fillers along related lines

The transport filler `transpFill L φ a` at a point `x` is a transport along the line `L(x ∧ j)`
(`transpFill_isub_cons`). Given transports of the bases along these lines (`KanT2At`), and robustness of
the lines in their variable, the fillers of related bases are related at all pairs of `I.Eq`-equal
points (`tfill_rel`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- Transport along related lines (at stage `k + 1`) relates the given related bases. -/
def KanT2At (S : Sig) (k : ℕ) (A A' a a' : Tm) : Prop :=
  LineRob S k A A' → ∀ (φ φ' : I), LineConst S k A φ → HasTy S k .one [] (.transp A φ a) (A.dinst .one) →
    HasTy S k .one [] (.transp A' φ' a') (A.dinst .one) →
    EqTm S k .one [] (.transp A φ a) (.transp A' φ' a') (A.dinst .one) → I.Entails φ φ' → I.Entails φ' φ →
    RE2 S k (A.dinst .zero) a a' → RE2 S k (A.dinst .one) (.transp A φ a) (.transp A' φ' a')

theorem KanT2.at {A A' : Tm} (h : KanT2 S k A A') (a a' : Tm) : KanT2At S k A A' a a' :=
  fun hLR φ φ' => h hLR φ φ' a a'

theorem KanT2.of_at {A A' : Tm} (h : ∀ a a', KanT2At S k A A' a a') : KanT2 S k A A' :=
  fun hLR φ φ' a a' => h a a' hLR φ φ'

theorem scoped_andShift {k3 : ℕ} {x : I} (hx : x.Scoped k3) : (I.and x.shift (.var 0)).Scoped (k3 + 1) :=
  ⟨KubusCore.I.scoped_shift hx, (show (0 : ℕ) < k3 + 1 by omega)⟩

/-- A transport filler at a point: a transport along the line `L(x ∧ j)`. -/
theorem transpFill_isub_cons (L : Tm) (φ : I) (a : Tm) {k3 : ℕ} (x : I) (hx : x.Scoped k3) (τ : ISub k3 k) :
    (Tm.transpFill L φ a).isub (ISub.cons x hx τ) =
      .transp (L.isub (ISub.cons (.and x.shift (.var 0)) (scoped_andShift hx) τ.up.tail))
        (.or (φ.subst τ.τ) (.neg x)) (a.isub τ) := by
  show Tm.transp ((L.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons x hx τ).up)
    ((I.or φ.shift (.neg (.var 0))).subst (ISub.cons x hx τ).τ) ((a.dshift).isub (ISub.cons x hx τ)) = _
  rw [isub_bindAnd, dshift_isub_cons]
  congr 1
  show I.or ((φ.shift).subst (ISub.cons x hx τ).τ) (.neg x) = _
  rw [I_shift_cons]

/-- A point of a restricted line. -/
theorem isub_line_pt (L : Tm) {k3 k4 : ℕ} (y : I) (hy : y.Scoped (k3 + 1)) (τ : ISub k3 k) (z : I) (hz : z.Scoped k4)
    (τ2 : ISub k4 k3) :
    (L.isub (ISub.cons y hy τ.up.tail)).isub (ISub.cons z hz τ2) =
      L.isub (ISub.cons (y.subst (ISub.cons z hz τ2).τ) (I.scoped_subst hy (ISub.cons z hz τ2).sc) (τ.comp τ2)) := by
  rw [Tm.isub_isub, ISub.cons_comp, ISub.up_tail_comp_cons]

/-- An endpoint of a restricted line. -/
theorem dinst_line {L : Tm} {n k3 : ℕ} (y : I) (hy : y.Scoped (k3 + 1)) (τ : ISub k3 k)
    (hc : (L.isub (ISub.cons y hy τ.up.tail)).closedB n (k3 + 1) = true) (r : I) (hr : r.Scoped k3) :
    (L.isub (ISub.cons y hy τ.up.tail)).dinst r =
      L.isub (ISub.cons (y.subst (ISub.cons r hr (ISub.id k3)).τ) (I.scoped_subst hy (ISub.cons r hr (ISub.id k3)).sc) τ) := by
  rw [← isub_cons_id_of_closed hc r hr, isub_line_pt, ISub.comp_id]

theorem andShift_subst {k3 k4 : ℕ} (x : I) (z : I) (hz : z.Scoped k4) (τ2 : ISub k4 k3) :
    (I.and x.shift (.var 0)).subst (ISub.cons z hz τ2).τ = I.and (x.subst τ2.τ) z := by
  show I.and (x.shift.subst (ISub.cons z hz τ2).τ) z = _
  rw [I_shift_cons]

theorem ieq_and_zero_left' {a : I} (b : I) (h : I.Eq a .zero) : I.Eq (I.and b a) .zero := fun ρ0 => by
  simp only [I.eval]; rw [h ρ0]; cases b.eval ρ0 <;> rfl

variable (hW : WfSig S)
include hW

/-- Transport fillers of related bases along related lines are related, at `I.Eq`-equal points. -/
theorem tfill_rel {L L' a a' : Tm} {φ φ' : I} {l : ℕ} (hL : HasTy S (k + 1) .one [] L (.univ l))
    (hφs : φ.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hR : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (L.isub (ISub.cons y hy τ)) (L'.isub (ISub.cons y' hy' τ)))
    (hRL : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (L.isub (ISub.cons y hy τ)) (L.isub (ISub.cons y' hy' τ)))
    (hLC : LineConst S k L φ)
    (hT : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
      KanT2At S k3 (L.isub (ISub.cons y hy τ.up.tail)) (L'.isub (ISub.cons y' hy' τ.up.tail)) (a.isub τ) (a'.isub τ))
    (htyF : HasTy S (k + 1) .one [] (Tm.transpFill L φ a) L)
    (htyF' : HasTy S (k + 1) .one [] (Tm.transpFill L' φ' a') L')
    (ha : RE2 S k (L.dinst .zero) a a') :
    ∀ k3 (σ σ' : ISub k3 (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k3 (L.isub σ) ((Tm.transpFill L φ a).isub σ) ((Tm.transpFill L' φ' a').isub σ') := by
  intro k3 σ σ' et e0
  have hLc : L.closedB 0 (k + 1) = true := closed_ty (spec_to_minimal hW hL)
  have hXL : ∀ {k4 : ℕ} (θ : ISub k4 (k + 1)), TyCode k4 (semK S k4 (L.isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW hL θ)
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the points
  obtain ⟨x, hx, τ, rfl⟩ : ∃ x hx τ, σ = ISub.cons x hx τ := ⟨_, _, _, (ISub.cons_tail σ).symm⟩
  obtain ⟨x', hx', τ', rfl⟩ : ∃ x hx τ, σ' = ISub.cons x hx τ := ⟨_, _, _, (ISub.cons_tail σ').symm⟩
  obtain rfl : τ = τ' := et
  change I.Eq x x' at e0
  rw [transpFill_isub_cons, transpFill_isub_cons]
  have hyx := scoped_andShift hx
  have hyx' := scoped_andShift hx'
  have hEy : I.Eq (I.and x.shift (.var 0)) (I.and x'.shift (.var 0)) :=
    ieq_and_congr (fun ρ0 => by simp only [I.shift, eval_ren]; exact e0 _) (I_eq_refl _)
  have K := hT k3 τ _ _ hyx hyx' hEy
  -- robustness of the restricted lines
  have LR : LineRob S k3 (L.isub (ISub.cons _ hyx τ.up.tail)) (L'.isub (ISub.cons _ hyx' τ.up.tail)) := by
    intro k4 τ2 z z' hz hz' hEz
    rw [isub_line_pt, isub_line_pt]
    refine hR k4 (τ.comp τ2) _ _ _ _ ?_
    rw [andShift_subst, andShift_subst]
    exact ieq_and_congr (I_eq_subst e0 _) hEz
  -- constancy of the restricted line on the face of the filler
  have hψs : (I.or (φ.subst τ.τ) (.neg x)).Scoped k3 := ⟨I.scoped_subst hφs τ.sc, hx⟩
  have LC : LineConst S k3 (L.isub (ISub.cons _ hyx τ.up.tail)) (.or (φ.subst τ.τ) (.neg x)) := by
    intro k4 τ2 z hz hh
    rw [isub_line_pt, isub_line_pt]
    have he := (holds_iff_entails (I.scoped_subst hψs τ2.sc)).1 hh
    rcases ent_or_cases (I.scoped_subst hψs.1 τ2.sc) (I.scoped_subst (show (I.neg x).Scoped k3 from hx) τ2.sc) he
      with hφ2 | hx2
    · have hh2 : (ival (idEnv k4) (φ.subst (τ.comp τ2).τ)).holds :=
        (holds_iff_entails (I.scoped_subst hφs (τ.comp τ2).sc)).2 (ent_comp_inv hφ2)
      have gz := hLC k4 (τ.comp τ2) _ (I.scoped_subst hyx (ISub.cons z hz τ2).sc) hh2
      have g0 := hLC k4 (τ.comp τ2) _ (I.scoped_subst hyx (ISub.cons .zero trivial τ2).sc) hh2
      exact RT2.trans hW (hXL _) gz (RT2.symm hW (hXL _) g0)
    · have e1 : I.Eq (x.subst τ2.τ) .zero :=
        ieq_zero_of_holds_neg (I.scoped_subst hx τ2.sc) (entails_holds hx2 (ρ := idEnv k4) (by rw [ival_one]; rfl))
      refine hRL k4 (τ.comp τ2) _ _ _ _ ?_
      rw [andShift_subst, andShift_subst]
      exact I_eq_trans (ieq_and_zero_left _ e1) (I_eq_symm (ieq_and_zero_left _ e1))
  -- the endpoints of the restricted lines
  have end1 : ∀ {M : Tm} {z : I} (hz : z.Scoped k3) (hyz : (I.and z.shift (.var 0)).Scoped (k3 + 1))
      (hM : (M.isub (ISub.cons _ hyz τ.up.tail)).closedB 0 (k3 + 1) = true) (r : I) (hr : r.Scoped k3),
      (M.isub (ISub.cons _ hyz τ.up.tail)).dinst r =
        M.isub (ISub.cons (I.and z r) (show (I.and z r).Scoped k3 from ⟨hz, hr⟩) τ) := by
    intro M z hz hyz hM r hr
    rw [dinst_line _ _ _ hM]
    congr 1
    ext i
    rcases i with _ | i
    · show (I.and z.shift (.var 0)).subst (ISub.cons r hr (ISub.id k3)).τ = I.and z r
      rw [andShift_subst, I_subst_id hz]
    · rfl
  have cL : (L.isub (ISub.cons _ hyx τ.up.tail)).closedB 0 (k3 + 1) = true :=
    closed_ty (spec_to_minimal hW (HasTy.isubS hW hL _))
  have rLL' := hR (k3 + 1) τ.up.tail _ _ hyx hyx' hEy
  have cL' : (L'.isub (ISub.cons _ hyx' τ.up.tail)).closedB 0 (k3 + 1) = true :=
    closed_of_isTyK hW (Comp2_ty_base rLL').2.2.1
  -- typings
  have hty1 : HasTy S k3 .one [] (.transp (L.isub (ISub.cons _ hyx τ.up.tail)) (.or (φ.subst τ.τ) (.neg x)) (a.isub τ))
      ((L.isub (ISub.cons _ hyx τ.up.tail)).dinst .one) := by
    have := HasTy.isubS hW htyF (ISub.cons x hx τ)
    rw [transpFill_isub_cons] at this
    exact transp_canon_typed hW this
  have e1 : TyEq S k3 ((L'.isub (ISub.cons _ hyx' τ.up.tail)).dinst .one) ((L.isub (ISub.cons _ hyx τ.up.tail)).dinst .one) := by
    rw [end1 hx' hyx' cL' .one trivial, end1 hx hyx cL .one trivial]
    exact tyB (RT2.symm hW (hXL _) (hR k3 τ _ _ _ _ (ieq_and_congr e0 (I_eq_refl _))))
  have hty2 : HasTy S k3 .one [] (.transp (L'.isub (ISub.cons _ hyx' τ.up.tail)) (.or (φ'.subst τ.τ) (.neg x'))
      (a'.isub τ)) ((L.isub (ISub.cons _ hyx τ.up.tail)).dinst .one) := by
    have := HasTy.isubS hW htyF' (ISub.cons x' hx' τ)
    rw [transpFill_isub_cons] at this
    exact (transp_canon_typed hW this).tyConv e1
  -- the base
  have hbase : RE2 S k3 ((L.isub (ISub.cons _ hyx τ.up.tail)).dinst .zero) (a.isub τ) (a'.isub τ) := by
    have h0 := RE2.isub hW ha τ
    rw [show (L.dinst .zero).isub τ = L.isub (ISub.cons .zero trivial τ) by
      rw [isub_dinst]; exact isub_up_dinst L τ .zero trivial] at h0
    rw [end1 hx hyx cL .zero trivial]
    exact RE2.conv hW (hRL k3 τ _ _ _ _ (I_eq_symm (ieq_and_zero_right x))) h0
  have hEn : I.Eq (I.neg x) (I.neg x') := fun ρ0 => by simp only [I.eval]; rw [e0 ρ0]
  have h12' : I.Entails (I.or (φ.subst τ.τ) (.neg x)) (I.or (φ'.subst τ.τ) (.neg x')) :=
    ent_or_elim (ent_trans (ent_subst h12 _) (ent_or_left _ _)) (ent_trans (eq_ent hEn) (ent_or_right _ _))
  have h21' : I.Entails (I.or (φ'.subst τ.τ) (.neg x')) (I.or (φ.subst τ.τ) (.neg x)) :=
    ent_or_elim (ent_trans (ent_subst h21 _) (ent_or_left _ _)) (ent_trans (eq_ent (I_eq_symm hEn)) (ent_or_right _ _))
  have heqw := eqTm_transp_of hW hty1 hty2 (tyB rLL') h12' h21' (RE2.typed hbase).2.2
  have r := K LR _ _ LC hty1 hty2 heqw h12' h21' hbase
  rw [end1 hx hyx cL .one trivial] at r
  exact RE2.conv hW (hRL k3 τ _ _ _ _ (ieq_and_one_right x)) r

/-- The transport filler where its face holds is (related to) the base. -/
theorem tfill_face {L a : Tm} {φ : I} {l : ℕ} (hL : HasTy S (k + 1) .one [] L (.univ l))
    (hRL : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (L.isub (ISub.cons y hy τ)) (L.isub (ISub.cons y' hy' τ)))
    (hLC : LineConst S k L φ) (htyF : HasTy S (k + 1) .one [] (Tm.transpFill L φ a) L)
    (haa : RE2 S k (L.dinst .zero) a a) {k3 : ℕ} (τ : ISub k3 k) (r : I) (hr : r.Scoped k3)
    (hh : I.Entails .one (I.or (φ.subst τ.τ) (.neg r))) (h0 : (ival (idEnv k3) (φ.subst τ.τ)).holds ∨ r = .zero) :
    RE2 S k3 (L.isub (ISub.cons r hr τ)) ((Tm.transpFill L φ a).isub (ISub.cons r hr τ)) (a.isub τ) := by
  have hXL : ∀ {k4 : ℕ} (θ : ISub k4 (k + 1)), TyCode k4 (semK S k4 (L.isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW hL θ)
  have hty := HasTy.isubS hW htyF (ISub.cons r hr τ)
  have hst := stable_transpFace hW hh (by rw [transpFill_isub_cons] at hty; exact hty)
  rw [← transpFill_isub_cons L φ a r hr τ] at hst
  have h1 := RE2.isub hW haa τ
  rw [show (L.dinst .zero).isub τ = L.isub (ISub.cons .zero trivial τ) by
    rw [isub_dinst]; exact isub_up_dinst L τ .zero trivial] at h1
  have hrel : RT2 S k3 (L.isub (ISub.cons .zero trivial τ)) (L.isub (ISub.cons r hr τ)) := by
    rcases h0 with hh0 | rfl
    · exact RT2.symm hW (hXL _) (hLC k3 τ r hr hh0)
    · exact hRL k3 τ _ _ _ _ (I_eq_refl _)
  have h2 := RE2.conv hW hrel h1
  have hAA : RT2 S k3 (L.isub (ISub.cons r hr τ)) (L.isub (ISub.cons r hr τ)) := hRL k3 τ _ _ _ _ (I_eq_refl _)
  exact RE2.expandL hW hAA hty (RE2.typed h2).1 hst h2

/-- The transport filler at the end of the line is related to the transport. -/
theorem tfill_one {L L' a a' : Tm} {φ φ' : I} {l : ℕ} (hL : HasTy S (k + 1) .one [] L (.univ l))
    (hφs : φ.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hR : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (L.isub (ISub.cons y hy τ)) (L'.isub (ISub.cons y' hy' τ)))
    (hRL : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (L.isub (ISub.cons y hy τ)) (L.isub (ISub.cons y' hy' τ)))
    (hLC : LineConst S k L φ)
    (hT : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
      KanT2At S k3 (L.isub (ISub.cons y hy τ.up.tail)) (L'.isub (ISub.cons y' hy' τ.up.tail)) (a.isub τ) (a'.isub τ))
    (htyF : HasTy S (k + 1) .one [] (Tm.transpFill L φ a) L)
    (htyO' : HasTy S k .one [] (.transp L' φ' a') (L.dinst .one))
    (ha : RE2 S k (L.dinst .zero) a a')
    (hO : RE2 S k (L.dinst .one) (.transp L φ a) (.transp L' φ' a')) {k3 : ℕ} (τ : ISub k3 k) :
    RE2 S k3 (L.isub (ISub.cons .one trivial τ)) ((Tm.transpFill L φ a).isub (ISub.cons .one trivial τ))
      ((Tm.transp L φ a).isub τ) := by
  have hXL : ∀ {k4 : ℕ} (θ : ISub k4 (k + 1)), TyCode k4 (semK S k4 (L.isub θ)) := fun θ =>
    tyCode_of_univ hW (HasTy.isubS hW hL θ)
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have e1L : ∀ {k4 : ℕ} (θ : ISub k4 k), (L.dinst .one).isub θ = L.isub (ISub.cons .one trivial θ) := fun θ => by
    rw [isub_dinst]; exact isub_up_dinst L θ .one trivial
  have e0L : (L.dinst .zero).isub τ = L.isub (ISub.cons .zero trivial τ) := by
    rw [isub_dinst]; exact isub_up_dinst L τ .zero trivial
  rw [transpFill_isub_cons]
  have hy1 := scoped_andShift (show (I.one).Scoped k3 from trivial)
  have hy0 : (I.var 0).Scoped (k3 + 1) := show 0 < k3 + 1 by omega
  have hone : ∀ (z : I), I.Eq (I.and .one z) z := fun z ρ0 => by simp only [I.eval]; cases z.eval ρ0 <;> rfl
  have hEy : I.Eq (I.and I.one.shift (.var 0)) (.var 0) := hone _
  have K := hT k3 τ _ _ hy1 hy0 hEy
  have eR : (L'.isub τ.up) = L'.isub (ISub.cons (.var 0) hy0 τ.up.tail) := by rw [ISub.cons_var0_up_tail]
  have LR : LineRob S k3 (L.isub (ISub.cons _ hy1 τ.up.tail)) (L'.isub (ISub.cons _ hy0 τ.up.tail)) := by
    intro k4 τ2 z z' hz hz' hEz
    rw [isub_line_pt, isub_line_pt]
    refine hR k4 (τ.comp τ2) _ _ _ _ ?_
    rw [andShift_subst]
    exact I_eq_trans (hone _) hEz
  have nen1 : ¬ I.Entails .one (I.neg .one) := by decide
  have hψs : (I.or (φ.subst τ.τ) (.neg .one)).Scoped k3 := ⟨I.scoped_subst hφs τ.sc, trivial⟩
  have LC : LineConst S k3 (L.isub (ISub.cons _ hy1 τ.up.tail)) (.or (φ.subst τ.τ) (.neg .one)) := by
    intro k4 τ2 z hz hh
    rw [isub_line_pt, isub_line_pt]
    have he := (holds_iff_entails (I.scoped_subst hψs τ2.sc)).1 hh
    rcases ent_or_cases (I.scoped_subst hψs.1 τ2.sc) (show ((I.neg .one).subst τ2.τ).Scoped k4 from trivial) he
      with hφ2 | hx2
    · have hh2 : (ival (idEnv k4) (φ.subst (τ.comp τ2).τ)).holds :=
        (holds_iff_entails (I.scoped_subst hφs (τ.comp τ2).sc)).2 (ent_comp_inv hφ2)
      have gz := hLC k4 (τ.comp τ2) _ (I.scoped_subst hy1 (ISub.cons z hz τ2).sc) hh2
      have g0 := hLC k4 (τ.comp τ2) _ (I.scoped_subst hy1 (ISub.cons .zero trivial τ2).sc) hh2
      exact RT2.trans hW (hXL _) gz (RT2.symm hW (hXL _) g0)
    · exact (nen1 hx2).elim
  have cL : (L.isub (ISub.cons _ hy1 τ.up.tail)).closedB 0 (k3 + 1) = true :=
    closed_ty (spec_to_minimal hW (HasTy.isubS hW hL _))
  have rLL' := hR (k3 + 1) τ.up.tail _ _ hy1 hy0 hEy
  have end1 : ∀ (r : I) (hr : r.Scoped k3), (L.isub (ISub.cons _ hy1 τ.up.tail)).dinst r =
      L.isub (ISub.cons (I.and .one r) (show (I.and .one r).Scoped k3 from ⟨trivial, hr⟩) τ) := by
    intro r hr
    rw [dinst_line _ _ _ cL r hr]
    congr 1
  have hty1 : HasTy S k3 .one [] (.transp (L.isub (ISub.cons _ hy1 τ.up.tail)) (.or (φ.subst τ.τ) (.neg .one))
      (a.isub τ)) ((L.isub (ISub.cons _ hy1 τ.up.tail)).dinst .one) := by
    have := HasTy.isubS hW htyF (ISub.cons .one trivial τ)
    rw [transpFill_isub_cons] at this
    exact transp_canon_typed hW this
  have e11 : TyEq S k3 (L.isub (ISub.cons .one trivial τ)) ((L.isub (ISub.cons _ hy1 τ.up.tail)).dinst .one) := by
    rw [end1 .one trivial]
    exact tyB (hRL k3 τ _ _ _ _ (I_eq_symm (hone _)))
  have hty2 : HasTy S k3 .one [] (.transp (L'.isub (ISub.cons _ hy0 τ.up.tail)) (φ'.subst τ.τ) (a'.isub τ))
      ((L.isub (ISub.cons _ hy1 τ.up.tail)).dinst .one) := by
    have := HasTy.isubS hW htyO' τ
    rw [e1L] at this
    rw [← eR]
    exact this.tyConv e11
  have hbase : RE2 S k3 ((L.isub (ISub.cons _ hy1 τ.up.tail)).dinst .zero) (a.isub τ) (a'.isub τ) := by
    have h0 := RE2.isub hW ha τ
    rw [e0L] at h0
    rw [end1 .zero trivial]
    exact RE2.conv hW (hRL k3 τ _ _ _ _ (I_eq_symm (hone _))) h0
  have h12' : I.Entails (I.or (φ.subst τ.τ) (.neg .one)) (φ'.subst τ.τ) :=
    ent_or_elim (ent_subst h12 _) (ent_trans (eq_ent (show I.Eq (I.neg .one) .zero from fun _ => rfl)) (ent_zero _))
  have h21' : I.Entails (φ'.subst τ.τ) (I.or (φ.subst τ.τ) (.neg .one)) :=
    ent_trans (ent_subst h21 _) (ent_or_left _ _)
  have heqw := eqTm_transp_of hW hty1 hty2 (tyB rLL') h12' h21' (RE2.typed hbase).2.2
  have r := K LR _ _ LC hty1 hty2 heqw h12' h21' hbase
  have hA1 : RT2 S k3 ((L.isub (ISub.cons _ hy1 τ.up.tail)).dinst .one) (L.isub (ISub.cons .one trivial τ)) := by
    rw [end1 .one trivial]; exact hRL k3 τ _ _ _ _ (hone _)
  have r' := RE2.conv hW hA1 r
  rw [← eR] at r'
  have hOτ := RE2.isub hW hO τ
  rw [e1L] at hOτ
  have hAA : RT2 S k3 (L.isub (ISub.cons .one trivial τ)) (L.isub (ISub.cons .one trivial τ)) :=
    hRL k3 τ _ _ _ _ (I_eq_refl _)
  exact RE2.trans hW hAA r' (RE2.symm hW hAA hOτ)

end

end Model.Whnf
