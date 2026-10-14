import Model.Whnf.Kan2Sigma

/-!
# The binary transport at Σ-types
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem sigma_dinst (A B : Tm) (r : I) : (Tm.sigma A B).dinst r = .sigma (A.dinst r) (B.dinst r) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, up_var]

theorem step_transp_sigma {A B a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.transp (.sigma A B) φ a) = some (Tm.transpSigma A B φ a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

variable (hW : WfSig S)
include hW

/-- The first projection of a transport along a line of Σ-types whose face does not hold. -/
theorem fst_transp_sigma {T A2 B2 a0 : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hR : RedT S (k + 1) T (.sigma A2 B2)) :
    Red S (.fst (.transp T φ a0)) (.transp A2 φ (.fst a0)) ∧
    EqTm S k .one [] (.fst (.transp T φ a0)) (.transp A2 φ (.fst a0)) (A2.dinst .one) := by
  have e1 := eq_transp_ty hW hty hR.2
  have e2 := EqTm.transpSigma (HasTy.eqR e1)
  have hT1 : TyEq S k (T.dinst .one) (.sigma (A2.dinst .one) (B2.dinst .one)) := by
    have := tyEq_dinst hW hR.2 (r := .one) trivial; rwa [sigma_dinst] at this
  have e3 := (e1.trans e2).tyConv hT1
  have e4 := EqTm.fst e3
  simp only [Tm.transpSigma] at e4
  have e5 := EqTm.fstBeta (HasTy.eqR e4)
  refine ⟨(red_fst ((red_transp_ty hn hR.1.1).trans (.step (step_transp_sigma hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rfl

/-- The second projection of a transport along a line of Σ-types whose face does not hold. -/
theorem snd_transp_sigma {T A2 B2 a0 : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hR : RedT S (k + 1) T (.sigma A2 B2)) :
    Red S (.snd (.transp T φ a0)) (.transp (B2.inst (Tm.transpFill A2 φ (.fst a0))) φ (.snd a0)) ∧
    EqTm S k .one [] (.snd (.transp T φ a0)) (.transp (B2.inst (Tm.transpFill A2 φ (.fst a0))) φ (.snd a0))
      ((B2.dinst .one).inst (.fst (.transp T φ a0))) := by
  have e1 := eq_transp_ty hW hty hR.2
  have e2 := EqTm.transpSigma (HasTy.eqR e1)
  have hT1 : TyEq S k (T.dinst .one) (.sigma (A2.dinst .one) (B2.dinst .one)) := by
    have := tyEq_dinst hW hR.2 (r := .one) trivial; rwa [sigma_dinst] at this
  have e3 := (e1.trans e2).tyConv hT1
  have e4 := EqTm.snd e3
  simp only [Tm.transpSigma] at e4
  have e5 := EqTm.sndBeta (HasTy.eqR e4)
  refine ⟨(red_snd ((red_transp_ty hn hR.1.1).trans (.step (step_transp_sigma hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rfl

/-- A projection of a transport whose face holds, stably. -/
theorem stable_fst_transpFace {X Y T a : Tm} {φ : I} (h : I.Entails .one φ)
    (hty : HasTy S k .one [] (.transp T φ a) (T.dinst .one)) (hT1 : TyEq S k (T.dinst .one) (.sigma X Y)) :
    StableE S k X (.fst (.transp T φ a)) (.fst a) := by
  intro k' σ
  have hσ : I.Entails .one (φ.subst σ.τ) := by have := ent_subst h σ.τ; simpa [I.subst] using this
  have hty' := HasTy.isubS hW hty σ
  have e := hT1.isub hW σ
  rw [isub_sigma] at e
  show Red S (.fst (.transp (T.isub σ.up) (φ.subst σ.τ) (a.isub σ))) _ ∧ _
  exact ⟨red_fst (.step (step_transp_face hσ) (.refl _)), EqTm.fst ((EqTm.transpFace hσ hty').tyConv e)⟩


/-- The Σ-type a type reduces to is typed. -/
theorem sigmaW_typed {X A B : Tm} (hX : IsTyK S k X) (hR : RedT S k X (.sigma A B)) :
    ∃ l, HasTy S k .one [] (.sigma A B) (.univ l) :=
  ty_of_tyEq hW hX hR.2 (fun l h => by cases h)

/-- The normal forms of related types whose normal forms are Σ-types are related componentwise. -/
theorem sigmaW_rel {X Y A B A' B' : Tm} (h : RT2 S k X Y) (hX : RedT S k X (.sigma A B))
    (hY : RedT S k Y (.sigma A' B')) :
    RT2 S k A A' ∧ ∀ a a', RE2 S k A a a' → RT2 S k (B.inst a) (B'.inst a') := by
  obtain ⟨l, hsig⟩ := sigmaW_typed hW (Comp2_ty_base h).2.1 hX
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := (SigmaStr_of hW h hX hsig).whnf k (ISub.id k)
  have hXc := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base h).2.1)
  have hYc := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base h).2.2.1)
  rw [hXc] at h1; rw [hYc] at h2
  obtain ⟨rfl, rfl⟩ : A1 = A ∧ B1 = B := by
    have := RedW.unique h1.1 hX.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1' = A' ∧ B1' = B' := by
    have := RedW.unique h2.1 hY.1; injection this; constructor <;> assumption
  exact ⟨h3, h4⟩

/-- The first projections of transports along related lines of Σ-types. -/
theorem kanT2_sigma_fst {T T' : Tm} (hTT : RT2 S (k + 1) T T') (hP : SigmaStr S (k + 1) T T')
    (hLR : LineRob S k T T')
    (hIHA : ∀ k1 (ρ : ISub k1 (k + 1)) A1 B1, RedT S k1 (T.isub ρ) (.sigma A1 B1) →
      ∀ k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) (A1.isub ρ') X' → KanT2 S k2 (A1.isub ρ') X')
    {φ φ' : I} {a0 a0' : Tm} (hC : LineConst S k T φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one))
    (hty' : HasTy S k .one [] (.transp T' φ' a0') (T.dinst .one))
    (heq : EqTm S k .one [] (.transp T φ a0) (.transp T' φ' a0') (T.dinst .one))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (ha0 : RE2 S k (T.dinst .zero) a0 a0')
    {A1 B1 : Tm} (hR1 : RedT S k (T.dinst .one) (.sigma A1 B1)) :
    RE2 S k A1 (.fst (.transp T φ a0)) (.fst (.transp T' φ' a0')) := by
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hXT : TyCode (k + 1) (semK S (k + 1) T) := tyCode_of_univ hW hTl'
  have hTK : ∀ k3 (σ : ISub k3 (k + 1)), IsTyK S k3 (T.isub σ) := fun k3 σ => ⟨l0, .inl (HasTy.isubS hW hTl' σ)⟩
  have hXTσ : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (T.isub σ)) := fun k3 σ => by
    rw [semK_isubTy hW ⟨l0, .inl hTl'⟩ σ]; exact hXT.res _
  choose A2 B2 A2' B2' hw using hP.whnf
  have hXA : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (A2 k3 σ)) := fun k3 σ => by
    obtain ⟨l, h⟩ := sigmaW_typed hW (hTK k3 σ) (hw k3 σ).1
    exact tyCode_of_univ hW (HasTy.sigmaDom h)
  have G3 : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((A2 k1 σ1).isub θ) (A2 k2 σ2) := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact (hP.coh k1 σ1 k2 θ _ _ _ _ (hw k1 σ1).1 (hw k2 _).1).1
  have G3' : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((A2' k1 σ1).isub θ) (A2' k2 σ2) := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact (hP.coh' k1 σ1 k2 θ _ _ _ _ (hw k1 σ1).2.1 (hw k2 _).2.1).1
  have G1 : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (A2 k3 (ISub.cons y hy τ)) (A2' k3 (ISub.cons y' hy' τ)) :=
    fun k3 τ y y' hy hy' hE => (sigmaW_rel hW (hLR k3 τ y y' hy hy' hE) (hw _ _).1 (hw _ _).2.1).1
  have G2 : ∀ k3 (τ : ISub k3 k) (y : I) (hy : y.Scoped k3), (ival (idEnv k3) (φ.subst τ.τ)).holds →
      RT2 S k3 (A2 k3 (ISub.cons y hy τ)) (A2 k3 (ISub.cons .zero trivial τ)) :=
    fun k3 τ y hy hh => (sigmaW_rel hW (hC k3 τ y hy hh) (hw _ _).1 (hw _ _).1).1
  -- the endpoint `T(1)`
  let ι1 : ISub k (k + 1) := ISub.cons .one trivial (ISub.id k)
  have hR1' : RedT S k (T.isub ι1) (.sigma A1 B1) := by rw [isub_cons_id_of_closed hTc]; exact hR1
  obtain ⟨hA1e, hB1e⟩ : A2 k ι1 = A1 ∧ B2 k ι1 = B1 := by
    have := RedW.unique (hw k ι1).1.1 hR1'.1; injection this; constructor <;> assumption
  have Aend : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A2 k' (ISub.cons .one trivial ρ)) := by
    intro k' ρ; rw [← hA1e]; exact G3 k ι1 k' ρ _ (cons_one_comp ρ)
  have hX : TyCode k (semK S k A1) := by rw [← hA1e]; exact hXA _ _
  have hYY : RT2 S k A1 A1 := by have := (hw k ι1).2.2.1; rw [hA1e] at this; exact RT2.refl hW hX this
  have hYK : IsTyK S k A1 := (Comp2_ty_base hYY).2.1
  have hXY : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' (A1.isub ρ)) := fun k' ρ => by
    rw [semK_isubTy hW hYK ρ]; exact hX.res _
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hT0 : ∀ {k3 : ℕ} (σ : ISub k3 k), (T.dinst .zero).isub σ = T.isub (ISub.cons .zero trivial σ) := fun σ => by
    rw [isub_dinst]; exact isub_up_dinst T σ .zero trivial
  -- the eliminated lines at points
  have Cpt : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      RT2 S k3 ((A2 (k' + 1) ρ.up).isub (ISub.cons x hx θ)) (A2 k3 (ISub.cons x hx (ρ.comp θ))) :=
    fun k' ρ k3 θ x hx => G3 (k' + 1) ρ.up k3 _ _ (ISub.up_comp_cons ρ x hx θ)
  have C'pt : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      RT2 S k3 ((A2' (k' + 1) ρ.up).isub (ISub.cons x hx θ)) (A2' k3 (ISub.cons x hx (ρ.comp θ))) :=
    fun k' ρ k3 θ x hx => G3' (k' + 1) ρ.up k3 _ _ (ISub.up_comp_cons ρ x hx θ)
  have Cd1 : ∀ k' (ρ : ISub k' k), RT2 S k' ((A2 (k' + 1) ρ.up).dinst .one) (A2 k' (ISub.cons .one trivial ρ)) := by
    intro k' ρ
    have hcl := closed_of_isTyK hW (Comp2_ty_base (hw (k' + 1) ρ.up).2.2.1).2.1
    rw [← isub_cons_id_of_closed hcl .one trivial]
    exact G3 (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id])
  have C'd1 : ∀ k' (ρ : ISub k' k), RT2 S k' ((A2' (k' + 1) ρ.up).dinst .one) (A2' k' (ISub.cons .one trivial ρ)) := by
    intro k' ρ
    have hcl := closed_of_isTyK hW (Comp2_ty_base (hw (k' + 1) ρ.up).2.2.1).2.2.1
    rw [← isub_cons_id_of_closed hcl .one trivial]
    exact G3' (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id])
  -- typings
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty ρ; rwa [isub_dinst] at this
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ))
      ((T'.isub ρ.up).dinst .one) := fun k' ρ => by
    have := (HasTy.isubS hW hty' ρ).tyConv ((tyEq_dinst hW hP.tyEq (r := .one) trivial).isub hW ρ)
    rwa [isub_dinst] at this
  -- the bases where the face holds
  have hfin : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst ρ.τ) →
      RE2 S k' (A1.isub ρ) (.fst (a0.isub ρ)) (.fst (a0'.isub ρ)) := by
    intro k' ρ hf
    have h0 := RE2.isub hW ha0 ρ
    rw [hT0] at h0
    have hCρ := hC k' ρ .one trivial ((holds_iff_entails (I.scoped_subst hφs ρ.sc)).2 hf)
    have h1 := RE2.conv' hW hCρ h0 (hXTσ _ _)
    exact RE2.conv' hW (Aend k' ρ) (hP.elim k' _ _ _ _ _ (hw k' _).1 h1).1 (hXY k' ρ)
  have eTF : ∀ k' (ρ : ISub k' k), TyEq S k' ((T.isub ρ.up).dinst .one) (.sigma (A1.isub ρ) (B1.isub ρ)) := by
    intro k' ρ; have := hR1.2.isub hW ρ; rw [isub_dinst, isub_sigma] at this; exact this
  have H := kanT2_elim_core hW (fun k' ρ x => .fst x) (fun k' ρ x => .fst x)
    (fun k' ρ => A2 (k' + 1) ρ.up) (fun k' ρ => A2' (k' + 1) ρ.up)
    (fun k' ρ => .fst (a0.isub ρ)) (fun k' ρ => .fst (a0'.isub ρ))
    hX hYY (HasTy.fst (hty.tyConv hR1.2)) (HasTy.fst (hty'.tyConv hR1.2)) (EqTm.fst (heq.tyConv hR1.2))
    (fun k' ρ k'' ρ' x => rfl) (fun k' ρ k'' ρ' x => rfl)
    (fun k' ρ => ⟨fun hf => ?_, fun hf => ?_⟩) (fun k' ρ => ⟨fun hf => ?_, fun hf => ?_⟩) hfin
    (fun k' ρ k'' ρ' _ hf2 => by
      show RE2 S k'' _ (.fst ((a0.isub ρ).isub ρ')) _; rw [Tm.isub_isub]; exact hfin k'' _ hf2)
    (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' hnf => ?_) (fun k' ρ k'' ρ' _ => ?_)
    (fun k' ρ k'' ρ' _ => ?_) h12 h21
  · exact H
  · exact ⟨red_fst (.step (step_transp_face hf) (.refl _)),
      EqTm.fst ((EqTm.transpFace hf (hρT k' ρ)).tyConv (eTF k' ρ))⟩
  · obtain ⟨a, b⟩ := fst_transp_sigma hW hf (hρT k' ρ) (hw (k' + 1) ρ.up).1
    exact ⟨a, b.tyConv (TyEq.trans hW (tyB (Cd1 k' ρ)) (TyEq.symm (tyB (Aend k' ρ))))⟩
  · have eT : TyEq S k' ((T'.isub ρ.up).dinst .one) ((T.isub ρ.up).dinst .one) := by
      have := (tyEq_dinst hW hP.tyEq (r := .one) trivial).isub hW ρ
      rw [isub_dinst, isub_dinst] at this; exact TyEq.symm this
    exact ⟨red_fst (.step (step_transp_face hf) (.refl _)),
      EqTm.fst ((EqTm.transpFace hf (hρT' k' ρ)).tyConv (TyEq.trans hW eT (eTF k' ρ)))⟩
  · obtain ⟨a, b⟩ := fst_transp_sigma hW hf (hρT' k' ρ) (hw (k' + 1) ρ.up).2.1
    have e1 := tyB (C'd1 k' ρ)
    have e2 := tyB ((hw k' (ISub.cons .one trivial ρ)).2.2.1)
    exact ⟨a, b.tyConv (TyEq.trans hW e1 (TyEq.trans hW (TyEq.symm e2) (TyEq.symm (tyB (Aend k' ρ)))))⟩
  · -- the lines at their ends
    show RT2 S k'' (((A2 (k' + 1) ρ.up).isub ρ'.up).dinst .one) _
    rw [isub_up_dinst _ ρ' .one trivial]
    have c := Cpt k' ρ k'' ρ' .one trivial
    exact RT2.trans hW (RT2.tyCode_l hW c (hXA _ _)) c (RT2.symm hW (hXY _ _) (Aend k'' _))
  · -- robustness
    intro k3 τ x x' hx hx' hEx
    show RT2 S k3 (((A2 (k' + 1) ρ.up).isub ρ'.up).isub (ISub.cons x hx τ))
      ((A2' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons x' hx' τ))
    rw [Tm.isub_isub, ISub.up_comp_cons]
    have c1 := Cpt k' ρ k3 (ρ'.comp τ) x hx
    have c3 := C'pt k'' (ρ.comp ρ') k3 τ x' hx'
    rw [ISub.comp_assoc] at c3
    have m := G1 k3 (ρ.comp (ρ'.comp τ)) x x' hx hx' hEx
    have t3 := RT2.tyCode_l hW c3 (RT2.tyCode_r hW m (hXA _ _))
    exact RT2.trans hW (RT2.tyCode_l hW c1 (hXA _ _)) c1 (RT2.trans hW (hXA _ _) m (RT2.symm hW t3 c3))
  · -- constancy
    intro k3 τ x hx hh
    show RT2 S k3 (((A2 (k' + 1) ρ.up).isub ρ'.up).isub (ISub.cons x hx τ))
      (((A2 (k' + 1) ρ.up).isub ρ'.up).isub (ISub.cons .zero trivial τ))
    rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons]
    have hh' : (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp τ)).τ)).holds := by
      rw [I_subst_comp, I_subst_comp]; exact hh
    have c1 := Cpt k' ρ k3 (ρ'.comp τ) x hx
    have c2 := Cpt k' ρ k3 (ρ'.comp τ) .zero trivial
    have m := G2 k3 _ x hx hh'
    exact RT2.trans hW (RT2.tyCode_l hW c1 (hXA _ _)) c1
      (RT2.trans hW (hXA _ _) m (RT2.symm hW (RT2.tyCode_l hW c2 (hXA _ _)) c2))
  · -- the bases
    show RE2 S k'' (((A2 (k' + 1) ρ.up).isub ρ'.up).dinst .zero) (.fst ((a0.isub ρ).isub ρ'))
      (.fst (a0'.isub (ρ.comp ρ')))
    rw [isub_up_dinst _ ρ' .zero trivial, Tm.isub_isub]
    have h0 := RE2.isub hW ha0 (ρ.comp ρ')
    rw [hT0] at h0
    have c := Cpt k' ρ k'' ρ' .zero trivial
    exact RE2.conv' hW c (hP.elim k'' _ _ _ _ _ (hw k'' _).1 h0).1 (RT2.tyCode_l hW c (hXA _ _))
  · -- the induction hypothesis
    refine hIHA (k' + 1) ρ.up _ _ (hw _ ρ.up).1 k'' ρ'.up _ ?_
    have c := G3 (k' + 1) ρ.up (k'' + 1) ρ'.up (ρ.comp ρ').up (ISub.up_comp ρ ρ').symm
    exact RT2.trans hW (RT2.tyCode_l hW c (hXA _ _)) c (hw (k'' + 1) (ρ.comp ρ').up).2.2.1

end

end Model.Whnf
