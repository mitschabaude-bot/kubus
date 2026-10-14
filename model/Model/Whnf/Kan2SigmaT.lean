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

theorem ISub.up_tail_comp_up {k3 : ℕ} (σ : ISub k3 k) (τ : ISub k'' k3) :
    (σ.up.tail).comp τ.up = (σ.comp τ).up.tail := by
  ext i
  show ((σ.τ i).shift).subst (I.up τ.τ) = ((σ.τ i).subst τ.τ).shift
  exact I_shift_subst_up _ _

theorem ieq_and_congr {a a' b b' : I} (h1 : I.Eq a a') (h2 : I.Eq b b') : I.Eq (I.and a b) (I.and a' b') :=
  fun ρ0 => by simp only [I.eval]; rw [h1 ρ0, h2 ρ0]

theorem ieq_and_zero_right (a : I) : I.Eq (I.and a .zero) .zero := fun ρ0 => by
  simp only [I.eval]; cases a.eval ρ0 <;> rfl

theorem ieq_and_one_right (a : I) : I.Eq (I.and a .one) a := fun ρ0 => by
  simp only [I.eval]; cases a.eval ρ0 <;> rfl

theorem ieq_and_zero_left {a : I} (b : I) (h : I.Eq a .zero) : I.Eq (I.and a b) .zero := fun ρ0 => by
  simp only [I.eval]; rw [h ρ0]; cases b.eval ρ0 <;> rfl

theorem isub_bindAnd {k3 : ℕ} (X : Tm) (x : I) (hx : x.Scoped k3) (τ : ISub k3 k') :
    (X.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons x hx τ).up =
      X.isub (ISub.cons (.and x.shift (.var 0)) ⟨KubusCore.I.scoped_shift hx, (show (0 : ℕ) < k3 + 1 by omega)⟩
        τ.up.tail) := by
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | i
  · rfl
  · rfl

theorem isub_bindAnd_up (X : Tm) (τ : ISub k'' k') :
    (X.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub τ.up.up =
      X.isub (ISub.cons (.and (.var 1) (.var 0)) ⟨show 1 < k'' + 2 by omega, show 0 < k'' + 2 by omega⟩
        τ.up.tail.up.tail) := by
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | i
  · rfl
  · rfl

theorem dsubst_bindAnd_closed {X : Tm} (hX : X.closedB 0 (k + 1) = true) :
    X.dsubst (Tm.bind2 (.and (.var 1) (.var 0))) =
      X.isub (ISub.cons (.and (.var 1) (.var 0)) ⟨show 1 < k + 2 by omega, show 0 < k + 2 by omega⟩
        (ISub.id k).up.tail.up.tail) := by
  simp only [Tm.dsubst, Tm.isub]
  refine closed_subst_eq X 0 (k + 1) _ _ _ _ hX (fun _ h => absurd h (Nat.not_lt_zero _)) fun i hi => ?_
  rcases i with _ | i
  · rfl
  · show I.var (i + 2) = (((ISub.id k).τ i).shift).shift
    simp [ISub.id, show i < k by omega, I.shift, I.ren, I.subst]

variable (hW : WfSig S)
include hW

/-- A transport is typed at the end of its line. -/
theorem transp_canon_typed {X T b : Tm} {ψ : I} (h : HasTy S k .one [] (.transp X ψ b) T) :
    HasTy S k .one [] (.transp X ψ b) (X.dinst .one) := by
  obtain ⟨l0, ⟨hL, hφ, hc, ha⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW h) rfl
  exact minimal_to_spec (HasTy0.transp hL hφ hc ha)

/-- The typing of the transport filler of the first projection, along a line of Σ-types. -/
theorem transpSigma_fill_typed {T A B a0 : Tm} {φ : I} (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one))
    (hR : RedT S (k + 1) T (.sigma A B)) :
    HasTy S (k + 1) .one [] (Tm.transpFill A φ (.fst a0)) A := by
  have hS := sigClosed_of_wfSig hW
  have h1 := HasTy.eqR (eq_transp_ty hW hty hR.2)
  obtain ⟨l0, ⟨hL, hφ, hc, ha⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW h1) rfl
  have hA0 := HasTy0.sigmaDom hS hL
  have hcD := EqTm0.sigmaInjDom (A' := (A.dinst .zero).dshift) hc
  rw [sigma_dinst] at ha
  exact minimal_to_spec (transpFill_typed hS hA0 hφ hcD (HasTy0.fst ha)).1

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


/-- The second projections of transports along related lines of Σ-types. -/
theorem kanT2_sigma_snd {T T' : Tm} (hTT : RT2 S (k + 1) T T') (hP : SigmaStr S (k + 1) T T')
    (hLR : LineRob S k T T')
    (hIHA : ∀ k1 (ρ : ISub k1 (k + 1)) A1 B1, RedT S k1 (T.isub ρ) (.sigma A1 B1) →
      ∀ k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) (A1.isub ρ') X' → KanT2 S k2 (A1.isub ρ') X')
    (hIHB : ∀ k1 (ρ : ISub k1 (k + 1)) A1 B1, RedT S k1 (T.isub ρ) (.sigma A1 B1) → ∀ b, RE2 S k1 A1 b b →
      ∀ k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) ((B1.inst b).isub ρ') X' → KanT2 S k2 ((B1.inst b).isub ρ') X')
    {φ φ' : I} {a0 a0' : Tm} (hC : LineConst S k T φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one))
    (hty' : HasTy S k .one [] (.transp T' φ' a0') (T.dinst .one))
    (heq : EqTm S k .one [] (.transp T φ a0) (.transp T' φ' a0') (T.dinst .one))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (ha0 : RE2 S k (T.dinst .zero) a0 a0')
    {A1 B1 : Tm} (hR1 : RedT S k (T.dinst .one) (.sigma A1 B1)) :
    RE2 S k (B1.inst (.fst (.transp T φ a0))) (.snd (.transp T φ a0)) (.snd (.transp T' φ' a0')) := by
  have FST := kanT2_sigma_fst hW hTT hP hLR hIHA hC hty hty' heq h12 h21 ha0 hR1
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hXT : TyCode (k + 1) (semK S (k + 1) T) := tyCode_of_univ hW hTl'
  have hTK : ∀ k3 (σ : ISub k3 (k + 1)), IsTyK S k3 (T.isub σ) := fun k3 σ => ⟨l0, .inl (HasTy.isubS hW hTl' σ)⟩
  have hXTσ : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (T.isub σ)) := fun k3 σ => by
    rw [semK_isubTy hW (hTK (k + 1) (ISub.id (k + 1)) |> fun _ => ⟨l0, .inl hTl'⟩) σ]; exact hXT.res _
  choose A2 B2 A2' B2' hw using hP.whnf
  have hXA : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (A2 k3 σ)) := fun k3 σ => by
    obtain ⟨l, h⟩ := sigmaW_typed hW (hTK k3 σ) (hw k3 σ).1
    exact tyCode_of_univ hW (HasTy.sigmaDom h)
  have hBpt : ∀ k3 (σ : ISub k3 (k + 1)) a, HasTy S k3 .one [] a (A2 k3 σ) →
      TyCode k3 (semK S k3 ((B2 k3 σ).inst a)) := fun k3 σ a ha => by
    obtain ⟨l, hpi⟩ := sigmaW_typed hW (hTK k3 σ) (hw k3 σ).1
    exact tyCode_of_univ hW (minimal_to_spec (HasTy0.subst (sigClosed_of_wfSig hW)
      (HasTy0.sigmaCod (sigClosed_of_wfSig hW) (spec_to_minimal hW hpi)) (spec_to_minimal hW ha)))
  have hBpt' : ∀ k3 (σ : ISub k3 (k + 1)) a, HasTy S k3 .one [] a (A2' k3 σ) →
      TyCode k3 (semK S k3 ((B2' k3 σ).inst a)) := fun k3 σ a ha => by
    obtain ⟨l, hpi⟩ := sigmaW_typed hW (Comp2_ty_base (RT2.isub hW hXT hTT σ)).2.2.1 (hw k3 σ).2.1
    exact tyCode_of_univ hW (minimal_to_spec (HasTy0.subst (sigClosed_of_wfSig hW)
      (HasTy0.sigmaCod (sigClosed_of_wfSig hW) (spec_to_minimal hW hpi)) (spec_to_minimal hW ha)))
  -- coherence of the normal forms of the restrictions
  have G3 : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((A2 k1 σ1).isub θ) (A2 k2 σ2) ∧ ∀ a a', RE2 S k2 ((A2 k1 σ1).isub θ) a a' →
        RT2 S k2 (((B2 k1 σ1).isub θ).inst a) ((B2 k2 σ2).inst a') := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact hP.coh k1 σ1 k2 θ _ _ _ _ (hw k1 σ1).1 (hw k2 _).1
  have G3' : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((A2' k1 σ1).isub θ) (A2' k2 σ2) ∧ ∀ a a', RE2 S k2 ((A2' k1 σ1).isub θ) a a' →
        RT2 S k2 (((B2' k1 σ1).isub θ).inst a) ((B2' k2 σ2).inst a') := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact hP.coh' k1 σ1 k2 θ _ _ _ _ (hw k1 σ1).2.1 (hw k2 _).2.1
  -- robustness in the line coordinate
  have G1 : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (A2 k3 (ISub.cons y hy τ)) (A2' k3 (ISub.cons y' hy' τ)) ∧
      ∀ a a', RE2 S k3 (A2 k3 (ISub.cons y hy τ)) a a' →
        RT2 S k3 ((B2 k3 (ISub.cons y hy τ)).inst a) ((B2' k3 (ISub.cons y' hy' τ)).inst a') :=
    fun k3 τ y y' hy hy' hE => sigmaW_rel hW (hLR k3 τ y y' hy hy' hE) (hw _ _).1 (hw _ _).2.1
  have G1L : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (A2 k3 (ISub.cons y hy τ)) (A2 k3 (ISub.cons y' hy' τ)) ∧
      ∀ a a', RE2 S k3 (A2 k3 (ISub.cons y hy τ)) a a' →
        RT2 S k3 ((B2 k3 (ISub.cons y hy τ)).inst a) ((B2 k3 (ISub.cons y' hy' τ)).inst a') := by
    intro k3 τ y y' hy hy' hE
    have m1 := hLR k3 τ y y' hy hy' hE
    have m2 := hLR k3 τ y' y' hy' hy' (I_eq_refl _)
    have m := RT2.trans hW (hXTσ k3 _) m1 (RT2.symm hW (hXTσ k3 _) m2)
    exact sigmaW_rel hW m (hw _ _).1 (hw _ _).1
  have G2 : ∀ k3 (τ : ISub k3 k) (y : I) (hy : y.Scoped k3), (ival (idEnv k3) (φ.subst τ.τ)).holds →
      RT2 S k3 (A2 k3 (ISub.cons y hy τ)) (A2 k3 (ISub.cons .zero trivial τ)) ∧
      ∀ a a', RE2 S k3 (A2 k3 (ISub.cons y hy τ)) a a' →
        RT2 S k3 ((B2 k3 (ISub.cons y hy τ)).inst a) ((B2 k3 (ISub.cons .zero trivial τ)).inst a') :=
    fun k3 τ y hy hh => sigmaW_rel hW (hC k3 τ y hy hh) (hw _ _).1 (hw _ _).1
  -- the generic lemmas on lines of domains
  have lk := lineKan_of hW A2 A2' hXA (fun k1 σ1 k2 θ σ2 h => (G3 k1 σ1 k2 θ σ2 h).1)
    (fun k1 σ1 k2 θ σ2 h => (G3' k1 σ1 k2 θ σ2 h).1) (fun k3 τ y y' hy hy' hE => (G1 k3 τ y y' hy hy' hE).1)
    (fun k1 σ1 k2 ρ' X' h => hIHA k1 σ1 _ _ (hw k1 σ1).1 k2 ρ' X' h)
  have lkL := lineKan_of hW A2 A2 hXA (fun k1 σ1 k2 θ σ2 h => (G3 k1 σ1 k2 θ σ2 h).1)
    (fun k1 σ1 k2 θ σ2 h => (G3 k1 σ1 k2 θ σ2 h).1) (fun k3 τ y y' hy hy' hE => (G1L k3 τ y y' hy hy' hE).1)
    (fun k1 σ1 k2 ρ' X' h => hIHA k1 σ1 _ _ (hw k1 σ1).1 k2 ρ' X' h)
  have LCgen := lineConst_of hW A2 hXA (fun k1 σ1 k2 θ σ2 h => (G3 k1 σ1 k2 θ σ2 h).1)
  -- the endpoint `T(1)`
  let ι1 : ISub k (k + 1) := ISub.cons .one trivial (ISub.id k)
  have hR1' : RedT S k (T.isub ι1) (.sigma A1 B1) := by rw [isub_cons_id_of_closed hTc]; exact hR1
  obtain ⟨hA1e, hB1e⟩ : A2 k ι1 = A1 ∧ B2 k ι1 = B1 := by
    have := RedW.unique (hw k ι1).1.1 hR1'.1; injection this; constructor <;> assumption
  have Aend : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A2 k' (ISub.cons .one trivial ρ)) ∧
      ∀ a a', RE2 S k' (A1.isub ρ) a a' → RT2 S k' ((B1.isub ρ).inst a) ((B2 k' (ISub.cons .one trivial ρ)).inst a') := by
    intro k' ρ; rw [← hA1e, ← hB1e]; exact G3 k ι1 k' ρ _ (cons_one_comp ρ)
  have Apt : ∀ k' (ρ : ISub k' k) (e : I) (he : e.Scoped k'),
      RT2 S k' ((A2 (k' + 1) ρ.up).dinst e) (A2 k' (ISub.cons e he ρ)) ∧
      ∀ a a', RE2 S k' ((A2 (k' + 1) ρ.up).dinst e) a a' →
        RT2 S k' (((B2 (k' + 1) ρ.up).dinst e).inst a) ((B2 k' (ISub.cons e he ρ)).inst a') := by
    intro k' ρ e he
    obtain ⟨l, hsig⟩ := sigmaW_typed hW (hTK _ ρ.up) (hw _ ρ.up).1
    have hcl := closed_of_ty hW hsig
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    rw [← isub_cons_id_of_closed hcl.1 e he, ← isub_cons_id_of_closed hcl.2 e he]
    exact G3 (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id])
  have Apt' : ∀ k' (ρ : ISub k' k) (e : I) (he : e.Scoped k'),
      RT2 S k' ((A2' (k' + 1) ρ.up).dinst e) (A2' k' (ISub.cons e he ρ)) ∧
      ∀ a a', RE2 S k' ((A2' (k' + 1) ρ.up).dinst e) a a' →
        RT2 S k' (((B2' (k' + 1) ρ.up).dinst e).inst a) ((B2' k' (ISub.cons e he ρ)).inst a') := by
    intro k' ρ e he
    obtain ⟨l, hsig⟩ := sigmaW_typed hW (Comp2_ty_base (RT2.isub hW hXT hTT ρ.up)).2.2.1 (hw _ ρ.up).2.1
    have hcl := closed_of_ty hW hsig
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    rw [← isub_cons_id_of_closed hcl.1 e he, ← isub_cons_id_of_closed hcl.2 e he]
    exact G3' (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id])
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hT0 : ∀ {k3 : ℕ} (σ : ISub k3 k), (T.dinst .zero).isub σ = T.isub (ISub.cons .zero trivial σ) := fun σ => by
    rw [isub_dinst]; exact isub_up_dinst T σ .zero trivial
  have hXA1 : TyCode k (semK S k A1) := by rw [← hA1e]; exact hXA _ _
  have hA1K : IsTyK S k A1 := isTyK_of_ty hW (RE2.typed FST).1
  have hXA1ρ : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' (A1.isub ρ)) := fun k' ρ => by
    rw [semK_isubTy hW hA1K ρ]; exact hXA1.res _
  have hA1A1 : RT2 S k A1 A1 := by
    have := (hw k ι1).2.2.1; rw [hA1e] at this; exact RT2.refl hW hXA1 this
  have hA1ρ : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A1.isub ρ) := fun k' ρ => RT2.isub hW hXA1 hA1A1 ρ
  -- the first projections
  have Fρ : ∀ k' (ρ : ISub k' k), RE2 S k' (A1.isub ρ) ((Tm.fst (.transp T φ a0)).isub ρ)
      ((Tm.fst (.transp T' φ' a0')).isub ρ) := fun k' ρ => RE2.isub hW FST ρ
  have Fs : ∀ k' (ρ : ISub k' k), RE2 S k' (A1.isub ρ) ((Tm.fst (.transp T φ a0)).isub ρ)
      ((Tm.fst (.transp T φ a0)).isub ρ) := fun k' ρ =>
    RE2.trans hW (hA1ρ k' ρ) (Fρ k' ρ) (RE2.symm hW (hA1ρ k' ρ) (Fρ k' ρ))
  -- the codomain of the endpoint at related arguments
  have hB11 : ∀ k' (ρ : ISub k' k) a a', RE2 S k' (A1.isub ρ) a a' →
      RT2 S k' ((B1.isub ρ).inst a) ((B1.isub ρ).inst a') := by
    intro k' ρ a a' h
    have h' := RE2.trans hW (hA1ρ k' ρ) (RE2.symm hW (hA1ρ k' ρ) h) h
    have c1 := (Aend k' ρ).2 a a' h
    have c2 := (Aend k' ρ).2 a' a' h'
    have u := hBpt k' _ _ (RE2.typed (RE2.conv hW (Aend k' ρ).1 h)).2.1
    exact RT2.trans hW (RT2.tyCode_l hW c1 u) c1 (RT2.symm hW (RT2.tyCode_l hW c2 u) c2)
  -- the type of the second projections
  have ht0 : HasTy S k .one [] (.snd (.transp T φ a0)) (B1.inst (.fst (.transp T φ a0))) :=
    HasTy.snd (hty.tyConv hR1.2)
  have hX : TyCode k (semK S k (B1.inst (.fst (.transp T φ a0)))) := tyCode_of_ty hW ht0
  have hYY : RT2 S k (B1.inst (.fst (.transp T φ a0))) (B1.inst (.fst (.transp T φ a0))) := by
    have hFF : RE2 S k (A2 k ι1) (.fst (.transp T φ a0)) (.fst (.transp T φ a0)) := by
      rw [hA1e]; exact RE2.trans hW hA1A1 FST (RE2.symm hW hA1A1 FST)
    have := (hw k ι1).2.2.2 _ _ hFF
    rw [hB1e] at this; exact RT2.refl hW hX this
  -- typings at restrictions
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty ρ; rwa [isub_dinst] at this
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ))
      ((T'.isub ρ.up).dinst .one) := fun k' ρ => by
    have := (HasTy.isubS hW hty' ρ).tyConv ((tyEq_dinst hW hP.tyEq (r := .one) trivial).isub hW ρ)
    rwa [isub_dinst] at this
  have eTF : ∀ k' (ρ : ISub k' k), TyEq S k' ((T.isub ρ.up).dinst .one) (.sigma (A1.isub ρ) (B1.isub ρ)) := by
    intro k' ρ; have := hR1.2.isub hW ρ; rw [isub_dinst, isub_sigma] at this; exact this
  have Cd1 : ∀ k' (ρ : ISub k' k), RT2 S k' ((A2 (k' + 1) ρ.up).dinst .one) (A1.isub ρ) := fun k' ρ =>
    RT2.trans hW (RT2.tyCode_l hW (Apt k' ρ .one trivial).1 (hXA _ _)) (Apt k' ρ .one trivial).1
      (RT2.symm hW (hXA1ρ k' ρ) (Aend k' ρ).1)
  have Cd1s : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) ((A2 (k' + 1) ρ.up).dinst .one) := fun k' ρ =>
    RT2.symm hW (RT2.tyCode_l hW (Cd1 k' ρ) (hXA1ρ _ _)) (Cd1 k' ρ)
  -- the bases, at the domains
  have a0e : ∀ k' (ρ : ISub k' k), RE2 S k' (A2 k' (ISub.cons .zero trivial ρ)) (.fst (a0.isub ρ)) (.fst (a0'.isub ρ)) ∧
      RE2 S k' ((B2 k' (ISub.cons .zero trivial ρ)).inst (.fst (a0.isub ρ))) (.snd (a0.isub ρ)) (.snd (a0'.isub ρ)) := by
    intro k' ρ
    have h0 := RE2.isub hW ha0 ρ
    rw [hT0] at h0
    exact hP.elim k' _ _ _ _ _ (hw k' _).1 h0
  have a0s : ∀ k' (ρ : ISub k' k), RE2 S k' (A2 k' (ISub.cons .zero trivial ρ)) (.fst (a0.isub ρ)) (.fst (a0.isub ρ)) :=
    fun k' ρ => RE2.trans hW (hw _ _).2.2.1 (a0e k' ρ).1 (RE2.symm hW (hw _ _).2.2.1 (a0e k' ρ).1)
  -- the first projection of the transport, against a transport of the first projection
  have Gfill : ∀ k3 (σ : ISub k3 k) k1 (σ1 : ISub k1 (k + 1)) (Θ1 : ISub (k3 + 1) k1) (y : I)
      (hy : y.Scoped (k3 + 1)), I.Eq y (.var 0) → σ1.comp Θ1 = ISub.cons y hy σ.up.tail → ∀ (ψ : I), ψ.Scoped k3 →
      I.Entails ψ (φ.subst σ.τ) → I.Entails (φ.subst σ.τ) ψ →
      HasTy S k3 .one [] (.transp ((A2 k1 σ1).isub Θ1) ψ (.fst (a0.isub σ))) (A1.isub σ) →
      LineConst S k3 ((A2 k1 σ1).isub Θ1) ψ →
      RE2 S k3 (A1.isub σ) ((Tm.fst (.transp T φ a0)).isub σ) (.transp ((A2 k1 σ1).isub Θ1) ψ (.fst (a0.isub σ))) := by
    intro k3 σ k1 σ1 Θ1 y hy hyE e1 ψ hψ hψ1 hψ2 htyX hLCX
    refine RE2.expandH hW (hA1ρ k3 σ) (RE2.typed (Fs k3 σ)).1 htyX fun k4 τ => ?_
    have hν : ((Tm.fst (.transp T φ a0)).isub σ).isub τ = .fst (.transp (T.isub (σ.comp τ).up)
        (φ.subst (σ.comp τ).τ) (a0.isub (σ.comp τ))) := by rw [Tm.isub_isub]; rfl
    have eX : (Tm.transp ((A2 k1 σ1).isub Θ1) ψ (.fst (a0.isub σ))).isub τ =
        .transp ((A2 k1 σ1).isub (Θ1.comp τ.up)) (ψ.subst τ.τ) (.fst (a0.isub (σ.comp τ))) := by
      show Tm.transp (((A2 k1 σ1).isub Θ1).isub τ.up) _ (.fst ((a0.isub σ).isub τ)) = _
      rw [Tm.isub_isub, Tm.isub_isub]
    have htyR := HasTy.isubS hW htyX τ
    rw [eX, Tm.isub_isub] at htyR
    rw [hν, eX, Tm.isub_isub]
    show ∃ u, Red S _ u ∧ EqTm S k4 .one [] _ u (A1.isub (σ.comp τ)) ∧ RE2 S k4 (A1.isub (σ.comp τ)) u _
    have hφν : I.Entails (φ.subst (σ.comp τ).τ) (ψ.subst τ.τ) := by rw [I_subst_comp]; exact ent_subst hψ2 _
    have hψν : I.Entails (ψ.subst τ.τ) (φ.subst (σ.comp τ).τ) := by rw [I_subst_comp]; exact ent_subst hψ1 _
    by_cases hf : I.Entails .one (φ.subst (σ.comp τ).τ)
    · refine ⟨.fst (a0.isub (σ.comp τ)), red_fst (.step (step_transp_face hf) (.refl _)),
        EqTm.fst ((EqTm.transpFace hf (hρT k4 _)).tyConv (eTF k4 _)), ?_⟩
      have hst := stable_transpFace hW (ent_trans hf hφν) htyR
      have hCν := hC k4 (σ.comp τ) .one trivial ((holds_iff_entails (I.scoped_subst hφs (σ.comp τ).sc)).2 hf)
      have hT1 := RT2.trans hW (hXTσ _ _) hCν (RT2.symm hW (hXTσ _ _) hCν)
      have h0 := RE2.isub hW ha0 (σ.comp τ)
      rw [hT0] at h0
      have h1 := RE2.conv' hW hCν h0 (hXTσ _ _)
      have el := (hP.elim k4 _ _ _ _ _ (hw k4 _).1 h1).1
      have hA := (hw k4 (ISub.cons .one trivial (σ.comp τ))).2.2.1
      have ell := RE2.trans hW hA el (RE2.symm hW hA el)
      have hf1 := RE2.conv' hW (Aend k4 _).1 ell (hXA1ρ _ _)
      exact RE2.expandR hW (hA1ρ k4 _) (RE2.typed hf1).1 htyR hst hf1
    · obtain ⟨a, b⟩ := fst_transp_sigma hW hf (hρT k4 _) (hw (k4 + 1) (σ.comp τ).up).1
      refine ⟨_, a, b.tyConv (tyB (Cd1 k4 _)), ?_⟩
      have hcl := closed_of_isTyK hW (Comp2_ty_base (hw (k4 + 1) (σ.comp τ).up).2.2.1).2.1
      have eL := isub_up_id_of_closed hcl
      have e1L : (σ.comp τ).up.comp (ISub.id k4).up =
          ISub.cons (.var 0) (show (0 : ℕ) < k4 + 1 by omega) (σ.comp τ).up.tail := by
        rw [← ISub.up_comp, ISub.comp_id, ISub.cons_var0_up_tail]
      have hyτ : (y.subst τ.up.τ).Scoped (k4 + 1) := I.scoped_subst hy τ.up.sc
      have e1R : σ1.comp (Θ1.comp τ.up) = ISub.cons (y.subst τ.up.τ) hyτ (σ.comp τ).up.tail := by
        rw [← ISub.comp_assoc, e1, ISub.cons_comp, ISub.up_tail_comp_up]
      have hEy : I.Eq (.var 0) (y.subst τ.up.τ) := I_eq_symm (I_eq_subst hyE _)
      have K := lkL (k4 + 1) k1 k4 (σ.comp τ).up σ1 (ISub.id k4).up (Θ1.comp τ.up) (σ.comp τ) (.var 0) _ _ hyτ
        hEy e1L e1R
      have hφνs : (φ.subst (σ.comp τ).τ).Scoped k4 := I.scoped_subst hφs (σ.comp τ).sc
      have LCL := LCgen (k4 + 1) k4 (σ.comp τ) (σ.comp τ).up (ISub.id k4).up (.var 0) _ e1L _ hφνs
        (fun k5 τ2 z hz he => by
          have hh2 := (holds_iff_entails (I.scoped_subst hφs ((σ.comp τ).comp τ2).sc)).2 (ent_comp_inv he)
          exact RT2.trans hW (hXA _ _) (G2 k5 _ z hz hh2).1 (RT2.symm hW (hXA _ _) (G2 k5 _ .zero trivial hh2).1))
      have htyL := transp_canon_typed hW (HasTy.eqR b)
      rw [← eL] at htyL
      have c1 := K.2.2.1 .one trivial
      have tL1 : TyEq S k4 (A1.isub (σ.comp τ))
          (((A2 (k4 + 1) (σ.comp τ).up).isub (ISub.id k4).up).dinst .one) :=
        TyEq.trans hW (tyB (Aend k4 _).1) (TyEq.symm (tyB c1))
      have htyR' := htyR.tyConv tL1
      have c0 := K.2.2.1 .zero trivial
      have hb := RE2.conv' hW c0 (a0s k4 _) (RT2.tyCode_l hW c0 (hXA _ _))
      have heqK := eqTm_transp_of hW htyL htyR' (tyB K.2.2.2.1) hφν hψν (RE2.typed hb).2.2
      have r := K.1 K.2.1 _ _ _ _ LCL htyL htyR' heqK hφν hψν hb
      have tr := RT2.trans hW (RT2.tyCode_l hW c1 (hXA _ _)) c1 (RT2.symm hW (hXA1ρ _ _) (Aend k4 _).1)
      rw [eL] at r tr
      exact RE2.conv hW tr r
  -- the transport fillers of the first projections
  let aL : ∀ k' (_ : ISub k' k), Tm := fun k' ρ => Tm.transpFill (A2 (k' + 1) ρ.up) (φ.subst ρ.τ) (.fst (a0.isub ρ))
  let aR : ∀ k' (_ : ISub k' k), Tm := fun k' ρ => Tm.transpFill (A2' (k' + 1) ρ.up) (φ'.subst ρ.τ) (.fst (a0'.isub ρ))
  have hyA : ∀ {k3 : ℕ} (x : I), x.Scoped k3 → (I.and x.shift (.var 0)).Scoped (k3 + 1) :=
    fun x hx => ⟨KubusCore.I.scoped_shift hx, (show (0 : ℕ) < _ by omega)⟩
  have apt : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      (aL k' ρ).isub (ISub.cons x hx τ) = .transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyA x hx) τ.up.tail))
        (.or (φ.subst (ρ.comp τ).τ) (.neg x)) (.fst (a0.isub (ρ.comp τ))) := by
    intro k' ρ k3 τ x hx
    show Tm.transp (((A2 (k' + 1) ρ.up).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons x hx τ).up)
      ((I.or (φ.subst ρ.τ).shift (.neg (.var 0))).subst (ISub.cons x hx τ).τ)
      (((Tm.fst (a0.isub ρ)).dshift).isub (ISub.cons x hx τ)) = _
    rw [isub_bindAnd, dshift_isub_cons]
    congr 1
    · show I.or (((φ.subst ρ.τ).shift).subst (ISub.cons x hx τ).τ) (.neg x) = _
      rw [I_shift_cons, ← I_subst_comp]
    · show Tm.fst ((a0.isub ρ).isub τ) = _; rw [Tm.isub_isub]
  have apt' : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      (aR k' ρ).isub (ISub.cons x hx τ) = .transp ((A2' (k' + 1) ρ.up).isub (ISub.cons _ (hyA x hx) τ.up.tail))
        (.or (φ'.subst (ρ.comp τ).τ) (.neg x)) (.fst (a0'.isub (ρ.comp τ))) := by
    intro k' ρ k3 τ x hx
    show Tm.transp (((A2' (k' + 1) ρ.up).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons x hx τ).up)
      ((I.or (φ'.subst ρ.τ).shift (.neg (.var 0))).subst (ISub.cons x hx τ).τ)
      (((Tm.fst (a0'.isub ρ)).dshift).isub (ISub.cons x hx τ)) = _
    rw [isub_bindAnd, dshift_isub_cons]
    congr 1
    · show I.or (((φ'.subst ρ.τ).shift).subst (ISub.cons x hx τ).τ) (.neg x) = _
      rw [I_shift_cons, ← I_subst_comp]
    · show Tm.fst ((a0'.isub ρ).isub τ) = _; rw [Tm.isub_isub]
  have taL : ∀ k' (ρ : ISub k' k), HasTy S (k' + 1) .one [] (aL k' ρ) (A2 (k' + 1) ρ.up) := fun k' ρ =>
    transpSigma_fill_typed hW (hρT k' ρ) (hw (k' + 1) ρ.up).1
  have taR : ∀ k' (ρ : ISub k' k), HasTy S (k' + 1) .one [] (aR k' ρ) (A2' (k' + 1) ρ.up) := fun k' ρ =>
    transpSigma_fill_typed hW (hρT' k' ρ) (hw (k' + 1) ρ.up).2.1
  have tA : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      HasTy S k3 .one [] (.transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyA x hx) τ.up.tail))
        (.or (φ.subst (ρ.comp τ).τ) (.neg x)) (.fst (a0.isub (ρ.comp τ))))
        (((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyA x hx) τ.up.tail)).dinst .one) := by
    intro k' ρ k3 τ x hx
    have h := HasTy.isubS hW (taL k' ρ) (ISub.cons x hx τ)
    rw [apt] at h; exact transp_canon_typed hW h
  have tA' : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      HasTy S k3 .one [] (.transp ((A2' (k' + 1) ρ.up).isub (ISub.cons _ (hyA x hx) τ.up.tail))
        (.or (φ'.subst (ρ.comp τ).τ) (.neg x)) (.fst (a0'.isub (ρ.comp τ))))
        (((A2' (k' + 1) ρ.up).isub (ISub.cons _ (hyA x hx) τ.up.tail)).dinst .one) := by
    intro k' ρ k3 τ x hx
    have h := HasTy.isubS hW (taR k' ρ) (ISub.cons x hx τ)
    rw [apt'] at h; exact transp_canon_typed hW h
  -- the type of the right second projection
  have hB1f : RT2 S k (B1.inst (.fst (.transp T φ a0))) (B1.inst (.fst (.transp T' φ' a0'))) := by
    have := hB11 k (ISub.id k) _ _ (Fρ k (ISub.id k))
    have hB1c : B1.isub (ISub.id k) = B1 := by
      obtain ⟨l, hsig⟩ := sigmaW_typed hW (isTyK_of_ty hW hty) hR1
      have hcl := closed_of_ty hW hsig
      simp only [Tm.closedB, Bool.and_eq_true] at hcl
      exact isub_id_of_closed hcl.2
    rwa [hB1c, isub_id_of_closed (closed_of_ty hW (RE2.typed FST).1),
      isub_id_of_closed (closed_of_ty hW (RE2.typed FST).2.1)] at this
  have hYK : IsTyK S k (B1.inst (.fst (.transp T φ a0))) := (Comp2_ty_base hYY).2.1
  have hXY : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' ((B1.inst (.fst (.transp T φ a0))).isub ρ)) := fun k' ρ => by
    rw [semK_isubTy hW hYK ρ]; exact hX.res _
  have hfinG : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst ρ.τ) →
      RE2 S k' ((B1.inst (.fst (.transp T φ a0))).isub ρ) (.snd (a0.isub ρ)) (.snd (a0'.isub ρ)) := by
    intro k' ρ hf
    have h0 := RE2.isub hW ha0 ρ
    rw [hT0] at h0
    have hCρ := hC k' ρ .one trivial ((holds_iff_entails (I.scoped_subst hφs ρ.sc)).2 hf)
    have h1 := RE2.conv' hW hCρ h0 (hXTσ _ _)
    have el := hP.elim k' _ _ _ _ _ (hw k' _).1 h1
    have hA := (hw k' (ISub.cons .one trivial ρ)).2.2.1
    have ell := RE2.trans hW hA el.1 (RE2.symm hW hA el.1)
    have hrefl := RE2.conv' hW (Aend k' ρ).1 ell (hXA1ρ _ _)
    have hst := stable_fst_transpFace hW hf (hρT k' ρ) (eTF k' ρ)
    have hfa := RE2.expandL hW (hA1ρ k' ρ) (RE2.typed (Fs k' ρ)).1 (RE2.typed hrefl).1 hst hrefl
    have c := (Aend k' ρ).2 _ _ hfa
    rw [← isub_inst] at c
    exact RE2.conv' hW c el.2 (hXY k' ρ)
  have upΘ : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (y : I) (hy : y.Scoped (k3 + 1)),
      ρ.up.comp (ISub.cons y hy τ.up.tail) = ISub.cons y hy (ρ.comp τ).up.tail := by
    intro k' ρ k3 τ y hy; rw [ISub.up_comp_cons, ISub.comp_up_tail]
  have nen1 : ¬ I.Entails .one (I.neg .one) := by decide
  have hbb : ∀ {k3 : ℕ}, (I.and (.var 1) (.var 0)).Scoped (k3 + 2) :=
    fun {k3} => ⟨show 1 < k3 + 2 by omega, show 0 < k3 + 2 by omega⟩
  have acr : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), RE2 S (k'' + 1) (A2 (k'' + 1) (ρ.comp ρ').up)
      ((aL k' ρ).isub ρ'.up) (aR k'' (ρ.comp ρ')) := by
    intro k' ρ k'' ρ'
    have eL : (aL k' ρ).isub ρ'.up = .transp ((A2 (k' + 1) ρ.up).isub (ISub.cons (.and (.var 1) (.var 0)) hbb ρ'.up.tail.up.tail))
        (.or (φ.subst (ρ.comp ρ').τ).shift (.neg (.var 0))) (Tm.fst (a0.isub (ρ.comp ρ'))).dshift := by
      show Tm.transp (((A2 (k' + 1) ρ.up).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub ρ'.up.up)
        ((I.or (φ.subst ρ.τ).shift (.neg (.var 0))).subst ρ'.up.τ) (((Tm.fst (a0.isub ρ)).dshift).isub ρ'.up) = _
      rw [isub_bindAnd_up, isub_dshift]
      congr 1
      · show I.or (((φ.subst ρ.τ).shift).subst (I.up ρ'.τ)) (.neg (.var 0)) = _
        rw [I_shift_subst_up, I_subst_comp]
      · show (Tm.fst ((a0.isub ρ).isub ρ')).dshift = _
        rw [Tm.isub_isub]
    have hclR := closed_of_isTyK hW (Comp2_ty_base (hw (k'' + 1) (ρ.comp ρ').up).2.2.1).2.2.1
    have eR : aR k'' (ρ.comp ρ') = .transp ((A2' (k'' + 1) (ρ.comp ρ').up).isub
        (ISub.cons (.and (.var 1) (.var 0)) hbb (ISub.id k'').up.tail.up.tail)) (.or (φ'.subst (ρ.comp ρ').τ).shift (.neg (.var 0)))
        (Tm.fst (a0'.isub (ρ.comp ρ'))).dshift := by
      show Tm.transp ((A2' (k'' + 1) (ρ.comp ρ').up).dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) _ _ = _
      rw [dsubst_bindAnd_closed hclR]
    have e1 : ρ.up.comp (ISub.cons (.and (.var 1) (.var 0)) hbb ρ'.up.tail.up.tail) = ISub.cons (.and (.var 1) (.var 0)) hbb (ρ.comp ρ').up.tail.up.tail := by
      rw [ISub.up_comp_cons, ISub.comp_up_tail, ISub.comp_up_tail]
    have e1' : (ρ.comp ρ').up.comp (ISub.cons (.and (.var 1) (.var 0)) hbb (ISub.id k'').up.tail.up.tail) =
        ISub.cons (.and (.var 1) (.var 0)) hbb (ρ.comp ρ').up.tail.up.tail := by
      rw [ISub.up_comp_cons, ISub.comp_up_tail, ISub.comp_up_tail, ISub.comp_id]
    have lk := lk (k' + 1) (k'' + 1) (k'' + 1) ρ.up (ρ.comp ρ').up _ _ (ρ.comp ρ').up.tail _ _ hbb hbb
      (I_eq_refl _) e1 e1'
    -- the typings
    have hty1 := HasTy.isubS hW (taL k' ρ) ρ'.up
    rw [eL] at hty1
    replace hty1 := transp_canon_typed hW hty1
    rw [eL]
    have hty2 := taR k'' (ρ.comp ρ')
    rw [eR] at hty2
    have hty2' := (transp_canon_typed hW hty2).tyConv (TyEq.symm (tyEq_dinst hW (tyB lk.2.2.2.1) (r := .one) trivial))
    rw [eR]
    -- the base
    have b0 := lk.2.2.1 .zero trivial
    have g0 := (G1L (k'' + 1) (ρ.comp ρ').up.tail _ .zero (I.scoped_subst hbb (ISub.cons .zero trivial
      (ISub.id (k'' + 1))).sc) trivial (ieq_and_zero_right _)).1
    have hv0 := (a0e (k'' + 1) (ρ.comp ρ').up.tail).1
    rw [isub_up_tail_eq, isub_up_tail_eq] at hv0
    have hbase := RE2.conv' hW (RT2.trans hW (RT2.tyCode_l hW b0 (hXA _ _)) b0 g0) hv0 (RT2.tyCode_l hW b0 (hXA _ _))
    have h12' : I.Entails (I.or (φ.subst (ρ.comp ρ').τ).shift (.neg (.var 0))) (I.or (φ'.subst (ρ.comp ρ').τ).shift (.neg (.var 0))) :=
      ent_or_elim (ent_trans (ent_shift (ent_subst h12 _)) (ent_or_left _ _)) (ent_or_right _ _)
    have h21' : I.Entails (I.or (φ'.subst (ρ.comp ρ').τ).shift (.neg (.var 0))) (I.or (φ.subst (ρ.comp ρ').τ).shift (.neg (.var 0))) :=
      ent_or_elim (ent_trans (ent_shift (ent_subst h21 _)) (ent_or_left _ _)) (ent_or_right _ _)
    have heqw := eqTm_transp_of hW hty1 hty2' (tyB lk.2.2.2.1) h12' h21' (RE2.typed hbase).2.2
    -- the constancy of the line
    have hsF : (I.or (φ.subst (ρ.comp ρ').τ).shift (.neg (.var 0))).Scoped (k'' + 1) :=
      ⟨KubusCore.I.scoped_shift (I.scoped_subst hφs (ρ.comp ρ').sc), show 0 < k'' + 1 by omega⟩
    have LC := LCgen (k' + 1) (k'' + 1) (ρ.comp ρ').up.tail ρ.up _ _ hbb e1 _ hsF (fun k4 τ2 z hz he => by
      rcases ent_or_cases (I.scoped_subst (KubusCore.I.scoped_shift (I.scoped_subst hφs (ρ.comp ρ').sc)) τ2.sc)
        (I.scoped_subst (show (I.neg (.var 0)).Scoped (k'' + 1) from show 0 < k'' + 1 by omega) τ2.sc) he with h | h
      · rw [shift_subst_comp] at h
        have hh2 := (holds_iff_entails (I.scoped_subst hφs (((ρ.comp ρ').up.tail).comp τ2).sc)).2 h
        have gz := G2 k4 _ _ (I.scoped_subst hbb (ISub.cons z hz τ2).sc) hh2
        have g0 := G2 k4 _ _ (I.scoped_subst hbb (ISub.cons .zero trivial τ2).sc) hh2
        exact RT2.trans hW (hXA _ _) gz.1 (RT2.symm hW (hXA _ _) g0.1)
      · have e1 : I.Eq (τ2.τ 0) .zero :=
          ieq_zero_of_holds_neg (I.scoped_subst (show (I.var 0).Scoped (k'' + 1) from show 0 < k'' + 1 by omega) τ2.sc)
            (entails_holds h (ρ := idEnv k4) (by rw [ival_one]; rfl))
        exact (G1L k4 _ _ _ _ _ (I_eq_trans (ieq_and_zero_left _ e1) (I_eq_symm (ieq_and_zero_left _ e1)))).1)
    have r := lk.1 lk.2.1 _ _ _ _ LC hty1 hty2' heqw h12' h21' hbase
    have c1 := lk.2.2.1 .one trivial
    have eid : I.Eq (((ISub.id (k'' + 1)).τ 0).and .one) (.var 0) := by
      have : (ISub.id (k'' + 1)).τ 0 = .var 0 := by simp [ISub.id]
      rw [this]; exact ieq_and_one_right _
    have g1 := (G1L (k'' + 1) (ρ.comp ρ').up.tail _ (.var 0) (I.scoped_subst hbb (ISub.cons .one trivial
      (ISub.id (k'' + 1))).sc) (show 0 < k'' + 1 by omega) eid).1
    rw [ISub.cons_var0_up_tail] at g1
    exact RE2.conv hW (RT2.trans hW (RT2.tyCode_l hW c1 (hXA _ _)) c1 g1) r
  have H := kanT2_elim_core hW (fun k' ρ x => .snd x) (fun k' ρ x => .snd x)
    (fun k' ρ => (B2 (k' + 1) ρ.up).inst (aL k' ρ)) (fun k' ρ => (B2' (k' + 1) ρ.up).inst (aR k' ρ))
    (fun k' ρ => .snd (a0.isub ρ)) (fun k' ρ => .snd (a0'.isub ρ))
    hX hYY ht0 ((HasTy.snd (hty'.tyConv hR1.2)).tyConv (TyEq.symm (tyB hB1f))) (EqTm.snd (heq.tyConv hR1.2))
    (fun k' ρ k'' ρ' x => rfl) (fun k' ρ k'' ρ' x => rfl)
    (fun k' ρ => ⟨fun hf => ?_, fun hf => ?_⟩) (fun k' ρ => ⟨fun hf => ?_, fun hf => ?_⟩) (fun k' ρ hf => ?_)
    (fun k' ρ k'' ρ' _ hf2 => ?_)
    (fun k' ρ k'' ρ' hnf => ?_) (fun k' ρ k'' ρ' hnf => ?_) (fun k' ρ k'' ρ' hnf => ?_) (fun k' ρ k'' ρ' hnf => ?_)
    (fun k' ρ k'' ρ' hnf => ?_) h12 h21
  · exact H
  · exact ⟨red_snd (.step (step_transp_face hf) (.refl _)), by
      rw [isub_inst]; exact EqTm.snd ((EqTm.transpFace hf (hρT k' ρ)).tyConv (eTF k' ρ))⟩
  · obtain ⟨a, b⟩ := snd_transp_sigma hW hf (hρT k' ρ) (hw (k' + 1) ρ.up).1
    refine ⟨a, b.tyConv ?_⟩
    rw [isub_inst]
    have c1 := (Apt k' ρ .one trivial).2 _ _ (RE2.conv hW (Cd1s k' ρ) (Fs k' ρ))
    have c2 := (Aend k' ρ).2 _ _ (Fs k' ρ)
    exact TyEq.trans hW (tyB c1) (TyEq.symm (tyB c2))
  · have eT : TyEq S k' ((T'.isub ρ.up).dinst .one) ((T.isub ρ.up).dinst .one) := by
      have := (tyEq_dinst hW hP.tyEq (r := .one) trivial).isub hW ρ
      rw [isub_dinst, isub_dinst] at this; exact TyEq.symm this
    refine ⟨red_snd (.step (step_transp_face hf) (.refl _)), ?_⟩
    have e := EqTm.snd ((EqTm.transpFace hf (hρT' k' ρ)).tyConv (TyEq.trans hW eT (eTF k' ρ)))
    have hBρ := RT2.isub hW hX hB1f ρ
    rw [isub_inst, isub_inst] at hBρ
    rw [isub_inst]
    exact e.tyConv (TyEq.symm (tyB hBρ))
  · obtain ⟨a, b⟩ := snd_transp_sigma hW hf (hρT' k' ρ) (hw (k' + 1) ρ.up).2.1
    refine ⟨a, b.tyConv ?_⟩
    rw [isub_inst]
    have hF' : RE2 S k' (A1.isub ρ) ((Tm.fst (.transp T' φ' a0')).isub ρ) ((Tm.fst (.transp T' φ' a0')).isub ρ) :=
      RE2.trans hW (hA1ρ k' ρ) (RE2.symm hW (hA1ρ k' ρ) (Fρ k' ρ)) (Fρ k' ρ)
    have r1 := (Aend k' ρ).1
    have r2 := (hw k' (ISub.cons .one trivial ρ)).2.2.1
    have r3 := (Apt' k' ρ .one trivial).1
    have t3 := RT2.tyCode_l hW r3 (RT2.tyCode_r hW r2 (hXA _ _))
    have tt := RT2.trans hW (hXA1ρ _ _) r1 (RT2.trans hW (hXA _ _) r2 (RT2.symm hW t3 r3))
    have c1 := (Apt' k' ρ .one trivial).2 _ _ (RE2.conv hW tt hF')
    have c2 := (hw k' (ISub.cons .one trivial ρ)).2.2.2 _ _ (RE2.conv hW r1 (Fρ k' ρ))
    have c3 := (Aend k' ρ).2 _ _ (Fs k' ρ)
    exact TyEq.trans hW (tyB c1) (TyEq.trans hW (TyEq.symm (tyB c2)) (TyEq.symm (tyB c3)))
  · exact hfinG k' ρ hf
  · show RE2 S k'' _ (.snd ((a0.isub ρ).isub ρ')) _
    rw [Tm.isub_isub]; exact hfinG k'' _ hf2
  · -- the eliminated lines at their ends
    show RT2 S k'' ((((B2 (k' + 1) ρ.up).inst (aL k' ρ)).isub ρ'.up).dinst .one) _
    rw [isub_up_dinst _ ρ' .one trivial, isub_inst, apt]
    have gL := G3 (k' + 1) ρ.up k'' (ISub.cons .one trivial ρ') (ISub.cons .one trivial (ρ.comp ρ'))
      (ISub.up_comp_cons ρ .one trivial ρ')
    have hXg := RT2.tyCode_l hW gL.1 (hXA _ _)
    have e1 := upΘ k' ρ k'' ρ' _ (hyA .one trivial)
    have K := lkL (k' + 1) (k' + 1) k'' ρ.up ρ.up _ _ (ρ.comp ρ') _ _ (hyA .one trivial) (hyA .one trivial)
      (I_eq_refl _) e1 e1
    have hψs : (I.or (φ.subst (ρ.comp ρ').τ) (.neg .one)).Scoped k'' := ⟨I.scoped_subst hφs (ρ.comp ρ').sc, trivial⟩
    have hEy : I.Eq (I.and I.one.shift (.var 0)) (.var 0) := fun ρ0 => by
      have : (I.one.shift : I) = .one := rfl
      rw [this]; simp only [I.eval]; cases ρ0 0 <;> rfl
    have c1 := K.2.2.1 .one trivial
    have g1 := (G1L k'' (ρ.comp ρ') _ .one (I.scoped_subst (hyA .one trivial) (ISub.cons .one trivial
      (ISub.id k'')).sc) trivial (fun ρ0 => by simp only [I.eval]; rfl)).1
    have tX := RT2.trans hW (RT2.tyCode_l hW c1 (hXA _ _)) c1
      (RT2.trans hW (hXA _ _) g1 (RT2.symm hW (hXA1ρ _ _) (Aend k'' _).1))
    have htyX := (tA k' ρ k'' ρ' .one trivial).tyConv (tyB tX)
    have LCX := LCgen (k' + 1) k'' (ρ.comp ρ') ρ.up _ _ (hyA .one trivial) e1 _ hψs (fun k4 τ2 z hz he => by
      rcases ent_or_cases (I.scoped_subst (I.scoped_subst hφs (ρ.comp ρ').sc) τ2.sc)
        (show ((I.neg .one).subst τ2.τ).Scoped k4 from trivial) he with h | h
      · have hh2 := (holds_iff_entails (I.scoped_subst hφs ((ρ.comp ρ').comp τ2).sc)).2
          (ent_comp_inv (ρ := ρ.comp ρ') (ρ' := τ2) h)
        exact RT2.trans hW (hXA _ _) (G2 k4 _ _ (I.scoped_subst (hyA .one trivial) (ISub.cons z hz τ2).sc) hh2).1
          (RT2.symm hW (hXA _ _) (G2 k4 _ _ (I.scoped_subst (hyA .one trivial) (ISub.cons .zero trivial τ2).sc)
            hh2).1)
      · exact (nen1 h).elim)
    have hψ1 : I.Entails (I.or (φ.subst (ρ.comp ρ').τ) (.neg .one)) (φ.subst (ρ.comp ρ').τ) :=
      ent_or_elim (ent_refl _) (ent_trans (eq_ent (show I.Eq (I.neg .one) .zero from fun _ => rfl)) (ent_zero _))
    have G := Gfill k'' (ρ.comp ρ') (k' + 1) ρ.up _ _ (hyA .one trivial) hEy e1 _ hψs hψ1 (ent_or_left _ _) htyX LCX
    have tAA := RT2.trans hW (hXA1ρ _ _) (Aend k'' _).1 (RT2.symm hW hXg gL.1)
    have b := gL.2 _ _ (RE2.conv hW tAA (RE2.symm hW (hA1ρ _ _) G))
    have c3 := (Aend k'' (ρ.comp ρ')).2 _ _ (Fs k'' _)
    rw [isub_inst]
    exact RT2.trans hW (RT2.tyCode_l hW b (RT2.tyCode_r hW c3 (hXY _ _ |> fun h => by rw [isub_inst] at h; exact h)))
      b (RT2.symm hW (by have := hXY k'' (ρ.comp ρ'); rwa [isub_inst] at this) c3)
  · -- robustness of the eliminated lines
    intro k3 τ x x' hx hx' hEx
    show RT2 S k3 ((((B2 (k' + 1) ρ.up).inst (aL k' ρ)).isub ρ'.up).isub (ISub.cons x hx τ))
      (((B2' (k'' + 1) (ρ.comp ρ').up).inst (aR k'' (ρ.comp ρ'))).isub (ISub.cons x' hx' τ))
    rw [Tm.isub_isub, ISub.up_comp_cons, isub_inst, isub_inst, apt, apt']
    have eσ : (ρ.comp ρ').comp τ = ρ.comp (ρ'.comp τ) := ISub.comp_assoc _ _ _
    rw [eσ]
    have hEy : I.Eq (I.and x.shift (.var 0)) (I.and x'.shift (.var 0)) :=
      ieq_and_congr (fun ρ0 => by simp only [I.shift, eval_ren]; exact hEx _) (I_eq_refl _)
    have lkF := lk (k' + 1) (k'' + 1) k3 ρ.up (ρ.comp ρ').up _ _ (ρ.comp (ρ'.comp τ)) _ _ (hyA x hx) (hyA x' hx')
      hEy (upΘ k' ρ k3 (ρ'.comp τ) _ _) (by rw [upΘ, eσ])
    -- the transports of the argument are related
    have hty1 := tA k' ρ k3 (ρ'.comp τ) x hx
    have hty2 := tA' k'' (ρ.comp ρ') k3 τ x' hx'
    rw [eσ] at hty2
    have eX1 := tyEq_dinst hW (tyB lkF.2.2.2.1) (r := .one) trivial
    have hty2' := hty2.tyConv (TyEq.symm eX1)
    have h0X := lkF.2.2.1 .zero trivial
    have g0 := (G1L k3 (ρ.comp (ρ'.comp τ)) _ .zero (I.scoped_subst (hyA x hx) (ISub.cons .zero trivial (ISub.id k3)).sc)
      trivial (ieq_and_zero_right _)).1
    have t0 := RT2.trans hW (RT2.tyCode_l hW h0X (hXA _ _)) h0X g0
    have hbase := RE2.conv' hW t0 (a0e k3 (ρ.comp (ρ'.comp τ))).1 (RT2.tyCode_l hW h0X (hXA _ _))
    have hEn : I.Eq (I.neg x) (I.neg x') := fun ρ0 => by simp only [I.eval]; rw [hEx ρ0]
    have h12' : I.Entails (I.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) (.neg x))
        (I.or (φ'.subst (ρ.comp (ρ'.comp τ)).τ) (.neg x')) :=
      ent_or_elim (ent_trans (ent_subst h12 _) (ent_or_left _ _)) (ent_trans (eq_ent hEn) (ent_or_right _ _))
    have h21' : I.Entails (I.or (φ'.subst (ρ.comp (ρ'.comp τ)).τ) (.neg x'))
        (I.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) (.neg x)) :=
      ent_or_elim (ent_trans (ent_subst h21 _) (ent_or_left _ _))
        (ent_trans (eq_ent (I_eq_symm hEn)) (ent_or_right _ _))
    have heqw := eqTm_transp_of hW hty1 hty2' (tyB lkF.2.2.2.1) h12' h21' (RE2.typed hbase).2.2
    have r := lkF.1 lkF.2.1 _ _ _ _ ?_ hty1 hty2' heqw h12' h21' hbase
    · -- the codomains
      have h1X := lkF.2.2.1 .one trivial
      have eqx : I.Eq ((I.and x.shift (.var 0)).subst (ISub.cons .one trivial (ISub.id k3)).τ) x := by
        show I.Eq (I.and (x.shift.subst (ISub.cons .one trivial (ISub.id k3)).τ) .one) x
        rw [I_shift_cons, I_subst_id hx]; exact ieq_and_one_right x
      have g1 := (G1L k3 (ρ.comp (ρ'.comp τ)) _ x (I.scoped_subst (hyA x hx) (ISub.cons .one trivial (ISub.id k3)).sc)
        hx eqx).1
      have t1 := RT2.trans hW (RT2.tyCode_l hW h1X (hXA _ _)) h1X g1
      have rA := RE2.conv hW t1 r
      have gL := G3 (k' + 1) ρ.up k3 (ISub.cons x hx (ρ'.comp τ)) (ISub.cons x hx (ρ.comp (ρ'.comp τ)))
        (ISub.up_comp_cons ρ x hx _)
      have gR := G3' (k'' + 1) (ρ.comp ρ').up k3 (ISub.cons x' hx' τ) (ISub.cons x' hx' (ρ.comp (ρ'.comp τ)))
        (by rw [ISub.up_comp_cons, eσ])
      have gm := G1 k3 (ρ.comp (ρ'.comp τ)) x x' hx hx' hEx
      have hXL := RT2.tyCode_l hW gL.1 (hXA _ _)
      have rAA := RE2.trans hW (RT2.refl hW (hXA _ _) gm.1) rA (RE2.symm hW (RT2.refl hW (hXA _ _) gm.1) rA)
      have rA'A' := RE2.trans hW (RT2.refl hW (hXA _ _) gm.1) (RE2.symm hW (RT2.refl hW (hXA _ _) gm.1) rA) rA
      have hXR' := RT2.tyCode_r hW gm.1 (hXA _ _)
      have hXR := RT2.tyCode_l hW gR.1 hXR'
      have b1 := gL.2 _ _ (RE2.conv hW (RT2.symm hW hXL gL.1) rAA)
      have b2 := gm.2 _ _ rA
      have b3 := gR.2 _ _ (RE2.conv hW (RT2.symm hW hXR gR.1) (RE2.conv hW gm.1 rA'A'))
      have u2 := hBpt k3 _ _ (RE2.typed rA).1
      have u3 := hBpt' k3 _ _ (RE2.typed (RE2.conv hW gm.1 rA'A')).1
      exact RT2.trans hW (RT2.tyCode_l hW b1 u2) b1 (RT2.trans hW u2 b2 (RT2.symm hW (RT2.tyCode_l hW b3 u3) b3))
    · -- the constancy of the line of the argument
      intro k4 τ2 z hz hh
      rw [Tm.isub_isub, Tm.isub_isub]
      have d : ∀ (z : I) (hz : z.Scoped k4), RT2 S k4
          ((A2 (k' + 1) ρ.up).isub ((ISub.cons _ (hyA x hx) (ρ'.comp τ).up.tail).comp (ISub.cons z hz τ2)))
          (A2 k4 (ISub.cons ((I.and x.shift (.var 0)).subst (ISub.cons z hz τ2).τ)
            (I.scoped_subst (hyA x hx) (ISub.cons z hz τ2).sc) ((ρ.comp (ρ'.comp τ)).comp τ2))) := fun z hz =>
        (G3 (k' + 1) ρ.up k4 _ _ (by rw [← ISub.comp_assoc, upΘ, ISub.cons_comp, ISub.up_tail_comp_cons])).1
      have d1 := d z hz
      have d0 := d .zero trivial
      have hsc : (I.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) (.neg x)).Scoped k3 :=
        ⟨I.scoped_subst hφs (ρ.comp (ρ'.comp τ)).sc, hx⟩
      have he := (holds_iff_entails (I.scoped_subst hsc τ2.sc)).1 hh
      have mid : RT2 S k4 (A2 k4 (ISub.cons ((I.and x.shift (.var 0)).subst (ISub.cons z hz τ2).τ)
            (I.scoped_subst (hyA x hx) (ISub.cons z hz τ2).sc) ((ρ.comp (ρ'.comp τ)).comp τ2)))
          (A2 k4 (ISub.cons ((I.and x.shift (.var 0)).subst (ISub.cons .zero trivial τ2).τ)
            (I.scoped_subst (hyA x hx) (ISub.cons .zero trivial τ2).sc) ((ρ.comp (ρ'.comp τ)).comp τ2))) := by
        rcases ent_or_cases (I.scoped_subst hsc.1 τ2.sc) (I.scoped_subst (show (I.neg x).Scoped k3 from hx) τ2.sc) he with hφ2 | hx2
        · have hh2 : (ival (idEnv k4) (φ.subst ((ρ.comp (ρ'.comp τ)).comp τ2).τ)).holds :=
            (holds_iff_entails (I.scoped_subst hφs ((ρ.comp (ρ'.comp τ)).comp τ2).sc)).2 (ent_comp_inv hφ2)
          have gz := G2 k4 _ _ (I.scoped_subst (hyA x hx) (ISub.cons z hz τ2).sc) hh2
          have g0 := G2 k4 _ _ (I.scoped_subst (hyA x hx) (ISub.cons .zero trivial τ2).sc) hh2
          exact RT2.trans hW (hXA _ _) gz.1 (RT2.symm hW (hXA _ _) g0.1)
        · have e1 : I.Eq (x.subst τ2.τ) .zero :=
            ieq_zero_of_holds_neg (I.scoped_subst hx τ2.sc) (entails_holds hx2 (ρ := idEnv k4) (by rw [ival_one]; rfl))
          have ez : I.Eq ((I.and x.shift (.var 0)).subst (ISub.cons z hz τ2).τ) .zero := by
            show I.Eq (I.and (x.shift.subst (ISub.cons z hz τ2).τ) _) _
            rw [I_shift_cons]; exact ieq_and_zero_left _ e1
          have e0 : I.Eq ((I.and x.shift (.var 0)).subst (ISub.cons .zero trivial τ2).τ) .zero := by
            show I.Eq (I.and (x.shift.subst (ISub.cons .zero trivial τ2).τ) _) _
            rw [I_shift_cons]; exact ieq_and_zero_left _ e1
          exact (G1L k4 _ _ _ _ _ (I_eq_trans ez (I_eq_symm e0))).1
      exact RT2.trans hW (RT2.tyCode_l hW d1 (hXA _ _)) d1
        (RT2.trans hW (hXA _ _) mid (RT2.symm hW (RT2.tyCode_l hW d0 (hXA _ _)) d0))
  · -- constancy of the eliminated lines
    intro k3 τ x hx hh
    have hhσ : (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp τ)).τ)).holds := by
      rw [I_subst_comp, I_subst_comp]; exact hh
    have hφσ : I.Entails .one (φ.subst (ρ.comp (ρ'.comp τ)).τ) :=
      (holds_iff_entails (I.scoped_subst hφs (ρ.comp (ρ'.comp τ)).sc)).1 hhσ
    -- the transported argument at a point, against the argument
    have wrel : ∀ (z : I) (hz : z.Scoped k3),
        RE2 S k3 ((A2 (k' + 1) ρ.up).isub (ISub.cons z hz (ρ'.comp τ)))
          (.transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyA z hz) (ρ'.comp τ).up.tail))
            (.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) (.neg z)) (.fst (a0.isub (ρ.comp (ρ'.comp τ))))) (.fst (a0.isub (ρ.comp (ρ'.comp τ)))) ∧
        RE2 S k3 (A2 k3 (ISub.cons z hz (ρ.comp (ρ'.comp τ)))) (.fst (a0.isub (ρ.comp (ρ'.comp τ))))
          (.fst (a0.isub (ρ.comp (ρ'.comp τ)))) := by
      intro z hz
      have gz := G2 k3 (ρ.comp (ρ'.comp τ)) z hz hhσ
      have hvz := RE2.conv hW (RT2.symm hW (hXA _ _) gz.1) (a0s k3 _)
      have gL := G3 (k' + 1) ρ.up k3 (ISub.cons z hz (ρ'.comp τ)) (ISub.cons z hz (ρ.comp (ρ'.comp τ)))
        (ISub.up_comp_cons ρ z hz _)
      have hXL := RT2.tyCode_l hW gL.1 (hXA _ _)
      have lk := (lkL (k' + 1) (k' + 1) k3 ρ.up ρ.up _ _ (ρ.comp (ρ'.comp τ)) _ _ (hyA z hz) (hyA z hz)
        (I_eq_refl _) (upΘ k' ρ k3 (ρ'.comp τ) _ _) (upΘ k' ρ k3 (ρ'.comp τ) _ _)).2.2.1 .one trivial
      have eqz : I.Eq ((I.and z.shift (.var 0)).subst (ISub.cons .one trivial (ISub.id k3)).τ) z := by
        show I.Eq (I.and (z.shift.subst (ISub.cons .one trivial (ISub.id k3)).τ) .one) z
        rw [I_shift_cons, I_subst_id hz]; exact ieq_and_one_right z
      have gz' := (G1L k3 (ρ.comp (ρ'.comp τ)) _ z (I.scoped_subst (hyA z hz) (ISub.cons .one trivial (ISub.id k3)).sc)
        hz eqz).1
      have tX := RT2.trans hW (RT2.tyCode_l hW lk (hXA _ _)) lk (RT2.trans hW (hXA _ _) gz' (RT2.symm hW hXL gL.1))
      have htw := (tA k' ρ k3 (ρ'.comp τ) z hz).tyConv (tyB tX)
      have hst := stable_transpFace hW (ent_trans hφσ (ent_or_left _ _)) htw
      have hvL := RE2.conv hW (RT2.symm hW hXL gL.1) hvz
      exact ⟨RE2.expandL hW (RT2.refl hW hXL gL.1) htw (RE2.typed hvL).1 hst hvL, hvz⟩
    show RT2 S k3 ((((B2 (k' + 1) ρ.up).inst (aL k' ρ)).isub ρ'.up).isub (ISub.cons x hx τ))
      ((((B2 (k' + 1) ρ.up).inst (aL k' ρ)).isub ρ'.up).isub (ISub.cons .zero trivial τ))
    rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons, isub_inst, isub_inst, apt, apt]
    have gLx := G3 (k' + 1) ρ.up k3 (ISub.cons x hx (ρ'.comp τ)) (ISub.cons x hx (ρ.comp (ρ'.comp τ)))
      (ISub.up_comp_cons ρ x hx _)
    have gL0 := G3 (k' + 1) ρ.up k3 (ISub.cons .zero trivial (ρ'.comp τ)) (ISub.cons .zero trivial (ρ.comp (ρ'.comp τ)))
      (ISub.up_comp_cons ρ .zero trivial _)
    have bx := gLx.2 _ _ (wrel x hx).1
    have b0 := gL0.2 _ _ (wrel .zero trivial).1
    have gx := (G2 k3 (ρ.comp (ρ'.comp τ)) x hx hhσ).2 _ _ (wrel x hx).2
    have u := hBpt k3 _ _ (RE2.typed (wrel x hx).2).1
    have u0 := RT2.tyCode_r hW gx u
    exact RT2.trans hW (RT2.tyCode_l hW bx u) bx (RT2.trans hW u gx (RT2.symm hW (RT2.tyCode_l hW b0 u0) b0))
  · -- the eliminated bases
    show RE2 S k'' ((((B2 (k' + 1) ρ.up).inst (aL k' ρ)).isub ρ'.up).dinst .zero) (.snd ((a0.isub ρ).isub ρ'))
      (.snd (a0'.isub (ρ.comp ρ')))
    rw [isub_up_dinst _ ρ' .zero trivial, isub_inst, apt, Tm.isub_isub]
    have gL0 := G3 (k' + 1) ρ.up k'' (ISub.cons .zero trivial ρ') (ISub.cons .zero trivial (ρ.comp ρ'))
      (ISub.up_comp_cons ρ .zero trivial ρ')
    have hXL := RT2.tyCode_l hW gL0.1 (hXA _ _)
    have lk0 := (lkL (k' + 1) (k' + 1) k'' ρ.up ρ.up _ _ (ρ.comp ρ') _ _ (hyA .zero trivial) (hyA .zero trivial)
      (I_eq_refl _) (upΘ k' ρ k'' ρ' _ _) (upΘ k' ρ k'' ρ' _ _)).2.2.1 .one trivial
    have g0 := (G1L k'' (ρ.comp ρ') _ .zero (I.scoped_subst (hyA .zero trivial) (ISub.cons .one trivial (ISub.id k'')).sc)
      trivial (ieq_and_one_right _)).1
    have tX := RT2.trans hW (RT2.tyCode_l hW lk0 (hXA _ _)) lk0 (RT2.trans hW (hXA _ _) g0 (RT2.symm hW hXL gL0.1))
    have htw := (tA k' ρ k'' ρ' .zero trivial).tyConv (tyB tX)
    have hst := stable_transpFace hW (ent_trans (show I.Entails .one (I.neg .zero) by decide) (ent_or_right _ _)) htw
    have hvL := RE2.conv hW (RT2.symm hW hXL gL0.1) (a0s k'' (ρ.comp ρ'))
    have hw0 := RE2.expandL hW (RT2.refl hW hXL gL0.1) htw (RE2.typed hvL).1 hst hvL
    have b := gL0.2 _ _ hw0
    exact RE2.conv' hW b (a0e k'' (ρ.comp ρ')).2 (RT2.tyCode_l hW b (hBpt _ _ _ (RE2.typed (a0s k'' _)).1))
  · -- the induction hypothesis for the codomains
    have aLL : RE2 S (k' + 1) (A2 (k' + 1) ρ.up) (aL k' ρ) (aL k' ρ) := by
      have r := acr k' ρ k' (ISub.id k')
      have hcl := closed_of_ty hW (taL k' ρ)
      rw [ISub.comp_id, isub_up_id_of_closed hcl] at r
      have hA := (hw (k' + 1) ρ.up).2.2.1
      exact RE2.trans hW hA r (RE2.symm hW hA r)
    refine hIHB (k' + 1) ρ.up _ _ (hw _ ρ.up).1 (aL k' ρ) aLL k'' ρ'.up _ ?_
    rw [isub_inst]
    have wc := acr k' ρ k'' ρ'
    have g := G3 (k' + 1) ρ.up (k'' + 1) ρ'.up (ρ.comp ρ').up (ISub.up_comp ρ ρ').symm
    have hXg := RT2.tyCode_l hW g.1 (hXA _ _)
    have hA := (hw (k'' + 1) (ρ.comp ρ').up).2.2.1
    have wcc := RE2.trans hW hA wc (RE2.symm hW hA wc)
    have b1 := g.2 _ _ (RE2.conv hW (RT2.symm hW hXg g.1) wcc)
    have b2 := (hw (k'' + 1) (ρ.comp ρ').up).2.2.2 _ _ wc
    have u := hBpt _ _ _ (RE2.typed wc).1
    exact RT2.trans hW (RT2.tyCode_l hW b1 u) b1 b2


/-- Transport along related lines whose normal forms are Σ-types. -/
theorem kanT2_sigma {T T' A B : Tm} {l : ℕ} (hTT : RT2 S (k + 1) T T') (hR : RedT S (k + 1) T (.sigma A B))
    (hsig : HasTy S (k + 1) .one [] (.sigma A B) (.univ l))
    (hIHA : ∀ k1 (ρ : ISub k1 (k + 1)) A1 B1, RedT S k1 (T.isub ρ) (.sigma A1 B1) →
      ∀ k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) (A1.isub ρ') X' → KanT2 S k2 (A1.isub ρ') X')
    (hIHB : ∀ k1 (ρ : ISub k1 (k + 1)) A1 B1, RedT S k1 (T.isub ρ) (.sigma A1 B1) → ∀ b, RE2 S k1 A1 b b →
      ∀ k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) ((B1.inst b).isub ρ') X' → KanT2 S k2 ((B1.inst b).isub ρ') X') :
    KanT2 S k T T' := by
  have hP := SigmaStr_of hW hTT hR hsig
  intro hLR φ φ' a0 a0' hC hty hty' heq h12 h21 ha0
  obtain ⟨l0, ⟨hTl, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hXT : TyCode (k + 1) (semK S (k + 1) T) := tyCode_of_univ hW (minimal_to_spec hTl)
  have hT1K : IsTyK S k (T.dinst .one) := isTyK_of_ty hW hty
  obtain ⟨A1, B1, A1', B1', h1, -, -, -⟩ := hP.whnf k (ISub.cons .one trivial (ISub.id k))
  rw [isub_cons_id_of_closed hTc] at h1
  obtain ⟨l1, hsig1⟩ := sigmaW_typed hW hT1K h1
  have hX1 : TyCode k (semK S k (T.dinst .one)) := tyCode_of_ty hW hty
  have hTT1 : RT2 S k (T.dinst .one) (T.dinst .one) := by
    have := hLR k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rw [isub_cons_id_of_closed hTc] at this
    exact RT2.refl hW hX1 this
  refine RE2_sigmaW_intro hW hTT1 h1 hsig1 ⟨hty, hty', heq⟩ fun k' ρ A3 B3 h => ?_
  have hd1 : ∀ (X : Tm) (x : I), (X.dinst x).isub ρ = (X.isub ρ.up).dinst (x.subst ρ.τ) := fun X x => isub_dinst X x ρ
  rw [hd1] at h
  have htyρ := HasTy.isubS hW hty ρ
  have htyρ' := HasTy.isubS hW hty' ρ
  have heqρ := EqTm.isubS hW heq ρ
  have ha0ρ := RE2.isub hW ha0 ρ
  rw [hd1] at htyρ htyρ' heqρ ha0ρ
  have hIHAρ : ∀ k1 (ρ1 : ISub k1 (k' + 1)) A4 B4, RedT S k1 ((T.isub ρ.up).isub ρ1) (.sigma A4 B4) →
      ∀ k2 (ρ2 : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) (A4.isub ρ2) X' → KanT2 S k2 (A4.isub ρ2) X' := by
    intro k1 ρ1 A4 B4 h4 k2 ρ2 X' hX'
    rw [Tm.isub_isub] at h4
    exact hIHA k1 (ρ.up.comp ρ1) A4 B4 h4 k2 ρ2 X' hX'
  have hIHBρ : ∀ k1 (ρ1 : ISub k1 (k' + 1)) A4 B4, RedT S k1 ((T.isub ρ.up).isub ρ1) (.sigma A4 B4) →
      ∀ b, RE2 S k1 A4 b b → ∀ k2 (ρ2 : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) ((B4.inst b).isub ρ2) X' →
      KanT2 S k2 ((B4.inst b).isub ρ2) X' := by
    intro k1 ρ1 A4 B4 h4 b hb k2 ρ2 X' hX'
    rw [Tm.isub_isub] at h4
    exact hIHB k1 (ρ.up.comp ρ1) A4 B4 h4 b hb k2 ρ2 X' hX'
  exact ⟨kanT2_sigma_fst hW (RT2.isub hW hXT hTT ρ.up) (hP.isub hW ρ.up) (hLR.isub ρ) hIHAρ (hC.isub ρ)
      htyρ htyρ' heqρ (ent_subst h12 ρ.τ) (ent_subst h21 ρ.τ) ha0ρ h,
    kanT2_sigma_snd hW (RT2.isub hW hXT hTT ρ.up) (hP.isub hW ρ.up) (hLR.isub ρ) hIHAρ hIHBρ (hC.isub ρ)
      htyρ htyρ' heqρ (ent_subst h12 ρ.τ) (ent_subst h21 ρ.τ) ha0ρ h⟩

end

end Model.Whnf
