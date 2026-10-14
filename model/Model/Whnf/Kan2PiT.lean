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

omit hW in
theorem ISub.up_tail_comp_cons {k3 k4 : ℕ} (σ0 : ISub k3 k) (z : I) (hz : z.Scoped k4) (τ2 : ISub k4 k3) :
    (σ0.up.tail).comp (ISub.cons z hz τ2) = σ0.comp τ2 := by
  ext i
  show ((σ0.τ i).shift).subst (ISub.cons z hz τ2).τ = (σ0.τ i).subst τ2.τ
  rw [I_shift_cons]

omit hW in
theorem ISub.comp_up_tail {k3 : ℕ} (ρ : ISub k' k) (τ : ISub k3 k') : ρ.comp τ.up.tail = (ρ.comp τ).up.tail := by
  ext i
  show (ρ.τ i).subst (I.up τ.τ ∘ Nat.succ) = ((ρ.τ i).subst τ.τ).shift
  simp only [I.shift, I.ren, I_subst_subst]; rfl

omit hW in
theorem isub_bind2 {k3 : ℕ} (X : Tm) (x : I) (hx : x.Scoped k3) (τ : ISub k3 k') :
    (X.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).isub (ISub.cons x hx τ).up =
      X.isub (ISub.cons (.or x.shift (.neg (.var 0))) ⟨KubusCore.I.scoped_shift hx, (show (0 : ℕ) < k3 + 1 by omega)⟩
        τ.up.tail) := by
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | i
  · rfl
  · rfl

omit hW in
theorem isub_negI (X : Tm) (τ : ISub k'' k') :
    (X.dsubst negI).isub τ.up = X.isub (ISub.cons (.neg (.var 0)) (show (0 : ℕ) < k'' + 1 by omega) τ.up.tail) := by
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | i
  · rfl
  · rfl

omit hW in
theorem dsubst_negI_closed {X : Tm} (hX : X.closedB 0 (k + 1) = true) :
    X.dsubst negI = X.isub (ISub.cons (.neg (.var 0)) (show (0 : ℕ) < k + 1 by omega) (ISub.id k).up.tail) := by
  simp only [Tm.dsubst, Tm.isub]
  refine closed_subst_eq X 0 (k + 1) _ _ _ _ hX (fun _ h => absurd h (Nat.not_lt_zero _)) fun i hi => ?_
  rcases i with _ | i
  · rfl
  · show I.var (i + 1) = ((ISub.id k).τ i).shift
    simp [ISub.id, show i < k by omega, I.shift, I.ren, I.subst]

/-- The typings of the transports of an argument, along a line of Π-types. -/
theorem transpPi_parts {T A B a0 v : Tm} {φ : I} (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one))
    (hR : RedT S (k + 1) T (.pi A B)) (hvt : HasTy S k .one [] v (A.dinst .one)) :
    HasTy S k .one [] (.transp (A.dsubst negI) φ v) ((A.dsubst negI).dinst .one) ∧
    TyEq S k ((A.dsubst negI).dinst .one) (A.dinst .zero) ∧
    HasTy S (k + 1) .one [] (.transp (A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
      v.dshift) ((A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).dinst .one) ∧
    TyEq S (k + 1) ((A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).dinst .one) A := by
  have hS := sigClosed_of_wfSig hW
  have h1 := HasTy.eqR (eq_transp_ty hW hty hR.2)
  obtain ⟨l0, ⟨hL, hφ, hc, -⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW h1) rfl
  have hA0 := HasTy0.piDom hS hL
  have hcD := EqTm0.piInjDom (A' := (A.dinst .zero).dshift) hc
  have hw := wT_typed hS hA0 hφ hcD
  obtain ⟨hw0, -, -⟩ := w0T_typed hS hA0 hφ hcD
  have hvt0 := spec_to_minimal hW hvt
  have hw0v := HasTy0.subst hS hw0 hvt0
  rw [w0T_inst, shift_dd_inst] at hw0v
  have eA0 : EqTm S k .one [] ((A.dsubst negI).dinst .one) (A.dinst .zero) (.univ l0) := by
    have := ieq0 hW (k := k) hA0 (τ1 := fun i => (negI i).subst (I.inst0 .one)) (τ2 := I.inst0 .zero)
      (fun i hi => by rcases i with _ | i <;> simp [negI, I.subst, I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i <;> simp [I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; rfl
                      · intro ρ; rfl)
    simpa [Tm.dinst, Tm.dsubst, subst_subst] using this
  have hvd := HasTy0.dwk hS hvt0
  have hwv := HasTy0.subst hS hw hvd
  rw [wT_inst, shift_inst] at hwv
  have eB2 : EqTm S (k + 1) .one [] ((A.subst .var (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).dinst .one) A
      (.univ l0) := by
    have := ieq0 hW (k := k + 1) hA0
      (τ1 := fun i => (Tm.bind2 (.or (.var 1) (.neg (.var 0))) i).subst (I.inst0 .one)) (τ2 := I.var)
      (fun i hi => by rcases i with _ | i <;> simp [Tm.bind2, I.subst, I.inst0, I.Scoped] <;> omega)
      (fun i hi => show i < k + 1 from hi)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; simp [I.eval, I.inst0, Tm.bind2, I.subst]
                      · intro ρ; rfl)
    simpa [Tm.dinst, Tm.dsubst, subst_subst, subst_var] using this
  exact ⟨minimal_to_spec hw0v, .inr ⟨l0, eA0⟩, HasTy.conv (minimal_to_spec hwv) (EqTm.symm eB2), .inr ⟨l0, eB2⟩⟩

omit hW in
theorem ieq_or_negzero (a : I) : I.Eq (I.or a (.neg .zero)) .one := fun ρ0 => by
  simp only [I.eval]; cases a.eval ρ0 <;> rfl

omit hW in
theorem ieq_or_negone (a : I) : I.Eq (I.or a (.neg .one)) a := fun ρ0 => by
  simp only [I.eval]; cases a.eval ρ0 <;> rfl

omit hW in
theorem ieq_or_one_left {a : I} (b : I) (h : I.Eq a .one) : I.Eq (I.or a b) .one := fun ρ0 => by
  simp only [I.eval]; rw [h ρ0]; cases b.eval ρ0 <;> rfl

omit hW in
theorem ieq_or_congr {a a' b b' : I} (h1 : I.Eq a a') (h2 : I.Eq b b') : I.Eq (I.or a b) (I.or a' b') := fun ρ0 => by
  simp only [I.eval]; rw [h1 ρ0, h2 ρ0]

theorem eqTm_transp_of {A A' a a' : Tm} {φ φ' : I} (h1 : HasTy S k .one [] (.transp A φ a) (A.dinst .one))
    (h2 : HasTy S k .one [] (.transp A' φ' a') (A.dinst .one)) (e : TyEq S (k + 1) A A')
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (ea : EqTm S k .one [] a a' (A.dinst .zero)) :
    EqTm S k .one [] (.transp A φ a) (.transp A' φ' a') (A.dinst .one) := by
  rcases e with rfl | ⟨l, e⟩
  · obtain ⟨l0, ⟨hL, -, -, -⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW h1) rfl
    exact EqTm.transp h1 h2 (EqTm.refl (minimal_to_spec hL)) h12 h21 ea
  · exact EqTm.transp h1 h2 e h12 h21 ea

/-- Transport along related lines of Π-types, applied to related arguments. -/
theorem kanT2_pi_core {T T' : Tm} (hTT : RT2 S (k + 1) T T') (hP : PiStr S (k + 1) T T')
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
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hXT : TyCode (k + 1) (semK S (k + 1) T) := tyCode_of_univ hW hTl'
  have hTK : ∀ k3 (σ : ISub k3 (k + 1)), IsTyK S k3 (T.isub σ) := fun k3 σ => ⟨l0, .inl (HasTy.isubS hW hTl' σ)⟩
  have hXTσ : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (T.isub σ)) := fun k3 σ => by
    rw [semK_isubTy hW (hTK (k + 1) (ISub.id (k + 1)) |> fun _ => ⟨l0, .inl hTl'⟩) σ]; exact hXT.res _
  choose A2 B2 A2' B2' hw using hP.whnf
  have hXA : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (A2 k3 σ)) := fun k3 σ => by
    obtain ⟨l, h⟩ := piW_typed hW (hTK k3 σ) (hw k3 σ).1
    exact tyCode_of_univ hW (HasTy.piDom h)
  have hBpt : ∀ k3 (σ : ISub k3 (k + 1)) a, HasTy S k3 .one [] a (A2 k3 σ) →
      TyCode k3 (semK S k3 ((B2 k3 σ).inst a)) := fun k3 σ a ha => by
    obtain ⟨l, hpi⟩ := piW_typed hW (hTK k3 σ) (hw k3 σ).1
    exact tyCode_of_univ hW (minimal_to_spec (HasTy0.subst (sigClosed_of_wfSig hW)
      (HasTy0.piCod (sigClosed_of_wfSig hW) (spec_to_minimal hW hpi)) (spec_to_minimal hW ha)))
  have hBpt' : ∀ k3 (σ : ISub k3 (k + 1)) a, HasTy S k3 .one [] a (A2' k3 σ) →
      TyCode k3 (semK S k3 ((B2' k3 σ).inst a)) := fun k3 σ a ha => by
    obtain ⟨l, hpi⟩ := piW_typed hW (Comp2_ty_base (RT2.isub hW hXT hTT σ)).2.2.1 (hw k3 σ).2.1
    exact tyCode_of_univ hW (minimal_to_spec (HasTy0.subst (sigClosed_of_wfSig hW)
      (HasTy0.piCod (sigClosed_of_wfSig hW) (spec_to_minimal hW hpi)) (spec_to_minimal hW ha)))
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
    fun k3 τ y y' hy hy' hE => piW_rel hW (hLR k3 τ y y' hy hy' hE) (hw _ _).1 (hw _ _).2.1
  have G1L : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (A2 k3 (ISub.cons y hy τ)) (A2 k3 (ISub.cons y' hy' τ)) ∧
      ∀ a a', RE2 S k3 (A2 k3 (ISub.cons y hy τ)) a a' →
        RT2 S k3 ((B2 k3 (ISub.cons y hy τ)).inst a) ((B2 k3 (ISub.cons y' hy' τ)).inst a') := by
    intro k3 τ y y' hy hy' hE
    have m1 := hLR k3 τ y y' hy hy' hE
    have m2 := hLR k3 τ y' y' hy' hy' (I_eq_refl _)
    have m := RT2.trans hW (hXTσ k3 _) m1 (RT2.symm hW (hXTσ k3 _) m2)
    exact piW_rel hW m (hw _ _).1 (hw _ _).1
  have G2 : ∀ k3 (τ : ISub k3 k) (y : I) (hy : y.Scoped k3), (ival (idEnv k3) (φ.subst τ.τ)).holds →
      RT2 S k3 (A2 k3 (ISub.cons y hy τ)) (A2 k3 (ISub.cons .zero trivial τ)) ∧
      ∀ a a', RE2 S k3 (A2 k3 (ISub.cons y hy τ)) a a' →
        RT2 S k3 ((B2 k3 (ISub.cons y hy τ)).inst a) ((B2 k3 (ISub.cons .zero trivial τ)).inst a') :=
    fun k3 τ y hy hh => piW_rel hW (hC k3 τ y hy hh) (hw _ _).1 (hw _ _).1
  -- transport along lines of domains
  have lineKan : ∀ k1 (σ1 : ISub k1 (k + 1)) k1' (σ1' : ISub k1' (k + 1)) k3 (Θ1 : ISub (k3 + 1) k1)
      (Θ1' : ISub (k3 + 1) k1') (σ0 : ISub k3 k) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)),
      I.Eq y y' → σ1.comp Θ1 = ISub.cons y hy σ0.up.tail → σ1'.comp Θ1' = ISub.cons y' hy' σ0.up.tail →
      KanT2 S k3 ((A2 k1 σ1).isub Θ1) ((A2' k1' σ1').isub Θ1') ∧
      LineRob S k3 ((A2 k1 σ1).isub Θ1) ((A2' k1' σ1').isub Θ1') ∧
      (∀ (e : I) (he : e.Scoped k3),
        RT2 S k3 (((A2 k1 σ1).isub Θ1).dinst e)
          (A2 k3 (ISub.cons (y.subst (ISub.cons e he (ISub.id k3)).τ)
            (I.scoped_subst hy (ISub.cons e he (ISub.id k3)).sc) σ0))) ∧
      RT2 S (k3 + 1) ((A2 k1 σ1).isub Θ1) ((A2' k1' σ1').isub Θ1') ∧
      (∀ (e : I) (he : e.Scoped k3),
        RT2 S k3 (((A2' k1' σ1').isub Θ1').dinst e)
          (A2' k3 (ISub.cons (y'.subst (ISub.cons e he (ISub.id k3)).τ)
            (I.scoped_subst hy' (ISub.cons e he (ISub.id k3)).sc) σ0))) := by
    intro k1 σ1 k1' σ1' k3 Θ1 Θ1' σ0 y y' hy hy' hE e1 e1'
    have c1 := (G3 k1 σ1 (k3 + 1) Θ1 _ e1).1
    have m := (G1 (k3 + 1) σ0.up.tail y y' hy hy' hE).1
    have c3 := (G3' k1' σ1' (k3 + 1) Θ1' _ e1').1
    have t1 := RT2.tyCode_l hW c1 (hXA _ _)
    have t3 := RT2.tyCode_l hW c3 (RT2.tyCode_r hW m (hXA _ _))
    have rel : RT2 S (k3 + 1) ((A2 k1 σ1).isub Θ1) ((A2' k1' σ1').isub Θ1') :=
      RT2.trans hW t1 c1 (RT2.trans hW (hXA _ _) m (RT2.symm hW t3 c3))
    refine ⟨hIHA k1 σ1 _ _ (hw k1 σ1).1 k3 Θ1 _ rel, fun k4 τ2 z z' hz hz' hEz => ?_, fun e he => ?_, rel,
      fun e he => ?_⟩
    · rw [Tm.isub_isub, Tm.isub_isub]
      have d1 := (G3 k1 σ1 k4 (Θ1.comp (ISub.cons z hz τ2)) _
        (by rw [← ISub.comp_assoc, e1, ISub.cons_comp, ISub.up_tail_comp_cons])).1
      have d3 := (G3' k1' σ1' k4 (Θ1'.comp (ISub.cons z' hz' τ2)) _
        (by rw [← ISub.comp_assoc, e1', ISub.cons_comp, ISub.up_tail_comp_cons])).1
      have hEs : I.Eq (y.subst (ISub.cons z hz τ2).τ) (y'.subst (ISub.cons z' hz' τ2).τ) :=
        I_eq_trans (I_eq_subst hE _) (I_eq_subst_congr (fun i => by
          rcases i with _ | i
          · exact hEz
          · exact I_eq_refl _) y')
      have mm := (G1 k4 (σ0.comp τ2) _ _ (I.scoped_subst hy (ISub.cons z hz τ2).sc)
        (I.scoped_subst hy' (ISub.cons z' hz' τ2).sc) hEs).1
      have u1 := RT2.tyCode_l hW d1 (hXA _ _)
      have u3 := RT2.tyCode_l hW d3 (RT2.tyCode_r hW mm (hXA _ _))
      exact RT2.trans hW u1 d1 (RT2.trans hW (hXA _ _) mm (RT2.symm hW u3 d3))
    · have hcl := closed_of_isTyK hW (Comp2_ty_base c1).2.1
      rw [← isub_cons_id_of_closed hcl e he, Tm.isub_isub]
      exact (G3 k1 σ1 k3 _ _ (by rw [← ISub.comp_assoc, e1, ISub.cons_comp, ISub.up_tail_comp_cons,
        ISub.comp_id])).1
    · have hcl := closed_of_isTyK hW (Comp2_ty_base c3).2.1
      rw [← isub_cons_id_of_closed hcl e he, Tm.isub_isub]
      exact (G3' k1' σ1' k3 _ _ (by rw [← ISub.comp_assoc, e1', ISub.cons_comp, ISub.up_tail_comp_cons,
        ISub.comp_id])).1
  -- the endpoint `T(1)`
  let ι1 : ISub k (k + 1) := ISub.cons .one trivial (ISub.id k)
  have hR1' : RedT S k (T.isub ι1) (.pi A1 B1) := by rw [isub_cons_id_of_closed hTc]; exact hR1
  obtain ⟨hA1e, hB1e⟩ : A2 k ι1 = A1 ∧ B2 k ι1 = B1 := by
    have := RedW.unique (hw k ι1).1.1 hR1'.1; injection this; constructor <;> assumption
  have hvv : RE2 S k A1 v v := by
    have hA := (hw k ι1).2.2.1; rw [hA1e] at hA
    exact RE2.trans hW hA hv (RE2.symm hW hA hv)
  have hvv' : RE2 S k A1 v' v' := by
    have hA := (hw k ι1).2.2.1; rw [hA1e] at hA
    exact RE2.trans hW hA (RE2.symm hW hA hv) hv
  -- the domain and the codomain at restrictions of the endpoint
  have Aend : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A2 k' (ISub.cons .one trivial ρ)) ∧
      ∀ a a', RE2 S k' (A1.isub ρ) a a' → RT2 S k' ((B1.isub ρ).inst a) ((B2 k' (ISub.cons .one trivial ρ)).inst a') := by
    intro k' ρ; rw [← hA1e, ← hB1e]; exact G3 k ι1 k' ρ _ (cons_one_comp ρ)
  -- the domain and codomain of the line at a restriction, at an endpoint
  have Apt : ∀ k' (ρ : ISub k' k) (e : I) (he : e.Scoped k'),
      RT2 S k' ((A2 (k' + 1) ρ.up).dinst e) (A2 k' (ISub.cons e he ρ)) ∧
      ∀ a a', RE2 S k' ((A2 (k' + 1) ρ.up).dinst e) a a' →
        RT2 S k' (((B2 (k' + 1) ρ.up).dinst e).inst a) ((B2 k' (ISub.cons e he ρ)).inst a') := by
    intro k' ρ e he
    obtain ⟨l, hpi⟩ := piW_typed hW (hTK _ ρ.up) (hw _ ρ.up).1
    have hcl := closed_of_ty hW hpi
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    rw [← isub_cons_id_of_closed hcl.1 e he, ← isub_cons_id_of_closed hcl.2 e he]
    exact G3 (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id])
  have Apt' : ∀ k' (ρ : ISub k' k) (e : I) (he : e.Scoped k'),
      RT2 S k' ((A2' (k' + 1) ρ.up).dinst e) (A2' k' (ISub.cons e he ρ)) ∧
      ∀ a a', RE2 S k' ((A2' (k' + 1) ρ.up).dinst e) a a' →
        RT2 S k' (((B2' (k' + 1) ρ.up).dinst e).inst a) ((B2' k' (ISub.cons e he ρ)).inst a') := by
    intro k' ρ e he
    have hTK' : IsTyK S (k' + 1) (T'.isub ρ.up) := (Comp2_ty_base (RT2.isub hW hXT hTT ρ.up)).2.2.1
    obtain ⟨l, hpi⟩ := piW_typed hW hTK' (hw _ ρ.up).2.1
    have hcl := closed_of_ty hW hpi
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    rw [← isub_cons_id_of_closed hcl.1 e he, ← isub_cons_id_of_closed hcl.2 e he]
    exact G3' (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id])
  -- the transports of the arguments
  let bb : I := .or (.var 1) (.neg (.var 0))
  let wL : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    .transp ((A2 (k' + 1) ρ.up).dsubst (Tm.bind2 bb)) (.or (φ.subst ρ.τ).shift (.var 0)) (v.isub ρ).dshift
  let wR : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    .transp ((A2' (k' + 1) ρ.up).dsubst (Tm.bind2 bb)) (.or (φ'.subst ρ.τ).shift (.var 0)) (v'.isub ρ).dshift
  let w0L : ∀ k' (_ : ISub k' k), Tm := fun k' ρ => .transp ((A2 (k' + 1) ρ.up).dsubst negI) (φ.subst ρ.τ) (v.isub ρ)
  let w0R : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    .transp ((A2' (k' + 1) ρ.up).dsubst negI) (φ'.subst ρ.τ) (v'.isub ρ)
  have hyx : ∀ {k3 : ℕ} (x : I), x.Scoped k3 → (I.or x.shift (.neg (.var 0))).Scoped (k3 + 1) :=
    fun x hx => ⟨KubusCore.I.scoped_shift hx, (show (0 : ℕ) < _ by omega)⟩
  have hy0 : ∀ {k3 : ℕ}, (I.neg (.var 0)).Scoped (k3 + 1) := fun {k3} => (show (0 : ℕ) < k3 + 1 by omega)
  have wpt : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      (wL k' ρ).isub (ISub.cons x hx τ) = .transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyx x hx) τ.up.tail))
        (.or (φ.subst (ρ.comp τ).τ) x) (v.isub (ρ.comp τ)) := by
    intro k' ρ k3 τ x hx
    show Tm.transp (((A2 (k' + 1) ρ.up).dsubst (Tm.bind2 bb)).isub (ISub.cons x hx τ).up)
      ((I.or (φ.subst ρ.τ).shift (.var 0)).subst (ISub.cons x hx τ).τ) (((v.isub ρ).dshift).isub (ISub.cons x hx τ)) = _
    rw [isub_bind2, dshift_isub_cons, Tm.isub_isub]
    congr 1
    show I.or (((φ.subst ρ.τ).shift).subst (ISub.cons x hx τ).τ) x = _
    rw [I_shift_cons, ← I_subst_comp]
  have wpt' : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      (wR k' ρ).isub (ISub.cons x hx τ) = .transp ((A2' (k' + 1) ρ.up).isub (ISub.cons _ (hyx x hx) τ.up.tail))
        (.or (φ'.subst (ρ.comp τ).τ) x) (v'.isub (ρ.comp τ)) := by
    intro k' ρ k3 τ x hx
    show Tm.transp (((A2' (k' + 1) ρ.up).dsubst (Tm.bind2 bb)).isub (ISub.cons x hx τ).up)
      ((I.or (φ'.subst ρ.τ).shift (.var 0)).subst (ISub.cons x hx τ).τ) (((v'.isub ρ).dshift).isub (ISub.cons x hx τ)) = _
    rw [isub_bind2, dshift_isub_cons, Tm.isub_isub]
    congr 1
    show I.or (((φ'.subst ρ.τ).shift).subst (ISub.cons x hx τ).τ) x = _
    rw [I_shift_cons, ← I_subst_comp]
  have w0pt : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k'),
      (w0L k' ρ).isub τ = .transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ hy0 τ.up.tail))
        (φ.subst (ρ.comp τ).τ) (v.isub (ρ.comp τ)) := by
    intro k' ρ k3 τ
    show Tm.transp (((A2 (k' + 1) ρ.up).dsubst negI).isub τ.up) ((φ.subst ρ.τ).subst τ.τ) ((v.isub ρ).isub τ) = _
    rw [isub_negI, Tm.isub_isub, ← I_subst_comp]
  have w0R' : ∀ k' (ρ : ISub k' k), w0R k' ρ = .transp ((A2' (k' + 1) ρ.up).isub (ISub.cons _ hy0 (ISub.id k').up.tail))
      (φ'.subst ρ.τ) (v'.isub ρ) := by
    intro k' ρ
    have hcl := closed_of_isTyK hW (Comp2_ty_base (hw (k' + 1) ρ.up).2.2.1).2.2.1
    show Tm.transp ((A2' (k' + 1) ρ.up).dsubst negI) _ _ = _
    rw [dsubst_negI_closed hcl]
  have upΘ : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (y : I) (hy : y.Scoped (k3 + 1)),
      ρ.up.comp (ISub.cons y hy τ.up.tail) = ISub.cons y hy (ρ.comp τ).up.tail := by
    intro k' ρ k3 τ y hy; rw [ISub.up_comp_cons, ISub.comp_up_tail]
  -- the type of the applications
  have ht0 : HasTy S k .one [] (.app (.transp T φ a0) v) (B1.inst v) := HasTy.app (hty.tyConv hR1.2) (RE2.typed hv).1
  have hX : TyCode k (semK S k (B1.inst v)) := tyCode_of_ty hW ht0
  have hYY : RT2 S k (B1.inst v) (B1.inst v) := by
    have := (hw k ι1).2.2.2 v v (by rw [hA1e]; exact hvv)
    rw [hB1e] at this; exact RT2.refl hW hX this
  have hYK : IsTyK S k (B1.inst v) := (Comp2_ty_base hYY).2.1
  have hXY : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' ((B1.inst v).isub ρ)) := fun k' ρ => by
    rw [semK_isubTy hW hYK ρ]; exact hX.res _
  have hYv : ∀ k' (ρ : ISub k' k), RT2 S k' ((B1.inst v).isub ρ) ((B1.inst v).isub ρ) := fun k' ρ =>
    RT2.isub hW hX hYY ρ
  have Ypt : ∀ k' (ρ : ISub k' k), RT2 S k' ((B1.inst v).isub ρ) ((B2 k' (ISub.cons .one trivial ρ)).inst (v.isub ρ)) := by
    intro k' ρ; rw [isub_inst]; exact (Aend k' ρ).2 _ _ (RE2.isub hW hvv ρ)
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the typings at a restriction
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty ρ; rwa [isub_dinst] at this
  have hvA : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (v.isub ρ) ((A2 (k' + 1) ρ.up).dinst .one) := fun k' ρ => by
    have e1 := tyB (Aend k' ρ).1
    have e2 := tyB (Apt k' ρ .one trivial).1
    exact (RE2.typed (RE2.isub hW hvv ρ)).1.tyConv (TyEq.trans hW e1 (TyEq.symm e2))
  have parts := fun k' (ρ : ISub k' k) => transpPi_parts hW (hρT k' ρ) (hw (k' + 1) ρ.up).1 (hvA k' ρ)
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ))
      ((T'.isub ρ.up).dinst .one) := fun k' ρ => by
    have := (HasTy.isubS hW hty' ρ).tyConv ((tyEq_dinst hW hP.tyEq (r := .one) trivial).isub hW ρ)
    rwa [isub_dinst] at this
  have hvA' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (v'.isub ρ) ((A2' (k' + 1) ρ.up).dinst .one) := fun k' ρ => by
    have e1 := tyB (Aend k' ρ).1
    have e2 := tyB (Apt k' ρ .one trivial).1
    have e3 := tyB (Apt' k' ρ .one trivial).1
    have e4 := tyB ((hw k' (ISub.cons .one trivial ρ)).2.2.1)
    exact (RE2.typed (RE2.isub hW hvv' ρ)).1.tyConv
      (TyEq.trans hW e1 (TyEq.trans hW e4 (TyEq.symm e3)))
  have parts' := fun k' (ρ : ISub k' k) => transpPi_parts hW (hρT' k' ρ) (hw (k' + 1) ρ.up).2.1 (hvA' k' ρ)
  have hT0 : ∀ {k3 : ℕ} (σ : ISub k3 k), (T.dinst .zero).isub σ = T.isub (ISub.cons .zero trivial σ) := fun σ => by
    rw [isub_dinst]; exact isub_up_dinst T σ .zero trivial
  -- the arguments, at the domains of the endpoint
  have v1 : ∀ k' (σ : ISub k' k), RE2 S k' (A2 k' (ISub.cons .one trivial σ)) (v.isub σ) (v'.isub σ) := fun k' σ =>
    RE2.conv hW (Aend k' σ).1 (RE2.isub hW hv σ)
  have v11 : ∀ k' (σ : ISub k' k), RE2 S k' (A2 k' (ISub.cons .one trivial σ)) (v.isub σ) (v.isub σ) := fun k' σ =>
    RE2.conv hW (Aend k' σ).1 (RE2.isub hW hvv σ)
  have v1L : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) ((A2 (k' + 1) ρ.up).dinst .one) := fun k' ρ =>
    RT2.trans hW (RT2.tyCode_l hW (Aend k' ρ).1 (hXA _ _)) (Aend k' ρ).1
      (RT2.symm hW (RT2.tyCode_l hW (Apt k' ρ .one trivial).1 (hXA _ _)) (Apt k' ρ .one trivial).1)
  have hvc : v.isub (ISub.id k) = v := isub_id_of_closed (closed_of_ty hW (RE2.typed hv).1)
  have hvc' : v'.isub (ISub.id k) = v' := isub_id_of_closed (closed_of_ty hW (RE2.typed hv).2.1)
  -- the transports of the arguments, at restrictions, in normal form
  have tw0 : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k'),
      HasTy S k3 .one [] (.transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ hy0 τ.up.tail)) (φ.subst (ρ.comp τ).τ)
        (v.isub (ρ.comp τ))) (((A2 (k' + 1) ρ.up).isub (ISub.cons _ hy0 τ.up.tail)).dinst .one) := by
    intro k' ρ k3 τ
    have h := HasTy.isubS hW (parts k' ρ).1 τ
    rw [isub_dinst, isub_negI] at h
    rw [← w0pt]; exact h
  have tw0' : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k'),
      HasTy S k3 .one [] (.transp ((A2' (k' + 1) ρ.up).isub (ISub.cons _ hy0 τ.up.tail)) (φ'.subst (ρ.comp τ).τ)
        (v'.isub (ρ.comp τ))) (((A2' (k' + 1) ρ.up).isub (ISub.cons _ hy0 τ.up.tail)).dinst .one) := by
    intro k' ρ k3 τ
    have h := HasTy.isubS hW (parts' k' ρ).1 τ
    rw [isub_dinst, isub_negI] at h
    show HasTy S k3 .one [] (.transp _ ((φ'.subst ρ.τ).subst τ.τ |> fun _ => φ'.subst (ρ.comp τ).τ) _) _
    have e : (w0R k' ρ).isub τ = .transp ((A2' (k' + 1) ρ.up).isub (ISub.cons _ hy0 τ.up.tail))
        (φ'.subst (ρ.comp τ).τ) (v'.isub (ρ.comp τ)) := by
      show Tm.transp (((A2' (k' + 1) ρ.up).dsubst negI).isub τ.up) ((φ'.subst ρ.τ).subst τ.τ) ((v'.isub ρ).isub τ) = _
      rw [isub_negI, Tm.isub_isub, ← I_subst_comp]
    rw [← e]; exact h
  have tw : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      HasTy S k3 .one [] (.transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyx x hx) τ.up.tail))
        (.or (φ.subst (ρ.comp τ).τ) x) (v.isub (ρ.comp τ)))
        (((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyx x hx) τ.up.tail)).dinst .one) := by
    intro k' ρ k3 τ x hx
    have h := HasTy.isubS hW (parts k' ρ).2.2.1 (ISub.cons x hx τ)
    rw [isub_dinst, isub_bind2] at h
    rw [← wpt]; exact h
  have tw' : ∀ k' (ρ : ISub k' k) k3 (τ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      HasTy S k3 .one [] (.transp ((A2' (k' + 1) ρ.up).isub (ISub.cons _ (hyx x hx) τ.up.tail))
        (.or (φ'.subst (ρ.comp τ).τ) x) (v'.isub (ρ.comp τ)))
        (((A2' (k' + 1) ρ.up).isub (ISub.cons _ (hyx x hx) τ.up.tail)).dinst .one) := by
    intro k' ρ k3 τ x hx
    have h := HasTy.isubS hW (parts' k' ρ).2.2.1 (ISub.cons x hx τ)
    rw [isub_dinst, isub_bind2] at h
    rw [← wpt']; exact h
  have ieqn1 : I.Eq (I.neg .one) .zero := fun _ => rfl
  have hE0 : EqTm S k .one [] (.app (.transp T φ a0) v) (.app (.transp T' φ' a0') v') (B1.inst v) :=
    EqTm.app (heq.tyConv hR1.2) (RE2.typed hv).2.2
  have H := kanT2_elim_core hW (fun k' ρ x => .app x (v.isub ρ)) (fun k' ρ x => .app x (v'.isub ρ))
    (fun k' ρ => (B2 (k' + 1) ρ.up).inst (wL k' ρ)) (fun k' ρ => (B2' (k' + 1) ρ.up).inst (wR k' ρ))
    (fun k' ρ => .app (a0.isub ρ) (w0L k' ρ)) (fun k' ρ => .app (a0'.isub ρ) (w0R k' ρ))
    hX hYY (by simp only [hvc]; exact ht0) (by simp only [hvc']; exact HasTy.eqR hE0)
    (by simp only [hvc, hvc']; exact hE0)
    (fun k' ρ k'' ρ' x => by show Tm.app (x.isub ρ') ((v.isub ρ).isub ρ') = _; rw [Tm.isub_isub])
    (fun k' ρ k'' ρ' x => by show Tm.app (x.isub ρ') ((v'.isub ρ).isub ρ') = _; rw [Tm.isub_isub])
    (fun k' ρ => ?_) (fun k' ρ => ?_) (fun k' ρ hf => ?_) (fun k' ρ k'' ρ' hf hf2 => ?_)
    (fun k' ρ k'' ρ' hnf => ?_) (fun k' ρ k'' ρ' hnf => ?_) (fun k' ρ k'' ρ' hnf => ?_)
    (fun k' ρ k'' ρ' hnf => ?_) (fun k' ρ k'' ρ' hnf => ?_) h12 h21
  · simpa only [hvc, hvc'] using H
  · -- the reducts on the left
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · have eF : TyEq S k' ((T.isub ρ.up).dinst .one) (.pi (A1.isub ρ) (B1.isub ρ)) := by
        have := hR1.2.isub hW ρ; rw [isub_dinst, isub_pi] at this; exact this
      obtain ⟨a, b⟩ := app_transp_face hW hf (hρT k' ρ) eF (RE2.typed (RE2.isub hW hvv ρ)).1
      rw [isub_inst]; exact ⟨a, b⟩
    · obtain ⟨a, b⟩ := app_transp_pi hW hf (hρT k' ρ) (hw (k' + 1) ρ.up).1 (hvA k' ρ)
      refine ⟨a, b.tyConv ?_⟩
      have c := (Apt k' ρ .one trivial).2 _ _ (RE2.conv hW (v1L k' ρ) (RE2.isub hW hvv ρ))
      exact TyEq.trans hW (tyB c) (TyEq.symm (tyB (Ypt k' ρ)))
  · -- the reducts on the right
    have eYv : TyEq S k' ((B2 k' (ISub.cons .one trivial ρ)).inst (v.isub ρ))
        ((B2' k' (ISub.cons .one trivial ρ)).inst (v'.isub ρ)) := tyB ((hw k' _).2.2.2 _ _ (v1 k' ρ))
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · have eF : TyEq S k' ((T'.isub ρ.up).dinst .one) (.pi (A1.isub ρ) (B1.isub ρ)) := by
        have := (TyEq.trans hW (TyEq.symm (tyEq_dinst hW hP.tyEq (r := .one) trivial)) hR1.2).isub hW ρ
        rw [isub_dinst, isub_pi] at this; exact this
      obtain ⟨a, b⟩ := app_transp_face hW hf (hρT' k' ρ) eF (RE2.typed (RE2.isub hW hv ρ)).2.1
      refine ⟨a, b.tyConv ?_⟩
      have c1 := tyB ((Aend k' ρ).2 _ _ (RE2.isub hW hv ρ))
      have c2 := tyB ((Aend k' ρ).2 _ _ (RE2.isub hW hvv' ρ))
      rw [isub_inst]
      exact TyEq.trans hW c2 (TyEq.symm c1)
    · obtain ⟨a, b⟩ := app_transp_pi hW hf (hρT' k' ρ) (hw (k' + 1) ρ.up).2.1 (hvA' k' ρ)
      refine ⟨a, b.tyConv ?_⟩
      have hv'1 : RE2 S k' ((A2' (k' + 1) ρ.up).dinst .one) (v'.isub ρ) (v'.isub ρ) := by
        have r1 := (hw k' (ISub.cons .one trivial ρ)).2.2.1
        have r2 := (Apt' k' ρ .one trivial).1
        have t := RT2.trans hW (RT2.tyCode_l hW (Aend k' ρ).1 (hXA _ _)) (Aend k' ρ).1
          (RT2.trans hW (hXA _ _) r1 (RT2.symm hW (RT2.tyCode_l hW r2 (RT2.tyCode_r hW r1 (hXA _ _))) r2))
        exact RE2.conv hW t (RE2.isub hW hvv' ρ)
      have c := (Apt' k' ρ .one trivial).2 _ _ hv'1
      exact TyEq.trans hW (tyB c) (TyEq.trans hW (TyEq.symm eYv) (TyEq.symm (tyB (Ypt k' ρ))))
  · -- the bases where the face holds
    have h0 := RE2.isub hW ha0 ρ
    rw [hT0] at h0
    have hCρ := hC k' ρ .one trivial ((holds_iff_entails (I.scoped_subst hφs ρ.sc)).2 hf)
    have h1 := RE2.conv' hW hCρ h0 (hXTσ _ _)
    have el := hP.elim k' _ _ _ _ _ (hw k' _).1 h1 _ _ (v1 k' ρ)
    exact RE2.conv' hW (Ypt k' ρ) el (hXY k' ρ)
  · -- the bases where the face holds only after restriction
    show RE2 S k'' _ ((Tm.app (a0.isub ρ) (w0L k' ρ)).isub ρ') (.app (a0'.isub (ρ.comp ρ')) (v'.isub (ρ.comp ρ')))
    have eapp : (Tm.app (a0.isub ρ) (w0L k' ρ)).isub ρ' = .app (a0.isub (ρ.comp ρ')) ((w0L k' ρ).isub ρ') := by
      show Tm.app ((a0.isub ρ).isub ρ') ((w0L k' ρ).isub ρ') = _
      rw [Tm.isub_isub]
    rw [eapp, w0pt]
    have hh := (holds_iff_entails (I.scoped_subst hφs (ρ.comp ρ').sc)).2 hf2
    have lk := (lineKan (k' + 1) ρ.up (k' + 1) ρ.up k'' _ _ (ρ.comp ρ') _ _ hy0 hy0 (I_eq_refl _)
      (upΘ k' ρ k'' ρ' _ hy0) (upΘ k' ρ k'' ρ' _ hy0)).2.2.1 .one trivial
    have c2 := (G1L k'' (ρ.comp ρ') (.neg .one) .zero trivial trivial ieqn1).1
    have g2 := G2 k'' (ρ.comp ρ') .one trivial hh
    have hX0 := hXA k'' (ISub.cons .zero trivial (ρ.comp ρ'))
    have c12 := RT2.trans hW (RT2.tyCode_l hW lk (hXA _ _)) lk c2
    have htw := (tw0 k' ρ k'' ρ').tyConv (tyB c12)
    have hst := stable_transpFace hW hf2 htw
    have hXX : RT2 S k'' (A2 k'' (ISub.cons .zero trivial (ρ.comp ρ'))) (A2 k'' (ISub.cons .zero trivial (ρ.comp ρ'))) :=
      RT2.refl hW hX0 (hw _ _).2.2.1
    have hvv0 := RE2.conv hW g2.1 (v11 k'' (ρ.comp ρ'))
    have hwv := RE2.expandL hW hXX htw (RE2.typed hvv0).1 hst hvv0
    have harg := RE2.trans hW hXX hwv (RE2.conv hW g2.1 (v1 k'' (ρ.comp ρ')))
    have h0 := RE2.isub hW ha0 (ρ.comp ρ')
    rw [hT0] at h0
    have el := hP.elim k'' _ _ _ _ _ (hw k'' _).1 h0 _ _ harg
    have g21 := RT2.symm hW (hXA _ _) g2.1
    have b2 := g2.2 _ _ (RE2.conv hW g21 (RE2.symm hW hXX hwv))
    exact RE2.conv' hW (RT2.trans hW (hXY _ _) (Ypt k'' _) b2) el (hXY _ _)
  · -- the eliminated lines at their ends
    show RT2 S k'' ((((B2 (k' + 1) ρ.up).inst (wL k' ρ)).isub ρ'.up).dinst .one) _
    rw [isub_up_dinst _ ρ' .one trivial, isub_inst, wpt]
    have g := G3 (k' + 1) ρ.up k'' (ISub.cons .one trivial ρ') (ISub.cons .one trivial (ρ.comp ρ'))
      (ISub.up_comp_cons ρ .one trivial ρ')
    have lk := (lineKan (k' + 1) ρ.up (k' + 1) ρ.up k'' _ _ (ρ.comp ρ') _ _ (hyx .one trivial) (hyx .one trivial)
      (I_eq_refl _) (upΘ k' ρ k'' ρ' _ _) (upΘ k' ρ k'' ρ' _ _)).2.2.1 .one trivial
    have c2 := (G1L k'' (ρ.comp ρ') (.or .one (.neg .one)) .one ⟨trivial, trivial⟩ trivial (fun _ => rfl)).1
    have hXg := RT2.tyCode_l hW g.1 (hXA _ _)
    have tX := RT2.trans hW (RT2.tyCode_l hW lk (hXA _ _)) lk (RT2.trans hW (hXA _ _) c2 (RT2.symm hW hXg g.1))
    have htw := (tw k' ρ k'' ρ' .one trivial).tyConv (tyB tX)
    have hst := stable_transpFace hW (ent_or_right _ _) htw
    have hAA := RT2.refl hW hXg g.1
    have hvv1 := RE2.conv hW (RT2.symm hW hXg g.1) (v11 k'' (ρ.comp ρ'))
    have hwv := RE2.expandL hW hAA htw (RE2.typed hvv1).1 hst hvv1
    have b := g.2 _ _ hwv
    exact RT2.trans hW (RT2.tyCode_l hW b (RT2.tyCode_r hW (Ypt k'' _) (hXY _ _))) b
      (RT2.symm hW (hXY _ _) (Ypt k'' _))
  · -- robustness of the eliminated lines
    intro k3 τ x x' hx hx' hEx
    show RT2 S k3 ((((B2 (k' + 1) ρ.up).inst (wL k' ρ)).isub ρ'.up).isub (ISub.cons x hx τ))
      (((B2' (k'' + 1) (ρ.comp ρ').up).inst (wR k'' (ρ.comp ρ'))).isub (ISub.cons x' hx' τ))
    rw [Tm.isub_isub, ISub.up_comp_cons, isub_inst, isub_inst, wpt, wpt']
    have eσ : (ρ.comp ρ').comp τ = ρ.comp (ρ'.comp τ) := ISub.comp_assoc _ _ _
    rw [eσ]
    have hEy : I.Eq (I.or x.shift (.neg (.var 0))) (I.or x'.shift (.neg (.var 0))) :=
      ieq_or_congr (fun ρ0 => by simp only [I.shift, eval_ren]; exact hEx _) (I_eq_refl _)
    have lkF := lineKan (k' + 1) ρ.up (k'' + 1) (ρ.comp ρ').up k3 _ _ (ρ.comp (ρ'.comp τ)) _ _ (hyx x hx) (hyx x' hx')
      hEy (upΘ k' ρ k3 (ρ'.comp τ) _ _) (by rw [upΘ, eσ])
    -- the transports of the argument are related
    have hty1 := tw k' ρ k3 (ρ'.comp τ) x hx
    have hty2 := tw' k'' (ρ.comp ρ') k3 τ x' hx'
    rw [eσ] at hty2
    have eX1 := tyEq_dinst hW (tyB lkF.2.2.2.1) (r := .one) trivial
    have hty2' := hty2.tyConv (TyEq.symm eX1)
    have h0X := lkF.2.2.1 .zero trivial
    have g0 := (G1L k3 (ρ.comp (ρ'.comp τ)) _ .one (I.scoped_subst (hyx x hx) (ISub.cons .zero trivial (ISub.id k3)).sc)
      trivial (ieq_or_negzero _)).1
    have t0 := RT2.trans hW (RT2.tyCode_l hW h0X (hXA _ _)) h0X g0
    have hbase := RE2.conv' hW t0 (v1 k3 (ρ.comp (ρ'.comp τ))) (RT2.tyCode_l hW h0X (hXA _ _))
    have h12' : I.Entails (I.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) x) (I.or (φ'.subst (ρ.comp (ρ'.comp τ)).τ) x') :=
      ent_or_elim (ent_trans (ent_subst h12 _) (ent_or_left _ _)) (ent_trans (eq_ent hEx) (ent_or_right _ _))
    have h21' : I.Entails (I.or (φ'.subst (ρ.comp (ρ'.comp τ)).τ) x') (I.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) x) :=
      ent_or_elim (ent_trans (ent_subst h21 _) (ent_or_left _ _))
        (ent_trans (eq_ent (I_eq_symm hEx)) (ent_or_right _ _))
    have heqw := eqTm_transp_of hW hty1 hty2' (tyB lkF.2.2.2.1) h12' h21' (RE2.typed hbase).2.2
    have r := lkF.1 lkF.2.1 _ _ _ _ ?_ hty1 hty2' heqw h12' h21' hbase
    · -- the codomains
      have h1X := lkF.2.2.1 .one trivial
      have eqx : I.Eq ((I.or x.shift (.neg (.var 0))).subst (ISub.cons .one trivial (ISub.id k3)).τ) x := by
        show I.Eq (I.or (x.shift.subst (ISub.cons .one trivial (ISub.id k3)).τ) (.neg .one)) x
        rw [I_shift_cons, I_subst_id hx]; exact ieq_or_negone x
      have g1 := (G1L k3 (ρ.comp (ρ'.comp τ)) _ x (I.scoped_subst (hyx x hx) (ISub.cons .one trivial (ISub.id k3)).sc)
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
          ((A2 (k' + 1) ρ.up).isub ((ISub.cons _ (hyx x hx) (ρ'.comp τ).up.tail).comp (ISub.cons z hz τ2)))
          (A2 k4 (ISub.cons ((I.or x.shift (.neg (.var 0))).subst (ISub.cons z hz τ2).τ)
            (I.scoped_subst (hyx x hx) (ISub.cons z hz τ2).sc) ((ρ.comp (ρ'.comp τ)).comp τ2))) := fun z hz =>
        (G3 (k' + 1) ρ.up k4 _ _ (by rw [← ISub.comp_assoc, upΘ, ISub.cons_comp, ISub.up_tail_comp_cons])).1
      have d1 := d z hz
      have d0 := d .zero trivial
      have hsc : (I.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) x).Scoped k3 := ⟨I.scoped_subst hφs (ρ.comp (ρ'.comp τ)).sc, hx⟩
      have he := (holds_iff_entails (I.scoped_subst hsc τ2.sc)).1 hh
      have mid : RT2 S k4 (A2 k4 (ISub.cons ((I.or x.shift (.neg (.var 0))).subst (ISub.cons z hz τ2).τ)
            (I.scoped_subst (hyx x hx) (ISub.cons z hz τ2).sc) ((ρ.comp (ρ'.comp τ)).comp τ2)))
          (A2 k4 (ISub.cons ((I.or x.shift (.neg (.var 0))).subst (ISub.cons .zero trivial τ2).τ)
            (I.scoped_subst (hyx x hx) (ISub.cons .zero trivial τ2).sc) ((ρ.comp (ρ'.comp τ)).comp τ2))) := by
        rcases ent_or_cases (I.scoped_subst hsc.1 τ2.sc) (I.scoped_subst hx τ2.sc) he with hφ2 | hx2
        · have hh2 : (ival (idEnv k4) (φ.subst ((ρ.comp (ρ'.comp τ)).comp τ2).τ)).holds :=
            (holds_iff_entails (I.scoped_subst hφs ((ρ.comp (ρ'.comp τ)).comp τ2).sc)).2 (ent_comp_inv hφ2)
          have gz := G2 k4 _ _ (I.scoped_subst (hyx x hx) (ISub.cons z hz τ2).sc) hh2
          have g0 := G2 k4 _ _ (I.scoped_subst (hyx x hx) (ISub.cons .zero trivial τ2).sc) hh2
          exact RT2.trans hW (hXA _ _) gz.1 (RT2.symm hW (hXA _ _) g0.1)
        · have e1 : I.Eq (x.subst τ2.τ) .one :=
            ieq_one_of_holds (I.scoped_subst hx τ2.sc) (entails_holds hx2 (ρ := idEnv k4) (by rw [ival_one]; rfl))
          have ez : I.Eq ((I.or x.shift (.neg (.var 0))).subst (ISub.cons z hz τ2).τ) .one := by
            show I.Eq (I.or (x.shift.subst (ISub.cons z hz τ2).τ) _) _
            rw [I_shift_cons]; exact ieq_or_one_left _ e1
          have e0 : I.Eq ((I.or x.shift (.neg (.var 0))).subst (ISub.cons .zero trivial τ2).τ) .one := by
            show I.Eq (I.or (x.shift.subst (ISub.cons .zero trivial τ2).τ) _) _
            rw [I_shift_cons]; exact ieq_or_one_left _ e1
          exact (G1L k4 _ _ _ _ _ (I_eq_trans ez (I_eq_symm e0))).1
      exact RT2.trans hW (RT2.tyCode_l hW d1 (hXA _ _)) d1
        (RT2.trans hW (hXA _ _) mid (RT2.symm hW (RT2.tyCode_l hW d0 (hXA _ _)) d0))
  · -- constancy of the eliminated lines
    intro k3 τ x hx hh
    have hhσ : (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp τ)).τ)).holds := by
      rw [I_subst_comp, I_subst_comp]; exact hh
    have hφσ : I.Entails .one (φ.subst (ρ.comp (ρ'.comp τ)).τ) :=
      (holds_iff_entails (I.scoped_subst hφs (ρ.comp (ρ'.comp τ)).sc)).1 hhσ
    have g1 := G2 k3 (ρ.comp (ρ'.comp τ)) .one trivial hhσ
    -- the transported argument at a point, against the argument
    have wrel : ∀ (z : I) (hz : z.Scoped k3),
        RE2 S k3 ((A2 (k' + 1) ρ.up).isub (ISub.cons z hz (ρ'.comp τ)))
          (.transp ((A2 (k' + 1) ρ.up).isub (ISub.cons _ (hyx z hz) (ρ'.comp τ).up.tail))
            (.or (φ.subst (ρ.comp (ρ'.comp τ)).τ) z) (v.isub (ρ.comp (ρ'.comp τ)))) (v.isub (ρ.comp (ρ'.comp τ))) ∧
        RE2 S k3 (A2 k3 (ISub.cons z hz (ρ.comp (ρ'.comp τ)))) (v.isub (ρ.comp (ρ'.comp τ)))
          (v.isub (ρ.comp (ρ'.comp τ))) := by
      intro z hz
      have gz := G2 k3 (ρ.comp (ρ'.comp τ)) z hz hhσ
      have hvz := RE2.conv hW (RT2.trans hW (hXA _ _) g1.1 (RT2.symm hW (hXA _ _) gz.1)) (v11 k3 _)
      have gL := G3 (k' + 1) ρ.up k3 (ISub.cons z hz (ρ'.comp τ)) (ISub.cons z hz (ρ.comp (ρ'.comp τ)))
        (ISub.up_comp_cons ρ z hz _)
      have hXL := RT2.tyCode_l hW gL.1 (hXA _ _)
      have lk := (lineKan (k' + 1) ρ.up (k' + 1) ρ.up k3 _ _ (ρ.comp (ρ'.comp τ)) _ _ (hyx z hz) (hyx z hz)
        (I_eq_refl _) (upΘ k' ρ k3 (ρ'.comp τ) _ _) (upΘ k' ρ k3 (ρ'.comp τ) _ _)).2.2.1 .one trivial
      have eqz : I.Eq ((I.or z.shift (.neg (.var 0))).subst (ISub.cons .one trivial (ISub.id k3)).τ) z := by
        show I.Eq (I.or (z.shift.subst (ISub.cons .one trivial (ISub.id k3)).τ) (.neg .one)) z
        rw [I_shift_cons, I_subst_id hz]; exact ieq_or_negone z
      have gz' := (G1L k3 (ρ.comp (ρ'.comp τ)) _ z (I.scoped_subst (hyx z hz) (ISub.cons .one trivial (ISub.id k3)).sc)
        hz eqz).1
      have tX := RT2.trans hW (RT2.tyCode_l hW lk (hXA _ _)) lk (RT2.trans hW (hXA _ _) gz' (RT2.symm hW hXL gL.1))
      have htw := (tw k' ρ k3 (ρ'.comp τ) z hz).tyConv (tyB tX)
      have hst := stable_transpFace hW (ent_trans hφσ (ent_or_left _ _)) htw
      have hvL := RE2.conv hW (RT2.symm hW hXL gL.1) hvz
      exact ⟨RE2.expandL hW (RT2.refl hW hXL gL.1) htw (RE2.typed hvL).1 hst hvL, hvz⟩
    show RT2 S k3 ((((B2 (k' + 1) ρ.up).inst (wL k' ρ)).isub ρ'.up).isub (ISub.cons x hx τ))
      ((((B2 (k' + 1) ρ.up).inst (wL k' ρ)).isub ρ'.up).isub (ISub.cons .zero trivial τ))
    rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons, isub_inst, isub_inst, wpt, wpt]
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
  all_goals sorry

end

end Model.Whnf
