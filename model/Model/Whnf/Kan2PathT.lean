import Model.Whnf.Kan2SigmaS
import Model.Whnf.Kan2PathTEq

/-!
# The binary transport along lines of path types
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The system of a point of a transport along a line of path types. -/
def sysT (φ r : I) (p0 a b : Tm) : Tm :=
  .split φ.shift (.papp p0.dshift r.shift) (.or (.neg r.shift) r.shift) (.split (.neg r.shift) a r.shift b)

theorem transpPath_body' (A a b p0 : Tm) (φ r : I) : ∃ t, Tm.transpPath A a b φ p0 = .plam t ∧
    t.dinst r = Tm.comp (A.dinst r.shift) (.or φ (.or (.neg r) r)) (sysT φ r p0 a b) (.papp p0 r) := by
  obtain ⟨t, ht, htr⟩ := transpPath_body A a b p0 φ r
  refine ⟨t, ht, htr.trans ?_⟩
  congr 1
  simp only [Tm.dinst, Tm.dsubst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · rfl
  · rfl
  · rfl

theorem path_dinst (A a b : Tm) (s : I) :
    (Tm.path A a b).dinst s = .path (A.dsubst (I.up (I.inst0 s))) (a.dinst s) (b.dinst s) := rfl

variable (hW : WfSig S)
include hW

omit hW in
theorem step_transp_path {A a b p : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.transp (.path A a b) φ p) = some (Tm.transpPath A a b φ p) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

/-- A point of a transport along a line of path types whose face does not hold. -/
theorem papp_transp_path {T A2 c0 c1 a0 : Tm} {φ r : I} (hn : ¬ I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hR : RedT S (k + 1) T (.path A2 c0 c1)) :
    Red S (.papp (.transp T φ a0) r)
      (Tm.comp (A2.dinst r.shift) (.or φ (.or (.neg r) r)) (sysT φ r a0 c0 c1) (.papp a0 r)) ∧
    EqTm S k .one [] (.papp (.transp T φ a0) r)
      (Tm.comp (A2.dinst r.shift) (.or φ (.or (.neg r) r)) (sysT φ r a0 c0 c1) (.papp a0 r))
      ((A2.dinst r.shift).dinst .one) := by
  obtain ⟨t, ht, htr⟩ := transpPath_body' A2 c0 c1 a0 φ r
  have e1 := eq_transp_ty hW hty hR.2
  have e2 := EqTm.transpPath (HasTy.eqR e1)
  have hT1 : TyEq S k (T.dinst .one) (.path (A2.dsubst (I.up (I.inst0 .one))) (c0.dinst .one) (c1.dinst .one)) := by
    have := tyEq_dinst hW hR.2 (r := .one) trivial; rwa [path_dinst] at this
  have e3 := (e1.trans e2).tyConv hT1
  have e4 := EqTm.papp e3 hr hr (I_eq_refl r)
  rw [ht] at e4
  have e5 := EqTm.pathBeta (HasTy.eqR e4)
  rw [htr] at e5
  rw [← dinst_shift_one] at e4 e5
  refine ⟨(red_papp r ((red_transp_ty hn hR.1.1).trans (.step (step_transp_path hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rw [ht]; show some (t.dinst r) = _; rw [htr]

/-- A point of a transport along a line of path types whose face holds. -/
theorem papp_transp_face' {T L b0 b1 a0 : Tm} {φ r : I} (h : I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hT1 : TyEq S k (T.dinst .one) (.path L b0 b1)) :
    Red S (.papp (.transp T φ a0) r) (.papp a0 r) ∧
    EqTm S k .one [] (.papp (.transp T φ a0) r) (.papp a0 r) (L.dinst r) :=
  ⟨red_papp r (.step (step_transp_face h) (.refl _)),
    EqTm.papp ((EqTm.transpFace h hty).tyConv hT1) hr hr (I_eq_refl r)⟩

/-- The path type a type reduces to is typed. -/
theorem pathW_typed {X L b0 b1 : Tm} (hX : IsTyK S k X) (hR : RedT S k X (.path L b0 b1)) :
    ∃ l, HasTy S k .one [] (.path L b0 b1) (.univ l) :=
  ty_of_tyEq hW hX hR.2 (fun l h => by cases h)

/-- The lines and endpoints of the normal forms of related types are related. -/
theorem pathW_rel {X Y L b0 b1 L' b0' b1' : Tm} (h : RT2 S k X Y) (hX : RedT S k X (.path L b0 b1))
    (hY : RedT S k Y (.path L' b0' b1')) :
    (∀ (s s' : I), s.Scoped k → s'.Scoped k → I.Eq s s' → RT2 S k (L.dinst s) (L'.dinst s')) ∧
    RE2 S k (L.dinst .zero) b0 b0' ∧ RE2 S k (L.dinst .one) b1 b1' := by
  obtain ⟨l, hp⟩ := pathW_typed hW (Comp2_ty_base h).2.1 hX
  have hP := PathStr_of hW h hX hp
  have hXc := closed_of_isTyK hW (Comp2_ty_base h).2.1
  have hYc := closed_of_isTyK hW (Comp2_ty_base h).2.2.1
  obtain ⟨L1, c0, c1, L1', c0', c1', h1, h2, hl, hc0, hc1⟩ := hP.whnf k (ISub.id k)
  rw [isub_id_of_closed hXc] at h1
  rw [isub_id_of_closed hYc] at h2
  obtain ⟨rfl, rfl, rfl⟩ : L1 = L ∧ c0 = b0 ∧ c1 = b1 := by
    have := RedW.unique h1.1 hX.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  obtain ⟨rfl, rfl, rfl⟩ : L1' = L' ∧ c0' = b0' ∧ c1' = b1' := by
    have := RedW.unique h2.1 hY.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  exact ⟨hl, hc0, hc1⟩

omit hW in
theorem sysT_isub (φ r : I) (p0 a b : Tm) (θ : ISub k' k) :
    (sysT φ r p0 a b).isub θ.up = sysT (φ.subst θ.τ) (r.subst θ.τ) (p0.isub θ) (a.isub θ.up) (b.isub θ.up) := by
  show Tm.split (φ.shift.subst (I.up θ.τ)) (.papp (p0.dshift.isub θ.up) (r.shift.subst (I.up θ.τ)))
    (.or (.neg (r.shift.subst (I.up θ.τ))) (r.shift.subst (I.up θ.τ)))
    (.split (.neg (r.shift.subst (I.up θ.τ))) (a.isub θ.up) (r.shift.subst (I.up θ.τ)) (b.isub θ.up)) = _
  rw [isub_dshift, I_shift_subst_up, I_shift_subst_up]; rfl

omit hW in
theorem sysT_isub_dinst (φ r : I) (p0 a b : Tm) (θ : ISub k' k) (x : I) :
    ((sysT φ r p0 a b).isub θ.up).dinst x = .split (φ.subst θ.τ) (.papp (p0.isub θ) (r.subst θ.τ))
      (.or (.neg (r.subst θ.τ)) (r.subst θ.τ))
      (.split (.neg (r.subst θ.τ)) ((a.isub θ.up).dinst x) (r.subst θ.τ) ((b.isub θ.up).dinst x)) := by
  have e : ∀ y : I, (y.shift.subst θ.up.τ).subst (I.inst0 x) = y.subst θ.τ := fun y => shift_up_inst0 y θ.τ x
  show Tm.split ((φ.shift.subst θ.up.τ).subst (I.inst0 x)) (.papp ((p0.dshift.isub θ.up).dinst x)
      ((r.shift.subst θ.up.τ).subst (I.inst0 x)))
    (.or (.neg ((r.shift.subst θ.up.τ).subst (I.inst0 x))) ((r.shift.subst θ.up.τ).subst (I.inst0 x)))
    (.split (.neg ((r.shift.subst θ.up.τ).subst (I.inst0 x))) ((a.isub θ.up).dinst x)
      ((r.shift.subst θ.up.τ).subst (I.inst0 x)) ((b.isub θ.up).dinst x)) = _
  rw [e, e, dshift_isub_up_dinst]

/-- Transport along related lines of path types, at related points. -/
theorem kanT2_path_core {T T' : Tm} (hTT : RT2 S (k + 1) T T') (hP : PathStr S (k + 1) T T')
    (hLR : LineRob S k T T')
    (hIHT : ∀ k1 (ρ : ISub (k1 + 1) (k + 1)) L c0 c1, RedT S (k1 + 1) (T.isub ρ) (.path L c0 c1) → ∀ (s : I),
      s.Scoped (k1 + 1) → ∀ k2 (ρ' : ISub (k2 + 1) (k1 + 1)) X', RT2 S (k2 + 1) ((L.dinst s).isub ρ') X' →
      KanT2 S k2 ((L.dinst s).isub ρ') X')
    (hIHH : ∀ k1 (ρ : ISub k1 (k + 1)) L c0 c1, RedT S k1 (T.isub ρ) (.path L c0 c1) → ∀ (s : I),
      s.Scoped k1 → ∀ k2 (ρ' : ISub k2 k1) X', RT2 S k2 ((L.dinst s).isub ρ') X' →
      KanH2 S k2 ((L.dinst s).isub ρ') X')
    {φ φ' : I} {a0 a0' : Tm} (hC : LineConst S k T φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one))
    (hty' : HasTy S k .one [] (.transp T' φ' a0') (T.dinst .one))
    (heq : EqTm S k .one [] (.transp T φ a0) (.transp T' φ' a0') (T.dinst .one))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (ha0 : RE2 S k (T.dinst .zero) a0 a0')
    {L1 b0 b1 : Tm} (hR1 : RedT S k (T.dinst .one) (.path L1 b0 b1)) {r r' : I} (hr : r.Scoped k)
    (hr' : r'.Scoped k) (hE : I.Eq r r') :
    RE2 S k (L1.dinst r) (.papp (.transp T φ a0) r) (.papp (.transp T' φ' a0') r') := by
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  obtain ⟨l0', ⟨-, hφs', -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  choose W c0 c1 W' c0' c1' hw using hP.whnf
  have hT0 : ∀ {k3 : ℕ} (v : ISub k3 k), (T.dinst .zero).isub v = T.isub (ISub.cons .zero trivial v) := fun v => by
    rw [isub_dinst]; exact isub_up_dinst T v .zero trivial
  let ι1 : ISub k (k + 1) := ISub.cons .one trivial (ISub.id k)
  have hR1' : RedT S k (T.isub ι1) (.path L1 b0 b1) := by rw [isub_cons_id_of_closed hTc]; exact hR1
  obtain ⟨hL1, hb0, hb1⟩ : W k ι1 = L1 ∧ c0 k ι1 = b0 ∧ c1 k ι1 = b1 := by
    have := RedW.unique (hw k ι1).1.1 hR1'.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  have hrid : r.subst (ISub.id k).τ = r := I_subst_id hr
  have hrid' : r'.subst (ISub.id k).τ = r' := I_subst_id hr'
  have hsc : ∀ k' (ρ : ISub k' k), (r.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr ρ.sc
  have hsc' : ∀ k' (ρ : ISub k' k), (r'.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr' ρ.sc
  have hEρ : ∀ k' (ρ : ISub k' k), I.Eq (r.subst ρ.τ) (r'.subst ρ.τ) := fun k' ρ => I_eq_subst hE ρ.τ
  have hX2 : ∀ k3 (σ : ISub k3 (k + 1)) (s : I), s.Scoped k3 → TyCode k3 (semK S k3 ((W k3 σ).dinst s)) :=
    fun k3 σ s hs => hP.tc k3 σ _ _ _ (hw k3 σ).1 s hs
  have hWW' : ∀ k3 (σ : ISub k3 (k + 1)) (s s' : I), s.Scoped k3 → s'.Scoped k3 → I.Eq s s' →
      RT2 S k3 ((W k3 σ).dinst s) ((W' k3 σ).dinst s') := fun k3 σ => (hw k3 σ).2.2.1
  have hcohW : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      ∀ (s : I), s.Scoped k2 → RT2 S k2 (((W k1 σ1).isub θ.up).dinst s) ((W k2 σ2).dinst s) := by
    intro k1 σ1 k2 θ σ2 h s hs; subst h
    exact hP.coh k1 σ1 k2 θ _ _ _ _ _ _ (hw k1 σ1).1 (hw k2 _).1 s hs
  have hcohW' : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      ∀ (s : I), s.Scoped k2 → RT2 S k2 (((W' k1 σ1).isub θ.up).dinst s) ((W' k2 σ2).dinst s) := by
    intro k1 σ1 k2 θ σ2 h s hs; subst h
    exact hP.coh' k1 σ1 k2 θ _ _ _ _ _ _ (hw k1 σ1).2.1 (hw k2 _).2.1 s hs
  have hends : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RE2 S k2 ((W k2 σ2).dinst .zero) ((c0 k1 σ1).isub θ) (c0 k2 σ2) ∧
      RE2 S k2 ((W k2 σ2).dinst .one) ((c1 k1 σ1).isub θ) (c1 k2 σ2) := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact hP.ends k1 σ1 k2 θ _ _ _ _ _ _ (hw k1 σ1).1 (hw k2 _).1
  have hends' : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RE2 S k2 ((W' k2 σ2).dinst .zero) ((c0' k1 σ1).isub θ) (c0' k2 σ2) ∧
      RE2 S k2 ((W' k2 σ2).dinst .one) ((c1' k1 σ1).isub θ) (c1' k2 σ2) := by
    intro k1 σ1 k2 θ σ2 h; subst h
    exact hP.ends' k1 σ1 k2 θ _ _ _ _ _ _ (hw k1 σ1).2.1 (hw k2 _).2.1
  -- the type of the points, at a restriction
  have Ypt : ∀ k3 (v : ISub k3 k), RT2 S k3 ((L1.dinst r).isub v)
      ((W k3 (ISub.cons .one trivial v)).dinst (r.subst v.τ)) := by
    intro k3 v; rw [isub_dinst, ← hL1]
    exact hcohW k ι1 k3 v _ (cons_one_comp v) _ (hsc k3 v)
  have hXY : ∀ k3 (v : ISub k3 k), TyCode k3 (semK S k3 ((L1.dinst r).isub v)) := fun k3 v =>
    RT2.tyCode_l hW (Ypt k3 v) (hX2 k3 _ _ (hsc k3 v))
  have tyB : ∀ {k3 : ℕ} {A B : Tm}, RT2 S k3 A B → TyEq S k3 A B := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hTl' : HasTy S (k + 1) .one [] T (.univ l0) := minimal_to_spec hTl
  have hTK : ∀ k3 (σ : ISub k3 (k + 1)), IsTyK S k3 (T.isub σ) := fun k3 σ => ⟨l0, .inl (HasTy.isubS hW hTl' σ)⟩
  have hTK' : ∀ k3 (σ : ISub k3 (k + 1)), IsTyK S k3 (T'.isub σ) := fun k3 σ =>
    ((Comp2_ty_base hTT).2.2.1).isub hW σ
  have hWcl : ∀ k3 (σ : ISub k3 (k + 1)), (W k3 σ).closedB 0 (k3 + 1) = true := fun k3 σ => by
    obtain ⟨lp, hp⟩ := pathW_typed hW (hTK k3 σ) (hw k3 σ).1
    exact closed_of_ty hW (HasTy.pathLine hp)
  have hWcl' : ∀ k3 (σ : ISub k3 (k + 1)), (W' k3 σ).closedB 0 (k3 + 1) = true := fun k3 σ => by
    obtain ⟨lp, hp⟩ := pathW_typed hW (hTK' k3 σ) (hw k3 σ).2.1
    exact closed_of_ty hW (HasTy.pathLine hp)
  have Cd1 : ∀ k' (ρ : ISub k' k), RT2 S k' (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).dinst .one) ((W k' (ISub.cons .one trivial ρ)).dinst (r.subst ρ.τ)) := by
    intro k' ρ
    rw [dinst_shift_dinst (hWcl _ _) _ .one (hsc k' ρ) trivial, ← isub_up_dinst _ _ _ (hsc k' ρ)]
    exact hcohW (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id]) _ (hsc k' ρ)
  have C'd1 : ∀ k' (ρ : ISub k' k), RT2 S k' (((W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)).dinst .one) ((W' k' (ISub.cons .one trivial ρ)).dinst (r'.subst ρ.τ)) := by
    intro k' ρ
    rw [dinst_shift_dinst (hWcl' _ _) _ .one (hsc' k' ρ) trivial, ← isub_up_dinst _ _ _ (hsc' k' ρ)]
    exact hcohW' (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id]) _ (hsc' k' ρ)
  -- the typings at restrictions
  have hρT : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ))
      ((T.isub ρ.up).dinst .one) := fun k' ρ => by
    have := HasTy.isubS hW hty ρ; rwa [isub_dinst] at this
  have hρT' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ))
      ((T'.isub ρ.up).dinst .one) := fun k' ρ => by
    have := (HasTy.isubS hW hty' ρ).tyConv ((tyEq_dinst hW hP.tyEq (r := .one) trivial).isub hW ρ)
    rw [isub_dinst] at this; exact this
  have eY1 : ∀ k' (ρ : ISub k' k), TyEq S k' ((T.isub ρ.up).dinst .one)
      (.path (L1.isub ρ.up) (b0.isub ρ) (b1.isub ρ)) := fun k' ρ => by
    have := hR1.2.isub hW ρ; rwa [isub_dinst, isub_path] at this
  have eY1' : ∀ k' (ρ : ISub k' k), TyEq S k' ((T'.isub ρ.up).dinst .one)
      (.path (L1.isub ρ.up) (b0.isub ρ) (b1.isub ρ)) := fun k' ρ => by
    have := (TyEq.trans hW (TyEq.symm (tyEq_dinst hW hP.tyEq (r := .one) trivial)) hR1.2).isub hW ρ
    rwa [isub_dinst, isub_path] at this
  have hWdd : ∀ k' (ρ : ISub k' k), TyEq S k' ((W k' (ISub.cons .one trivial ρ)).dinst (r'.subst ρ.τ))
      ((L1.dinst r).isub ρ) := by
    intro k' ρ
    have a := tyB (hWW' k' (ISub.cons .one trivial ρ) _ _ (hsc' k' ρ) (hsc' k' ρ) (I_eq_refl _))
    have b := tyB (hWW' k' (ISub.cons .one trivial ρ) _ _ (hsc k' ρ) (hsc' k' ρ) (hEρ k' ρ))
    exact TyEq.trans hW (TyEq.trans hW a (TyEq.symm b)) (TyEq.symm (tyB (Ypt k' ρ)))
  have hTyR : ∀ k' (ρ : ISub k' k), TyEq S k' ((L1.isub ρ.up).dinst (r'.subst ρ.τ)) ((L1.dinst r).isub ρ) := by
    intro k' ρ
    have c : RT2 S k' ((L1.isub ρ.up).dinst (r'.subst ρ.τ))
        ((W k' (ISub.cons .one trivial ρ)).dinst (r'.subst ρ.τ)) := by
      rw [← hL1]; exact hcohW k ι1 k' ρ _ (cons_one_comp ρ) _ (hsc' k' ρ)
    exact TyEq.trans hW (tyB c) (hWdd k' ρ)
  -- the reductions of the points of the restricted transports
  have redL : ∀ k' (ρ : ISub k' k), ¬ I.Entails .one (φ.subst ρ.τ) →
      Red S (.papp (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ)) (r.subst ρ.τ))
        (Tm.comp ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)) (.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))) (sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)) (.papp (a0.isub ρ) (r.subst ρ.τ))) ∧
      EqTm S k' .one [] (.papp (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ)) (r.subst ρ.τ))
        (Tm.comp ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)) (.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))) (sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)) (.papp (a0.isub ρ) (r.subst ρ.τ))) ((L1.dinst r).isub ρ) := by
    intro k' ρ hf
    obtain ⟨a, b⟩ := papp_transp_path hW hf (hsc k' ρ) (hρT k' ρ) (hw (k' + 1) ρ.up).1
    exact ⟨a, b.tyConv (TyEq.trans hW (tyB (Cd1 k' ρ)) (TyEq.symm (tyB (Ypt k' ρ))))⟩
  have redR : ∀ k' (ρ : ISub k' k), ¬ I.Entails .one (φ'.subst ρ.τ) →
      Red S (.papp (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ)) (r'.subst ρ.τ))
        (Tm.comp ((W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)) (.or (φ'.subst ρ.τ) (.or (.neg (r'.subst ρ.τ)) (r'.subst ρ.τ))) (sysT (φ'.subst ρ.τ) (r'.subst ρ.τ) (a0'.isub ρ) (c0' (k' + 1) ρ.up) (c1' (k' + 1) ρ.up)) (.papp (a0'.isub ρ) (r'.subst ρ.τ))) ∧
      EqTm S k' .one [] (.papp (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ)) (r'.subst ρ.τ))
        (Tm.comp ((W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)) (.or (φ'.subst ρ.τ) (.or (.neg (r'.subst ρ.τ)) (r'.subst ρ.τ))) (sysT (φ'.subst ρ.τ) (r'.subst ρ.τ) (a0'.isub ρ) (c0' (k' + 1) ρ.up) (c1' (k' + 1) ρ.up)) (.papp (a0'.isub ρ) (r'.subst ρ.τ))) ((L1.dinst r).isub ρ) := by
    intro k' ρ hf
    obtain ⟨a, b⟩ := papp_transp_path hW hf (hsc' k' ρ) (hρT' k' ρ) (hw (k' + 1) ρ.up).2.1
    have c := TyEq.trans hW (tyB (C'd1 k' ρ)) (TyEq.symm (tyB (hWW' k' (ISub.cons .one trivial ρ) _ _
      (hsc' k' ρ) (hsc' k' ρ) (I_eq_refl _))))
    exact ⟨a, b.tyConv (TyEq.trans hW c (hWdd k' ρ))⟩
  have faceL : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst ρ.τ) →
      Red S (.papp (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ)) (r.subst ρ.τ)) (.papp (a0.isub ρ) (r.subst ρ.τ)) ∧
      EqTm S k' .one [] (.papp (.transp (T.isub ρ.up) (φ.subst ρ.τ) (a0.isub ρ)) (r.subst ρ.τ))
        (.papp (a0.isub ρ) (r.subst ρ.τ)) ((L1.dinst r).isub ρ) := by
    intro k' ρ hf
    have := papp_transp_face' hW hf (hsc k' ρ) (hρT k' ρ) (eY1 k' ρ)
    rwa [← isub_dinst] at this
  have faceR : ∀ k' (ρ : ISub k' k), I.Entails .one (φ'.subst ρ.τ) →
      Red S (.papp (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ)) (r'.subst ρ.τ))
        (.papp (a0'.isub ρ) (r'.subst ρ.τ)) ∧
      EqTm S k' .one [] (.papp (.transp (T'.isub ρ.up) (φ'.subst ρ.τ) (a0'.isub ρ)) (r'.subst ρ.τ))
        (.papp (a0'.isub ρ) (r'.subst ρ.τ)) ((L1.dinst r).isub ρ) := by
    intro k' ρ hf
    obtain ⟨a, b⟩ := papp_transp_face' hW hf (hsc' k' ρ) (hρT' k' ρ) (eY1' k' ρ)
    exact ⟨a, b.tyConv (hTyR k' ρ)⟩
  have Cpt : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      RT2 S k3 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons x hx θ)) ((W k3 (ISub.cons x hx (ρ.comp θ))).dinst (r.subst (ρ.comp θ).τ)) := by
    intro k' ρ k3 θ x hx
    rw [isub_dinst, I_shift_cons, ← I_subst_comp]
    exact hcohW (k' + 1) ρ.up k3 (ISub.cons x hx θ) _ (ISub.up_comp_cons ρ x hx θ) _ (hsc k3 _)
  have C'pt : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      RT2 S k3 (((W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)).isub (ISub.cons x hx θ)) ((W' k3 (ISub.cons x hx (ρ.comp θ))).dinst (r'.subst (ρ.comp θ).τ)) := by
    intro k' ρ k3 θ x hx
    rw [isub_dinst, I_shift_cons, ← I_subst_comp]
    exact hcohW' (k' + 1) ρ.up k3 (ISub.cons x hx θ) _ (ISub.up_comp_cons ρ x hx θ) _ (hsc' k3 _)
  have hE0 : EqTm S k .one [] (.papp (.transp T φ a0) r) (.papp (.transp T' φ' a0') r') (L1.dinst r) :=
    EqTm.papp (heq.tyConv hR1.2) hr hr' hE
  -- the points of the bases, where the face holds
  have faceRel : ∀ k3 (σ : ISub k3 k), I.Entails .one (φ.subst σ.τ) →
      RE2 S k3 ((L1.dinst r).isub σ) (.papp (a0.isub σ) (r.subst σ.τ)) (.papp (a0'.isub σ) (r'.subst σ.τ)) := by
    intro k3 σ hf
    have h0 := RE2.isub hW ha0 σ
    rw [hT0] at h0
    have hCσ := hC k3 σ .one trivial ((holds_iff_entails (I.scoped_subst hφs σ.sc)).2 hf)
    have h1 := RE2.conv' hW hCσ h0 (RT2.tyCode_l hW hCσ (RE2.tyCode hW h0))
    exact RE2.conv' hW (Ypt k3 σ) ((hP.elim k3 _ _ _ _ _ _ (hw k3 _).1 h1).1 _ _ (hsc k3 σ) (hsc' k3 σ) (hEρ k3 σ))
      (hXY k3 σ)
  -- the relations at the points of the lines of the restricted transports
  have hWs : ∀ k4 (σ : ISub k4 (k + 1)) (s s' : I), s.Scoped k4 → s'.Scoped k4 → I.Eq s s' →
      RT2 S k4 ((W k4 σ).dinst s) ((W k4 σ).dinst s') := by
    intro k4 σ s s' hs hs' he
    have a := hWW' k4 σ s s' hs hs' he
    have b := hWW' k4 σ s' s' hs' hs' (I_eq_refl _)
    exact RT2.trans hW (hX2 _ _ _ hs) a (RT2.symm hW (RT2.tyCode_l hW b (RT2.tyCode_r hW a (hX2 _ _ _ hs))) b)
  have aPt : ∀ k4 (τ : ISub k4 k) (y : I) (hy : y.Scoped k4), (ival (idEnv k4) (φ.subst τ.τ)).holds →
      RE2 S k4 (T.isub (ISub.cons y hy τ)) (a0.isub τ) (a0'.isub τ) := by
    intro k4 τ y hy hh
    have h0 := RE2.isub hW ha0 τ
    rw [hT0] at h0
    have hCτ := hC k4 τ y hy hh
    exact RE2.conv' hW hCτ h0 (RT2.tyCode_l hW hCτ (RE2.tyCode hW h0))
  have hTy : ∀ k4 (τ : ISub k4 k) (y : I) (hy : y.Scoped k4), RT2 S k4 (T.isub (ISub.cons y hy τ))
      (T.isub (ISub.cons y hy τ)) := fun k4 τ y hy => by
    have a := hLR k4 τ y y hy hy (I_eq_refl _)
    exact RT2.refl hW (tyCode_of_univ hW (HasTy.isubS hW hTl' _)) a
  have aPtL : ∀ k4 (τ : ISub k4 k) (y : I) (hy : y.Scoped k4), (ival (idEnv k4) (φ.subst τ.τ)).holds →
      RE2 S k4 (T.isub (ISub.cons y hy τ)) (a0.isub τ) (a0.isub τ) := fun k4 τ y hy hh =>
    RE2.trans hW (hTy k4 τ y hy) (aPt k4 τ y hy hh) (RE2.symm hW (hTy k4 τ y hy) (aPt k4 τ y hy hh))
  have aPtR : ∀ k4 (τ : ISub k4 k) (y : I) (hy : y.Scoped k4), (ival (idEnv k4) (φ.subst τ.τ)).holds →
      RE2 S k4 (T.isub (ISub.cons y hy τ)) (a0'.isub τ) (a0'.isub τ) := fun k4 τ y hy hh =>
    RE2.trans hW (hTy k4 τ y hy) (RE2.symm hW (hTy k4 τ y hy) (aPt k4 τ y hy hh)) (aPt k4 τ y hy hh)
  have e_pp : ∀ k4 (τ : ISub k4 k) (y : I) (hy : y.Scoped k4),
      RE2 S k4 (T.isub (ISub.cons y hy τ)) (a0.isub τ) (a0'.isub τ) →
      RE2 S k4 ((W k4 (ISub.cons y hy τ)).dinst (r.subst τ.τ)) (.papp (a0.isub τ) (r.subst τ.τ))
        (.papp (a0'.isub τ) (r'.subst τ.τ)) := fun k4 τ y hy hb =>
    (hP.elim k4 _ _ _ _ _ _ (hw k4 _).1 hb).1 _ _ (hsc k4 τ) (hsc' k4 τ) (hEρ k4 τ)
  -- the endpoints of the lines
  have e_c : ∀ k4 (τ : ISub k4 k) (y y' : I) (hy : y.Scoped k4) (hy' : y'.Scoped k4), I.Eq y y' →
      (I.Eq (r.subst τ.τ) .zero → RE2 S k4 ((W k4 (ISub.cons y hy τ)).dinst (r.subst τ.τ))
        (c0 k4 (ISub.cons y hy τ)) (c0' k4 (ISub.cons y' hy' τ))) ∧
      (I.Eq (r.subst τ.τ) .one → RE2 S k4 ((W k4 (ISub.cons y hy τ)).dinst (r.subst τ.τ))
        (c1 k4 (ISub.cons y hy τ)) (c1' k4 (ISub.cons y' hy' τ))) := by
    intro k4 τ y y' hy hy' hE'
    have m := pathW_rel hW (hLR k4 τ y y' hy hy' hE') (hw _ _).1 (hw _ _).2.1
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have t := hWs k4 (ISub.cons y hy τ) _ .zero (hsc k4 τ) trivial e
      exact RE2.conv' hW t m.2.1 (RT2.tyCode_l hW t (RE2.tyCode hW m.2.1))
    · have t := hWs k4 (ISub.cons y hy τ) _ .one (hsc k4 τ) trivial e
      exact RE2.conv' hW t m.2.2 (RT2.tyCode_l hW t (RE2.tyCode hW m.2.2))
  -- a base against the endpoints, where the face holds
  have e_pc : ∀ k4 (τ : ISub k4 k) (y y' : I) (hy : y.Scoped k4) (hy' : y'.Scoped k4), I.Eq y y' →
      RE2 S k4 (T.isub (ISub.cons y hy τ)) (a0.isub τ) (a0'.isub τ) →
      (I.Eq (r.subst τ.τ) .zero → RE2 S k4 ((W k4 (ISub.cons y hy τ)).dinst (r.subst τ.τ))
          (.papp (a0.isub τ) (r.subst τ.τ)) (c0' k4 (ISub.cons y' hy' τ)) ∧
        RE2 S k4 ((W k4 (ISub.cons y hy τ)).dinst (r.subst τ.τ))
          (c0 k4 (ISub.cons y hy τ)) (.papp (a0'.isub τ) (r'.subst τ.τ))) ∧
      (I.Eq (r.subst τ.τ) .one → RE2 S k4 ((W k4 (ISub.cons y hy τ)).dinst (r.subst τ.τ))
          (.papp (a0.isub τ) (r.subst τ.τ)) (c1' k4 (ISub.cons y' hy' τ)) ∧
        RE2 S k4 ((W k4 (ISub.cons y hy τ)).dinst (r.subst τ.τ))
          (c1 k4 (ISub.cons y hy τ)) (.papp (a0'.isub τ) (r'.subst τ.τ))) := by
    intro k4 τ y y' hy hy' hE' hb
    have elL := hP.elim k4 _ _ _ _ _ _ (hw k4 _).1
      (RE2.trans hW (hTy k4 τ y hy) hb (RE2.symm hW (hTy k4 τ y hy) hb))
    have elR := hP.elim k4 _ _ _ _ _ _ (hw k4 _).1
      (RE2.trans hW (hTy k4 τ y hy) (RE2.symm hW (hTy k4 τ y hy) hb) hb)
    have ec := e_c k4 τ y y' hy hy' hE'
    have hXr := hX2 k4 (ISub.cons y hy τ) _ (hsc k4 τ)
    have hRr := RT2.refl hW hXr (hWs k4 (ISub.cons y hy τ) _ _ (hsc k4 τ) (hsc k4 τ) (I_eq_refl _))
    refine ⟨fun e => ⟨?_, ?_⟩, fun e => ⟨?_, ?_⟩⟩
    · have t := hWs k4 (ISub.cons y hy τ) _ .zero (hsc k4 τ) trivial e
      have a := elL.1 (r.subst τ.τ) .zero (hsc k4 τ) trivial e
      have b := RE2.conv' hW t elL.2.1 hXr
      exact RE2.trans hW hRr a (RE2.trans hW hRr b (ec.1 e))
    · have t := hWs k4 (ISub.cons y hy τ) _ .zero (hsc k4 τ) trivial e
      have a := RE2.conv' hW t (elR.1 .zero _ trivial (hsc' k4 τ) (I_eq_trans (I_eq_symm e) (hEρ k4 τ))) hXr
      have b := RE2.conv' hW t elR.2.1 hXr
      have c := RE2.trans hW hRr (RE2.symm hW hRr b) a
      exact RE2.trans hW hRr (RE2.trans hW hRr (ec.1 e) (RE2.symm hW hRr (ec.1 e))) c
    · have t := hWs k4 (ISub.cons y hy τ) _ .one (hsc k4 τ) trivial e
      have a := elL.1 (r.subst τ.τ) .one (hsc k4 τ) trivial e
      have b := RE2.conv' hW t elL.2.2 hXr
      exact RE2.trans hW hRr a (RE2.trans hW hRr b (ec.2 e))
    · have t := hWs k4 (ISub.cons y hy τ) _ .one (hsc k4 τ) trivial e
      have a := RE2.conv' hW t (elR.1 .one _ trivial (hsc' k4 τ) (I_eq_trans (I_eq_symm e) (hEρ k4 τ))) hXr
      have b := RE2.conv' hW t elR.2.2 hXr
      have c := RE2.trans hW hRr (RE2.symm hW hRr b) a
      exact RE2.trans hW hRr (RE2.trans hW hRr (ec.2 e) (RE2.symm hW hRr (ec.2 e))) c
  -- the composition, where the face does not hold
  have compC : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), ¬ I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RE2 S k'' ((L1.dinst r).isub (ρ.comp ρ'))
        (Tm.comp (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up) (.or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ))) ((sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)).isub ρ'.up) (.papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ)))
        (Tm.comp ((W' (k'' + 1) (ρ.comp ρ').up).dinst ((r'.subst (ρ.comp ρ').τ).shift)) (.or (φ'.subst (ρ.comp ρ').τ) (.or (.neg (r'.subst (ρ.comp ρ').τ)) (r'.subst (ρ.comp ρ').τ))) (sysT (φ'.subst (ρ.comp ρ').τ) (r'.subst (ρ.comp ρ').τ) (a0'.isub (ρ.comp ρ')) (c0' (k'' + 1) (ρ.comp ρ').up) (c1' (k'' + 1) (ρ.comp ρ').up)) (.papp (a0'.isub (ρ.comp ρ')) (r'.subst (ρ.comp ρ').τ))) := by
    intro k' ρ k'' ρ' hf2
    have hf : ¬ I.Entails .one (φ.subst ρ.τ) := fun h => hf2 (ent_comp h)
    have hf2' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hf2 (ent_trans h (ent_subst h21 _))
    have eC1 : (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up).dinst .one = ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons .one trivial ρ') := isub_up_dinst _ ρ' .one trivial
    have conv1 : RT2 S k'' ((((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up).dinst .one) ((L1.dinst r).isub (ρ.comp ρ')) := by
      rw [eC1]
      have c := Cpt k' ρ k'' ρ' .one trivial
      exact RT2.trans hW (RT2.tyCode_l hW c (hX2 _ _ _ (hsc k'' _))) c
        (RT2.symm hW (hXY k'' _) (Ypt k'' (ρ.comp ρ')))
    have eT := TyEq.symm (tyB conv1)
    have hpa : (Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ' = .papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ) := by
      show Tm.papp ((a0.isub ρ).isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = _
      rw [Tm.isub_isub, I_subst_comp]
    have e : (I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).subst ρ'.τ =
        .or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ)) := by
      show I.or ((φ.subst ρ.τ).subst ρ'.τ) (.or (.neg ((r.subst ρ.τ).subst ρ'.τ)) ((r.subst ρ.τ).subst ρ'.τ)) = _
      rw [← I_subst_comp, ← I_subst_comp]
    have EL := EqTm.isubS hW (redL k' ρ hf).2 ρ'
    rw [comp_isub, hpa, Tm.isub_isub (L1.dinst r), e] at EL
    replace EL : EqTm S k'' .one [] ((Tm.papp (.transp T φ a0) r).isub (ρ.comp ρ'))
        (Tm.comp (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up) (.or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ))) ((sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)).isub ρ'.up) (.papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ)))
        ((L1.dinst r).isub (ρ.comp ρ')) := by
      rw [← Tm.isub_isub]; exact EL
    have EM := EqTm.isubS hW hE0 (ρ.comp ρ')
    have ER := (redR k'' (ρ.comp ρ') hf2').2
    have Eall := (EL.symm.trans EM).trans ER
    -- the systems at the points of the lines
    have pts : ∀ k4 (θ : ISub k4 k'') (y y' : I) (hy : y.Scoped k4) (hy' : y'.Scoped k4), I.Eq y y' →
        (RE2 S k4 (T.isub (ISub.cons y hy (ρ.comp (ρ'.comp θ)))) (a0.isub (ρ.comp (ρ'.comp θ))) (a0'.isub (ρ.comp (ρ'.comp θ))) →
          RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) (.papp (a0.isub (ρ.comp (ρ'.comp θ)))
            (r.subst (ρ.comp (ρ'.comp θ)).τ)) (.papp (a0'.isub (ρ.comp (ρ'.comp θ))) (r'.subst (ρ.comp (ρ'.comp θ)).τ))) ∧
        (I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .zero →
          RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) ((c0 (k' + 1) ρ.up).isub (ISub.cons y hy (ρ'.comp θ)))
            ((c0' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons y' hy' θ))) ∧
        (I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .one →
          RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) ((c1 (k' + 1) ρ.up).isub (ISub.cons y hy (ρ'.comp θ)))
            ((c1' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons y' hy' θ))) ∧
        (RE2 S k4 (T.isub (ISub.cons y hy (ρ.comp (ρ'.comp θ)))) (a0.isub (ρ.comp (ρ'.comp θ))) (a0'.isub (ρ.comp (ρ'.comp θ))) → I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .zero →
          RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) (.papp (a0.isub (ρ.comp (ρ'.comp θ)))
            (r.subst (ρ.comp (ρ'.comp θ)).τ)) ((c0' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons y' hy' θ)) ∧
          RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) ((c0 (k' + 1) ρ.up).isub (ISub.cons y hy (ρ'.comp θ)))
            (.papp (a0'.isub (ρ.comp (ρ'.comp θ))) (r'.subst (ρ.comp (ρ'.comp θ)).τ))) ∧
        (RE2 S k4 (T.isub (ISub.cons y hy (ρ.comp (ρ'.comp θ)))) (a0.isub (ρ.comp (ρ'.comp θ))) (a0'.isub (ρ.comp (ρ'.comp θ))) → I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .one →
          RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) (.papp (a0.isub (ρ.comp (ρ'.comp θ)))
            (r.subst (ρ.comp (ρ'.comp θ)).τ)) ((c1' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons y' hy' θ)) ∧
          RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) ((c1 (k' + 1) ρ.up).isub (ISub.cons y hy (ρ'.comp θ)))
            (.papp (a0'.isub (ρ.comp (ρ'.comp θ))) (r'.subst (ρ.comp (ρ'.comp θ)).τ))) := by
      intro k4 θ y y' hy hy' hE'
      have eθ : (ρ.comp ρ').comp θ = ρ.comp (ρ'.comp θ) := ISub.comp_assoc _ _ _
      have c := Cpt k' ρ k4 (ρ'.comp θ) y hy
      have hXc := RT2.tyCode_l hW c (hX2 _ _ _ (hsc k4 (ρ.comp (ρ'.comp θ))))
      have toA : ∀ {u v : Tm}, RE2 S k4 ((W k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ)))).dinst
          (r.subst (ρ.comp (ρ'.comp θ)).τ)) u v → RE2 S k4 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp θ))) u v :=
        fun h => RE2.conv' hW c h hXc
      have hRc := RT2.refl hW (hX2 _ _ _ (hsc k4 (ρ.comp (ρ'.comp θ))))
        (hWs k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ))) _ _ (hsc k4 (ρ.comp (ρ'.comp θ))) (hsc k4 (ρ.comp (ρ'.comp θ))) (I_eq_refl _))
      -- the endpoints of the restricted lines, against the endpoints at the points
      have eL := hends (k' + 1) ρ.up k4 (ISub.cons y hy (ρ'.comp θ)) _ (ISub.up_comp_cons ρ y hy _)
      have eR := hends' (k'' + 1) (ρ.comp ρ').up k4 (ISub.cons y' hy' θ) _ (ISub.up_comp_cons (ρ.comp ρ') y' hy' θ)
      rw [eθ] at eR
      have ec := e_c k4 (ρ.comp (ρ'.comp θ)) y y' hy hy' hE'
      have toR0 : I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .zero → ∀ {u v : Tm},
          RE2 S k4 ((W k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ)))).dinst .zero) u v →
          RE2 S k4 ((W k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ)))).dinst (r.subst (ρ.comp (ρ'.comp θ)).τ)) u v :=
        fun e u v h => RE2.conv' hW (hWs k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ))) _ .zero (hsc k4 (ρ.comp (ρ'.comp θ))) trivial e) h (hX2 _ _ _ (hsc k4 (ρ.comp (ρ'.comp θ))))
      have toR1 : I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .one → ∀ {u v : Tm},
          RE2 S k4 ((W k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ)))).dinst .one) u v →
          RE2 S k4 ((W k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ)))).dinst (r.subst (ρ.comp (ρ'.comp θ)).τ)) u v :=
        fun e u v h => RE2.conv' hW (hWs k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ))) _ .one (hsc k4 (ρ.comp (ρ'.comp θ))) trivial e) h (hX2 _ _ _ (hsc k4 (ρ.comp (ρ'.comp θ))))
      -- the right endpoints at the points, against those of the left normal forms
      have ecR : (I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .zero → RE2 S k4
            ((W k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ)))).dinst (r.subst (ρ.comp (ρ'.comp θ)).τ))
            (c0' k4 (ISub.cons y' hy' (ρ.comp (ρ'.comp θ))))
            ((c0' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons y' hy' θ))) ∧
          (I.Eq (r.subst (ρ.comp (ρ'.comp θ)).τ) .one → RE2 S k4
            ((W k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ)))).dinst (r.subst (ρ.comp (ρ'.comp θ)).τ))
            (c1' k4 (ISub.cons y' hy' (ρ.comp (ρ'.comp θ))))
            ((c1' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons y' hy' θ))) := by
        have m := (pathW_rel hW (hLR k4 (ρ.comp (ρ'.comp θ)) y y' hy hy' hE') (hw _ _).1 (hw _ _).2.1).1
        refine ⟨fun e => ?_, fun e => ?_⟩
        · have t := m .zero .zero trivial trivial (I_eq_refl _)
          have hX0 := hX2 k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ))) .zero trivial
          have sy := RE2.symm hW (RT2.refl' hW hX0 t) eR.1
          exact toR0 e (RE2.conv' hW t sy hX0)
        · have t := m .one .one trivial trivial (I_eq_refl _)
          have hX1 := hX2 k4 (ISub.cons y hy (ρ.comp (ρ'.comp θ))) .one trivial
          have sy := RE2.symm hW (RT2.refl' hW hX1 t) eR.2
          exact toR1 e (RE2.conv' hW t sy hX1)
      refine ⟨fun hh => toA (e_pp k4 _ y hy hh), fun e => ?_, fun e => ?_, fun hh e => ⟨?_, ?_⟩,
        fun hh e => ⟨?_, ?_⟩⟩
      · exact toA (RE2.trans hW hRc (toR0 e eL.1) (RE2.trans hW hRc (ec.1 e) (ecR.1 e)))
      · exact toA (RE2.trans hW hRc (toR1 e eL.2) (RE2.trans hW hRc (ec.2 e) (ecR.2 e)))
      · have p := (e_pc k4 _ y y' hy hy' hE' hh).1 e
        exact toA (RE2.trans hW hRc p.1 (ecR.1 e))
      · have p := (e_pc k4 _ y y' hy hy' hE' hh).1 e
        exact toA (RE2.trans hW hRc (toR0 e eL.1) p.2)
      · have p := (e_pc k4 _ y y' hy hy' hE' hh).2 e
        exact toA (RE2.trans hW hRc p.1 (ecR.2 e))
      · have p := (e_pc k4 _ y y' hy hy' hE' hh).2 e
        exact toA (RE2.trans hW hRc (toR1 e eL.2) p.2)
    refine RE2.conv hW conv1 (comp2 hW ?_ ?_ ?_ ?_ ((HasTy.eqR EL).tyConv eT) ((HasTy.eqR ER).tyConv eT)
      (Eall.tyConv eT) ?_ (ent_or3 (ent_subst h12 _) (hEρ k'' _)) (ent_or3 (ent_subst h21 _) (I_eq_symm (hEρ k'' _)))
      ?_ ?_ ?_ ?_)
    · -- robustness across the two sides
      intro k3 τ y y' hy hy' hE'
      have e1 : (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up).isub (ISub.cons y hy τ) = ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons y hy (ρ'.comp τ)) := by
        rw [Tm.isub_isub, ISub.up_comp_cons]
      rw [e1]
      have c1 := Cpt k' ρ k3 (ρ'.comp τ) y hy
      have c2 := C'pt k'' (ρ.comp ρ') k3 τ y' hy'
      rw [ISub.comp_assoc] at c2
      have m := (pathW_rel hW (hLR k3 (ρ.comp (ρ'.comp τ)) y y' hy hy' hE') (hw _ _).1 (hw _ _).2.1).1 _ _
        (hsc k3 (ρ.comp (ρ'.comp τ))) (hsc' k3 (ρ.comp (ρ'.comp τ))) (hEρ k3 (ρ.comp (ρ'.comp τ)))
      exact RT2.trans hW (RT2.tyCode_l hW c1 (hX2 _ _ _ (hsc k3 (ρ.comp (ρ'.comp τ))))) c1
        (RT2.trans hW (hX2 _ _ _ (hsc k3 (ρ.comp (ρ'.comp τ)))) m (RT2.symm hW (RT2.tyCode_l hW c2 (RT2.tyCode_r hW m
          (hX2 _ _ _ (hsc k3 (ρ.comp (ρ'.comp τ)))))) c2))
    · -- robustness of the left line
      intro k3 τ y y' hy hy' hE'
      have e1 : ∀ (z : I) (hz : z.Scoped k3), (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up).isub (ISub.cons z hz τ) =
          ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons z hz (ρ'.comp τ)) := by
        intro z hz; rw [Tm.isub_isub, ISub.up_comp_cons]
      rw [e1, e1]
      have c1 := Cpt k' ρ k3 (ρ'.comp τ) y hy
      have c2 := Cpt k' ρ k3 (ρ'.comp τ) y' hy'
      have hTT3 : RT2 S k3 (T.isub (ISub.cons y hy (ρ.comp (ρ'.comp τ)))) (T.isub (ISub.cons y' hy' (ρ.comp (ρ'.comp τ)))) := by
        have a := hLR k3 (ρ.comp (ρ'.comp τ)) y y' hy hy' hE'
        have b := hLR k3 (ρ.comp (ρ'.comp τ)) y' y' hy' hy' (I_eq_refl _)
        have hX3 : TyCode k3 (semK S k3 (T.isub (ISub.cons y hy (ρ.comp (ρ'.comp τ))))) :=
          tyCode_of_univ hW (HasTy.isubS hW hTl' _)
        exact RT2.trans hW hX3 a (RT2.symm hW (RT2.tyCode_r hW a hX3 |> fun h => RT2.tyCode_l hW b h) b)
      have m := (pathW_rel hW hTT3 (hw _ _).1 (hw _ _).1).1 _ _ (hsc k3 (ρ.comp (ρ'.comp τ))) (hsc k3 (ρ.comp (ρ'.comp τ))) (I_eq_refl _)
      exact RT2.trans hW (RT2.tyCode_l hW c1 (hX2 _ _ _ (hsc k3 (ρ.comp (ρ'.comp τ))))) c1
        (RT2.trans hW (hX2 _ _ _ (hsc k3 (ρ.comp (ρ'.comp τ)))) m (RT2.symm hW (RT2.tyCode_l hW c2 (hX2 _ _ _ (hsc k3 (ρ.comp (ρ'.comp τ))))) c2))
    · -- transport along the restrictions of the left line
      intro k3 Θ X' hX'
      rw [Tm.isub_isub] at hX' ⊢
      exact hIHT k' ρ.up _ _ _ (hw _ _).1 _ (KubusCore.I.scoped_shift (hsc k' ρ)) k3 _ X' hX'
    · -- composition at the end of the left line
      intro X' hX'
      rw [eC1] at hX' ⊢
      exact hIHH (k' + 1) ρ.up _ _ _ (hw _ _).1 _ (KubusCore.I.scoped_shift (hsc k' ρ)) k'' _ X' hX'
    · -- the judgmental equality of the systems
      have eU : ((sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up))).isub ρ'.up = sysT (φ.subst (ρ.comp ρ').τ) (r.subst (ρ.comp ρ').τ) (a0.isub (ρ.comp ρ'))
          ((c0 (k' + 1) ρ.up).isub ρ'.up) ((c1 (k' + 1) ρ.up).isub ρ'.up) := by
        rw [sysT_isub, Tm.isub_isub, ← I_subst_comp, ← I_subst_comp]
      have eCc : (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift))).isub ρ'.up = ((W (k' + 1) ρ.up).isub ρ'.up.up).dinst ((r.subst (ρ.comp ρ').τ).shift) := by
        rw [isub_dinst]
        show ((W (k' + 1) ρ.up).isub ρ'.up.up).dinst (((r.subst ρ.τ).shift).subst (I.up ρ'.τ)) = _
        rw [I_shift_subst_up, ← I_subst_comp]
      rw [eU, eCc]
      -- the typings of the transports in the normal forms
      have hTW : ∀ k3 (σ : ISub k3 k), TyEq S (k3 + 1) (T.isub σ.up) (.path (W (k3 + 1) σ.up) (c0 (k3 + 1) σ.up)
          (c1 (k3 + 1) σ.up)) := fun k3 σ => (hw (k3 + 1) σ.up).1.2
      have hTW' : ∀ k3 (σ : ISub k3 k), TyEq S (k3 + 1) (T'.isub σ.up) (.path (W' (k3 + 1) σ.up) (c0' (k3 + 1) σ.up)
          (c1' (k3 + 1) σ.up)) := fun k3 σ => (hw (k3 + 1) σ.up).2.1.2
      have hLt := HasTy.isubS hW (HasTy.eqR (eq_transp_ty hW (hρT k' ρ) (hTW k' ρ))) ρ'
      have hLt' : HasTy S k'' .one [] (.transp (.path ((W (k' + 1) ρ.up).isub ρ'.up.up) ((c0 (k' + 1) ρ.up).isub ρ'.up)
          ((c1 (k' + 1) ρ.up).isub ρ'.up)) (φ.subst (ρ.comp ρ').τ) (a0.isub (ρ.comp ρ')))
          (((T.isub ρ.up).dinst .one).isub ρ') := by
        have e3 : (Tm.transp (.path (W (k' + 1) ρ.up) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)) (φ.subst ρ.τ)
            (a0.isub ρ)).isub ρ' = .transp (.path ((W (k' + 1) ρ.up).isub ρ'.up.up) ((c0 (k' + 1) ρ.up).isub ρ'.up)
            ((c1 (k' + 1) ρ.up).isub ρ'.up)) (φ.subst (ρ.comp ρ').τ) (a0.isub (ρ.comp ρ')) := by
          show Tm.transp ((Tm.path _ _ _).isub ρ'.up) ((φ.subst ρ.τ).subst ρ'.τ) ((a0.isub ρ).isub ρ') = _
          rw [isub_path, Tm.isub_isub, ← I_subst_comp]
        rw [e3] at hLt; exact hLt
      have hRt := HasTy.eqR (eq_transp_ty hW (hρT' k'' (ρ.comp ρ')) (hTW' k'' (ρ.comp ρ')))
      have ePL : TyEq S (k'' + 1) (.path ((W (k' + 1) ρ.up).isub ρ'.up.up) ((c0 (k' + 1) ρ.up).isub ρ'.up)
          ((c1 (k' + 1) ρ.up).isub ρ'.up)) (T.isub (ρ.comp ρ').up) := by
        have := (hTW k' ρ).isub hW ρ'.up
        rw [Tm.isub_isub, ← ISub.up_comp, isub_path] at this
        exact TyEq.symm this
      have ePP : TyEq S (k'' + 1) (.path ((W (k' + 1) ρ.up).isub ρ'.up.up) ((c0 (k' + 1) ρ.up).isub ρ'.up)
          ((c1 (k' + 1) ρ.up).isub ρ'.up)) (.path (W' (k'' + 1) (ρ.comp ρ').up) (c0' (k'' + 1) (ρ.comp ρ').up)
          (c1' (k'' + 1) (ρ.comp ρ').up)) :=
        TyEq.trans hW ePL (TyEq.trans hW (hP.tyEq.isub hW (ρ.comp ρ').up) (hTW' k'' (ρ.comp ρ')))
      have hPP : Tm.path ((W (k' + 1) ρ.up).isub ρ'.up.up) ((c0 (k' + 1) ρ.up).isub ρ'.up)
          ((c1 (k' + 1) ρ.up).isub ρ'.up) = .path (W' (k'' + 1) (ρ.comp ρ').up) (c0' (k'' + 1) (ρ.comp ρ').up)
          (c1' (k'' + 1) (ρ.comp ρ').up) ∨ ∃ l, EqTm0 S (k'' + 1) .one []
          (.path ((W (k' + 1) ρ.up).isub ρ'.up.up) ((c0 (k' + 1) ρ.up).isub ρ'.up) ((c1 (k' + 1) ρ.up).isub ρ'.up))
          (.path (W' (k'' + 1) (ρ.comp ρ').up) (c0' (k'' + 1) (ρ.comp ρ').up) (c1' (k'' + 1) (ρ.comp ρ').up))
          (.univ l) := by
        rcases ePP with e | ⟨l, e⟩
        · exact .inl e
        · exact .inr ⟨l, spec_to_minimal_eq hW e⟩
      have hp0 : EqTm S k'' .one [] (a0.isub (ρ.comp ρ')) (a0'.isub (ρ.comp ρ'))
          ((Tm.path ((W (k' + 1) ρ.up).isub ρ'.up.up) ((c0 (k' + 1) ρ.up).isub ρ'.up)
            ((c1 (k' + 1) ρ.up).isub ρ'.up)).dinst .zero) := by
        have e := EqTm.isubS hW (RE2.typed ha0).2.2 (ρ.comp ρ')
        rw [isub_dinst] at e
        exact e.tyConv (TyEq.symm (tyEq_dinst hW ePL (r := .zero) trivial))
      exact minimal_to_spec_eq (transpPath_sysr_eq hW (spec_to_minimal hW hLt') (spec_to_minimal hW hRt) hPP
        (spec_to_minimal_eq hW hp0) (ent_subst h12 _) (hsc k'' (ρ.comp ρ')) (hsc' k'' (ρ.comp ρ'))
        (hEρ k'' (ρ.comp ρ')))
    · -- the tubes
      intro k3 σ x x' hx hx' hEx hh
      have eσ : (ρ.comp ρ').comp σ = ρ.comp (ρ'.comp σ) := ISub.comp_assoc _ _ _
      have eA : (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up).isub (ISub.cons x hx σ) = ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons x hx (ρ'.comp σ)) := by
        rw [Tm.isub_isub, ISub.up_comp_cons]
      have eUL : (((sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)).isub ρ'.up).isub σ.up).dinst x = Tm.split (φ.subst (ρ.comp (ρ'.comp σ)).τ)
          (.papp (a0.isub (ρ.comp (ρ'.comp σ))) (r.subst (ρ.comp (ρ'.comp σ)).τ))
          (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ)) (r.subst (ρ.comp (ρ'.comp σ)).τ))
          (.split (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ)) ((c0 (k' + 1) ρ.up).isub (ISub.cons x hx (ρ'.comp σ)))
            (r.subst (ρ.comp (ρ'.comp σ)).τ) ((c1 (k' + 1) ρ.up).isub (ISub.cons x hx (ρ'.comp σ)))) := by
        rw [Tm.isub_isub, ← ISub.up_comp, sysT_isub_dinst, isub_up_dinst _ _ x hx, isub_up_dinst _ _ x hx,
          Tm.isub_isub, ← I_subst_comp, ← I_subst_comp]
      have eUR : ((sysT (φ'.subst (ρ.comp ρ').τ) (r'.subst (ρ.comp ρ').τ) (a0'.isub (ρ.comp ρ')) (c0' (k'' + 1) (ρ.comp ρ').up) (c1' (k'' + 1) (ρ.comp ρ').up)).isub σ.up).dinst x' = Tm.split (φ'.subst (ρ.comp (ρ'.comp σ)).τ)
          (.papp (a0'.isub (ρ.comp (ρ'.comp σ))) (r'.subst (ρ.comp (ρ'.comp σ)).τ))
          (.or (.neg (r'.subst (ρ.comp (ρ'.comp σ)).τ)) (r'.subst (ρ.comp (ρ'.comp σ)).τ))
          (.split (.neg (r'.subst (ρ.comp (ρ'.comp σ)).τ))
            ((c0' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons x' hx' σ))
            (r'.subst (ρ.comp (ρ'.comp σ)).τ) ((c1' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons x' hx' σ))) := by
        rw [sysT_isub_dinst, isub_up_dinst _ _ x' hx', isub_up_dinst _ _ x' hx', Tm.isub_isub, ← I_subst_comp,
          ← I_subst_comp, eσ]
      have tL := comp_tube_typed hW (HasTy.eqR EL) σ x hx hh
      have hh' : (ival (idEnv k3) ((I.or (φ'.subst (ρ.comp ρ').τ) (.or (.neg (r'.subst (ρ.comp ρ').τ)) (r'.subst (ρ.comp ρ').τ))).subst σ.τ)).holds :=
        entails_holds (ent_subst (ent_or3 (ent_subst h12 _) (hEρ k'' _)) σ.τ) hh
      have tR := comp_tube_typed hW (HasTy.eqR ER) σ x' hx' hh'
      rw [eA, eUL] at tL
      rw [eUR] at tR
      rw [eA, eUL, eUR]
      have LR : RT2 S k3 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons x hx (ρ'.comp σ))) (((W' (k'' + 1) (ρ.comp ρ').up).dinst ((r'.subst (ρ.comp ρ').τ).shift)).isub (ISub.cons x' hx' σ)) := by
        have c1 := Cpt k' ρ k3 (ρ'.comp σ) x hx
        have c2 := C'pt k'' (ρ.comp ρ') k3 σ x' hx'
        rw [ISub.comp_assoc] at c2
        have m := (pathW_rel hW (hLR k3 (ρ.comp (ρ'.comp σ)) x x' hx hx' hEx) (hw _ _).1 (hw _ _).2.1).1 _ _
          (hsc k3 (ρ.comp (ρ'.comp σ))) (hsc' k3 (ρ.comp (ρ'.comp σ))) (hEρ k3 (ρ.comp (ρ'.comp σ)))
        have hX0 := hX2 k3 (ISub.cons x hx (ρ.comp (ρ'.comp σ))) _ (hsc k3 (ρ.comp (ρ'.comp σ)))
        exact RT2.trans hW (RT2.tyCode_l hW c1 hX0) c1
          (RT2.trans hW hX0 m (RT2.symm hW (RT2.tyCode_l hW c2 (RT2.tyCode_r hW m hX0)) c2))
      replace tR := tR.tyConv (TyEq.symm (tyB LR))
      have hsφ3 : (I.or (φ.subst (ρ.comp (ρ'.comp σ)).τ) (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ))
          (r.subst (ρ.comp (ρ'.comp σ)).τ))).Scoped k3 :=
        ⟨I.scoped_subst hφs (ρ.comp (ρ'.comp σ)).sc, hsc k3 (ρ.comp (ρ'.comp σ)), hsc k3 (ρ.comp (ρ'.comp σ))⟩
      have hor : I.Entails .one (I.or (φ.subst (ρ.comp (ρ'.comp σ)).τ) (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ))
          (r.subst (ρ.comp (ρ'.comp σ)).τ))) := by
        refine (holds_iff_entails hsφ3).1 ?_
        have e2 : ((I.or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ)))).subst σ.τ = I.or (φ.subst (ρ.comp (ρ'.comp σ)).τ) (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ))
            (r.subst (ρ.comp (ρ'.comp σ)).τ)) := by
          show I.or ((φ.subst (ρ.comp ρ').τ).subst σ.τ) (.or (.neg ((r.subst (ρ.comp ρ').τ).subst σ.τ))
            ((r.subst (ρ.comp ρ').τ).subst σ.τ)) = _
          rw [← I_subst_comp, ← I_subst_comp, eσ]
        rw [← e2]; exact hh
      have c0t := Cpt k' ρ k3 (ρ'.comp σ) x hx
      have hAA := RT2.refl hW (RT2.tyCode_l hW c0t (hX2 k3 (ISub.cons x hx (ρ.comp (ρ'.comp σ))) _ (hsc k3 (ρ.comp (ρ'.comp σ))))) c0t
      -- normal forms of the restrictions of the branches
      have nA : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons x hx (ρ'.comp σ))).isub σ4 =
          ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons (x.subst σ4.τ) (I.scoped_subst hx σ4.sc) (ρ'.comp (σ.comp σ4))) := by
        intro k4 σ4; rw [Tm.isub_isub, ISub.cons_comp, ISub.comp_assoc]
      have nP : ∀ {k4 : ℕ} (σ4 : ISub k4 k3) (w : Tm) (z : I),
          (Tm.papp (w.isub (ρ.comp (ρ'.comp σ))) (z.subst (ρ.comp (ρ'.comp σ)).τ)).isub σ4 =
            .papp (w.isub (ρ.comp (ρ'.comp (σ.comp σ4)))) (z.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) := by
        intro k4 σ4 w z
        show Tm.papp ((w.isub _).isub σ4) ((z.subst _).subst σ4.τ) = _
        rw [Tm.isub_isub, ← I_subst_comp, ISub.comp_assoc, ISub.comp_assoc]
      have nL : ∀ {k4 : ℕ} (σ4 : ISub k4 k3) (w : Tm), (w.isub (ISub.cons x hx (ρ'.comp σ))).isub σ4 =
          w.isub (ISub.cons (x.subst σ4.τ) (I.scoped_subst hx σ4.sc) (ρ'.comp (σ.comp σ4))) := by
        intro k4 σ4 w; rw [Tm.isub_isub, ISub.cons_comp, ISub.comp_assoc]
      have nR : ∀ {k4 : ℕ} (σ4 : ISub k4 k3) (w : Tm), (w.isub (ISub.cons x' hx' σ)).isub σ4 =
          w.isub (ISub.cons (x'.subst σ4.τ) (I.scoped_subst hx' σ4.sc) (σ.comp σ4)) := by
        intro k4 σ4 w; rw [Tm.isub_isub, ISub.cons_comp]
      have hφ4 : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), I.Entails .one ((φ.subst (ρ.comp (ρ'.comp σ)).τ).subst σ4.τ) →
          (ival (idEnv k4) (φ.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ)).holds := by
        intro k4 σ4 h
        refine (holds_iff_entails (I.scoped_subst hφs (ρ.comp (ρ'.comp (σ.comp σ4))).sc)).2 ?_
        have := ent_comp_inv (φ := φ) (ρ := ρ.comp (ρ'.comp σ)) (ρ' := σ4) h
        rwa [ISub.comp_assoc, ISub.comp_assoc] at this
      have hr0 : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), I.Entails .one ((I.neg (r.subst (ρ.comp (ρ'.comp σ)).τ)).subst σ4.τ) →
          I.Eq (r.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) .zero := by
        intro k4 σ4 h
        have := ent_comp_inv (φ := .neg r) (ρ := ρ.comp (ρ'.comp σ)) (ρ' := σ4) h
        rw [ISub.comp_assoc, ISub.comp_assoc] at this
        exact ieq_zero_of_holds_neg (hsc k4 (ρ.comp (ρ'.comp (σ.comp σ4)))) (entails_holds this (ρ := idEnv k4) (by rw [ival_one]; rfl))
      have hr1 : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), I.Entails .one ((r.subst (ρ.comp (ρ'.comp σ)).τ).subst σ4.τ) →
          I.Eq (r.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) .one := by
        intro k4 σ4 h
        have := ent_comp_inv (φ := r) (ρ := ρ.comp (ρ'.comp σ)) (ρ' := σ4) h
        rw [ISub.comp_assoc, ISub.comp_assoc] at this
        exact ieq_one_of_holds (hsc k4 (ρ.comp (ρ'.comp (σ.comp σ4)))) (entails_holds this (ρ := idEnv k4) (by rw [ival_one]; rfl))
      refine RE2_pathSys hW (I.scoped_subst hφs (ρ.comp (ρ'.comp σ)).sc) (I.scoped_subst hφs' (ρ.comp (ρ'.comp σ)).sc) (hsc k3 (ρ.comp (ρ'.comp σ))) (hsc' k3 (ρ.comp (ρ'.comp σ))) (hEρ k3 (ρ.comp (ρ'.comp σ)))
        (ent_subst h12 _) (ent_subst h21 _) hor hAA tL tR (fun k4 σ4 h => ?_) (fun k4 σ4 h h' => ?_)
        (fun k4 σ4 h h' => ?_) (fun k4 σ4 h h' => ?_) (fun k4 σ4 h h' => ?_) (fun k4 σ4 h' => ?_)
        (fun k4 σ4 h' => ?_) <;> rw [nA σ4]
      · rw [nP, nP]; exact (pts k4 (σ.comp σ4) _ _ _ (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)).1 (aPt k4 _ _ _ (hφ4 σ4 h))
      · rw [nP, nR]
        exact ((pts k4 (σ.comp σ4) _ _ _ (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)).2.2.2.1 (aPt k4 _ _ _ (hφ4 σ4 h))
          (hr0 σ4 h')).1
      · rw [nL, nP]
        exact ((pts k4 (σ.comp σ4) _ _ _ (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)).2.2.2.1 (aPt k4 _ _ _ (hφ4 σ4 h))
          (hr0 σ4 h')).2
      · rw [nP, nR]
        exact ((pts k4 (σ.comp σ4) _ _ _ (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)).2.2.2.2 (aPt k4 _ _ _ (hφ4 σ4 h))
          (hr1 σ4 h')).1
      · rw [nL, nP]
        exact ((pts k4 (σ.comp σ4) _ _ _ (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)).2.2.2.2 (aPt k4 _ _ _ (hφ4 σ4 h))
          (hr1 σ4 h')).2
      · rw [nL, nR]
        exact (pts k4 (σ.comp σ4) _ _ _ (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)).2.1 (hr0 σ4 h')
      · rw [nL, nR]
        exact (pts k4 (σ.comp σ4) _ _ _ (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)).2.2.1 (hr1 σ4 h')
    · -- the bases
      have P := pts k'' (ISub.id k'') .zero .zero trivial trivial (I_eq_refl _)
      simp only [ISub.comp_id] at P
      rw [isub_up_dinst _ ρ' .zero trivial]
      have h0 := RE2.isub hW ha0 (ρ.comp ρ')
      rw [hT0] at h0
      exact P.1 h0
    all_goals intro k3 σ hh
    all_goals
      have eσ : (ρ.comp ρ').comp σ = ρ.comp (ρ'.comp σ) := ISub.comp_assoc _ _ _
    all_goals
      have eA : (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub ρ'.up).isub (ISub.cons .zero trivial σ) =
          ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons .zero trivial (ρ'.comp σ)) := by rw [Tm.isub_isub, ISub.up_comp_cons]
    all_goals
      have eP : ∀ (w : Tm) (z : I), (Tm.papp (w.isub (ρ.comp ρ')) (z.subst (ρ.comp ρ').τ)).isub σ =
          .papp (w.isub (ρ.comp (ρ'.comp σ))) (z.subst (ρ.comp (ρ'.comp σ)).τ) := by
        intro w z
        show Tm.papp ((w.isub _).isub σ) ((z.subst _).subst σ.τ) = _
        rw [Tm.isub_isub, ← I_subst_comp, eσ]
    all_goals
      have h0 : RE2 S k3 (T.isub (ISub.cons .zero trivial (ρ.comp (ρ'.comp σ))))
          (a0.isub (ρ.comp (ρ'.comp σ))) (a0'.isub (ρ.comp (ρ'.comp σ))) := by
        have := RE2.isub hW ha0 (ρ.comp (ρ'.comp σ)); rwa [hT0] at this
    all_goals
      have P := pts k3 σ .zero .zero trivial trivial (I_eq_refl _)
    all_goals
      have c0t := Cpt k' ρ k3 (ρ'.comp σ) .zero trivial
    all_goals
      have hAA := RT2.refl hW (RT2.tyCode_l hW c0t (hX2 k3 (ISub.cons .zero trivial (ρ.comp (ρ'.comp σ))) _
        (hsc k3 (ρ.comp (ρ'.comp σ))))) c0t
    all_goals
      have hsc3 : (I.or (φ.subst (ρ.comp (ρ'.comp σ)).τ) (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ))
            (r.subst (ρ.comp (ρ'.comp σ)).τ))).Scoped k3 :=
          ⟨I.scoped_subst hφs (ρ.comp (ρ'.comp σ)).sc, hsc k3 (ρ.comp (ρ'.comp σ)), hsc k3 (ρ.comp (ρ'.comp σ))⟩
    all_goals
      have hor : I.Entails .one (I.or (φ.subst (ρ.comp (ρ'.comp σ)).τ) (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ))
            (r.subst (ρ.comp (ρ'.comp σ)).τ))) := by
        refine (holds_iff_entails hsc3).1 ?_
        have e2 : (I.or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ))).subst σ.τ =
            I.or (φ.subst (ρ.comp (ρ'.comp σ)).τ) (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ))
              (r.subst (ρ.comp (ρ'.comp σ)).τ)) := by
          show I.or ((φ.subst (ρ.comp ρ').τ).subst σ.τ) (.or (.neg ((r.subst (ρ.comp ρ').τ).subst σ.τ))
            ((r.subst (ρ.comp ρ').τ).subst σ.τ)) = _
          rw [← I_subst_comp, ← I_subst_comp, eσ]
        rw [← e2]; exact hh
    all_goals
      have nA : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons .zero trivial (ρ'.comp σ))).isub σ4 =
            ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons .zero trivial (ρ'.comp (σ.comp σ4))) := by
          intro k4 σ4; rw [Tm.isub_isub, ISub.cons_comp, ISub.comp_assoc]; rfl
    all_goals
      have nP : ∀ {k4 : ℕ} (σ4 : ISub k4 k3) (w : Tm) (z : I),
            (Tm.papp (w.isub (ρ.comp (ρ'.comp σ))) (z.subst (ρ.comp (ρ'.comp σ)).τ)).isub σ4 =
              .papp (w.isub (ρ.comp (ρ'.comp (σ.comp σ4)))) (z.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) := by
          intro k4 σ4 w z
          show Tm.papp ((w.isub _).isub σ4) ((z.subst _).subst σ4.τ) = _
          rw [Tm.isub_isub, ← I_subst_comp, ISub.comp_assoc, ISub.comp_assoc]
    all_goals
      have nL : ∀ {k4 : ℕ} (σ4 : ISub k4 k3) (w : Tm), (w.isub (ISub.cons .zero trivial (ρ'.comp σ))).isub σ4 =
            w.isub (ISub.cons .zero trivial (ρ'.comp (σ.comp σ4))) := by
          intro k4 σ4 w; rw [Tm.isub_isub, ISub.cons_comp, ISub.comp_assoc]; rfl
    all_goals
      have nR : ∀ {k4 : ℕ} (σ4 : ISub k4 k3) (w : Tm), (w.isub (ISub.cons .zero trivial σ)).isub σ4 =
            w.isub (ISub.cons .zero trivial (σ.comp σ4)) := by
          intro k4 σ4 w; rw [Tm.isub_isub, ISub.cons_comp]; rfl
    all_goals
      have h04 : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), RE2 S k4 (T.isub (ISub.cons .zero trivial
          (ρ.comp (ρ'.comp (σ.comp σ4))))) (a0.isub (ρ.comp (ρ'.comp (σ.comp σ4))))
          (a0'.isub (ρ.comp (ρ'.comp (σ.comp σ4)))) := by
        intro k4 σ4; have := RE2.isub hW ha0 (ρ.comp (ρ'.comp (σ.comp σ4))); rwa [hT0] at this
    all_goals
      have P4 := fun {k4 : ℕ} (σ4 : ISub k4 k3) => pts k4 (σ.comp σ4) .zero .zero trivial trivial (I_eq_refl _)
    all_goals
      have hr0 : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), I.Entails .one ((I.neg (r.subst (ρ.comp (ρ'.comp σ)).τ)).subst σ4.τ) →
            I.Eq (r.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) .zero := by
          intro k4 σ4 h
          have := ent_comp_inv (φ := .neg r) (ρ := ρ.comp (ρ'.comp σ)) (ρ' := σ4) h
          rw [ISub.comp_assoc, ISub.comp_assoc] at this
          exact ieq_zero_of_holds_neg (hsc k4 (ρ.comp (ρ'.comp (σ.comp σ4))))
            (entails_holds this (ρ := idEnv k4) (by rw [ival_one]; rfl))
    all_goals
      have hr1 : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), I.Entails .one ((r.subst (ρ.comp (ρ'.comp σ)).τ).subst σ4.τ) →
            I.Eq (r.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) .one := by
          intro k4 σ4 h
          have := ent_comp_inv (φ := r) (ρ := ρ.comp (ρ'.comp σ)) (ρ' := σ4) h
          rw [ISub.comp_assoc, ISub.comp_assoc] at this
          exact ieq_one_of_holds (hsc k4 (ρ.comp (ρ'.comp (σ.comp σ4))))
            (entails_holds this (ρ := idEnv k4) (by rw [ival_one]; rfl))
    · -- the boundary, on the left
      have eU0 : (((sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)).isub ρ'.up).isub σ.up).dinst .zero = Tm.split (φ.subst (ρ.comp (ρ'.comp σ)).τ)
          (.papp (a0.isub (ρ.comp (ρ'.comp σ))) (r.subst (ρ.comp (ρ'.comp σ)).τ))
          (.or (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ)) (r.subst (ρ.comp (ρ'.comp σ)).τ))
          (.split (.neg (r.subst (ρ.comp (ρ'.comp σ)).τ)) ((c0 (k' + 1) ρ.up).isub (ISub.cons .zero trivial (ρ'.comp σ)))
            (r.subst (ρ.comp (ρ'.comp σ)).τ) ((c1 (k' + 1) ρ.up).isub (ISub.cons .zero trivial (ρ'.comp σ)))) := by
        rw [Tm.isub_isub, ← ISub.up_comp, sysT_isub_dinst, isub_up_dinst _ _ .zero trivial,
          isub_up_dinst _ _ .zero trivial, Tm.isub_isub, ← I_subst_comp, ← I_subst_comp]
      have tL := comp_tube_typed hW (HasTy.eqR EL) σ .zero trivial hh
      rw [eA, eU0] at tL
      rw [eA, eU0, eP]
      have hq := (RE2.typed (P.1 h0)).2.1
      refine RE2.symm hW hAA (RE2_sys_r hW (I.scoped_subst hφs (ρ.comp (ρ'.comp σ)).sc) (hsc k3 _) hor hAA tL hq
        (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_)) <;> rw [nA σ4]
      · rw [nP, nP]
        have Q := (P4 σ4).1 (h04 σ4)
        exact RE2.symm hW (RT2.isub hW (RT2.tyCode_l hW c0t (hX2 _ _ _ (hsc k3 _))) hAA σ4 |> fun h => by
          rw [nA σ4] at h; exact h) Q
      · rw [nP, nL]
        have Q := ((P4 σ4).2.2.2.1 (h04 σ4) (hr0 σ4 h)).2
        exact RE2.symm hW (RT2.isub hW (RT2.tyCode_l hW c0t (hX2 _ _ _ (hsc k3 _))) hAA σ4 |> fun h => by
          rw [nA σ4] at h; exact h) Q
      · rw [nP, nL]
        have Q := ((P4 σ4).2.2.2.2 (h04 σ4) (hr1 σ4 h)).2
        exact RE2.symm hW (RT2.isub hW (RT2.tyCode_l hW c0t (hX2 _ _ _ (hsc k3 _))) hAA σ4 |> fun h => by
          rw [nA σ4] at h; exact h) Q
    · -- the boundary, on the right
      have eU0 : ((sysT (φ'.subst (ρ.comp ρ').τ) (r'.subst (ρ.comp ρ').τ) (a0'.isub (ρ.comp ρ')) (c0' (k'' + 1) (ρ.comp ρ').up) (c1' (k'' + 1) (ρ.comp ρ').up)).isub σ.up).dinst .zero = Tm.split (φ'.subst (ρ.comp (ρ'.comp σ)).τ)
          (.papp (a0'.isub (ρ.comp (ρ'.comp σ))) (r'.subst (ρ.comp (ρ'.comp σ)).τ))
          (.or (.neg (r'.subst (ρ.comp (ρ'.comp σ)).τ)) (r'.subst (ρ.comp (ρ'.comp σ)).τ))
          (.split (.neg (r'.subst (ρ.comp (ρ'.comp σ)).τ))
            ((c0' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons .zero trivial σ))
            (r'.subst (ρ.comp (ρ'.comp σ)).τ) ((c1' (k'' + 1) (ρ.comp ρ').up).isub (ISub.cons .zero trivial σ))) := by
        rw [sysT_isub_dinst, isub_up_dinst _ _ .zero trivial, isub_up_dinst _ _ .zero trivial, Tm.isub_isub,
          ← I_subst_comp, ← I_subst_comp, eσ]
      have hh' : (ival (idEnv k3) ((I.or (φ'.subst (ρ.comp ρ').τ) (.or (.neg (r'.subst (ρ.comp ρ').τ))
          (r'.subst (ρ.comp ρ').τ))).subst σ.τ)).holds :=
        entails_holds (ent_subst (ent_or3 (ent_subst h12 _) (hEρ k'' _)) σ.τ) hh
      have tR := comp_tube_typed hW (HasTy.eqR ER) σ .zero trivial hh'
      rw [eU0] at tR
      have LR : RT2 S k3 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons .zero trivial (ρ'.comp σ))) (((W' (k'' + 1) (ρ.comp ρ').up).dinst ((r'.subst (ρ.comp ρ').τ).shift)).isub (ISub.cons .zero trivial σ)) := by
        have c1 := Cpt k' ρ k3 (ρ'.comp σ) .zero trivial
        have c2 := C'pt k'' (ρ.comp ρ') k3 σ .zero trivial
        rw [ISub.comp_assoc] at c2
        have m := (pathW_rel hW (hLR k3 (ρ.comp (ρ'.comp σ)) .zero .zero trivial trivial (I_eq_refl _)) (hw _ _).1
          (hw _ _).2.1).1 _ _ (hsc k3 (ρ.comp (ρ'.comp σ))) (hsc' k3 (ρ.comp (ρ'.comp σ))) (hEρ k3 (ρ.comp (ρ'.comp σ)))
        have hX0 := hX2 k3 (ISub.cons .zero trivial (ρ.comp (ρ'.comp σ))) _ (hsc k3 (ρ.comp (ρ'.comp σ)))
        exact RT2.trans hW (RT2.tyCode_l hW c1 hX0) c1
          (RT2.trans hW hX0 m (RT2.symm hW (RT2.tyCode_l hW c2 (RT2.tyCode_r hW m hX0)) c2))
      replace tR := tR.tyConv (TyEq.symm (tyB LR))
      rw [eA, eU0, eP]
      have hq := (RE2.typed (P.1 h0)).1
      have hor' : I.Entails .one (I.or (φ'.subst (ρ.comp (ρ'.comp σ)).τ) (.or (.neg (r'.subst (ρ.comp (ρ'.comp σ)).τ))
          (r'.subst (ρ.comp (ρ'.comp σ)).τ))) := ent_trans hor (ent_or3 (ent_subst h12 _) (hEρ k3 _))
      refine RE2_sys_r hW (I.scoped_subst hφs' (ρ.comp (ρ'.comp σ)).sc) (hsc' k3 _) hor' hAA tR hq
        (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_) <;> rw [nA σ4]
      · rw [nP, nP]; exact (P4 σ4).1 (h04 σ4)
      · rw [nP, nR]
        have e0 : I.Eq (r.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) .zero := by
          have := ent_comp_inv (φ := .neg r') (ρ := ρ.comp (ρ'.comp σ)) (ρ' := σ4) h
          rw [ISub.comp_assoc, ISub.comp_assoc] at this
          exact I_eq_trans (hEρ k4 _) (ieq_zero_of_holds_neg (hsc' k4 _)
            (entails_holds this (ρ := idEnv k4) (by rw [ival_one]; rfl)))
        exact ((P4 σ4).2.2.2.1 (h04 σ4) e0).1
      · rw [nP, nR]
        have e1 : I.Eq (r.subst (ρ.comp (ρ'.comp (σ.comp σ4))).τ) .one := by
          have := ent_comp_inv (φ := r') (ρ := ρ.comp (ρ'.comp σ)) (ρ' := σ4) h
          rw [ISub.comp_assoc, ISub.comp_assoc] at this
          exact I_eq_trans (hEρ k4 _) (ieq_one_of_holds (hsc' k4 _)
            (entails_holds this (ρ := idEnv k4) (by rw [ival_one]; rfl)))
        exact ((P4 σ4).2.2.2.2 (h04 σ4) e1).1
  -- the expansion
  have hX : TyCode k (semK S k (L1.dinst r)) := by have := hX2 k ι1 r hr; rwa [hL1] at this
  have hYY : RT2 S k (L1.dinst r) (L1.dinst r) := by
    have := hWW' k ι1 r r hr hr (I_eq_refl r); rw [hL1] at this; exact RT2.refl hW hX this
  have hpT : HasTy S k .one [] (.transp T φ a0) (.path L1 b0 b1) := hty.tyConv hR1.2
  refine RE2.expandBoth hW hX hYY (HasTy.papp hpT hr) (HasTy.eqR hE0)
    (fun k' ρ => if I.Entails .one (φ.subst ρ.τ) then .papp (a0.isub ρ) (r.subst ρ.τ)
      else Tm.comp ((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)) (.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))) (sysT (φ.subst ρ.τ) (r.subst ρ.τ) (a0.isub ρ) (c0 (k' + 1) ρ.up) (c1 (k' + 1) ρ.up)) (.papp (a0.isub ρ) (r.subst ρ.τ)))
    (fun k' ρ => if I.Entails .one (φ'.subst ρ.τ) then .papp (a0'.isub ρ) (r'.subst ρ.τ)
      else Tm.comp ((W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)) (.or (φ'.subst ρ.τ) (.or (.neg (r'.subst ρ.τ)) (r'.subst ρ.τ))) (sysT (φ'.subst ρ.τ) (r'.subst ρ.τ) (a0'.isub ρ) (c0' (k' + 1) ρ.up) (c1' (k' + 1) ρ.up)) (.papp (a0'.isub ρ) (r'.subst ρ.τ)))
    (fun k' ρ => ?_) (fun k' ρ => ?_) (fun k' ρ k'' ρ' => ?_)
  · by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · simp only [if_pos hf]; exact faceL k' ρ hf
    · simp only [if_neg hf]; exact redL k' ρ hf
  · by_cases hf : I.Entails .one (φ'.subst ρ.τ)
    · simp only [if_pos hf]; exact faceR k' ρ hf
    · simp only [if_neg hf]; exact redR k' ρ hf
  · have hpa : (Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ' = .papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ) := by
      show Tm.papp ((a0.isub ρ).isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = _
      rw [Tm.isub_isub, I_subst_comp]
    by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · have hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ) := ent_comp hf
      have hf2' : I.Entails .one (φ'.subst (ρ.comp ρ').τ) := ent_trans hf2 (ent_subst h12 _)
      simp only [if_pos hf, if_pos hf2']
      rw [hpa]
      exact faceRel k'' _ hf2
    · simp only [if_neg hf]
      rw [comp_isub, hpa]
      by_cases hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ)
      · simp only [if_pos (ent_trans hf2 (ent_subst h12 _))]
        have e : (I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).subst ρ'.τ =
            .or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ)) := by
          show I.or ((φ.subst ρ.τ).subst ρ'.τ) (.or (.neg ((r.subst ρ.τ).subst ρ'.τ)) ((r.subst ρ.τ).subst ρ'.τ)) = _
          rw [← I_subst_comp, ← I_subst_comp]
        have hcT := HasTy.isubS hW (HasTy.eqR (redL k' ρ hf).2) ρ'
        rw [comp_isub, hpa, Tm.isub_isub (L1.dinst r), e] at hcT
        rw [e]
        rw [comp_eq] at hcT ⊢
        have hYσ := RT2.isub hW hX hYY (ρ.comp ρ')
        have hor : I.Entails .one (.or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ))) :=
          ent_trans hf2 (ent_or_left _ _)
        have hh2 := (holds_iff_entails (show (I.or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ))
          (r.subst (ρ.comp ρ').τ))).Scoped k'' from ⟨I.scoped_subst hφs (ρ.comp ρ').sc, hsc k'' _, hsc k'' _⟩)).2 hor
        have s1 := stable_hcompFace hW hor hcT
        have t2 := hcomp_tube_typed' hW hcT .one trivial hh2
        rw [compTube_d1] at t2 s1
        have s2 := stable_transpFace hW (ent_refl .one) t2
        have t3 := HasTy.eqR (EqTm.transpFace (ent_refl .one) t2)
        have hpa' : Tm.papp ((a0.isub ρ).isub ρ') ((r.subst ρ.τ).subst ρ'.τ) =
            .papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ) := by rw [Tm.isub_isub, ← I_subst_comp]
        rw [sysT_isub_dinst, hpa'] at t3 s2 t2 s1
        have hf2' : I.Entails .one ((φ.subst ρ.τ).subst ρ'.τ) := by rw [← I_subst_comp]; exact hf2
        have s3 := stable_splitL hW hf2' t3
        have e0 := faceRel k'' (ρ.comp ρ') hf2
        have e1 := RE2.expandL hW hYσ t3 (RE2.typed e0).2.1 s3 e0
        have e2 := RE2.expandL hW hYσ t2 (RE2.typed e0).2.1 s2 e1
        exact RE2.expandL hW hYσ hcT (RE2.typed e0).2.1 s1 e2
      · have hf2' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hf2 (ent_trans h (ent_subst h21 _))
        simp only [if_neg hf2']
        have e : (I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).subst ρ'.τ =
            .or (φ.subst (ρ.comp ρ').τ) (.or (.neg (r.subst (ρ.comp ρ').τ)) (r.subst (ρ.comp ρ').τ)) := by
          show I.or ((φ.subst ρ.τ).subst ρ'.τ) (.or (.neg ((r.subst ρ.τ).subst ρ'.τ)) ((r.subst ρ.τ).subst ρ'.τ)) = _
          rw [← I_subst_comp, ← I_subst_comp]
        rw [e]
        exact compC k' ρ k'' ρ' hf2

end

end Model.Whnf
