import Model.Whnf.Kan2ElimT
import Model.Whnf.Kan2IPi

/-!
# The binary transport at types of the form `(i : I) → A`
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem transpIPi_body' (A u0 : Tm) (φ r : I) : ∃ t, Tm.transpIPi A φ u0 = .plam t ∧
    t.dinst r = .transp (A.dinst r.shift) φ (.papp u0 r) := by
  obtain ⟨t, ht, htr⟩ := transpIPi_body A u0 φ r
  refine ⟨t, ht, htr.trans ?_⟩
  congr 1
  simp only [Tm.dinst, Tm.dsubst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · rfl
  · rfl
  · show ((Tm.var (i + 1) : Tm) |> fun _ => (I.var (i + 2)).subst (I.up (I.inst0 r))) = _
    rfl

theorem ipi_dinst (A : Tm) (s : I) : (Tm.ipi A).dinst s = .ipi (A.dsubst (I.up (I.inst0 s))) := rfl

theorem dinst_shift_one (A : Tm) (r : I) :
    (A.dinst r.shift).dinst .one = (A.dsubst (I.up (I.inst0 .one))).dinst r := by
  simp only [Tm.dinst, Tm.dsubst, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · exact I_shift_inst0 r .one
  · rfl
  · rfl

/-- The double instantiation of a line of lines, as an interval substitution. -/
theorem dinst_shift_dinst {X : Tm} (hX : X.closedB 0 (k + 2) = true) (t x : I) (ht : t.Scoped k) (hx : x.Scoped k) :
    (X.dinst t.shift).dinst x = X.isub (ISub.cons t ht (ISub.cons x hx (ISub.id k))) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.isub, subst_subst]
  refine closed_subst_eq X 0 (k + 2) _ _ _ _ hX (fun _ h => absurd h (Nat.not_lt_zero _)) fun i hi => ?_
  rcases i with _ | _ | i
  · exact I_shift_inst0 t x
  · rfl
  · show I.var i = (ISub.id k).τ i
    simp [ISub.id, show i < k by omega]

variable (hW : WfSig S)
include hW

omit hW in
theorem step_transp_ipi {A a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.transp (.ipi A) φ a) = some (Tm.transpIPi A φ a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

/-- A point of a transport along a line of interval Π-types whose face does not hold. -/
theorem papp_transp_ipi {T A2 a0 : Tm} {φ r : I} (hn : ¬ I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hR : RedT S (k + 1) T (.ipi A2)) :
    Red S (.papp (.transp T φ a0) r) (.transp (A2.dinst r.shift) φ (.papp a0 r)) ∧
    EqTm S k .one [] (.papp (.transp T φ a0) r) (.transp (A2.dinst r.shift) φ (.papp a0 r))
      ((A2.dinst r.shift).dinst .one) := by
  obtain ⟨t, ht, htr⟩ := transpIPi_body' A2 a0 φ r
  have e1 := eq_transp_ty hW hty hR.2
  have e2 := EqTm.transpIPi (HasTy.eqR e1)
  have hT1 : TyEq S k (T.dinst .one) (.ipi (A2.dsubst (I.up (I.inst0 .one)))) := by
    have := tyEq_dinst hW hR.2 (r := .one) trivial; rwa [ipi_dinst] at this
  have e3 := (e1.trans e2).tyConv hT1
  have e4 := EqTm.iapp e3 hr hr (I_eq_refl r)
  rw [ht] at e4
  have e5 := EqTm.pathBeta (HasTy.eqR e4)
  rw [htr] at e5
  rw [← dinst_shift_one] at e4 e5
  refine ⟨(red_papp r ((red_transp_ty hn hR.1.1).trans (.step (step_transp_ipi hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rw [ht]; show some (t.dinst r) = _; rw [htr]

/-- A point of a transport whose face holds. -/
theorem papp_transp_face {T L a0 : Tm} {φ r : I} (h : I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one)) (hT1 : TyEq S k (T.dinst .one) (.ipi L)) :
    Red S (.papp (.transp T φ a0) r) (.papp a0 r) ∧
    EqTm S k .one [] (.papp (.transp T φ a0) r) (.papp a0 r) (L.dinst r) :=
  ⟨red_papp r (.step (step_transp_face h) (.refl _)),
    EqTm.iapp ((EqTm.transpFace h hty).tyConv hT1) hr hr (I_eq_refl r)⟩

/-- The interval Π-type a type reduces to is typed. -/
theorem ipiW_typed {X L : Tm} (hX : IsTyK S k X) (hR : RedT S k X (.ipi L)) :
    ∃ l, HasTy S k .one [] (.ipi L) (.univ l) :=
  ty_of_tyEq hW hX hR.2 (fun l h => by cases h)

/-- The lines of the normal forms of related types are related at related points. -/
theorem ipiW_rel {X Y L L' : Tm} (h : RT2 S k X Y) (hX : RedT S k X (.ipi L)) (hY : RedT S k Y (.ipi L'))
    (s s' : I) (hs : s.Scoped k) (hs' : s'.Scoped k) (hE : I.Eq s s') : RT2 S k (L.dinst s) (L'.dinst s') := by
  obtain ⟨l, hipi⟩ := ipiW_typed hW (Comp2_ty_base h).2.1 hX
  obtain ⟨L1, L1', h1, h2, -, h4⟩ := (IPiStr_of hW h hX hipi).whnf k (ISub.id k)
  have hXc := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base h).2.1)
  have hYc := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base h).2.2.1)
  rw [hXc] at h1; rw [hYc] at h2
  obtain rfl : L1 = L := by have := RedW.unique h1.1 hX.1; injection this
  obtain rfl : L1' = L' := by have := RedW.unique h2.1 hY.1; injection this
  exact h4 s s' hs hs' hE

omit hW in
theorem ieq_shift {x y : I} (h : I.Eq x y) : I.Eq x.shift y.shift := fun ρ0 => by
  simp only [I.shift, eval_ren]; exact h _

/-- Transport along related lines of interval Π-types, at related points. -/
theorem kanT2_ipi_core {T T' : Tm} (hP : IPiStr S (k + 1) T T') (hLR : LineRob S k T T')
    (hIH : ∀ k1 (ρ : ISub (k1 + 1) (k + 1)) L, RedT S (k1 + 1) (T.isub ρ) (.ipi L) → ∀ (s : I),
      s.Scoped (k1 + 1) → ∀ k2 (ρ' : ISub (k2 + 1) (k1 + 1)) X', RT2 S (k2 + 1) ((L.dinst s).isub ρ') X' →
      KanT2 S k2 ((L.dinst s).isub ρ') X')
    {φ φ' : I} {a0 a0' : Tm} (hC : LineConst S k T φ)
    (hty : HasTy S k .one [] (.transp T φ a0) (T.dinst .one))
    (hty' : HasTy S k .one [] (.transp T' φ' a0') (T.dinst .one))
    (heq : EqTm S k .one [] (.transp T φ a0) (.transp T' φ' a0') (T.dinst .one))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (ha0 : RE2 S k (T.dinst .zero) a0 a0')
    {L1 : Tm} (hR1 : RedT S k (T.dinst .one) (.ipi L1)) {r r' : I} (hr : r.Scoped k) (hr' : r'.Scoped k)
    (hE : I.Eq r r') :
    RE2 S k (L1.dinst r) (.papp (.transp T φ a0) r) (.papp (.transp T' φ' a0') r') := by
  obtain ⟨l0, ⟨hTl, hφs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  choose W W' hw using hP.whnf
  have hT0 : ∀ {k3 : ℕ} (v : ISub k3 k), (T.dinst .zero).isub v = T.isub (ISub.cons .zero trivial v) := fun v => by
    rw [isub_dinst]; exact isub_up_dinst T v .zero trivial
  let ι1 : ISub k (k + 1) := ISub.cons .one trivial (ISub.id k)
  have hR1' : RedT S k (T.isub ι1) (.ipi L1) := by rw [isub_cons_id_of_closed hTc]; exact hR1
  have hL1 : W k ι1 = L1 := by have := RedW.unique (hw k ι1).1.1 hR1'.1; injection this
  have hrid : r.subst (ISub.id k).τ = r := I_subst_id hr
  have hrid' : r'.subst (ISub.id k).τ = r' := I_subst_id hr'
  have hsc : ∀ k' (ρ : ISub k' k), (r.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr ρ.sc
  have hsc' : ∀ k' (ρ : ISub k' k), (r'.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr' ρ.sc
  have hEρ : ∀ k' (ρ : ISub k' k), I.Eq (r.subst ρ.τ) (r'.subst ρ.τ) := fun k' ρ => I_eq_subst hE ρ.τ
  have hX2 : ∀ k3 (σ : ISub k3 (k + 1)) (s : I), s.Scoped k3 → TyCode k3 (semK S k3 ((W k3 σ).dinst s)) :=
    fun k3 σ s hs => hP.tc k3 σ _ (hw k3 σ).1 s hs
  have hWW' : ∀ k3 (σ : ISub k3 (k + 1)) (s s' : I), s.Scoped k3 → s'.Scoped k3 → I.Eq s s' →
      RT2 S k3 ((W k3 σ).dinst s) ((W' k3 σ).dinst s') := fun k3 σ => (hw k3 σ).2.2.2
  have hcohW : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      ∀ (s : I), s.Scoped k2 → RT2 S k2 (((W k1 σ1).isub θ.up).dinst s) ((W k2 σ2).dinst s) := by
    intro k1 σ1 k2 θ σ2 h s hs; subst h
    exact hP.coh k1 σ1 k2 θ _ _ (hw k1 σ1).1 (hw k2 _).1 s hs
  have hcohW' : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      ∀ (s : I), s.Scoped k2 → RT2 S k2 (((W' k1 σ1).isub θ.up).dinst s) ((W' k2 σ2).dinst s) := by
    intro k1 σ1 k2 θ σ2 h s hs; subst h
    exact hP.coh' k1 σ1 k2 θ _ _ (hw k1 σ1).2.1 (hw k2 _).2.1 s hs
  -- the type of the points, at a restriction
  have Ypt : ∀ k3 (v : ISub k3 k), RT2 S k3 ((L1.dinst r).isub v)
      ((W k3 (ISub.cons .one trivial v)).dinst (r.subst v.τ)) := by
    intro k3 v; rw [isub_dinst, ← hL1]
    exact hcohW k ι1 k3 v _ (cons_one_comp v) _ (hsc k3 v)
  have hXY : ∀ k3 (v : ISub k3 k), TyCode k3 (semK S k3 ((L1.dinst r).isub v)) := fun k3 v =>
    RT2.tyCode_l hW (Ypt k3 v) (hX2 k3 _ _ (hsc k3 v))
  -- the eliminated lines
  let C : ∀ k' (_ : ISub k' k), Tm := fun k' ρ => (W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)
  let C' : ∀ k' (_ : ISub k' k), Tm := fun k' ρ => (W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)
  have Cpt : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      RT2 S k3 ((C k' ρ).isub (ISub.cons x hx θ)) ((W k3 (ISub.cons x hx (ρ.comp θ))).dinst (r.subst (ρ.comp θ).τ)) := by
    intro k' ρ k3 θ x hx
    show RT2 S k3 (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).isub (ISub.cons x hx θ)) _
    rw [isub_dinst, I_shift_cons, ← I_subst_comp]
    exact hcohW (k' + 1) ρ.up k3 (ISub.cons x hx θ) _ (ISub.up_comp_cons ρ x hx θ) _ (hsc k3 _)
  have C'pt : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I) (hx : x.Scoped k3),
      RT2 S k3 ((C' k' ρ).isub (ISub.cons x hx θ)) ((W' k3 (ISub.cons x hx (ρ.comp θ))).dinst (r'.subst (ρ.comp θ).τ)) := by
    intro k' ρ k3 θ x hx
    show RT2 S k3 (((W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)).isub (ISub.cons x hx θ)) _
    rw [isub_dinst, I_shift_cons, ← I_subst_comp]
    exact hcohW' (k' + 1) ρ.up k3 (ISub.cons x hx θ) _ (ISub.up_comp_cons ρ x hx θ) _ (hsc' k3 _)
  have Cd1 : ∀ k' (ρ : ISub k' k), RT2 S k' ((C k' ρ).dinst .one)
      ((W k' (ISub.cons .one trivial ρ)).dinst (r.subst ρ.τ)) := by
    intro k' ρ
    have hcl : (W (k' + 1) ρ.up).closedB 0 (k' + 2) = true :=
      closed_of_isTyK hW (Comp2_ty_base (hw (k' + 1) ρ.up).2.2.1).2.1
    show RT2 S k' (((W (k' + 1) ρ.up).dinst ((r.subst ρ.τ).shift)).dinst .one) _
    rw [dinst_shift_dinst hcl _ .one (hsc k' ρ) trivial, ← isub_up_dinst _ _ _ (hsc k' ρ)]
    exact hcohW (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id]) _ (hsc k' ρ)
  have C'd1 : ∀ k' (ρ : ISub k' k), RT2 S k' ((C' k' ρ).dinst .one)
      ((W' k' (ISub.cons .one trivial ρ)).dinst (r'.subst ρ.τ)) := by
    intro k' ρ
    have hcl : (W' (k' + 1) ρ.up).closedB 0 (k' + 2) = true :=
      closed_of_isTyK hW (Comp2_ty_base (hw (k' + 1) ρ.up).2.2.1).2.2.1
    show RT2 S k' (((W' (k' + 1) ρ.up).dinst ((r'.subst ρ.τ).shift)).dinst .one) _
    rw [dinst_shift_dinst hcl _ .one (hsc' k' ρ) trivial, ← isub_up_dinst _ _ _ (hsc' k' ρ)]
    exact hcohW' (k' + 1) ρ.up k' _ _ (by rw [ISub.up_comp_cons, ISub.comp_id]) _ (hsc' k' ρ)
  -- the judgmental equalities of the types of the points
  have tyB : ∀ {k3 : ℕ} {A B : Tm}, RT2 S k3 A B → TyEq S k3 A B := fun h => (Comp2_ty_base h).2.2.2.2.2
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
  have hX : TyCode k (semK S k (L1.dinst r)) := by have := hX2 k ι1 r hr; rwa [hL1] at this
  have hYY : RT2 S k (L1.dinst r) (L1.dinst r) := by
    have := hWW' k ι1 r r hr hr (I_eq_refl r); rw [hL1] at this; exact RT2.refl hW hX this
  have hpT : HasTy S k .one [] (.transp T φ a0) (.ipi L1) := hty.tyConv hR1.2
  have hE0 : EqTm S k .one [] (.papp (.transp T φ a0) r) (.papp (.transp T' φ' a0') r') (L1.dinst r) :=
    EqTm.iapp (heq.tyConv hR1.2) hr hr' hE
  -- the eliminated bases, where the face holds
  have hfin : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst ρ.τ) →
      RE2 S k' ((L1.dinst r).isub ρ) (.papp (a0.isub ρ) (r.subst ρ.τ)) (.papp (a0'.isub ρ) (r'.subst ρ.τ)) := by
    intro k' ρ hf
    have h0 := RE2.isub hW ha0 ρ
    rw [hT0] at h0
    have hCρ := hC k' ρ .one trivial ((holds_iff_entails (I.scoped_subst hφs ρ.sc)).2 hf)
    have h1 := RE2.conv' hW hCρ h0 (RT2.tyCode_l hW hCρ (RE2.tyCode hW h0))
    exact RE2.conv' hW (Ypt k' ρ) (hP.elim k' _ _ _ _ (hw k' _).1 h1 _ _ (hsc k' ρ) (hsc' k' ρ) (hEρ k' ρ))
      (hXY k' ρ)
  have hA0e : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'),
      (Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ' = .papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ) := by
    intro k' ρ k'' ρ'
    show Tm.papp ((a0.isub ρ).isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = _
    rw [Tm.isub_isub, I_subst_comp]
  have H := kanT2_elim_core hW (fun k' ρ x => .papp x (r.subst ρ.τ)) (fun k' ρ x => .papp x (r'.subst ρ.τ))
    C C' (fun k' ρ => .papp (a0.isub ρ) (r.subst ρ.τ)) (fun k' ρ => .papp (a0'.isub ρ) (r'.subst ρ.τ))
    hX hYY (by simp only [hrid]; exact HasTy.iapp hpT hr) (by simp only [hrid']; exact HasTy.eqR hE0)
    (by simp only [hrid, hrid']; exact hE0)
    (fun k' ρ k'' ρ' x => by
      show Tm.papp (x.isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = Tm.papp (x.isub ρ') (r.subst (ρ.comp ρ').τ)
      rw [I_subst_comp])
    (fun k' ρ k'' ρ' x => by
      show Tm.papp (x.isub ρ') ((r'.subst ρ.τ).subst ρ'.τ) = Tm.papp (x.isub ρ') (r'.subst (ρ.comp ρ').τ)
      rw [I_subst_comp])
    (fun k' ρ => ?_) (fun k' ρ => ?_) hfin
    (fun k' ρ k'' ρ' _ hf2 => by rw [hA0e]; exact hfin k'' _ hf2)
    (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' _ => ?_)
    (fun k' ρ k'' ρ' _ => ?_) h12 h21
  · simpa only [hrid, hrid'] using H
  · -- the reducts on the left
    have hρ := HasTy.isubS hW hty ρ
    rw [isub_dinst] at hρ
    have eF : TyEq S k' ((T.isub ρ.up).dinst .one) (.ipi (L1.isub ρ.up)) := by
      have := hR1.2.isub hW ρ; rw [isub_dinst] at this; exact this
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a, b⟩ := papp_transp_face hW hf (hsc k' ρ) hρ eF
      rw [isub_dinst]; exact ⟨a, b⟩
    · obtain ⟨a, b⟩ := papp_transp_ipi hW hf (hsc k' ρ) hρ (hw (k' + 1) ρ.up).1
      exact ⟨a, b.tyConv (TyEq.trans hW (Comp2_ty_base (Cd1 k' ρ)).2.2.2.2.2
        (TyEq.symm (Comp2_ty_base (Ypt k' ρ)).2.2.2.2.2))⟩
  · -- the reducts on the right
    have hρ := (HasTy.isubS hW hty' ρ).tyConv (TyEq.refl _)
    rw [isub_dinst] at hρ
    have eT : TyEq S k' ((T'.isub ρ.up).dinst .one) ((T.isub ρ.up).dinst .one) := by
      have := ((tyEq_dinst hW hP.tyEq (r := .one) trivial).isub hW ρ)
      rw [isub_dinst, isub_dinst] at this; exact TyEq.symm this
    have hρ' := hρ.tyConv (TyEq.symm eT)
    have eF : TyEq S k' ((T'.isub ρ.up).dinst .one) (.ipi (L1.isub ρ.up)) := by
      have := hR1.2.isub hW ρ; rw [isub_dinst] at this; exact TyEq.trans hW eT this
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a, b⟩ := papp_transp_face hW hf (hsc' k' ρ) hρ' eF
      exact ⟨a, b.tyConv (hTyR k' ρ)⟩
    · obtain ⟨a, b⟩ := papp_transp_ipi hW hf (hsc' k' ρ) hρ' (hw (k' + 1) ρ.up).2.1
      refine ⟨a, b.tyConv ?_⟩
      have c := tyB (C'd1 k' ρ)
      have d := tyB (hWW' k' (ISub.cons .one trivial ρ) _ _ (hsc' k' ρ) (hsc' k' ρ) (I_eq_refl _))
      exact TyEq.trans hW c (TyEq.trans hW (TyEq.symm d) (hWdd k' ρ))
  · -- the eliminated line at its end
    rw [isub_up_dinst _ ρ' .one trivial]
    have c := Cpt k' ρ k'' ρ' .one trivial
    exact RT2.trans hW (RT2.tyCode_l hW c (hX2 _ _ _ (hsc k'' _))) c
      (RT2.symm hW (hXY k'' _) (Ypt k'' (ρ.comp ρ')))
  · -- robustness of the eliminated lines
    intro k3 τ x x' hx hx' hEx
    rw [Tm.isub_isub, ISub.up_comp_cons]
    have c1 := Cpt k' ρ k3 (ρ'.comp τ) x hx
    have c3 := C'pt k'' (ρ.comp ρ') k3 τ x' hx'
    rw [ISub.comp_assoc] at c3
    have m := ipiW_rel hW (hLR k3 (ρ.comp (ρ'.comp τ)) x x' hx hx' hEx) (hw k3 _).1 (hw k3 _).2.1 _ _
      (hsc k3 (ρ.comp (ρ'.comp τ))) (hsc' k3 (ρ.comp (ρ'.comp τ))) (hEρ k3 (ρ.comp (ρ'.comp τ)))
    have t1 := hX2 k3 (ISub.cons x hx (ρ.comp (ρ'.comp τ))) _ (hsc k3 (ρ.comp (ρ'.comp τ)))
    have t3 := RT2.tyCode_r hW m t1
    exact RT2.trans hW (RT2.tyCode_l hW c1 t1) c1
      (RT2.trans hW t1 m (RT2.symm hW (RT2.tyCode_l hW c3 t3) c3))
  · -- constancy of the eliminated lines
    intro k3 τ x hx hh
    rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons]
    have c1 := Cpt k' ρ k3 (ρ'.comp τ) x hx
    have c2 := Cpt k' ρ k3 (ρ'.comp τ) .zero trivial
    have hh' : (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp τ)).τ)).holds := by
      rw [I_subst_comp, I_subst_comp]; exact hh
    have m := ipiW_rel hW (hC k3 _ x hx hh') (hw k3 _).1 (hw k3 _).1 _ _ (hsc k3 (ρ.comp (ρ'.comp τ)))
      (hsc k3 (ρ.comp (ρ'.comp τ))) (I_eq_refl _)
    have t1 := hX2 k3 (ISub.cons x hx (ρ.comp (ρ'.comp τ))) _ (hsc k3 (ρ.comp (ρ'.comp τ)))
    have t2 := RT2.tyCode_r hW m t1
    exact RT2.trans hW (RT2.tyCode_l hW c1 t1) c1
      (RT2.trans hW t1 m (RT2.symm hW (RT2.tyCode_l hW c2 t2) c2))
  · -- the eliminated bases
    rw [isub_up_dinst _ ρ' .zero trivial]
    show RE2 S k'' _ ((Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ') (Tm.papp (a0'.isub (ρ.comp ρ')) (r'.subst (ρ.comp ρ').τ))
    rw [hA0e]
    have h0 := RE2.isub hW ha0 (ρ.comp ρ')
    rw [hT0] at h0
    have el := hP.elim k'' _ _ _ _ (hw k'' _).1 h0 _ _ (hsc k'' (ρ.comp ρ')) (hsc' k'' (ρ.comp ρ'))
      (hEρ k'' (ρ.comp ρ'))
    have c := Cpt k' ρ k'' ρ' .zero trivial
    exact RE2.conv' hW c el (RT2.tyCode_l hW c (hX2 _ _ _ (hsc k'' (ρ.comp ρ'))))
  · -- the induction hypothesis
    refine hIH k' ρ.up (W (k' + 1) ρ.up) (hw _ _).1 _ (KubusCore.I.scoped_shift (hsc k' ρ)) k'' ρ'.up _ ?_
    rw [isub_dinst]
    have e : ((r.subst ρ.τ).shift).subst ρ'.up.τ = (r.subst (ρ.comp ρ').τ).shift := by
      rw [I_subst_comp]; exact I_shift_subst_up _ _
    rw [e]
    have c := hcohW (k' + 1) ρ.up (k'' + 1) ρ'.up _ (ISub.up_comp ρ ρ').symm _ (KubusCore.I.scoped_shift (hsc k'' (ρ.comp ρ')))
    have m := hWW' (k'' + 1) (ρ.comp ρ').up _ _ (KubusCore.I.scoped_shift (hsc k'' (ρ.comp ρ'))) (KubusCore.I.scoped_shift (hsc' k'' (ρ.comp ρ')))
      (ieq_shift (hEρ k'' _))
    exact RT2.trans hW (RT2.tyCode_l hW c (hX2 _ _ _ (KubusCore.I.scoped_shift (hsc k'' (ρ.comp ρ'))))) c m


omit hW in
theorem LineRob.isub {T T' : Tm} (h : LineRob S k T T') (ρ : ISub k' k) : LineRob S k' (T.isub ρ.up) (T'.isub ρ.up) := by
  intro k3 τ x x' hx hx' hE
  rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons]
  exact h k3 (ρ.comp τ) x x' hx hx' hE

omit hW in
theorem LineConst.isub {T : Tm} {φ : I} (h : LineConst S k T φ) (ρ : ISub k' k) :
    LineConst S k' (T.isub ρ.up) (φ.subst ρ.τ) := by
  intro k3 τ x hx hh
  rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons]
  exact h k3 (ρ.comp τ) x hx (by rw [I_subst_comp]; exact hh)

/-- Transport along related lines whose normal forms are interval Π-types. -/
theorem kanT2_ipi {T T' A : Tm} {l : ℕ} (hTT : RT2 S (k + 1) T T') (hR : RedT S (k + 1) T (.ipi A))
    (hipi : HasTy S (k + 1) .one [] (.ipi A) (.univ l))
    (hIH : ∀ k1 (ρ : ISub (k1 + 1) (k + 1)) L, RedT S (k1 + 1) (T.isub ρ) (.ipi L) → ∀ (s : I),
      s.Scoped (k1 + 1) → ∀ k2 (ρ' : ISub (k2 + 1) (k1 + 1)) X', RT2 S (k2 + 1) ((L.dinst s).isub ρ') X' →
      KanT2 S k2 ((L.dinst s).isub ρ') X') : KanT2 S k T T' := by
  have hP := IPiStr_of hW hTT hR hipi
  intro hLR φ φ' a0 a0' hC hty hty' heq h12 h21 ha0
  obtain ⟨l0, ⟨hTl, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hTc : T.closedB 0 (k + 1) = true := closed_ty hTl
  have hT1K : IsTyK S k (T.dinst .one) := isTyK_of_ty hW hty
  obtain ⟨L1, L1', h1, -, -, hd⟩ := hP.whnf k (ISub.cons .one trivial (ISub.id k))
  rw [isub_cons_id_of_closed hTc] at h1
  obtain ⟨l1, hipi1⟩ := ipiW_typed hW hT1K h1
  have hX1 : TyCode k (semK S k (T.dinst .one)) := tyCode_of_ty hW hty
  have hTT1 : RT2 S k (T.dinst .one) (T.dinst .one) := by
    have := hLR k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rw [isub_cons_id_of_closed hTc] at this
    exact RT2.refl hW hX1 this
  refine RE2_ipiW_intro hW hTT1 h1 hipi1 ⟨hty, hty', heq⟩ fun k' ρ L h r r' hr hr' hE => ?_
  have hd1 : ∀ (X : Tm) (x : I), (X.dinst x).isub ρ = (X.isub ρ.up).dinst (x.subst ρ.τ) := fun X x => isub_dinst X x ρ
  rw [hd1] at h
  have htyρ := HasTy.isubS hW hty ρ
  have htyρ' := HasTy.isubS hW hty' ρ
  have heqρ := EqTm.isubS hW heq ρ
  have ha0ρ := RE2.isub hW ha0 ρ
  rw [hd1] at htyρ htyρ' heqρ ha0ρ
  refine kanT2_ipi_core hW (hP.isub hW ρ.up) (hLR.isub ρ) (fun k1 ρ1 L3 h3 s hs k2 ρ2 X' hX' => ?_) (hC.isub ρ)
    htyρ htyρ' heqρ (ent_subst h12 ρ.τ) (ent_subst h21 ρ.τ) ha0ρ h hr hr' hE
  rw [Tm.isub_isub] at h3
  exact hIH k1 (ρ.up.comp ρ1) L3 h3 s hs k2 ρ2 X' hX'

end

end Model.Whnf
