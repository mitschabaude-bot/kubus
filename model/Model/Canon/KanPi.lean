import Model.Canon.KanBasic

/-!
# Canonicity: the Kan operations at Π-types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem hcompPi_body_inst (B u u0 a : Tm) (φ : I) :
    (Tm.hcomp B φ (.app u.shift (.var 0)) (.app u0.shift (.var 0))).inst a =
      .hcomp (B.inst a) φ (.app u a.dshift) (.app u0 a) := by
  simp only [Tm.inst, Tm.subst, I_subst_var, I_up_var, shift_subst]
  congr 2
  · exact subst_id_of (fun n => rfl) (fun i => rfl) u
  · exact subst_id_of (fun n => rfl) (fun i => rfl) u0

theorem isub_hcompPi (A B u u0 : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.hcompPi A B φ u u0).isub σ =
      Tm.hcompPi (A.isub σ) (B.isub σ) (φ.subst σ.τ) (u.isub σ.up) (u0.isub σ) := by
  show (Tm.hcompPi A B φ u u0).subst .var σ.τ = _
  rw [hcompPi_subst, up_var]; rfl

theorem I_subst_comp (φ : I) (σ : ISub k' k) {k'' : ℕ} (σ' : ISub k'' k') :
    φ.subst (σ.comp σ').τ = (φ.subst σ.τ).subst σ'.τ := (I_subst_subst _ _ _).symm

theorem dshift_isub_up_dinst (a : Tm) (σ : ISub k' k) (r : I) : (a.dshift.isub σ.up).dinst r = a.isub σ := by
  rw [isub_dshift, dshift_dinst]


theorem transpPi_body_inst (B w w0 u0 v : Tm) (φ : I) :
    (Tm.transp (B.subst (consT w wkS) I.var) φ (.app u0.shift w0)).inst v =
      .transp (B.inst (w.inst v.dshift)) φ (.app u0 (w0.inst v)) := by
  simp only [Tm.inst, Tm.subst, I_subst_var, I_up_var, shift_subst, subst_subst]
  congr 1
  · refine subst_congr (fun n => ?_) (fun i => ?_) B
    · rcases n with _ | n
      · simp only [consT]; exact subst_congr (fun n => by rcases n with _ | n <;> rfl) (fun i => rfl) w
      · rfl
    · rfl
  · congr 1
    exact subst_id_of (fun n => rfl) (fun i => rfl) u0

theorem wT_inst (A v : Tm) (φ : I) :
    (wT A φ).inst v.dshift = .transp (A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0)) v.dshift := by
  simp only [wT, Tm.inst, Tm.subst, I_subst_var, I_up_var, Tm.dsubst, shift_subst, subst_subst]
  rfl

theorem w0T_inst (A v : Tm) (φ : I) : (w0T A φ).inst v = .transp (A.dsubst negI) φ v := by
  simp only [w0T, Tm.inst, Tm.subst, I_subst_var, I_up_var, Tm.dsubst, shift_subst, subst_subst]
  rfl

theorem dinst_inst (B w : Tm) (r : I) : (B.inst w).dinst r = (B.dinst r).inst (w.dinst r) := by
  simp only [Tm.inst, Tm.dinst, Tm.dsubst, subst_subst]
  refine subst_congr (fun n => ?_) (fun i => ?_) B
  · rcases n with _ | n <;> rfl
  · simp [I.subst, I_subst_var]

variable (hW : WfSig S)
include hW

theorem kanH_pi {A B : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A B) (.univ l))
    (hB : ∀ k' (σ : ISub k' k) a, RE S k' (A.isub σ) a → KanH S k' ((B.isub σ).inst a)) :
    KanH S k (.pi A B) := by
  intro φ u u0 hty hu hu0
  have e := EqTm.hcompPi hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  refine RE_pi_intro hW hpi (HasTy.eqR e) fun k' σ a ha => ?_
  rw [isub_hcompPi]
  have hf := HasTy.isubS hW (HasTy.eqR e) σ
  rw [isub_hcompPi, isub_pi] at hf
  have hβ := EqTm.piBeta (HasTy.app hf (Comp_el_typed ha).1)
  simp only [Tm.hcompPi] at hβ ⊢
  rw [hcompPi_body_inst] at hβ
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm hβ)
  refine hB k' σ a ha _ _ _ (HasTy.eqR hβ) (fun k'' σ' r hr hh => ?_) ?_
  · have h1 := hu k'' (σ.comp σ') r hr (by rw [I_subst_comp]; exact hh)
    rw [isub_pi] at h1
    have h2 := RE_pi_elim hW h1 (by have := ha.isub hW σ'; rwa [Tm.isub_isub] at this)
    rw [isub_inst, Tm.isub_isub, isub_app]
    simp only [Tm.dinst, Tm.dsubst] at h2 ⊢
    show RE S k'' _ (Tm.app ((u.isub σ.up).isub σ'.up |>.dinst r) ((a.dshift.isub σ'.up).dinst r))
    rw [dshift_isub_up_dinst, Tm.isub_isub, ← ISub.up_comp]
    exact h2
  · have h1 := hu0.isub hW σ
    rw [isub_pi] at h1
    exact RE_pi_elim hW h1 ha

omit hW in
theorem shift_dd_inst (X v : Tm) (τ : ℕ → I) (r : I) : ((X.shift.dsubst τ).dinst r).inst v = (X.dsubst τ).dinst r := by
  simp only [Tm.inst, Tm.dinst, Tm.dsubst, shift_subst, subst_subst]
  exact subst_congr (fun n => rfl) (fun i => I_subst_var _) X

omit hW in
theorem pi_dinst (A B : Tm) (r : I) : (Tm.pi A B).dinst r = .pi (A.dinst r) (B.dinst r) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, up_var]

/-- The core of transport in Π-types, at a computable argument. -/
theorem transpPi_core {A B u0 v : Tm} {φ : I}
    (hA : ∀ k' (σ : ISub (k' + 1) (k + 1)), KanT S k' (A.isub σ))
    (hB : ∀ k' (σ : ISub (k' + 1) (k + 1)) w, RE S (k' + 1) (A.isub σ) w → KanT S k' ((B.isub σ).inst w))
    (hty : HasTy S k .one [] (.transp (.pi A B) φ u0) ((Tm.pi A B).dinst .one))
    (hu0 : RE S k (.pi (A.dinst .zero) (B.dinst .zero)) u0) (hv : RE S k (A.dinst .one) v) :
    RE S k ((B.dinst .one).inst v) (.app (Tm.transpPi A B φ u0) v) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hL, hφ, hc, -⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) h0 rfl
  have hA0 := HasTy0.piDom hS hL
  have hAc : A.closedB 0 (k + 1) = true := closed_ty hA0
  have hBc : B.closedB 1 (k + 1) = true := closed_ty (HasTy0.piCod hS hL)
  have hcD := EqTm0.piInjDom (A' := (A.dinst .zero).dshift) hc
  have hw := wT_typed hS hA0 hφ hcD
  obtain ⟨hw0, -, -⟩ := w0T_typed hS hA0 hφ hcD
  have hvt := (Comp_el_typed hv).1
  have hvt0 := spec_to_minimal hW hvt
  have hL0 := HasTy0.dsubst hS (Φ := .one) (Γ := []) hL (r := .zero) trivial
  have hL1 := HasTy0.dsubst hS (Φ := .one) (Γ := []) hL (r := .one) trivial
  rw [pi_dinst] at hL0 hL1
  have hB0' := HasTy0.piCod hS hL0
  have hB1' := HasTy0.piCod hS hL1
  -- step (a): `w0 = transp (j. A(~j)) φ v : A(0)`
  have hw0v := HasTy0.subst hS hw0 hvt0
  rw [w0T_inst, shift_dd_inst] at hw0v
  have hsc0 : ∀ i < k + 1, (negI i).Scoped (k + 1) := fun i hi => by
    rcases i with _ | i
    · show 0 < k + 1; omega
    · show i + 1 < k + 1; omega
  have KT0 := hA k (ISub.ofFun (k + 1) negI hsc0)
  rw [isub_ofFun hAc] at KT0
  have eA1 : EqTm S k .one [] (A.dinst .one) ((A.dsubst negI).dinst .zero) (.univ l0) := by
    have := ieq0 hW (k := k) hA0 (τ1 := I.inst0 .one) (τ2 := fun i => (negI i).subst (I.inst0 .zero))
      (fun i hi => by rcases i with _ | i <;> simp [I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i <;> simp [negI, I.subst, I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; rfl
                      · intro ρ; rfl)
    simpa [Tm.dinst, Tm.dsubst, subst_subst] using this
  have eA0 : EqTm S k .one [] ((A.dsubst negI).dinst .one) (A.dinst .zero) (.univ l0) := by
    have := ieq0 hW (k := k) hA0 (τ1 := fun i => (negI i).subst (I.inst0 .one)) (τ2 := I.inst0 .zero)
      (fun i hi => by rcases i with _ | i <;> simp [negI, I.subst, I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i <;> simp [I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; rfl
                      · intro ρ; rfl)
    simpa [Tm.dinst, Tm.dsubst, subst_subst] using this
  have hw0RE : RE S k (A.dinst .zero) (.transp (A.dsubst negI) φ v) :=
    by
      have h1 : HasTy S k .one [] (.transp (A.subst .var negI) φ v) ((A.subst .var negI).dinst .one) :=
        minimal_to_spec hw0v
      have h2 := KT0 φ v h1 (hv.conv_ty hW (.inr ⟨l0, eA1⟩))
      exact h2.conv_ty hW (.inr ⟨l0, eA0⟩)
  -- step (b): `w = transp (j. A(i ∨ ~j)) (φ ∨ i) v : A`, at stage `k + 1`
  have hvd := HasTy0.dwk hS hvt0
  have hwv := HasTy0.subst hS hw hvd
  rw [wT_inst, shift_inst] at hwv
  have hsc1 : ∀ i < k + 1, (Tm.bind2 (.or (.var 1) (.neg (.var 0))) i).Scoped (k + 1 + 1) := fun i hi => by
    rcases i with _ | i
    · exact ⟨show 1 < k + 1 + 1 by omega, show 0 < k + 1 + 1 by omega⟩
    · show i + 2 < k + 1 + 1; omega
  have KT1 := hA (k + 1) (ISub.ofFun (k + 1) _ hsc1)
  rw [isub_ofFun hAc] at KT1
  have eB1 : EqTm S (k + 1) .one [] (A.dinst .one).dshift
      ((A.subst .var (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).dinst .zero) (.univ l0) := by
    have := ieq0 hW (k := k + 1) hA0 (τ1 := fun i => (I.inst0 .one i).shift)
      (τ2 := fun i => (Tm.bind2 (.or (.var 1) (.neg (.var 0))) i).subst (I.inst0 .zero))
      (fun i hi => I.scoped_shift (by rcases i with _ | i <;> simp [I.inst0, I.Scoped] <;> omega))
      (fun i hi => by rcases i with _ | i <;> simp [Tm.bind2, I.subst, I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; simp [I.eval, I.inst0, I.shift, I.ren, Tm.bind2, I.subst]
                      · intro ρ; rfl)
    simpa [Tm.dinst, Tm.dsubst, subst_subst, dshift_eq] using this
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
  have hwRE : RE S (k + 1) A (.transp (A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
      v.dshift) := by
    have h1 : HasTy S (k + 1) .one [] (.transp (A.subst .var (Tm.bind2 (.or (.var 1) (.neg (.var 0)))))
        (.or φ.shift (.var 0)) v.dshift) ((A.subst .var (Tm.bind2 (.or (.var 1) (.neg (.var 0))))).dinst .one) :=
      HasTy.conv (minimal_to_spec hwv) (EqTm.symm eB2)
    exact (KT1 _ _ h1 ((RE.dshift hW hv).conv_ty hW (.inr ⟨l0, eB1⟩))).conv_ty hW (.inr ⟨l0, eB2⟩)
  -- step (c): the line `B[w]`
  have KTB := hB k (ISub.id (k + 1)) _ (by rw [isub_id_of_closed hAc]; exact hwRE)
  rw [isub_id_of_closed hBc] at KTB
  -- step (d): β
  have htp := minimal_to_spec (transpPi_typed hS h0)
  rw [pi_dinst] at htp
  have happ := HasTy.app htp hvt
  try rw [transpPi_eq] at happ
  try rw [transpPi_eq]
  have hβ := EqTm.piBeta happ
  rw [transpPi_body_inst, wT_inst, w0T_inst] at hβ
  -- step (e): the endpoints of `B[w]`
  have hwv1 := minimal_to_spec (HasTy0.dsubst hS (Γ := []) (Φ := .one) hwv (r := .one) trivial)
  have ew1 : EqTm S k .one [] ((Tm.transp (A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
        v.dshift).dinst .one) v (A.dinst .one) := by
    have := EqTm.transpFace (ent_or_right _ _) hwv1
    convert this using 1
    exact (dshift_dinst v .one).symm
  have eF : EqTm S k .one [] ((B.dinst .one).inst v)
      ((B.inst (.transp (A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
        v.dshift)).dinst .one) (.univ l0) := by
    rw [dinst_inst]
    exact EqTm.subst (EqTm.refl (minimal_to_spec hB1')) (EqTm.symm ew1)
  have hwv0 := minimal_to_spec (HasTy0.dsubst hS (Γ := []) (Φ := .one) hwv (r := .zero) trivial)
  have eL : EqTm S (k + 1) .one [] (A.subst .var negI)
      (A.subst .var (fun i => (Tm.bind2 (.or (.var 1) (.neg (.var 0))) i).subst (I.up (I.inst0 .zero)))) (.univ l0) := by
    have := ieq0 hW (k := k + 1) hA0 (τ1 := negI)
      (τ2 := fun i => (Tm.bind2 (.or (.var 1) (.neg (.var 0))) i).subst (I.up (I.inst0 .zero)))
      (fun i hi => by rcases i with _ | i <;> simp [negI, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i <;> simp [Tm.bind2, I.subst, I.up, I.inst0, I.Scoped, I.shift, I.ren] <;> omega)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; simp [I.eval, negI, I.inst0, Tm.bind2, I.subst, I.up, I.shift, I.ren]
                      · intro ρ; simp [negI, I.inst0, Tm.bind2, I.subst, I.up, I.shift, I.ren])
    simpa using this
  have hφs : (φ.shift.subst (I.inst0 .zero)) = φ := by
    simp only [I.shift, I_ren_subst]; exact I_subst_var φ
  have ew0 : EqTm S k .one [] (.transp (A.dsubst negI) φ v)
      ((Tm.transp (A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0)) v.dshift).dinst .zero)
      ((A.dsubst negI).dinst .one) := by
    have h2 : HasTy S k .one [] ((Tm.transp (A.dsubst (Tm.bind2 (.or (.var 1) (.neg (.var 0))))) (.or φ.shift (.var 0))
        v.dshift).dinst .zero) ((A.dsubst negI).dinst .one) := HasTy.conv hwv0 (EqTm.symm eA0)
    have eL2 : EqTm S (k + 1) I.one.shift (Ctx.dshift []) (Tm.dsubst negI A)
        (Tm.subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .zero))
          (Tm.dsubst (Tm.bind2 ((I.var 1).or (I.var 0).neg)) A)) (Tm.univ l0) := by
      have eqT : (Tm.dsubst (Tm.bind2 ((I.var 1).or (I.var 0).neg)) A).subst (fun n => (Tm.var n).dshift)
          (I.up (I.inst0 .zero)) = A.subst .var (fun i => (Tm.bind2 (.or (.var 1) (.neg (.var 0))) i).subst
            (I.up (I.inst0 .zero))) := by
        unfold Tm.dsubst; rw [subst_subst]; rfl
      rw [eqT]; exact eL
    refine EqTm.transp (minimal_to_spec hw0v) h2 eL2 ?_ ?_ ?_
    · show I.Entails φ (.or (φ.shift.subst (I.inst0 .zero)) .zero); rw [hφs]; exact ent_or_left _ _
    · show I.Entails (.or (φ.shift.subst (I.inst0 .zero)) .zero) φ; rw [hφs]; exact ent_or_elim (ent_refl _) (ent_zero _)
    · show EqTm S k .one [] v (v.dshift.dinst .zero) _
      rw [dshift_dinst]; exact EqTm.refl (HasTy.conv hvt eA1)
  have hin := (RE_pi_elim hW hu0 hw0RE).conv_ty hW
    (.inr ⟨l0, EqTm.subst (EqTm.refl (minimal_to_spec hB0')) (EqTm.conv ew0 eA0)⟩)
  rw [← dinst_inst] at hin
  have htyB := HasTy.conv (HasTy.eqR hβ) eF
  exact (KTB φ _ htyB hin).conv hW (.inr ⟨l0, EqTm.symm eF⟩) (EqTm.symm hβ)

omit hW in
theorem isub_transpPi (A B u0 : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.transpPi A B φ u0).isub σ = Tm.transpPi (A.isub σ.up) (B.isub σ.up) (φ.subst σ.τ) (u0.isub σ) := by
  show (Tm.transpPi A B φ u0).subst .var σ.τ = _
  rw [transpPi_subst, show dupS Tm.var = Tm.var from funext fun n => rfl, up_var]; rfl

omit hW in
theorem isub_transp (A a : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.transp A φ a).isub σ = .transp (A.isub σ.up) (φ.subst σ.τ) (a.isub σ) := rfl

theorem kanT_pi {A B : Tm} {l : ℕ} (hpi : HasTy S (k + 1) .one [] (.pi A B) (.univ l))
    (hA : ∀ k' (σ : ISub (k' + 1) (k + 1)), KanT S k' (A.isub σ))
    (hB : ∀ k' (σ : ISub (k' + 1) (k + 1)) w, RE S (k' + 1) (A.isub σ) w → KanT S k' ((B.isub σ).inst w)) :
    KanT S k (.pi A B) := by
  have hS := sigClosed_of_wfSig hW
  intro φ u0 hty hu0
  have e := EqTm.transpPi hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  have htpi := HasTy.eqR e
  rw [pi_dinst] at htpi hu0 ⊢
  have hpi1 := HasTy0.dsubst hS (Φ := .one) (Γ := []) (spec_to_minimal hW hpi) (r := .one) trivial
  rw [pi_dinst] at hpi1
  refine RE_pi_intro hW (minimal_to_spec hpi1) htpi fun k' σ v hv => ?_
  rw [isub_transpPi, isub_dinst]
  rw [isub_dinst] at hv
  have hty' := HasTy.isubS hW hty σ
  rw [isub_transp, isub_dinst, isub_pi] at hty'
  have hu0' := hu0.isub hW σ
  rw [isub_pi, isub_dinst, isub_dinst] at hu0'
  exact transpPi_core hW (fun k'' σ'' => by rw [Tm.isub_isub]; exact hA k'' (σ.up.comp σ''))
    (fun k'' σ'' w hw => by
      rw [Tm.isub_isub] at hw ⊢; exact hB k'' (σ.up.comp σ'') w hw) hty' hu0' hv

end

end Model.Canon
