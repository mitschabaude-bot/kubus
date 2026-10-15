import Model.Whnf.Kan2Univ

/-!
# Heterogeneous fillers of binary compositions

The relation of the fillers `fill C ψ u u0` of related heterogeneous compositions along related
lines, at pointwise equal restrictions (`fill_rel`), and the end of a filler against its
composition (`fill_one_pt`). These are the heterogeneous analogues of `hfill_rel` (`Kan2Fill.lean`)
and `hfill_one_pt` (`Kan2Comp.lean`), with `comp2` in place of the composition at the type.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem isub_bindAnd_cons (X : Tm) {k3 : ℕ} (ρ : ISub k3 (k' + 1)) (r : I) (hr : r.Scoped k3) :
    (X.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons r hr ρ) =
      X.isub (ISub.cons (.and (ρ.τ 0) r) ⟨ρ.sc 0 (by omega), hr⟩ ρ.tail) := by
  simp only [Tm.isub, Tm.dsubst, subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl

theorem isub_bindAnd_gen (X : Tm) {k3 : ℕ} (ρ : ISub k3 (k' + 1 + 1)) :
    (X.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub ρ =
      X.isub (ISub.cons (.and (ρ.τ 1) (ρ.τ 0)) ⟨ρ.sc 1 (by omega), ρ.sc 0 (by omega)⟩ ρ.tail.tail) := by
  simp only [Tm.isub, Tm.dsubst, subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl

/-- The parts of a typed heterogeneous composition. -/
theorem comp_parts (hS : SigClosed S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {C u u0 X : Tm} {ψ : I}
    (hc : HasTy0 S Ψ Φ Γ (Tm.comp C ψ u u0) X) :
    ∃ l, HasTy0 S (Ψ + 1) Φ.shift Γ.dshift C (.univ l) ∧ ψ.Scoped Ψ ∧
      HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C ∧ HasTy0 S Ψ Φ Γ u0 (C.dinst .zero) := by
  rw [comp_eq] at hc
  obtain ⟨_, ⟨_, hψs, htube, hb, _⟩, _⟩ := gen_hcomp hc rfl
  obtain ⟨lC, ⟨hC, _, _, hu0⟩, _⟩ := gen_transpF hb rfl
  obtain ⟨_, ⟨_, _, _, hu⟩, _⟩ := gen_transpF htube rfl
  have hs := scoped_of_ty hc
  have hw0 := wf_of_ty hc
  have hXs : (cof Φ ψ).shift.Scoped (Ψ + 1) := KubusCore.Meta.scoped_shift ⟨hs, hψs⟩
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left Φ ψ)
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hwX : Wf0 S (Ψ + 1) (cof Φ ψ).shift (ctxI (fun n => .var (n + 1)) Γ) := by
    rw [ctxI_add1]; exact (Wf0.dwk hS hw0).restrict hXs hXΦ
  have eL0 : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift C
      ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .zero) (.univ lC) := by
    rw [L_d0]
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .var 0) (r' := .or (.var 0) .zero) hXΦ hv0
      ⟨hv0, trivial⟩ (by omega) (I_eq_symm (I_eq_or_zero_r _)) hwX
    rwa [ctxI_add1, sk_var1] at e
  exact ⟨lC, hC, hψs, HasTy0.conv hu (EqTm0.symm eL0), hu0⟩

/-- The parts of a typed heterogeneous filler. -/
theorem fill_parts2 (hS : SigClosed S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {C u u0 X : Tm} {ψ : I}
    (hF : HasTy0 S (Ψ + 1) Φ Γ (Tm.fill C ψ u u0) X) :
    ∃ l, HasTy0 S (Ψ + 1 + 1) Φ.shift Γ.dshift (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.univ l) ∧
      (I.or ψ.shift (.neg (.var 0))).Scoped (Ψ + 1) ∧
      HasTy0 S (Ψ + 1 + 1) (cof Φ (.or ψ.shift (.neg (.var 0)))).shift Γ.dshift (KubusCore.Meta.fillTube ψ u u0)
        (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) ∧
      HasTy0 S (Ψ + 1) Φ Γ u0.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) :=
  comp_parts hS (C := C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (ψ := .or ψ.shift (.neg (.var 0)))
    (u := KubusCore.Meta.fillTube ψ u u0) (u0 := u0.dshift) hF

/-- The tube of the end of a heterogeneous filler is judgmentally the tube of its composition. -/
theorem fill1_tubeH_eq (hS : SigClosed S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {C u u0 X Y : Tm} {ψ : I}
    (hF : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (Tm.fill C ψ u u0) X) (hc : HasTy0 S Ψ Φ Γ (Tm.comp C ψ u u0) Y) :
    EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u
      ((KubusCore.Meta.fillTube ψ u u0).subst Tm.var (I.up (I.inst0 .one))) C := by
  obtain ⟨lC, hC, hψ, hu, -⟩ := comp_parts hS hc
  obtain ⟨-, -, -, hT, -⟩ := fill_parts2 hS hF
  have hs := scoped_of_ty hc
  have hw0 := wf_of_ty hc
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hX : (cof Φ (.or ψ (.neg .one))).Scoped Ψ := ⟨hs, ⟨hψ, trivial⟩⟩
  have hXe : I.Entails (cof Φ (.or ψ (.neg .one))).shift (cof Φ ψ).shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_neg_one ψ))
  have hXs : (cof Φ (.or ψ (.neg .one))).shift.Scoped (Ψ + 1) := KubusCore.Meta.scoped_shift hX
  have htyped := HasTy0.isub hS (τ := I.up (I.inst0 .one)) (Φ' := (cof Φ (.or ψ (.neg .one))).shift)
    hT (Iup_scoped (fun i hi => by
      rcases i with _ | i
      · trivial
      · exact show i < Ψ by omega))
    (by rw [fillR_up1]; exact ent_refl _)
    (by rw [ctxI_up_inst0]; exact (Wf0.dwk hS hw0).restrict hXs (ent_shift (ent_and_left _ _)))
  rw [ctxI_up_inst0, fillTube_up1', Cfill_up1] at htyped
  rw [fillTube_up1']
  have e1 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_neg_one ψ))) htyped
  have e2 := HasTy0.ieq hS (Φ' := (cof Φ (.or ψ (.neg .one))).shift) (τ1 := sk (.and .one (.var 0)) 1)
    (τ2 := sk (.var 0) 1) hu (sk_scoped ⟨trivial, hv0⟩ (by omega)) (sk_scoped hv0 (by omega))
    (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
      (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
    (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
      (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
    (ieq_sk (I_eq_and_one_l _) 1) (by rw [ctxI_sk1, ctxI_sk1])
    (by rw [ctxI_sk1]; exact (wf_of_ty hu).restrict hXs hXe)
  rw [ctxI_sk1, sk_var1] at e2
  have hY : (cof Φ ψ).shift.Scoped (Ψ + 1) := KubusCore.Meta.scoped_shift ⟨hs, hψ⟩
  have hYe : I.Entails (cof Φ ψ).shift (cof Φ (.or ψ (.neg .one))).shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_or_left _ _))
  have eC := HasTy0.sk1_ieq hS hC (r := .and .one (.var 0)) (r' := .var 0) ⟨trivial, hv0⟩ hv0
    (I_eq_and_one_l _) hY (ent_shift (ent_and_left _ _))
  rw [sk_var1] at eC
  exact EqTm0.symm (EqTm0.conv (EqTm0.restrict hY hYe (EqTm0.trans e1 e2)) eC)

/-- Converting the type of a judgmental equality of tubes along an equality of lines. -/
theorem EqTm.cofConvL {u u' A B : Tm} {φ : I} (hφ : φ.Scoped k)
    (h : EqTm S (k + 1) (cof .one φ).shift [] u u' A) (e : TyEq S (k + 1) A B) :
    EqTm S (k + 1) (cof .one φ).shift [] u u' B := by
  rcases e with rfl | ⟨l, e⟩
  · exact h
  · exact EqTm.conv h (EqTm.toCof hφ e)

theorem lineRob_bindAnd {C C' : Tm} (h : LineRob S k C C') {k3 : ℕ} (σ σ' : ISub k3 (k + 1))
    (et : σ.tail = σ'.tail) (e0 : I.Eq (σ.τ 0) (σ'.τ 0)) :
    LineRob S k3 ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up)
      ((C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ'.up) := by
  intro k4 τ r r' hr hr' hE
  rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons, isub_bindAnd_cons, isub_bindAnd_cons,
    ISub.comp_tail, ISub.comp_tail, ← et]
  exact h k4 (σ.tail.comp τ) _ _ _ _ (ieq_and_congr (I_eq_subst e0 τ.τ) hE)

/-- The tubes of related heterogeneous fillers are judgmentally equal. -/
theorem fillTubeH_eq (hS : SigClosed S) {C C' u u' u0 u0' X X' : Tm} {ψ ψ' : I}
    (hF : HasTy0 S (k + 1) .one [] (Tm.fill C ψ u u0) X) (hF' : HasTy0 S (k + 1) .one [] (Tm.fill C' ψ' u' u0') X')
    (hC : IsTypB S (k + 1) .one [] C)
    (hDD : C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))) = C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0))) ∨
      ∃ l, EqTm0 S (k + 1 + 1) .one [] (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
        (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.univ l))
    (huu : EqTm0 S (k + 1) (cof .one ψ).shift [] u u' C) (hu0 : EqTm0 S k .one [] u0 u0' (C.dinst .zero))
    (h12 : I.Entails ψ ψ') :
    EqTm0 S (k + 1 + 1) (cof .one (.or ψ.shift (.neg (.var 0)))).shift [] (KubusCore.Meta.fillTube ψ u u0)
      (KubusCore.Meta.fillTube ψ' u' u0') (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) := by
  obtain ⟨-, -, hχ, hsL, -⟩ := fill_parts2 hS hF
  obtain ⟨-, -, -, hsR, -⟩ := fill_parts2 hS hF'
  have hCs : (cof I.one (.or ψ.shift (.neg (.var 0)))).shift.Scoped (k + 1 + 1) :=
    KubusCore.Meta.scoped_shift ⟨trivial, hχ⟩
  have hφ2 : ψ.shift.shift.Scoped (k + 1 + 1) := KubusCore.Meta.scoped_shift hχ.1
  have hv1 : (I.var 1).Scoped (k + 1 + 1) := show 1 < k + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (k + 1 + 1) := show 0 < k + 1 + 1 by omega
  have hCC : I.Entails (cof I.one (.or ψ.shift (.neg (.var 0)))).shift
      (cof I.one (.or ψ'.shift (.neg (.var 0)))).shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _))
      (ent_or_right _ _)))
  have hsR' : HasTy0 S (k + 1 + 1) (cof I.one (.or ψ.shift (.neg (.var 0)))).shift []
      (KubusCore.Meta.fillTube ψ' u' u0') (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) := by
    rcases hDD with e | ⟨l, e⟩
    · rw [e]; exact HasTy0.restrict hCs hCC hsR
    · exact HasTy0.conv (HasTy0.restrict hCs hCC hsR) (EqTm0.symm (EqTm0.restrict hCs (ent_one _) e))
  refine EqTm0.local (φ := ψ.shift.shift) (ψ := .neg (.var 1)) hφ2 hv1 (ent_trans (ent_and_right _ _) (ent_refl _))
    hsL hsR' ?_ ?_
  · have hc : (cof (cof I.one (.or ψ.shift (.neg (.var 0)))).shift ψ.shift.shift).Scoped (k + 1 + 1) := ⟨hCs, hφ2⟩
    have s1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have s2 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_shift h12)))
      (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m : EqTm0 S (k + 1 + 1) (cof (cof I.one (.or ψ.shift (.neg (.var 0)))).shift ψ.shift.shift) [] _ _ _ :=
      EqTm0.isub hS huu (τ := Tm.bind2 (.and (.var 1) (.var 0)))
        (fun i hi => by
          rcases i with _ | i
          · exact ⟨show 1 < k + 1 + 1 by omega, show 0 < k + 1 + 1 by omega⟩
          · show i + 2 < k + 1 + 1; omega)
        (ent_bind2_shift _ (ent_and_intro (ent_one _) (ent_and_right _ _))) (Wf0.nil hc)
    exact EqTm0.trans s1 (EqTm0.trans m (EqTm0.symm s2))
  · have hc : (cof (cof I.one (.or ψ.shift (.neg (.var 0)))).shift (.neg (.var 1))).Scoped (k + 1 + 1) := ⟨hCs, hv1⟩
    have t1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsL)
    have t2 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hc (ent_and_left _ _) hsR')
    have m := EqTm0.restrict hc (ent_one _) (EqTm0.dwk hS (EqTm0.dwk hS hu0))
    have m' : EqTm0 S (k + 1 + 1) (cof (cof I.one (.or ψ.shift (.neg (.var 0)))).shift (.neg (.var 1))) []
        u0.dshift.dshift u0'.dshift.dshift (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) := by
      rcases hC with ⟨l, hCt⟩ | ⟨l, rfl, -⟩
      · have hDl : HasTy0 S (k + 1 + 1) (cof (cof I.one (.or ψ.shift (.neg (.var 0)))).shift (.neg (.var 1))) []
            (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.univ l) :=
          HasTy0.isub hS (τ := Tm.bind2 (.and (.var 1) (.var 0))) hCt
            (fun i hi => by
              rcases i with _ | i
              · exact ⟨show 1 < k + 1 + 1 by omega, show 0 < k + 1 + 1 by omega⟩
              · show i + 2 < k + 1 + 1; omega)
            (ent_one _) (Wf0.nil hc)
        have e1 := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _) hDl
        rw [tf_L1] at e1
        have e2 := HasTy0.sk2_ieq hS (Ξ := .one) (Γ := []) hCt (r := .and .zero (.var 0)) (r' := .zero)
          ⟨trivial, hv0'⟩ trivial (I_eq_and_zero _) hc (ent_one _)
        rw [sk_zero2] at e2
        exact EqTm0.conv m (EqTm0.symm (EqTm0.trans e1 e2))
      · exact m
    exact EqTm0.trans t1 (EqTm0.trans m' (EqTm0.symm t2))

variable (hW : WfSig S)
include hW

/-- The heterogeneous fillers of related compositions along related lines are related, at
pointwise equal restrictions. -/
theorem fill_rel {C C' u u' u0 u0' : Tm} {ψ ψ' : I} (hψs : ψ.Scoped k)
    (hLR : LineRob S k C C') (hLRL : LineRob S k C C)
    (hKT : ∀ k3 (Θ : ISub (k3 + 1) (k + 1)) X', RT2 S (k3 + 1) (C.isub Θ) X' → KanT2 S k3 (C.isub Θ) X')
    (hKH : ∀ k3 (Θ : ISub k3 (k + 1)) X', RT2 S k3 (C.isub Θ) X' → KanH2 S k3 (C.isub Θ) X')
    (htyF : HasTy S (k + 1) .one [] (Tm.fill C ψ u u0) C)
    (htyF' : HasTy S (k + 1) .one [] (Tm.fill C' ψ' u' u0') C)
    (heqF : EqTm S (k + 1) .one [] (Tm.fill C ψ u u0) (Tm.fill C' ψ' u' u0') C)
    (hteq : EqTm S (k + 1) (cof .one ψ).shift [] u u' C)
    (h12 : I.Entails ψ ψ') (h21 : I.Entails ψ' ψ)
    (htube : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r'))
    (hu0 : RE2 S k (C.dinst .zero) u0 u0')
    (hbd : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) ((u.isub σ.up).dinst .zero) (u0'.isub σ))
    (hbd' : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) (u0.isub σ) ((u'.isub σ.up).dinst .zero))
    {k3 : ℕ} (σ σ' : ISub k3 (k + 1)) (et : σ.tail = σ'.tail) (e0 : I.Eq (σ.τ 0) (σ'.τ 0)) :
    RE2 S k3 (C.isub σ) ((Tm.fill C ψ u u0).isub σ) ((Tm.fill C' ψ' u' u0').isub σ') := by
  have hS := sigClosed_of_wfSig hW
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hFm := spec_to_minimal hW htyF
  have hFm' := spec_to_minimal hW htyF'
  obtain ⟨lD, hDt, hχs, -, -⟩ := fill_parts2 hS (Ψ := k) (Φ := .one) (Γ := []) hFm
  obtain ⟨lD', hDt', hχs', hTt', -⟩ := fill_parts2 hS (Ψ := k) (Φ := .one) (Γ := []) hFm'
  have hψs' : ψ'.Scoped k := scoped_unshift hχs'.1
  have hDc := closed_of_ty hW (minimal_to_spec hDt)
  have hDc' := closed_of_ty hW (minimal_to_spec hDt')
  -- the lines
  have hCC' : ∀ k4 (ρ : ISub k4 (k + 1)), RT2 S k4 (C.isub ρ) (C'.isub ρ) := by
    intro k4 ρ
    have := hLR k4 ρ.tail (ρ.τ 0) (ρ.τ 0) (ρ.sc 0 (by omega)) (ρ.sc 0 (by omega)) (I_eq_refl _)
    rwa [ISub.cons_tail] at this
  have hTD : TyEq S (k + 1 + 1) (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) := by
    have h := tyB (hCC' (k + 1 + 1) (ISub.cons (.and ((ISub.id (k + 1 + 1)).τ 1) ((ISub.id (k + 1 + 1)).τ 0))
      ⟨(ISub.id (k + 1 + 1)).sc 1 (by omega), (ISub.id (k + 1 + 1)).sc 0 (by omega)⟩ (ISub.id (k + 1 + 1)).tail.tail))
    rwa [← isub_bindAnd_gen C (ISub.id (k + 1 + 1)), ← isub_bindAnd_gen C' (ISub.id (k + 1 + 1)),
      isub_id_of_closed hDc, isub_id_of_closed hDc'] at h
  have hDDm : (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) = (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) ∨ ∃ l, EqTm0 S (k + 1 + 1) .one [] (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.univ l) := by
    rcases hTD with e | ⟨l, e⟩
    · exact .inl e
    · exact .inr ⟨l, spec_to_minimal_eq hW e⟩
  have hCty : IsTypB S (k + 1) .one [] C := pre_ty hS (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2 hFm
  have htEqF := minimal_to_spec_eq (fillTubeH_eq hS hFm hFm' hCty hDDm (spec_to_minimal_eq hW hteq)
    (spec_to_minimal_eq hW (RE2.typed hu0).2.2) h12)
  have hholds : ∀ {k4 : ℕ} (ρ : ISub k4 k), I.Entails .one (ψ.subst ρ.τ) → (ival (idEnv k4) (ψ.subst ρ.τ)).holds :=
    fun ρ h => (holds_iff_entails (I.scoped_subst hψs ρ.sc)).2 h
  -- the relations of the tubes and bases at points, at a type `C` at a point
  have eT0 : ∀ {k4 : ℕ} (ρ : ISub k4 k), (C.dinst .zero).isub ρ = C.isub (ISub.cons .zero trivial ρ) := by
    intro k4 ρ; rw [isub_dinst]; exact isub_up_dinst C ρ .zero trivial
  have hAw : ∀ k4 (ρ : ISub k4 k) (w : I) (hw : w.Scoped k4), RT2 S k4 (C.isub (ISub.cons w hw ρ)) (C.isub (ISub.cons w hw ρ)) :=
    fun k4 ρ w hw => hLRL k4 ρ w w hw hw (I_eq_refl _)
  have u0c : ∀ k4 (ρ : ISub k4 k) (w : I) (hw : w.Scoped k4), I.Eq w .zero →
      RE2 S k4 (C.isub (ISub.cons w hw ρ)) (u0.isub ρ) (u0'.isub ρ) := by
    intro k4 ρ w hw he
    have c := RE2.isub hW hu0 ρ
    rw [eT0] at c
    exact RE2.conv hW (hLRL k4 ρ .zero _ trivial hw (I_eq_symm he)) c
  have uuw : ∀ k4 (ρ : ISub k4 k) (x x' w : I) (hx : x.Scoped k4) (hx' : x'.Scoped k4) (hw : w.Scoped k4), I.Eq x x' →
      I.Eq x w → I.Entails .one (ψ.subst ρ.τ) →
      RE2 S k4 (C.isub (ISub.cons w hw ρ)) ((u.isub ρ.up).dinst x) ((u'.isub ρ.up).dinst x') :=
    fun k4 ρ x x' w hx hx' hw he hxw h => RE2.conv hW (hLRL k4 ρ x w hx hw hxw) (htube k4 ρ x x' hx hx' he (hholds ρ h))
  have u0r : ∀ k4 (ρ : ISub k4 k) (z w : I) (hz : z.Scoped k4) (hw : w.Scoped k4), I.Eq z .zero → I.Eq w .zero →
      I.Entails .one (ψ.subst ρ.τ) → RE2 S k4 (C.isub (ISub.cons w hw ρ)) ((u.isub ρ.up).dinst z) (u0'.isub ρ) := by
    intro k4 ρ z w hz hw hez hew h
    have a := uuw k4 ρ z .zero w hz trivial hw hez (I_eq_trans hez (I_eq_symm hew)) h
    have b := RE2.conv hW (hLRL k4 ρ .zero _ trivial hw (I_eq_symm hew)) (hbd' k4 ρ (hholds ρ h))
    exact RE2.trans hW (hAw k4 ρ w hw) a (RE2.trans hW (hAw k4 ρ w hw) (RE2.symm hW (hAw k4 ρ w hw) b)
      (u0c k4 ρ w hw hew))
  have u0l : ∀ k4 (ρ : ISub k4 k) (z w : I) (hz : z.Scoped k4) (hw : w.Scoped k4), I.Eq z .zero → I.Eq w .zero →
      I.Entails .one (ψ.subst ρ.τ) → RE2 S k4 (C.isub (ISub.cons w hw ρ)) (u0.isub ρ) ((u'.isub ρ.up).dinst z) := by
    intro k4 ρ z w hz hw hez hew h
    have a := uuw k4 ρ .zero z w trivial hz hw (I_eq_symm hez) (I_eq_symm hew) h
    have b := RE2.conv hW (hLRL k4 ρ .zero _ trivial hw (I_eq_symm hew)) (hbd k4 ρ (hholds ρ h))
    exact RE2.trans hW (hAw k4 ρ w hw) (u0c k4 ρ w hw hew)
      (RE2.trans hW (hAw k4 ρ w hw) (RE2.symm hW (hAw k4 ρ w hw) b) a)
  -- the faces
  have hface : I.Entails (I.or ψ.shift (.neg (.var 0))) (I.or ψ'.shift (.neg (.var 0))) :=
    ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _)) (ent_or_right _ _)
  have hface' : I.Entails (I.or ψ'.shift (.neg (.var 0))) (I.or ψ.shift (.neg (.var 0))) :=
    ent_or_elim (ent_trans (ent_shift h21) (ent_or_left _ _)) (ent_or_right _ _)
  have hσσ : ∀ i < k + 1, I.Eq (σ.τ i) (σ'.τ i) := by
    intro i hi; rcases i with _ | i
    · exact e0
    · have : σ.tail.τ i = σ'.tail.τ i := by rw [et]
      exact this ▸ I_eq_refl _
  have hψσ : ∀ k3 (σ : ISub k3 (k + 1)), (ival (idEnv k3) ((I.or ψ.shift (.neg (.var 0))).subst σ.τ)).holds →
      I.Entails .one (I.or (ψ.subst σ.tail.τ) (.neg (σ.τ 0))) := by
    intro k3 σ hh
    have := (holds_iff_entails (I.scoped_subst hχs σ.sc)).1 hh
    show I.Entails .one (I.or (ψ.subst σ.tail.τ) (.neg (σ.τ 0)))
    rw [← shift_subst_tail]; exact this
  have hσ0 : ∀ k3 (σ : ISub k3 (k + 1)), (σ.τ 0).Scoped k3 := fun k3 σ => σ.sc 0 (by omega)
  have hχσ : I.Eq ((I.or ψ'.shift (.neg (.var 0))).subst σ.τ) ((I.or ψ'.shift (.neg (.var 0))).subst σ'.τ) :=
    ieq_subst_ptw hσσ hχs'
  -- the judgmental equalities
  have eD1 : ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up).dinst .one = C.isub (ISub.cons (.and (σ.τ 0) .one) ⟨σ.sc 0 (by omega), trivial⟩ σ.tail) := by
    rw [isub_up_dinst _ σ .one trivial, isub_bindAnd_cons]
  have hR1 : RT2 S k3 (C.isub σ) (((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up).dinst .one) := by
    rw [eD1]
    have := hLRL k3 σ.tail (σ.τ 0) (.and (σ.τ 0) .one) (σ.sc 0 (by omega)) ⟨σ.sc 0 (by omega), trivial⟩
      (I_eq_symm (I_eq_and_one_r _))
    rwa [ISub.cons_tail] at this
  have hR1' : RT2 S k3 (C.isub σ') (((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up).dinst .one) := by
    rw [eD1]
    have := hLRL k3 σ'.tail (σ'.τ 0) (.and (σ.τ 0) .one) (σ'.sc 0 (by omega)) ⟨σ.sc 0 (by omega), trivial⟩
      (I_eq_trans (I_eq_symm e0) (I_eq_symm (I_eq_and_one_r _)))
    rwa [ISub.cons_tail, ← et] at this
  have hR1r : RT2 S k3 (((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up).dinst .one) (C.isub σ) := by
    rw [eD1]
    have := hLRL k3 σ.tail (.and (σ.τ 0) .one) (σ.τ 0) ⟨σ.sc 0 (by omega), trivial⟩ (σ.sc 0 (by omega))
      (I_eq_and_one_r _)
    rwa [ISub.cons_tail] at this
  have htyFc : HasTy S (k + 1) .one [] (Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ u u0)
      u0.dshift) C := htyF
  have htyFc' : HasTy S (k + 1) .one [] (Tm.comp (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ'.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ' u' u0')
      u0'.dshift) C := htyF'
  have hty := HasTy.isubS hW htyFc σ
  rw [comp_isub] at hty
  have hty' := HasTy.isubS hW htyFc' σ'
  rw [comp_isub] at hty'
  have heqσ : EqTm S k3 .one [] ((Tm.fill C ψ u u0).isub σ) ((Tm.fill C' ψ' u' u0').isub σ') (C.isub σ) :=
    (EqTm.isubS hW heqF σ).trans (eqTm_isub_ieq hW htyF' σ σ' hσσ trivial (ent_refl _) (ent_refl _))
  change EqTm S k3 .one [] ((Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ u u0)
      u0.dshift).isub σ) ((Tm.comp (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ'.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ' u' u0')
      u0'.dshift).isub σ') _ at heqσ
  rw [comp_isub, comp_isub] at heqσ
  have htσ : EqTm S (k3 + 1) (cof .one ((I.or ψ.shift (.neg (.var 0))).subst σ.τ)).shift []
      ((KubusCore.Meta.fillTube ψ u u0).isub σ.up) ((KubusCore.Meta.fillTube ψ' u' u0').isub σ'.up) ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up) := by
    have t1 := EqTm.cofIsub hW hχs htEqF σ
    have hup : ∀ i < k + 1 + 1, I.Eq (σ.up.τ i) (σ'.up.τ i) := by
      intro i hi; rcases i with _ | i
      · exact I_eq_refl _
      · exact ieq_shift (hσσ i (by omega))
    have hsc : (cof .one ((I.or ψ.shift (.neg (.var 0))).subst σ.τ)).shift.Scoped (k3 + 1) :=
      KubusCore.I.scoped_shift ⟨trivial, I.scoped_subst hχs σ.sc⟩
    have t2 := eqTm_isub_ieq hW (minimal_to_spec hTt') σ.up σ'.up hup hsc
      (by
        show I.Entails _ (((cof .one (I.or ψ'.shift (.neg (.var 0)))).shift).subst (I.up σ.τ))
        rw [I_shift_subst_up]
        exact ent_shift (ent_and_mono (ent_refl _) (ent_subst hface σ.τ)))
      (by
        show I.Entails _ (((cof .one (I.or ψ'.shift (.neg (.var 0)))).shift).subst (I.up σ'.τ))
        rw [I_shift_subst_up]
        exact ent_shift (ent_and_mono (ent_refl _) (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ))))
    exact t1.trans (EqTm.cofConvL (I.scoped_subst hχs σ.sc) t2 (TyEq.symm (hTD.isub hW σ.up)))
  have R := comp2 hW (k := k3) (C := (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up) (C' := (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ'.up)
    (ψ := (I.or ψ.shift (.neg (.var 0))).subst σ.τ) (ψ' := (I.or ψ'.shift (.neg (.var 0))).subst σ'.τ)
    (u := (KubusCore.Meta.fillTube ψ u u0).isub σ.up) (u' := (KubusCore.Meta.fillTube ψ' u' u0').isub σ'.up)
    (u0 := u0.dshift.isub σ) (u0' := u0'.dshift.isub σ')
    (lineRob_bindAnd hLR σ σ' et e0) (lineRob_bindAnd hLRL σ σ rfl (I_eq_refl _))
    (fun k4 Θ X' => by rw [Tm.isub_isub, isub_bindAnd_gen]; exact hKT k4 _ X')
    (fun X' => by rw [isub_up_dinst _ σ .one trivial, isub_bindAnd_cons]; exact hKH k3 _ X')
    (hty.tyConv (tyB hR1)) (hty'.tyConv (tyB hR1')) (heqσ.tyConv (tyB hR1)) htσ
    (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ)) (ent_trans (eq_ent (I_eq_symm hχσ)) (ent_subst hface' σ.τ))
    ?_ ?_ ?_ ?_
  · show RE2 S k3 (C.isub σ) ((Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ u u0)
      u0.dshift).isub σ) ((Tm.comp (C'.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ'.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ' u' u0')
      u0'.dshift).isub σ')
    rw [comp_isub, comp_isub]
    exact RE2.conv hW hR1r R
  · -- the tubes of the fillers
    intro k4 σ2 x x' hx hx' hEx hh
    have hh2 : (ival (idEnv k4) ((I.or ψ.shift (.neg (.var 0))).subst (σ.comp σ2).τ)).holds := by
      rw [I_subst_comp]; exact hh
    have hh2' : (ival (idEnv k4) ((I.or ψ'.shift (.neg (.var 0))).subst (σ'.comp σ2).τ)).holds := by
      rw [I_subst_comp]
      exact entails_holds (ent_subst (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ)) σ2.τ) hh
    have hsp := comp_tube_typed hW htyFc (σ.comp σ2) x hx hh2
    have hsp' := comp_tube_typed hW htyFc' (σ'.comp σ2) x' hx' hh2'
    rw [isub_bindAnd_cons, fillTube_isub_dinst, ISub.comp_tail] at hsp hsp'
    rw [← et] at hsp'
    have hyy' : I.Eq ((σ.comp σ2).τ 0) ((σ'.comp σ2).τ 0) := I_eq_subst e0 σ2.τ
    have hy := hσ0 k4 (σ.comp σ2)
    have hy' := hσ0 k4 (σ'.comp σ2)
    have hsp'' := hsp'.tyConv (TyEq.symm (tyB (hLR k4 (σ.tail.comp σ2) _ _ (show (I.and ((σ.comp σ2).τ 0) x).Scoped k4 from ⟨hy, hx⟩)
      (show (I.and ((σ'.comp σ2).τ 0) x').Scoped k4 from ⟨hy', hx'⟩)
      (ieq_and_congr hyy' hEx))))
    rw [Tm.isub_isub (KubusCore.Meta.fillTube ψ u u0), Tm.isub_isub (KubusCore.Meta.fillTube ψ' u' u0'),
      ← ISub.up_comp, ← ISub.up_comp, fillTube_isub_dinst, fillTube_isub_dinst, ISub.comp_tail, ISub.comp_tail,
      ← et, Tm.isub_isub (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))), ISub.up_comp_cons, isub_bindAnd_cons, ISub.comp_tail]
    have hor := hψσ k4 (σ.comp σ2) hh2
    rw [ISub.comp_tail] at hor
    refine RE2_sys2 hW (I.scoped_subst hψs (σ.tail.comp σ2).sc) (I.scoped_subst hψs' (σ.tail.comp σ2).sc) hy hy'
      (ent_subst h12 _) (ent_subst h21 _) (eq_ent (ieq_neg hyy')) (eq_ent (ieq_neg (I_eq_symm hyy'))) hor
      (hAw k4 _ _ _) hsp hsp'' (fun k5 σ4 h => ?_) (fun k5 σ4 h h' => ?_) (fun k5 σ4 h h' => ?_) (fun k5 σ4 h' => ?_)
    · rw [dinst_up_isub, dinst_up_isub, Tm.isub_isub, ISub.cons_comp]
      have hxs := I.scoped_subst (show (I.and ((σ.comp σ2).τ 0) x).Scoped k4 from ⟨hy, hx⟩) σ4.sc
      exact uuw k5 _ _ _ _ hxs (I.scoped_subst (show (I.and _ x').Scoped k4 from ⟨hy', hx'⟩) σ4.sc) hxs
        (I_eq_subst (ieq_and_congr hyy' hEx) _) (I_eq_refl _) (ent_comp_inv h)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      have e0' := ieq_zero_of_holds_neg (I.scoped_subst hy σ4.sc)
        (entails_holds h' (ρ := idEnv k5) (by rw [ival_one]; rfl))
      exact u0r k5 _ _ _ (I.scoped_subst (show (I.and ((σ.comp σ2).τ 0) x).Scoped k4 from ⟨hy, hx⟩) σ4.sc) _ (ieq_and_zero_left _ e0') (ieq_and_zero_left _ e0') (ent_comp_inv h)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      have e0' := ieq_zero_of_holds_neg (I.scoped_subst hy σ4.sc)
        (entails_holds h' (ρ := idEnv k5) (by rw [ival_one]; rfl))
      exact u0l k5 _ _ _ (I.scoped_subst (show (I.and _ x').Scoped k4 from ⟨hy', hx'⟩) σ4.sc) _
        (ieq_and_zero_left _ (I_eq_trans (I_eq_subst (I_eq_symm hyy') _) e0')) (ieq_and_zero_left _ e0')
        (ent_comp_inv h)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      have e0' := ieq_zero_of_holds_neg (I.scoped_subst hy σ4.sc)
        (entails_holds h' (ρ := idEnv k5) (by rw [ival_one]; rfl))
      exact u0c k5 _ _ _ (ieq_and_zero_left _ e0')
  · -- the bases
    rw [isub_up_dinst _ σ .zero trivial, isub_bindAnd_cons, dshift_isub_tail, dshift_isub_tail, ← et]
    exact u0c k3 σ.tail _ _ (ieq_and_zero_right _)
  · -- the boundary of the tubes, on the left
    intro k4 σ2 hh
    have hh2 : (ival (idEnv k4) ((I.or ψ.shift (.neg (.var 0))).subst (σ.comp σ2).τ)).holds := by
      rw [I_subst_comp]; exact hh
    have hsp := comp_tube_typed hW htyFc (σ.comp σ2) .zero trivial hh2
    rw [isub_bindAnd_cons, fillTube_isub_dinst, ISub.comp_tail] at hsp
    rw [Tm.isub_isub (KubusCore.Meta.fillTube ψ u u0), ← ISub.up_comp, fillTube_isub_dinst, ISub.comp_tail,
      Tm.isub_isub (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))), ISub.up_comp_cons, isub_bindAnd_cons, ISub.comp_tail, dshift_isub_tail, ← et, Tm.isub_isub u0']
    have hy := hσ0 k4 (σ.comp σ2)
    have hor := hψσ k4 (σ.comp σ2) hh2
    rw [ISub.comp_tail] at hor
    refine RE2_split_l hW (I.scoped_subst hψs (σ.tail.comp σ2).sc) hy hor (hAw k4 _ _ _) hsp
      (RE2.typed (u0c k4 (σ.tail.comp σ2) _ (show (I.and ((σ.comp σ2).τ 0) .zero).Scoped k4 from ⟨hy, trivial⟩) (ieq_and_zero_right _))).2.1 (fun k5 σ4 h => ?_)
      (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      exact u0r k5 _ _ _ (I.scoped_subst (show (I.and ((σ.comp σ2).τ 0) .zero).Scoped k4 from ⟨hy, trivial⟩) σ4.sc) _ (ieq_and_zero_right _) (ieq_and_zero_right _) (ent_comp_inv h)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      exact u0c k5 _ _ _ (ieq_and_zero_right _)
  · -- the boundary of the tubes, on the right
    intro k4 σ2 hh
    have hh2 : (ival (idEnv k4) ((I.or ψ.shift (.neg (.var 0))).subst (σ.comp σ2).τ)).holds := by
      rw [I_subst_comp]; exact hh
    have hh2' : (ival (idEnv k4) ((I.or ψ'.shift (.neg (.var 0))).subst (σ'.comp σ2).τ)).holds := by
      rw [I_subst_comp]
      exact entails_holds (ent_subst (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ)) σ2.τ) hh
    have hyy' : I.Eq ((σ.comp σ2).τ 0) ((σ'.comp σ2).τ 0) := I_eq_subst e0 σ2.τ
    have hy := hσ0 k4 (σ.comp σ2)
    have hy' := hσ0 k4 (σ'.comp σ2)
    have hsp := comp_tube_typed hW htyFc' (σ'.comp σ2) .zero trivial hh2'
    rw [isub_bindAnd_cons, fillTube_isub_dinst, ISub.comp_tail, ← et] at hsp
    have hsp' := hsp.tyConv (TyEq.symm (tyB (hLR k4 (σ.tail.comp σ2) _ _ (show (I.and ((σ.comp σ2).τ 0) .zero).Scoped k4 from ⟨hy, trivial⟩)
      (show (I.and ((σ'.comp σ2).τ 0) .zero).Scoped k4 from ⟨hy', trivial⟩)
      (ieq_and_congr hyy' (I_eq_refl _)))))
    rw [Tm.isub_isub (KubusCore.Meta.fillTube ψ' u' u0'), ← ISub.up_comp, fillTube_isub_dinst, ISub.comp_tail, ← et,
      Tm.isub_isub (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))), ISub.up_comp_cons, isub_bindAnd_cons, ISub.comp_tail, dshift_isub_tail, Tm.isub_isub u0]
    have hor := hψσ k4 (σ.comp σ2) hh2
    rw [ISub.comp_tail] at hor
    have hor' : I.Entails .one (I.or (ψ'.subst (σ.tail.comp σ2).τ) (.neg ((σ'.comp σ2).τ 0))) :=
      ent_trans hor (ent_or_elim (ent_trans (ent_subst h12 _) (ent_or_left _ _))
        (ent_trans (eq_ent (ieq_neg hyy')) (ent_or_right _ _)))
    refine RE2_split_r hW (I.scoped_subst hψs' (σ.tail.comp σ2).sc) hy' hor' (hAw k4 _ _ _) hsp'
      (RE2.typed (u0c k4 (σ.tail.comp σ2) _ (show (I.and ((σ.comp σ2).τ 0) .zero).Scoped k4 from ⟨hy, trivial⟩) (ieq_and_zero_right _))).1 (fun k5 σ4 h => ?_)
      (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      exact u0l k5 _ _ _ (I.scoped_subst (show (I.and ((σ'.comp σ2).τ 0) .zero).Scoped k4 from ⟨hy', trivial⟩) σ4.sc) _ (ieq_and_zero_right _) (ieq_and_zero_right _)
        (ent_trans (ent_comp_inv h) (ent_subst h21 _))
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      exact u0c k5 _ _ _ (ieq_and_zero_right _)

/-- The end of a heterogeneous filler, against its composition. -/
theorem fill_one_pt {C u u0 : Tm} {ψ : I} (hψs : ψ.Scoped k) (hLRL : LineRob S k C C)
    (hKT : ∀ k3 (Θ : ISub (k3 + 1) (k + 1)) X', RT2 S (k3 + 1) (C.isub Θ) X' → KanT2 S k3 (C.isub Θ) X')
    (hKH : ∀ k3 (Θ : ISub k3 (k + 1)) X', RT2 S k3 (C.isub Θ) X' → KanH2 S k3 (C.isub Θ) X')
    (htyC : HasTy S k .one [] (Tm.comp C ψ u u0) (C.dinst .one))
    (htyF : HasTy S (k + 1) .one [] (Tm.fill C ψ u u0) C)
    (htube : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r) ((u.isub σ.up).dinst r'))
    (hu0 : RE2 S k (C.dinst .zero) u0 u0)
    (hbd : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) ((u.isub σ.up).dinst .zero) (u0.isub σ))
    {k3 : ℕ} (τ : ISub k3 k) :
    RE2 S k3 (C.isub (ISub.cons .one trivial τ)) ((Tm.fill C ψ u u0).isub (ISub.cons .one trivial τ))
      ((Tm.comp C ψ u u0).isub τ) := by
  have hS := sigClosed_of_wfSig hW
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hFm : HasTy0 S (k + 1) (I.one).shift (Ctx.dshift []) (Tm.fill C ψ u u0) C := spec_to_minimal hW htyF
  have hCm := spec_to_minimal hW htyC
  obtain ⟨lC, hCt, -, -, hu0t⟩ := comp_parts hS hCm
  have hv0 : (I.var 0).Scoped (k + 1) := show 0 < k + 1 by omega
  have hχs : (I.or ψ.shift (.neg (.var 0))).Scoped (k + 1) := ⟨KubusCore.I.scoped_shift hψs, hv0⟩
  -- the end of the filler, judgmentally
  have hCD : EqTm0 S (k + 1) (I.one).shift (Ctx.dshift []) C
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).subst Tm.var (I.up (I.inst0 .one))) (.univ lC) := by
    rw [Cfill_up1]
    have e := HasTy0.sk1_ieq hS hCt (r := .var 0) (r' := .and .one (.var 0)) hv0 ⟨trivial, hv0⟩
      (I_eq_symm (I_eq_and_one_l _)) (KubusCore.Meta.scoped_shift (show I.one.Scoped k from trivial)) (ent_refl _)
    rwa [sk_var1] at e
  have hF1 : HasTy0 S k .one [] (Tm.comp ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).subst Tm.var
      (I.up (I.inst0 .one))) (.or ψ (.neg .one))
      ((KubusCore.Meta.fillTube ψ u u0).subst Tm.var (I.up (I.inst0 .one))) u0) (C.dinst .one) := by
    have := HasTy0.dsubst hS hFm (r := .one) trivial
    rwa [fill_dinst] at this
  have hceq := comp_cong hS hCm hF1 hCD (ent_or_left _ _) (ent_neg_one ψ) (fill1_tubeH_eq hS hFm hCm)
    (EqTm0.refl hu0t)
  rw [← fill_dinst C ψ u u0 .one] at hceq
  have eF1 : ((Tm.fill C ψ u u0).dinst .one).isub τ = (Tm.fill C ψ u u0).isub (ISub.cons .one trivial τ) := by
    rw [isub_dinst]; exact isub_up_dinst _ τ .one trivial
  have eC1 : (C.dinst .one).isub τ = (C.isub τ.up).dinst .one := by rw [isub_dinst]; rfl
  have heqk := EqTm.isubS hW (minimal_to_spec_eq hceq) τ
  rw [eF1, eC1] at heqk
  change EqTm S k3 .one [] _ ((Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0)))
    (KubusCore.Meta.fillTube ψ u u0) u0.dshift).isub (ISub.cons .one trivial τ)) _ at heqk
  rw [comp_isub, comp_isub] at heqk
  have hteq := EqTm.cofIsub hW hψs (minimal_to_spec_eq (fill1_tubeH_eq hS hFm hCm)) τ
  rw [up_inst0_one_isub] at hteq
  have eT0 : ∀ {k4 : ℕ} (ρ : ISub k4 k), (C.dinst .zero).isub ρ = C.isub (ISub.cons .zero trivial ρ) := by
    intro k4 ρ; rw [isub_dinst]; exact isub_up_dinst C ρ .zero trivial
  have hholds : ∀ {k4 : ℕ} (ρ : ISub k4 k), I.Entails .one (ψ.subst ρ.τ) → (ival (idEnv k4) (ψ.subst ρ.τ)).holds :=
    fun ρ h => (holds_iff_entails (I.scoped_subst hψs ρ.sc)).2 h
  -- the composition at the end of the filler, against the composition
  have htyFc : HasTy S (k + 1) .one [] (Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      (.or ψ.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ u u0) u0.dshift) C := htyF
  have hty := HasTy.isubS hW htyC τ
  rw [comp_isub, eC1] at hty
  have hty' := HasTy.isubS hW htyFc (ISub.cons .one trivial τ)
  rw [comp_isub, ← isub_up_dinst C τ .one trivial] at hty'
  have R := comp2 hW (k := k3) (C := C.isub τ.up)
    (C' := (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons .one trivial τ).up)
    (ψ := ψ.subst τ.τ) (ψ' := (I.or ψ.shift (.neg (.var 0))).subst (ISub.cons .one trivial τ).τ)
    (u := u.isub τ.up) (u' := (KubusCore.Meta.fillTube ψ u u0).isub (ISub.cons .one trivial τ).up)
    (u0 := u0.isub τ) (u0' := u0.dshift.isub (ISub.cons .one trivial τ))
    (fun k4 τ2 r r' hr hr' hE => by
      rw [Tm.isub_isub, Tm.isub_isub, ISub.up_comp_cons, ISub.up_comp_cons, isub_bindAnd_cons, ISub.comp_tail,
        ISub.tail_cons]
      exact hLRL k4 (τ.comp τ2) r _ hr _ (I_eq_trans hE (I_eq_symm (I_eq_and_one_l r'))))
    (LineRob.isub hLRL τ)
    (fun k4 Θ X' => by rw [Tm.isub_isub]; exact hKT k4 _ X')
    (fun X' => by rw [isub_up_dinst C τ .one trivial]; exact hKH k3 _ X')
    hty hty' heqk hteq
    (by show I.Entails _ (I.or (ψ.shift.subst (ISub.cons .one trivial τ).τ) (.neg .one))
        rw [I_shift_cons]; exact ent_or_left _ _)
    (by show I.Entails (I.or (ψ.shift.subst (ISub.cons .one trivial τ).τ) (.neg .one)) _
        rw [I_shift_cons]; exact ent_neg_one _)
    ?_ ?_ ?_ ?_
  · show RE2 S k3 _ ((Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0)))
      (KubusCore.Meta.fillTube ψ u u0) u0.dshift).isub (ISub.cons .one trivial τ)) ((Tm.comp C ψ u u0).isub τ)
    rw [comp_isub, comp_isub, ← isub_up_dinst C τ .one trivial]
    refine RE2.symm hW (A' := (C.isub τ.up).dinst .one) ?_ R
    rw [isub_up_dinst C τ .one trivial]
    exact hLRL k3 τ .one .one trivial trivial (I_eq_refl _)
  · -- the tubes
    intro k4 τ2 r r' hr hr' hE hh
    have hh4 : (ival (idEnv k4) (ψ.subst (τ.comp τ2).τ)).holds := by rw [I_subst_comp]; exact hh
    have hf4 : I.Entails .one (ψ.subst (τ.comp τ2).τ) := (holds_iff_entails (I.scoped_subst hψs (τ.comp τ2).sc)).1 hh4
    have hhF : (ival (idEnv k4) ((I.or ψ.shift (.neg (.var 0))).subst ((ISub.cons .one trivial τ).comp τ2).τ)).holds := by
      rw [I_subst_comp]
      refine (holds_iff_entails ?_).2 ?_
      · exact I.scoped_subst (I.scoped_subst hχs (ISub.cons .one trivial τ).sc) τ2.sc
      · show I.Entails .one (I.or ((ψ.shift.subst (ISub.cons .one trivial τ).τ).subst τ2.τ) (.neg (I.one.subst τ2.τ)))
        rw [I_shift_cons, ← I_subst_comp]; exact ent_trans hf4 (ent_or_left _ _)
    have hsp := comp_tube_typed hW htyFc ((ISub.cons .one trivial τ).comp τ2) r' hr' hhF
    rw [isub_bindAnd_cons, fillTube_isub_dinst, ISub.comp_tail, ISub.tail_cons] at hsp
    have hsp' := hsp.tyConv (tyB (hLRL k4 (τ.comp τ2) _ r _ hr (I_eq_trans (I_eq_and_one_l r') (I_eq_symm hE))))
    rw [Tm.isub_isub (KubusCore.Meta.fillTube ψ u u0), ← ISub.up_comp, fillTube_isub_dinst, ISub.comp_tail,
      ISub.tail_cons, Tm.isub_isub u, ← ISub.up_comp, Tm.isub_isub C, ISub.up_comp_cons]
    have hA := hLRL k4 (τ.comp τ2) r r hr hr (I_eq_refl _)
    refine RE2_split_r hW (I.scoped_subst hψs (τ.comp τ2).sc) (show (I.neg (I.one.subst τ2.τ)).Scoped k4 from trivial)
      (ent_trans hf4 (ent_or_left _ _)) hA hsp' (RE2.typed (htube k4 (τ.comp τ2) r r hr hr (I_eq_refl _) hh4)).1
      (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, dinst_up_isub, Tm.isub_isub, ISub.cons_comp]
      exact htube k5 _ _ _ (I.scoped_subst hr σ4.sc) (I.scoped_subst (show (I.and (I.one.subst τ2.τ) r').Scoped k4 from
        ⟨trivial, hr'⟩) σ4.sc) (I_eq_subst (I_eq_trans hE (I_eq_symm (I_eq_and_one_l r'))) _)
        (hholds _ (ent_comp_inv h))
    · exact absurd h (by show ¬ I.Entails .one (I.neg .one); decide)
  · -- the bases
    rw [isub_up_dinst _ τ .zero trivial, dshift_isub_cons, ← eT0]
    exact RE2.isub hW hu0 τ
  · -- the boundary, on the left
    intro k4 τ2 hh
    rw [Tm.isub_isub u, ← ISub.up_comp, Tm.isub_isub C, ISub.up_comp_cons, dshift_isub_cons, Tm.isub_isub u0]
    exact hbd k4 (τ.comp τ2) (by rw [I_subst_comp]; exact hh)
  · -- the boundary, on the right
    intro k4 τ2 hh
    have hh4 : (ival (idEnv k4) (ψ.subst (τ.comp τ2).τ)).holds := by rw [I_subst_comp]; exact hh
    have hf4 : I.Entails .one (ψ.subst (τ.comp τ2).τ) := (holds_iff_entails (I.scoped_subst hψs (τ.comp τ2).sc)).1 hh4
    have hhF : (ival (idEnv k4) ((I.or ψ.shift (.neg (.var 0))).subst ((ISub.cons .one trivial τ).comp τ2).τ)).holds := by
      rw [I_subst_comp]
      refine (holds_iff_entails ?_).2 ?_
      · exact I.scoped_subst (I.scoped_subst hχs (ISub.cons .one trivial τ).sc) τ2.sc
      · show I.Entails .one (I.or ((ψ.shift.subst (ISub.cons .one trivial τ).τ).subst τ2.τ) (.neg (I.one.subst τ2.τ)))
        rw [I_shift_cons, ← I_subst_comp]; exact ent_trans hf4 (ent_or_left _ _)
    have hsp := comp_tube_typed hW htyFc ((ISub.cons .one trivial τ).comp τ2) .zero trivial hhF
    rw [isub_bindAnd_cons, fillTube_isub_dinst, ISub.comp_tail, ISub.tail_cons] at hsp
    have hsp' := hsp.tyConv (tyB (hLRL k4 (τ.comp τ2) _ .zero _ trivial (ieq_and_zero_right _)))
    rw [Tm.isub_isub (KubusCore.Meta.fillTube ψ u u0), ← ISub.up_comp, fillTube_isub_dinst, ISub.comp_tail,
      ISub.tail_cons, Tm.isub_isub u0, Tm.isub_isub C, ISub.up_comp_cons]
    have hA := hLRL k4 (τ.comp τ2) .zero .zero trivial trivial (I_eq_refl _)
    have hb := hbd k4 (τ.comp τ2) hh4
    refine RE2_split_r hW (I.scoped_subst hψs (τ.comp τ2).sc) (show (I.neg (I.one.subst τ2.τ)).Scoped k4 from trivial)
      (ent_trans hf4 (ent_or_left _ _)) hA hsp' (RE2.typed hb).2.1 (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
      have hh5 := hholds ((τ.comp τ2).comp σ4) (ent_comp_inv h)
      have hA5 := hLRL k5 ((τ.comp τ2).comp σ4) .zero .zero trivial trivial (I_eq_refl _)
      exact RE2.trans hW hA5 (RE2.symm hW hA5 (hbd k5 _ hh5)) (htube k5 _ .zero _ trivial
        (I.scoped_subst (show (I.and (I.one.subst τ2.τ) I.zero).Scoped k4 from ⟨trivial, trivial⟩) σ4.sc)
        (I_eq_symm (ieq_and_zero_right _)) hh5)
    · exact absurd h (by show ¬ I.Entails .one (I.neg .one); decide)

/-- A filler at a point where the face of its restricted composition holds steps to the system of its tube
at the end. -/
theorem fill_pt_expand {C u u0 x : Tm} {ψ : I} (hψs : ψ.Scoped k) (hLRL : LineRob S k C C)
    (htyF : HasTy S (k + 1) .one [] (Tm.fill C ψ u u0) C) {k3 : ℕ} (τ : ISub k3 k) (r : I) (hr : r.Scoped k3)
    (hor : I.Entails .one (.or (ψ.subst τ.τ) (.neg r))) (hx : HasTy S k3 .one [] x (C.isub (ISub.cons r hr τ)))
    (h : HasTy S k3 .one [] (.split (ψ.subst τ.τ) ((u.isub τ.up).dinst (.and r .one)) (.neg r) (u0.isub τ))
        (C.isub (ISub.cons r hr τ)) →
      RE2 S k3 (C.isub (ISub.cons r hr τ)) (.split (ψ.subst τ.τ) ((u.isub τ.up).dinst (.and r .one)) (.neg r)
        (u0.isub τ)) x) :
    RE2 S k3 (C.isub (ISub.cons r hr τ)) ((Tm.fill C ψ u u0).isub (ISub.cons r hr τ)) x := by
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hA := hLRL k3 τ r r hr hr (I_eq_refl _)
  have hχs : (I.or ψ.shift (.neg (.var 0))).Scoped (k + 1) := ⟨KubusCore.I.scoped_shift hψs, show 0 < k + 1 by omega⟩
  have hχ : I.Entails .one ((I.or ψ.shift (.neg (.var 0))).subst (ISub.cons r hr τ).τ) := by
    show I.Entails .one (I.or (ψ.shift.subst (ISub.cons r hr τ).τ) (.neg r))
    rw [I_shift_cons]; exact hor
  have hhχ := (holds_iff_entails (I.scoped_subst hχs (ISub.cons r hr τ).sc)).2 hχ
  have htyFc : HasTy S (k + 1) .one [] (Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      (.or ψ.shift (.neg (.var 0))) (KubusCore.Meta.fillTube ψ u u0) u0.dshift) C := htyF
  have hH := HasTy.isubS hW htyFc (ISub.cons r hr τ)
  rw [comp_isub, comp_eq] at hH
  have s1 := stable_hcompFace hW hχ hH
  have hsp1 := hcomp_tube_typed' hW hH .one trivial hhχ
  rw [compTube_d1] at s1 hsp1
  have s2 := stable_transpFace hW (ent_refl _) hsp1
  have hsp2 := comp_tube_typed hW htyFc (ISub.cons r hr τ) .one trivial hhχ
  rw [isub_bindAnd_cons, ISub.tail_cons] at hsp2
  have hsp2' := hsp2.tyConv (tyB (hLRL k3 τ (.and r .one) r ⟨hr, trivial⟩ hr (I_eq_and_one_r r)))
  rw [fillTube_isub_dinst, ISub.tail_cons] at hsp2' s2 s1 hsp1
  have e1 := h hsp2'
  have e2 := RE2.expandL hW hA hsp1 hx s2 e1
  have e3 := RE2.expandL hW hA hH hx s1 e2
  show RE2 S k3 _ ((Tm.comp (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0)))
    (KubusCore.Meta.fillTube ψ u u0) u0.dshift).isub (ISub.cons r hr τ)) x
  rw [comp_isub, comp_eq]
  exact e3

/-- A heterogeneous filler at a point where the face of its composition holds. -/
theorem fill_face_pt {C u u0 : Tm} {ψ : I} (hψs : ψ.Scoped k) (hLRL : LineRob S k C C)
    (htyF : HasTy S (k + 1) .one [] (Tm.fill C ψ u u0) C)
    (htube : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r) ((u.isub σ.up).dinst r'))
    {k3 : ℕ} (τ : ISub k3 k) (r : I) (hr : r.Scoped k3) (hh : (ival (idEnv k3) (ψ.subst τ.τ)).holds) :
    RE2 S k3 (C.isub (ISub.cons r hr τ)) ((Tm.fill C ψ u u0).isub (ISub.cons r hr τ)) ((u.isub τ.up).dinst r) := by
  have hf : I.Entails .one (ψ.subst τ.τ) := (holds_iff_entails (I.scoped_subst hψs τ.sc)).1 hh
  have hA := hLRL k3 τ r r hr hr (I_eq_refl _)
  have base := RE2.conv hW (hLRL k3 τ (.and r .one) r ⟨hr, trivial⟩ hr (I_eq_and_one_r r))
    (htube k3 τ (.and r .one) r ⟨hr, trivial⟩ hr (I_eq_and_one_r r) hh)
  exact fill_pt_expand hW hψs hLRL htyF τ r hr (ent_trans hf (ent_or_left _ _)) (RE2.typed base).2.1
    (fun hsp => RE2.expandL hW hA hsp (RE2.typed base).2.1 (stable_splitL hW hf hsp) base)

/-- A heterogeneous filler at the start of its line. -/
theorem fill_zero_pt {C u u0 : Tm} {ψ : I} (hψs : ψ.Scoped k) (hLRL : LineRob S k C C)
    (htyF : HasTy S (k + 1) .one [] (Tm.fill C ψ u u0) C)
    (htube : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r) ((u.isub σ.up).dinst r'))
    (hu0 : RE2 S k (C.dinst .zero) u0 u0)
    (hbd : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) ((u.isub σ.up).dinst .zero) (u0.isub σ))
    {k3 : ℕ} (τ : ISub k3 k) :
    RE2 S k3 (C.isub (ISub.cons .zero trivial τ)) ((Tm.fill C ψ u u0).isub (ISub.cons .zero trivial τ)) (u0.isub τ) := by
  have eT0 : ∀ {k4 : ℕ} (ρ : ISub k4 k), (C.dinst .zero).isub ρ = C.isub (ISub.cons .zero trivial ρ) := by
    intro k4 ρ; rw [isub_dinst]; exact isub_up_dinst C ρ .zero trivial
  have hu0τ := RE2.isub hW hu0 τ
  rw [eT0] at hu0τ
  have hor : I.Entails .one (.or (ψ.subst τ.τ) (.neg .zero)) :=
    ent_trans (show I.Entails .one (.neg .zero) by decide) (ent_or_right _ _)
  refine fill_pt_expand hW hψs hLRL htyF τ .zero trivial hor (RE2.typed hu0τ).1 (fun hsp => ?_)
  refine RE2_split_l hW (I.scoped_subst hψs τ.sc) (show (I.neg I.zero).Scoped k3 from trivial) hor
    (hLRL k3 τ .zero .zero trivial trivial (I_eq_refl _)) hsp (RE2.typed hu0τ).1 (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_)
  · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
    have hh4 : (ival (idEnv k4) (ψ.subst (τ.comp σ4).τ)).holds :=
      (holds_iff_entails (I.scoped_subst hψs (τ.comp σ4).sc)).2 (ent_comp_inv h)
    have hz := I.scoped_subst (show (I.and I.zero I.one).Scoped k3 from ⟨trivial, trivial⟩) σ4.sc
    exact RE2.trans hW (hLRL k4 _ .zero .zero trivial trivial (I_eq_refl _))
      (RE2.conv hW (hLRL k4 _ _ .zero hz trivial (fun _ => rfl))
        (htube k4 (τ.comp σ4) _ .zero hz trivial (fun _ => rfl) hh4))
      (hbd k4 _ hh4)
  · rw [Tm.isub_isub, Tm.isub_isub, ISub.cons_comp]
    have := RE2.isub hW hu0 (τ.comp σ4)
    rw [eT0] at this
    exact this

end

end Model.Whnf
