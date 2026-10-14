import Model.Whnf.Kan2Fill

/-!
# Binary heterogeneous composition
-/

set_option autoImplicit false

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- The tubes of congruent heterogeneous compositions are judgmentally equal. -/
theorem compTube_eq (hS : SigClosed S) {Ψ Φ Γ C C' ψ ψ' u u' u0 u0' l}
    (hc : HasTy0 S Ψ Φ Γ (comp C ψ u u0) (C.dinst .one))
    (hc' : HasTy0 S Ψ Φ Γ (comp C' ψ' u' u0') (C.dinst .one))
    (hCC : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift C C' (univ l))
    (h1 : I.Entails ψ ψ')
    (hu : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u u' C) :
    EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (transp (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u)
      (transp (C'.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u') (C.dinst .one).dshift := by
  rw [comp_eq] at hc hc'
  obtain ⟨_, ⟨_, hψs, htube, hb, _⟩, _⟩ := gen_hcomp hc rfl
  obtain ⟨_, ⟨_, _, htube', _, _⟩, _⟩ := gen_hcomp hc' rfl
  have hs := scoped_of_ty hc
  have hw0 := wf_of_ty hc
  have hXs : (cof Φ ψ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hψs⟩
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left Φ ψ)
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  obtain ⟨lC, ⟨hC, _, _, _⟩, _⟩ := gen_transpF hb rfl
  have htr := transp_retype htube
  have htr' := transp_retype (HasTy0.restrict hXs (ent_shift (ent_and_mono (ent_refl _) h1)) htube')
  have hLL : EqTm0 S (Ψ + 1 + 1) (cof Φ ψ).shift.shift Γ.dshift.dshift
      (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (C'.dsubst (bind2 (.or (.var 1) (.var 0)))) (univ l) := by
    have := EqTm0.isub hS (τ := bind2 (.or (.var 1) (.var 0))) hCC
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (ent_bind2_shift _ (ent_shift hXΦ))
      (by rw [ctxI_bind2]; exact (hw0.dwk2 hS).restrict (scoped_shift hXs) (ent_shift hXΦ))
    rwa [ctxI_bind2] at this
  have eL1 := EqTm0.dsubst hS hLL (r := .one) trivial
  have hwX : Wf0 S (Ψ + 1) (cof Φ ψ).shift (ctxI (fun n => .var (n + 1)) Γ) := by
    rw [ctxI_add1]; exact (Wf0.dwk hS hw0).restrict hXs hXΦ
  have eL0 : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift C
      ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .zero) (univ lC) := by
    rw [L_d0]
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .var 0) (r' := .or (.var 0) .zero) hXΦ hv0
      ⟨hv0, trivial⟩ (by omega) (I_eq_symm (I_eq_or_zero_r _)) hwX
    rwa [ctxI_add1, sk_var1] at e
  have et := EqTm0.transp htr (HasTy0.conv htr' (EqTm0.symm eL1)) hLL (ent_refl _) (ent_refl _)
    (EqTm0.conv hu eL0)
  have eC1' : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift
      ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .one) (C.dinst .one).dshift (univ lC) := by
    rw [L_d1]
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .or (.var 0) .one) (r' := .one) hXΦ
      ⟨hv0, trivial⟩ trivial (by omega) (I_eq_or_one_r _) hwX
    rwa [ctxI_add1, sk_one1] at e
  exact EqTm0.conv et eC1'

/-- The tube of the end of a filler is judgmentally the tube of the composition. -/
theorem hfill1_tube_eq (hS : SigClosed S) {Ψ Φ Γ A φ u u0 l} (hA : HasTy0 S Ψ Φ Γ A (univ l))
    (hφ : φ.Scoped Ψ) (hu : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift)
    (hu0 : HasTy0 S Ψ Φ Γ u0 A) (hside : EqTm0 S Ψ (cof Φ φ) Γ (u.dinst .zero) u0 A) :
    EqTm0 S (Ψ + 1) (cof Φ (.or φ (.neg .one))).shift Γ.dshift
      ((fillTube φ u u0).subst Tm.var (I.up (I.inst0 .one))) u A.dshift := by
  have hs := scoped_of_ty hA
  have hw0 := wf_of_ty hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hF := (hfill_typed hS hA hφ hu hu0 hside).1
  rw [hfill_eq] at hF
  obtain ⟨_, ⟨_, _, htube, _, _⟩, _⟩ := gen_hcomp hF rfl
  have hX : (cof Φ (.or φ (.neg .one))).Scoped Ψ := ⟨hs, ⟨hφ, trivial⟩⟩
  have hXe : I.Entails (cof Φ (.or φ (.neg .one))).shift (cof Φ φ).shift :=
    ent_shift (ent_and_mono (ent_refl _) (ent_neg_one φ))
  have hXs : (cof Φ (.or φ (.neg .one))).shift.Scoped (Ψ + 1) := scoped_shift hX
  have htyped := HasTy0.isub hS (τ := I.up (I.inst0 .one)) (Φ' := (cof Φ (.or φ (.neg .one))).shift)
    htube (Iup_scoped (fun i hi => by
      rcases i with _ | i
      · trivial
      · exact show i < Ψ by omega))
    (by rw [fillR_up1]; exact ent_refl _)
    (by rw [ctxI_up_inst0]; exact (Wf0.dwk hS hw0).restrict hXs (ent_shift (ent_and_left _ _)))
  rw [ctxI_up_inst0, dshift2_up_inst0, fillTube_up1'] at htyped
  rw [fillTube_up1']
  have e1 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_neg_one φ))) htyped
  have e2 := HasTy0.ieq hS (Φ' := (cof Φ (.or φ (.neg .one))).shift) (τ1 := sk (.and .one (.var 0)) 1)
    (τ2 := sk (.var 0) 1) hu (sk_scoped ⟨trivial, hv0⟩ (by omega)) (sk_scoped hv0 (by omega))
    (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
      (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
    (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
      (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
    (ieq_sk (I_eq_and_one_l _) 1) (by rw [ctxI_sk1, ctxI_sk1])
    (by rw [ctxI_sk1]; exact (wf_of_ty hu).restrict hXs hXe)
  rw [ctxI_sk1, dshift_sk, subst_add1, sk_var1] at e2
  exact EqTm0.trans e1 e2

/-- The first components of a composition in a Σ-type. -/
theorem hcomp_sigma_parts (hS : SigClosed S) {Ψ Φ Γ A B φ u a T}
    (h : HasTy0 S Ψ Φ Γ (hcomp (sigma A B) φ u a) T) :
    HasTy0 S Ψ Φ Γ (hcomp A φ (fst u) (fst a)) A ∧
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (hfill A φ (fst u) (fst a)) A.dshift ∧
    HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (fst u) A.dshift ∧
    EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (hfill A φ (fst u) (fst a)) (fst u) A.dshift ∧
    EqTm0 S Ψ Φ Γ ((hfill A φ (fst u) (fst a)).dinst .one) (hcomp A φ (fst u) (fst a)) A := by
  obtain ⟨l, ⟨hsig, hφ, hu, ha, hside⟩, -⟩ := gen_hcomp h rfl
  have hA := HasTy0.sigmaDom hS hsig
  have hu' := HasTy0.fst hu
  have ha' := HasTy0.fst ha
  have hside' := EqTm0.fst hside
  have F := hfill_typed hS hA hφ hu' ha' hside'
  exact ⟨HasTy0.hcomp hA hφ hu' ha' hside', F.1, hu', F.2.2.2, F.2.2.1⟩

/-- Congruence of fillers. -/
theorem hfill_cong (hW : WfSig S) {Ψ : Nat} {A A' v v' v0 v0' : Tm} {φ φ' : I}
    (h : HasTy0 S (Ψ + 1) .one [] (hfill A φ v v0) A.dshift)
    (h' : HasTy0 S (Ψ + 1) .one [] (hfill A' φ' v' v0') A.dshift)
    (hAA : A = A' ∨ ∃ l, EqTm0 S Ψ .one [] A A' (univ l))
    (huu : EqTm0 S (Ψ + 1) (cof .one φ).shift [] v v' A.dshift) (hv0 : EqTm0 S Ψ .one [] v0 v0' A)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) :
    EqTm0 S (Ψ + 1) .one [] (hfill A φ v v0) (hfill A' φ' v' v0') A.dshift := by
  have hS := sigClosed_of_wfSig hW
  have ht := fillTube_eq hW h h' hAA huu hv0 h12
  obtain ⟨l1, ⟨hA1, -, -, -, -⟩, -⟩ := gen_hcomp h rfl
  obtain ⟨l, eA⟩ : ∃ l, EqTm0 S (Ψ + 1) .one [] A.dshift A'.dshift (univ l) := by
    rcases hAA with rfl | ⟨l, e⟩
    · exact ⟨l1, EqTm0.refl hA1⟩
    · exact ⟨l, EqTm0.restrict (Φ' := .one) trivial (ent_one _) (EqTm0.dwk hS e)⟩
  have hb := EqTm0.restrict (Φ' := .one) trivial (ent_one _) (EqTm0.dwk hS hv0)
  rw [hfill_eq] at h h' ⊢
  exact EqTm0.hcomp h h' eA (ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _)) (ent_or_right _ _))
    (ent_or_elim (ent_trans (ent_shift h21) (ent_or_left _ _)) (ent_or_right _ _)) ht hb

end KubusCore.Meta

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' : ℕ}

theorem isub_bindOr {k3 : ℕ} (X : Tm) (x : I) (hx : x.Scoped k3) (τ : ISub k3 k') :
    (X.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).isub (ISub.cons x hx τ).up =
      X.isub (ISub.cons (.or x.shift (.var 0)) ⟨KubusCore.I.scoped_shift hx, (show (0 : ℕ) < k3 + 1 by omega)⟩
        τ.up.tail) := by
  simp only [Tm.dsubst, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | i
  · rfl
  · rfl

/-- The tube of a heterogeneous composition at a point. -/
theorem compTube_pt (C u : Tm) {k3 : ℕ} (σ : ISub k3 k) (r : I) (hr : r.Scoped k3) :
    ((Tm.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u).isub σ.up).dinst r =
      .transp (C.isub (ISub.cons (.or r.shift (.var 0)) ⟨KubusCore.I.scoped_shift hr, (show (0 : ℕ) < k3 + 1 by omega)⟩
        σ.up.tail)) r ((u.isub σ.up).dinst r) := by
  rw [isub_up_dinst _ σ r hr]
  show Tm.transp ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).isub (ISub.cons r hr σ).up) r
    (u.isub (ISub.cons r hr σ)) = _
  rw [isub_bindOr, isub_up_dinst _ σ r hr]

theorem comp_isub (C : Tm) (ψ : I) (u u0 : Tm) (σ : ISub k' k) :
    (Tm.comp C ψ u u0).isub σ = Tm.comp (C.isub σ.up) (ψ.subst σ.τ) (u.isub σ.up) (u0.isub σ) :=
  comp_substI C ψ u u0 σ.τ

variable (hW : WfSig S)
include hW

/-- Heterogeneous composition along related lines relates related tubes and bases. -/
theorem comp2 {C C' u u' u0 u0' : Tm} {ψ ψ' : I} (hLR : LineRob S k C C') (hLRL : LineRob S k C C)
    (hKT : ∀ k3 (Θ : ISub (k3 + 1) (k + 1)) X', RT2 S (k3 + 1) (C.isub Θ) X' → KanT2 S k3 (C.isub Θ) X')
    (hKH : ∀ X', RT2 S k (C.dinst .one) X' → KanH2 S k (C.dinst .one) X')
    (hty : HasTy S k .one [] (Tm.comp C ψ u u0) (C.dinst .one))
    (hty' : HasTy S k .one [] (Tm.comp C' ψ' u' u0') (C.dinst .one))
    (heq : EqTm S k .one [] (Tm.comp C ψ u u0) (Tm.comp C' ψ' u' u0') (C.dinst .one))
    (hteq : EqTm S (k + 1) (cof .one ψ).shift [] u u' C)
    (h12 : I.Entails ψ ψ') (h21 : I.Entails ψ' ψ)
    (htube : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons r hr σ)) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r'))
    (hu0 : RE2 S k (C.dinst .zero) u0 u0')
    (hbd : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) ((u.isub σ.up).dinst .zero) (u0'.isub σ))
    (hbd' : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) (ψ.subst σ.τ)).holds →
      RE2 S k3 (C.isub (ISub.cons .zero trivial σ)) (u0.isub σ) ((u'.isub σ.up).dinst .zero)) :
    RE2 S k (C.dinst .one) (Tm.comp C ψ u u0) (Tm.comp C' ψ' u' u0') := by
  have hS := sigClosed_of_wfSig hW
  have hm := spec_to_minimal hW hty
  have hm' := spec_to_minimal hW hty'
  rw [comp_eq] at hm hm'
  obtain ⟨l1, ⟨-, hψs, -, hb, -⟩, -⟩ := gen_hcomp hm rfl
  obtain ⟨l2, ⟨-, hψs', -, hb', -⟩, -⟩ := gen_hcomp hm' rfl
  obtain ⟨lC, ⟨hC, -, -, -⟩, -⟩ := gen_transpF hb rfl
  obtain ⟨lC', ⟨hC', -, -, -⟩, -⟩ := gen_transpF hb' rfl
  have hCs : HasTy S (k + 1) .one [] C (.univ lC) := minimal_to_spec hC
  have hCs' : HasTy S (k + 1) .one [] C' (.univ lC') := minimal_to_spec hC'
  have hCc : C.closedB 0 (k + 1) = true := closed_of_ty hW hCs
  have hCc' : C'.closedB 0 (k + 1) = true := closed_of_ty hW hCs'
  have eC : C.isub (ISub.id (k + 1)) = C := isub_id_of_closed hCc
  have eC' : C'.isub (ISub.id (k + 1)) = C' := isub_id_of_closed hCc'
  have hXD : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (C.isub σ)) := fun k3 σ =>
    tyCode_of_univ hW (HasTy.isubS hW hCs σ)
  have hRR : ∀ k3 (σ : ISub k3 (k + 1)), RT2 S k3 (C.isub σ) (C.isub σ) := by
    intro k3 σ
    have h0 := hLRL (k + 1) (ISub.id k).up.tail (.var 0) (.var 0) (show 0 < k + 1 by omega)
      (show 0 < k + 1 by omega) (I_eq_refl _)
    rw [ISub.cons_var0_up_tail, isub_up_id_of_closed hCc] at h0
    have := RT2.isub hW (by have := hXD (k + 1) (ISub.id k).up; rwa [isub_up_id_of_closed hCc] at this) h0 σ
    exact this
  have cohD : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((C.isub σ1).isub θ) (C.isub σ2) := by
    intro k1 σ1 k2 θ σ2 h; rw [Tm.isub_isub, h]; exact hRR k2 σ2
  have hCC : RT2 S (k + 1) C C' := by
    have h0 := hLR (k + 1) (ISub.id k).up.tail (.var 0) (.var 0) (show 0 < k + 1 by omega)
      (show 0 < k + 1 by omega) (I_eq_refl _)
    rwa [ISub.cons_var0_up_tail, isub_up_id_of_closed hCc, isub_up_id_of_closed hCc'] at h0
  have hXC : TyCode (k + 1) (semK S (k + 1) C) := by have := hXD (k + 1) (ISub.id (k + 1)); rwa [eC] at this
  have hCC' : RT2 S (k + 1) C' C' := RT2.trans hW (RT2.tyCode_r hW hCC hXC) (RT2.symm hW hXC hCC) hCC
  have cohD' : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((C'.isub σ1).isub θ) (C'.isub σ2) := by
    intro k1 σ1 k2 θ σ2 h; rw [Tm.isub_isub, h]
    exact RT2.isub hW (RT2.tyCode_r hW hCC hXC) hCC' σ2
  have tyB : ∀ {k3 : ℕ} {X Z : Tm}, RT2 S k3 X Z → TyEq S k3 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the transports along restrictions of the lines
  have lk : ∀ k3 (σ : ISub k3 k) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
      KanT2 S k3 (C.isub (ISub.cons y hy σ.up.tail)) (C'.isub (ISub.cons y' hy' σ.up.tail)) ∧
      LineRob S k3 (C.isub (ISub.cons y hy σ.up.tail)) (C'.isub (ISub.cons y' hy' σ.up.tail)) ∧
      (∀ (e : I) (he : e.Scoped k3), RT2 S k3 ((C.isub (ISub.cons y hy σ.up.tail)).dinst e)
        (C.isub (ISub.cons (y.subst (ISub.cons e he (ISub.id k3)).τ)
          (I.scoped_subst hy (ISub.cons e he (ISub.id k3)).sc) σ))) ∧
      RT2 S (k3 + 1) (C.isub (ISub.cons y hy σ.up.tail)) (C'.isub (ISub.cons y' hy' σ.up.tail)) := by
    intro k3 σ y y' hy hy' hE
    have L := lineKan_of hW (fun k3 σ => C.isub σ) (fun k3 σ => C'.isub σ) hXD cohD cohD' hLR
      (fun k1 σ1 k2 ρ' X' h => by
        simp only [Tm.isub_isub] at h ⊢; exact hKT k2 (σ1.comp ρ') X' h)
      (k + 1) (k + 1) k3 (ISub.id (k + 1)) (ISub.id (k + 1)) (ISub.cons y hy σ.up.tail) (ISub.cons y' hy' σ.up.tail)
      σ y y' hy hy' hE (ISub.id_comp _) (ISub.id_comp _)
    simp only [eC, eC'] at L
    exact ⟨L.1, L.2.1, L.2.2.1, L.2.2.2.1⟩
  have LC : ∀ k3 (σ : ISub k3 k) (y : I) (hy : y.Scoped (k3 + 1)) (χ : I) (hχ : χ.Scoped k3),
      (∀ k4 (τ2 : ISub k4 k3) (z : I) (hz : z.Scoped k4), I.Entails .one (χ.subst τ2.τ) →
        RT2 S k4 (C.isub (ISub.cons (y.subst (ISub.cons z hz τ2).τ) (I.scoped_subst hy (ISub.cons z hz τ2).sc)
          (σ.comp τ2))) (C.isub (ISub.cons (y.subst (ISub.cons .zero trivial τ2).τ)
          (I.scoped_subst hy (ISub.cons .zero trivial τ2).sc) (σ.comp τ2)))) →
      LineConst S k3 (C.isub (ISub.cons y hy σ.up.tail)) χ := by
    intro k3 σ y hy χ hχ hmid
    have L := lineConst_of hW (fun k3 σ => C.isub σ) hXD cohD (k + 1) k3 σ (ISub.id (k + 1))
      (ISub.cons y hy σ.up.tail) y hy (ISub.id_comp _) χ hχ hmid
    simpa only [eC] using L
  have LC0 : ∀ k3 (L : Tm), LineConst S k3 L .zero := by
    intro k3 L k4 τ2 z hz hh
    exact absurd ((holds_iff_entails (show (I.zero.subst τ2.τ).Scoped k4 from trivial)).1 hh)
      (show ¬ I.Entails .one .zero by decide)
  have hC1 : RT2 S k (C.dinst .one) (C'.dinst .one) := by
    have := RT2.isub hW hXC hCC (ISub.cons .one trivial (ISub.id k))
    rwa [isub_cons_id_of_closed hCc, isub_cons_id_of_closed hCc'] at this
  obtain ⟨lq, hCCe⟩ : ∃ l, EqTm0 S (k + 1) I.one.shift [] C C' (.univ l) := by
    rcases tyB hCC with e | ⟨l, e⟩
    · subst e; exact ⟨lC, EqTm0.refl hC⟩
    · exact ⟨l, spec_to_minimal_eq hW e⟩
  have htE := minimal_to_spec_eq (compTube_eq hS (spec_to_minimal hW hty) (spec_to_minimal hW hty') hCCe h12
    (spec_to_minimal_eq hW hteq))
  have hv : ∀ {k3 : ℕ}, (I.var 0).Scoped (k3 + 1) := fun {k3} => show 0 < k3 + 1 by omega
  have eT : ∀ {k3 : ℕ} (σ : ISub k3 k), (C.dinst .one).isub σ = C.isub (ISub.cons .one trivial σ) := by
    intro k3 σ; rw [isub_dinst]; exact isub_up_dinst C σ .one trivial
  have hσ : ∀ {k3 : ℕ} (σ : ISub k3 k), HasTy S k3 .one [] (.hcomp ((C.dinst .one).isub σ) (ψ.subst σ.τ)
      ((Tm.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u).isub σ.up)
      ((Tm.transp C .zero u0).isub σ)) ((C.dinst .one).isub σ) := fun σ => HasTy.isubS hW hty σ
  have hσ' : ∀ {k3 : ℕ} (σ : ISub k3 k), HasTy S k3 .one [] (.hcomp ((C'.dinst .one).isub σ) (ψ'.subst σ.τ)
      ((Tm.transp (C'.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u').isub σ.up)
      ((Tm.transp C' .zero u0').isub σ)) ((C.dinst .one).isub σ) := fun σ => HasTy.isubS hW hty' σ
  have hsy : ∀ {k3 : ℕ} (x : I), x.Scoped k3 → (I.or x.shift (.var 0)).Scoped (k3 + 1) :=
    fun x hx => ⟨KubusCore.I.scoped_shift hx, show 0 < _ by omega⟩
  -- the end of a tube line, as a type
  have endT : ∀ {k3 : ℕ} (σ : ISub k3 k) (y : I) (hy : y.Scoped (k3 + 1)),
      I.Eq (y.subst (ISub.cons .one trivial (ISub.id k3)).τ) .one →
      RT2 S k3 ((C.isub (ISub.cons y hy σ.up.tail)).dinst .one) ((C.dinst .one).isub σ) := by
    intro k3 σ y hy e
    have e1 := (lk k3 σ y y hy hy (I_eq_refl _)).2.2.1 .one trivial
    have m1 := hLRL k3 σ _ .one (I.scoped_subst hy (ISub.cons .one trivial (ISub.id k3)).sc) trivial e
    rw [eT]
    exact RT2.trans hW (RT2.tyCode_l hW e1 (hXD _ _)) e1 m1
  refine hKH _ hC1 ψ ψ' (Tm.transp (C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u)
    (Tm.transp (C'.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))) (.var 0) u') (Tm.transp C .zero u0)
    (Tm.transp C' .zero u0') hty hty' heq htE h12 h21 ?_ ?_ ?_ ?_
  · -- the tubes
    intro k3 σ r r' hr hr' hE hh
    have hh' := entails_holds (ent_subst h12 σ.τ) hh
    have t1 := hcomp_tube_typed hW (hσ σ) r hr hh
    have t2 := hcomp_tube_typed hW (hσ' σ) r' hr' hh'
    rw [compTube_pt C u σ r hr] at t1
    rw [compTube_pt C' u' σ r' hr'] at t2
    rw [compTube_pt C u σ r hr, compTube_pt C' u' σ r' hr']
    have L := lk k3 σ _ _ (hsy r hr) (hsy r' hr') (ieq_or_congr (ieq_shift hE) (I_eq_refl _))
    have t1x : HasTy S k3 .one [] (Tm.transp (C.isub (ISub.cons (.or r.shift (.var 0)) (hsy r hr) σ.up.tail)) r ((u.isub σ.up).dinst r)) ((C.dinst .one).isub σ) := t1
    have ty1 := transp_canon_typed hW t1x
    have t2x : HasTy S k3 .one [] (Tm.transp (C'.isub (ISub.cons (.or r'.shift (.var 0)) (hsy r' hr') σ.up.tail)) r'
        ((u'.isub σ.up).dinst r')) ((C'.dinst .one).isub σ) := t2
    have ty2 := (transp_canon_typed hW t2x).tyConv (TyEq.symm (tyEq_dinst hW (tyB L.2.2.2) (r := .one) trivial))
    have e0 := L.2.2.1 .zero trivial
    have m0 := hLRL k3 σ _ r (I.scoped_subst (hsy r hr) (ISub.cons .zero trivial (ISub.id k3)).sc) hr (show I.Eq (I.or (r.shift.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero) r by
      rw [I_shift_cons, I_subst_id hr]; exact I_eq_or_zero_r r)
    have hbase := RE2.conv' hW (RT2.trans hW (RT2.tyCode_l hW e0 (hXD _ _)) e0 m0) (htube k3 σ r r' hr hr' hE hh)
      (RT2.tyCode_l hW e0 (hXD _ _))
    have heqw := eqTm_transp_of hW ty1 ty2 (tyB L.2.2.2) (eq_ent hE) (eq_ent (I_eq_symm hE)) (RE2.typed hbase).2.2
    have LCr := LC k3 σ _ (hsy r hr) r hr (fun k4 τ2 z hz he => by
      have e1 : I.Eq (r.subst τ2.τ) .one :=
        ieq_one_of_holds (I.scoped_subst hr τ2.sc) (entails_holds he (ρ := idEnv k4) (by rw [ival_one]; rfl))
      have ez : I.Eq ((I.or r.shift (.var 0)).subst (ISub.cons z hz τ2).τ) .one := by
        show I.Eq (I.or (r.shift.subst (ISub.cons z hz τ2).τ) z) _
        rw [I_shift_cons]; exact ieq_or_one_left _ e1
      have e0 : I.Eq ((I.or r.shift (.var 0)).subst (ISub.cons .zero trivial τ2).τ) .one := by
        show I.Eq (I.or (r.shift.subst (ISub.cons .zero trivial τ2).τ) .zero) _
        rw [I_shift_cons]; exact ieq_or_one_left _ e1
      exact hLRL k4 (σ.comp τ2) _ _ _ _ (I_eq_trans ez (I_eq_symm e0)))
    have R := L.1 L.2.1 r r' _ _ LCr ty1 ty2 heqw (eq_ent hE) (eq_ent (I_eq_symm hE)) hbase
    refine RE2.conv hW (endT σ _ _ ?_) R
    show I.Eq (I.or (r.shift.subst (ISub.cons .one trivial (ISub.id k3)).τ) .one) .one
    exact I_eq_or_one_r _
  · -- the bases
    have L := lk k (ISub.id k) (.var 0) (.var 0) hv hv (I_eq_refl _)
    rw [ISub.cons_var0_up_tail, isub_up_id_of_closed hCc, isub_up_id_of_closed hCc'] at L
    have tyb := minimal_to_spec hb
    have tyb' := (minimal_to_spec hb').tyConv (TyEq.symm (tyEq_dinst hW (tyB hCC) (r := .one) trivial))
    have eqb := eqTm_transp_of hW tyb tyb' (tyB hCC) (ent_refl _) (ent_refl _) (RE2.typed hu0).2.2
    exact L.1 L.2.1 .zero .zero u0 u0' (LC0 _ _) tyb tyb' eqb (ent_refl _) (ent_refl _) hu0
  · -- the boundary, on the left
    intro k3 σ hh
    have t1 := hcomp_tube_typed hW (hσ σ) .zero trivial hh
    rw [compTube_pt C u σ .zero trivial] at t1
    rw [compTube_pt C u σ .zero trivial]
    have eσ : C'.isub σ.up = C'.isub (ISub.cons (.var 0) hv σ.up.tail) := by rw [ISub.cons_var0_up_tail]
    show RE2 S k3 _ _ (Tm.transp (C'.isub σ.up) .zero (u0'.isub σ))
    rw [eσ]
    have L := lk k3 σ _ (.var 0) (hsy .zero trivial) hv (I_eq_or_zero_l _)
    have t1x : HasTy S k3 .one [] (Tm.transp (C.isub (ISub.cons (.or I.zero.shift (.var 0)) (hsy .zero trivial)
        σ.up.tail)) .zero ((u.isub σ.up).dinst .zero)) ((C.dinst .one).isub σ) := t1
    have ty1 := transp_canon_typed hW t1x
    have t2 : HasTy S k3 .one [] (Tm.transp (C'.isub σ.up) .zero (u0'.isub σ)) ((C'.dinst .one).isub σ) :=
      HasTy.isubS hW (minimal_to_spec hb') σ
    rw [eσ] at t2
    have ty2 := (transp_canon_typed hW t2).tyConv (TyEq.symm (tyEq_dinst hW (tyB L.2.2.2) (r := .one) trivial))
    have e0 := L.2.2.1 .zero trivial
    have m0 := hLRL k3 σ _ .zero (I.scoped_subst (hsy .zero trivial) (ISub.cons .zero trivial (ISub.id k3)).sc) trivial
      (I_eq_or_zero_r .zero)
    have hbase := RE2.conv' hW (RT2.trans hW (RT2.tyCode_l hW e0 (hXD _ _)) e0 m0) (hbd k3 σ hh)
      (RT2.tyCode_l hW e0 (hXD _ _))
    have heqw := eqTm_transp_of hW ty1 ty2 (tyB L.2.2.2) (ent_refl _) (ent_refl _) (RE2.typed hbase).2.2
    have R := L.1 L.2.1 .zero .zero _ _ (LC0 _ _) ty1 ty2 heqw (ent_refl _) (ent_refl _) hbase
    exact RE2.conv hW (endT σ _ (hsy .zero trivial) (I_eq_or_one_r .zero)) R
  · -- the boundary, on the right
    intro k3 σ hh
    have hh' := entails_holds (ent_subst h12 σ.τ) hh
    have t2 := hcomp_tube_typed hW (hσ' σ) .zero trivial hh'
    rw [compTube_pt C' u' σ .zero trivial] at t2
    rw [compTube_pt C' u' σ .zero trivial]
    have eσ : C.isub σ.up = C.isub (ISub.cons (.var 0) hv σ.up.tail) := by rw [ISub.cons_var0_up_tail]
    show RE2 S k3 _ (Tm.transp (C.isub σ.up) .zero (u0.isub σ)) _
    rw [eσ]
    have L := lk k3 σ (.var 0) _ hv (hsy .zero trivial) (I_eq_symm (I_eq_or_zero_l _))
    have t1 : HasTy S k3 .one [] (Tm.transp (C.isub σ.up) .zero (u0.isub σ)) ((C.dinst .one).isub σ) :=
      HasTy.isubS hW (minimal_to_spec hb) σ
    rw [eσ] at t1
    have ty1 := transp_canon_typed hW t1
    have t2x : HasTy S k3 .one [] (Tm.transp (C'.isub (ISub.cons (.or I.zero.shift (.var 0)) (hsy .zero trivial)
        σ.up.tail)) .zero ((u'.isub σ.up).dinst .zero)) ((C'.dinst .one).isub σ) := t2
    have ty2 := (transp_canon_typed hW t2x).tyConv (TyEq.symm (tyEq_dinst hW (tyB L.2.2.2) (r := .one) trivial))
    have e0 := L.2.2.1 .zero trivial
    have m0 := hLRL k3 σ _ .zero (I.scoped_subst hv (ISub.cons .zero trivial (ISub.id k3)).sc) trivial (I_eq_refl _)
    have hbase := RE2.conv' hW (RT2.trans hW (RT2.tyCode_l hW e0 (hXD _ _)) e0 m0) (hbd' k3 σ hh)
      (RT2.tyCode_l hW e0 (hXD _ _))
    have heqw := eqTm_transp_of hW ty1 ty2 (tyB L.2.2.2) (ent_refl _) (ent_refl _) (RE2.typed hbase).2.2
    have R := L.1 L.2.1 .zero .zero _ _ (LC0 _ _) ty1 ty2 heqw (ent_refl _) (ent_refl _) hbase
    exact RE2.conv hW (endT σ (.var 0) hv (I_eq_refl _)) R

omit hW in
theorem hfill_isub_cons (A : Tm) (φ : I) (v v0 : Tm) {k3 : ℕ} (τ : ISub k3 k) (r : I) (hr : r.Scoped k3) :
    (Tm.hfill A φ v v0).isub (ISub.cons r hr τ) = .hcomp (A.isub τ) (.or (φ.subst τ.τ) (.neg r))
      ((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons r hr τ).up) (v0.isub τ) := by
  show Tm.hcomp (A.dshift.isub (ISub.cons r hr τ)) (.or (φ.shift.subst (ISub.cons r hr τ).τ) (.neg r))
    ((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons r hr τ).up) (v0.dshift.isub (ISub.cons r hr τ)) = _
  rw [dshift_isub_cons, dshift_isub_cons, I_shift_cons]

/-- A filler at a point where the face of its composition holds. -/
theorem hfill_face_pt {A v v0 : Tm} {φ : I} (hφs : φ.Scoped k) (hX : TyCode k (semK S k A)) (hAA : RT2 S k A A)
    (htyF : HasTy S (k + 1) .one [] (Tm.hfill A φ v v0) A.dshift) (htube : Tube2 S k A φ v v)
    {k3 : ℕ} (τ : ISub k3 k) (r : I) (hr : r.Scoped k3) (hh : (ival (idEnv k3) (φ.subst τ.τ)).holds) :
    RE2 S k3 (A.isub τ) ((Tm.hfill A φ v v0).isub (ISub.cons r hr τ)) ((v.isub τ.up).dinst r) := by
  have hAτ := RT2.isub hW hX hAA τ
  have hf : I.Entails .one (φ.subst τ.τ) := (holds_iff_entails (I.scoped_subst hφs τ.sc)).1 hh
  have hH := HasTy.isubS hW htyF (ISub.cons r hr τ)
  rw [hfill_isub_cons, dshift_isub_cons] at hH
  rw [hfill_isub_cons]
  have hor : I.Entails .one (.or (φ.subst τ.τ) (.neg r)) := ent_trans hf (ent_or_left _ _)
  have s1 := stable_hcompFace hW hor hH
  have hsp := hcomp_tube_typed' hW hH .one trivial
    ((holds_iff_entails (show (I.or (φ.subst τ.τ) (.neg r)).Scoped k3 from ⟨I.scoped_subst hφs τ.sc, hr⟩)).2 hor)
  rw [fillTube_isub_dinst, ISub.tail_cons] at hsp s1
  have s2 := stable_splitL hW hf hsp
  have base := htube k3 τ (.and r .one) r ⟨hr, trivial⟩ hr (ieq_and_one_right r) hh
  have e1 := RE2.expandL hW hAτ hsp (RE2.typed base).2.1 s2 base
  exact RE2.expandL hW hAτ hH (RE2.typed base).2.1 s1 e1

/-- A filler at the start of its line. -/
theorem hfill_zero_pt {A v v0 : Tm} {φ : I} (hφs : φ.Scoped k) (hX : TyCode k (semK S k A)) (hAA : RT2 S k A A)
    (htyF : HasTy S (k + 1) .one [] (Tm.hfill A φ v v0) A.dshift) (htube : Tube2 S k A φ v v)
    (hv0 : RE2 S k A v0 v0)
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((v.isub σ.up).dinst .zero) (v0.isub σ))
    {k3 : ℕ} (τ : ISub k3 k) :
    RE2 S k3 (A.isub τ) ((Tm.hfill A φ v v0).isub (ISub.cons .zero trivial τ)) (v0.isub τ) := by
  have hAτ := RT2.isub hW hX hAA τ
  have hH := HasTy.isubS hW htyF (ISub.cons .zero trivial τ)
  rw [hfill_isub_cons, dshift_isub_cons] at hH
  rw [hfill_isub_cons]
  have hor : I.Entails .one (.or (φ.subst τ.τ) (.neg .zero)) :=
    ent_trans (show I.Entails .one (.neg .zero) by decide) (ent_or_right _ _)
  have s1 := stable_hcompFace hW hor hH
  have hsp := hcomp_tube_typed' hW hH .one trivial
    ((holds_iff_entails (show (I.or (φ.subst τ.τ) (.neg .zero)).Scoped k3 from ⟨I.scoped_subst hφs τ.sc, trivial⟩)).2 hor)
  rw [fillTube_isub_dinst, ISub.tail_cons] at hsp s1
  have hv0τ := RE2.isub hW hv0 τ
  have e1 := RE2_split_l hW (I.scoped_subst hφs τ.sc) (show (I.neg I.zero).Scoped k3 from trivial) hor hAτ hsp
    (RE2.typed hv0τ).1 (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_)
  · exact RE2.expandL hW hAτ hH (RE2.typed hv0τ).1 s1 e1
  · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
    have hh4 : (ival (idEnv k4) (φ.subst (τ.comp σ4).τ)).holds :=
      (holds_iff_entails (I.scoped_subst hφs (τ.comp σ4).sc)).2 (ent_comp_inv h)
    have hA4 := RT2.isub hW hX hAA (τ.comp σ4)
    exact RE2.trans hW hA4 (htube k4 (τ.comp σ4) _ .zero (I.scoped_subst (show (I.and I.zero I.one).Scoped k3 from
      ⟨trivial, trivial⟩) σ4.sc) trivial (fun _ => rfl) hh4) (hbd k4 _ hh4)
  · rw [Tm.isub_isub, Tm.isub_isub]
    exact RE2.isub hW hv0 _

omit hW in
theorem up_inst0_one_isub (X : Tm) {k3 : ℕ} (τ : ISub k3 k) :
    (X.subst Tm.var (I.up (I.inst0 .one))).isub τ.up = X.isub (ISub.cons .one trivial τ).up := by
  simp only [Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) X
  rcases i with _ | _ | i
  · rfl
  · rfl
  · show ((I.var i).shift).subst (I.up τ.τ) = _
    rw [I_shift_subst_up]; rfl

/-- The end of a filler, against its composition. -/
theorem hfill_one_pt {A v v0 : Tm} {φ : I} (hφs : φ.Scoped k) (hX : TyCode k (semK S k A)) (hAA : RT2 S k A A)
    (hK : ∀ k3 (τ : ISub k3 k), KanH2 S k3 (A.isub τ) (A.isub τ))
    (htyH : HasTy S k .one [] (.hcomp A φ v v0) A)
    (htyF : HasTy S (k + 1) .one [] (Tm.hfill A φ v v0) A.dshift) (htube : Tube2 S k A φ v v)
    (hv0 : RE2 S k A v0 v0)
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((v.isub σ.up).dinst .zero) (v0.isub σ))
    {k3 : ℕ} (τ : ISub k3 k) :
    RE2 S k3 (A.isub τ) ((Tm.hfill A φ v v0).isub (ISub.cons .one trivial τ)) ((Tm.hcomp A φ v v0).isub τ) := by
  have hS := sigClosed_of_wfSig hW
  have hAτ := RT2.isub hW hX hAA τ
  obtain ⟨l0, ⟨hA0, hφ0, hu0', hv00, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW htyH) rfl
  have hH := HasTy.isubS hW htyF (ISub.cons .one trivial τ)
  rw [hfill_isub_cons, dshift_isub_cons] at hH
  have hH' := HasTy.isubS hW htyH τ
  have heq := EqTm.isubS hW (minimal_to_spec_eq (hfill_typed hS hA0 hφ0 hu0' hv00 hside).2.2.1) τ
  rw [isub_dinst] at heq
  change EqTm S k3 .one [] (((Tm.hfill A φ v v0).isub τ.up).dinst .one) _ _ at heq
  rw [isub_up_dinst _ τ .one trivial, hfill_isub_cons] at heq
  have hsc1 : (I.or φ (.neg .one)).Scoped k := ⟨hφs, trivial⟩
  have ht := EqTm.cofIsub hW hsc1 (minimal_to_spec_eq (hfill1_tube_eq hS hA0 hφ0 hu0' hv00 hside)) τ
  rw [up_inst0_one_isub, isub_dshift] at ht
  rw [hfill_isub_cons]
  have hholds : ∀ {k4 : ℕ} (σ2 : ISub k4 k3), (ival (idEnv k4) ((I.or (φ.subst τ.τ) (.neg .one)).subst σ2.τ)).holds →
      (ival (idEnv k4) (φ.subst (τ.comp σ2).τ)).holds ∧ I.Entails .one (φ.subst (τ.comp σ2).τ) := by
    intro k4 σ2 hh
    have h1 := (holds_iff_entails (I.scoped_subst (show (I.or (φ.subst τ.τ) (.neg .one)).Scoped k3 from
      ⟨I.scoped_subst hφs τ.sc, trivial⟩) σ2.sc)).1 hh
    have h2 : I.Entails .one (φ.subst (τ.comp σ2).τ) := by
      rw [I_subst_comp]; exact ent_trans h1 (ent_neg_one _)
    exact ⟨(holds_iff_entails (I.scoped_subst hφs (τ.comp σ2).sc)).2 h2, h2⟩
  have pts : ∀ {k4 : ℕ} (σ2 : ISub k4 k3) (x : I),
      (((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons .one trivial τ).up).isub σ2.up).dinst x =
        .split (φ.subst (τ.comp σ2).τ) ((v.isub (τ.comp σ2).up).dinst (.and .one x)) (.neg .one) (v0.isub (τ.comp σ2)) := by
    intro k4 σ2 x
    rw [Tm.isub_isub, ← ISub.up_comp, ISub.cons_comp, fillTube_isub_dinst, ISub.tail_cons]; rfl
  have nen1 : ∀ {k4 k5 : ℕ} (σ4 : ISub k5 k4), ¬ I.Entails .one ((I.neg I.one).subst σ4.τ) :=
    fun σ4 => by show ¬ I.Entails .one (I.neg .one); decide
  refine hK k3 τ _ _ _ _ _ _ hH hH' heq ht (ent_neg_one _) (ent_or_left _ _) (fun k4 σ2 x x' hx hx' hEx hh => ?_)
    (RE2.isub hW hv0 τ) (fun k4 σ2 hh => ?_) (fun k4 σ2 hh => ?_)
  · have hA4 := RT2.isub hW hX hAA (τ.comp σ2)
    obtain ⟨hh4, hf4⟩ := hholds σ2 hh
    have hsp : HasTy S k4 .one [] ((((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons .one trivial τ).up).isub
        σ2.up).dinst x) ((A.isub τ).isub σ2) := hcomp_tube_typed' hW (HasTy.isubS hW hH σ2) x hx hh
    rw [pts, Tm.isub_isub] at hsp
    change RE2 S k4 _ _ (((v.isub τ.up).isub σ2.up).dinst x')
    rw [pts, Tm.isub_isub A, Tm.isub_isub v, ← ISub.up_comp]
    have r := htube k4 (τ.comp σ2) x x' hx hx' hEx hh4
    refine RE2_split_l hW (I.scoped_subst hφs (τ.comp σ2).sc) (show (I.neg I.one).Scoped k4 from trivial)
      (ent_trans hf4 (ent_or_left _ _)) hA4 hsp (RE2.typed r).2.1 (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, dinst_up_isub, Tm.isub_isub]
      exact htube k5 _ _ _ (I.scoped_subst (show (I.and I.one x).Scoped k4 from ⟨trivial, hx⟩) σ4.sc)
        (I.scoped_subst hx' σ4.sc) (I_eq_subst (I_eq_trans (I_eq_and_one_l x) hEx) _)
        ((holds_iff_entails (I.scoped_subst hφs ((τ.comp σ2).comp σ4).sc)).2 (ent_comp_inv h))
    · exact absurd h (nen1 σ4)
  · have hA4 := RT2.isub hW hX hAA (τ.comp σ2)
    obtain ⟨hh4, hf4⟩ := hholds σ2 hh
    have hsp : HasTy S k4 .one [] ((((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons .one trivial τ).up).isub
        σ2.up).dinst .zero) ((A.isub τ).isub σ2) := hcomp_tube_typed' hW (HasTy.isubS hW hH σ2) .zero trivial hh
    rw [pts, Tm.isub_isub] at hsp
    change RE2 S k4 _ _ ((v0.isub τ).isub σ2)
    rw [pts, Tm.isub_isub A, Tm.isub_isub v0]
    have r := hbd k4 (τ.comp σ2) hh4
    refine RE2_split_l hW (I.scoped_subst hφs (τ.comp σ2).sc) (show (I.neg I.one).Scoped k4 from trivial)
      (ent_trans hf4 (ent_or_left _ _)) hA4 hsp (RE2.typed r).2.1 (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      have hh5 := (holds_iff_entails (I.scoped_subst hφs ((τ.comp σ2).comp σ4).sc)).2 (ent_comp_inv h)
      exact RE2.trans hW (RT2.isub hW hX hAA _) (htube k5 _ _ .zero
        (I.scoped_subst (show (I.and I.one I.zero).Scoped k4 from ⟨trivial, trivial⟩) σ4.sc) trivial
        (fun _ => rfl) hh5) (hbd k5 _ hh5)
    · exact absurd h (nen1 σ4)
  · obtain ⟨hh4, -⟩ := hholds σ2 hh
    change RE2 S k4 _ ((v0.isub τ).isub σ2) (((v.isub τ.up).isub σ2.up).dinst .zero)
    rw [Tm.isub_isub A, Tm.isub_isub v0, Tm.isub_isub v, ← ISub.up_comp]
    exact RE2.symm hW (RT2.isub hW hX hAA _) (hbd k4 (τ.comp σ2) hh4)

/-- The tube of a heterogeneous composition is typed at the points of its line where its face holds. -/
theorem comp_tube_typed {C u u0 X : Tm} {ψ : I} (h : HasTy S k .one [] (Tm.comp C ψ u u0) X) {k3 : ℕ} (σ : ISub k3 k)
    (x : I) (hx : x.Scoped k3) (hh : (ival (idEnv k3) (ψ.subst σ.τ)).holds) :
    HasTy S k3 .one [] ((u.isub σ.up).dinst x) (C.isub (ISub.cons x hx σ)) := by
  have hS := sigClosed_of_wfSig hW
  have hm := spec_to_minimal hW h
  rw [comp_eq] at hm
  obtain ⟨l1, ⟨-, hψ, htube, hb, -⟩, -⟩ := gen_hcomp hm rfl
  obtain ⟨lC, ⟨hC, -, -, -⟩, -⟩ := gen_transpF hb rfl
  obtain ⟨lL, ⟨-, -, -, hu⟩, -⟩ := gen_transpF htube rfl
  have h1 := HasTy0.isub hS hu (Ψ' := k3) (Φ' := .one) (τ := (ISub.cons x hx σ).τ)
    (fun i hi => (ISub.cons x hx σ).sc i hi) (ent_cof_cons hW hψ x hx σ hh) (Wf0.nil trivial)
  have h2 : HasTy S k3 .one [] ((u.isub σ.up).dinst x)
      ((((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .zero)).isub (ISub.cons x hx σ)) := by
    rw [isub_up_dinst _ σ x hx]; exact minimal_to_spec h1
  refine h2.tyConv (tyEq_ieq hW hC (τ1 := fun i => ((Tm.bind2 (.or (.var 1) (.var 0)) i).subst (I.inst0 .zero)).subst
    (ISub.cons x hx σ).τ) (τ2 := (ISub.cons x hx σ).τ) (fun i hi => ?_) (fun i hi => (ISub.cons x hx σ).sc i hi)
    (fun i hi => ?_) (by
      simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]; exact subst_congr (fun _ => rfl) (fun _ => rfl) C) rfl)
  · rcases i with _ | i
    · exact ⟨hx, trivial⟩
    · exact σ.sc i (by omega)
  · rcases i with _ | i
    · exact I_eq_or_zero_r x
    · exact I_eq_refl _

end

end Model.Whnf
