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

end

end Model.Whnf
