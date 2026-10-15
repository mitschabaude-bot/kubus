import Model.Whnf.Kan2Glue
import Model.Whnf.Kan2IPiT
import Model.Canon.KanGlueT
import Model.Whnf.NearEquiv
import Model.Whnf.Kan2Rel

/-!
# Binary Kan lemma: transport along lines of Glue types

`transp (i. Glue A [φ ↦ (T, e)]) ψ u0` computes (`transpGlueWith`) to a Glue element built from a
composition in `A`, a transport in `T` and a contraction in the fibres of `e(1)`. Related lines and
related starts give related results, piece by piece as in the unary `KanGlueT`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- The parts of a heterogeneous composition, typed. -/
theorem comp_partsS {C u u0 X : Tm} {ψ : I} (h : HasTy S k .one [] (Tm.comp C ψ u u0) X) :
    ∃ l, HasTy S (k + 1) .one [] C (.univ l) ∧ ψ.Scoped k ∧ HasTy S (k + 1) (cof .one ψ).shift [] u C ∧
      HasTy S k .one [] u0 (C.dinst .zero) := by
  have hS := sigClosed_of_wfSig hW
  have hm := spec_to_minimal hW h
  rw [comp_eq] at hm
  obtain ⟨l1, ⟨-, hψ, htube, hb, -⟩, -⟩ := gen_hcomp hm rfl
  obtain ⟨lC, ⟨hC, -, -, hu0⟩, -⟩ := gen_transpF hb rfl
  obtain ⟨lL, ⟨-, -, -, hu⟩, -⟩ := gen_transpF htube rfl
  have hXs : (cof .one ψ).shift.Scoped (k + 1) := KubusCore.I.scoped_shift ⟨trivial, hψ⟩
  have hv0 : (I.var 0).Scoped (k + 1) := show 0 < k + 1 by omega
  have e := line_ieq hS hC (k := 1) (Ψ' := k + 1) (X := (cof .one ψ).shift) (r := .or (.var 0) .zero) (r' := .var 0)
    (ent_one _) ⟨hv0, trivial⟩ hv0 (by omega) (I_eq_or_zero_r _) (by rw [ctxI_add1]; exact Wf0.nil hXs)
  rw [ctxI_add1, sk_var1] at e
  rw [L_d0] at hu
  exact ⟨lC, minimal_to_spec hC, hψ, minimal_to_spec (HasTy0.conv hu e), minimal_to_spec hu0⟩

/-- Lines related at all their points are judgmentally equal. -/
theorem eqLine_of_rob {C C' : Tm} {l l' : ℕ} (hC : HasTy S (k + 1) .one [] C (.univ l))
    (hC' : HasTy S (k + 1) .one [] C' (.univ l')) (h : LineRob S k C C') :
    EqTm S (k + 1) .one [] C C' (.univ maxLevel) := by
  have hm : HasTy S (k + 1) .one [] C (.univ maxLevel) := hC.cumulTo (lvl_of_ty hW hC) le_rfl
  have hm' : HasTy S (k + 1) .one [] C' (.univ maxLevel) := hC'.cumulTo (lvl_of_ty hW hC') le_rfl
  have hc : (cof .one .one).Scoped (k + 1) := ⟨trivial, trivial⟩
  have e := eq_of_restr hW (φ := .one) trivial (.inr rfl) (HasTy.restrict hc (ent_and_left _ _) hm)
    (HasTy.restrict hc (ent_and_left _ _) hm') fun k' σ _ => by
      have h1 := h k' σ.tail (σ.τ 0) (σ.τ 0) (σ.sc 0 (by omega)) (σ.sc 0 (by omega)) (I_eq_refl _)
      rw [ISub.cons_tail] at h1
      rw [isub_univ]
      exact eqTop hW (Comp2_ty_base h1).2.2.2.2.2 (HasTy.isubS hW hC σ)
  exact EqTm.restrict trivial (ent_and_intro (ent_refl _) (ent_refl _)) e


/-- Heterogeneous composition along related lines, from relations alone. -/
theorem comp2r {C C' u u' u0 u0' : Tm} {ψ ψ' : I} (hLR : LineRob S k C C') (hLRL : LineRob S k C C)
    (hKT : ∀ k3 (Θ : ISub (k3 + 1) (k + 1)) X', RT2 S (k3 + 1) (C.isub Θ) X' → KanT2 S k3 (C.isub Θ) X')
    (hKH : ∀ X', RT2 S k (C.dinst .one) X' → KanH2 S k (C.dinst .one) X')
    (hty : HasTy S k .one [] (Tm.comp C ψ u u0) (C.dinst .one))
    (hty' : HasTy S k .one [] (Tm.comp C' ψ' u' u0') (C.dinst .one))
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
  obtain ⟨l, hC, hψs, hu, -⟩ := comp_partsS hW hty
  obtain ⟨l', hC', -, hu', -⟩ := comp_partsS hW hty'
  have hCC := eqLine_of_rob hW hC hC' hLR
  have hc : (cof .one ψ).shift.Scoped (k + 1) := KubusCore.I.scoped_shift ⟨trivial, hψs⟩
  have hu'C : HasTy S (k + 1) (cof .one ψ).shift [] u' C :=
    (HasTy.restrict hc (ent_shift (ent_and_mono (ent_refl _) h12)) hu').conv
      (EqTm.restrict hc (ent_trans (ent_shift (ent_and_left _ _)) (ent_refl _)) hCC).symm
  have hteq := eqTube_of_rel hW hψs (HasTy.restrict hc (ent_trans (ent_shift (ent_and_left _ _)) (ent_refl _)) hC)
    hu hu'C fun k3 σ r hr hh => htube k3 σ r r hr hr (I_eq_refl _) hh
  have heq := minimal_to_spec_eq (comp_cong hS (spec_to_minimal hW hty) (spec_to_minimal hW hty')
    (spec_to_minimal_eq hW hCC) h12 h21 (spec_to_minimal_eq hW hteq) (spec_to_minimal_eq hW (RE2.typed hu0).2.2))
  exact comp2 hW hLR hLRL hKT hKH hty hty' heq hteq h12 h21 htube hu0 hbd hbd'


/-- The data of a transport along a pair of Glue lines: related bases, fibers and equivalences, Kan
bases and fibers, and a related start of the transport at the left line. -/
structure TGD2 (S : Sig) (k : ℕ) (A : Tm) (φ : I) (T e A' : Tm) (φ' : I) (T' e' : Tm) (ψ ψ' : I) (u0 u0' : Tm)
    (δ δ' : I) : Prop where
  hG : ∃ l, HasTy S (k + 1) .one [] (.glue A φ T e) (.univ l)
  hG' : ∃ l, HasTy S (k + 1) .one [] (.glue A' φ' T' e') (.univ l)
  rA : LineRob S k A A'
  rAA : LineRob S k A A
  rT : ∀ k' (σ : ISub k' (k + 1)), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T'.isub σ)
  rTT : ∀ k' (σ : ISub k' (k + 1)), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ)
  rE : ∀ k' (σ : ISub k' (k + 1)), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)
  rEL : ∀ k' (σ : ISub k' (k + 1)), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e.isub σ)
  f12 : I.Entails φ φ'
  f21 : I.Entails φ' φ
  kAR : KHRel S (k + 1) A
  kATR : KTRel S (k + 1) A
  kTR : ∀ k' (σ : ISub k' (k + 1)), (ival (idEnv k') (φ.subst σ.τ)).holds → ∀ X X', RT2 S k' (T.isub σ) X →
    RT2 S k' X X' → KanH2 S k' X X'
  kTTR : ∀ k' (Θ : ISub (k' + 1) (k + 1)), (ival (idEnv (k' + 1)) (φ.subst Θ.τ)).holds → ∀ X X',
    RT2 S (k' + 1) (T.isub Θ) X → RT2 S (k' + 1) X X' → KanT2 S k' X X'
  hδs : δ.Scoped k
  hδ1 : I.Entails δ φ.forall0
  hδ2 : I.Entails φ.forall0 δ
  hδs' : δ'.Scoped k
  hδ1' : I.Entails δ' φ'.forall0
  hδ2' : I.Entails φ'.forall0 δ'
  hty : HasTy S k .one [] (.transp (.glue A φ T e) ψ u0) ((Tm.glue A φ T e).dinst .one)
  hty' : HasTy S k .one [] (.transp (.glue A' φ' T' e') ψ' u0') ((Tm.glue A φ T e).dinst .one)
  heq : EqTm S k .one [] (.transp (.glue A φ T e) ψ u0) (.transp (.glue A' φ' T' e') ψ' u0')
    ((Tm.glue A φ T e).dinst .one)
  p12 : I.Entails ψ ψ'
  p21 : I.Entails ψ' ψ
  rG : LineRob S k (.glue A φ T e) (.glue A' φ' T' e')
  rGG : LineRob S k (.glue A φ T e) (.glue A φ T e)
  cG : LineConst S k (.glue A φ T e) ψ
  ha0 : RE2 S k ((Tm.glue A φ T e).dinst .zero) u0 u0'

  kAC : KanP2 S (k + 1) (semK S (k + 1) A)
  kTC : ∀ k' (σ : ISub k' (k + 1)), (ival (idEnv k') (φ.subst σ.τ)).holds →
    KanP2 S k' (semK S k' (T.isub σ))


theorem TGD2.isub {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') (ρ : ISub k' k) :
    TGD2 S k' (A.isub ρ.up) (φ.subst ρ.up.τ) (T.isub ρ.up) (e.isub ρ.up) (A'.isub ρ.up) (φ'.subst ρ.up.τ)
      (T'.isub ρ.up) (e'.isub ρ.up) (ψ.subst ρ.τ) (ψ'.subst ρ.τ) (u0.isub ρ) (u0'.isub ρ) (δ.subst ρ.τ)
      (δ'.subst ρ.τ) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨-, lA, hA, -⟩ := glue_data hW hG
  have hc : ∀ {k3} (σ : ISub k3 (k' + 1)), (ival (idEnv k3) ((φ.subst ρ.up.τ).subst σ.τ)).holds →
      (ival (idEnv k3) (φ.subst (ρ.up.comp σ).τ)).holds := fun σ h => by rwa [I_subst_comp]
  refine ⟨⟨l, HasTy.isubS hW hG ρ.up⟩, ⟨l', HasTy.isubS hW hG' ρ.up⟩, D.rA.isub ρ, D.rAA.isub ρ,
    fun k3 σ hh => ?_, fun k3 σ hh => ?_, fun k3 σ hh => ?_, fun k3 σ hh => ?_, ent_subst D.f12 _,
    ent_subst D.f21 _, D.kAR.isub ρ.up, D.kATR.isub ρ.up, fun k3 σ hh X X' h => ?_, fun k3 Θ hh X X' h => ?_,
    I.scoped_subst D.hδs ρ.sc, ent_trans (ent_subst D.hδ1 ρ.τ) (forall0_subst φ ρ.τ).1,
    ent_trans (forall0_subst φ ρ.τ).2 (ent_subst D.hδ2 ρ.τ), I.scoped_subst D.hδs' ρ.sc,
    ent_trans (ent_subst D.hδ1' ρ.τ) (forall0_subst φ' ρ.τ).1, ent_trans (forall0_subst φ' ρ.τ).2 (ent_subst D.hδ2' ρ.τ),
    ?_, ?_, ?_, ent_subst D.p12 _, ent_subst D.p21 _, D.rG.isub ρ, D.rGG.isub ρ, D.cG.isub ρ, ?_, ?_, ?_⟩
  · rw [Tm.isub_isub, Tm.isub_isub]; exact D.rT k3 _ (hc σ hh)
  · rw [Tm.isub_isub]; exact D.rTT k3 _ (hc σ hh)
  · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact D.rE k3 _ (hc σ hh)
  · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact D.rEL k3 _ (hc σ hh)
  · rw [Tm.isub_isub] at h; exact D.kTR k3 _ (hc σ hh) X X' h
  · rw [Tm.isub_isub] at h; exact D.kTTR k3 _ (hc Θ hh) X X' h
  · have := HasTy.isubS hW D.hty ρ
    rwa [transp_isub, dinst_isub_end _ (.inr rfl)] at this
  · have := HasTy.isubS hW D.hty' ρ
    rwa [transp_isub, dinst_isub_end _ (.inr rfl)] at this
  · have := EqTm.isubS hW D.heq ρ
    rwa [transp_isub, transp_isub, dinst_isub_end _ (.inr rfl)] at this
  · have := RE2.isub hW D.ha0 ρ
    rwa [dinst_isub_end _ (.inl rfl)] at this
  · rw [semK_isubS hW hA]
    exact D.kAC.restrict hW (semK_ne hW hA) ρ.up.hom
  · intro k3 σ hh
    rw [Tm.isub_isub]
    exact D.kTC k3 _ (hc σ hh)

omit hW in
theorem TGD2.kAH {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') (k' : ℕ) (σ : ISub k' (k + 1)) (X' : Tm)
    (h : RT2 S k' (A.isub σ) X') : KanH2 S k' (A.isub σ) X' := by
  have := D.rAA k' σ.tail (σ.τ 0) (σ.τ 0) (σ.sc 0 (by omega)) (σ.sc 0 (by omega)) (I_eq_refl _)
  rw [ISub.cons_tail] at this
  exact D.kAR k' σ _ X' this h

omit hW in
theorem TGD2.kAT {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') (k' : ℕ) (Θ : ISub (k' + 1) (k + 1)) (X' : Tm)
    (h : RT2 S (k' + 1) (A.isub Θ) X') : KanT2 S k' (A.isub Θ) X' := by
  have := D.rAA (k' + 1) Θ.tail (Θ.τ 0) (Θ.τ 0) (Θ.sc 0 (by omega)) (Θ.sc 0 (by omega)) (I_eq_refl _)
  rw [ISub.cons_tail] at this
  exact D.kATR k' Θ _ X' this h

omit hW in
theorem TGD2.kTH {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') (k' : ℕ) (σ : ISub k' (k + 1))
    (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) (X' : Tm) (h : RT2 S k' (T.isub σ) X') : KanH2 S k' (T.isub σ) X' :=
  D.kTR k' σ hh _ X' (D.rTT k' σ hh) h

omit hW in
theorem TGD2.kTT {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') (k' : ℕ) (Θ : ISub (k' + 1) (k + 1))
    (hh : (ival (idEnv (k' + 1)) (φ.subst Θ.τ)).holds) (X' : Tm) (h : RT2 S (k' + 1) (T.isub Θ) X') :
    KanT2 S k' (T.isub Θ) X' :=
  D.kTTR k' Θ hh _ X' (D.rTT (k' + 1) Θ hh) h

omit hW in
theorem near_cons (X : Tm) {τ : ISub k' k} {r r' : I} (hr : r.Scoped k') (hr' : r'.Scoped k') (he : I.Eq r r') :
    TmNear (X.isub (ISub.cons r hr τ)) (X.isub (ISub.cons r' hr' τ)) :=
  (TmNear.refl X).dsubst fun i => by
    rcases i with _ | i
    · exact he
    · exact I_eq_refl _

omit hW in
theorem holds_cons_near {φ φ' : I} (hφ : φ.Scoped (k + 1)) (hφ' : φ'.Scoped (k + 1)) (f12 : I.Entails φ φ')
    {τ : ISub k' k} {r r' : I} (hr : r.Scoped k') (hr' : r'.Scoped k') (he : I.Eq r r')
    (hh : (ival (idEnv k') (φ.subst (ISub.cons r hr τ).τ)).holds) :
    (ival (idEnv k') (φ'.subst (ISub.cons r' hr' τ).τ)).holds := by
  rw [holds_iff_entails (I.scoped_subst hφ (ISub.cons r hr τ).sc)] at hh
  rw [holds_iff_entails (I.scoped_subst hφ' (ISub.cons r' hr' τ).sc)]
  refine ent_trans (ent_trans hh (ent_subst f12 _)) (eq_ent (I_eq_subst_congr (fun i => ?_) φ'))
  rcases i with _ | i
  · exact he
  · exact I_eq_refl _

/-- The fibers at near points. -/
theorem TGD2.rTN {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') {k' : ℕ} (τ : ISub k' k) {r r' : I} (hr : r.Scoped k')
    (hr' : r'.Scoped k') (he : I.Eq r r') (hh : (ival (idEnv k') (φ.subst (ISub.cons r hr τ).τ)).holds) :
    RT2 S k' (T.isub (ISub.cons r hr τ)) (T'.isub (ISub.cons r' hr' τ)) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  have hh' := holds_cons_near (glue_data hW hG).1 (glue_data hW hG').1 D.f12 hr hr' he hh
  obtain ⟨lT, hT, -⟩ := glue_fiber_ty hW hG _ hh
  obtain ⟨lT', hT', -⟩ := glue_fiber_ty hW hG' _ hh'
  exact RT2_near hW (tyCode_of_univ hW hT) (D.rT k' _ hh) (near_cons T' hr hr' he) ⟨lT', .inl hT'⟩

/-- The equivalences at near points. -/
theorem TGD2.rEN {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') {k' : ℕ} (τ : ISub k' k) {r r' : I} (hr : r.Scoped k')
    (hr' : r'.Scoped k') (he : I.Eq r r') (hh : (ival (idEnv k') (φ.subst (ISub.cons r hr τ).τ)).holds) :
    RE2 S k' (Tm.equiv (T.isub (ISub.cons r hr τ)) (A.isub (ISub.cons r hr τ))) (e.isub (ISub.cons r hr τ))
      (e'.isub (ISub.cons r' hr' τ)) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨-, lA, hA, -⟩ := glue_data hW hG
  have hh' := holds_cons_near (glue_data hW hG).1 (glue_data hW hG').1 D.f12 hr hr' he hh
  obtain ⟨lT, hT, -⟩ := glue_fiber_ty hW hG _ hh
  obtain ⟨-, -, he'⟩ := glue_fiber_ty hW hG' _ hh'
  have x := D.rE k' _ hh
  have hEE : TyEq S k' (Tm.equiv (T'.isub (ISub.cons r' hr' τ)) (A'.isub (ISub.cons r' hr' τ)))
      (Tm.equiv (T.isub (ISub.cons r hr τ)) (A.isub (ISub.cons r hr τ))) := by
    have eT := (Comp2_ty_base (D.rTN hW τ hr hr' he hh)).2.2.2.2.2
    have eA := (Comp2_ty_base (D.rA k' τ r r' hr hr' he)).2.2.2.2.2
    exact TyEq.symm (equiv_tyEq hW hT (HasTy.isubS hW hA _) eT eA)
  exact RE2_equiv_near hW hT (HasTy.isubS hW hA _) (D.rTT k' _ hh) (D.rAA k' τ r r hr hr (I_eq_refl _)) x (near_cons e' hr hr' he)
    (he'.tyConv hEE)


theorem tg_of {A T e u0 X : Tm} {φ ψ δ : I} (h : HasTy S k .one [] (.transp (.glue A φ T e) ψ u0) X)
    (hδs : δ.Scoped k) (hδ1 : I.Entails δ φ.forall0) : ∃ l, TG S k .one [] A φ T e ψ u0 δ l := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨m, ⟨hG, hψ, hconst, hu0⟩, -⟩ := gen_transpF (spec_to_minimal hW h) rfl
  obtain ⟨l0, ⟨hA0, hφ, hT0, he0⟩, chg⟩ := gen_glue hS hG rfl
  have hconst' := (chg.restrict (scoped_shift (show (cof I.one ψ).Scoped k from ⟨trivial, hψ⟩))
    (ent_shift (ent_and_left I.one ψ))).backEq hconst
  exact ⟨l0, ⟨hS, hA0, hφ, hT0, he0, hψ, hδs, hδ1, hconst', hu0⟩⟩

theorem TGD2.tgL {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') : ∃ l, TG S k .one [] A φ T e ψ u0 δ l :=
  tg_of hW D.hty D.hδs D.hδ1

theorem TGD2.tgR {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') : ∃ l, TG S k .one [] A' φ' T' e' ψ' u0' δ' l :=
  tg_of hW D.hty' D.hδs' D.hδ1'


omit hW in
theorem LineRob.at {C C' : Tm} (h : LineRob S k C C') (σ : ISub k' (k + 1)) : RT2 S k' (C.isub σ) (C'.isub σ) := by
  have := h k' σ.tail (σ.τ 0) (σ.τ 0) (σ.sc 0 (by omega)) (σ.sc 0 (by omega)) (I_eq_refl _)
  rwa [ISub.cons_tail] at this

/-- `unglue` along restrictions of the Glue lines. -/
theorem TGD2.ugAt {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
    (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ') (σ : ISub k' (k + 1)) {g g' : Tm}
    (h : RE2 S k' ((Tm.glue A φ T e).isub σ) g g') :
    RE2 S k' (A.isub σ) (.unglue (φ.subst σ.τ) (e.isub σ) g) (.unglue (φ'.subst σ.τ) (e'.isub σ) g') := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  have hGσ : HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) := HasTy.isubS hW hG σ
  have hG'σ : HasTy S k' .one [] (.glue (A'.isub σ) (φ'.subst σ.τ) (T'.isub σ) (e'.isub σ)) (.univ l') :=
    HasTy.isubS hW hG' σ
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hGσ
  obtain ⟨hφs', lA', hA0', he0'⟩ := glue_data hW hG'σ
  have hc : ∀ {k3} (τ : ISub k3 k'), (ival (idEnv k3) ((φ.subst σ.τ).subst τ.τ)).holds →
      (ival (idEnv k3) (φ.subst (σ.comp τ).τ)).holds := fun τ h => by rwa [I_subst_comp]
  have hAσ := D.rA.at σ
  have hT : ∀ k3 (τ : ISub k3 k'), (ival (idEnv k3) ((φ.subst σ.τ).subst τ.τ)).holds →
      RT2 S k3 ((T.isub σ).isub τ) ((T'.isub σ).isub τ) := fun k3 τ hh => by
    rw [Tm.isub_isub, Tm.isub_isub]; exact D.rT k3 _ (hc τ hh)
  have hE : ∀ k3 (τ : ISub k3 k'), (ival (idEnv k3) ((φ.subst σ.τ).subst τ.τ)).holds →
      RE2 S k3 (Tm.equiv ((T.isub σ).isub τ) ((A.isub σ).isub τ)) ((e.isub σ).isub τ) ((e'.isub σ).isub τ) :=
    fun k3 τ hh => by rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact D.rE k3 _ (hc τ hh)
  have ee' := glue_ee hW hGσ hG'σ (ent_subst D.f12 σ.τ) hAσ hT hE
  have hu := unglue_ty hW ⟨l, .inl hGσ⟩ ⟨lA, hA0, he0⟩ (RE2.typed h).1
  have eGG : TyEq S k' ((Tm.glue A φ T e).isub σ) ((Tm.glue A' φ' T' e').isub σ) :=
    (Comp2_ty_base (D.rG.at σ)).2.2.2.2.2
  have hu' := (unglue_ty hW ⟨l', .inl hG'σ⟩ ⟨lA', hA0', he0'⟩ ((RE2.typed h).2.1.tyConv eGG)).tyConv
    (TyEq.symm (Comp2_ty_base hAσ).2.2.2.2.2)
  exact RE2_unglue_gen hW hGσ h hu hu' hφs' (ent_subst D.f12 σ.τ) (ent_subst D.f21 σ.τ) ee'
    (fun k3 τ => by rw [Tm.isub_isub]; exact D.rAA.at _)
    (fun k3 τ hh => by rw [Tm.isub_isub]; exact D.rTT k3 _ (hc τ hh)) hE

end

end Model.Whnf
