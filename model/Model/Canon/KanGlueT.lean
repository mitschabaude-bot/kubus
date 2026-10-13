import Model.Canon.KanGlue

/-!
# Canonicity: transport in Glue types

`transp (i. Glue A [φ ↦ (T, e)]) ψ u0` computes (`transpGlueWith`) to a Glue element built from a
composition in `A`, a transport in `T` and a contraction in the fibres of `e(1)`. Each part is
computable, given the computability data of the Glue line (`GlueL`).
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The data of a transport along a Glue line: the line is computable, the transport is typed,
the start is computable, and `δ` is equivalent to `∀i. φ`. -/
structure TGD (S : Sig) (k : ℕ) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I) : Prop where
  gl : GlueL S (k + 1) A φ T e
  hty : HasTy S k .one [] (.transp (.glue A φ T e) ψ u0) ((Tm.glue A φ T e).dinst .one)
  hu0 : RE S k ((Tm.glue A φ T e).dinst .zero) u0
  hδs : δ.Scoped k
  hδ1 : I.Entails δ φ.forall0
  hδ2 : I.Entails φ.forall0 δ

theorem GlueL.isub {n n' : ℕ} {A T e : Tm} {φ : I} (D : GlueL S n A φ T e) (hW : WfSig S) (ρ : ISub n' n) :
    GlueL S n' (A.isub ρ) (φ.subst ρ.τ) (T.isub ρ) (e.isub ρ) := by
  have hf : ∀ {k'} (σ : ISub k' n'), (φ.subst ρ.τ).subst σ.τ = φ.subst (ρ.comp σ).τ :=
    fun σ => I_subst_subst _ _ _
  obtain ⟨l, hG⟩ := D.ty
  refine ⟨⟨l, HasTy.isubS hW hG ρ⟩, fun k' σ => ?_, kanAll_isub D.kA ρ, fun k' σ hh => ?_, fun k' σ hh => ?_,
    fun k' σ hh => ?_, fun k' σ hh => ?_⟩
  · rw [Tm.isub_isub]; exact D.rtA k' (ρ.comp σ)
  · rw [hf] at hh; rw [Tm.isub_isub]; exact D.rtT k' (ρ.comp σ) hh
  · rw [hf] at hh; rw [Tm.isub_isub]; exact D.kTH k' (ρ.comp σ) hh
  · rw [hf] at hh; rw [Tm.isub_isub]; exact D.kTT k' (ρ.comp σ) hh
  · rw [hf] at hh; rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact D.eqv k' (ρ.comp σ) hh

/-- An endpoint instance, as a restriction. -/
theorem dinst_isub (X : Tm) (r : I) (σ : ISub k' k) (hr : (r.subst σ.τ).Scoped k') :
    (X.dinst r).isub σ = X.isub (ISub.cons (r.subst σ.τ) hr σ) := by
  simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  congr 1; funext i; rcases i with _ | i <;> rfl

theorem I_dinst_isub (φ : I) (r : I) (σ : ISub k' k) (hr : (r.subst σ.τ).Scoped k') :
    (φ.subst (I.inst0 r)).subst σ.τ = φ.subst (ISub.cons (r.subst σ.τ) hr σ).τ := by
  rw [I_subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl

section
variable (δ : I) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (σ : ℕ → Tm) (τ : ℕ → I)

theorem tg_subst_top :
    (tgExt A φ T e ψ u0 δ).subst σ τ = tgExt (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (T.subst (dupS σ) (I.up τ)) (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) (δ.subst τ) ∧
    (tgA1 A φ T e ψ u0 δ).subst σ τ = tgA1 (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (T.subst (dupS σ) (I.up τ)) (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) (δ.subst τ) := by
  have h := transpGlueWith_subst (σ := σ) (τ := τ) δ A φ T e ψ u0
  rw [transpGlueWith_eq, transpGlueWith_eq] at h
  simp only [Tm.subst] at h
  injection h with h1 h2 h3 h4
  injection h3 with h3
  exact ⟨h3, h4⟩

theorem tg_subst_mid :
    (tgFib A φ T e ψ u0).subst σ τ = tgFib (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (T.subst (dupS σ) (I.up τ)) (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) ∧
    (tgC A φ e ψ u0).subst σ τ = tgC (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) ∧
    (tgPd A φ T e ψ u0).subst σ τ = tgPd (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (T.subst (dupS σ) (I.up τ)) (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) ∧
    (tgPpsi A φ e ψ u0).subst σ τ = tgPpsi (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) ∧
    (tgA1' A φ e ψ u0).subst σ τ = tgA1' (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) := by
  obtain ⟨h1, h2⟩ := tg_subst_top .zero A φ T e ψ u0 σ τ
  rw [tgExt_eq, tgExt_eq] at h1
  rw [tgA1_eq, tgA1_eq] at h2
  simp only [Tm.subst] at h1 h2
  injection h1 with hfib _ hsys hfc
  injection h2 with _ _ _ ha1
  injection hfc with hc
  injection hsys with _ hPd _ hPpsi
  injection hPd with hPd _
  injection hPpsi with hPpsi _
  have dd : ∀ X Y : Tm, X.dshift.subst (dupS σ) (I.up τ) = Y.dshift → X.subst σ τ = Y := fun X Y h => by
    have := congrArg (·.dinst .zero) h
    simp only at this
    rwa [dshift_subst_dup, Meta.dshift_dinst, Meta.dshift_dinst] at this
  exact ⟨hfib, hc, dd _ _ hPd, dd _ _ hPpsi, ha1⟩

theorem tg_subst_low :
    (tgT1 T ψ u0).subst σ τ = tgT1 (T.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) ∧
    (tgBody A φ T e ψ u0).subst (dupS σ) (I.up τ) = tgBody (A.subst (dupS σ) (I.up τ)) (φ.subst (I.up τ))
      (T.subst (dupS σ) (I.up τ)) (e.subst (dupS σ) (I.up τ)) (ψ.subst τ) (u0.subst σ τ) ∧
    (tgA0 φ e u0).subst σ τ = tgA0 (φ.subst (I.up τ)) (e.subst (dupS σ) (I.up τ)) (u0.subst σ τ) ∧
    (tgTube φ e u0).subst (dupS σ) (I.up τ) = tgTube (φ.subst (I.up τ)) (e.subst (dupS σ) (I.up τ)) (u0.subst σ τ) := by
  obtain ⟨-, -, hPd, -, ha1⟩ := tg_subst_mid A φ T e ψ u0 σ τ
  simp only [tgPd, tgOmega, tgA1', Tm.comp, Tm.subst] at hPd ha1
  injection hPd with _ hp
  injection hp with ht1 hω
  injection hω with hb
  injection ha1 with _ _ htu ha0
  injection htu with _ _ htube
  injection ha0 with _ _ ha0
  exact ⟨ht1, hb, ha0, htube⟩

end

theorem dinst_isub_end (X : Tm) {r : I} (hr : r = .zero ∨ r = .one) (σ : ISub k' k) :
    (X.dinst r).isub σ = (X.isub σ.up).dinst r := by
  simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  congr 1; funext i; rcases i with _ | i
  · rcases hr with rfl | rfl <;> rfl
  · show σ.τ i = ((σ.τ i).shift).subst _; rw [I_shift_inst0]

theorem transp_isub (A : Tm) (ψ : I) (u0 : Tm) (σ : ISub k' k) :
    (Tm.transp A ψ u0).isub σ = .transp (A.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) := by
  show Tm.transp (A.subst (dupS Tm.var) (I.up σ.τ)) _ _ = _
  rw [dupS_var]; rfl

variable (hW : WfSig S) (hGC : GlueCompat S)
include hW

theorem TGD.isub {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (ρ : ISub k' k) :
    TGD S k' (A.isub ρ.up) (φ.subst ρ.up.τ) (T.isub ρ.up) (e.isub ρ.up) (ψ.subst ρ.τ) (u0.isub ρ) (δ.subst ρ.τ) := by
  refine ⟨D.gl.isub hW ρ.up, ?_, ?_, I.scoped_subst D.hδs ρ.sc,
    ent_trans (ent_subst D.hδ1 ρ.τ) (forall0_subst φ ρ.τ).1, ent_trans (forall0_subst φ ρ.τ).2 (ent_subst D.hδ2 ρ.τ)⟩
  · have := HasTy.isubS hW D.hty ρ
    rwa [transp_isub, dinst_isub_end _ (.inr rfl)] at this
  · have := D.hu0.isub hW ρ
    rwa [dinst_isub_end _ (.inl rfl)] at this

theorem TGD.tg {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) :
    ∃ l, TG S k .one [] A φ T e ψ u0 δ l := by
  have hS := sigClosed_of_wfSig hW
  have h := spec_to_minimal hW D.hty
  obtain ⟨m, ⟨hG, hψ, hconst, hu0⟩, -⟩ := gen_transpF h rfl
  obtain ⟨l0, ⟨hA0, hφ, hT0, he0⟩, chg⟩ := gen_glue hS hG rfl
  have hconst' := (chg.restrict (scoped_shift (show (cof I.one ψ).Scoped k from ⟨trivial, hψ⟩))
    (ent_shift (ent_and_left I.one ψ))).backEq hconst
  exact ⟨l0, ⟨hS, hA0, hφ, hT0, he0, hψ, D.hδs, D.hδ1, hconst', hu0⟩⟩

/-- An instance of a Glue line at an interval point. -/
theorem GlueL.slice {A T e : Tm} {φ : I} (D : GlueL S (k + 1) A φ T e) (r : I) (hr : r.Scoped k) :
    GlueL S k (A.dinst r) (φ.subst (I.inst0 r)) (T.dinst r) (e.dinst r) := by
  obtain ⟨l, hG⟩ := D.ty
  obtain ⟨hφs, -⟩ := glue_data hW hG
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  have h := D.isub hW (ISub.cons r hr (ISub.id k))
  have eφ : φ.subst (ISub.cons r hr (ISub.id k)).τ = φ.subst (I.inst0 r) :=
    I_subst_congr_scoped (fun i hi => by
      rcases i with _ | i
      · rfl
      · show (ISub.id k).τ i = .var i; simp [ISub.id, show i < k by omega]) hφs
  rwa [isub_cons_id_dinst hW hc.1.1.1, isub_cons_id_dinst hW hc.1.2, isub_cons_id_dinst hW hc.2, eφ] at h

include hGC in
theorem L_a0 {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) :
    RE S k (A.dinst .zero) (tgA0 φ e u0) := by
  have D0 := D.gl.slice hW .zero trivial
  obtain ⟨l, hG⟩ := D0.ty
  exact RE_unglue_gen hW hGC hG D0.eqv D.hu0

omit hW in
theorem tgTube_isub (φ : I) (e u0 : Tm) (σ : ISub k' k) :
    (tgTube φ e u0).isub σ.up = tgTube (φ.subst σ.up.τ) (e.isub σ.up) (u0.isub σ) := by
  have := (tg_subst_low (.var 0) φ (.var 0) e .zero u0 Tm.var σ.τ).2.2.2; rw [dupS_var] at this; exact this

include hGC in
theorem L_tube0 {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (r : I) (hr : r.Scoped k)
    (hψ : (ival (idEnv k) ψ).holds) : RE S k (A.dinst r) ((tgTube φ e u0).dinst r) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, H⟩ := D.tg hW
  have Dr := D.gl.slice hW r hr
  obtain ⟨lr, hGr⟩ := Dr.ty
  rw [tgTube_dinst]
  refine RE_unglue_gen hW hGC hGr Dr.eqv ?_
  have hc := EqTm0.dsubst hS (Ψ := k) (Φ := cof .one ψ) (Γ := []) H.hconst (r := r) hr
  rw [Meta.dshift_dinst] at hc
  have hc' := EqTm.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds H.hψ hψ)) (minimal_to_spec_eq hc)
  exact D.hu0.conv_ty hW (.inr ⟨l, hc'.symm⟩)

include hGC in
theorem L_a1' {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) :
    RE S k (A.dinst .one) (tgA1' A φ e ψ u0) := by
  obtain ⟨l, H⟩ := D.tg hW
  refine RE_comp hW D.gl.kA (minimal_to_spec H.ha1') (fun k' σ r hr hh => ?_) (L_a0 hW hGC D)
  rw [tgTube_isub]
  exact L_tube0 hW hGC (D.isub hW σ) r hr hh

end

end Model.Canon
