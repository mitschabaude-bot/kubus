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

/-- On `δ`, the face of the line holds everywhere along it. -/
theorem TGD.face_line {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ)
    (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (σ : ISub k' (k + 1)) : (ival (idEnv k') (φ.subst σ.τ)).holds := by
  obtain ⟨l, H⟩ := D.tg hW
  have hent : I.Entails .one δ := entails_of_holds D.hδs hδ
  have h1 : I.Entails .one φ := ent_trans (ent_shift hent) (ent_forall_shift D.hδ1)
  rw [holds_iff_entails (I.scoped_subst H.hφ σ.sc)]
  exact ent_subst h1 σ.τ

theorem TGD.closed {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) :
    A.closedB 0 (k + 1) = true ∧ T.closedB 0 (k + 1) = true ∧ e.closedB 0 (k + 1) = true := by
  obtain ⟨l, hG⟩ := D.gl.ty
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1, hc.1.2, hc.2⟩

theorem TGD.hu0T {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (hδ : (ival (idEnv k) δ).holds) :
    RE S k (T.dinst .zero) u0 := by
  obtain ⟨l, H⟩ := D.tg hW
  have hent : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  exact D.hu0.conv_ty hW (.inr ⟨l, EqTm.restrict (Φ' := .one) trivial hent
    (minimal_to_spec_eq (H.hGTr (r := .zero) trivial))⟩)

theorem L_t1' {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (hδ : (ival (idEnv k) δ).holds) :
    RE S k (T.dinst .one) (tgT1 T ψ u0) := by
  obtain ⟨l, H⟩ := D.tg hW
  have hent : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have KT := D.gl.kTT k (ISub.id (k + 1)) (D.face_line hW hδ _)
  rw [isub_id_of_closed (D.closed hW).2.1] at KT
  exact KT ψ u0 (HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.ht1)) (D.hu0T hW hδ)

theorem RE_app_fst {X Y e x : Tm} (he : RE S k (Tm.equiv X Y) e) (hx : RE S k X x) :
    RE S k Y (.app (.fst e) x) := by
  unfold Tm.equiv at he
  have h := RE_pi_elim hW (RE_sigma_elim hW he).1 hx
  rwa [shift_inst] at h

theorem TGD.eqvAt {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (hδ : (ival (idEnv k) δ).holds)
    (ρ : ISub k' (k + 1)) : RE S k' (Tm.equiv (T.isub ρ) (A.isub ρ)) (e.isub ρ) :=
  D.gl.eqv k' ρ (D.face_line hW hδ ρ)

include hGC in
theorem L_fillA {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) :
    RE S (k + 1) A (Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)) := by
  obtain ⟨l, H⟩ := D.tg hW
  refine RE_fill hW D.gl.kA (minimal_to_spec H.hA) H.hψ (minimal_to_spec H.htube) (minimal_to_spec H.ha0)
    (minimal_to_spec_eq H.htube_side) (fun k' σ r hr hh => ?_) (L_a0 hW hGC D)
  rw [tgTube_isub]
  exact L_tube0 hW hGC (D.isub hW σ) r hr hh

theorem L_tfT {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (hδ : (ival (idEnv k) δ).holds) :
    RE S (k + 1) T (Tm.transpFill T ψ u0) := by
  obtain ⟨l, H⟩ := D.tg hW
  have hent : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  exact RE_transpFill hW (fun k' ρ => D.gl.kTT k' ρ (D.face_line hW hδ ρ))
    (HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.ht1)) (D.hu0T hW hδ)

omit hW in
theorem sk2_isub (X : Tm) (σ : ISub k' k) {s r : I} (hs : s.Scoped k') (hr : r.Scoped k') :
    (X.dsubst (sk (.var 0) 2)).isub (ISub.cons s hs (ISub.cons r hr σ)) = X.isub (ISub.cons s hs σ) := by
  simp only [Tm.isub, Tm.dsubst, subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl

omit hW in
theorem tgSys_isub (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (r : I) (σ : ISub k' k) {s : I}
    (hs : s.Scoped k') (hr : (r.subst σ.τ).Scoped k') :
    (((tgSys A φ T e ψ u0).subst Tm.var (I.up (I.inst0 r))).isub σ.up).dinst s =
      (tgSys A φ T e ψ u0).isub (ISub.cons s hs (ISub.cons (r.subst σ.τ) hr σ)) := by
  simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  congr 1; funext i; rcases i with _ | _ | i
  · rfl
  · show ((r.shift).subst (I.up σ.τ)).subst (I.inst0 s) = r.subst σ.τ
    rw [I_shift_subst_up, I_shift_inst0]
  · show (((σ.τ i).shift).subst (I.inst0 s)) = σ.τ i
    rw [I_shift_inst0]

omit hW in
theorem tgSys'_isub (e : Tm) (ψ : I) (u0 F G : Tm) (σ : ISub k' k) {s r : I} (hs : s.Scoped k') (hr : r.Scoped k') :
    (tgSys' e ψ u0 F G).isub (ISub.cons s hs (ISub.cons r hr σ)) =
      .split (ψ.subst σ.τ) (.app (.fst (e.isub (ISub.cons s hs σ))) (u0.isub σ)) (.or (.neg r) r)
        (.split (.neg r) (.app (.fst (e.isub (ISub.cons s hs σ))) (F.isub (ISub.cons s hs σ))) r
          (G.isub (ISub.cons s hs σ))) := by
  show Tm.split (ψ.shift.shift.subst _) (.app (.fst ((e.dsubst (sk (.var 0) 2)).isub _))
      (u0.dshift.dshift.isub (ISub.cons s hs (ISub.cons r hr σ)))) _
    (.split _ (.app (.fst ((e.dsubst (sk (.var 0) 2)).isub _)) ((F.dsubst (sk (.var 0) 2)).isub _)) _
      ((G.dsubst (sk (.var 0) 2)).isub _)) = _
  rw [I_shift_cons, I_shift_cons, sk2_isub, sk2_isub, sk2_isub, dshift_isub_cons, dshift_isub_cons]
  rfl

include hGC in
/-- The body of `ω`, at a point of the path. -/
theorem L_body {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (hδ : (ival (idEnv k) δ).holds)
    (r : I) (hr : r.Scoped k) :
    RE S k (A.dinst .one) (Tm.comp A (.or ψ (.or (.neg r) r)) ((tgSys A φ T e ψ u0).subst Tm.var (I.up (I.inst0 r)))
      (.app (.fst (e.dinst .zero)) u0)) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, H⟩ := D.tg hW
  obtain ⟨hAc, hTc, hec⟩ := D.closed hW
  have hentδ : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hb := HasTy0.dsubst hS (Ψ := k) (Φ := cof .one δ) (Γ := []) H.hbody (r := r) hr
  rw [tgBody_dinst, Meta.dshift_dinst] at hb
  have hty := HasTy.restrict (Φ' := .one) trivial hentδ (minimal_to_spec hb)
  refine RE_comp hW D.gl.kA hty (fun k' σ s hs hh => ?_) ?_
  swap
  · have he0 := D.eqvAt hW hδ (ISub.cons .zero trivial (ISub.id k))
    rw [isub_cons_id_dinst hW hTc, isub_cons_id_dinst hW hAc, isub_cons_id_dinst hW hec] at he0
    exact RE_app_fst hW he0 (D.hu0T hW hδ)
  have hr' : (r.subst σ.τ).Scoped k' := I.scoped_subst hr σ.sc
  rw [tgSys_isub A φ T e ψ u0 r σ hs hr', isub_up_dinst _ _ _ hs]
  have hsys := HasTy.isubF hW (show ((cof (cof .one δ).shift (tgChi ψ)).shift).Scoped (k + 1 + 1) from
    I.scoped_shift ⟨I.scoped_shift ⟨trivial, D.hδs⟩, I.scoped_shift H.hψ, show 0 < k + 1 by omega,
      show 0 < k + 1 by omega⟩) (minimal_to_spec H.hsys) (ISub.cons s hs (ISub.cons (r.subst σ.τ) hr' σ))
  have hchi : (tgChi ψ).subst (ISub.cons (r.subst σ.τ) hr' σ).τ = (I.or ψ (.or (.neg r) r)).subst σ.τ := by
    show I.or (ψ.shift.subst _) _ = _; rw [I_shift_cons]; rfl
  have hctx : I.Entails .one (((cof (cof .one δ).shift (tgChi ψ)).shift).subst
      (ISub.cons s hs (ISub.cons (r.subst σ.τ) hr' σ)).τ) := by
    rw [I_shift_cons]
    show I.Entails .one (I.and (((cof .one δ).shift).subst _) ((tgChi ψ).subst _))
    rw [I_shift_cons, hchi]
    exact ent_and_intro (ent_subst hentδ σ.τ)
      (entails_of_holds (I.scoped_subst (show (I.or ψ (.or (.neg r) r)).Scoped k from ⟨H.hψ, hr, hr⟩) σ.sc) hh)
  have hsys' := HasTy.restrict (Φ' := .one) trivial hctx hsys
  rw [sk2_isub] at hsys'
  unfold tgSys at hsys' ⊢
  rw [tgSys'_isub] at hsys' ⊢
  rcases holds_or hh with h1 | h23
  · have e1 := EqTm.splitL (entails_of_holds (I.scoped_subst H.hψ σ.sc) h1) hsys'
    have hu0σ := (D.hu0T hW hδ).isub hW σ
    rw [dinst_isub T .zero σ trivial] at hu0σ
    have ec := EqTm.isubF hW (show ((cof (cof .one δ) ψ).shift).Scoped (k + 1) from
      I.scoped_shift ⟨⟨trivial, D.hδs⟩, H.hψ⟩) (minimal_to_spec_eq H.hconstT) (ISub.cons s hs σ)
    rw [I_shift_cons] at ec
    have ec' := EqTm.restrict (Φ' := .one) trivial
      (ent_and_intro (ent_subst hentδ σ.τ) (entails_of_holds (I.scoped_subst H.hψ σ.sc) h1)) ec
    rw [dshift_isub_cons, dinst_isub T .zero σ trivial] at ec'
    have hu0s := hu0σ.conv_ty hW (.inr ⟨l, ec'.symm⟩)
    exact (RE_app_fst hW (D.eqvAt hW hδ (ISub.cons s hs σ)) hu0s).conv hW (TyEq.refl _) e1.symm
  · have hs23 : (I.or (.neg (r.subst σ.τ)) (r.subst σ.τ)).Scoped k' := ⟨hr', hr'⟩
    have e1 := EqTm.splitR (entails_of_holds hs23 h23) hsys'
    have hin := HasTy.eqR e1
    rcases holds_or h23 with h2 | h3
    · have e2 := EqTm.splitL (entails_of_holds (show (I.neg (r.subst σ.τ)).Scoped k' from hr') h2) hin
      exact (RE_app_fst hW (D.eqvAt hW hδ (ISub.cons s hs σ)) ((L_tfT hW D hδ).isub hW _)).conv hW (TyEq.refl _)
        (e1.trans e2).symm
    · have e2 := EqTm.splitR (entails_of_holds hr' h3) hin
      exact ((L_fillA hW hGC D).isub hW _).conv hW (TyEq.refl _) (e1.trans e2).symm

omit hW in
theorem tgOmega_isub (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (σ : ISub k' k) :
    (tgOmega A φ T e ψ u0).isub σ =
      tgOmega (A.isub σ.up) (φ.subst σ.up.τ) (T.isub σ.up) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) := by
  have h := (tg_subst_low A φ T e ψ u0 Tm.var σ.τ).2.1
  rw [dupS_var] at h
  show Tm.plam ((tgBody A φ T e ψ u0).subst (dupS Tm.var) (I.up σ.τ)) = _
  rw [dupS_var, h]; rfl

theorem holds_isub {δ : I} (hδs : δ.Scoped k) (hδ : (ival (idEnv k) δ).holds) (σ : ISub k' k) :
    (ival (idEnv k') (δ.subst σ.τ)).holds := by
  rw [holds_iff_entails (I.scoped_subst hδs σ.sc)]
  exact ent_subst (entails_of_holds hδs hδ) σ.τ

include hGC in
/-- `ω : Path A(1) (e(1).1 t1') a1'` is computable (on `δ`). -/
theorem L_omega {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (hδ : (ival (idEnv k) δ).holds) :
    RE S k (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0))
      (tgOmega A φ T e ψ u0) := by
  obtain ⟨l, H⟩ := D.tg hW
  have hentδ : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hω := HasTy.restrict (Φ' := .one) trivial hentδ (minimal_to_spec H.hω)
  obtain ⟨lp, hpT⟩ := ty_of_tyEq hW (isTyK_of_ty hW hω) (TyEq.refl _) (fun l h => by cases h)
  unfold Tm.pathC at hω hpT ⊢
  refine RE_path_intro hW hpT hω (fun k' σ r hr => ?_)
  have hωσ := HasTy.isubS hW hω σ
  rw [isub_path, tgOmega_isub] at hωσ
  rw [tgOmega_isub]
  have eβ := EqTm.pathBeta (HasTy.papp hωσ hr)
  have hb := L_body hW hGC (D.isub hW σ) (holds_isub hW D.hδs hδ σ) r hr
  rw [isub_up_dinst _ _ _ hr, dshift_isub_cons, dinst_isub_end _ (.inr rfl)]
  unfold tgOmega at eβ
  rw [tgBody_dinst, isub_up_dinst _ _ _ hr, dshift_isub_cons, dinst_isub_end _ (.inr rfl)] at eβ
  exact hb.conv hW (TyEq.refl _) eβ.symm

omit hW in
theorem dshift_isub_up (X : Tm) (ρ : ISub k' k) : X.dshift.isub ρ.up = (X.isub ρ).dshift := by
  have := dshift_subst_dup Tm.var ρ.τ X
  rw [dupS_var] at this
  exact this

omit hW in
theorem pathC_isub (X x y : Tm) (ρ : ISub k' k) :
    (Tm.pathC X x y).isub ρ = Tm.pathC (X.isub ρ) (x.isub ρ) (y.isub ρ) := by
  unfold Tm.pathC; rw [isub_path, dshift_isub_up]

/-- Path types with a constant line between computable endpoints are Kan. -/
theorem kanAll_pathC {X x y : Tm} {l : ℕ} (hpT : HasTy S k .one [] (Tm.pathC X x y) (.univ l)) (hX : KanAll S k X)
    (hx : ∀ k' (ρ : ISub k' k), RE S k' (X.isub ρ) (x.isub ρ)) (hy : ∀ k' (ρ : ISub k' k), RE S k' (X.isub ρ) (y.isub ρ)) :
    KanAll S k (Tm.pathC X x y) := by
  constructor
  · intro k' ρ
    have hp := HasTy.isubS hW hpT ρ
    rw [pathC_isub] at hp ⊢
    unfold Tm.pathC at hp ⊢
    refine kanH_path hW hp (fun k'' ρ' => ?_) ?_ ?_
    · rw [dshift_isub_tail, Tm.isub_isub]; exact hX.1 _ _
    · rw [Meta.dshift_dinst]; exact hx k' ρ
    · rw [Meta.dshift_dinst]; exact hy k' ρ
  · intro k' ρ
    have hp := HasTy.isubS hW hpT ρ
    rw [pathC_isub] at hp ⊢
    unfold Tm.pathC at hp ⊢
    refine kanT_path hW hp ?_ (fun k'' σ => ?_) (fun k'' σ => ?_)
    · exact ⟨fun k3 ρ'' => by rw [dshift_isub_tail, Tm.isub_isub]; exact hX.1 _ _,
        fun k3 ρ'' => by rw [dshift_isub_tail, Tm.isub_isub]; exact hX.2 _ _⟩
    · rw [isub_up_dinst _ _ _ (show I.Scoped k'' .zero from trivial), dshift_isub_cons, Tm.isub_isub,
        Tm.isub_isub]; exact hx _ _
    · rw [isub_up_dinst _ _ _ (show I.Scoped k'' .one from trivial), dshift_isub_cons, Tm.isub_isub,
        Tm.isub_isub]; exact hy _ _

theorem GlueL.eqv0 {n : ℕ} {A T e : Tm} {φ : I} (G : GlueL S n A φ T e) (hh : (ival (idEnv n) φ).holds) :
    RE S n (Tm.equiv T A) e := by
  obtain ⟨l, hG⟩ := G.ty
  obtain ⟨hφs, -⟩ := glue_data hW hG
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  have := G.eqv n (ISub.id n) (by rw [I_subst_id hφs]; exact hh)
  rwa [isub_id_of_closed hc.1.2, isub_id_of_closed hc.1.1.1, isub_id_of_closed hc.2] at this

omit hW in
theorem tgA1'_isub (A : Tm) (φ : I) (e : Tm) (ψ : I) (u0 : Tm) (σ : ISub k' k) :
    (tgA1' A φ e ψ u0).isub σ = tgA1' (A.isub σ.up) (φ.subst σ.up.τ) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) := by
  have := (tg_subst_mid A φ (.var 0) e ψ u0 Tm.var σ.τ).2.2.2.2; rw [dupS_var] at this; exact this

include hGC in
theorem L_a1'_isub {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (σ : ISub k' k) :
    RE S k' ((A.dinst .one).isub σ) ((tgA1' A φ e ψ u0).isub σ) := by
  rw [tgA1'_isub, dinst_isub_end _ (.inr rfl)]; exact L_a1' hW hGC (D.isub hW σ)

include hGC in
theorem L_c {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ)
    (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) :
    RE S k (Tm.isContr (tgFib A φ T e ψ u0)) (tgC A φ e ψ u0) := by
  have he1 := (D.gl.slice hW .one trivial).eqv0 hW hφ1
  unfold Tm.equiv at he1
  have h2 := (RE_sigma_elim hW he1).2
  rw [isEquiv_inst, isEquiv_eq] at h2
  have h3 := RE_pi_elim hW h2 (L_a1' hW hGC D)
  rwa [isContr_fiber_inst] at h3

include hGC in
theorem L_fibK {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ)
    (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) : KanH S k (tgFib A φ T e ψ u0) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, H⟩ := D.tg hW
  have D1 := D.gl.slice hW .one trivial
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) :=
    ent_cof_one hW (entails_of_holds (H.hφr (r := .one) trivial) hφ1)
  have hfib := HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hfib)
  rw [tgFib_eq] at hfib ⊢
  refine kanH_sigma hW hfib (fun k' ρ => D1.kTH k' ρ (holds_isub hW (H.hφr (r := .one) trivial) hφ1 ρ))
    (fun k' σ a ha => ?_)
  have hφσ := holds_isub hW (H.hφr (r := .one) trivial) hφ1 σ
  rw [pathC_isub, isub_shift, isub_shift]
  have eapp : ((Tm.fst (e.dinst .one)).shift.app (.var 0)).isub σ =
      .app ((Tm.fst (e.dinst .one)).isub σ).shift (.var 0) := by
    show Tm.app ((Tm.fst (e.dinst .one)).shift.isub σ) (Tm.var 0) = _; rw [isub_shift]
  rw [eapp, P_inst]
  have heσ : RE S k' (Tm.equiv ((T.dinst .one).isub σ) ((A.dinst .one).isub σ)) ((e.dinst .one).isub σ) :=
    D1.eqv k' σ hφσ
  have happ := RE_app_fst hW heσ ha
  have ha1 := L_a1'_isub hW hGC D σ
  obtain ⟨lp, hpT⟩ : ∃ lp, HasTy S k' .one [] (Tm.pathC ((A.dinst .one).isub σ) (.app (.fst ((e.dinst .one).isub σ)) a)
      ((tgA1' A φ e ψ u0).isub σ)) (.univ lp) := by
    obtain ⟨lG, hG1⟩ := D1.ty
    obtain ⟨-, lA, hAt, -⟩ := glue_data hW hG1
    have hp := pathC_typed hS (spec_to_minimal hW (HasTy.isubS hW hAt σ)) (spec_to_minimal hW (Comp_el_typed happ).1)
      (spec_to_minimal hW (Comp_el_typed ha1).1)
    exact ⟨lA, minimal_to_spec hp⟩
  refine kanAll_pathC hW hpT (kanAll_isub D1.kA σ) (fun k'' ρ => ?_) (fun k'' ρ => ?_)
  · show RE S k'' (((A.dinst .one).isub σ).isub ρ) (Tm.app (.fst (((e.dinst .one).isub σ).isub ρ)) (a.isub ρ))
    rw [Tm.isub_isub, Tm.isub_isub]
    have haρ := ha.isub hW ρ
    rw [Tm.isub_isub] at haρ
    exact RE_app_fst hW (D1.eqv k'' (σ.comp ρ) (holds_isub hW (H.hφr (r := .one) trivial) hφ1 _)) haρ
  · rw [Tm.isub_isub, Tm.isub_isub]; exact L_a1'_isub hW hGC D (σ.comp ρ)

theorem RE_contr {X c p : Tm} (hc : RE S k (Tm.isContr X) c) (hp : RE S k X p) :
    RE S k (Tm.pathC X (.fst c) p) (.app (.snd c) p) := by
  unfold Tm.isContr at hc
  have h := (RE_sigma_elim hW hc).2
  rw [K_inst] at h
  have h2 := RE_pi_elim hW h hp
  rwa [pathC_var0_inst] at h2

theorem RE_pair_intro {A B a b : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A B) (.univ l))
    (hp : HasTy S k .one [] (.pair a b) (.sigma A B)) (ha : RE S k A a) (hb : RE S k (B.inst a) b) :
    RE S k (.sigma A B) (.pair a b) := by
  have hf := EqTm.fstBeta (HasTy.fst hp)
  have hB := HasTy.sigmaCod hsig
  have hBeq := EqTm.subst (EqTm.refl hB) (EqTm.symm hf)
  exact RE_sigma_intro hW hsig hp (ha.conv hW (TyEq.refl _) (EqTm.symm hf))
    (hb.conv hW (.inr ⟨l, hBeq⟩) (EqTm.symm (EqTm.sndBeta (HasTy.snd hp))))

theorem TGD.ent1 {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ)
    (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) {X : I} (hXs : X.Scoped k) (hX : (ival (idEnv k) X).holds) :
    I.Entails .one (cof (cof .one (φ.subst (I.inst0 .one))) X) := by
  obtain ⟨l, H⟩ := D.tg hW
  exact ent_and_intro (ent_cof_one hW (entails_of_holds (H.hφr (r := .one) trivial) hφ1)) (entails_of_holds hXs hX)

include hGC in
theorem L_Pd {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ)
    (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) (hδ : (ival (idEnv k) δ).holds) :
    RE S k (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)))
      (tgPd A φ T e ψ u0) := by
  obtain ⟨l, H⟩ := D.tg hW
  have hent := D.ent1 hW hφ1 D.hδs hδ
  have hp := HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.hpd)
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) :=
    ent_cof_one hW (entails_of_holds (H.hφr (r := .one) trivial) hφ1)
  have hfib := HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hfib)
  rw [tgFib_eq] at hp hfib
  have hpair : RE S k (tgFib A φ T e ψ u0) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)) := by
    rw [tgFib_eq]
    refine RE_pair_intro hW hfib hp (L_t1' hW D hδ) ?_
    rw [P_inst]; exact L_omega hW hGC D hδ
  exact RE_contr hW (L_c hW hGC D hφ1) hpair

include hGC in
theorem L_Ppsi {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ)
    (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) (hψ : (ival (idEnv k) ψ).holds) :
    RE S k (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift)))
      (tgPpsi A φ e ψ u0) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, H⟩ := D.tg hW
  have hent := D.ent1 hW hφ1 H.hψ hψ
  have hp := HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.hpψ)
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) :=
    ent_cof_one hW (entails_of_holds (H.hφr (r := .one) trivial) hφ1)
  have hfib := HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hfib)
  rw [tgFib_eq] at hp hfib
  -- `u0` lies in `T(1)`
  have hu0 : RE S k (T.dinst .one) u0 := by
    have hc := EqTm0.dsubst hS (Ψ := k) (Φ := cof .one ψ) (Γ := []) H.hconst (r := .one) trivial
    rw [Meta.dshift_dinst] at hc
    have hc' := EqTm.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds H.hψ hψ))
      (minimal_to_spec_eq hc)
    obtain ⟨l1, hG1⟩ := (D.gl.slice hW .one trivial).ty
    have hf := EqTm.glueFace (entails_of_holds (H.hφr (r := .one) trivial) hφ1) hG1
    exact D.hu0.conv_ty hW ((TyEq.symm (.inr ⟨l, hc'⟩)).trans hW (.inr ⟨l1, hf⟩))
  have hpl := HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.hpl)
  have hpair : RE S k (tgFib A φ T e ψ u0) (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift)) := by
    rw [tgFib_eq]
    refine RE_pair_intro hW hfib hp hu0 ?_
    rw [P_inst]
    obtain ⟨lp, hpT⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpl) (TyEq.refl _) (fun l h => by cases h)
    unfold Tm.pathC at hpl hpT ⊢
    refine RE_path_intro hW hpT hpl (fun k' σ r hr => ?_)
    have hσ := HasTy.isubS hW hpl σ
    rw [isub_path] at hσ
    have eβ := EqTm.pathBeta (HasTy.papp hσ hr)
    have e1 : ((tgA1' A φ e ψ u0).dshift.subst (fun n => (Tm.var n).dshift) (I.up σ.τ)).dinst r =
        (tgA1' A φ e ψ u0).isub σ := by
      rw [dshift_subst_dup, Meta.dshift_dinst]; rfl
    have e2 : ((A.dinst .one).dshift.isub σ.up).dinst r = (A.dinst .one).isub σ := by
      rw [dshift_isub_up, Meta.dshift_dinst]
    rw [e1, e2] at eβ
    rw [e2]
    exact (L_a1'_isub hW hGC D σ).conv hW (TyEq.refl _) eβ.symm
  exact RE_contr hW (L_c hW hGC D hφ1) hpair

omit hW in
theorem tg_isub (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I) (σ : ISub k' k) :
    (tgFib A φ T e ψ u0).isub σ = tgFib (A.isub σ.up) (φ.subst σ.up.τ) (T.isub σ.up) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) ∧
    (tgC A φ e ψ u0).isub σ = tgC (A.isub σ.up) (φ.subst σ.up.τ) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) ∧
    (tgPd A φ T e ψ u0).isub σ = tgPd (A.isub σ.up) (φ.subst σ.up.τ) (T.isub σ.up) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) ∧
    (tgPpsi A φ e ψ u0).isub σ = tgPpsi (A.isub σ.up) (φ.subst σ.up.τ) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) ∧
    (tgExt A φ T e ψ u0 δ).isub σ =
      tgExt (A.isub σ.up) (φ.subst σ.up.τ) (T.isub σ.up) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) (δ.subst σ.τ) ∧
    (tgA1 A φ T e ψ u0 δ).isub σ =
      tgA1 (A.isub σ.up) (φ.subst σ.up.τ) (T.isub σ.up) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) (δ.subst σ.τ) := by
  have h1 := tg_subst_top δ A φ T e ψ u0 Tm.var σ.τ
  have h2 := tg_subst_mid A φ T e ψ u0 Tm.var σ.τ
  rw [dupS_var] at h1 h2
  exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h1.1, h1.2⟩

omit hW in
theorem I_phi1_isub (φ : I) (σ : ISub k' k) :
    (φ.subst (I.inst0 .one)).subst σ.τ = (φ.subst σ.up.τ).subst (I.inst0 .one) := by
  rw [I_subst_subst, I_subst_subst]; congr 1; funext i; rcases i with _ | i
  · rfl
  · show σ.τ i = ((σ.τ i).shift).subst _; rw [I_shift_inst0]

omit hW in
theorem psys_isub (δ ψ : I) (X Y : Tm) (σ : ISub k' k) (r : I) :
    ((Tm.split δ.shift (.papp X.dshift (.var 0)) ψ.shift (.papp Y.dshift (.var 0))).isub σ.up).dinst r =
      .split (δ.subst σ.τ) (.papp (X.isub σ) r) (ψ.subst σ.τ) (.papp (Y.isub σ) r) := by
  have e : (Tm.split δ.shift (.papp X.dshift (.var 0)) ψ.shift (.papp Y.dshift (.var 0))).isub σ.up =
      .split (δ.subst σ.τ).shift (.papp (X.isub σ).dshift (.var 0)) (ψ.subst σ.τ).shift
        (.papp (Y.isub σ).dshift (.var 0)) := by
    show Tm.split (δ.shift.subst (I.up σ.τ)) (.papp (X.dshift.isub σ.up) (.var 0)) (ψ.shift.subst (I.up σ.τ))
      (.papp (Y.dshift.isub σ.up) (.var 0)) = _
    rw [I_shift_subst_up, I_shift_subst_up, dshift_isub_up, dshift_isub_up]
  rw [e, psys_dinst]

omit hW in
theorem asys_isub (φ1 ψ : I) (X Y : Tm) (σ : ISub k' k) (r : I) :
    ((Tm.split φ1.shift (.papp X.dshift (.neg (.var 0))) ψ.shift Y.dshift).isub σ.up).dinst r =
      .split (φ1.subst σ.τ) (.papp (X.isub σ) (.neg r)) (ψ.subst σ.τ) (Y.isub σ) := by
  have e : (Tm.split φ1.shift (.papp X.dshift (.neg (.var 0))) ψ.shift Y.dshift).isub σ.up =
      .split (φ1.subst σ.τ).shift (.papp (X.isub σ).dshift (.neg (.var 0))) (ψ.subst σ.τ).shift (Y.isub σ).dshift := by
    show Tm.split (φ1.shift.subst (I.up σ.τ)) (.papp (X.dshift.isub σ.up) (.neg (.var 0))) (ψ.shift.subst (I.up σ.τ))
      (Y.dshift.isub σ.up) = _
    rw [I_shift_subst_up, I_shift_subst_up, dshift_isub_up, dshift_isub_up]
  rw [e, asys_dinst]

include hGC in
theorem L_ext {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ)
    (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) :
    RE S k (tgFib A φ T e ψ u0) (tgExt A φ T e ψ u0 δ) := by
  obtain ⟨l, H⟩ := D.tg hW
  have hφ1s : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) := ent_cof_one hW (entails_of_holds hφ1s hφ1)
  have hext := HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hext)
  have hc := L_c hW hGC D hφ1
  unfold Tm.isContr at hc
  rw [tgExt_eq] at hext ⊢
  refine L_fibK hW hGC D hφ1 _ _ _ hext (fun k' σ r hr hh => ?_) (RE_sigma_elim hW hc).1
  have hφ1σ := holds_isub hW hφ1s hφ1 σ
  rw [I_phi1_isub] at hφ1σ
  have hsp := HasTy.isubF hW (show ((cof (cof .one (φ.subst (I.inst0 .one))) (.or δ ψ)).shift).Scoped (k + 1) from
    I.scoped_shift ⟨⟨trivial, hφ1s⟩, D.hδs, H.hψ⟩) (minimal_to_spec H.hpsys) (ISub.cons r hr σ)
  rw [I_shift_cons, dshift_isub_cons, ← isub_up_dinst _ _ _ hr, psys_isub] at hsp
  have hsp' := HasTy.restrict (Φ' := .one) trivial (ent_and_intro (ent_subst hent1 σ.τ)
    (entails_of_holds (I.scoped_subst (show (I.or δ ψ).Scoped k from ⟨D.hδs, H.hψ⟩) σ.sc) hh)) hsp
  rw [psys_isub]
  obtain ⟨hF, hC, hPd, hPpsi, -, -⟩ := tg_isub A φ T e ψ u0 δ σ
  rw [hF, hPd, hPpsi] at hsp' ⊢
  rcases holds_or hh with h1 | h2
  · have e1 := EqTm.splitL (entails_of_holds (I.scoped_subst D.hδs σ.sc) h1) hsp'
    have hP := L_Pd hW hGC (D.isub hW σ) hφ1σ h1
    unfold Tm.pathC at hP
    have := RE_path_elim hW hP r hr
    rw [Meta.dshift_dinst] at this
    exact this.conv hW (TyEq.refl _) e1.symm
  · have e1 := EqTm.splitR (entails_of_holds (I.scoped_subst H.hψ σ.sc) h2) hsp'
    have hP := L_Ppsi hW hGC (D.isub hW σ) hφ1σ h2
    unfold Tm.pathC at hP
    have := RE_path_elim hW hP r hr
    rw [Meta.dshift_dinst] at this
    exact this.conv hW (TyEq.refl _) e1.symm

include hGC in
theorem L_a1 {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) :
    RE S k (A.dinst .one) (tgA1 A φ T e ψ u0 δ) := by
  obtain ⟨l, H⟩ := D.tg hW
  obtain ⟨hAc, -, -⟩ := D.closed hW
  have hφ1s : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have KA := (D.gl.slice hW .one trivial).kA.1 k (ISub.id k)
  rw [isub_id_of_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial)))] at KA
  rw [tgA1_eq]
  refine KA _ _ _ (by have := minimal_to_spec H.ha1; rwa [tgA1_eq] at this) (fun k' σ r hr hh => ?_) (L_a1' hW hGC D)
  have hsp := HasTy.isubF hW (show ((cof .one (.or (φ.subst (I.inst0 .one)) ψ)).shift).Scoped (k + 1) from
    I.scoped_shift ⟨trivial, hφ1s, H.hψ⟩) (minimal_to_spec H.hasys) (ISub.cons r hr σ)
  rw [I_shift_cons, dshift_isub_cons, ← isub_up_dinst _ _ _ hr, asys_isub] at hsp
  have hsp' := HasTy.restrict (Φ' := .one) trivial (ent_cof_one hW
    (entails_of_holds (I.scoped_subst (show (I.or (φ.subst (I.inst0 .one)) ψ).Scoped k from ⟨hφ1s, H.hψ⟩) σ.sc) hh)) hsp
  rw [asys_isub]
  rcases holds_or hh with h1 | h2
  · have e1 := EqTm.splitL (entails_of_holds (I.scoped_subst hφ1s σ.sc) h1) hsp'
    have hφ1σ := h1
    rw [I_phi1_isub] at hφ1σ
    have hE := L_ext hW hGC (D.isub hW σ) hφ1σ
    rw [tgFib_eq] at hE
    have h2 := (RE_sigma_elim hW hE).2
    rw [P_inst] at h2
    unfold Tm.pathC at h2
    have h3 := RE_path_elim hW h2 (.neg r) hr
    rw [Meta.dshift_dinst, ← dinst_isub_end _ (.inr rfl)] at h3
    obtain ⟨-, -, -, -, hX, -⟩ := tg_isub A φ T e ψ u0 δ σ
    have hsnd : (Tm.snd (tgExt A φ T e ψ u0 δ)).isub σ = .snd ((tgExt A φ T e ψ u0 δ).isub σ) := rfl
    rw [hsnd, hX] at e1 ⊢
    exact h3.conv hW (TyEq.refl _) e1.symm
  · have e1 := EqTm.splitR (entails_of_holds (I.scoped_subst H.hψ σ.sc) h2) hsp'
    exact (L_a1'_isub hW hGC D σ).conv hW (TyEq.refl _) e1.symm

include hGC in
/-- Transport along a computable Glue line. -/
theorem kanT_glue {A T e : Tm} {φ : I} (hD : GlueL S (k + 1) A φ T e) : KanT S k (.glue A φ T e) := by
  intro ψ u0 hty hu0
  by_cases hψ : (ival (idEnv k) ψ).holds
  · exact RE_transp_face hW hty hψ hu0
  obtain ⟨l, hG⟩ := hD.ty
  obtain ⟨hφs, l', hAt, he⟩ := glue_data hW hG
  have hδs := forall0_scoped hφs
  have D : TGD S k A φ T e ψ u0 φ.forall0 := ⟨hD, hty, hu0, hδs, ent_refl _, ent_refl _⟩
  have eq := EqTm.transpGlue hty hAt he hδs (ent_refl _) (ent_refl _)
  rw [transpGlueWith_eq] at eq
  have D1 := hD.slice hW .one trivial
  obtain ⟨l1, hG1⟩ := D1.ty
  have hg := HasTy.eqR eq
  have hφ1s : (φ.subst (I.inst0 .one)).Scoped k := (glue_data hW hG1).1
  by_cases hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds
  · have hE := L_ext hW hGC D hφ1
    rw [tgFib_eq] at hE
    have hT := (RE_sigma_elim hW hE).1
    have hent := entails_of_holds hφ1s hφ1
    have eGT := EqTm.glueFace hent hG1
    have eF := EqTm.glueElFace hent hg
    exact hT.conv hW (TyEq.symm (.inr ⟨l1, eGT⟩)) (eq.trans eF).symm
  · refine (RE_glueEl_intro hW hG1 hφ1 hg (fun k' σ => ?_) (fun k' σ hh => ?_)).conv hW (TyEq.refl _) eq.symm
    · rw [(tg_isub A φ T e ψ u0 φ.forall0 σ).2.2.2.2.2, dinst_isub_end _ (.inr rfl)]
      exact L_a1 hW hGC (D.isub hW σ)
    · rw [I_phi1_isub] at hh
      have hE := L_ext hW hGC (D.isub hW σ) hh
      rw [tgFib_eq] at hE
      have hX := (tg_isub A φ T e ψ u0 φ.forall0 σ).2.2.2.2.1
      rw [show (Tm.fst (tgExt A φ T e ψ u0 φ.forall0)).isub σ = .fst ((tgExt A φ T e ψ u0 φ.forall0).isub σ) from rfl,
        hX, dinst_isub_end _ (.inr rfl)]
      exact (RE_sigma_elim hW hE).1


include hGC in
theorem kanP_glue {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
    (hKA : KR S m A) (ihA : KanP S m A)
    (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → KR S k (dat Tp k f) ∧ KanP S k (dat Tp k f)) :
    KanP S m (glueC m A φ Tp ep) := by
  refine ⟨fun k f T hT => ?_, fun k f T hT => ?_⟩
  · by_cases hf : (φ.restr f).holds
    · rw [Comp_glueC_at hφ hTp hTkv f, if_pos hf] at hT
      exact (ihT k f hf).2.1 k (Hom.id k) T hT
    · obtain ⟨A1, φ1, T1, e1, hE, hD⟩ := glueL_of_comp hW hA hφ hTp hTkv hKA ihA ihT hf hT
      exact kanH_retype hW hE (kanH_glue hW hGC hD)
  · by_cases hf : (φ.restr f).holds
    · rw [Comp_glueC_at hφ hTp hTkv f, if_pos hf] at hT
      exact (ihT (k + 1) f hf).2.2 k (Hom.id (k + 1)) T hT
    · obtain ⟨A1, φ1, T1, e1, hE, hD⟩ := glueL_of_comp hW hA hφ hTp hTkv hKA ihA ihT hf hT
      rcases hE with rfl | ⟨l, e⟩
      · exact kanT_glue hW hGC hD
      · exact kanT_retype hW e (kanT_glue hW hGC hD)

end

end Model.Canon
