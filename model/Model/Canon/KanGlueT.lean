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

section
open Tm
/-- The typings of the parts of `fill` (adapted from `KubusCore.Meta.fill_typed`). -/
theorem fill_parts (hS : SigClosed S) {Ψ Φ Γ C ψ u u0 l}
    (hC : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift C (univ l)) (hψ : ψ.Scoped Ψ)
    (hu : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C) (hu0 : HasTy0 S Ψ Φ Γ u0 (C.dinst .zero))
    (hside : EqTm0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (C.dinst .zero)) :
    HasTy0 S (Ψ + 1 + 1) (cof Φ.shift (.or ψ.shift (.neg (.var 0)))).shift Γ.dshift.dshift (Meta.fillTube ψ u u0)
      (C.dsubst (bind2 (.and (.var 1) (.var 0)))) ∧
    EqTm0 S (Ψ + 1 + 1) (cof (cof Φ.shift (.or ψ.shift (.neg (.var 0)))).shift (.neg (.var 1))) Γ.dshift.dshift
      (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (C.dinst .zero).dshift.dshift (univ l) ∧
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (fill C ψ u u0) ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one) ∧
    EqTm0 S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one) C (univ l) ∧
    EqTm0 S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero)
      (C.dinst .zero).dshift (univ l) := by
  have hw0 := wf_unshift hS (wf_of_ty hC)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hXψs : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  have hL : HasTy0 S (Ψ + 1 + 1) Φ.shift.shift Γ.dshift.dshift
      (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (univ l) := by
    have := HasTy0.isub hS (τ := bind2 (.and (.var 1) (.var 0))) hC
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (ent_bind2_shift _ (ent_refl _))
      (by rw [ctxI_bind2]; exact hw0.dwk2 hS)
    rwa [ctxI_bind2] at this
  let χ : I := .or ψ.shift (.neg (.var 0))
  have hχs : χ.Scoped (Ψ + 1) := ⟨scoped_shift hψ, hv0⟩
  have hΞs : (cof Φ.shift χ).Scoped (Ψ + 1) := ⟨scoped_shift hs, hχs⟩
  have hRs : (cof Φ.shift χ).shift.Scoped (Ψ + 1 + 1) := scoped_shift hΞs
  have hRΦ : I.Entails (cof Φ.shift χ).shift Φ.shift.shift := ent_shift (ent_and_left _ _)
  have hφ2 : ψ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hψ)
  have hLR := HasTy0.restrict hRs hRΦ hL
  -- the tube
  have hR1s : (cof (cof Φ.shift χ).shift ψ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hRs, hφ2⟩
  have hR1Φ : I.Entails (cof (cof Φ.shift χ).shift ψ.shift.shift) (cof Φ ψ).shift.shift :=
    ent_and_mono hRΦ (ent_refl _)
  have hT1 : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift ψ.shift.shift) Γ.dshift.dshift
      (u.dsubst (bind2 (.and (.var 1) (.var 0)))) (C.dsubst (bind2 (.and (.var 1) (.var 0)))) := by
    have := HasTy0.isub hS (τ := bind2 (.and (.var 1) (.var 0))) hu
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (ent_bind2_shift _ hR1Φ)
      (by rw [ctxI_bind2]; exact (hw0.dwk2 hS).restrict hR1s (ent_trans (ent_and_left _ _) hRΦ))
    rwa [ctxI_bind2] at this
  have hR2s : (cof (cof Φ.shift χ).shift (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hRs, hv1⟩
  have hR2Φ : I.Entails (cof (cof Φ.shift χ).shift (.neg (.var 1))) Φ.shift.shift :=
    ent_trans (ent_and_left _ _) hRΦ
  -- under `i = 0` the line is `C(0)`
  have eC0 : EqTm0 S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift (.neg (.var 1))) Γ.dshift.dshift
      (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (C.dinst .zero).dshift.dshift (univ l) := by
    have e1 := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _)
      (HasTy0.restrict hR2s (ent_and_left _ _) hLR)
    rw [tf_L1] at e1
    have e2 := HasTy0.sk2_ieq hS hC (r := .and .zero (.var 0)) (r' := .zero) ⟨trivial, hv0'⟩ trivial
      (I_eq_and_zero _) hR2s hR2Φ
    rw [sk_zero2] at e2
    exact EqTm0.trans e1 e2
  have hT2 : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift (.neg (.var 1))) Γ.dshift.dshift
      u0.dshift.dshift (C.dsubst (bind2 (.and (.var 1) (.var 0)))) :=
    HasTy0.conv (HasTy0.restrict hR2s hR2Φ (HasTy0.dwk hS (HasTy0.dwk hS hu0))) (EqTm0.symm eC0)
  have hR3s : (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
    ⟨hR1s, hv1⟩
  have hover : EqTm0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1)))
      Γ.dshift.dshift (u.dsubst (bind2 (.and (.var 1) (.var 0)))) u0.dshift.dshift
      (C.dsubst (bind2 (.and (.var 1) (.var 0)))) := by
    have hR3e : I.Entails (cof (cof (cof Φ.shift χ).shift ψ.shift.shift) (.neg (.var 1)))
        (cof (cof Φ.shift χ).shift (.neg (.var 1))) :=
      ent_and_mono (ent_and_left _ _) (ent_refl _)
    have eC0' := EqTm0.restrict hR3s hR3e eC0
    have e1 := EqTm0.face (i := 1) (d := false) hv1 (ent_and_right _ _)
      (HasTy0.restrict hR3s (ent_trans hR3e (ent_and_left _ _)) hLR)
      (HasTy0.restrict hR3s (ent_and_left _ _) hT1)
    rw [fillTube_dset1 ψ u u0] at e1
    have e2 := HasTy0.sk2_ieq hS hu (r := .and .zero (.var 0)) (r' := .zero) ⟨trivial, hv0'⟩ trivial
      (I_eq_and_zero _) hR3s (ent_trans (ent_and_left _ _) hR1Φ)
    rw [sk_zero2] at e2
    have eCC := HasTy0.sk2_ieq hS hC (r := .and .zero (.var 0)) (r' := .zero) ⟨trivial, hv0'⟩ trivial
      (I_eq_and_zero _) hR3s (ent_trans hR3e hR2Φ)
    rw [sk_zero2] at eCC
    have e3 := EqTm0.restrict hR3s (ent_trans (ent_and_left _ _) hR1Φ)
      (EqTm0.dwk hS (EqTm0.dwk hS hside))
    exact EqTm0.trans e1 (EqTm0.conv (EqTm0.trans e2 (EqTm0.conv e3 (EqTm0.symm eCC)))
      (EqTm0.trans eCC (EqTm0.symm eC0')))
  have htube : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift (Meta.fillTube ψ u u0)
      (C.dsubst (bind2 (.and (.var 1) (.var 0)))) :=
    HasTy0.split hφ2 hv1 (ent_shift (ent_and_right Φ.shift χ)) hLR hT1 hT2 hover
  -- the base
  have eL0 : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero)
      (C.dinst .zero).dshift (univ l) := by
    rw [tf_L0]
    have e := HasTy0.sk1_ieq hS hC (r := .and (.var 0) .zero) (r' := .zero) ⟨hv0, trivial⟩ trivial
      (I_eq_and_zero_r _) (scoped_shift hs) (ent_refl _)
    rwa [sk_zero1] at e
  have hbase : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift u0.dshift
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero) :=
    HasTy0.conv (HasTy0.dwk hS hu0) (EqTm0.symm eL0)
  -- the side condition
  have htube0 := HasTy0.dsubst hS htube (r := .zero) trivial
  rw [fillTube_d0] at htube0
  have hside' : EqTm0 S (Ψ + 1) (cof Φ.shift χ) Γ.dshift
      (split ψ.shift (u.subst Tm.var (sk (.and (.var 0) .zero) 1)) (.neg (.var 0)) u0.dshift)
      u0.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    refine EqTm0.local (φ := ψ.shift) (ψ := .neg (.var 0)) (scoped_shift hψ) hv0 (ent_and_right _ _)
      htube0 (HasTy0.restrict hΞs (ent_and_left _ _) hbase) ?_ ?_
    · have hX : (cof (cof Φ.shift χ) ψ.shift).Scoped (Ψ + 1) := ⟨hΞs, scoped_shift hψ⟩
      have hXe : I.Entails (cof (cof Φ.shift χ) ψ.shift) (cof Φ ψ).shift :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have e1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) htube0)
      have e2 := HasTy0.sk1_ieq hS hu (r := .and (.var 0) .zero) (r' := .zero) ⟨hv0, trivial⟩ trivial
        (I_eq_and_zero_r _) hX hXe
      rw [sk_zero1] at e2
      have e3 := EqTm0.restrict hX hXe (EqTm0.dwk hS hside)
      have eL0' := EqTm0.restrict hX (ent_trans (ent_and_left _ _) (ent_and_left _ _)) eL0
      rw [tf_L0] at e1 eL0' ⊢
      exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.conv e3 (EqTm0.symm eL0')))
    · have hX : (cof (cof Φ.shift χ) (.neg (.var 0))).Scoped (Ψ + 1) := ⟨hΞs, hv0⟩
      exact EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) htube0)
  have hside'' : EqTm0 S (Ψ + 1) (cof Φ.shift χ) Γ.dshift ((Meta.fillTube ψ u u0).dinst .zero) u0.dshift
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by rw [fillTube_d0]; exact hside'
  have hc := comp_typed hS hL hχs htube hbase hside''
  have eC : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one) C (univ l) := by
    have e := HasTy0.sk1_ieq hS hC (r := .and (.var 0) .one) (r' := .var 0) ⟨hv0, trivial⟩ hv0
      (I_eq_and_one_r _) (scoped_shift hs) (ent_refl _)
    rw [sk_var1] at e
    rw [tf_L1']; exact e
  exact ⟨htube, eC0, hc, eC, eL0⟩

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

theorem L_t1' {A T e u0 : Tm} {φ ψ δ : I} (D : TGD S k A φ T e ψ u0 δ) (hδ : (ival (idEnv k) δ).holds) :
    RE S k (T.dinst .one) (tgT1 T ψ u0) := by
  obtain ⟨l, H⟩ := D.tg hW
  have hent : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have KT := D.gl.kTT k (ISub.id (k + 1)) (D.face_line hW hδ _)
  rw [isub_id_of_closed (D.closed hW).2.1] at KT
  refine KT ψ u0 (HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.ht1)) ?_
  exact D.hu0.conv_ty hW (.inr ⟨l, EqTm.restrict (Φ' := .one) trivial hent
    (minimal_to_spec_eq (H.hGTr (r := .zero) trivial))⟩)

/-- The filler of a heterogeneous composition along a Kan line is computable. -/
theorem RE_fill {C u u0 : Tm} {ψ : I} {l : ℕ} (hC : KanAll S (k + 1) C) (hCt : HasTy S (k + 1) .one [] C (.univ l))
    (hψ : ψ.Scoped k) (hut : HasTy S (k + 1) (cof .one ψ).shift [] u C)
    (hu0t : HasTy S k .one [] u0 (C.dinst .zero)) (hside : EqTm S k (cof .one ψ) [] (u.dinst .zero) u0 (C.dinst .zero))
    (hu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (ψ.subst σ.τ)).holds →
      RE S k' ((C.isub σ.up).dinst r) ((u.isub σ.up).dinst r))
    (hu0 : RE S k (C.dinst .zero) u0) : RE S (k + 1) C (Tm.fill C ψ u u0) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨htube, eC0, hc, eC, eL0⟩ := fill_parts hS (Ψ := k) (Φ := .one) (Γ := []) (spec_to_minimal hW hCt) hψ
    (spec_to_minimal hW hut) (spec_to_minimal hW hu0t) (spec_to_minimal_eq hW hside)
  have hCc := closed_of_ty hW hCt
  have hsc : ∀ i < k + 1, (Tm.bind2 (.and (.var 1) (.var 0)) i).Scoped (k + 1 + 1) := fun i hi => by
    rcases i with _ | i
    · exact ⟨show 1 < k + 1 + 1 by omega, show 0 < k + 1 + 1 by omega⟩
    · show i + 2 < k + 1 + 1; omega
  have hC' : KanAll S (k + 1 + 1) (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))) := by
    have := kanAll_isub hC (ISub.ofFun (k + 1) _ hsc)
    rwa [isub_ofFun hCc] at this
  have hbase : RE S (k + 1) ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) u0.dshift := by
    have := hu0.isub hW (ISub.wk k)
    rw [isub_wk_of_closed (closed_of_ty hW hu0t), isub_wk_of_closed (closed_of_isTyK hW (isTyK_of_ty hW hu0t))] at this
    exact this.conv_ty hW (.inr ⟨l, (minimal_to_spec_eq eL0).symm⟩)
  have r := RE_comp hW hC' (minimal_to_spec hc) ?_ hbase
  · exact r.conv_ty hW (.inr ⟨l, minimal_to_spec_eq eC⟩)
  intro k' σ t ht hh
  have hσ0 : (σ.τ 0).Scoped k' := σ.sc 0 (by omega)
  have hat : (I.and (σ.τ 0) t).Scoped k' := ⟨hσ0, ht⟩
  rw [isub_up_dinst _ _ _ ht, isub_up_dinst _ _ _ ht]
  have hχ : (I.or ψ.shift (.neg (.var 0))).Scoped (k + 1) := ⟨I.scoped_shift hψ, show 0 < k + 1 by omega⟩
  have eT : (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons t ht σ) =
      C.isub (ISub.cons (.and (σ.τ 0) t) hat σ.tail) := by
    simp only [Tm.isub, Tm.dsubst, subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl
  have esp : (Meta.fillTube ψ u u0).isub (ISub.cons t ht σ) =
      .split (ψ.subst σ.tail.τ) (u.isub (ISub.cons (.and (σ.τ 0) t) hat σ.tail)) (.neg (σ.τ 0)) (u0.isub σ.tail) := by
    have e1 : (u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub (ISub.cons t ht σ) =
        u.isub (ISub.cons (.and (σ.τ 0) t) hat σ.tail) := by
      simp only [Tm.isub, Tm.dsubst, subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl
    show Tm.split (ψ.shift.shift.subst (ISub.cons t ht σ).τ) ((u.dsubst _).isub (ISub.cons t ht σ))
      ((I.neg (.var 1)).subst (ISub.cons t ht σ).τ) (u0.dshift.dshift.isub (ISub.cons t ht σ)) = _
    rw [I_shift_cons, I_shift_tail, e1, dshift_isub_cons, dshift_isub_tail]; rfl
  have hsp := HasTy.isubF hW (show (cof (I.one.shift) (I.or ψ.shift (.neg (.var 0)))).shift.Scoped (k + 1 + 1) from
    I.scoped_shift ⟨trivial, hχ⟩) (minimal_to_spec htube) (ISub.cons t ht σ)
  rw [I_shift_cons, esp, eT] at hsp
  have hent : I.Entails .one ((cof (I.one.shift) (I.or ψ.shift (.neg (.var 0)))).subst σ.τ) :=
    ent_cof_one hW (entails_of_holds (I.scoped_subst hχ σ.sc) hh)
  have hsp' := HasTy.restrict (Φ' := .one) trivial hent hsp
  change RE S k' _ ((Meta.fillTube ψ u u0).isub (ISub.cons t ht σ))
  rw [esp, eT]
  rcases holds_or hh with h1 | h2
  · rw [I_shift_tail] at h1
    have e1 := EqTm.splitL (entails_of_holds (I.scoped_subst hψ σ.tail.sc) h1) hsp'
    have := hu k' σ.tail (.and (σ.τ 0) t) hat h1
    rw [isub_up_dinst _ _ _ hat, isub_up_dinst _ _ _ hat] at this
    exact this.conv hW (TyEq.refl _) e1.symm
  · have hn : I.Entails .one (.neg (σ.τ 0)) := entails_of_holds (show (I.neg (σ.τ 0)).Scoped k' from hσ0) h2
    have e1 := EqTm.splitR hn hsp'
    have e2 := EqTm.isubF hW (show (cof (cof (I.one.shift) (I.or ψ.shift (.neg (.var 0)))).shift
      (.neg (.var 1))).Scoped (k + 1 + 1) from ⟨I.scoped_shift ⟨trivial, hχ⟩, show 1 < k + 1 + 1 by omega⟩)
      (minimal_to_spec_eq eC0) (ISub.cons t ht σ)
    have e2' := EqTm.restrict (Φ' := .one) trivial (ent_and_intro (by rw [I_shift_cons]; exact hent) hn) e2
    rw [eT, dshift_isub_cons, dshift_isub_tail] at e2'
    exact (hu0.isub hW σ.tail).conv hW (.inr ⟨l, e2'.symm⟩) e1.symm

end

end Model.Canon
