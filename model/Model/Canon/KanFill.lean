import Model.Canon.KanPath

/-!
# Canonicity: the filler of heterogeneous composition
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

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

variable (hW : WfSig S)
include hW

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
