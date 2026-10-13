import KubusCore.Meta.KanPath

/-!
# Metatheory: typing of the homogeneous filler `hfill` and of `comp`
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem ctxI_dshift_gen (τ : Nat → I) (Γ : Ctx) : ctxI τ Γ.dshift = ctxI (fun n => τ (n + 1)) Γ := by
  simp only [ctxI, Ctx.dshift, List.map_map]; congr 1; funext t
  simp only [Function.comp, dshift_eq, subst_subst]; rfl

theorem ctxI_add1 (Γ : Ctx) : ctxI (fun n => .var (n + 1)) Γ = Γ.dshift := by
  simp only [ctxI, Ctx.dshift]; congr 1; funext t; rw [dshift_eq]

theorem ctxI_add2 (Γ : Ctx) : ctxI (fun n => .var (n + 2)) Γ = Γ.dshift.dshift := by
  simp only [ctxI, Ctx.dshift, List.map_map]; congr 1; funext t
  simp only [Function.comp, dshift_eq, subst_subst]; rfl

theorem ctxI_id (Γ : Ctx) : ctxI I.var Γ = Γ := by
  simp only [ctxI]; conv => rhs; rw [← List.map_id Γ]
  congr 1; funext t; exact subst_var t

theorem I_shift_subst (Φ : I) (τ : Nat → I) : Φ.shift.subst τ = Φ.subst (fun n => τ (n + 1)) := by
  simp only [I.shift, I.ren, I_subst_subst]; rfl

theorem I_add2 (Φ : I) : Φ.subst (fun n => .var (n + 2)) = Φ.shift.shift := by
  simp only [I.shift, I.ren, I_subst_subst]; rfl

theorem I_add1 (Φ : I) : Φ.subst (fun n => .var (n + 1)) = Φ.shift := rfl

/-- `bind2 r`: the line variable to `r`, skipping the new variable 1. -/
theorem bind2_succ (r : I) (n : Nat) : bind2 r (n + 1) = .var (n + 2) := rfl

theorem ctxI_bind2 (r : I) (Γ : Ctx) : ctxI (bind2 r) Γ.dshift = Γ.dshift.dshift := by
  rw [ctxI_dshift_gen]; exact ctxI_add2 Γ

theorem ent_bind2_shift {X Φ : I} (r : I) (h : I.Entails X Φ.shift.shift) :
    I.Entails X (Φ.shift.subst (bind2 r)) := by
  have e : (fun n => bind2 r (n + 1)) = (fun n => I.var (n + 2)) := rfl
  rw [I_shift_subst, e, I_add2]; exact h

theorem dshift_bind2 (A : Tm) (r : I) : A.dshift.subst Tm.var (bind2 r) = A.dshift.dshift := by
  ssub

/-- The tube of `hfill`: `[φ ↦ k. u(i ∧ k), i = 0 ↦ u0]`. -/
def fillTube (φ : I) (u u0 : Tm) : Tm :=
  split φ.shift.shift (u.dsubst (bind2 (.and (.var 1) (.var 0)))) (.neg (.var 1)) u0.dshift.dshift

theorem hfill_eq (A : Tm) (φ : I) (u u0 : Tm) :
    hfill A φ u u0 = hcomp A.dshift (.or φ.shift (.neg (.var 0))) (fillTube φ u u0) u0.dshift := rfl

theorem fillTube_dinst0 (φ : I) (u u0 : Tm) :
    (fillTube φ u u0).dinst .zero =
      split φ.shift (u.subst Tm.var (fun n => match n with | 0 => .and (.var 0) .zero | n + 1 => .var (n + 1)))
        (.neg (.var 0)) u0.dshift := by
  simp only [fillTube, Tm.dinst, Tm.dsubst, Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; rfl
  · ssub
  · ssub

theorem sk_succ (r : I) (k n : Nat) : sk r k (n + 1) = .var (n + k) := rfl

theorem ctxI_sk1 (r : I) (Γ : Ctx) : ctxI (sk r 1) Γ.dshift = Γ.dshift := by
  rw [ctxI_dshift_gen]; exact ctxI_add1 Γ
theorem ctxI_sk2 (r : I) (Γ : Ctx) : ctxI (sk r 2) Γ.dshift = Γ.dshift.dshift := by
  rw [ctxI_dshift_gen]; exact ctxI_add2 Γ
theorem ctxI_sk0 (r : I) (Γ : Ctx) : ctxI (sk r 0) Γ.dshift = Γ := by
  rw [ctxI_dshift_gen]; exact ctxI_id Γ

theorem ent_sk1 {X Φ : I} (r : I) (h : I.Entails X Φ.shift) : I.Entails X (Φ.shift.subst (sk r 1)) := by
  rw [I_shift_subst]; exact h
theorem ent_sk2 {X Φ : I} (r : I) (h : I.Entails X Φ.shift.shift) :
    I.Entails X (Φ.shift.subst (sk r 2)) := by
  have e : (fun n => sk r 2 (n + 1)) = (fun n => I.var (n + 2)) := rfl
  rw [I_shift_subst, e, I_add2]; exact h
theorem ent_sk0 {X Φ : I} (r : I) (h : I.Entails X Φ) : I.Entails X (Φ.shift.subst (sk r 0)) := by
  rw [I_shift_subst]; simpa [sk, I_subst_var] using h

theorem dshift_sk (A : Tm) (r : I) (k : Nat) : A.dshift.subst Tm.var (sk r k) = A.subst Tm.var (fun n => .var (n + k)) := by
  rw [dshift_subst]; rfl

theorem subst_add1 (A : Tm) : A.subst Tm.var (fun n => .var (n + 1)) = A.dshift := (dshift_eq A).symm
theorem subst_add2 (A : Tm) : A.subst Tm.var (fun n => .var (n + 2)) = A.dshift.dshift := by ssub
theorem subst_add0 (A : Tm) : A.subst Tm.var (fun n => .var (n + 0)) = A := subst_var A

theorem sk_scoped {r : I} {Ψ Ψ' k : Nat} (hr : r.Scoped Ψ') (hk : Ψ + k ≤ Ψ') :
    ∀ i < Ψ + 1, (sk r k i).Scoped Ψ' := by
  intro i hi; rcases i with _ | i
  · exact hr
  · show i + k < Ψ'; omega

theorem ieq_sk {r r' : I} (h : I.Eq r r') (k : Nat) : ∀ i < Ψ + 1, I.Eq (sk r k i) (sk r' k i) := by
  intro i _; rcases i with _ | i
  · exact h
  · exact I_eq_refl _

theorem I_eq_and_zero (r : I) : I.Eq (.and .zero r) .zero := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_and_one_l (r : I) : I.Eq (.and .one r) r := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_and_one_r (r : I) : I.Eq (.and r .one) r := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_and_zero_r (r : I) : I.Eq (.and r .zero) .zero := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_or_one_l (r : I) : I.Eq (.or .one r) .one := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_or_zero_r (r : I) : I.Eq (.or r .zero) r := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_or_zero_l (r : I) : I.Eq (.or .zero r) r := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl
theorem I_eq_or_one_r (r : I) : I.Eq (.or r .one) .one := fun ρ => by
  cases h : r.eval ρ <;> simp [I.eval, h] <;> rfl

theorem sk_var1 (u : Tm) : u.subst Tm.var (sk (.var 0) 1) = u := by ssub
theorem sk_zero1 (u : Tm) : u.subst Tm.var (sk .zero 1) = (u.dinst .zero).dshift := by ssub
theorem sk_zero2 (u : Tm) : u.subst Tm.var (sk .zero 2) = (u.dinst .zero).dshift.dshift := by ssub
theorem sk_zero0 (u : Tm) : u.subst Tm.var (sk .zero 0) = u.dinst .zero := by ssub

theorem fillTube_dset1 (φ : I) (u u0 : Tm) :
    (u.dsubst (bind2 (.and (.var 1) (.var 0)))).dset 1 (I.ofDir false) =
      u.subst Tm.var (sk (.and .zero (.var 0)) 2) := by ssub

theorem fillTube_d0 (φ : I) (u u0 : Tm) :
    (fillTube φ u u0).dinst .zero =
      split φ.shift (u.subst Tm.var (sk (.and (.var 0) .zero) 1)) (.neg (.var 0)) u0.dshift := by
  simp only [fillTube, Tm.dinst, Tm.dsubst, Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; rfl
  · ssub
  · ssub

theorem fillTube_d1 (φ : I) (u u0 : Tm) :
    (fillTube φ u u0).dinst .one =
      split φ.shift (u.subst Tm.var (sk (.and (.var 0) .one) 1)) (.neg (.var 0)) u0.dshift := by
  simp only [fillTube, Tm.dinst, Tm.dsubst, Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; rfl
  · ssub
  · ssub

theorem fillTube_end (φ : I) (u u0 : Tm) :
    (fillTube φ u u0).subst Tm.var (endS false) =
      split φ (u.subst Tm.var (sk (.and .zero .one) 0)) (.neg .zero) u0 := by
  simp only [fillTube, Tm.subst]
  congr 1
  · exact shift2_endS φ false
  · ssub
  · ssub

theorem fillTube_up1 (φ : I) (u u0 : Tm) :
    (fillTube φ u u0).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .one)) =
      split φ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift := by
  simp only [fillTube, Tm.subst]
  congr 1
  · simp only [I.shift, I.ren, I_subst_subst]; rfl
  · ssub
  · ssub

theorem dsub_end0 (X : Tm) :
    (X.subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .zero))).dinst .one = X.subst Tm.var (endS false) :=
  dsub_end X false
theorem dsub_end1 (X : Tm) :
    (X.subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .one))).dinst .one = X.subst Tm.var (endS true) :=
  dsub_end X true

theorem fillR_up1 (Φ φ : I) :
    ((cof Φ.shift (.or φ.shift (.neg (.var 0)))).shift).subst (I.up (I.inst0 .one)) =
      (cof Φ (.or φ (.neg .one))).shift := by
  simp only [I.shift, I.ren, I.subst, I_subst_subst]; rfl

theorem fillTube_up1' (φ : I) (u u0 : Tm) :
    (fillTube φ u u0).subst Tm.var (I.up (I.inst0 .one)) =
      split φ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift :=
  fillTube_up1 φ u u0

theorem ctxI_up_inst0 (r : I) (Γ : Ctx) : ctxI (I.up (I.inst0 r)) Γ.dshift.dshift = Γ.dshift := by
  rw [ctxI_dshift_gen, ctxI_dshift_gen]; exact ctxI_add1 Γ

theorem dshift2_up_inst0 (A : Tm) (r : I) : A.dshift.dshift.subst Tm.var (I.up (I.inst0 r)) = A.dshift := by
  ssub

theorem hfill_d1_eq (A : Tm) (φ : I) (T u0 : Tm) :
    (hcomp A.dshift (.or φ.shift (.neg (.var 0))) T u0.dshift).dinst .one =
      hcomp A (.or φ (.neg .one)) (T.subst Tm.var (I.up (I.inst0 .one))) u0 := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst]
  rw [show A.dshift.subst Tm.var (I.inst0 .one) = A from dshift_dinst A .one,
    show u0.dshift.subst Tm.var (I.inst0 .one) = u0 from dshift_dinst u0 .one]
  congr 1
  simp only [I.subst, I.shift, I.ren, I_subst_subst]
  rw [show (fun i => I.inst0 I.one i.succ) = I.var from rfl, I_subst_var]; rfl

theorem dshift2_endS (A : Tm) (d : Bool) : A.dshift.dshift.subst Tm.var (endS d) = A := by ssub

theorem ent_neg_one (φ : I) : I.Entails (.or φ (.neg .one)) φ :=
  ent_or_elim (ent_refl _) (ent_of_sem fun _ _ h => by cases h)

/-- Typing of the homogeneous filler and its boundary. -/
theorem hfill_typed (hS : SigClosed S) {Ψ Φ Γ A φ u u0 l} (hA : HasTy0 S Ψ Φ Γ A (univ l))
    (hφ : φ.Scoped Ψ) (hu : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift)
    (hu0 : HasTy0 S Ψ Φ Γ u0 A) (hside : EqTm0 S Ψ (cof Φ φ) Γ (u.dinst .zero) u0 A) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (hfill A φ u u0) A.dshift ∧
    EqTm0 S Ψ Φ Γ ((hfill A φ u u0).dinst .zero) u0 A ∧
    EqTm0 S Ψ Φ Γ ((hfill A φ u u0).dinst .one) (hcomp A φ u u0) A ∧
    EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (hfill A φ u u0) u A.dshift := by
  have hs := scoped_of_ty hA
  have hw0 := wf_of_ty hA
  have hA1 := HasTy0.dwk hS hA
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  let χ : I := .or φ.shift (.neg (.var 0))
  have hχs : χ.Scoped (Ψ + 1) := ⟨scoped_shift hφ, hv0⟩
  have hΞs : (cof Φ.shift χ).Scoped (Ψ + 1) := ⟨scoped_shift hs, hχs⟩
  have hRs : (cof Φ.shift χ).shift.Scoped (Ψ + 1 + 1) := scoped_shift hΞs
  have hRΦ : I.Entails (cof Φ.shift χ).shift Φ.shift.shift := ent_shift (ent_and_left Φ.shift χ)
  have hφ2 : φ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hφ)
  have hA2 : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift A.dshift.dshift (univ l) :=
    HasTy0.restrict hRs hRΦ (HasTy0.dwk hS hA1)
  -- the tube
  have hR1s : (cof (cof Φ.shift χ).shift φ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hRs, hφ2⟩
  have hR1Φ : I.Entails (cof (cof Φ.shift χ).shift φ.shift.shift) (cof Φ φ).shift.shift :=
    ent_and_mono hRΦ (ent_refl _)
  have hT1 : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift φ.shift.shift) Γ.dshift.dshift
      (u.dsubst (bind2 (.and (.var 1) (.var 0)))) A.dshift.dshift := by
    have := HasTy0.isub hS (τ := bind2 (.and (.var 1) (.var 0))) hu
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (show I.Entails _ (.and _ _) from ent_and_intro (ent_bind2_shift _ (ent_trans (ent_and_left _ _) hRΦ))
        (ent_bind2_shift _ (ent_and_right _ _)))
      (by rw [ctxI_bind2]; exact hw0.dwk2 hS |>.restrict hR1s (ent_trans (ent_and_left _ _) hRΦ))
    rwa [ctxI_bind2, dshift_bind2] at this
  have hR2s : (cof (cof Φ.shift χ).shift (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hRs, hv1⟩
  have hT2 : HasTy0 S (Ψ + 1 + 1) (cof (cof Φ.shift χ).shift (.neg (.var 1))) Γ.dshift.dshift
      u0.dshift.dshift A.dshift.dshift :=
    HasTy0.restrict hR2s (ent_trans (ent_and_left _ _) hRΦ) (HasTy0.dwk hS (HasTy0.dwk hS hu0))
  have hR3s : (cof (cof (cof Φ.shift χ).shift φ.shift.shift) (.neg (.var 1))).Scoped (Ψ + 1 + 1) :=
    ⟨hR1s, hv1⟩
  have hover : EqTm0 S (Ψ + 1 + 1) (cof (cof (cof Φ.shift χ).shift φ.shift.shift) (.neg (.var 1)))
      Γ.dshift.dshift (u.dsubst (bind2 (.and (.var 1) (.var 0)))) u0.dshift.dshift A.dshift.dshift := by
    have e1 := EqTm0.face (i := 1) (d := false) hv1 (ent_and_right _ _)
      (HasTy0.restrict hR3s (ent_trans (ent_and_left _ _) (ent_and_left _ _)) hA2)
      (HasTy0.restrict hR3s (ent_and_left _ _) hT1)
    rw [fillTube_dset1 φ u u0] at e1
    have e2 := HasTy0.ieq hS (Φ' := cof (cof (cof Φ.shift χ).shift φ.shift.shift) (.neg (.var 1)))
      (τ1 := sk (.and .zero (.var 0)) 2) (τ2 := sk .zero 2) hu
      (sk_scoped ⟨trivial, hv0'⟩ (by omega)) (sk_scoped trivial (by omega))
      (show I.Entails _ (.and _ _) from ent_and_intro
        (ent_sk2 _ (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hRΦ)))
        (ent_sk2 _ (ent_trans (ent_and_left _ _) (ent_and_right _ _))))
      (show I.Entails _ (.and _ _) from ent_and_intro
        (ent_sk2 _ (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hRΦ)))
        (ent_sk2 _ (ent_trans (ent_and_left _ _) (ent_and_right _ _))))
      (ieq_sk (I_eq_and_zero _) 2) (by rw [ctxI_sk2, ctxI_sk2])
      (by rw [ctxI_sk2]; exact (hw0.dwk2 hS).restrict hR3s
            (ent_trans (ent_and_left _ _) (ent_trans (ent_and_left _ _) hRΦ)))
    rw [ctxI_sk2, dshift_sk, subst_add2, sk_zero2] at e2
    have e3 := EqTm0.restrict hR3s (ent_trans (ent_and_left _ _) hR1Φ)
      (EqTm0.dwk hS (EqTm0.dwk hS hside))
    exact EqTm0.trans e1 (EqTm0.trans e2 e3)
  have htube : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift (fillTube φ u u0)
      A.dshift.dshift :=
    HasTy0.split hφ2 hv1 (ent_shift (ent_and_right Φ.shift χ)) hA2 hT1 hT2 hover
  -- the base and the side condition
  have hbase := HasTy0.dwk hS hu0
  have htube0 := HasTy0.dsubst hS htube (r := .zero) trivial
  rw [dshift_dinst, fillTube_d0] at htube0
  have hu1 : ∀ {X : I} {r : I}, X.Scoped (Ψ + 1) → I.Entails X (cof Φ φ).shift → r.Scoped (Ψ + 1) →
      I.Eq r (.var 0) →
      EqTm0 S (Ψ + 1) X Γ.dshift (u.subst Tm.var (sk r 1)) u A.dshift := by
    intro X r hX hXe hr he
    have := HasTy0.ieq hS (Φ' := X) (τ1 := sk r 1) (τ2 := sk (.var 0) 1) hu
      (sk_scoped hr (by omega)) (sk_scoped hv0 (by omega))
      (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
        (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
      (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
        (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
      (ieq_sk he 1) (by rw [ctxI_sk1, ctxI_sk1])
      (by rw [ctxI_sk1]; exact (wf_of_ty hu).restrict hX hXe)
    rwa [ctxI_sk1, dshift_sk, subst_add1, sk_var1] at this
  have hside' : EqTm0 S (Ψ + 1) (cof Φ.shift χ) Γ.dshift
      (split φ.shift (u.subst Tm.var (sk (.and (.var 0) .zero) 1)) (.neg (.var 0)) u0.dshift)
      u0.dshift A.dshift := by
    refine EqTm0.local (φ := φ.shift) (ψ := .neg (.var 0)) (scoped_shift hφ) hv0 (ent_and_right _ _)
      htube0 (HasTy0.restrict hΞs (ent_and_left _ _) hbase) ?_ ?_
    · have hX : (cof (cof Φ.shift χ) φ.shift).Scoped (Ψ + 1) := ⟨hΞs, scoped_shift hφ⟩
      have hXe : I.Entails (cof (cof Φ.shift χ) φ.shift) (cof Φ φ).shift :=
        ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
      have e1 := EqTm0.splitL (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) htube0)
      have e2 := HasTy0.ieq hS (Φ' := cof (cof Φ.shift χ) φ.shift) (τ1 := sk (.and (.var 0) .zero) 1)
        (τ2 := sk .zero 1) hu (sk_scoped ⟨hv0, trivial⟩ (by omega)) (sk_scoped trivial (by omega))
        (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
          (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
        (show I.Entails _ (.and _ _) from ent_and_intro (ent_sk1 _ (ent_trans hXe (ent_and_left _ _)))
          (ent_sk1 _ (ent_trans hXe (ent_and_right _ _))))
        (ieq_sk (I_eq_and_zero_r _) 1) (by rw [ctxI_sk1, ctxI_sk1])
        (by rw [ctxI_sk1]; exact (wf_of_ty hu).restrict hX hXe)
      rw [ctxI_sk1, dshift_sk, subst_add1, sk_zero1] at e2
      have e3 := EqTm0.restrict hX hXe (EqTm0.dwk hS hside)
      exact EqTm0.trans e1 (EqTm0.trans e2 e3)
    · have hX : (cof (cof Φ.shift χ) (.neg (.var 0))).Scoped (Ψ + 1) := ⟨hΞs, hv0⟩
      have e1 := EqTm0.splitR (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) htube0)
      exact e1
  have hfT : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (hfill A φ u u0) A.dshift := by
    rw [hfill_eq]
    refine HasTy0.hcomp hA1 hχs htube hbase ?_
    rw [fillTube_d0]; exact hside'
  refine ⟨hfT, ?_, ?_, ?_⟩
  · -- the endpoint 0
    have hd := HasTy0.dsubst hS hfT (r := .zero) trivial
    rw [hfill_eq] at hd
    have e1 := EqTm0.hcompFace (ent_trans (ent_negzero Φ) (ent_or_right _ _)) hd
    rw [dsub_end0, fillTube_end] at e1
    have hE := HasTy0.isub hS (τ := endS false) htube (endS_scoped Ψ false)
      (ent_and_intro (ent_shift2_endS Φ false) (ent_trans (ent_negzero Φ) (ent_or_right _ _)))
      (by rw [ctxI_endS]; exact hw0)
    rw [ctxI_endS, dshift2_endS, fillTube_end] at hE
    have e2 := EqTm0.splitR (ent_negzero Φ) hE
    have hAA : EqTm0 S Ψ Φ Γ A (A.dshift.dinst .zero) (univ l) := by rw [dshift_dinst]; exact EqTm0.refl hA
    rw [hfill_eq]
    exact EqTm0.conv (EqTm0.trans e1 (EqTm0.conv e2 hAA)) (EqTm0.symm hAA)
  · -- the endpoint 1
    have hd := HasTy0.dsubst hS hfT (r := .one) trivial
    rw [hfill_eq] at hd
    have hc := HasTy0.hcomp hA hφ hu hu0 hside
    have hX : (cof Φ (.or φ (.neg .one))).Scoped Ψ := ⟨hs, ⟨hφ, trivial⟩⟩
    have hXe : I.Entails (cof Φ (.or φ (.neg .one))).shift (cof Φ φ).shift :=
      ent_shift (ent_and_mono (ent_refl _) (ent_neg_one φ))
    have hXs : (cof Φ (.or φ (.neg .one))).shift.Scoped (Ψ + 1) := scoped_shift hX
    have htu : EqTm0 S (Ψ + 1) (cof Φ (.or φ (.neg .one))).shift Γ.dshift
        (split φ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift) u
        (A.dshift.dinst .one).dshift := by
      rw [dshift_dinst]
      have htyped := HasTy0.isub hS (τ := I.up (I.inst0 .one)) (Φ' := (cof Φ (.or φ (.neg .one))).shift)
        htube (Iup_scoped (fun i hi => by
          rcases i with _ | i
          · trivial
          · exact show i < Ψ by omega))
        (by rw [fillR_up1]; exact ent_refl _)
        (by rw [ctxI_up_inst0]; exact (Wf0.dwk hS hw0).restrict hXs (ent_shift (ent_and_left _ _)))
      rw [ctxI_up_inst0, dshift2_up_inst0, fillTube_up1'] at htyped
      have e1 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_neg_one φ))) htyped
      exact EqTm0.trans e1 (hu1 hXs hXe ⟨trivial, hv0⟩ (I_eq_and_one_l _))
    rw [hfill_d1_eq] at hd
    rw [hfill_eq, hfill_d1_eq]
    rw [dshift_dinst] at hd htu
    rw [fillTube_up1'] at hd ⊢
    exact EqTm0.hcomp hd hc (EqTm0.refl hA) (ent_neg_one φ) (ent_or_left _ _) htu (EqTm0.refl hu0)
  · -- under `φ` the filler is the tube
    have hs' : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ⟩
    have hφφ : I.Entails (cof Φ φ).shift φ.shift := ent_shift (ent_and_right Φ φ)
    have hf' := HasTy0.restrict hs' (ent_shift (ent_and_left Φ φ)) hfT
    rw [hfill_eq] at hf' ⊢
    have e1 := EqTm0.hcompFace (ent_trans hφφ (ent_or_left _ _)) hf'
    have ht1 := HasTy0.dsubst hS (Φ := cof Φ.shift χ) (Γ := Γ.dshift) htube (r := .one) trivial
    rw [dshift_dinst] at ht1
    have ht1' := HasTy0.restrict hs'
      (ent_and_intro (ent_shift (ent_and_left Φ φ)) (ent_trans hφφ (ent_or_left _ _))) ht1
    rw [fillTube_d1] at e1 ht1'
    have e2 := EqTm0.splitL hφφ ht1'
    exact EqTm0.trans e1 (EqTm0.trans e2 (hu1 hs' (ent_refl _) ⟨hv0, trivial⟩ (I_eq_and_one_r _)))

/-! ## `comp` -/

theorem ctxI_skk (r : I) (k : Nat) (Γ : Ctx) : ctxI (sk r k) Γ.dshift = ctxI (fun n => .var (n + k)) Γ := by
  rw [ctxI_dshift_gen]; rfl

theorem ent_skk {X Φ : I} (r : I) (k : Nat) (h : I.Entails X (Φ.subst (fun n => .var (n + k)))) :
    I.Entails X (Φ.shift.subst (sk r k)) := by
  rw [I_shift_subst]; exact h

/-- Interval functionality of a line in its line variable. -/
theorem line_ieq (hS : SigClosed S) {Ψ : Nat} {Φ : I} {Γ : Ctx} {C T : Tm} (hC : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift C T) {k : Nat}
    {X r r' : I} {Ψ' : Nat} (hX : I.Entails X (Φ.subst (fun n => .var (n + k)))) (hr : r.Scoped Ψ')
    (hr' : r'.Scoped Ψ') (hk : Ψ + k ≤ Ψ') (he : I.Eq r r')
    (hw : Wf0 S Ψ' X (ctxI (fun n => .var (n + k)) Γ)) :
    EqTm0 S Ψ' X (ctxI (fun n => .var (n + k)) Γ) (C.subst Tm.var (sk r k)) (C.subst Tm.var (sk r' k))
      (T.subst Tm.var (sk r k)) := by
  have := HasTy0.ieq hS (Φ' := X) (τ1 := sk r k) (τ2 := sk r' k) hC (sk_scoped hr hk) (sk_scoped hr' hk)
    (ent_skk _ _ hX) (ent_skk _ _ hX) (ieq_sk he k) (by rw [ctxI_skk, ctxI_skk]) (by rw [ctxI_skk]; exact hw)
  rwa [ctxI_skk] at this

theorem L_dset11 (C : Tm) :
    (C.dsubst (bind2 (.or (.var 1) (.var 0)))).dset 1 (I.ofDir true) = C.subst Tm.var (sk (.or .one (.var 0)) 2) := by
  ssub
theorem L_d0_dshift (C : Tm) :
    ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .zero).dshift = C.subst Tm.var (sk (.or (.var 1) .zero) 2) := by
  ssub
theorem sk_dset11 (C : Tm) :
    (C.subst Tm.var (sk (.or (.var 1) .zero) 2)).dset 1 (I.ofDir true) = C.subst Tm.var (sk (.or .one .zero) 2) := by
  ssub
theorem L_d0 (C : Tm) : (C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .zero = C.subst Tm.var (sk (.or (.var 0) .zero) 1) := by
  ssub
theorem L_d1 (C : Tm) : (C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .one = C.subst Tm.var (sk (.or (.var 0) .one) 1) := by
  ssub
theorem sk_one1 (C : Tm) : C.subst Tm.var (sk .one 1) = (C.dinst .one).dshift := by ssub
theorem sk_one0 (C : Tm) : C.subst Tm.var (sk .one 0) = C.dinst .one := by ssub
theorem L_up0 (C : Tm) :
    (C.dsubst (bind2 (.or (.var 1) (.var 0)))).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .zero)) =
      C.subst Tm.var (sk (.or .zero (.var 0)) 1) := by ssub
theorem sk1_d0 (C : Tm) (r : I) :
    (C.subst Tm.var (sk (.or r (.var 0)) 1)).dinst .zero = C.subst Tm.var (sk (.or (r.subst (I.inst0 .zero)) .zero) 0) := by
  ssub
theorem sk1_d1 (C : Tm) (r : I) :
    (C.subst Tm.var (sk (.or r (.var 0)) 1)).dinst .one = C.subst Tm.var (sk (.or (r.subst (I.inst0 .one)) .one) 0) := by
  ssub
theorem tube_d0 (C u : Tm) :
    (transp (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u).dinst .zero =
      transp (C.subst Tm.var (sk (.or .zero (.var 0)) 1)) .zero (u.dinst .zero) := by
  show transp ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).subst (fun n => (Tm.var n).dshift)
    (I.up (I.inst0 .zero))) ((I.var 0).subst (I.inst0 .zero)) (u.dinst .zero) = _
  rw [L_up0]; rfl

theorem L_d1_d0 (C : Tm) :
    ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .one).dinst .zero =
      C.subst Tm.var (sk (.or .zero .one) 0) := by ssub
theorem sk1_d1z (C : Tm) :
    (C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .one = C.subst Tm.var (sk (.or .zero .one) 0) := by ssub
theorem sk1_d0z (C : Tm) :
    (C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .zero = C.subst Tm.var (sk (.or .zero .zero) 0) := by ssub
theorem dsubst_eq_subst (C : Tm) (τ : Nat → I) : C.dsubst τ = C.subst Tm.var τ := rfl

theorem ctxI_add0 (Γ : Ctx) : ctxI (fun n => .var (n + 0)) Γ = Γ := ctxI_id Γ
theorem I_add0 (Φ : I) : Φ.subst (fun n => .var (n + 0)) = Φ := I_subst_var Φ

/-- Typing of heterogeneous composition. -/
theorem comp_typed (hS : SigClosed S) {Ψ Φ Γ C ψ u u0 l}
    (hC : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift C (univ l)) (hψ : ψ.Scoped Ψ)
    (hu : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C) (hu0 : HasTy0 S Ψ Φ Γ u0 (C.dinst .zero))
    (hside : EqTm0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (C.dinst .zero)) :
    HasTy0 S Ψ Φ Γ (comp C ψ u u0) (C.dinst .one) := by
  have hw0 := wf_unshift hS (wf_of_ty hC)
  have hs := scoped_of_wf hw0
  have hC1 := HasTy0.dsubst hS hC (r := .one) trivial
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hXs : (cof Φ ψ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hψ⟩
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left Φ ψ)
  -- the line of the tube's transports
  have hL : HasTy0 S (Ψ + 1 + 1) (cof Φ ψ).shift.shift Γ.dshift.dshift
      (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (univ l) := by
    have := HasTy0.isub hS (τ := bind2 (.or (.var 1) (.var 0))) hC
      (fun i hi => by rcases i with _ | i
                      · exact ⟨hv1, hv0'⟩
                      · show i + 2 < Ψ + 1 + 1; omega)
      (ent_bind2_shift _ (ent_shift hXΦ))
      (by rw [ctxI_bind2]; exact (hw0.dwk2 hS).restrict (scoped_shift hXs) (ent_shift hXΦ))
    rwa [ctxI_bind2] at this
  have hYs : (cof (cof Φ ψ).shift (.var 0)).shift.Scoped (Ψ + 1 + 1) := scoped_shift ⟨hXs, hv0⟩
  have hYX : I.Entails (cof (cof Φ ψ).shift (.var 0)).shift (cof Φ ψ).shift.shift :=
    ent_shift (ent_and_left _ _)
  have hY1 : I.Entails (cof (cof Φ ψ).shift (.var 0)).shift (I.lit 1 true) :=
    ent_shift (ent_and_right _ (.var 0))
  have hYΦ : I.Entails (cof (cof Φ ψ).shift (.var 0)).shift (Φ.subst (fun n => .var (n + 2))) := by
    rw [I_add2]; exact ent_trans hYX (ent_shift hXΦ)
  have hwY : Wf0 S (Ψ + 1 + 1) (cof (cof Φ ψ).shift (.var 0)).shift (ctxI (fun n => .var (n + 2)) Γ) := by
    rw [ctxI_add2]; exact (hw0.dwk2 hS).restrict hYs (by rw [← I_add2]; exact hYΦ)
  have hconst : EqTm0 S (Ψ + 1 + 1) (cof (cof Φ ψ).shift (.var 0)).shift Γ.dshift.dshift
      (C.dsubst (bind2 (.or (.var 1) (.var 0))))
      ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .zero).dshift (univ l) := by
    have hLY := HasTy0.restrict hYs hYX hL
    have e1 := EqTm0.faceU (i := 1) (d := true) hv1 hY1 hLY
    rw [L_dset11] at e1
    have e2 := line_ieq hS hC (k := 2) (Ψ' := Ψ + 1 + 1) (r := .or .one (.var 0)) (r' := .one) hYΦ ⟨trivial, hv0'⟩ trivial (by omega) (I_eq_or_one_l _) hwY
    rw [ctxI_add2] at e2
    have hL0 := HasTy0.restrict hYs hYX (HasTy0.dwk hS (HasTy0.dsubst hS (Φ := (cof Φ ψ).shift) (Γ := Γ.dshift) hL (r := .zero) trivial))
    rw [L_d0_dshift] at hL0
    have e3 := EqTm0.faceU (i := 1) (d := true) hv1 hY1 hL0
    rw [sk_dset11] at e3
    have e4 := line_ieq hS hC (k := 2) (Ψ' := Ψ + 1 + 1) (r := .or .one .zero) (r' := .one) hYΦ ⟨trivial, trivial⟩ trivial (by omega) (I_eq_or_one_l _) hwY
    rw [ctxI_add2] at e4
    rw [L_d0_dshift]
    exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.symm (EqTm0.trans e3 e4)))
  -- the tube
  have hwX : Wf0 S (Ψ + 1) (cof Φ ψ).shift (ctxI (fun n => .var (n + 1)) Γ) := by
    rw [ctxI_add1]; exact wf_of_ty hu
  have hu' : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u
      ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).dinst .zero) := by
    rw [L_d0]
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .var 0) (r' := .or (.var 0) .zero) hXΦ hv0
      ⟨hv0, trivial⟩ (by omega) (I_eq_symm (I_eq_or_zero_r _)) hwX
    rw [ctxI_add1, sk_var1] at e
    exact HasTy0.conv hu e
  have ht0 := HasTy0.transp hL hv0 hconst hu'
  have htube : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift
      (transp (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u) (C.dinst .one).dshift := by
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .or (.var 0) .one) (r' := .one) hXΦ
      ⟨hv0, trivial⟩ trivial (by omega) (I_eq_or_one_r _) hwX
    rw [ctxI_add1, sk_one1] at e
    rw [L_d1] at ht0
    exact HasTy0.conv ht0 e
  -- the base
  have hab : I.Entails (cof Φ .zero).shift .zero := ent_shift (ent_and_right Φ .zero)
  have hZs : (cof Φ .zero).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, trivial⟩
  have hb := HasTy0.transp hC (φ := .zero) trivial
    (EqTm0.absurd hab (HasTy0.restrict hZs (ent_shift (ent_and_left _ _)) hC)
      (HasTy0.restrict hZs (ent_shift (ent_and_left _ _)) (HasTy0.dwk hS (HasTy0.dsubst hS hC (r := .zero) trivial))))
    hu0
  -- the side condition
  have hψs : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
  have hwψ : Wf0 S Ψ (cof Φ ψ) (ctxI (fun n => .var (n + 0)) Γ) := by
    rw [ctxI_add0]; exact hw0.restrict hψs (ent_and_left _ _)
  have hψΦ0 : I.Entails (cof Φ ψ) (Φ.subst (fun n => .var (n + 0))) := by rw [I_add0]; exact ent_and_left _ _
  have hside' : EqTm0 S Ψ (cof Φ ψ) Γ
      ((transp (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u).dinst .zero)
      (transp C .zero u0) (C.dinst .one) := by
    rw [tube_d0]
    have h0 := HasTy0.dsubst hS (Φ := cof Φ ψ) (Γ := Γ) ht0 (r := .zero) trivial
    rw [tube_d0, L_d1_d0] at h0
    have eA1 := line_ieq hS hC (k := 0) (Ψ' := Ψ) (r := .or .zero .one) (r' := .one) hψΦ0 ⟨trivial, trivial⟩
      trivial (by omega) (I_eq_or_one_r _) hwψ
    rw [ctxI_add0, sk_one0] at eA1
    have h0' : HasTy0 S Ψ (cof Φ ψ) Γ (transp (C.subst Tm.var (sk (.or .zero (.var 0)) 1)) .zero (u.dinst .zero))
        ((C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .one) := by
      rw [sk1_d1z]; exact h0
    have h1 : HasTy0 S Ψ (cof Φ ψ) Γ (transp C .zero u0) ((C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .one) := by
      rw [sk1_d1z]
      exact HasTy0.conv (HasTy0.restrict hψs (ent_and_left _ _) hb) (EqTm0.symm eA1)
    have h2 := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .or .zero (.var 0)) (r' := .var 0) hXΦ
      ⟨trivial, hv0⟩ hv0 (by omega) (I_eq_or_zero_l _) hwX
    rw [ctxI_add1, sk_var1] at h2
    have eA0 := line_ieq hS hC (k := 0) (Ψ' := Ψ) (r := .zero) (r' := .or .zero .zero) hψΦ0 trivial
      ⟨trivial, trivial⟩ (by omega) (I_eq_symm (I_eq_or_zero_l _)) hwψ
    rw [ctxI_add0, sk_zero0] at eA0
    have h5 : EqTm0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 ((C.subst Tm.var (sk (.or .zero (.var 0)) 1)).dinst .zero) := by
      rw [sk1_d0z]; exact EqTm0.conv hside eA0
    have e := EqTm0.transp h0' h1 h2 (ent_refl _) (ent_refl _) h5
    rw [sk1_d1z] at e
    exact EqTm0.conv e eA1
  exact HasTy0.hcomp hC1 hψ htube hb hside'


end KubusCore.Meta
