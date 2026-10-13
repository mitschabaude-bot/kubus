import KubusCore.Meta.KanU

/-!
# Metatheory: auxiliary lemmas for the contractum of `transp` in Glue types

`∀i. φ` entails every instance of `φ` (Kleene monotonicity), and the boundary, congruence and
filler lemmas for `comp`, `fill` and `transpFill`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## `∀i. φ` entails the instances of `φ` -/

theorem k3_refine_neg : ∀ x y : I.M4, isK3 x → isK3 y → (x = .a ∨ x = y) →
    (x.neg = .a ∨ x.neg = y.neg) := by
  intro x y; cases x <;> cases y <;> decide

theorem k3_refine_meet : ∀ x y x' y' : I.M4, isK3 x → isK3 y → isK3 x' → isK3 y' →
    (x = .a ∨ x = x') → (y = .a ∨ y = y') → (x.meet y = .a ∨ x.meet y = x'.meet y') := by
  intro x y x' y'; cases x <;> cases y <;> cases x' <;> cases y' <;> decide

theorem k3_refine_join : ∀ x y x' y' : I.M4, isK3 x → isK3 y → isK3 x' → isK3 y' →
    (x = .a ∨ x = x') → (y = .a ∨ y = y') → (x.join y = .a ∨ x.join y = x'.join y') := by
  intro x y x' y'; cases x <;> cases y <;> cases x' <;> cases y' <;> decide

/-- Evaluation in the Kleene algebra is monotone in the information order (`a` below `0`, `1`). -/
theorem eval_refine {ρ ρ' : Nat → I.M4} (hρ : K3Asg ρ) (hρ' : K3Asg ρ')
    (h : ∀ i, ρ i = .a ∨ ρ i = ρ' i) : ∀ r : I, r.eval ρ = .a ∨ r.eval ρ = r.eval ρ'
  | .zero => .inr rfl
  | .one => .inr rfl
  | .var i => h i
  | .neg r => k3_refine_neg _ _ (eval_k3 hρ r) (eval_k3 hρ' r) (eval_refine hρ hρ' h r)
  | .and r s => k3_refine_meet _ _ _ _ (eval_k3 hρ r) (eval_k3 hρ s) (eval_k3 hρ' r) (eval_k3 hρ' s)
      (eval_refine hρ hρ' h r) (eval_refine hρ hρ' h s)
  | .or r s => k3_refine_join _ _ _ _ (eval_k3 hρ r) (eval_k3 hρ s) (eval_k3 hρ' r) (eval_k3 hρ' s)
      (eval_refine hρ hρ' h r) (eval_refine hρ hρ' h s)

/-- `δ ⊨ ∀i. φ` gives `δ ⊨ φ(r)`, with the other variables of `φ` shifted by `k`. -/
theorem ent_forall_sk {δ φ : I} (hδ : I.Entails δ φ.forall0) (r : I) (k : Nat) :
    I.Entails (δ.subst (fun n => .var (n + k))) (φ.subst (sk r k)) := by
  refine entails_iff.2 fun ρ hρ h => ?_
  let ρk : Nat → I.M4 := fun n => ρ (n + k)
  have hk : K3Asg ρk := fun n => hρ (n + k)
  rw [eval_subst] at h
  have h1 := (forall0_sem hk φ).1 (entails_iff.1 hδ ρk hk h)
  have hc : K3Asg (consAsg .a ρk) := consAsg_k3 (by decide) hk
  have hτ : K3Asg (fun i => (sk r k i).eval ρ) := fun i => eval_k3 hρ _
  have href := eval_refine hc hτ (fun i => by
    rcases i with _ | i
    · exact .inl rfl
    · exact .inr rfl) φ
  rw [eval_subst]
  rcases href with h2 | h2
  · rw [h1] at h2; cases h2
  · rw [← h2]; exact h1

theorem ent_forall_shift {δ φ : I} (hδ : I.Entails δ φ.forall0) : I.Entails δ.shift φ := by
  have := ent_forall_sk hδ (.var 0) 1
  rwa [I_add1, show φ.subst (sk (.var 0) 1) = φ from by
    rw [show sk (.var 0) 1 = I.var from funext fun i => by rcases i with _ | i <;> rfl, I_subst_var]] at this

theorem ent_forall_inst {δ φ : I} (hδ : I.Entails δ φ.forall0) (r : I) :
    I.Entails δ (φ.subst (I.inst0 r)) := by
  have := ent_forall_sk hδ r 0
  rwa [I_add0, show sk r 0 = I.inst0 r from funext fun i => by rcases i with _ | i <;> rfl] at this

/-! ## `comp` -/

theorem comp_substI (C : Tm) (ψ : I) (u u0 : Tm) (τ : Nat → I) :
    (comp C ψ u u0).subst Tm.var τ =
      comp (C.subst Tm.var (I.up τ)) (ψ.subst τ) (u.subst Tm.var (I.up τ)) (u0.subst Tm.var τ) := by
  simp only [comp]; scalc
theorem fill_substI (C : Tm) (ψ : I) (u u0 : Tm) (τ : Nat → I) :
    (fill C ψ u u0).subst Tm.var (I.up τ) =
      fill (C.subst Tm.var (I.up τ)) (ψ.subst τ) (u.subst Tm.var (I.up τ)) (u0.subst Tm.var τ) := by
  simp only [fill, comp]; scalc
theorem compTube_d1 (C u : Tm) :
    (transp (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u).dinst .one =
      transp (C.subst Tm.var (sk (.or .one (.var 0)) 1)) .one (u.dinst .one) := by
  show transp ((C.dsubst (bind2 (.or (.var 1) (.var 0)))).subst (fun n => (Tm.var n).dshift)
    (I.up (I.inst0 .one))) ((I.var 0).subst (I.inst0 .one)) (u.dinst .one) = _
  congr 1; ssub

theorem comp_eq (C : Tm) (ψ : I) (u u0 : Tm) : comp C ψ u u0 = hcomp (C.dinst .one) ψ
    (transp (C.dsubst (bind2 (.or (.var 1) (.var 0)))) (.var 0) u) (transp C .zero u0) := rfl

/-- On its cofibration, `comp` is the end of its tube. -/
theorem comp_face (hS : SigClosed S) {Ψ Φ Γ C ψ u u0 T} (hc : HasTy0 S Ψ Φ Γ (comp C ψ u u0) T)
    (hψ : I.Entails Φ ψ) : EqTm0 S Ψ Φ Γ (comp C ψ u u0) (u.dinst .one) T := by
  rw [comp_eq] at hc ⊢
  obtain ⟨l, ⟨_, hψs, htube, _, _⟩, ch⟩ := gen_hcomp hc rfl
  have e1 := EqTm0.hcompFace hψ hc
  have ht1 := HasTy0.dsubst hS htube (r := .one) trivial
  rw [dshift_dinst] at ht1
  have ht1' := HasTy0.restrict (scoped_of_ty hc) (ent_and_intro (ent_refl _) hψ) ht1
  rw [compTube_d1] at ht1' e1
  exact EqTm0.trans e1 (EqTm0.transpFace (ent_one Φ) (ch.transport ht1'))

theorem TyChainC.transportEq {Ψ Φ Γ X Y} : TyChainC S Ψ Φ Γ X Y → ∀ {t u}, EqTm0 S Ψ Φ Γ t u X →
    EqTm0 S Ψ Φ Γ t u Y
  | .refl _, _, _, h => h
  | .step e ch, _, _, h => ch.transportEq (EqTm0.conv h e)
  | .up hl ch, _, _, h => ch.transportEq (EqTm0.cumul hl h)

/-- A typed `transp` is typed by its rule. -/
theorem transp_retype {Ψ Φ Γ A φ a T} (h : HasTy0 S Ψ Φ Γ (transp A φ a) T) :
    HasTy0 S Ψ Φ Γ (transp A φ a) (A.dinst .one) := by
  obtain ⟨l, ⟨h0, h1, h2, h3⟩, _⟩ := gen_transpF h rfl
  exact HasTy0.transp h0 h1 h2 h3

/-- Congruence of `comp`. -/
theorem comp_cong (hS : SigClosed S) {Ψ Φ Γ C C' ψ ψ' u u' u0 u0' l}
    (hc : HasTy0 S Ψ Φ Γ (comp C ψ u u0) (C.dinst .one))
    (hc' : HasTy0 S Ψ Φ Γ (comp C' ψ' u' u0') (C.dinst .one))
    (hCC : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift C C' (univ l))
    (h1 : I.Entails ψ ψ') (h2 : I.Entails ψ' ψ)
    (hu : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u u' C)
    (hu0 : EqTm0 S Ψ Φ Γ u0 u0' (C.dinst .zero)) :
    EqTm0 S Ψ Φ Γ (comp C ψ u u0) (comp C' ψ' u' u0') (C.dinst .one) := by
  rw [comp_eq] at hc hc' ⊢
  obtain ⟨_, ⟨_, hψs, htube, hb, _⟩, _⟩ := gen_hcomp hc rfl
  obtain ⟨_, ⟨_, _, htube', hb', _⟩, ch'⟩ := gen_hcomp hc' rfl
  have hs := scoped_of_ty hc
  have hw0 := wf_of_ty hc
  have hXs : (cof Φ ψ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hψs⟩
  have hXΦ : I.Entails (cof Φ ψ).shift Φ.shift := ent_shift (ent_and_left Φ ψ)
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  -- the base
  have htb := transp_retype hb
  have htb' := transp_retype hb'
  obtain ⟨lC, ⟨hC, _, _, _⟩, _⟩ := gen_transpF hb rfl
  have eC1 := EqTm0.dsubst hS hCC (r := .one) trivial
  have eb := EqTm0.transp htb (HasTy0.conv htb' (EqTm0.symm eC1)) hCC (ent_refl _) (ent_refl _) hu0
  -- the tube
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
  exact EqTm0.hcomp hc hc' eC1 h1 h2 (EqTm0.conv et eC1') eb

/-! ## The transport filler -/

theorem transpFill_eq (C : Tm) (ψ : I) (a : Tm) : transpFill C ψ a =
    transp (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0))) a.dshift := rfl

theorem transpFill_d1 (C : Tm) (ψ : I) (a : Tm) : (transpFill C ψ a).dinst .one =
    transp (C.subst Tm.var (sk (.and .one (.var 0)) 1)) (.or ψ (.neg .one)) a := by
  show transp ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).subst (fun n => (Tm.var n).dshift)
    (I.up (I.inst0 .one))) ((I.or ψ.shift (.neg (.var 0))).subst (I.inst0 .one)) (a.dshift.dinst .one) = _
  rw [dshift_dinst]
  congr 1
  · ssub
  · show I.or (ψ.shift.subst (I.inst0 .one)) _ = _
    simp only [I.shift, I.ren, I_subst_subst]; congr 1; exact I_subst_var ψ

theorem transpFill_typed (hS : SigClosed S) {Ψ Φ Γ C ψ a l}
    (hC : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift C (univ l)) (hψ : ψ.Scoped Ψ)
    (hconst : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift C (C.dinst .zero).dshift (univ l))
    (ha : HasTy0 S Ψ Φ Γ a (C.dinst .zero)) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (transpFill C ψ a) C ∧
    EqTm0 S Ψ Φ Γ ((transpFill C ψ a).dinst .zero) a (C.dinst .zero) ∧
    EqTm0 S Ψ Φ Γ ((transpFill C ψ a).dinst .one) (transp C ψ a) (C.dinst .one) ∧
    EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (transpFill C ψ a) a.dshift C := by
  have hw0 := wf_unshift hS (wf_of_ty hC)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
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
  have hXs : (cof Φ.shift χ).shift.Scoped (Ψ + 1 + 1) := scoped_shift ⟨scoped_shift hs, hχs⟩
  have hYX : I.Entails (cof Φ.shift χ).shift Φ.shift.shift := ent_shift (ent_and_left _ _)
  have hYΦ : I.Entails (cof Φ.shift χ).shift (Φ.subst (fun n => .var (n + 2))) := by
    rw [I_add2]; exact hYX
  have hwY : Wf0 S (Ψ + 1 + 1) (cof Φ.shift χ).shift (ctxI (fun n => .var (n + 2)) Γ) := by
    rw [ctxI_add2]; exact (hw0.dwk2 hS).restrict hXs hYX
  -- `L(0) ≡ C(0)`
  have eL0 : EqTm0 S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift (C.dinst .zero).dshift.dshift (univ l) := by
    have e := line_ieq hS hC (k := 2) (Ψ' := Ψ + 1 + 1) (r := .and (.var 1) .zero) (r' := .zero) hYΦ
      ⟨hv1, trivial⟩ trivial (by omega) (I_eq_and_zero_r _) hwY
    rw [ctxI_add2, sk_zero2] at e
    rw [tf_L0s]; exact e
  have hconstL : EqTm0 S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift
      (C.dsubst (bind2 (.and (.var 1) (.var 0))))
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift (univ l) := by
    have hLY := HasTy0.restrict hXs hYX hL
    have hL0 := HasTy0.restrict hXs hYX (HasTy0.dwk hS (HasTy0.dsubst hS (Φ := Φ.shift) (Γ := Γ.dshift) hL (r := .zero) trivial))
    have hψ2 : ψ.shift.shift.Scoped (Ψ + 1 + 1) := scoped_shift (scoped_shift hψ)
    refine EqTm0.local (φ := ψ.shift.shift) (ψ := .neg (.var 1)) hψ2 hv1
      (ent_shift (ent_and_right Φ.shift χ)) hLY hL0 ?_ ?_
    · have hZs : (cof (cof Φ.shift χ).shift ψ.shift.shift).Scoped (Ψ + 1 + 1) := ⟨hXs, hψ2⟩
      have hZ : I.Entails (cof (cof Φ.shift χ).shift ψ.shift.shift) (cof Φ ψ).shift.shift :=
        show I.Entails _ (.and _ _) from ent_and_intro (ent_trans (ent_and_left _ _) hYX) (ent_and_right _ _)
      have e1 := EqTm0.isub hS (τ := bind2 (.and (.var 1) (.var 0))) hconst
        (fun i hi => by rcases i with _ | i
                        · exact ⟨hv1, hv0'⟩
                        · show i + 2 < Ψ + 1 + 1; omega)
        (ent_bind2_shift _ hZ)
        (by rw [ctxI_bind2]; exact (hw0.dwk2 hS).restrict hZs (ent_trans (ent_and_left _ _) hYX))
      rw [ctxI_bind2, dshift_bind2] at e1
      exact EqTm0.trans e1 (EqTm0.symm (EqTm0.restrict hZs (ent_and_left _ _) eL0))
    · have hZs : (cof (cof Φ.shift χ).shift (.neg (.var 1))).Scoped (Ψ + 1 + 1) := ⟨hXs, hv1⟩
      have hZΦ : I.Entails (cof (cof Φ.shift χ).shift (.neg (.var 1))) (Φ.subst (fun n => .var (n + 2))) :=
        ent_trans (ent_and_left _ _) hYΦ
      have e1 := EqTm0.faceU (i := 1) (d := false) hv1 (ent_and_right _ _)
        (HasTy0.restrict hZs (ent_and_left _ _) hLY)
      rw [tf_L1] at e1
      have e2 := line_ieq hS hC (k := 2) (Ψ' := Ψ + 1 + 1) (r := .and .zero (.var 0)) (r' := .zero) hZΦ
        ⟨trivial, hv0'⟩ trivial (by omega) (I_eq_and_zero _) (by rw [ctxI_add2]; exact (hw0.dwk2 hS).restrict hZs (by rw [← I_add2]; exact hZΦ))
      rw [ctxI_add2, sk_zero2] at e2
      exact EqTm0.trans e1 (EqTm0.trans e2 (EqTm0.symm (EqTm0.restrict hZs (ent_and_left _ _) eL0)))
  have hwX : Wf0 S (Ψ + 1) Φ.shift (ctxI (fun n => .var (n + 1)) Γ) := by
    rw [ctxI_add1]; exact wf_of_ty hC
  have ha' : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift a.dshift
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    rw [tf_L0]
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .zero) (r' := .and (.var 0) .zero) (ent_refl _) trivial
      ⟨hv0, trivial⟩ (by omega) (I_eq_symm (I_eq_and_zero_r _)) hwX
    rw [ctxI_add1, sk_zero1] at e
    exact HasTy0.conv (HasTy0.dwk hS ha) e
  have ht0 := HasTy0.transp hL hχs hconstL ha'
  have eC : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one) C (univ l) := by
    have e := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .and (.var 0) .one) (r' := .var 0) (ent_refl _)
      ⟨hv0, trivial⟩ hv0 (by omega) (I_eq_and_one_r _) hwX
    rw [ctxI_add1, sk_var1] at e
    rw [tf_L1']; exact e
  have hT : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (transpFill C ψ a) C := HasTy0.conv ht0 eC
  refine ⟨hT, ?_, ?_, ?_⟩
  · have h0 := HasTy0.dsubst hS ht0 (r := .zero) trivial
    have eC0 := EqTm0.dsubst hS eC (r := .zero) trivial
    have hf := EqTm0.transpFace (ent_trans (ent_negzero Φ) (ent_or_right _ _))
      (show HasTy0 S Ψ Φ Γ (transp ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).subst
        (fun n => (Tm.var n).dshift) (I.up (I.inst0 .zero))) (χ.subst (I.inst0 .zero)) (a.dshift.dinst .zero)) _ from h0)
    have hf' : EqTm0 S Ψ Φ Γ ((transpFill C ψ a).dinst .zero) (a.dshift.dinst .zero) _ := hf
    rw [dshift_dinst] at hf'
    exact EqTm0.conv hf' eC0
  · have h1 := HasTy0.dsubst hS hT (r := .one) trivial
    rw [transpFill_d1] at h1
    have htC := HasTy0.transp hC hψ hconst ha
    have eA := line_ieq hS hC (k := 1) (Ψ' := Ψ + 1) (r := .and .one (.var 0)) (r' := .var 0) (ent_refl _)
      ⟨trivial, hv0⟩ hv0 (by omega) (I_eq_and_one_l _) hwX
    rw [ctxI_add1, sk_var1] at eA
    have eA1 := EqTm0.dsubst hS eA (r := .one) trivial
    have eA0 := EqTm0.dsubst hS eA (r := .zero) trivial
    have e := EqTm0.transp (HasTy0.conv h1 (EqTm0.symm eA1)) (HasTy0.conv htC (EqTm0.symm eA1)) eA
      (ent_neg_one ψ) (ent_or_left _ _) (EqTm0.refl (HasTy0.conv ha (EqTm0.symm eA0)))
    rw [transpFill_d1]
    exact EqTm0.conv e eA1
  · have hXs' : (cof Φ ψ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hψ⟩
    exact EqTm0.transpFace (ent_trans (ent_shift (ent_and_right Φ ψ)) (ent_or_left _ _))
      (HasTy0.restrict hXs' (ent_shift (ent_and_left Φ ψ)) hT)

end KubusCore.Meta
