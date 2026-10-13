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

/-! ## Instantiating a line variable by `sk r k` -/

section
variable (hS : SigClosed S)
include hS

theorem wf_sk (k : Nat) {Ψ Ξ Γ} (hw : Wf0 S Ψ Ξ Γ) :
    Wf0 S (Ψ + k) (Ξ.subst (fun n => .var (n + k))) (ctxI (fun n => .var (n + k)) Γ) := by
  induction k with
  | zero => rw [ctxI_add0, I_add0]; exact hw
  | succ k ih =>
    have := Wf0.dwk hS ih
    have e1 : (Ξ.subst (fun n => .var (n + k))).shift = Ξ.subst (fun n => .var (n + (k + 1))) := by
      simp only [I.shift, I.ren, I_subst_subst]; rfl
    have e2 : (ctxI (fun n => .var (n + k)) Γ).dshift = ctxI (fun n => .var (n + (k + 1))) Γ := by
      simp only [ctxI, Ctx.dshift, List.map_map]; congr 1; funext t
      simp only [Function.comp, dshift_eq, subst_subst]; rfl
    rw [e1, e2] at this; rwa [show Ψ + (k + 1) = Ψ + k + 1 by omega]

theorem HasTy0.skk {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {k : Nat} {X r : I}
    (hr : r.Scoped (Ψ + k)) (hXs : X.Scoped (Ψ + k)) (hX : I.Entails X (Ξ.subst (fun n => .var (n + k)))) :
    HasTy0 S (Ψ + k) X (ctxI (fun n => .var (n + k)) Γ) (t.subst Tm.var (sk r k)) (T.subst Tm.var (sk r k)) := by
  have hw := wf_unshift hS (wf_of_ty h)
  have := HasTy0.isub hS (τ := sk r k) h (sk_scoped hr (by omega)) (ent_skk _ _ hX)
    (by rw [ctxI_skk]; exact (wf_sk hS k hw).restrict hXs hX)
  rwa [ctxI_skk] at this

theorem EqTm0.skk {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t t' T : Tm} (h : EqTm0 S (Ψ + 1) Ξ.shift Γ.dshift t t' T) {k : Nat} {X r : I}
    (hr : r.Scoped (Ψ + k)) (hXs : X.Scoped (Ψ + k)) (hX : I.Entails X (Ξ.subst (fun n => .var (n + k)))) :
    EqTm0 S (Ψ + k) X (ctxI (fun n => .var (n + k)) Γ) (t.subst Tm.var (sk r k)) (t'.subst Tm.var (sk r k))
      (T.subst Tm.var (sk r k)) := by
  have hw := wf_unshift hS (wf_of_eq h)
  have := EqTm0.isub hS (τ := sk r k) h (sk_scoped hr (by omega)) (ent_skk _ _ hX)
    (by rw [ctxI_skk]; exact (wf_sk hS k hw).restrict hXs hX)
  rwa [ctxI_skk] at this

theorem HasTy0.skk_ieq {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {k : Nat} {X r r' : I}
    (hr : r.Scoped (Ψ + k)) (hr' : r'.Scoped (Ψ + k)) (he : I.Eq r r') (hXs : X.Scoped (Ψ + k))
    (hX : I.Entails X (Ξ.subst (fun n => .var (n + k)))) :
    EqTm0 S (Ψ + k) X (ctxI (fun n => .var (n + k)) Γ) (t.subst Tm.var (sk r k)) (t.subst Tm.var (sk r' k))
      (T.subst Tm.var (sk r k)) :=
  line_ieq hS h hX hr hr' (Nat.le_refl _) he ((wf_sk hS k (wf_unshift hS (wf_of_ty h))).restrict hXs hX)

/-! ### `k = 1` -/

theorem HasTy0.sk1 {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {X r : I}
    (hr : r.Scoped (Ψ + 1)) (hXs : X.Scoped (Ψ + 1)) (hX : I.Entails X Ξ.shift) :
    HasTy0 S (Ψ + 1) X Γ.dshift (t.subst Tm.var (sk r 1)) (T.subst Tm.var (sk r 1)) := by
  have := HasTy0.skk hS h (k := 1) hr hXs hX; rwa [ctxI_add1] at this

theorem EqTm0.sk1 {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t t' T : Tm} (h : EqTm0 S (Ψ + 1) Ξ.shift Γ.dshift t t' T) {X r : I}
    (hr : r.Scoped (Ψ + 1)) (hXs : X.Scoped (Ψ + 1)) (hX : I.Entails X Ξ.shift) :
    EqTm0 S (Ψ + 1) X Γ.dshift (t.subst Tm.var (sk r 1)) (t'.subst Tm.var (sk r 1)) (T.subst Tm.var (sk r 1)) := by
  have := EqTm0.skk hS h (k := 1) hr hXs hX; rwa [ctxI_add1] at this

theorem HasTy0.sk1_ieq {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {X r r' : I}
    (hr : r.Scoped (Ψ + 1)) (hr' : r'.Scoped (Ψ + 1)) (he : I.Eq r r') (hXs : X.Scoped (Ψ + 1))
    (hX : I.Entails X Ξ.shift) :
    EqTm0 S (Ψ + 1) X Γ.dshift (t.subst Tm.var (sk r 1)) (t.subst Tm.var (sk r' 1)) (T.subst Tm.var (sk r 1)) := by
  have := HasTy0.skk_ieq hS h (k := 1) hr hr' he hXs hX; rwa [ctxI_add1] at this

/-! ### `k = 2` -/

theorem HasTy0.sk2 {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {X r : I}
    (hr : r.Scoped (Ψ + 1 + 1)) (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X Ξ.shift.shift) :
    HasTy0 S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk r 2)) (T.subst Tm.var (sk r 2)) := by
  have := HasTy0.skk hS h (k := 2) hr hXs (by rw [I_add2]; exact hX); rwa [ctxI_add2] at this

theorem EqTm0.sk2 {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t t' T : Tm} (h : EqTm0 S (Ψ + 1) Ξ.shift Γ.dshift t t' T) {X r : I}
    (hr : r.Scoped (Ψ + 1 + 1)) (hXs : X.Scoped (Ψ + 1 + 1)) (hX : I.Entails X Ξ.shift.shift) :
    EqTm0 S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk r 2)) (t'.subst Tm.var (sk r 2)) (T.subst Tm.var (sk r 2)) := by
  have := EqTm0.skk hS h (k := 2) hr hXs (by rw [I_add2]; exact hX); rwa [ctxI_add2] at this

theorem HasTy0.sk2_ieq {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {X r r' : I}
    (hr : r.Scoped (Ψ + 1 + 1)) (hr' : r'.Scoped (Ψ + 1 + 1)) (he : I.Eq r r') (hXs : X.Scoped (Ψ + 1 + 1))
    (hX : I.Entails X Ξ.shift.shift) :
    EqTm0 S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk r 2)) (t.subst Tm.var (sk r' 2)) (T.subst Tm.var (sk r 2)) := by
  have := HasTy0.skk_ieq hS h (k := 2) hr hr' he hXs (by rw [I_add2]; exact hX); rwa [ctxI_add2] at this

/-! ### `k = 0` -/

theorem HasTy0.sk0 {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {X r : I}
    (hr : r.Scoped Ψ) (hXs : X.Scoped Ψ) (hX : I.Entails X Ξ) :
    HasTy0 S Ψ X Γ (t.subst Tm.var (sk r 0)) (T.subst Tm.var (sk r 0)) := by
  have := HasTy0.skk hS h (k := 0) hr hXs (by rw [I_add0]; exact hX); rwa [ctxI_add0] at this

theorem EqTm0.sk0 {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t t' T : Tm} (h : EqTm0 S (Ψ + 1) Ξ.shift Γ.dshift t t' T) {X r : I}
    (hr : r.Scoped Ψ) (hXs : X.Scoped Ψ) (hX : I.Entails X Ξ) :
    EqTm0 S Ψ X Γ (t.subst Tm.var (sk r 0)) (t'.subst Tm.var (sk r 0)) (T.subst Tm.var (sk r 0)) := by
  have := EqTm0.skk hS h (k := 0) hr hXs (by rw [I_add0]; exact hX); rwa [ctxI_add0] at this

theorem HasTy0.sk0_ieq {Ψ : Nat} {Ξ : I} {Γ : Ctx} {t T : Tm} (h : HasTy0 S (Ψ + 1) Ξ.shift Γ.dshift t T) {X r r' : I}
    (hr : r.Scoped Ψ) (hr' : r'.Scoped Ψ) (he : I.Eq r r') (hXs : X.Scoped Ψ) (hX : I.Entails X Ξ) :
    EqTm0 S Ψ X Γ (t.subst Tm.var (sk r 0)) (t.subst Tm.var (sk r' 0)) (T.subst Tm.var (sk r 0)) := by
  have := HasTy0.skk_ieq hS h (k := 0) hr hr' he hXs (by rw [I_add0]; exact hX); rwa [ctxI_add0] at this

end

/-! ## The filler of `comp` -/

theorem fill_eq (C : Tm) (ψ : I) (u u0 : Tm) : fill C ψ u u0 =
    comp (C.dsubst (bind2 (.and (.var 1) (.var 0)))) (.or ψ.shift (.neg (.var 0))) (fillTube ψ u u0) u0.dshift := rfl

theorem chi_inst0 (ψ r : I) : (I.or ψ.shift (.neg (.var 0))).subst (I.inst0 r) = .or ψ (.neg r) := by
  show I.or (ψ.shift.subst (I.inst0 r)) _ = _
  simp only [I.shift, I.ren, I_subst_subst]; congr 1; exact I_subst_var ψ

theorem fill_dinst (C : Tm) (ψ : I) (u u0 : Tm) (r : I) : (fill C ψ u u0).dinst r =
    comp ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).subst Tm.var (I.up (I.inst0 r))) (.or ψ (.neg r))
      ((fillTube ψ u u0).subst Tm.var (I.up (I.inst0 r))) u0 := by
  rw [fill_eq]
  show (comp _ _ _ _).subst Tm.var (I.inst0 r) = _
  rw [comp_substI, chi_inst0]
  congr 1
  exact dshift_dinst u0 r

theorem var_up_end0 (X : Tm) :
    (X.subst Tm.var (I.up (I.inst0 .zero))).dinst .one = X.subst Tm.var (endS false) := by ssub
theorem var_up_end1 (X : Tm) :
    (X.subst Tm.var (I.up (I.inst0 .one))).dinst .one = X.subst Tm.var (endS true) := by ssub

theorem Cfill_up (C : Tm) (r : I) : (C.dsubst (bind2 (.and (.var 1) (.var 0)))).subst Tm.var (I.up (I.inst0 r)) =
    C.subst Tm.var (sk (.and (r.shift) (.var 0)) 1) := by ssub
theorem Cfill_up1 (C : Tm) : (C.dsubst (bind2 (.and (.var 1) (.var 0)))).subst Tm.var (I.up (I.inst0 .one)) =
    C.subst Tm.var (sk (.and .one (.var 0)) 1) := by ssub
theorem Cfill_endS (C : Tm) : (C.dsubst (bind2 (.and (.var 1) (.var 0)))).subst Tm.var (endS false) =
    C.subst Tm.var (sk (.and .zero .one) 0) := by ssub

/-- Typing of the filler of heterogeneous composition and its boundary. -/
theorem fill_typed (hS : SigClosed S) {Ψ Φ Γ C ψ u u0 l}
    (hC : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift C (univ l)) (hψ : ψ.Scoped Ψ)
    (hu : HasTy0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u C) (hu0 : HasTy0 S Ψ Φ Γ u0 (C.dinst .zero))
    (hside : EqTm0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) u0 (C.dinst .zero)) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (fill C ψ u u0) C ∧
    EqTm0 S Ψ Φ Γ ((fill C ψ u u0).dinst .zero) u0 (C.dinst .zero) ∧
    EqTm0 S Ψ Φ Γ ((fill C ψ u u0).dinst .one) (comp C ψ u u0) (C.dinst .one) ∧
    EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (fill C ψ u u0) u C := by
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
  have htube : HasTy0 S (Ψ + 1 + 1) (cof Φ.shift χ).shift Γ.dshift.dshift (fillTube ψ u u0)
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
  have hside'' : EqTm0 S (Ψ + 1) (cof Φ.shift χ) Γ.dshift ((fillTube ψ u u0).dinst .zero) u0.dshift
      ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by rw [fillTube_d0]; exact hside'
  have hc := comp_typed hS hL hχs htube hbase hside''
  have eC : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (bind2 (.and (.var 1) (.var 0)))).dinst .one) C (univ l) := by
    have e := HasTy0.sk1_ieq hS hC (r := .and (.var 0) .one) (r' := .var 0) ⟨hv0, trivial⟩ hv0
      (I_eq_and_one_r _) (scoped_shift hs) (ent_refl _)
    rw [sk_var1] at e
    rw [tf_L1']; exact e
  have hfT : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (fill C ψ u u0) C := HasTy0.conv hc eC
  refine ⟨hfT, ?_, ?_, ?_⟩
  · -- the endpoint 0
    have hd := HasTy0.dsubst hS hfT (r := .zero) trivial
    rw [fill_dinst] at hd
    have e1 := comp_face hS hd (ent_trans (ent_negzero Φ) (ent_or_right _ _))
    rw [var_up_end0, fillTube_end] at e1
    have hE := HasTy0.isub hS (τ := endS false) htube (endS_scoped Ψ false)
      (ent_and_intro (ent_shift2_endS Φ false) (ent_trans (ent_negzero Φ) (ent_or_right _ _)))
      (by rw [ctxI_endS]; exact hw0)
    rw [ctxI_endS, Cfill_endS, fillTube_end] at hE
    have eE := HasTy0.sk0_ieq hS hC (r := .and .zero .one) (r' := .zero) ⟨trivial, trivial⟩ trivial
      (I_eq_and_zero _) hs (ent_refl _)
    rw [sk_zero0] at eE
    have e2 := EqTm0.splitR (ent_negzero Φ) (HasTy0.conv hE eE)
    rw [fill_dinst]
    exact EqTm0.trans e1 e2
  · -- the endpoint 1
    have hd := HasTy0.dsubst hS hfT (r := .one) trivial
    rw [fill_dinst, Cfill_up1, fillTube_up1'] at hd
    have hc1 := comp_typed hS hC hψ hu hu0 hside
    have hX : (cof Φ (.or ψ (.neg .one))).Scoped Ψ := ⟨hs, ⟨hψ, trivial⟩⟩
    have hXs : (cof Φ (.or ψ (.neg .one))).shift.Scoped (Ψ + 1) := scoped_shift hX
    have hXe : I.Entails (cof Φ (.or ψ (.neg .one))).shift (cof Φ ψ).shift :=
      ent_shift (ent_and_mono (ent_refl _) (ent_neg_one ψ))
    have eA := HasTy0.sk1_ieq hS hC (r := .and .one (.var 0)) (r' := .var 0) ⟨trivial, hv0⟩ hv0
      (I_eq_and_one_l _) (scoped_shift hs) (ent_refl _)
    rw [sk_var1] at eA
    have eA1 := EqTm0.dsubst hS eA (r := .one) trivial
    have eA0 := EqTm0.dsubst hS eA (r := .zero) trivial
    have htyped := HasTy0.isub hS (τ := I.up (I.inst0 .one)) (Φ' := (cof Φ (.or ψ (.neg .one))).shift)
      htube (Iup_scoped (fun i hi => by
        rcases i with _ | i
        · trivial
        · exact show i < Ψ by omega))
      (by rw [fillR_up1]; exact ent_refl _)
      (by rw [ctxI_up_inst0]; exact (Wf0.dwk hS hw0).restrict hXs (ent_shift (ent_and_left _ _)))
    rw [ctxI_up_inst0, Cfill_up1, fillTube_up1'] at htyped
    have htu : EqTm0 S (Ψ + 1) (cof Φ (.or ψ (.neg .one))).shift Γ.dshift
        (split ψ.shift (u.subst Tm.var (sk (.and .one (.var 0)) 1)) (.neg .one) u0.dshift) u
        (C.subst Tm.var (sk (.and .one (.var 0)) 1)) := by
      have e1 := EqTm0.splitL (ent_trans (ent_and_right _ _) (ent_shift (ent_neg_one ψ))) htyped
      have e2 := HasTy0.sk1_ieq hS hu (r := .and .one (.var 0)) (r' := .var 0) ⟨trivial, hv0⟩ hv0
        (I_eq_and_one_l _) hXs hXe
      rw [sk_var1] at e2
      exact EqTm0.trans e1 e2
    have e := comp_cong hS (HasTy0.conv hd (EqTm0.symm eA1)) (HasTy0.conv hc1 (EqTm0.symm eA1)) eA
      (ent_neg_one ψ) (ent_or_left _ _) htu (EqTm0.refl (HasTy0.conv hu0 (EqTm0.symm eA0)))
    rw [fill_dinst, Cfill_up1, fillTube_up1']
    exact EqTm0.conv e eA1
  · -- under `ψ` the filler is the tube
    have hs' : (cof Φ ψ).shift.Scoped (Ψ + 1) := scoped_shift hXψs
    have hψψ : I.Entails (cof Φ ψ).shift ψ.shift := ent_shift (ent_and_right Φ ψ)
    have hf' := HasTy0.restrict hs' (ent_shift (ent_and_left Φ ψ)) hfT
    have e1 : EqTm0 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift (fill C ψ u u0) ((fillTube ψ u u0).dinst .one) C :=
      comp_face hS hf' (ent_trans hψψ (ent_or_left _ _))
    have ht1 := HasTy0.dsubst hS (Φ := cof Φ.shift χ) (Γ := Γ.dshift) htube (r := .one) trivial
    have ht1' := HasTy0.restrict hs'
      (ent_and_intro (ent_shift (ent_and_left Φ ψ)) (ent_trans hψψ (ent_or_left _ _))) ht1
    rw [fillTube_d1] at e1 ht1'
    have e2 := EqTm0.splitL hψψ ht1'
    have e3 := HasTy0.sk1_ieq hS hu (r := .and (.var 0) .one) (r' := .var 0) ⟨hv0, trivial⟩ hv0
      (I_eq_and_one_r _) hs' (ent_refl _)
    rw [sk_var1] at e3
    have eC' := EqTm0.restrict hs' (ent_shift (ent_and_left Φ ψ)) eC
    rw [tf_L1'] at e2 eC'
    exact EqTm0.trans e1 (EqTm0.conv (EqTm0.trans e2 e3) eC')

/-! ## Judgments under a cofibration in the line variable -/

theorem sk0_inst0 (r : I) : sk r 0 = I.inst0 r := funext fun i => by rcases i with _ | i <;> rfl
theorem sk1_var : sk (.var 0) 1 = I.var := funext fun i => by rcases i with _ | i <;> rfl

section
variable (hS : SigClosed S)
include hS

theorem HasTy0.cof_sk {Ψ : Nat} {Φ φ : I} {Γ : Ctx} {t T : Tm}
    (h : HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t T) (hw : Wf0 S Ψ Φ Γ) {k : Nat} {X r : I}
    (hr : r.Scoped (Ψ + k)) (hXs : X.Scoped (Ψ + k)) (hXΦ : I.Entails X (Φ.subst (fun n => .var (n + k))))
    (hXφ : I.Entails X (φ.subst (sk r k))) :
    HasTy0 S (Ψ + k) X (ctxI (fun n => .var (n + k)) Γ) (t.subst Tm.var (sk r k)) (T.subst Tm.var (sk r k)) := by
  have := HasTy0.isub hS (τ := sk r k) h (sk_scoped hr (by omega))
    (show I.Entails X (.and _ _) from ent_and_intro (ent_skk r k hXΦ) hXφ)
    (by rw [ctxI_skk]; exact (wf_sk hS k hw).restrict hXs hXΦ)
  rwa [ctxI_skk] at this

theorem EqTm0.cof_sk {Ψ : Nat} {Φ φ : I} {Γ : Ctx} {t t' T : Tm}
    (h : EqTm0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t t' T) (hw : Wf0 S Ψ Φ Γ) {k : Nat} {X r : I}
    (hr : r.Scoped (Ψ + k)) (hXs : X.Scoped (Ψ + k)) (hXΦ : I.Entails X (Φ.subst (fun n => .var (n + k))))
    (hXφ : I.Entails X (φ.subst (sk r k))) :
    EqTm0 S (Ψ + k) X (ctxI (fun n => .var (n + k)) Γ) (t.subst Tm.var (sk r k)) (t'.subst Tm.var (sk r k))
      (T.subst Tm.var (sk r k)) := by
  have := EqTm0.isub hS (τ := sk r k) h (sk_scoped hr (by omega))
    (show I.Entails X (.and _ _) from ent_and_intro (ent_skk r k hXΦ) hXφ)
    (by rw [ctxI_skk]; exact (wf_sk hS k hw).restrict hXs hXΦ)
  rwa [ctxI_skk] at this

theorem HasTy0.cof_inst {Ψ : Nat} {Φ φ : I} {Γ : Ctx} {t T : Tm}
    (h : HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t T) (hw : Wf0 S Ψ Φ Γ) {X r : I}
    (hr : r.Scoped Ψ) (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ) (hXφ : I.Entails X (φ.subst (I.inst0 r))) :
    HasTy0 S Ψ X Γ (t.dinst r) (T.dinst r) := by
  have := HasTy0.cof_sk hS h hw (k := 0) hr hXs (by rw [I_add0]; exact hXΦ) (by rw [sk0_inst0]; exact hXφ)
  rwa [ctxI_add0, sk0_inst0] at this

theorem EqTm0.cof_inst {Ψ : Nat} {Φ φ : I} {Γ : Ctx} {t t' T : Tm}
    (h : EqTm0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t t' T) (hw : Wf0 S Ψ Φ Γ) {X r : I}
    (hr : r.Scoped Ψ) (hXs : X.Scoped Ψ) (hXΦ : I.Entails X Φ) (hXφ : I.Entails X (φ.subst (I.inst0 r))) :
    EqTm0 S Ψ X Γ (t.dinst r) (t'.dinst r) (T.dinst r) := by
  have := EqTm0.cof_sk hS h hw (k := 0) hr hXs (by rw [I_add0]; exact hXΦ) (by rw [sk0_inst0]; exact hXφ)
  rwa [ctxI_add0, sk0_inst0] at this

theorem HasTy0.cof_ins {Ψ : Nat} {Φ φ : I} {Γ : Ctx} {t T : Tm}
    (h : HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t T) (hw : Wf0 S Ψ Φ Γ) {X : I}
    (hXs : X.Scoped (Ψ + 1 + 1)) (hXΦ : I.Entails X Φ.shift.shift) (hXφ : I.Entails X (φ.subst (sk (.var 0) 2))) :
    HasTy0 S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk (.var 0) 2)) (T.subst Tm.var (sk (.var 0) 2)) := by
  have := HasTy0.cof_sk hS h hw (k := 2) (r := .var 0) (show 0 < Ψ + 2 by omega) hXs (by rw [I_add2]; exact hXΦ) hXφ
  rwa [ctxI_add2] at this

theorem EqTm0.cof_ins {Ψ : Nat} {Φ φ : I} {Γ : Ctx} {t t' T : Tm}
    (h : EqTm0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t t' T) (hw : Wf0 S Ψ Φ Γ) {X : I}
    (hXs : X.Scoped (Ψ + 1 + 1)) (hXΦ : I.Entails X Φ.shift.shift) (hXφ : I.Entails X (φ.subst (sk (.var 0) 2))) :
    EqTm0 S (Ψ + 1 + 1) X Γ.dshift.dshift (t.subst Tm.var (sk (.var 0) 2)) (t'.subst Tm.var (sk (.var 0) 2))
      (T.subst Tm.var (sk (.var 0) 2)) := by
  have := EqTm0.cof_sk hS h hw (k := 2) (r := .var 0) (show 0 < Ψ + 2 by omega) hXs (by rw [I_add2]; exact hXΦ) hXφ
  rwa [ctxI_add2] at this

omit hS in
/-- Restricting a judgment under `φ` to a restriction that entails `φ`. -/
theorem HasTy0.cof_restrict {Ψ : Nat} {Φ φ : I} {Γ : Ctx} {t T : Tm}
    (h : HasTy0 S (Ψ + 1) (cof Φ.shift φ) Γ.dshift t T) {X : I}
    (hXs : X.Scoped (Ψ + 1)) (hXΦ : I.Entails X Φ.shift) (hXφ : I.Entails X φ) :
    HasTy0 S (Ψ + 1) X Γ.dshift t T :=
  HasTy0.restrict hXs (ent_and_intro hXΦ hXφ) h

end

end KubusCore.Meta
