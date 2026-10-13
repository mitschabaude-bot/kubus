import Model.Canon.KanBasic

/-!
# Canonicity: derived Kan operations (`comp`, fillers) preserve computability
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem isub_eq_subst (t : Tm) (σ : ISub k' k) : t.isub σ = t.subst .var σ.τ := rfl

theorem isub_dinst_eq (t : Tm) (σ : ISub k' k) (r : I) :
    (t.isub σ).dinst r = t.subst .var (fun i => (σ.τ i).subst (I.inst0 r)) := by
  simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]; rfl

theorem I_shift_cons (φ : I) (r : I) (hr : r.Scoped k') (σ : ISub k' k) :
    φ.shift.subst (ISub.cons r hr σ).τ = φ.subst σ.τ := by
  simp only [I.shift, I_ren_subst]; rfl

theorem I_shift_inst0 (x r : I) : x.shift.subst (I.inst0 r) = x := by
  simp only [I.shift, I_ren_subst]; exact I_subst_var x

theorem dshift_isub_cons (t : Tm) (r : I) (hr : r.Scoped k') (σ : ISub k' k) :
    t.dshift.isub (ISub.cons r hr σ) = t.isub σ := by
  simp only [Tm.isub, dshift_subst]; rfl

variable (hW : WfSig S)
include hW

theorem ent_cof_cons {X : I} (hX : X.Scoped k) (r : I) (hr : r.Scoped k') (σ : ISub k' k)
    (h : (ival (idEnv k') (X.subst σ.τ)).holds) : I.Entails .one ((cof .one X).shift.subst (ISub.cons r hr σ).τ) := by
  show I.Entails .one (I.and .one (X.shift.subst (ISub.cons r hr σ).τ))
  rw [I_shift_cons]; exact ent_cof_one hW (entails_of_holds (I.scoped_subst hX σ.sc) h)

theorem tyEq_ieq {n : ℕ} {C : Tm} {l : ℕ} (hCt : HasTy0 S n .one [] C (.univ l)) {τ1 τ2 : ℕ → I}
    (hb1 : ∀ i < n, (τ1 i).Scoped k) (hb2 : ∀ i < n, (τ2 i).Scoped k) (heq : ∀ i < n, I.Eq (τ1 i) (τ2 i))
    {T1 T2 : Tm} (h1 : T1 = C.subst .var τ1) (h2 : T2 = C.subst .var τ2) : TyEq S k T1 T2 :=
  .inr ⟨l, by subst h1 h2; exact ieq0 hW hCt hb1 hb2 heq⟩

/-- Heterogeneous composition along a computable line preserves computability. -/
theorem RE_comp {C u u0 : Tm} {ψ : I} (hC : KanAll S (k + 1) C)
    (hty : HasTy S k .one [] (Tm.comp C ψ u u0) (C.dinst .one))
    (hu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (ψ.subst σ.τ)).holds →
      RE S k' ((C.isub σ.up).dinst r) ((u.isub σ.up).dinst r))
    (hu0 : RE S k (C.dinst .zero) u0) : RE S k (C.dinst .one) (Tm.comp C ψ u u0) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨-, hψ, htube, hbase, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) h0 rfl
  obtain ⟨l1, ⟨hCt, -, -, -⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) hbase rfl
  have hCc : C.closedB 0 (k + 1) = true := closed_ty hCt
  have KH := hC.1 k (ISub.cons .one trivial (ISub.id k))
  rw [isub_cons_id_of_closed hCc] at KH
  have KT0 := hC.2 k (ISub.id (k + 1))
  rw [isub_id_of_closed hCc] at KT0
  refine KH ψ _ _ hty (fun k' σ r hr hh => ?_) (KT0 .zero u0 (minimal_to_spec hbase) hu0)
  rw [isub_up_dinst _ σ r hr]
  let τ : ℕ → I := fun x => ((Tm.bind2 (.or (.var 1) (.var 0))) x).subst (I.up (ISub.cons r hr σ).τ)
  have hsc : ∀ x < k + 1, (τ x).Scoped (k' + 1) := fun x hx => by
    rcases x with _ | x
    · exact ⟨I.scoped_shift hr, show 0 < k' + 1 by omega⟩
    · exact I.scoped_shift (σ.sc x (by omega))
  have KT := hC.2 k' (ISub.ofFun (k + 1) τ hsc)
  rw [isub_ofFun hCc] at KT
  have hline : ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).isub (ISub.cons r hr σ).up) = C.subst .var τ := by
    simp only [Tm.isub, Tm.dsubst, subst_subst]; rfl
  show RE S k' _ (Tm.transp ((C.dsubst (Tm.bind2 (.or (.var 1) (.var 0)))).isub (ISub.cons r hr σ).up) r
    (u.isub (ISub.cons r hr σ)))
  rw [hline]
  have hT := HasTy0.isub hS (Ψ' := k') (Φ' := .one) (τ := (ISub.cons r hr σ).τ) htube
    (fun i hi => (ISub.cons r hr σ).sc i hi)
    (by show I.Entails .one (I.and I.one.shift (ψ.shift.subst (ISub.cons r hr σ).τ))
        rw [I_shift_cons]; exact ent_cof_one hW (entails_of_holds (I.scoped_subst hψ σ.sc) hh))
    (Wf0.nil trivial)
  have hT' : HasTy S k' .one [] (.transp (C.subst .var τ) r (u.isub (ISub.cons r hr σ))) ((C.dinst .one).isub σ) := by
    have := minimal_to_spec hT
    rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons] at this
    rw [← hline]; exact this
  have e1 : TyEq S k' ((C.dinst .one).isub σ) ((C.subst .var τ).dinst .one) :=
    tyEq_ieq hW hCt (τ1 := fun i => (I.inst0 .one i).subst σ.τ) (τ2 := fun i => (τ i).subst (I.inst0 .one))
      (fun i hi => I.scoped_subst (by rcases i with _ | i <;> simp [I.inst0, I.Scoped] <;> omega) σ.sc)
      (fun i hi => I.scoped_subst (hsc i hi) (fun j hj => by rcases j with _ | j <;> simp [I.inst0, I.Scoped] <;> omega))
      (fun i hi => by
        rcases i with _ | i
        · intro ρ; simp [τ, I.eval, I.inst0, I.subst, Tm.bind2, I.up, ISub.cons]
        · show I.Eq (σ.τ i) (((σ.τ i).shift).subst (I.inst0 .one))
          rw [I_shift_inst0]; exact I_eq_refl _)
      (by simp only [Tm.dinst, Tm.dsubst, Tm.isub, subst_subst]; rfl) (by simp only [Tm.dinst, Tm.dsubst, subst_subst]; rfl)
  have e0 : TyEq S k' (C.isub (ISub.cons r hr σ)) ((C.subst .var τ).dinst .zero) :=
    tyEq_ieq hW hCt (τ1 := (ISub.cons r hr σ).τ) (τ2 := fun i => (τ i).subst (I.inst0 .zero))
      (fun i hi => (ISub.cons r hr σ).sc i hi)
      (fun i hi => I.scoped_subst (hsc i hi) (fun j hj => by rcases j with _ | j <;> simp [I.inst0, I.Scoped] <;> omega))
      (fun i hi => by
        rcases i with _ | i
        · intro ρ; simp [τ, I.eval, I.inst0, I.subst, Tm.bind2, I.up, ISub.cons]; rw [I_shift_inst0]
        · show I.Eq (σ.τ i) (((σ.τ i).shift).subst (I.inst0 .zero))
          rw [I_shift_inst0]; exact I_eq_refl _)
      rfl (by simp only [Tm.dinst, Tm.dsubst, subst_subst]; rfl)
  have hin := hu k' σ r hr hh
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r hr] at hin
  exact (KT r _ (HasTy.tyConv hT' e1) (hin.conv_ty hW e0)).conv_ty hW (TyEq.symm e1)

omit hW in
theorem dshift_isub_tail (t : Tm) (σ : ISub k' (k + 1)) : t.dshift.isub σ = t.isub σ.tail := by
  simp only [Tm.isub, dshift_subst]; rfl

omit hW in
theorem I_shift_tail (φ : I) (σ : ISub k' (k + 1)) : φ.shift.subst σ.τ = φ.subst σ.tail.τ := by
  simp only [I.shift, I_ren_subst]; rfl

/-- The composition filler preserves computability, given the composition at its base. -/
theorem RE_hfill_of {A u u0 : Tm} {φ : I}
    (KH : ∀ (φ' : I) (u' : Tm), HasTy S (k + 1) .one [] (.hcomp A.dshift φ' u' u0.dshift) A.dshift →
      TubeC S (k + 1) A.dshift φ' u' → RE S (k + 1) A.dshift (.hcomp A.dshift φ' u' u0.dshift))
    (hty : HasTy S k .one [] (.hcomp A φ u u0) A) (hu : TubeC S k A φ u) (hu0 : RE S k A u0) :
    RE S (k + 1) A.dshift (Tm.hfill A φ u u0) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hAt, hφ, hut, hu0t, hside⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) h0 rfl
  obtain ⟨hH, -, -, -⟩ := hfill_typed hS hAt hφ hut hu0t hside
  obtain ⟨-, ⟨-, -, htube, -, -⟩, -⟩ := gen_hcomp hH rfl
  refine KH _ _ (minimal_to_spec hH) (fun k' σ r hr hh => ?_)
  rw [isub_up_dinst _ σ r hr, dshift_isub_tail]
  have hT := HasTy0.isub hS (Ψ' := k') (Φ' := .one) (τ := (ISub.cons r hr σ).τ) htube
    (fun i hi => (ISub.cons r hr σ).sc i hi)
    (by show I.Entails .one (I.and I.one.shift.shift ((I.or φ.shift (.neg (.var 0))).shift.subst (ISub.cons r hr σ).τ))
        rw [I_shift_cons]
        exact ent_cof_one hW (entails_of_holds (I.scoped_subst
          (show (I.or φ.shift (.neg (.var 0))).Scoped (k + 1) from ⟨I.scoped_shift hφ, show 0 < k + 1 by omega⟩) σ.sc) hh))
    (Wf0.nil trivial)
  have hT' := minimal_to_spec hT
  rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons, dshift_isub_tail] at hT'
  have hσ0 : (σ.τ 0).Scoped k' := σ.sc 0 (by omega)
  rcases holds_or hh with h1 | h2
  · have hent : I.Entails .one (φ.shift.shift.subst (ISub.cons r hr σ).τ) := by
      rw [I_shift_cons]; exact entails_of_holds (I.scoped_subst (I.scoped_shift hφ) σ.sc) h1
    have e := EqTm.splitL hent hT'
    have hY : ((u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).subst .var (ISub.cons r hr σ).τ) =
        u.isub (ISub.cons (.and (σ.τ 0) r) (show (I.and (σ.τ 0) r).Scoped k' from ⟨hσ0, hr⟩) σ.tail) := by
      simp only [Tm.isub, Tm.dsubst, subst_subst]
      exact subst_congr (fun _ => rfl) (fun x => by rcases x with _ | x <;> rfl) u
    have h3 := hu k' σ.tail (.and (σ.τ 0) r) (show (I.and (σ.τ 0) r).Scoped k' from ⟨hσ0, hr⟩)
      (by rw [← I_shift_tail]; exact h1)
    rw [isub_up_dinst _ _ _ (show (I.and (σ.τ 0) r).Scoped k' from ⟨hσ0, hr⟩), ← hY] at h3
    exact h3.conv hW (TyEq.refl _) (EqTm.symm e)
  · have e := EqTm.splitR (show I.Entails .one (I.neg (σ.τ 0)) from
      entails_of_holds hσ0 h2) hT'
    have hW' : ((u0.dshift.dshift).subst .var (ISub.cons r hr σ).τ) = u0.isub σ.tail := by
      simp only [Tm.isub, dshift_subst]; rfl
    have h3 := hu0.isub hW σ.tail
    rw [← hW'] at h3
    exact h3.conv hW (TyEq.refl _) (EqTm.symm e)

/-- The composition filler preserves computability. -/
theorem RE_hfill {A u u0 : Tm} {φ : I} (hA : ∀ k' (ρ : ISub k' k), KanH S k' (A.isub ρ))
    (hty : HasTy S k .one [] (.hcomp A φ u u0) A) (hu : TubeC S k A φ u) (hu0 : RE S k A u0) :
    RE S (k + 1) A.dshift (Tm.hfill A φ u u0) := by
  have hAc : A.closedB 0 k = true := closed_of_isTyK hW (isTyK_of_ty hW hty)
  have KH := hA (k + 1) (ISub.wk k)
  rw [isub_wk_of_closed hAc] at KH
  exact RE_hfill_of hW (fun φ' u' h1 h2 => KH φ' u' _ h1 h2 (RE.dshift hW hu0)) hty hu hu0

/-- The transport filler preserves computability. -/
theorem RE_transpFill {A a : Tm} {φ : I} (hA : ∀ k' (ρ : ISub (k' + 1) (k + 1)), KanT S k' (A.isub ρ))
    (hty : HasTy S k .one [] (.transp A φ a) (A.dinst .one)) (ha : RE S k (A.dinst .zero) a) :
    RE S (k + 1) A (Tm.transpFill A φ a) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hAt, hφ, hc, hat⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) h0 rfl
  obtain ⟨hF, -, -, -⟩ := transpFill_typed hS hAt hφ hc hat
  have hAc : A.closedB 0 (k + 1) = true := closed_ty hAt
  have hsc : ∀ i < k + 1, (Tm.bind2 (.and (.var 1) (.var 0)) i).Scoped (k + 1 + 1) := fun i hi => by
    rcases i with _ | i
    · exact ⟨show 1 < k + 1 + 1 by omega, show 0 < k + 1 + 1 by omega⟩
    · show i + 2 < k + 1 + 1; omega
  have KT := hA (k + 1) (ISub.ofFun (k + 1) _ hsc)
  rw [isub_ofFun hAc] at KT
  have e1 : TyEq S (k + 1) ((A.subst .var (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) A :=
    tyEq_ieq hW hAt (τ1 := fun i => (Tm.bind2 (.and (.var 1) (.var 0)) i).subst (I.inst0 .one)) (τ2 := I.var)
      (fun i hi => by rcases i with _ | i <;> simp [Tm.bind2, I.subst, I.inst0, I.Scoped] <;> omega)
      (fun i hi => show i < k + 1 from hi)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; simp [I.eval, I.inst0, Tm.bind2, I.subst]
                      · intro ρ; rfl)
      (by simp only [Tm.dinst, Tm.dsubst, subst_subst]; rfl) (subst_var A).symm
  have e0 : TyEq S (k + 1) (A.dinst .zero).dshift ((A.subst .var (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) :=
    tyEq_ieq hW hAt (τ1 := fun i => (I.inst0 .zero i).shift)
      (τ2 := fun i => (Tm.bind2 (.and (.var 1) (.var 0)) i).subst (I.inst0 .zero))
      (fun i hi => I.scoped_shift (by rcases i with _ | i <;> simp [I.inst0, I.Scoped] <;> omega))
      (fun i hi => by rcases i with _ | i <;> simp [Tm.bind2, I.subst, I.inst0, I.Scoped] <;> omega)
      (fun i hi => by rcases i with _ | i
                      · intro ρ; simp [I.eval, I.inst0, Tm.bind2, I.subst, I.shift, I.ren]
                      · intro ρ; rfl)
      (by simp only [Tm.dinst, Tm.dsubst, dshift_eq, subst_subst]; rfl) (by simp only [Tm.dinst, Tm.dsubst, subst_subst]; rfl)
  exact (KT _ _ (HasTy.tyConv (minimal_to_spec hF) (TyEq.symm e1)) ((RE.dshift hW ha).conv_ty hW e0)).conv_ty hW e1

end

end Model.Canon
