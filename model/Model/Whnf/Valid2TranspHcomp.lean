import Model.Whnf.Valid2HcompCon
import Model.Whnf.Kan2DataHITStep
import Model.Whnf.Kan2DataHITRel

/-!
# Transport of formal compositions

The binary validity of `transpHcomp` (higher inductive types with parameters): the transport of a formal
composition is related to the composition of the transports of its tube and base. Formal compositions
are related by `hcomp_relD` from tubes related pointwise; the transports are related by the Kan oracle.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- The tube of the `transpHcomp` contractum under a substitution. -/
theorem transp_skip_subst (A : Tm) (φ : I) (u : Tm) (γ : ℕ → Tm) (τ : ℕ → I) :
    (Tm.transp (A.dsubst skip1I) φ.shift u).subst (dupS γ) (I.up τ) =
      .transp ((A.subst (dupS γ) (I.up τ)).dsubst skip1I) (φ.subst τ).shift (u.subst (dupS γ) (I.up τ)) := by
  show Tm.transp ((A.dsubst skip1I).subst (dupS (dupS γ)) (I.up (I.up τ))) ((φ.shift).subst (I.up τ)) _ = _
  rw [I_shift_subst_up]
  congr 1
  simp only [Tm.dsubst, subst_subst]
  refine subst_congr (fun n => ?_) (fun i => ?_) A
  · show (Tm.var n).subst (dupS (dupS γ)) (I.up (I.up τ)) = (dupS γ n).subst Tm.var skip1I
    simp only [Tm.subst, dupS]
    rw [dshift_skip1I]
  · rcases i with _ | i
    · rfl
    · show (I.var (i + 2)).subst (I.up (I.up τ)) = ((τ i).shift).subst skip1I
      rw [I_shift_skip1I]; rfl

/-- The tube of the `transpHcomp` contractum at `1`. -/
theorem transp_skip_dinst1 (A : Tm) (φ : I) (u : Tm) :
    (Tm.transp (A.dsubst skip1I) φ.shift u).dinst .one = .transp A φ (u.dinst .one) := by
  show Tm.transp ((A.subst Tm.var skip1I).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .one)))
    (φ.shift.subst (I.inst0 .one)) (u.dinst .one) = _
  congr 1
  · rw [subst_subst]
    apply subst_id_of
    · intro n; rfl
    · intro i; cases i with
      | zero => rfl
      | succ i => rfl
  · simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var φ

section
variable (hW : WfSig S)
include hW
variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- Transport along a valid line, at a related substitution, of related elements of the start. -/
theorem transp_rel_at (hK : KanOracle2 S) {A : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hLV : Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A (.univ l))
    (hCV : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (.univ l))
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (c : CSub2 S Ψ Φ Γ k) {b b' : Tm} (hb : RE2 S k (c.L (A.dinst .zero)) b b') :
    RE2 S k (c.L (A.dinst .one)) (.transp ((c.up hW).L A) (φ.subst c.σ.τ) b)
      (.transp ((c.up hW).R A) (φ.subst c.σ'.τ) b') := by
  have hφL := I.scoped_subst hφ c.σ.sc
  have hφR := I.scoped_subst hφ c.σ'.sc
  have e0 : c.L (A.dinst .zero) = ((c.up hW).L A).dinst .zero := CSub2.L_dinst hW c A .zero
  have e1 : c.L (A.dinst .one) = ((c.up hW).L A).dinst .one := CSub2.L_dinst hW c A .one
  rw [e0] at hb
  rw [e1]
  have hLt : HasTy S (k + 1) .one [] ((c.up hW).L A) (.univ l) := (c.up hW).ty hW hL
  have hLt' : HasTy S (k + 1) .one [] ((c.up hW).R A) (.univ l) := (c.up hW).tyR hW hL
  have eLR : EqTm S (k + 1) .one [] ((c.up hW).L A) ((c.up hW).R A) (.univ l) := (c.up hW).eqLR hW hL
  have hcL : EqTm S (k + 1) (cof .one (φ.subst c.σ.τ)).shift [] ((c.up hW).L A) (((c.up hW).L A).dinst .zero).dshift
      (.univ l) := by
    have h := (c.diagL hW).eqCofUp hW hφL hc
    have e : ((c.diagL hW).up hW).R (A.dinst .zero).dshift = (((c.up hW).L A).dinst .zero).dshift := by
      show (A.dinst .zero).dshift.subst (dupS c.γ) (I.up c.σ.τ) = _
      rw [dshift_dup_subst]; exact congrArg Tm.dshift e0
    rw [e] at h; exact h
  have hcR : EqTm S (k + 1) (cof .one (φ.subst c.σ'.τ)).shift [] ((c.up hW).R A) (((c.up hW).R A).dinst .zero).dshift
      (.univ l) := by
    have h := (c.diagR hW).eqCofUp hW hφR hc
    have e : ((c.diagR hW).up hW).R (A.dinst .zero).dshift = (((c.up hW).R A).dinst .zero).dshift := by
      show (A.dinst .zero).dshift.subst (dupS c.γ') (I.up c.σ'.τ) = _
      rw [dshift_dup_subst]; exact congrArg Tm.dshift (CSub2.R_dinst hW c A .zero)
    rw [e] at h; exact h
  -- the ends of the lines
  have hT0 := hLV.tySelf hW (c.cons .zero .zero trivial trivial (I_eq_refl _))
  rw [CSub2.L_cons hW, CSub2.R_cons hW] at hT0
  have hT1 := hLV.tySelf hW (c.cons .one .one trivial trivial (I_eq_refl _))
  rw [CSub2.L_cons hW, CSub2.R_cons hW] at hT1
  have tyB : ∀ {X Z : Tm}, RT2 S k X Z → TyEq S k X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hb0 := (RE2.typed hb).1
  have hb0' := (RE2.typed hb).2.1.tyConv (tyB hT0)
  have hty : HasTy S k .one [] (.transp ((c.up hW).L A) (φ.subst c.σ.τ) b) (((c.up hW).L A).dinst .one) :=
    HasTy.transp hLt hφL hcL hb0
  have hty' : HasTy S k .one [] (.transp ((c.up hW).R A) (φ.subst c.σ'.τ) b') (((c.up hW).L A).dinst .one) :=
    (HasTy.transp hLt' hφR hcR hb0').tyConv (TyEq.symm (tyB hT1))
  have heq := EqTm.transp hty hty' eLR (c.ent_LR (ent_refl φ)) (c.ent_RL (ent_refl φ)) (RE2.typed hb).2.2
  exact hK.transp k _ _ (hLV.ty hW (c.up hW)) (lineRob_of_valid hW hLV c) _ _ b b' (lineConst_of_valid hW hφ hCV c)
    hty hty' heq (c.ent_LR (ent_refl φ)) (c.ent_RL (ent_refl φ)) hb

end

end

end Model.Whnf
