import Model.Whnf.Valid2ElimH18
import Model.Whnf.Valid2ElimH19

/-! # Weakening the valid premises of a higher inductive eliminator -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} (hW : WfSig S)
include hW

/-- Weakening a valid telescope whose declared types have no interval variables. -/
theorem VTele2.dwk {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ts : Tm} {Δ prev : List Tm}
    (ht : HasTele0 S Ψ Φ Γ ts Δ prev)
    (hc : ∀ (j : ℕ) (A : Tm), Δ[j]? = some A → A.closedB (prev.length + j) 0 = true)
    (hv : VTele2 S Ψ Φ Γ ts ts Δ prev) :
    VTele2 S (Ψ + 1) Φ.shift Γ.dshift ts.dshift ts.dshift Δ (prev.map Tm.dshift) := by
  match ht with
  | .nil _ => trivial
  | @HasTele0.cons _ Ψ Φ Γ a as A Δ prev h0 h1 =>
    change Valid2 S Ψ Φ Γ a a (A.substList prev) ∧ _ at hv
    change Valid2 S (Ψ + 1) Φ.shift Γ.dshift a.dshift a.dshift
      (A.substList (prev.map Tm.dshift)) ∧ _
    refine ⟨?_, VTele2.dwk h1 (fun j B hb => ?_) hv.2⟩
    · have hd := (VTy.dwk' hW (⟨h0, hv.1⟩ : VTy S Ψ Φ Γ a (A.substList prev))).v
      have hA : A.closedB prev.length 0 = true := by simpa using hc 0 A (by simp)
      have e : (A.substList prev).dshift = A.substList (prev.map Tm.dshift) := by
        rw [Tm.dshift, ren_eq_subst, substList_subst hA]
        simp only [id_eq, ← dshift_eq]
      rwa [e] at hd
    · have h := hc (j + 1) B (by simpa using hb)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h
termination_by structural ht

omit hW in
theorem upN_var2 (n : ℕ) : upN n Tm.var = Tm.var := by
  funext i
  rw [upN_eq]
  split_ifs with hi
  · rfl
  · simp only [Tm.subst]
    congr 1
    omega

omit hW in
theorem dupN_var2 (n : ℕ) : dupN n Tm.var = Tm.var := by
  funext i
  rw [dupN_eq]
  rfl

/-- Interval weakening of the branch telescope changes only its outer components. -/
theorem branchTele2_dshift {d c : ℕ} {D : DataDecl} {C : Ctor} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) {ps M : Tm} (hp : IsList ps) (hpl : ps.toList.length = D.params.length) :
    branchTele2 d D C ps.dshift M.dshift = (branchTele2 d D C ps M).map Tm.dshift := by
  simp only [branchTele2, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have e := branchArgTy_subst (σ := Tm.var) (τ := fun i => I.var (i + 1))
      (argTy_closed hW hD hC j) hp hpl
    simpa only [upN_var2, ← dshift_eq] using e.symm
  · apply List.map_congr_left
    intro j hj
    have e := branchIhTy_subst (σ := Tm.var) (τ := fun i => I.var (i + 1)) (List.mem_range.1 hj) M
    simpa only [upN_var2, up_var, ← dshift_eq] using e.symm

omit hW in
theorem Ctx.dren_dshift (n : ℕ) (Γ : Ctx) : Ctx.dren n Γ.dshift = Ctx.dren (n + 1) Γ := by
  simp only [Ctx.dren, Ctx.dshift, List.map_map]
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_def, Tm.dshift, ren_ren]
  congr 1
  funext i
  omega

theorem branchCtx_outerShift {d c : ℕ} {D : DataDecl} {C : Ctor} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) {ps M : Tm} (hp : IsList ps) (hpl : ps.toList.length = D.params.length)
    (Γ : Ctx) : D.branchCtx d C ps.dshift M.dshift Γ.dshift =
      Ctx.dren (C.dims + 1) ((branchTele2 d D C ps M).reverse ++ Γ) := by
  rw [branchCtx_tele2, branchTele2_dshift hW hD hC hp hpl, ← List.map_reverse]
  change ctxWkI C.dims (((branchTele2 d D C ps M).reverse.map Tm.dshift) ++ Γ.map Tm.dshift) = _
  rw [← List.map_append, ← Ctx_ren_add_eq]
  change Ctx.dren C.dims (Ctx.dshift ((branchTele2 d D C ps M).reverse ++ Γ)) = _
  exact Ctx.dren_dshift _ _

omit hW in
theorem branchFace_outerShift {n : ℕ} {Φ ψ : I} (hψ : ψ.Scoped n) :
    (cof (Φ.ren (· + n)) ψ).subst (IupN n (fun i => I.var (i + 1))) =
      cof (Φ.shift.ren (· + n)) ψ := by
  change I.and ((Φ.ren (· + n)).subst _) (ψ.subst _) = _
  rw [I_ren_subst, subst_scoped_id hψ (fun i hi => IupN_lt hi _)]
  congr 1
  rw [I.shift, I_ren_ren]
  apply congrArg (fun τ => Φ.subst τ)
  funext i
  rw [IupN_add]
  rfl

/-- Boundary validity weakens outside the constructor's own interval binders. -/
theorem valid_branchBnd_dwk {Ψ : ℕ} {Φ : I} {Γ : Ctx} {d c kb : ℕ} {D : DataDecl} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {ps M bs b e : Tm} {ψ : I}
    (hb : C.bnd[kb]? = some (ψ, e)) (hp : IsList ps) (hpl : ps.toList.length = D.params.length) (hbs : IsList bs)
    (ht : EqTm0 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps M Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps M))
    (hv : Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps M Γ)
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps M)) :
    Valid2 S (Ψ + 1 + C.dims) (cof (Φ.shift.ren (· + C.dims)) ψ) (D.branchCtx d C ps.dshift M.dshift Γ.dshift)
      (DataDecl.branchApp C b.dshift) (D.bndElim C ps.dshift bs.dshift e) (DataDecl.branchBody d c C ps.dshift M.dshift) := by
  have hψ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ e hb
  have hc := (presup hW ht).1
  have hc' := (presup hW ht).2
  have hv' : Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ)
      (Ctx.dren C.dims ((branchTele2 d D C ps M).reverse ++ Γ))
      (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps M) := by
    simpa only [branchCtx_tele2, Ctx.dren, Ctx_ren_add_eq] using hv
  have H := valid_dsub (n := C.dims) (m := C.dims + 1) (Ψ0 := Ψ)
    (IupN C.dims (fun i => I.var (i + 1)))
    (fun i hi => by rw [IupN_lt hi]; exact show i < Ψ + (C.dims + 1) by omega)
    (fun i => by rw [IupN_add]; simp only [I.subst]; congr 1; omega) (scoped_of_ty hc)
    (by rw [branchFace_outerShift hψ.1]; exact ent_refl _)
    (closed_ty hc) (closed_ty hc') (closedT_of_ty hW hc) hv'
  have ea := branchApp_subst (σ := Tm.var) (τ := fun i => I.var (i + 1)) C b
  have eb := bndElim_subst (D := D) (σ := Tm.var) (τ := fun i => I.var (i + 1)) hp hpl hbs e hψ.2.1
  have et := branchBody_subst (σ := Tm.var) (τ := fun i => I.var (i + 1)) d c C ps M
  simp only [upN_var2, dupN_var2, up_var, ← dshift_eq] at ea eb et
  change Valid2 S (Ψ + (C.dims + 1)) _ _ _ _ _ at H
  rw [show Ψ + (C.dims + 1) = Ψ + 1 + C.dims by omega, ← branchCtx_outerShift hW hD hC hp hpl Γ] at H
  simpa only [Tm.dsubst, ea, eb, et] using H

end

end Model.Whnf
