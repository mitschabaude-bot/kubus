import Model.Whnf.Kan2PiT

/-!
# Transport along lines of components of normal forms

Generic lemmas for lines of the form `D(σ1)[Θ1]`, where `D(σ)` is a component (e.g. the domain) of the
normal form of a restriction `T[σ]` of a line `T`, and `σ1 ∘ Θ1` sends the line variable to `y` and the
other variables to `σ0`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

/-- Transport along lines of a family of components of normal forms. -/
theorem lineKan_of (D D' : ∀ k3, ISub k3 (k + 1) → Tm)
    (hXD : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (D k3 σ)))
    (cohD : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((D k1 σ1).isub θ) (D k2 σ2))
    (cohD' : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((D' k1 σ1).isub θ) (D' k2 σ2))
    (robD : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
      RT2 S k3 (D k3 (ISub.cons y hy τ)) (D' k3 (ISub.cons y' hy' τ)))
    (IH : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (ρ' : ISub (k2 + 1) k1) X', RT2 S (k2 + 1) ((D k1 σ1).isub ρ') X' →
      KanT2 S k2 ((D k1 σ1).isub ρ') X')
    {k1 k1' k3 : ℕ} (σ1 : ISub k1 (k + 1)) (σ1' : ISub k1' (k + 1)) (Θ1 : ISub (k3 + 1) k1)
    (Θ1' : ISub (k3 + 1) k1') (σ0 : ISub k3 k) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1))
    (hE : I.Eq y y') (e1 : σ1.comp Θ1 = ISub.cons y hy σ0.up.tail) (e1' : σ1'.comp Θ1' = ISub.cons y' hy' σ0.up.tail) :
    KanT2 S k3 ((D k1 σ1).isub Θ1) ((D' k1' σ1').isub Θ1') ∧
    LineRob S k3 ((D k1 σ1).isub Θ1) ((D' k1' σ1').isub Θ1') ∧
    (∀ (e : I) (he : e.Scoped k3),
      RT2 S k3 (((D k1 σ1).isub Θ1).dinst e)
        (D k3 (ISub.cons (y.subst (ISub.cons e he (ISub.id k3)).τ)
          (I.scoped_subst hy (ISub.cons e he (ISub.id k3)).sc) σ0))) ∧
    RT2 S (k3 + 1) ((D k1 σ1).isub Θ1) ((D' k1' σ1').isub Θ1') ∧
    (∀ (e : I) (he : e.Scoped k3),
      RT2 S k3 (((D' k1' σ1').isub Θ1').dinst e)
        (D' k3 (ISub.cons (y'.subst (ISub.cons e he (ISub.id k3)).τ)
          (I.scoped_subst hy' (ISub.cons e he (ISub.id k3)).sc) σ0))) := by
  have hXD' : ∀ k3 (τ : ISub k3 k) (y : I) (hy : y.Scoped k3), TyCode k3 (semK S k3 (D' k3 (ISub.cons y hy τ))) :=
    fun k3 τ y hy => RT2.tyCode_r hW (robD k3 τ y y hy hy (I_eq_refl _)) (hXD _ _)
  have c1 := cohD k1 σ1 (k3 + 1) Θ1 _ e1
  have m := robD (k3 + 1) σ0.up.tail y y' hy hy' hE
  have c3 := cohD' k1' σ1' (k3 + 1) Θ1' _ e1'
  have t1 := RT2.tyCode_l hW c1 (hXD _ _)
  have t3 := RT2.tyCode_l hW c3 (RT2.tyCode_r hW m (hXD _ _))
  have rel : RT2 S (k3 + 1) ((D k1 σ1).isub Θ1) ((D' k1' σ1').isub Θ1') :=
    RT2.trans hW t1 c1 (RT2.trans hW (hXD _ _) m (RT2.symm hW t3 c3))
  refine ⟨IH k1 σ1 k3 Θ1 _ rel, fun k4 τ2 z z' hz hz' hEz => ?_, fun e he => ?_, rel, fun e he => ?_⟩
  · rw [Tm.isub_isub, Tm.isub_isub]
    have d1 := cohD k1 σ1 k4 (Θ1.comp (ISub.cons z hz τ2)) _
      (by rw [← ISub.comp_assoc, e1, ISub.cons_comp, ISub.up_tail_comp_cons])
    have d3 := cohD' k1' σ1' k4 (Θ1'.comp (ISub.cons z' hz' τ2)) _
      (by rw [← ISub.comp_assoc, e1', ISub.cons_comp, ISub.up_tail_comp_cons])
    have hEs : I.Eq (y.subst (ISub.cons z hz τ2).τ) (y'.subst (ISub.cons z' hz' τ2).τ) :=
      I_eq_trans (I_eq_subst hE _) (I_eq_subst_congr (fun i => by
        rcases i with _ | i
        · exact hEz
        · exact I_eq_refl _) y')
    have mm := robD k4 (σ0.comp τ2) _ _ (I.scoped_subst hy (ISub.cons z hz τ2).sc)
      (I.scoped_subst hy' (ISub.cons z' hz' τ2).sc) hEs
    have u1 := RT2.tyCode_l hW d1 (hXD _ _)
    have u3 := RT2.tyCode_l hW d3 (RT2.tyCode_r hW mm (hXD _ _))
    exact RT2.trans hW u1 d1 (RT2.trans hW (hXD _ _) mm (RT2.symm hW u3 d3))
  · have hcl := closed_of_isTyK hW (Comp2_ty_base c1).2.1
    rw [← isub_cons_id_of_closed hcl e he, Tm.isub_isub]
    exact cohD k1 σ1 k3 _ _ (by rw [← ISub.comp_assoc, e1, ISub.cons_comp, ISub.up_tail_comp_cons, ISub.comp_id])
  · have hcl := closed_of_isTyK hW (Comp2_ty_base c3).2.1
    rw [← isub_cons_id_of_closed hcl e he, Tm.isub_isub]
    exact cohD' k1' σ1' k3 _ _ (by rw [← ISub.comp_assoc, e1', ISub.cons_comp, ISub.up_tail_comp_cons,
      ISub.comp_id])

/-- Constancy of lines of a family of components of normal forms. -/
theorem lineConst_of (D : ∀ k3, ISub k3 (k + 1) → Tm)
    (hXD : ∀ k3 (σ : ISub k3 (k + 1)), TyCode k3 (semK S k3 (D k3 σ)))
    (cohD : ∀ k1 (σ1 : ISub k1 (k + 1)) k2 (θ : ISub k2 k1) (σ2 : ISub k2 (k + 1)), σ1.comp θ = σ2 →
      RT2 S k2 ((D k1 σ1).isub θ) (D k2 σ2))
    {k1 k3 : ℕ} (σ0 : ISub k3 k) (σ1 : ISub k1 (k + 1)) (Θ1 : ISub (k3 + 1) k1) (y : I)
    (hy : y.Scoped (k3 + 1)) (e1 : σ1.comp Θ1 = ISub.cons y hy σ0.up.tail) (ψ : I) (hψ : ψ.Scoped k3)
    (hmid : ∀ k4 (τ2 : ISub k4 k3) (z : I) (hz : z.Scoped k4), I.Entails .one (ψ.subst τ2.τ) →
      RT2 S k4 (D k4 (ISub.cons (y.subst (ISub.cons z hz τ2).τ) (I.scoped_subst hy (ISub.cons z hz τ2).sc)
        (σ0.comp τ2)))
        (D k4 (ISub.cons (y.subst (ISub.cons .zero trivial τ2).τ)
          (I.scoped_subst hy (ISub.cons .zero trivial τ2).sc) (σ0.comp τ2)))) :
    LineConst S k3 ((D k1 σ1).isub Θ1) ψ := by
  intro k4 τ2 z hz hh
  rw [Tm.isub_isub, Tm.isub_isub]
  have d : ∀ (z : I) (hz : z.Scoped k4), RT2 S k4 ((D k1 σ1).isub (Θ1.comp (ISub.cons z hz τ2)))
      (D k4 (ISub.cons (y.subst (ISub.cons z hz τ2).τ) (I.scoped_subst hy (ISub.cons z hz τ2).sc)
        (σ0.comp τ2))) := fun z hz =>
    cohD k1 σ1 k4 _ _ (by rw [← ISub.comp_assoc, e1, ISub.cons_comp, ISub.up_tail_comp_cons])
  have d1 := d z hz
  have d0 := d .zero trivial
  have mid := hmid k4 τ2 z hz ((holds_iff_entails (I.scoped_subst hψ τ2.sc)).1 hh)
  exact RT2.trans hW (RT2.tyCode_l hW d1 (hXD _ _)) d1
    (RT2.trans hW (hXD _ _) mid (RT2.symm hW (RT2.tyCode_l hW d0 (hXD _ _)) d0))

end

end Model.Whnf
