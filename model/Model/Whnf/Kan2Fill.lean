import Model.Whnf.Kan2SigmaH
import Model.Whnf.Kan2Path

/-!
# Fillers of binary compositions

The relation of the fillers `hfill A φ u u0` of related compositions, through the composition at the
weakened type.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem fillTube_isub_dinst (φ : I) (u u0 : Tm) {k3 : ℕ} (σ : ISub k3 (k + 1)) (x : I) :
    ((KubusCore.Meta.fillTube φ u u0).isub σ.up).dinst x = Tm.split (φ.subst σ.tail.τ)
      ((u.isub σ.tail.up).dinst (.and (σ.τ 0) x)) (.neg (σ.τ 0)) (u0.isub σ.tail) := by
  show Tm.split ((φ.shift.shift.subst σ.up.τ).subst (I.inst0 x))
    (((u.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).isub σ.up).dinst x)
    (((I.neg (I.var 1)).subst σ.up.τ).subst (I.inst0 x)) (((u0.dshift.dshift).isub σ.up).dinst x) = _
  congr 1
  · show ((φ.shift.shift).subst (I.up σ.τ)).subst (I.inst0 x) = _
    rw [I_shift_subst_up, I_shift_inst0]
    show (φ.shift).subst σ.τ = _
    simp only [I.shift, I_ren_subst]; rfl
  · simp only [Tm.dsubst, Tm.dinst, Tm.isub, subst_subst]
    refine subst_congr (fun _ => rfl) (fun i => ?_) u
    rcases i with _ | i
    · show I.and (((σ.τ 0).shift).subst (I.inst0 x)) x = I.and (σ.τ 0) x
      rw [I_shift_inst0]
    · show (((σ.τ (i + 1)).shift).subst (I.inst0 x)) = ((σ.τ (i + 1)).shift).subst (I.inst0 _)
      rw [I_shift_inst0, I_shift_inst0]
  · show I.neg (((σ.τ 0).shift).subst (I.inst0 x)) = _
    rw [I_shift_inst0]
  · rw [isub_dshift, dshift_dinst, dshift_isub_tail]


theorem isub_hfill (A : Tm) (φ : I) (u u0 : Tm) (σ : ISub k' k) :
    (Tm.hfill A φ u u0).isub σ.up = Tm.hfill (A.isub σ) (φ.subst σ.τ) (u.isub σ.up) (u0.isub σ) := by
  show (Tm.hfill A φ u u0).subst .var (I.up σ.τ) = _
  rw [show (Tm.var : ℕ → Tm) = dupS Tm.var from funext fun n => rfl, hfill_subst]; rfl

variable (hW : WfSig S)
include hW

/-- Two systems `[φ ↦ p, ψ ↦ q]`, related on the intersections of their faces. -/
theorem RE2_sys2 {A p p' q q' : Tm} {φ φ' ψ ψ' : I} (hφ : φ.Scoped k) (hφ' : φ'.Scoped k)
    (hψ : ψ.Scoped k) (hψ' : ψ'.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (k12 : I.Entails ψ ψ') (k21 : I.Entails ψ' ψ)
    (hor : I.Entails .one (.or φ ψ)) (hAA : RT2 S k A A)
    (hsp : HasTy S k .one [] (.split φ p ψ q) A) (hsp' : HasTy S k .one [] (.split φ' p' ψ' q') A)
    (hpp : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → RE2 S k' (A.isub σ) (p.isub σ) (p'.isub σ))
    (hpq : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → I.Entails .one (ψ.subst σ.τ) →
      RE2 S k' (A.isub σ) (p.isub σ) (q'.isub σ))
    (hqp : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → I.Entails .one (ψ.subst σ.τ) →
      RE2 S k' (A.isub σ) (q.isub σ) (p'.isub σ))
    (hqq : ∀ k' (σ : ISub k' k), I.Entails .one (ψ.subst σ.τ) → RE2 S k' (A.isub σ) (q.isub σ) (q'.isub σ)) :
    RE2 S k A (.split φ p ψ q) (.split φ' p' ψ' q') := by
  have hX := tyCode_of_ty hW hsp
  have hor' : I.Entails .one (.or φ' ψ') :=
    ent_trans hor (ent_or_elim (ent_trans h12 (ent_or_left _ _)) (ent_trans k12 (ent_or_right _ _)))
  refine RE2_split_l hW hφ hψ hor hAA hsp hsp' (fun k1 σ hσ => ?_) (fun k1 σ hσ => ?_)
  · refine RE2_split_r hW (I.scoped_subst hφ' σ.sc) (I.scoped_subst hψ' σ.sc) (ent_one_subst hor' σ.τ)
      (RT2.isub hW hX hAA σ) (HasTy.isubS hW hsp' σ) (RE2.typed (hpp k1 σ hσ)).1
      (fun k2 σ2 h => ?_) (fun k2 σ2 h => ?_)
    · have := hpp k2 (σ.comp σ2) (ent_trans (ent_comp_inv h) (ent_subst h21 _))
      rwa [← Tm.isub_isub A, ← Tm.isub_isub p, ← Tm.isub_isub p'] at this
    · have := hpq k2 (σ.comp σ2) (ent_comp hσ) (ent_trans (ent_comp_inv h) (ent_subst k21 _))
      rwa [← Tm.isub_isub A, ← Tm.isub_isub p, ← Tm.isub_isub q'] at this
  · refine RE2_split_r hW (I.scoped_subst hφ' σ.sc) (I.scoped_subst hψ' σ.sc) (ent_one_subst hor' σ.τ)
      (RT2.isub hW hX hAA σ) (HasTy.isubS hW hsp' σ) (RE2.typed (hqq k1 σ hσ)).1
      (fun k2 σ2 h => ?_) (fun k2 σ2 h => ?_)
    · have := hqp k2 (σ.comp σ2) (ent_trans (ent_comp_inv h) (ent_subst h21 _)) (ent_comp hσ)
      rwa [← Tm.isub_isub A, ← Tm.isub_isub q, ← Tm.isub_isub p'] at this
    · have := hqq k2 (σ.comp σ2) (ent_comp hσ)
      rwa [← Tm.isub_isub A, ← Tm.isub_isub q, ← Tm.isub_isub q'] at this


omit hW in
theorem shift_subst_tail (φ : I) {k3 : ℕ} (σ : ISub k3 (k + 1)) : φ.shift.subst σ.τ = φ.subst σ.tail.τ := by
  simp only [I.shift, I_ren_subst]; rfl

/-- The tube of a composition is typed at the composition's type, at points where its face holds. -/
theorem hcomp_tube_typed' {X T u a : Tm} {φ : I} (hty : HasTy S k .one [] (.hcomp T φ u a) X) (x : I)
    (hx : x.Scoped k) (hh : (ival (idEnv k) φ).holds) : HasTy S k .one [] (u.dinst x) X := by
  have h := hcomp_tube_typed hW hty x hx hh
  obtain ⟨_, _, ch⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
  exact minimal_to_spec (ch.transport (spec_to_minimal hW h))

/-- The fillers of related compositions are related. -/
theorem hfill_rel {A A' u u' u0 u0' : Tm} {φ φ' : I} (hφs : φ.Scoped k)
    (hK : KanH2 S (k + 1) A.dshift A'.dshift) (hAA : RT2 S k A A) (hTA : TyEq S k A A')
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift)
    (htyF : HasTy S (k + 1) .one [] (Tm.hfill A φ u u0) A.dshift)
    (htyF' : HasTy S (k + 1) .one [] (Tm.hfill A' φ' u' u0') A.dshift)
    (heqF : EqTm S (k + 1) .one [] (Tm.hfill A φ u u0) (Tm.hfill A' φ' u' u0') A.dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k A φ u u') (hu0 : RE2 S k A u0 u0')
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (u0'.isub σ))
    (hbd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (u0.isub σ) ((u'.isub σ.up).dinst .zero)) :
    RE2 S (k + 1) A.dshift (Tm.hfill A φ u u0) (Tm.hfill A' φ' u' u0') := by
  have hX := RE2.tyCode hW hu0
  have hAσ : ∀ k3 (σ : ISub k3 k), RT2 S k3 (A.isub σ) (A.isub σ) := fun k3 σ => RT2.isub hW hX hAA σ
  have hholds : ∀ {k3 : ℕ} (σ : ISub k3 k), I.Entails .one (φ.subst σ.τ) → (ival (idEnv k3) (φ.subst σ.τ)).holds :=
    fun σ h => (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 h
  -- the relations of the tubes at points
  have uu : ∀ k3 (σ : ISub k3 k) (x x' : I), x.Scoped k3 → x'.Scoped k3 → I.Eq x x' →
      I.Entails .one (φ.subst σ.τ) → RE2 S k3 (A.isub σ) ((u.isub σ.up).dinst x) ((u'.isub σ.up).dinst x') :=
    fun k3 σ x x' hx hx' hE h => htube k3 σ x x' hx hx' hE (hholds σ h)
  have u0r : ∀ k3 (σ : ISub k3 k) (x : I), x.Scoped k3 → I.Eq x .zero → I.Entails .one (φ.subst σ.τ) →
      RE2 S k3 (A.isub σ) ((u.isub σ.up).dinst x) (u0'.isub σ) := by
    intro k3 σ x hx he h
    have a := uu k3 σ x .zero hx trivial he h
    have b := hbd' k3 σ (hholds σ h)
    have c := RE2.isub hW hu0 σ
    exact RE2.trans hW (hAσ k3 σ) a (RE2.trans hW (hAσ k3 σ) (RE2.symm hW (hAσ k3 σ) b) c)
  have u0l : ∀ k3 (σ : ISub k3 k) (x : I), x.Scoped k3 → I.Eq x .zero → I.Entails .one (φ.subst σ.τ) →
      RE2 S k3 (A.isub σ) (u0.isub σ) ((u'.isub σ.up).dinst x) := by
    intro k3 σ x hx he h
    have a := uu k3 σ .zero x trivial hx (I_eq_symm he) h
    have b := hbd k3 σ (hholds σ h)
    have c := RE2.isub hW hu0 σ
    exact RE2.trans hW (hAσ k3 σ) c (RE2.trans hW (hAσ k3 σ) (RE2.symm hW (hAσ k3 σ) b) a)
  have hface : I.Entails (I.or φ.shift (.neg (.var 0))) (I.or φ'.shift (.neg (.var 0))) :=
    ent_or_elim (ent_trans (ent_shift h12) (ent_or_left _ _)) (ent_or_right _ _)
  have hface' : I.Entails (I.or φ'.shift (.neg (.var 0))) (I.or φ.shift (.neg (.var 0))) :=
    ent_or_elim (ent_trans (ent_shift h21) (ent_or_left _ _)) (ent_or_right _ _)
  have hsψ : (I.or φ.shift (.neg (.var 0))).Scoped (k + 1) :=
    ⟨KubusCore.I.scoped_shift hφs, show 0 < k + 1 by omega⟩
  -- the faces at a restriction
  have hψσ : ∀ k3 (σ : ISub k3 (k + 1)), (ival (idEnv k3) ((I.or φ.shift (.neg (.var 0))).subst σ.τ)).holds →
      I.Entails .one (I.or (φ.subst σ.tail.τ) (.neg (σ.τ 0))) := by
    intro k3 σ hh
    have := (holds_iff_entails (I.scoped_subst hsψ σ.sc)).1 hh
    show I.Entails .one (I.or (φ.subst σ.tail.τ) (.neg (σ.τ 0)))
    rw [← shift_subst_tail]; exact this
  have hσ0 : ∀ k3 (σ : ISub k3 (k + 1)), (σ.τ 0).Scoped k3 := fun k3 σ => σ.sc 0 (by omega)
  have hAA' : A = A' ∨ ∃ l, EqTm0 S k .one [] A A' (.univ l) := by
    rcases hTA with e | ⟨l, e⟩
    · exact .inl e
    · exact .inr ⟨l, spec_to_minimal_eq hW e⟩
  have htEqF := minimal_to_spec_eq (fillTube_eq hW (spec_to_minimal hW htyF) (spec_to_minimal hW htyF') hAA'
    (spec_to_minimal_eq hW hteq) (spec_to_minimal_eq hW (RE2.typed hu0).2.2) h12)
  refine hK _ _ _ _ _ _ htyF htyF' heqF htEqF hface hface' (fun k3 σ x x' hx hx' hEx hh => ?_) (RE2.dshift hW hu0)
    (fun k3 σ hh => ?_) (fun k3 σ hh => ?_)
  · -- the tubes of the fillers
    have hσF : HasTy S k3 .one [] (.hcomp (A.dshift.isub σ) ((I.or φ.shift (.neg (.var 0))).subst σ.τ)
        ((KubusCore.Meta.fillTube φ u u0).isub σ.up) (u0.dshift.isub σ)) (A.dshift.isub σ) := HasTy.isubS hW htyF σ
    have hσF' : HasTy S k3 .one [] (.hcomp (A'.dshift.isub σ) ((I.or φ'.shift (.neg (.var 0))).subst σ.τ)
        ((KubusCore.Meta.fillTube φ' u' u0').isub σ.up) (u0'.dshift.isub σ)) (A.dshift.isub σ) := HasTy.isubS hW htyF' σ
    have hh' : (ival (idEnv k3) ((I.or φ'.shift (.neg (.var 0))).subst σ.τ)).holds :=
      entails_holds (ent_subst hface σ.τ) hh
    have hsp := hcomp_tube_typed' hW hσF x hx hh
    have hsp' := hcomp_tube_typed' hW hσF' x' hx' hh'
    rw [fillTube_isub_dinst, dshift_isub_tail] at hsp hsp'
    show RE2 S k3 (A.dshift.isub σ) (((KubusCore.Meta.fillTube φ u u0).isub σ.up).dinst x)
      (((KubusCore.Meta.fillTube φ' u' u0').isub σ.up).dinst x')
    rw [fillTube_isub_dinst, fillTube_isub_dinst, dshift_isub_tail]
    have hsφ : (φ.subst σ.tail.τ).Scoped k3 := I.scoped_subst hφs σ.tail.sc
    have hsφ' : (φ'.subst σ.tail.τ).Scoped k3 := by
      obtain ⟨l1, ⟨-, h, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW htyF') rfl
      have h1 : (φ'.shift).Scoped (k + 1) := h.1
      have := I.scoped_subst h1 σ.sc
      rwa [shift_subst_tail] at this
    refine RE2_sys2 hW hsφ hsφ' (hσ0 k3 σ) (hσ0 k3 σ) (ent_subst h12 _) (ent_subst h21 _) (ent_refl _) (ent_refl _)
      (hψσ k3 σ hh) (hAσ k3 σ.tail) hsp hsp' (fun k4 σ4 h => ?_) (fun k4 σ4 h h' => ?_) (fun k4 σ4 h h' => ?_)
      (fun k4 σ4 h' => ?_)
    · rw [dinst_up_isub, dinst_up_isub, Tm.isub_isub]
      exact uu k4 _ _ _ (I.scoped_subst (show (I.and (σ.τ 0) x).Scoped k3 from ⟨hσ0 k3 σ, hx⟩) σ4.sc) (I.scoped_subst (show (I.and (σ.τ 0) x').Scoped k3 from ⟨hσ0 k3 σ, hx'⟩) σ4.sc)
        (I_eq_subst (ieq_and_congr (I_eq_refl _) hEx) _) (ent_comp_inv h)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      have e0 := ieq_zero_of_holds_neg (I.scoped_subst (hσ0 k3 σ) σ4.sc)
        (entails_holds h' (ρ := idEnv k4) (by rw [ival_one]; rfl))
      exact u0r k4 _ _ (I.scoped_subst (show (I.and (σ.τ 0) x).Scoped k3 from ⟨hσ0 k3 σ, hx⟩) σ4.sc) (ieq_and_zero_left _ e0) (ent_comp_inv h)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      have e0 := ieq_zero_of_holds_neg (I.scoped_subst (hσ0 k3 σ) σ4.sc)
        (entails_holds h' (ρ := idEnv k4) (by rw [ival_one]; rfl))
      exact u0l k4 _ _ (I.scoped_subst (show (I.and (σ.τ 0) x').Scoped k3 from ⟨hσ0 k3 σ, hx'⟩) σ4.sc) (ieq_and_zero_left _ e0) (ent_comp_inv h)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact RE2.isub hW hu0 _
  · -- the boundary of the tubes, on the left
    have hσF : HasTy S k3 .one [] (.hcomp (A.dshift.isub σ) ((I.or φ.shift (.neg (.var 0))).subst σ.τ)
        ((KubusCore.Meta.fillTube φ u u0).isub σ.up) (u0.dshift.isub σ)) (A.dshift.isub σ) := HasTy.isubS hW htyF σ
    have hsp := hcomp_tube_typed' hW hσF .zero trivial hh
    rw [fillTube_isub_dinst, dshift_isub_tail] at hsp
    show RE2 S k3 (A.dshift.isub σ) (((KubusCore.Meta.fillTube φ u u0).isub σ.up).dinst .zero) (u0'.dshift.isub σ)
    rw [fillTube_isub_dinst, dshift_isub_tail, dshift_isub_tail]
    have hsφ : (φ.subst σ.tail.τ).Scoped k3 := I.scoped_subst hφs σ.tail.sc
    refine RE2_split_l hW hsφ (hσ0 k3 σ) (hψσ k3 σ hh) (hAσ k3 σ.tail) hsp
      (RE2.typed (RE2.isub hW hu0 σ.tail)).2.1 (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      exact u0r k4 _ _ (I.scoped_subst (show (I.and (σ.τ 0) .zero).Scoped k3 from ⟨hσ0 k3 σ, trivial⟩) σ4.sc)
        (ieq_and_zero_right _) (ent_comp_inv h)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact RE2.isub hW hu0 _
  · -- the boundary of the tubes, on the right
    have hh' : (ival (idEnv k3) ((I.or φ'.shift (.neg (.var 0))).subst σ.τ)).holds :=
      entails_holds (ent_subst hface σ.τ) hh
    have hσF' : HasTy S k3 .one [] (.hcomp (A'.dshift.isub σ) ((I.or φ'.shift (.neg (.var 0))).subst σ.τ)
        ((KubusCore.Meta.fillTube φ' u' u0').isub σ.up) (u0'.dshift.isub σ)) (A.dshift.isub σ) := HasTy.isubS hW htyF' σ
    have hsp := hcomp_tube_typed' hW hσF' .zero trivial hh'
    rw [fillTube_isub_dinst, dshift_isub_tail] at hsp
    show RE2 S k3 (A.dshift.isub σ) (u0.dshift.isub σ) (((KubusCore.Meta.fillTube φ' u' u0').isub σ.up).dinst .zero)
    rw [fillTube_isub_dinst, dshift_isub_tail, dshift_isub_tail]
    have hsφ' : (φ'.subst σ.tail.τ).Scoped k3 := by
      obtain ⟨l1, ⟨-, h, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW htyF') rfl
      have h1 : (φ'.shift).Scoped (k + 1) := h.1
      have := I.scoped_subst h1 σ.sc
      rwa [shift_subst_tail] at this
    have hor' : I.Entails .one (I.or (φ'.subst σ.tail.τ) (.neg (σ.τ 0))) :=
      ent_trans (hψσ k3 σ hh) (ent_or_elim (ent_trans (ent_subst h12 _) (ent_or_left _ _)) (ent_or_right _ _))
    refine RE2_split_r hW hsφ' (hσ0 k3 σ) hor' (hAσ k3 σ.tail) hsp
      (RE2.typed (RE2.isub hW hu0 σ.tail)).1 (fun k4 σ4 h => ?_) (fun k4 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      exact u0l k4 _ _ (I.scoped_subst (show (I.and (σ.τ 0) .zero).Scoped k3 from ⟨hσ0 k3 σ, trivial⟩) σ4.sc)
        (ieq_and_zero_right _) (ent_trans (ent_comp_inv h) (ent_subst h21 _))
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact RE2.isub hW hu0 _

end

end Model.Whnf
