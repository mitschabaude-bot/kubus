import Model.Whnf.Kan2DataBasic

/-!
# Fillers of binary compositions, given the composition at their base

Versions of `hfill_rel` and `hfill_one_pt` which only use the composition at the (restrictions of
the) base of the filler (`KanH2At`), as the induction over the relation of an inductive type
provides it, and the corresponding facts for the heterogeneous filler `fill`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- Compositions in the types `L` and `L'` over the given bases, related at the type `A`, relate
related tubes. -/
def HC2 (S : Sig) (k : ℕ) (A L L' a a' : Tm) : Prop :=
  ∀ (φ φ' : I) (u u' : Tm), HasTy S k .one [] (.hcomp L φ u a) A → HasTy S k .one [] (.hcomp L' φ' u' a') A →
    EqTm S k .one [] (.hcomp L φ u a) (.hcomp L' φ' u' a') A →
    EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift →
    I.Entails φ φ' → I.Entails φ' φ → Tube2 S k A φ u u' → RE2 S k A a a' →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ)) →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) →
    RE2 S k A (.hcomp L φ u a) (.hcomp L' φ' u' a')

/-- Composition in related types relates related tubes over the given related bases. -/
abbrev KanH2At (S : Sig) (k : ℕ) (A A' a a' : Tm) : Prop := HC2 S k A A A' a a'

theorem KanH2.at {A A' : Tm} (h : KanH2 S k A A') (a a' : Tm) : KanH2At S k A A' a a' :=
  fun φ φ' u u' => h φ φ' u u' a a'

theorem KanH2.of_at {A A' : Tm} (h : ∀ a a', KanH2At S k A A' a a') : KanH2 S k A A' :=
  fun φ φ' u u' a a' => h a a' φ φ' u u'

variable (hW : WfSig S)
include hW

/-- Compositions related at a type are related at a related type. -/
theorem HC2.conv {A B L L' a a' : Tm} (hAB : RT2 S k A B) (hX : TyCode k (semK S k A)) (h : HC2 S k A L L' a a') :
    HC2 S k B L L' a a' := by
  intro φ φ' u u' hty hty' heq hteq h12 h21 htube haa hbd hbd'
  have hXB : TyCode k (semK S k B) := RT2.tyCode_r hW hAB hX
  have hBA : RT2 S k B A := RT2.symm hW hX hAB
  have eBA : TyEq S k B A := (Comp2_ty_base hBA).2.2.2.2.2
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hBAσ : ∀ k' (σ : ISub k' k), RT2 S k' (B.isub σ) (A.isub σ) := fun k' σ => RT2.isub hW hXB hBA σ
  have hABσ : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (B.isub σ) := fun k' σ => RT2.isub hW hX hAB σ
  refine RE2.conv hW hAB (h φ φ' u u' (hty.tyConv eBA) (hty'.tyConv eBA) (heq.tyConv eBA)
    (EqTm.cofConv hφs hteq eBA) h12 h21 (fun k' σ r r' hr hr' hE hh => ?_) (RE2.conv hW hBA haa)
    (fun k' σ hh => RE2.conv hW (hBAσ k' σ) (hbd k' σ hh)) (fun k' σ hh => RE2.conv hW (hBAσ k' σ) (hbd' k' σ hh)))
  exact RE2.conv hW (hBAσ k' σ) (htube k' σ r r' hr hr' hE hh)

/-- The fillers of related compositions are related, at pointwise equal restrictions. -/
theorem hfill_relAt {A A' u u' u0 u0' : Tm} {φ φ' : I} (hφs : φ.Scoped k)
    (hK : ∀ k3 (τ : ISub k3 k), KanH2At S k3 (A.isub τ) (A'.isub τ) (u0.isub τ) (u0'.isub τ)) (hAA : RT2 S k A A) (hTA : TyEq S k A A')
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift)
    (htyF : HasTy S (k + 1) .one [] (Tm.hfill A φ u u0) A.dshift)
    (htyF' : HasTy S (k + 1) .one [] (Tm.hfill A' φ' u' u0') A.dshift)
    (heqF : EqTm S (k + 1) .one [] (Tm.hfill A φ u u0) (Tm.hfill A' φ' u' u0') A.dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k A φ u u') (hu0 : RE2 S k A u0 u0')
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (u0'.isub σ))
    (hbd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (u0.isub σ) ((u'.isub σ.up).dinst .zero))
    {k3 : ℕ} (σ σ' : ISub k3 (k + 1)) (et : σ.tail = σ'.tail) (e0 : I.Eq (σ.τ 0) (σ'.τ 0)) :
    RE2 S k3 (A.dshift.isub σ) ((Tm.hfill A φ u u0).isub σ) ((Tm.hfill A' φ' u' u0').isub σ') := by
  have hS := sigClosed_of_wfSig hW
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
  obtain ⟨l1, ⟨-, hsψ', htF', -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW htyF') rfl
  have hφs' : φ'.Scoped k := scoped_unshift hsψ'.1
  have hσσ : ∀ i < k + 1, I.Eq (σ.τ i) (σ'.τ i) := by
    intro i hi; rcases i with _ | i
    · exact e0
    · have : σ.tail.τ i = σ'.tail.τ i := by rw [et]
      exact this ▸ I_eq_refl _
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
  have hχσ : I.Eq ((I.or φ'.shift (.neg (.var 0))).subst σ.τ) ((I.or φ'.shift (.neg (.var 0))).subst σ'.τ) :=
    ieq_subst_ptw hσσ hsψ'
  -- the judgmental equalities
  have heqσ : EqTm S k3 .one [] ((Tm.hfill A φ u u0).isub σ) ((Tm.hfill A' φ' u' u0').isub σ') (A.dshift.isub σ) :=
    (EqTm.isubS hW heqF σ).trans (eqTm_isub_ieq hW htyF' σ σ' hσσ trivial (ent_refl _) (ent_refl _))
  have htσ : EqTm S (k3 + 1) (cof .one ((I.or φ.shift (.neg (.var 0))).subst σ.τ)).shift []
      ((KubusCore.Meta.fillTube φ u u0).isub σ.up) ((KubusCore.Meta.fillTube φ' u' u0').isub σ'.up)
      (A.dshift.isub σ).dshift := by
    have t1 := EqTm.cofIsub hW hsψ htEqF σ
    have hup : ∀ i < k + 1 + 1, I.Eq (σ.up.τ i) (σ'.up.τ i) := by
      intro i hi; rcases i with _ | i
      · exact I_eq_refl _
      · exact ieq_shift (hσσ i (by omega))
    have hsc : (cof .one ((I.or φ.shift (.neg (.var 0))).subst σ.τ)).shift.Scoped (k3 + 1) :=
      KubusCore.I.scoped_shift ⟨trivial, I.scoped_subst hsψ σ.sc⟩
    have t2 := eqTm_isub_ieq hW (minimal_to_spec htF') σ.up σ'.up hup hsc
      (by
        show I.Entails _ (((cof .one (I.or φ'.shift (.neg (.var 0)))).shift).subst (I.up σ.τ))
        rw [I_shift_subst_up]
        exact ent_shift (ent_and_mono (ent_refl _) (ent_subst hface σ.τ)))
      (by
        show I.Entails _ (((cof .one (I.or φ'.shift (.neg (.var 0)))).shift).subst (I.up σ'.τ))
        rw [I_shift_subst_up]
        exact ent_shift (ent_and_mono (ent_refl _) (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ))))
    rw [isub_dshift] at t1 t2
    have e3 : TyEq S k3 (A'.dshift.isub σ) (A.dshift.isub σ) := by
      rw [dshift_isub_tail, dshift_isub_tail]; exact TyEq.symm (hTA.isub hW σ.tail)
    exact t1.trans (EqTm.cofConv (I.scoped_subst hsψ σ.sc) t2 e3)
  have hF := HasTy.isubS hW htyF σ
  have hF' := HasTy.isubS hW htyF' σ'
  have eAs : A.dshift.isub σ' = A.dshift.isub σ := by rw [dshift_isub_tail, dshift_isub_tail, et]
  rw [eAs] at hF'
  have eA' : A'.dshift.isub σ' = A'.isub σ.tail := by rw [dshift_isub_tail, et]
  have eu0' : u0'.dshift.isub σ' = u0'.isub σ.tail := by rw [dshift_isub_tail, et]
  show RE2 S k3 (A.dshift.isub σ) (.hcomp (A.dshift.isub σ) ((I.or φ.shift (.neg (.var 0))).subst σ.τ)
      ((KubusCore.Meta.fillTube φ u u0).isub σ.up) (u0.dshift.isub σ))
    (.hcomp (A'.dshift.isub σ') ((I.or φ'.shift (.neg (.var 0))).subst σ'.τ)
      ((KubusCore.Meta.fillTube φ' u' u0').isub σ'.up) (u0'.dshift.isub σ'))
  change HasTy S k3 .one [] (.hcomp (A.dshift.isub σ) ((I.or φ.shift (.neg (.var 0))).subst σ.τ)
      ((KubusCore.Meta.fillTube φ u u0).isub σ.up) (u0.dshift.isub σ)) (A.dshift.isub σ) at hF
  change HasTy S k3 .one [] (.hcomp (A'.dshift.isub σ') ((I.or φ'.shift (.neg (.var 0))).subst σ'.τ)
      ((KubusCore.Meta.fillTube φ' u' u0').isub σ'.up) (u0'.dshift.isub σ')) (A.dshift.isub σ) at hF'
  change EqTm S k3 .one [] (.hcomp (A.dshift.isub σ) ((I.or φ.shift (.neg (.var 0))).subst σ.τ)
      ((KubusCore.Meta.fillTube φ u u0).isub σ.up) (u0.dshift.isub σ))
    (.hcomp (A'.dshift.isub σ') ((I.or φ'.shift (.neg (.var 0))).subst σ'.τ)
      ((KubusCore.Meta.fillTube φ' u' u0').isub σ'.up) (u0'.dshift.isub σ')) (A.dshift.isub σ) at heqσ
  rw [eA', eu0'] at hF' heqσ ⊢
  simp only [dshift_isub_tail] at hF hF' heqσ htσ ⊢
  refine hK k3 σ.tail _ _ _ _ hF hF' heqσ htσ (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ))
    (ent_trans (eq_ent (I_eq_symm hχσ)) (ent_subst hface' σ.τ)) (fun k4 σ2 x x' hx hx' hEx hh => ?_)
    (RE2.isub hW hu0 σ.tail) (fun k4 σ2 hh => ?_) (fun k4 σ2 hh => ?_)
  · -- the tubes of the fillers
    have hh2 : (ival (idEnv k4) ((I.or φ.shift (.neg (.var 0))).subst (σ.comp σ2).τ)).holds := by
      rw [I_subst_comp]; exact hh
    have hh2' : (ival (idEnv k4) ((I.or φ'.shift (.neg (.var 0))).subst (σ'.comp σ2).τ)).holds := by
      rw [I_subst_comp]
      exact entails_holds (ent_subst (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ)) σ2.τ) hh
    have hsp : HasTy S k4 .one [] (((KubusCore.Meta.fillTube φ u u0).isub (σ.comp σ2).up).dinst x)
        (A.dshift.isub (σ.comp σ2)) := hcomp_tube_typed' hW (HasTy.isubS hW htyF (σ.comp σ2)) x hx hh2
    have hsp' : HasTy S k4 .one [] (((KubusCore.Meta.fillTube φ' u' u0').isub (σ'.comp σ2).up).dinst x')
        (A.dshift.isub (σ'.comp σ2)) := hcomp_tube_typed' hW (HasTy.isubS hW htyF' (σ'.comp σ2)) x' hx' hh2'
    simp only [fillTube_isub_dinst, dshift_isub_tail, ISub.comp_tail] at hsp hsp'
    rw [← et] at hsp'
    rw [Tm.isub_isub (KubusCore.Meta.fillTube φ u u0), Tm.isub_isub (KubusCore.Meta.fillTube φ' u' u0'),
      ← ISub.up_comp, ← ISub.up_comp, fillTube_isub_dinst, fillTube_isub_dinst, ISub.comp_tail, ISub.comp_tail,
      ← et, Tm.isub_isub A]
    have hyy' : I.Eq ((σ.comp σ2).τ 0) ((σ'.comp σ2).τ 0) := I_eq_subst e0 σ2.τ
    have hy := hσ0 k4 (σ.comp σ2)
    have hy' := hσ0 k4 (σ'.comp σ2)
    have hor := hψσ k4 (σ.comp σ2) hh2
    rw [ISub.comp_tail] at hor
    refine RE2_sys2 hW (I.scoped_subst hφs (σ.tail.comp σ2).sc) (I.scoped_subst hφs' (σ.tail.comp σ2).sc) hy hy'
      (ent_subst h12 _) (ent_subst h21 _) (eq_ent (ieq_neg hyy')) (eq_ent (ieq_neg (I_eq_symm hyy'))) hor
      (hAσ k4 _) hsp hsp' (fun k5 σ4 h => ?_) (fun k5 σ4 h h' => ?_) (fun k5 σ4 h h' => ?_) (fun k5 σ4 h' => ?_)
    · rw [dinst_up_isub, dinst_up_isub, Tm.isub_isub]
      exact uu k5 _ _ _ (I.scoped_subst (show (I.and _ x).Scoped k4 from ⟨hy, hx⟩) σ4.sc)
        (I.scoped_subst (show (I.and _ x').Scoped k4 from ⟨hy', hx'⟩) σ4.sc)
        (I_eq_subst (ieq_and_congr hyy' hEx) _) (ent_comp_inv h)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      have e0' := ieq_zero_of_holds_neg (I.scoped_subst hy σ4.sc)
        (entails_holds h' (ρ := idEnv k5) (by rw [ival_one]; rfl))
      exact u0r k5 _ _ (I.scoped_subst (show (I.and _ x).Scoped k4 from ⟨hy, hx⟩) σ4.sc)
        (ieq_and_zero_left _ e0') (ent_comp_inv h)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      have e0' := ieq_zero_of_holds_neg (I.scoped_subst hy σ4.sc)
        (entails_holds h' (ρ := idEnv k5) (by rw [ival_one]; rfl))
      exact u0l k5 _ _ (I.scoped_subst (show (I.and _ x').Scoped k4 from ⟨hy', hx'⟩) σ4.sc)
        (ieq_and_zero_left _ (I_eq_trans (I_eq_subst (I_eq_symm hyy') _) e0')) (ent_comp_inv h)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact RE2.isub hW hu0 _
  · -- the boundary of the tubes, on the left
    have hh2 : (ival (idEnv k4) ((I.or φ.shift (.neg (.var 0))).subst (σ.comp σ2).τ)).holds := by
      rw [I_subst_comp]; exact hh
    have hsp : HasTy S k4 .one [] (((KubusCore.Meta.fillTube φ u u0).isub (σ.comp σ2).up).dinst .zero)
        (A.dshift.isub (σ.comp σ2)) := hcomp_tube_typed' hW (HasTy.isubS hW htyF (σ.comp σ2)) .zero trivial hh2
    simp only [fillTube_isub_dinst, dshift_isub_tail, ISub.comp_tail] at hsp
    rw [Tm.isub_isub (KubusCore.Meta.fillTube φ u u0), ← ISub.up_comp, fillTube_isub_dinst, ISub.comp_tail,
      Tm.isub_isub A, Tm.isub_isub u0']
    have hy := hσ0 k4 (σ.comp σ2)
    have hor := hψσ k4 (σ.comp σ2) hh2
    rw [ISub.comp_tail] at hor
    refine RE2_split_l hW (I.scoped_subst hφs (σ.tail.comp σ2).sc) hy hor (hAσ k4 _) hsp
      (RE2.typed (RE2.isub hW hu0 (σ.tail.comp σ2))).2.1 (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      exact u0r k5 _ _ (I.scoped_subst (show (I.and _ .zero).Scoped k4 from ⟨hy, trivial⟩) σ4.sc)
        (ieq_and_zero_right _) (ent_comp_inv h)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact RE2.isub hW hu0 _
  · -- the boundary of the tubes, on the right
    have hh2 : (ival (idEnv k4) ((I.or φ.shift (.neg (.var 0))).subst (σ.comp σ2).τ)).holds := by
      rw [I_subst_comp]; exact hh
    have hh2' : (ival (idEnv k4) ((I.or φ'.shift (.neg (.var 0))).subst (σ'.comp σ2).τ)).holds := by
      rw [I_subst_comp]
      exact entails_holds (ent_subst (ent_trans (ent_subst hface σ.τ) (eq_ent hχσ)) σ2.τ) hh
    have hsp : HasTy S k4 .one [] (((KubusCore.Meta.fillTube φ' u' u0').isub (σ'.comp σ2).up).dinst .zero)
        (A.dshift.isub (σ'.comp σ2)) := hcomp_tube_typed' hW (HasTy.isubS hW htyF' (σ'.comp σ2)) .zero trivial hh2'
    simp only [fillTube_isub_dinst, dshift_isub_tail, ISub.comp_tail] at hsp
    rw [← et] at hsp
    rw [Tm.isub_isub (KubusCore.Meta.fillTube φ' u' u0'), ← ISub.up_comp, fillTube_isub_dinst, ISub.comp_tail, ← et,
      Tm.isub_isub A, Tm.isub_isub u0]
    have hyy' : I.Eq ((σ.comp σ2).τ 0) ((σ'.comp σ2).τ 0) := I_eq_subst e0 σ2.τ
    have hy' := hσ0 k4 (σ'.comp σ2)
    have hor := hψσ k4 (σ.comp σ2) hh2
    rw [ISub.comp_tail] at hor
    have hor' : I.Entails .one (I.or (φ'.subst (σ.tail.comp σ2).τ) (.neg ((σ'.comp σ2).τ 0))) :=
      ent_trans hor (ent_or_elim (ent_trans (ent_subst h12 _) (ent_or_left _ _))
        (ent_trans (eq_ent (ieq_neg hyy')) (ent_or_right _ _)))
    refine RE2_split_r hW (I.scoped_subst hφs' (σ.tail.comp σ2).sc) hy' hor' (hAσ k4 _) hsp
      (RE2.typed (RE2.isub hW hu0 (σ.tail.comp σ2))).1 (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      exact u0l k5 _ _ (I.scoped_subst (show (I.and _ .zero).Scoped k4 from ⟨hy', trivial⟩) σ4.sc)
        (ieq_and_zero_right _) (ent_trans (ent_comp_inv h) (ent_subst h21 _))
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact RE2.isub hW hu0 _

/-- The end of a filler, against its composition. -/
theorem hfill_one_ptAt {A v v0 : Tm} {φ : I} (hφs : φ.Scoped k) (hX : TyCode k (semK S k A)) (hAA : RT2 S k A A)
    (hK : ∀ k3 (τ : ISub k3 k), KanH2At S k3 (A.isub τ) (A.isub τ) (v0.isub τ) (v0.isub τ))
    (htyH : HasTy S k .one [] (.hcomp A φ v v0) A)
    (htyF : HasTy S (k + 1) .one [] (Tm.hfill A φ v v0) A.dshift) (htube : Tube2 S k A φ v v)
    (hv0 : RE2 S k A v0 v0)
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((v.isub σ.up).dinst .zero) (v0.isub σ))
    {k3 : ℕ} (τ : ISub k3 k) :
    RE2 S k3 (A.isub τ) ((Tm.hfill A φ v v0).isub (ISub.cons .one trivial τ)) ((Tm.hcomp A φ v v0).isub τ) := by
  have hS := sigClosed_of_wfSig hW
  have hAτ := RT2.isub hW hX hAA τ
  obtain ⟨l0, ⟨hA0, hφ0, hu0', hv00, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW htyH) rfl
  have hH := HasTy.isubS hW htyF (ISub.cons .one trivial τ)
  rw [hfill_isub_cons, dshift_isub_cons] at hH
  have hH' := HasTy.isubS hW htyH τ
  have heq := EqTm.isubS hW (minimal_to_spec_eq (hfill_typed hS hA0 hφ0 hu0' hv00 hside).2.2.1) τ
  rw [isub_dinst] at heq
  change EqTm S k3 .one [] (((Tm.hfill A φ v v0).isub τ.up).dinst .one) _ _ at heq
  rw [isub_up_dinst _ τ .one trivial, hfill_isub_cons] at heq
  have hsc1 : (I.or φ (.neg .one)).Scoped k := ⟨hφs, trivial⟩
  have ht := EqTm.cofIsub hW hsc1 (minimal_to_spec_eq (hfill1_tube_eq hS hA0 hφ0 hu0' hv00 hside)) τ
  rw [up_inst0_one_isub, isub_dshift] at ht
  rw [hfill_isub_cons]
  have hholds : ∀ {k4 : ℕ} (σ2 : ISub k4 k3), (ival (idEnv k4) ((I.or (φ.subst τ.τ) (.neg .one)).subst σ2.τ)).holds →
      (ival (idEnv k4) (φ.subst (τ.comp σ2).τ)).holds ∧ I.Entails .one (φ.subst (τ.comp σ2).τ) := by
    intro k4 σ2 hh
    have h1 := (holds_iff_entails (I.scoped_subst (show (I.or (φ.subst τ.τ) (.neg .one)).Scoped k3 from
      ⟨I.scoped_subst hφs τ.sc, trivial⟩) σ2.sc)).1 hh
    have h2 : I.Entails .one (φ.subst (τ.comp σ2).τ) := by
      rw [I_subst_comp]; exact ent_trans h1 (ent_neg_one _)
    exact ⟨(holds_iff_entails (I.scoped_subst hφs (τ.comp σ2).sc)).2 h2, h2⟩
  have pts : ∀ {k4 : ℕ} (σ2 : ISub k4 k3) (x : I),
      (((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons .one trivial τ).up).isub σ2.up).dinst x =
        .split (φ.subst (τ.comp σ2).τ) ((v.isub (τ.comp σ2).up).dinst (.and .one x)) (.neg .one) (v0.isub (τ.comp σ2)) := by
    intro k4 σ2 x
    rw [Tm.isub_isub, ← ISub.up_comp, ISub.cons_comp, fillTube_isub_dinst, ISub.tail_cons]; rfl
  have nen1 : ∀ {k4 k5 : ℕ} (σ4 : ISub k5 k4), ¬ I.Entails .one ((I.neg I.one).subst σ4.τ) :=
    fun σ4 => by show ¬ I.Entails .one (I.neg .one); decide
  refine hK k3 τ _ _ _ _ hH hH' heq ht (ent_neg_one _) (ent_or_left _ _) (fun k4 σ2 x x' hx hx' hEx hh => ?_)
    (RE2.isub hW hv0 τ) (fun k4 σ2 hh => ?_) (fun k4 σ2 hh => ?_)
  · have hA4 := RT2.isub hW hX hAA (τ.comp σ2)
    obtain ⟨hh4, hf4⟩ := hholds σ2 hh
    have hsp : HasTy S k4 .one [] ((((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons .one trivial τ).up).isub
        σ2.up).dinst x) ((A.isub τ).isub σ2) := hcomp_tube_typed' hW (HasTy.isubS hW hH σ2) x hx hh
    rw [pts, Tm.isub_isub] at hsp
    change RE2 S k4 _ _ (((v.isub τ.up).isub σ2.up).dinst x')
    rw [pts, Tm.isub_isub A, Tm.isub_isub v, ← ISub.up_comp]
    have r := htube k4 (τ.comp σ2) x x' hx hx' hEx hh4
    refine RE2_split_l hW (I.scoped_subst hφs (τ.comp σ2).sc) (show (I.neg I.one).Scoped k4 from trivial)
      (ent_trans hf4 (ent_or_left _ _)) hA4 hsp (RE2.typed r).2.1 (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, dinst_up_isub, Tm.isub_isub]
      exact htube k5 _ _ _ (I.scoped_subst (show (I.and I.one x).Scoped k4 from ⟨trivial, hx⟩) σ4.sc)
        (I.scoped_subst hx' σ4.sc) (I_eq_subst (I_eq_trans (I_eq_and_one_l x) hEx) _)
        ((holds_iff_entails (I.scoped_subst hφs ((τ.comp σ2).comp σ4).sc)).2 (ent_comp_inv h))
    · exact absurd h (nen1 σ4)
  · have hA4 := RT2.isub hW hX hAA (τ.comp σ2)
    obtain ⟨hh4, hf4⟩ := hholds σ2 hh
    have hsp : HasTy S k4 .one [] ((((KubusCore.Meta.fillTube φ v v0).isub (ISub.cons .one trivial τ).up).isub
        σ2.up).dinst .zero) ((A.isub τ).isub σ2) := hcomp_tube_typed' hW (HasTy.isubS hW hH σ2) .zero trivial hh
    rw [pts, Tm.isub_isub] at hsp
    change RE2 S k4 _ _ ((v0.isub τ).isub σ2)
    rw [pts, Tm.isub_isub A, Tm.isub_isub v0]
    have r := hbd k4 (τ.comp σ2) hh4
    refine RE2_split_l hW (I.scoped_subst hφs (τ.comp σ2).sc) (show (I.neg I.one).Scoped k4 from trivial)
      (ent_trans hf4 (ent_or_left _ _)) hA4 hsp (RE2.typed r).2.1 (fun k5 σ4 h => ?_) (fun k5 σ4 h => ?_)
    · rw [dinst_up_isub, Tm.isub_isub, Tm.isub_isub]
      have hh5 := (holds_iff_entails (I.scoped_subst hφs ((τ.comp σ2).comp σ4).sc)).2 (ent_comp_inv h)
      exact RE2.trans hW (RT2.isub hW hX hAA _) (htube k5 _ _ .zero
        (I.scoped_subst (show (I.and I.one I.zero).Scoped k4 from ⟨trivial, trivial⟩) σ4.sc) trivial
        (fun _ => rfl) hh5) (hbd k5 _ hh5)
    · exact absurd h (nen1 σ4)
  · obtain ⟨hh4, -⟩ := hholds σ2 hh
    change RE2 S k4 _ ((v0.isub τ).isub σ2) (((v.isub τ.up).isub σ2.up).dinst .zero)
    rw [Tm.isub_isub A, Tm.isub_isub v0, Tm.isub_isub v, ← ISub.up_comp]
    exact RE2.symm hW (RT2.isub hW hX hAA _) (hbd k4 (τ.comp σ2) hh4)


end

end Model.Whnf
