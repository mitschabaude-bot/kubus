import Model.Canon.KanDerived
import Model.Canon.KanSigma

/-!
# Canonicity: the Kan operations at path types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem dshift_dinst' (t : Tm) (r : I) : t.dshift.subst .var (I.inst0 r) = t := dshift_dinst t r

theorem hcompPath_body (A a b u p0 : Tm) (φ r : I) : ∃ t, Tm.hcompPath A a b φ u p0 = .plam t ∧
    t.dinst r = .hcomp (A.dinst r) (.or φ (.or (.neg r) r))
      (.split φ.shift (.papp u r.shift) (.or (.neg r.shift) r.shift) (.split (.neg r.shift) a.dshift r.shift b.dshift))
      (.papp p0 r) := by
  refine ⟨_, rfl, ?_⟩
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, I.subst, I_shift_inst0]
  have hφ : φ.shift.shift.subst (I.up (I.inst0 r)) = φ.shift := by
    rw [I_shift_subst_up, I_shift_inst0]
  have hd : ∀ x : Tm, x.dshift.dshift.subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 r)) = x.dshift := by
    intro x; simp only [dshift_eq, subst_subst]
    exact subst_congr (fun _ => rfl) (fun i => rfl) x
  rw [hφ, hd a, hd b, dshift_dinst']
  congr 3
  simp only [subst_subst]
  exact subst_id_of (fun _ => rfl) (fun i => by rcases i with _ | i <;> rfl) u

theorem isub_hcompPath (A a b u p0 : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.hcompPath A a b φ u p0).isub σ =
      Tm.hcompPath (A.isub σ.up) (a.isub σ) (b.isub σ) (φ.subst σ.τ) (u.isub σ.up) (p0.isub σ) := by
  show (Tm.hcompPath A a b φ u p0).subst .var σ.τ = _
  rw [hcompPath_subst, show dupS Tm.var = Tm.var from funext fun n => rfl]; rfl

theorem isub_isub_up_cons (X : Tm) (σ : ISub k' k) {k'' : ℕ} (r : I) (hr : r.Scoped k'') (σ' : ISub k'' k') :
    (X.isub σ.up).isub (ISub.cons r hr σ') = (X.isub (σ.comp σ').up).dinst r := by
  rw [← isub_up_dinst _ _ r hr, Tm.isub_isub]
  exact congrArg (fun s => (X.isub s).dinst r) (ISub.up_comp σ σ').symm

variable (hW : WfSig S)
include hW

theorem tyEq_dinst_ieq {A : Tm} {l : ℕ} (hA : HasTy0 S (k + 1) .one [] A (.univ l)) (ρ : ISub k' k) {x1 x2 : I}
    (h1 : x1.Scoped k') (h2 : x2.Scoped k') (he : I.Eq x1 x2) :
    TyEq S k' ((A.isub ρ.up).dinst x1) ((A.isub ρ.up).dinst x2) :=
  tyEq_ieq hW hA (τ1 := fun i => (ρ.up.τ i).subst (I.inst0 x1)) (τ2 := fun i => (ρ.up.τ i).subst (I.inst0 x2))
    (fun i hi => I.scoped_subst (ρ.up.sc i hi) (fun j hj => by rcases j with _ | j <;> simp [I.inst0, I.Scoped] <;> omega))
    (fun i hi => I.scoped_subst (ρ.up.sc i hi) (fun j hj => by rcases j with _ | j <;> simp [I.inst0, I.Scoped] <;> omega))
    (fun i hi => by
      rcases i with _ | i
      · exact he
      · show I.Eq (((ρ.τ i).shift).subst (I.inst0 x1)) (((ρ.τ i).shift).subst (I.inst0 x2))
        rw [I_shift_inst0, I_shift_inst0]; exact I_eq_refl _)
    (isub_dinst_eq _ _ _) (isub_dinst_eq _ _ _)

theorem kanH_path {A a b : Tm} {l : ℕ} (hpath : HasTy S k .one [] (.path A a b) (.univ l))
    (hA : ∀ k' (ρ : ISub k' (k + 1)), KanH S k' (A.isub ρ))
    (ha : RE S k (A.dinst .zero) a) (hb : RE S k (A.dinst .one) b) : KanH S k (.path A a b) := by
  have hS := sigClosed_of_wfSig hW
  have hAt := HasTy0.pathLine hS (spec_to_minimal hW hpath)
  intro φ u p0 hty hu hp0
  obtain ⟨-, ⟨-, hφ, -, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
  have e := EqTm.hcompPath hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  refine RE_path_intro hW hpath (HasTy.eqR e) fun k' σ r hr => ?_
  obtain ⟨t, ht, htr⟩ := hcompPath_body (A.isub σ.up) (a.isub σ) (b.isub σ) (u.isub σ.up) (p0.isub σ) (φ.subst σ.τ) r
  have hf := HasTy.isubS hW (HasTy.eqR e) σ
  rw [isub_hcompPath, ht, isub_path] at hf
  rw [isub_hcompPath, ht]
  have hβ := EqTm.pathBeta (HasTy.papp hf hr)
  rw [htr] at hβ
  have KH := hA k' (ISub.cons r hr σ)
  rw [← isub_up_dinst _ σ r hr] at KH
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm hβ)
  refine KH _ _ _ (HasTy.eqR hβ) (fun k'' σ' r' hr' hh => ?_) ?_
  · rw [isub_up_dinst _ σ' r' hr']
    have h0 := spec_to_minimal hW (HasTy.eqR hβ)
    obtain ⟨-, ⟨-, hψ, htube, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) h0 rfl
    have hT := HasTy0.isub hS (Ψ' := k'') (Φ' := .one) (τ := (ISub.cons r' hr' σ').τ) htube
      (fun i hi => (ISub.cons r' hr' σ').sc i hi)
      (ent_cof_cons hW hψ r' hr' σ' hh)
      (Wf0.nil trivial)
    have hT' := minimal_to_spec hT
    rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons] at hT'
    have hrs : (r.subst σ'.τ).Scoped k'' := I.scoped_subst hr σ'.sc
    have hTy : ((A.isub σ.up).dinst r).isub σ' = (A.isub (σ.comp σ').up).dinst (r.subst σ'.τ) := by
      rw [isub_dinst, Tm.isub_isub, ISub.up_comp]
    rw [hTy] at hT' ⊢
    rcases holds_or hh with h1 | h23
    · have e := EqTm.splitL (by
        show I.Entails .one ((φ.subst σ.τ).shift.subst (ISub.cons r' hr' σ').τ)
        rw [I_shift_cons]
        exact entails_of_holds (I.scoped_subst (I.scoped_subst hφ σ.sc) σ'.sc) h1) hT'
      have h2 := hu k'' (σ.comp σ') r' hr' (by rw [I_subst_comp]; exact h1)
      rw [isub_path] at h2
      have h3 := RE_path_elim hW h2 (r.subst σ'.τ) hrs
      refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
      show RE S k'' _ (Tm.papp ((u.isub σ.up).isub (ISub.cons r' hr' σ')) (r.shift.subst (ISub.cons r' hr' σ').τ))
      rw [isub_isub_up_cons, I_shift_cons]
      exact h3
    · have hor : I.Entails .one ((I.or (.neg r.shift) r.shift).subst (ISub.cons r' hr' σ').τ) := by
        show I.Entails .one (I.or (.neg (r.shift.subst (ISub.cons r' hr' σ').τ)) (r.shift.subst (ISub.cons r' hr' σ').τ))
        rw [I_shift_cons]
        exact entails_of_holds (show (I.or (.neg (r.subst σ'.τ)) (r.subst σ'.τ)).Scoped k'' from ⟨hrs, hrs⟩) h23
      have e1 := EqTm.splitR hor hT'
      rcases holds_or h23 with h2 | h3
      · have e2 := EqTm.splitL (by
          show I.Entails .one (.neg (r.shift.subst (ISub.cons r' hr' σ').τ))
          rw [I_shift_cons]; exact entails_of_holds (show (I.neg (r.subst σ'.τ)).Scoped k'' from hrs) h2)
          (HasTy.eqR e1)
        have h4 := ha.isub hW (σ.comp σ')
        rw [isub_dinst] at h4
        have h5 := h4.conv_ty hW (tyEq_dinst_ieq hW hAt (σ.comp σ') trivial hrs
          (I_eq_symm (ieq_zero_of_holds_neg hrs h2)))
        refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm (EqTm.trans e1 e2))
        show RE S k'' _ ((a.isub σ).dshift.isub (ISub.cons r' hr' σ'))
        rw [dshift_isub_cons, Tm.isub_isub]; exact h5
      · have e2 := EqTm.splitR (by
          show I.Entails .one (r.shift.subst (ISub.cons r' hr' σ').τ)
          rw [I_shift_cons]; exact entails_of_holds hrs h3)
          (HasTy.eqR e1)
        have h4 := hb.isub hW (σ.comp σ')
        rw [isub_dinst] at h4
        have h5 := h4.conv_ty hW (tyEq_dinst_ieq hW hAt (σ.comp σ') trivial hrs
          (I_eq_symm (ieq_one_of_holds hrs h3)))
        refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm (EqTm.trans e1 e2))
        show RE S k'' _ ((b.isub σ).dshift.isub (ISub.cons r' hr' σ'))
        rw [dshift_isub_cons, Tm.isub_isub]; exact h5
  · have h1 := hp0.isub hW σ
    rw [isub_path] at h1
    exact RE_path_elim hW h1 r hr

end

end Model.Canon
