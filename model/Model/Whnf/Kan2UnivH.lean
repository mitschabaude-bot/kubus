import Model.Whnf.Kan2Univ
import Model.Whnf.Kan2Glue
import Model.Whnf.Valid2LineEquivB
import Model.Whnf.NearAll
import Model.Whnf.Fund2

/-!
# Binary composition in universes

`hcomp U [ψ ↦ u] a` computes to the Glue type `hcompU ψ u a = Glue a [ψ ↦ (u(1), lineEquiv (u⁻))]`.
Related compositions give related contracta (`RE2_hcompU`): the bases are related, and the
equivalences are related by the binary validity of `lineEquiv` (`VEq.lineEquiv₂`), applied to the
restricted tubes as closed lines. Transport is only used along lines of level `l` (`KTAt S l`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem subst_closed_isub {t : Tm} {Ψ : ℕ} (hc : t.closedB 0 Ψ = true) (γ : ℕ → Tm) (σ : ISub k Ψ) :
    t.subst γ σ.τ = t.isub σ :=
  closed_subst_eq t 0 Ψ γ Tm.var σ.τ σ.τ hc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun _ _ => rfl)

theorem near_inear (X : Tm) {Ψ : ℕ} {σ σ' : ISub k Ψ} (h : INear σ σ') : TmNear (X.isub σ) (X.isub σ') :=
  (TmNear.refl X).dsubst fun i => h i

theorem hcompU_isub (φ : I) (u u0 : Tm) (σ : ISub k' k) :
    (Tm.hcompU φ u u0).isub σ = Tm.hcompU (φ.subst σ.τ) (u.isub σ.up) (u0.isub σ) := by
  have h := hcompU_subst (σ := Tm.var) (τ := σ.τ) φ u u0
  rw [dupS_var] at h
  exact h

variable (hW : WfSig S)
include hW

/-- The diagonal related substitution of a restriction where a face holds (closed terms). -/
def CSub2.diagF (S : Sig) {Ψ : ℕ} (Φ : I) (σ : ISub k Ψ) (hface : I.Entails .one (Φ.subst σ.τ)) :
    CSub2 S Ψ Φ [] k where
  σ := σ
  σ' := σ
  hσ := INear.refl _
  γ := Tm.var
  γ' := Tm.var
  hγ _ := rfl
  hγ' _ := rfl
  face := hface
  look x A h := by simp [Ctx.lookup] at h
  lookT x A h := by simp [Ctx.lookup] at h

/-- Validity of closed terms under a face from their relation at every restriction where the face holds. -/
theorem valid_closed_ofF {Ψ : ℕ} {Φ : I} {t u A : Tm} (hΦ : Φ.Scoped Ψ) (ht : HasTy S Ψ Φ [] t A)
    (hu : HasTy S Ψ Φ [] u A)
    (hAA : ∀ k (θ : ISub k Ψ), I.Entails .one (Φ.subst θ.τ) → RT2 S k (A.isub θ) (A.isub θ))
    (h : ∀ k (θ : ISub k Ψ), I.Entails .one (Φ.subst θ.τ) → RE2 S k (A.isub θ) (t.isub θ) (u.isub θ)) :
    Valid2 S Ψ Φ [] t u A := by
  intro k c
  have ht0 := spec_to_minimal hW ht
  have hu0 := spec_to_minimal hW hu
  have htc : t.closedB 0 Ψ = true := closed_ty ht0
  have huc : u.closedB 0 Ψ = true := closed_ty hu0
  have hAc : A.closedB 0 Ψ = true := closedT_of_ty hW ht0
  simp only [CSub2.L, CSub2.R]
  rw [subst_closed_isub htc, subst_closed_isub huc, subst_closed_isub hAc, subst_closed_isub hAc]
  have huσ' := HasTy.restrict (Φ' := .one) trivial c.face' (HasTy.isubF hW hΦ hu c.σ')
  have hX : TyCode k (semK S k (A.isub c.σ)) := RE2.tyCode hW (h k c.σ c.face)
  have hAA' := RT2_near hW hX (hAA k c.σ c.face) (near_inear A c.hσ) (isTyK_of_ty hW huσ')
  refine ⟨hAA', RE2_near hW (hAA k c.σ c.face) (h k c.σ c.face) (near_inear u c.hσ) ?_⟩
  exact huσ'.tyConv (TyEq.symm (Comp2_ty_base hAA').2.2.2.2.2)

/-- A tube at an arbitrary restriction of its line. -/
theorem tubeAt {X u1 u2 : Tm} {ψ : I} (tube : Tube2 S k X ψ u1 u2) {k3 : ℕ} (ρ : ISub k3 (k + 1))
    (hh : (ival (idEnv k3) (ψ.subst ρ.tail.τ)).holds) : RE2 S k3 (X.isub ρ.tail) (u1.isub ρ) (u2.isub ρ) := by
  have := tube k3 ρ.tail (ρ.τ 0) (ρ.τ 0) (ρ.sc 0 (by omega)) (ρ.sc 0 (by omega)) (I_eq_refl _) hh
  rwa [isub_up_dinst _ _ _ (ρ.sc 0 (by omega)), isub_up_dinst _ _ _ (ρ.sc 0 (by omega)), ISub.cons_tail] at this

/-- Related tubes in a universe are valid together, under the face. -/
theorem tube_valid {u1 u2 : Tm} {ψ : I} {l : ℕ} (hψs : ψ.Scoped k)
    (hu1 : HasTy S (k + 1) (cof .one ψ).shift [] u1 (.univ l)) (hu2 : HasTy S (k + 1) (cof .one ψ).shift [] u2 (.univ l))
    (tube : Tube2 S k (.univ l) ψ u1 u2) : Valid2 S (k + 1) (cof .one ψ).shift [] u1 u2 (.univ l) := by
  have hc : (cof .one ψ).shift.Scoped (k + 1) := KubusCore.I.scoped_shift ⟨trivial, hψs⟩
  have hh : ∀ {k3} (θ : ISub k3 (k + 1)), I.Entails .one ((cof .one ψ).shift.subst θ.τ) →
      (ival (idEnv k3) (ψ.subst θ.tail.τ)).holds := fun θ h => by
    rw [holds_iff_entails (I.scoped_subst hψs θ.tail.sc)]
    have := ent_trans h (ent_subst (ent_shift (ent_and_right .one ψ)) θ.τ)
    rwa [shift_subst_tail] at this
  exact valid_closed_ofF hW hc hu1 hu2 (fun k3 θ _ => RT2_univ hW) (fun k3 θ h => tubeAt hW tube θ (hh θ h))


/-- The equivalences of the `hcompU` contracta of related tubes, valid together under the face. -/
theorem equiv_valid {u1 u2 a1 : Tm} {ψ : I} {l : ℕ} (hKT : KTAt S l) (hψs : ψ.Scoped k)
    (hu1 : HasTy S (k + 1) (cof .one ψ).shift [] u1 (.univ l)) (hu2 : HasTy S (k + 1) (cof .one ψ).shift [] u2 (.univ l))
    (hteq : EqTm S (k + 1) (cof .one ψ).shift [] u1 u2 (.univ l))
    (tube : Tube2 S k (.univ l) ψ u1 u2) (tube1 : Tube2 S k (.univ l) ψ u1 u1)
    (hside : EqTm S k (cof .one ψ) [] (u1.dinst .zero) a1 (.univ l)) (ha1 : HasTy S k .one [] a1 (.univ l))
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds →
      RE2 S k' (.univ l) ((u1.isub σ.up).dinst .zero) (a1.isub σ)) :
    Valid2 S k (cof .one ψ) [] (Tm.lineEquiv (u1.dsubst revI)) (Tm.lineEquiv (u2.dsubst revI))
      (Tm.equiv (u1.dinst .one) a1) := by
  have hS := sigClosed_of_wfSig hW
  have hX : (cof .one ψ).Scoped k := ⟨trivial, hψs⟩
  have hu10 := spec_to_minimal hW hu1
  have hw1 := wf_of_ty hu10
  have V12 : VEq S (k + 1) (cof .one ψ).shift [] u1 u2 (.univ l) :=
    ⟨spec_to_minimal_eq hW hteq, tube_valid hW hψs hu1 hu2 tube⟩
  have V11 : VTy S (k + 1) (cof .one ψ).shift [] u1 (.univ l) := ⟨hu10, tube_valid hW hψs hu1 hu1 tube1⟩
  have hB : VEq S (k + 1) (cof .one ψ).shift [] (u1.dsubst revI) (u2.dsubst revI) (.univ l) := by
    have := VEq.isubL hW (n := 1) (m := 1) (Ψ0 := k) (Φs := (cof .one ψ).shift) (Γ0 := []) revI
      (fun i hi => by rcases Nat.lt_one_iff.1 hi with rfl; exact (show 0 < k + 1 by omega))
      (fun i => rfl) (KubusCore.I.scoped_shift hX) (ent_sk1 _ (ent_refl _)) hw1 V12
    exact this
  have hLE := VEq.lineEquiv₂ hW (Ψ := k) (Φ := cof .one ψ) (Γ := []) hKT hB
  rw [rev_d0, rev_d1] at hLE
  have hw0 : Wf0 S (k + 0) (cof .one ψ) (Ctx.dren 0 []) := by
    rw [Ctx.dren_zero]; exact wf_unshift hS hw1
  have hX0 : I.Entails (cof .one ψ) ((cof .one ψ).subst (fun n => .var (n + 0))) := by
    rw [I_add0]; exact ent_refl _
  have e0 := VTy.lineIeq hW V11 (k := 0) (r := .neg .zero) (r' := .one) hX0 trivial trivial I_eq_neg_zero hw0
  have e1 := VTy.lineIeq hW V11 (k := 0) (r := .neg .one) (r' := .zero) hX0 trivial trivial I_eq_neg_one hw0
  rw [Ctx.dren_zero, sk_one0] at e0
  rw [Ctx.dren_zero, sk_zero0] at e1
  have hha : ∀ {k3} (θ : ISub k3 k), I.Entails .one ((cof .one ψ).subst θ.τ) →
      (ival (idEnv k3) (ψ.subst θ.τ)).holds := fun θ h => by
    rw [holds_iff_entails (I.scoped_subst hψs θ.sc)]
    exact ent_trans h (ent_subst (ent_and_right .one ψ) θ.τ)
  have hsideV : VEq S k (cof .one ψ) [] (u1.dinst .zero) a1 (.univ l) := by
    refine ⟨spec_to_minimal_eq hW hside, valid_closed_ofF hW hX (HasTy.eqL hside)
      (HasTy.restrict hX (ent_and_left _ _) ha1) (fun k3 θ _ => RT2_univ hW) fun k3 θ h => ?_⟩
    rw [isub_dinst]; exact hbd k3 θ (hha θ h)
  have eq := VEq.equiv₂ hW e0 (VEq.trans' hW e1 hsideV)
  exact (VEq.conv' hW hLE eq).v


/-- A Glue type whose face holds is stably its fibre, as an element of a universe. -/
theorem stable_glueU {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (h : I.Entails .one φ) : StableE S k (.univ l) (.glue A φ T e) T := by
  intro k' σ
  have hσ : I.Entails .one (φ.subst σ.τ) := by
    have := ent_subst h σ.τ; simpa [I.subst] using this
  have hGσ := HasTy.isubS hW hG σ
  rw [isub_glue] at hGσ ⊢
  exact ⟨.step (by simp [step, show I.entails .one (φ.subst σ.τ) = true from hσ]) (.refl _), EqTm.glueFace hσ hGσ⟩

/-- Related compositions in a universe whose face does not hold have related contracta. -/
theorem RE2_hcompU {X' : Tm} {ψ ψ' : I} {u u' a a' : Tm} {l : ℕ} (hKT : KTAt S l)
    (K : KD S k (.univ l) X' ψ ψ' u u' a a') (hR' : ∀ k' (σ : ISub k' k), RedT S k' (X'.isub σ) (.univ l))
    (hn : ¬ I.Entails .one ψ) :
    RE2 S k (.univ l) (Tm.hcompU ψ u a) (Tm.hcompU ψ' u' a') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l0, ⟨-, hψs, hu, ha, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW K.hty) rfl
  obtain ⟨l0', ⟨hX'0, -, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW K.hty') rfl
  have hR0 := hR' k (ISub.id k)
  rw [isub_id_of_closed (closed_ty hX'0)] at hR0
  have r := hcomp_retype hW K.hty' hR0.2
  have hty'U := r.1.tyConv hR0.2
  obtain ⟨-, ⟨-, hψs', hu', ha', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty'U) rfl
  have eL := EqTm.hcompU K.hty
  have eR := EqTm.hcompU hty'U
  have he := eL.symm.trans (K.heq.trans ((r.2.tyConv hR0.2).trans eR))
  have hG := HasTy.eqR eL
  have hG' := HasTy.eqR eR
  have hnh : ¬ (ival (idEnv k) ψ).holds := fun h => hn ((holds_iff_entails hψs).1 h)
  have hc : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds → I.Entails .one (cof .one (ψ.subst σ.τ)) :=
    fun σ hh => ent_cof_one hW ((holds_iff_entails (I.scoped_subst hψs σ.sc)).1 hh)
  have hc' : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds → I.Entails .one (cof .one (ψ'.subst σ.τ)) :=
    fun σ hh => ent_trans (hc σ hh) (ent_and_mono (ent_refl _) (ent_subst K.p12 σ.τ))
  have hUU : ∀ {k3 : ℕ}, RT2 S k3 (.univ l) (.univ l) := RT2_univ hW
  -- the tubes against themselves, and against the bases
  have hh21 : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (ψ'.subst σ.τ)).holds → (ival (idEnv k') (ψ.subst σ.τ)).holds :=
    fun σ hh => (holds_iff_entails (I.scoped_subst hψs σ.sc)).2
      (ent_trans ((holds_iff_entails (I.scoped_subst hψs' σ.sc)).1 hh) (ent_subst K.p21 σ.τ))
  have tube11 : Tube2 S k (.univ l) ψ u u := fun k' σ r r' hr hr' hE hh =>
    RE2.trans hW hUU (K.tube k' σ r r' hr hr' hE hh) (RE2.symm hW hUU (K.tube k' σ r' r' hr' hr' (I_eq_refl _) hh))
  have tube22 : Tube2 S k (.univ l) ψ' u' u' := fun k' σ r r' hr hr' hE hh =>
    RE2.trans hW hUU (RE2.symm hW hUU (K.tube k' σ r r hr hr (I_eq_refl _) (hh21 σ hh)))
      (K.tube k' σ r r' hr hr' hE (hh21 σ hh))
  have hbd1 : ∀ k' (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds →
      RE2 S k' (.univ l) ((u.isub σ.up).dinst .zero) (a.isub σ) := fun k' σ hh =>
    RE2.trans hW hUU (K.bd k' σ hh) (RE2.symm hW hUU (RE2.isub hW K.ha0 σ))
  have hbd2 : ∀ k' (σ : ISub k' k), (ival (idEnv k') (ψ'.subst σ.τ)).holds →
      RE2 S k' (.univ l) ((u'.isub σ.up).dinst .zero) (a'.isub σ) := fun k' σ hh =>
    RE2.trans hW hUU (RE2.symm hW hUU (K.bd' k' σ (hh21 σ hh))) (RE2.isub hW K.ha0 σ)
  have hu1 := minimal_to_spec hu
  have hu2 := minimal_to_spec hu'
  have hu2ψ : HasTy S (k + 1) (cof .one ψ).shift [] u' (.univ l) :=
    HasTy.restrict (KubusCore.I.scoped_shift ⟨trivial, hψs⟩) (ent_shift (ent_and_mono (ent_refl _) K.p12)) hu2
  have V := equiv_valid hW hKT hψs hu1 hu2ψ K.hteq K.tube tube11 (minimal_to_spec_eq hside) (minimal_to_spec ha) hbd1
  have VL := equiv_valid hW hKT hψs hu1 hu1 (EqTm.refl hu1) tube11 tube11 (minimal_to_spec_eq hside)
    (minimal_to_spec ha) hbd1
  have VR := equiv_valid hW hKT hψs' hu2 hu2 (EqTm.refl hu2) tube22 tube22 (minimal_to_spec_eq hside')
    (minimal_to_spec ha') hbd2
  simp only [hcompU_eq] at he hG hG' ⊢
  refine RE2_univ_of hW ⟨hG, hG', he⟩ (RT2_glue_intro hW hG hG' he hnh K.p12 K.p21
    (fun k' σ => RE2_univ_ty hW (RE2.isub hW K.ha0 σ)) (fun k' σ hh => ?_) (fun k' σ hh => ?_)
    (fun k' σ hh => ?_) (fun k' σ hh => ?_))
  · have := K.tube k' σ .one .one trivial trivial (I_eq_refl _) hh
    rw [isub_dinst, isub_dinst]; exact RE2_univ_ty hW this
  · have : RE2 S k' ((Tm.equiv (u.dinst .one) a).isub σ) ((Tm.lineEquiv (u.dsubst revI)).isub σ)
        ((Tm.lineEquiv (u'.dsubst revI)).isub σ) := (V k' (CSub2.diagF S (cof .one ψ) σ (hc σ hh))).2
    rwa [isub_equiv] at this
  · have : RE2 S k' ((Tm.equiv (u.dinst .one) a).isub σ) ((Tm.lineEquiv (u.dsubst revI)).isub σ)
        ((Tm.lineEquiv (u.dsubst revI)).isub σ) := (VL k' (CSub2.diagF S (cof .one ψ) σ (hc σ hh))).2
    rwa [isub_equiv] at this
  · have : RE2 S k' ((Tm.equiv (u'.dinst .one) a').isub σ) ((Tm.lineEquiv (u'.dsubst revI)).isub σ)
        ((Tm.lineEquiv (u'.dsubst revI)).isub σ) := (VR k' (CSub2.diagF S (cof .one ψ') σ (hc' σ hh))).2
    rwa [isub_equiv] at this

end

end Model.Whnf
