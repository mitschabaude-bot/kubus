import Model.Whnf.Valid2ElimH17
import Model.Whnf.Kan2GlueTP

/-! # Formal composition computation at every restriction -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' : ℕ}

theorem elimHcompTm_isub (d : ℕ) (P M bs u a : Tm) (φ : I) (σ : ISub k' k) :
    (elimHcompTm d P M bs φ u a).isub σ =
      elimHcompTm d (P.isub σ) (M.isub σ) (bs.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ) := by
  simpa only [Tm.isub, up_var] using
    (elimHcomp_subst (σ := Tm.var) (τ := σ.τ) d P M bs φ u a)

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
    (hH : D.isHIT = true) {K : ℕ} {P M bs : Tm}
    (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (H : ElimRelH S d D K P M bs P M bs)
include hW hD hH hP hPP H

/-- Elimination of a formal composition agrees with its contractum, even at restrictions
where the face holds. Only computability of its base, tube and boundary eliminations is used. -/
theorem elimHcomp_compH (ρ : ISub k K) {qs u a : Tm} {φ : I}
    (ht : HasTy S k .one [] (.hcomp (.data d qs) φ u a) (.data d (P.isub ρ)))
    (hu : TubeD S k (.data d (P.isub ρ)) φ u u)
    (ha : RE2 S k (.data d (P.isub ρ)) a a)
    (hb : HcompBnd2 S k (.data d (P.isub ρ)) φ u a)
    (iha : RE2 S k ((M.isub ρ).inst a)
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a)
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a))
    (ihu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst r))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst r))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst r)))
    (ihb : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst .zero))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst .zero))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) (a.isub σ))) :
    RE2 S k ((M.isub ρ).inst (.hcomp (.data d qs) φ u a))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (.hcomp (.data d qs) φ u a))
      (elimHcompTm d (P.isub ρ) (M.isub ρ) (bs.isub ρ) φ u a) := by
  have cr := hcomp_relD hW hD hH hP hPP ρ ht ht (EqTm.refl ht)
    (ent_refl _) (ent_refl _) hu hu hu ha hb hb
  have hT := H.mot k ρ _ _ cr
  obtain ⟨m, hE⟩ := H.tyL k ρ
  have he := minimal_to_spec (hE.elim_ty (spec_to_minimal hW ht))
  have hcan := (hcomp_data_retype hW ht (HasTy.isubS hW hP ρ)).1
  have ec := EqTm.elimHcomp hD hH hcan he
  have rc := em2_hcompH hW hD hH hP hPP H H ρ ht ht (ent_refl _) (ent_refl _)
    hu ha hb hb iha ihu ihb
  refine RE2.expandH hW hT he (HasTy.eqR ec) ?_
  intro k' σ
  have htσ := HasTy.isubS hW ht σ
  rw [isub_hcomp, data_isub_comp] at htσ
  have heσ := HasTy.isubS hW he σ
  have hTσ := RT2.isub hW (tyCode_of_ty hW he) hT σ
  have rcσ := RE2.isub hW rc σ
  have ecσ := EqTm.isubS hW ec σ
  by_cases hf : I.Entails .one (φ.subst σ.τ)
  · have es := EqTm.hcompFace hf htσ
    obtain ⟨m', hE'⟩ := H.tyL k' (ρ.comp σ)
    have ee := minimal_to_spec_eq (hE'.elim_congr (sigClosed_of_wfSig hW)
      (spec_to_minimal hW htσ) (spec_to_minimal hW (HasTy.eqR es)) (spec_to_minimal_eq hW es))
    have et : (Tm.elim d (P.isub (ρ.comp σ)).dshift (M.isub (ρ.comp σ)).dshift
        (bs.isub (ρ.comp σ)).dshift (u.isub σ.up)).dinst .one =
        .elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst .one) := by
      simp only [Tm.dinst, Tm.dsubst, Tm.subst, up_var]
      change Tm.elim d ((P.isub (ρ.comp σ)).dshift.dinst .one)
        ((M.isub (ρ.comp σ)).dshift.dinst .one) ((bs.isub (ρ.comp σ)).dshift.dinst .one) _ = _
      simp only [dshift_dinst]
    have st' : StableE S k' (((M.isub ρ).inst (.hcomp (.data d qs) φ u a)).isub σ)
        ((elimHcompTm d (P.isub ρ) (M.isub ρ) (bs.isub ρ) φ u a).isub σ)
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ))
          ((u.isub σ.up).dinst .one)) := by
      have ect : HasTy S k' .one []
          ((elimHcompTm d (P.isub ρ) (M.isub ρ) (bs.isub ρ) φ u a).isub σ) _ := HasTy.eqR ecσ
      rw [elimHcompTm_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub] at ect ⊢
      exact et ▸ stable_compFace hW hf ect
    refine ⟨Tm.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ))
      ((u.isub σ.up).dinst .one), ?_, ?_, ?_⟩
    · have r : Red S (.hcomp (.data d (qs.isub σ)) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ))
          ((u.isub σ.up).dinst .one) := .step (step_hcomp_face hf) (.refl _)
      simpa only [isub_elim, isub_hcomp, data_isub_comp, Tm.isub_isub] using
        red_elim_scrut (d := d) (ps := P.isub (ρ.comp σ)) (M := M.isub (ρ.comp σ)) (bs := bs.isub (ρ.comp σ)) r
    · simpa only [isub_elim, isub_hcomp, data_isub_comp, isub_inst, Tm.isub_isub] using ee
    · exact RE2.reduceL hW hTσ rcσ st' (by
        simpa only [isub_inst, isub_hcomp, data_isub_comp, Tm.isub_isub] using HasTy.eqR ee)
  · refine ⟨_, ?_, ecσ, rcσ⟩
    change Red S ((Tm.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (.hcomp (.data d qs) φ u a)).isub σ)
      ((elimHcompTm d (P.isub ρ) (M.isub ρ) (bs.isub ρ) φ u a).isub σ)
    rw [isub_elim, isub_hcomp, elimHcompTm_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
    exact .step (step_elimHcompH hD hH hf) (.refl _)

end

end Model.Whnf
