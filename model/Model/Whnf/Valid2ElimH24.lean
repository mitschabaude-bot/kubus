import Model.Whnf.Valid2ElimH23

/-! # Normalization of eliminations of formal composition heads -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k K : ℕ}

theorem elimLine_dinst (d : ℕ) (P M bs u : Tm) (r : I) :
    (Tm.elim d P.dshift M.dshift bs.dshift u).dinst r = .elim d P M bs (u.dinst r) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, up_var]
  change Tm.elim d (P.dshift.dinst r) (M.dshift.dinst r) (bs.dshift.dinst r) _ = _
  simp only [dshift_dinst]

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
    {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (H : ElimRelH S d D K P M bs P M bs)
include hW hD hH hP hPP H

/-- A formal composition head normalizes coherently when its tube eliminations do. -/
theorem elimNorm_hcompH (ρ : ISub k K) {qs u a : Tm} {φ : I}
    (ht : HasTy S k .one [] (.hcomp (.data d qs) φ u a) (.data d (P.isub ρ)))
    (hu : TubeD S k (.data d (P.isub ρ)) φ u u) (ha : RE2 S k (.data d (P.isub ρ)) a a)
    (hb : HcompBnd2 S k (.data d (P.isub ρ)) φ u a)
    (iha : RE2 S k ((M.isub ρ).inst a)
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a) (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a))
    (ihu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst r))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst r))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst r)))
    (ihb : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst .zero))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst .zero))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) (a.isub σ)))
    (Nu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      ElimNormH S d D K P M bs k' (ρ.comp σ) ((u.isub σ.up).dinst r)) :
    ElimNormH S d D K P M bs k ρ (.hcomp (.data d qs) φ u a) := by
  have RC := elimHcomp_compH hW hD hH hP hPP H ρ ht hu ha hb iha ihu ihb
  have cr := hcomp_relD hW hD hH hP hPP ρ ht ht (EqTm.refl ht)
    (ent_refl _) (ent_refl _) hu hu hu ha hb hb
  intro k' σ W hw
  have htσ := HasTy.isubS hW ht σ
  rw [isub_hcomp, data_isub_comp] at htσ
  have R := RE2.isub hW RC σ
  simp only [isub_inst, isub_elim, isub_hcomp, Tm.isub_isub] at R
  have hT := RT2.isub hW (RE2.tyCode hW RC) (H.mot k ρ _ _ cr) σ
  simp only [isub_inst, Tm.isub_isub, isub_hcomp] at hT
  have CR := RE2.isub hW cr σ
  rw [data_isub_comp] at CR
  by_cases hf : I.Entails .one (φ.subst σ.τ)
  · have es := EqTm.hcompFace hf htσ
    have rr : Red S ((Tm.hcomp (.data d qs) φ u a).isub σ) ((u.isub σ.up).dinst .one) :=
      .step (step_hcomp_face hf) (.refl _)
    have hw' : RedE S k' (.data d (P.isub (ρ.comp σ))) ((u.isub σ.up).dinst .one) W :=
      ⟨red_redW rr hw.1, es.symm.trans hw.2⟩
    have hφ := (gen_hcomp (spec_to_minimal hW ht) rfl).choose_spec.1.2.1
    have hh : (ival (idEnv k') (φ.subst σ.τ)).holds := (holds_iff_entails (I.scoped_subst hφ σ.sc)).2 hf
    have NN := Nu k' σ .one trivial hh
    have hc := closed_of_ty hW (HasTy.eqR es)
    have N := NN k' (ISub.id k') W (by rw [ISub.comp_id, isub_id_of_closed hc]; exact hw')
    rw [ISub.comp_id, isub_id_of_closed hc] at N
    have hs : StableE S k' (.data d (P.isub (ρ.comp σ)))
        ((Tm.hcomp (.data d qs) φ u a).isub σ) ((u.isub σ.up).dinst .one) := stable_hcompFace hW hf htσ
    have hA := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp σ)
    have er := RE2.reduceL hW hA CR hs (HasTy.eqR es)
    have TN := H.mot k' (ρ.comp σ) _ _ er
    obtain ⟨m, E⟩ := H.tyL k' (ρ.comp σ)
    have ee := minimal_to_spec_eq (E.elim_congr (sigClosed_of_wfSig hW) (spec_to_minimal hW htσ)
      (spec_to_minimal hW (HasTy.eqR es)) (spec_to_minimal_eq hW es))
    have htC := (RE2.typed R).2.1
    change HasTy S k' .one [] ((elimHcompTm d (P.isub ρ) (M.isub ρ) (bs.isub ρ) φ u a).isub σ) _ at htC
    have st : StableE S k' ((M.isub (ρ.comp σ)).inst ((Tm.hcomp (.data d qs) φ u a).isub σ))
        ((elimHcompTm d (P.isub ρ) (M.isub ρ) (bs.isub ρ) φ u a).isub σ)
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst .one)) := by
      rw [elimHcompTm_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub] at htC ⊢
      simpa only [elimLine_dinst] using stable_compFace hW hf htC
    have R' := RE2.reduceR hW hT R st (HasTy.eqR ee)
    exact RE2.trans hW hT R' (RE2.conv hW TN N)
  · have wh : RedW S ((Tm.hcomp (.data d qs) φ u a).isub σ) ((Tm.hcomp (.data d qs) φ u a).isub σ) :=
      redW_self (step_hcomp_HIT hD hH hf)
    obtain rfl := RedW.unique hw.1 wh
    change RE2 S k' _ _ (elimRedH d D (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ))
      (.hcomp (.data d (qs.isub σ)) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ)))
    rw [elimRedH_hcomp]
    simpa only [elimHcompTm_isub, Tm.isub_isub] using R

end

end Model.Whnf
