import Model.Whnf.Valid2ElimH16

/-!
# Formal composition stages of higher inductive elimination
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- A point of the eliminator's tube is elimination of the corresponding tube point. -/
theorem elimLine_pt {k' : ℕ} (d : ℕ) (P M bs u : Tm) (σ : ISub k' k) (r : I) :
    ((Tm.elim d P.dshift M.dshift bs.dshift u).isub σ.up).dinst r =
      .elim d (P.isub σ) (M.isub σ) (bs.isub σ) ((u.isub σ.up).dinst r) := by
  show ((Tm.elim d P.dshift M.dshift bs.dshift u).subst Tm.var σ.up.τ).subst Tm.var (I.inst0 r) = _
  simp only [Tm.subst, up_var]
  change Tm.elim d ((P.dshift.isub σ.up).dinst r) ((M.dshift.isub σ.up).dinst r)
    ((bs.dshift.isub σ.up).dinst r) ((u.isub σ.up).dinst r) = _
  simp only [isub_dshift, dshift_dinst]

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
    {K : ℕ} {P M bs Q M' bs' : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P))
    (HL : ElimRelH S d D K P M bs P M bs) (H : ElimRelH S d D K P M bs Q M' bs')
include hW hD hH hP hPP HL H

/-- The contracta of eliminations of related formal compositions are related. -/
theorem em2_hcompH (ρ : ISub k K) {qs qs' u u' a a' : Tm} {φ φ' : I}
    (ht : HasTy S k .one [] (.hcomp (.data d qs) φ u a) (.data d (P.isub ρ)))
    (ht' : HasTy S k .one [] (.hcomp (.data d qs') φ' u' a') (.data d (P.isub ρ)))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (hu : TubeD S k (.data d (P.isub ρ)) φ u u')
    (ha : RE2 S k (.data d (P.isub ρ)) a a')
    (hb : HcompBnd2 S k (.data d (P.isub ρ)) φ u a) (hb' : HcompBnd2 S k (.data d (P.isub ρ)) φ' u' a')
    (iha : RE2 S k ((M.isub ρ).inst a)
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) a)
      (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) a'))
    (ihu : ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst r))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst r))
        (.elim d (Q.isub (ρ.comp σ)) (M'.isub (ρ.comp σ)) (bs'.isub (ρ.comp σ)) ((u'.isub σ.up).dinst r)))
    (ihb : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' ((M.isub (ρ.comp σ)).inst ((u.isub σ.up).dinst .zero))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) ((u.isub σ.up).dinst .zero))
        (.elim d (P.isub (ρ.comp σ)) (M.isub (ρ.comp σ)) (bs.isub (ρ.comp σ)) (a.isub σ))) :
    RE2 S k ((M.isub ρ).inst (.hcomp (.data d qs) φ u a))
      (elimHcompTm d (P.isub ρ) (M.isub ρ) (bs.isub ρ) φ u a)
      (elimHcompTm d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) φ' u' a') := by
  have hPρ : HasTy S k .one [] (.data d (P.isub ρ)) (.univ D.level) := HasTy.isubS hW hP ρ
  have hA := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
  have hAσ := fun {k'} (σ : ISub k' k) => RT2.isub hW (tyCode_of_univ hW hPρ) hA σ
  have hs := (gen_hcomp (spec_to_minimal hW ht) rfl).choose_spec.1.2.1
  have hs' := (gen_hcomp (spec_to_minimal hW ht') rfl).choose_spec.1.2.1
  have hcan := (hcomp_data_retype hW ht hPρ).1
  have hPQ := (Comp2_ty_base (H.dat k ρ)).2.2.2.2.2
  obtain ⟨mR, hER⟩ := H.tyR k ρ
  have hQρ := minimal_to_spec hER.hdata
  have hcanR := (hcomp_data_retype hW (ht'.tyConv hPQ) hQρ).1
  have hcanR' := hcanR.tyConv hPQ.symm
  have aL := RE2.trans hW hA ha (RE2.symm hW hA ha)
  have uL : TubeD S k (.data d (P.isub ρ)) φ u u := fun k' σ r hr hh =>
    RE2.trans hW (hAσ σ) (hu k' σ r hr hh) (RE2.symm hW (hAσ σ) (hu k' σ r hr hh))
  have uR : TubeD S k (.data d (P.isub ρ)) φ' u' u' := by
    intro k' σ r hr hh
    have hh' : (ival (idEnv k') (φ.subst σ.τ)).holds :=
      (holds_iff_entails (I.scoped_subst hs σ.sc)).2
        (ent_trans ((holds_iff_entails (I.scoped_subst hs' σ.sc)).1 hh) (ent_subst h21 _))
    exact RE2.trans hW (hAσ σ) (RE2.symm hW (hAσ σ) (hu k' σ r hr hh')) (hu k' σ r hr hh')
  have uL2 := TubeD.toTube2 hW hA (ent_refl _) hcan hcan uL
  have u2 := TubeD.toTube2 hW hA h12 ht ht' hu
  have hK := H.dataKan.isub hW hP ρ
  obtain ⟨hF, hF', heF, RF⟩ := hfill_formal_rel2 hW hPρ hQρ (H.dat k ρ) hK hcan hcanR' h12 h21 hu ha hb hb'
  obtain ⟨hFL, -, -, RFL⟩ := hfill_formal_rel2 hW hPρ hPρ hA hK hcan hcan (ent_refl _) (ent_refl _) uL aL hb hb
  have RF' : ∀ k' (σ σ' : ISub k' (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k' (.data d (P.isub (ρ.comp σ.tail)))
        ((Tm.hfill (.data d (P.isub ρ)) φ u a).isub σ) ((Tm.hfill (.data d (Q.isub ρ)) φ' u' a').isub σ') := by
    intro k' σ σ' et e0
    have R := RF k' σ σ' et e0
    rw [dshift_isub_tail] at R
    change RE2 S k' (.data d ((P.isub ρ).isub σ.tail)) _ _ at R
    rwa [Tm.isub_isub] at R
  have RFL' : ∀ k' (σ σ' : ISub k' (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k' (.data d (P.isub (ρ.comp σ.tail)))
        ((Tm.hfill (.data d (P.isub ρ)) φ u a).isub σ) ((Tm.hfill (.data d (P.isub ρ)) φ u a).isub σ') := by
    intro k' σ σ' et e0
    have R := RFL k' σ σ' et e0
    rw [dshift_isub_tail] at R
    change RE2 S k' (.data d ((P.isub ρ).isub σ.tail)) _ _ at R
    rwa [Tm.isub_isub] at R
  have faceF := fun k' (σ : ISub k' k) r hr hh => hfill_face_pt hW hs (tyCode_of_univ hW hPρ) hA hF uL2 (τ := σ) r hr hh
  have zeroF := fun k' (σ : ISub k' k) => hfill_zero_pt hW hs (tyCode_of_univ hW hPρ) hA hF uL2 aL hb (τ := σ)
  have endF := hfill_one_pt hW hs (tyCode_of_univ hW hPρ) hA
    (fun k' σ => (hK.isub hW hPρ σ).1 k' (Hom.id k') _ _ (hAσ σ)) hcan hF uL2 aL hb (τ := ISub.id k)
  have hcF : (Tm.hfill (.data d (P.isub ρ)) φ u a).closedB 0 (k + 1) = true := closed_of_ty hW hF
  change RE2 S k ((Tm.data d (P.isub ρ)).isub (ISub.id k))
    ((Tm.hfill (.data d (P.isub ρ)) φ u a).isub (ISub.cons .one trivial (ISub.id k)))
    ((Tm.hcomp (.data d (P.isub ρ)) φ u a).isub (ISub.id k)) at endF
  rw [isub_cons_id_of_closed hcF .one trivial, isub_id_of_closed (closed_of_ty hW hcan),
    isub_id_of_closed (closed_of_ty hW hPρ)] at endF
  have rcan := hcomp_relD hW hD hH hP hPP ρ hcan ht
    ((hcomp_data_retype hW ht hPρ).2.symm) (ent_refl _) (ent_refl _) uL uL uL aL hb hb
  have hcanP' := (hcomp_data_retype hW ht' hPρ).1
  have htu := minimal_to_spec (gen_hcomp (spec_to_minimal hW hcan) rfl).choose_spec.1.2.2.1
  have htu' := minimal_to_spec (gen_hcomp (spec_to_minimal hW hcanP') rfl).choose_spec.1.2.2.1
  have htuR := HasTy.restrict (KubusCore.I.scoped_shift (show (cof .one φ).Scoped k from ⟨trivial, hs⟩))
    (ent_shift (ent_and_mono (ent_refl _) h12)) htu'
  have heTube := TubeD.eq hW hs hPρ htu htuR hu
  have hePair := EqTm.hcomp hcan hcanP' (EqTm.refl hPρ) h12 h21 heTube (RE2.typed ha).2.2
  have heSrc := (hcomp_data_retype hW ht hPρ).2.trans
    (hePair.trans (hcomp_data_retype hW ht' hPρ).2.symm)
  have rsrc := hcomp_relD hW hD hH hP hPP ρ ht ht' heSrc h12 h21 hu uL uR ha hb hb'
  have Tend : RT2 S k ((motiveLine (M.isub ρ) (Tm.hfill (.data d (P.isub ρ)) φ u a)).dinst .one)
      ((M.isub ρ).inst (.hcomp (.data d qs) φ u a)) := by
    simpa only [motiveLine_eq, dshift_inst_dinst] using HL.mot k ρ _ _ (RE2.trans hW hA endF rcan)
  have te := (Comp2_ty_base Tend).2.2.2.2.2
  obtain ⟨mL, hEL⟩ := HL.tyL k ρ
  have ecL := EqTm.elimHcomp hD hH hcan
    (minimal_to_spec (hEL.elim_ty (spec_to_minimal hW ht)))
  have ecR := EqTm.elimHcomp hD hH hcanR
    (minimal_to_spec (hER.elim_ty (spec_to_minimal hW (ht'.tyConv hPQ))))
  have htC := (HasTy.eqR ecL).tyConv te.symm
  have htC' := (HasTy.eqR ecR).tyConv ((Comp2_ty_base (H.mot k ρ _ _ rsrc)).2.2.2.2.2.symm.trans hW te.symm)
  refine RE2.conv hW Tend (elimComp_relH hW HL H ρ hF RF' RFL'
    (by intro k' σ r hr hh; simpa only [data_isub_comp] using faceF k' σ r hr hh)
    (by intro k' σ; simpa only [data_isub_comp] using zeroF k' σ) hb ?_
    iha ?_ htC htC' h12 h21)
  · intro k' σ r r' hr hr' he hh
    have R := ihu k' σ r hr hh
    simp only [elimLine_pt, Tm.isub_isub]
    have ur := u2 k' σ r r' hr hr' he hh
    have ur' : RE2 S k' (.data d (P.isub (ρ.comp σ))) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r') := by
      change RE2 S k' (.data d ((P.isub ρ).isub σ)) _ _ at ur
      rwa [Tm.isub_isub] at ur
    obtain ⟨m, hE⟩ := H.tyR k' (ρ.comp σ)
    have htr := minimal_to_spec (hE.elim_ty (spec_to_minimal hW ((RE2.typed ur').2.1.tyConv
      (Comp2_ty_base (H.dat k' (ρ.comp σ))).2.2.2.2.2)))
    have T := H.mot k' (ρ.comp σ) _ _ ur'
    exact RE2_near hW (HL.mot k' (ρ.comp σ) _ _ (by
      have R := uL k' σ r hr hh
      change RE2 S k' (.data d ((P.isub ρ).isub σ)) _ _ at R
      rwa [Tm.isub_isub] at R)) R
      (.elim (.refl _) (.refl _) (.refl _) ((TmNear.refl _).dinst he))
      (htr.tyConv (Comp2_ty_base T).2.2.2.2.2.symm)
  · intro k' σ hh
    have R := ihb k' σ hh
    rw [elimLine_pt]
    simp only [isub_elim, Tm.isub_isub]
    exact R

end

end Model.Whnf
