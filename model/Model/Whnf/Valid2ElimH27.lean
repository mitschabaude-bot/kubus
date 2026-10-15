import Model.Whnf.Valid2ElimH26

/-! # Normalization of constructor eliminations, including boundaries -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {K : ℕ} (hW : WfSig S) {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (H : ElimRelH S d D K P M bs P M bs)
    (HB : ElimBndRel2 S d D K P M bs)
include hW hD hH hyp hP hPP H HB

/-- Constructor elimination normalizes when its recursive arguments' eliminations do. -/
theorem elimNorm_conH : ∀ c, ECNorm2 S d D K P M bs c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro k ρ C q X rs hC ht ha Nh
    have hPρ := HasTy.isubS hW hP ρ
    have CI := con_inv hW hD hC ht hPρ
    have hX := CI.2.2.2.2.2.1
    have hPl := (dataLit_rel hW hD hP hPP ρ).2.2.2.2.2.1
    have hplen : (P.isub ρ).toList.length = D.params.length := by
      have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k (.data d (P.isub ρ)))
      rwa [dataD_eq hW hD] at this
    have hrec : ∀ j, j ∈ C.recPos → RE2 S k (.data d (P.isub ρ)) (X.getD j .abort) (X.getD j .abort) := by
      intro j hj
      obtain ⟨hjn, hr⟩ := mem_recPos hj
      have R := ha j hjn
      rw [argTy_rec_inst hr hPl hplen (by simp [hX]; omega)] at R
      exact R
    have hi : ∀ j, j ∈ C.recPos → RE2 S k ((M.isub ρ).inst (X.getD j .abort))
        (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD j .abort))
        (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD j .abort)) :=
      fun j hj => ElimNormH.computable hW hD hH hyp hP hPP H ρ (hrec j hj) (Nh j hj)
    intro k' σ W hw
    rw [isub_conT] at hw ⊢
    let ρ' := ρ.comp σ
    let q' := q.isub σ
    let X' := X.map (·.isub σ)
    let rs' := rs.map (·.subst σ.τ)
    have htσ := HasTy.isubS hW ht σ
    rw [isub_conT, data_isub_comp] at htσ
    have haσ := args_restr hW hD hP hPP ρ hC hX hX ha σ
    have hiσ : ∀ j, j ∈ C.recPos → RE2 S k' ((M.isub ρ').inst (X'.getD j .abort))
        (.elim d (P.isub ρ') (M.isub ρ') (bs.isub ρ') (X'.getD j .abort))
        (.elim d (P.isub ρ') (M.isub ρ') (bs.isub ρ') (X'.getD j .abort)) := by
      intro j hj
      have R := RE2.isub hW (hi j hj) σ
      simpa only [isub_inst, isub_elim, Tm.isub_isub, getD_map_isub, X', ρ'] using R
    have Nσ : ∀ j, j ∈ C.recPos → ElimNormH S d D K P M bs k' ρ' (X'.getD j .abort) := by
      intro j hj
      rw [show X'.getD j .abort = (X.getD j .abort).isub σ from getD_map_isub X j σ]
      exact (Nh j hj).isub σ
    change RE2 S k' ((M.isub ρ').inst (.con d c q' (Tm.ofList X') rs'))
      (.elim d (P.isub ρ') (M.isub ρ') (bs.isub ρ') (.con d c q' (Tm.ofList X') rs'))
      (elimRedH d D (P.isub ρ') (M.isub ρ') (bs.isub ρ') W)
    cases hf : firstBnd C.bnd rs' with
    | none =>
      have wh : RedW S (.con d c q' (Tm.ofList X') rs') (.con d c q' (Tm.ofList X') rs') :=
        redW_self (step_con_none hD hC _ _ hf)
      obtain rfl := RedW.unique hw.1 wh
      rw [elimRedH_con hC]
      exact elimCon_compH hW hD hH hyp hP hPP H HB c ρ' hC htσ haσ hiσ
    | some e =>
      obtain ⟨kb, ψ, hb, hh⟩ := firstBnd_spec hf
      have hPρ' := HasTy.isubS hW hP ρ'
      have hPPρ' := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
      have CI' := con_inv hW hD hC htσ hPρ'
      have hX' : X'.length = C.args.length := CI'.2.2.2.2.2.1
      have htP := CI'.2.2.2.2.2.2.1
      have hqlist : IsList q' := CI'.2.2.2.2.2.2.2.2.1
      have hql : q'.toList.length = D.params.length := CI'.2.2.2.2.2.2.2.2.2
      have hPl' := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
      have eb : EqTm S k' .one [] (.con d c q' (Tm.ofList X') rs') (Ctor.bndAt e q'.toList X' rs')
          (.data d (P.isub ρ')) := by
        have := EqTm.conBnd hD hC hb hh hqlist (by rw [toList_ofList]) htσ
        rwa [toList_ofList] at this
      have ebP : EqTm S k' .one [] (.con d c (P.isub ρ') (Tm.ofList X') rs')
          (Ctor.bndAt e (P.isub ρ').toList X' rs') (.data d (P.isub ρ')) := by
        have := EqTm.conBnd hD hC hb hh hPl' (by rw [toList_ofList]) htP
        rwa [toList_ofList] at this
      have hrel := hyp.bndTy (by omega) hD hH hC hb hh hPρ' hPPρ' hX' htP haσ
      have ihCR : ∀ c' < c, CRSt S d D K P c' := by
        intro c' hc k'' τ C q q' X X' rs rs' hC ht ht' hrs ha
        exact con_rel hW hD hP hPP hH hyp c' τ hC ht ht' hrs ha
      obtain ⟨-, hcl, hs, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ e hb
      have BN := bndNormH hW hD hP hPP hC ihCR ih ρ' q' hql X' rs' hX' haσ Nσ
        (sizeOf e + 1) e (by omega) hs hcl hrel (HasTy.eqR eb) (HasTy.eqR ebP)
      have rr : Red S (.con d c q' (Tm.ofList X') rs') (Ctor.bndAt e q'.toList X' rs') := by
        apply Red.step _ (.refl _)
        rw [step_con_some hD hC _ _ hf, toList_ofList]
      have wb : RedE S k' (.data d (P.isub ρ')) (Ctor.bndAt e q'.toList X' rs') W :=
        ⟨red_redW rr hw.1, eb.symm.trans hw.2⟩
      have hbc := closed_of_ty hW (HasTy.eqR eb)
      have NB := BN k' (ISub.id k') W (by rw [ISub.comp_id, isub_id_of_closed hbc]; exact wb)
      rw [ISub.comp_id, isub_id_of_closed hbc] at NB
      have RB := elimCon_bndH hW hD hH hyp hP hPP H HB hC hb ρ' hh htσ haσ hiσ
      have T := H.mot k' ρ' _ _ RB.1
      have hXcode := RE2.tyCode hW RB.2
      exact RE2.trans hW (RT2.refl hW hXcode T) RB.2 (RE2.conv hW (RT2.symm hW hXcode T) NB)

end

end Model.Whnf
