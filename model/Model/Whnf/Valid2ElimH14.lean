import Model.Whnf.Valid2ElimH13

/-!
# Constructor computation for higher inductive eliminators

At a constructor boundary the branch equation identifies the contractum with the boundary
interpreter. Computation at earlier constructors identifies that interpreter with elimination.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k : ℕ} (hW : WfSig S) {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {K : ℕ} {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (H : ElimRelH S d D K P M bs P M bs)
    (HB : ElimBndRel2 S d D K P M bs)
include hW hD hH hyp hP hPP H HB

/-- A constructor elimination has a reduct related to its branch contractum, including at a boundary. -/
theorem elimCon_stageH {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    (ihEC : ∀ c' < c, ECSt2 S d D K P M bs c')
    (ρ : ISub k K) {q : Tm} {X : List Tm} {rs : List I}
    (ht : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ)))
    (ha : ∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X.getD i .abort))
    (hi : ∀ i, i ∈ C.recPos → RE2 S k ((M.isub ρ).inst (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))) :
    ∃ u, Red S (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (.con d c q (Tm.ofList X) rs)) u ∧
      EqTm S k .one [] (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (.con d c q (Tm.ofList X) rs)) u
        ((M.isub ρ).inst (.con d c q (Tm.ofList X) rs)) ∧
      RE2 S k ((M.isub ρ).inst (.con d c q (Tm.ofList X) rs)) u
        (Tm.papps (ecTm d C c (P.isub ρ) (M.isub ρ) (bs.isub ρ) X) rs) := by
  have hPρ := HasTy.isubS hW hP ρ
  have hPPρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
  have CI := con_inv hW hD hC ht hPρ
  have hrs := CI.2.2.2.1
  have hsc := CI.2.2.2.2.1
  have hX := CI.2.2.2.2.2.1
  have htP := CI.2.2.2.2.2.2.1
  have hqlist := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have hplen : (P.isub ρ).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k (.data d (P.isub ρ)))
    rwa [dataD_eq hW hD] at this
  have cr : RE2 S k (.data d (P.isub ρ)) (.con d c (P.isub ρ) (Tm.ofList X) rs)
      (.con d c q (Tm.ofList X) rs) :=
    con_rel hW hD hP hPP hH hyp c ρ hC htP ht (forall2_ieq_refl _) ha
  have crSelf := con_rel hW hD hP hPP hH hyp c ρ hC ht ht (forall2_ieq_refl _) ha
  have rbr := elimCon_relH hW hD hC hplen (H.br k ρ c C hC) hX hX
    (fun i hi hi' => by simpa only [getD_eq_get' hi] using ha i (by omega)) hi
    hrs (ieqL_iff.2 (forall2_ieq_refl _)) hsc hsc
  have rbr' := RE2.conv hW (H.mot k ρ _ _ cr) rbr
  obtain ⟨m, hE⟩ := H.tyL k ρ
  cases hf : firstBnd C.bnd rs with
  | none =>
    obtain ⟨r, e⟩ := elim_reductH hW hD hE ht hC
      ⟨redW_self (step_con_none hD hC _ _ hf), EqTm.refl ht⟩ hf
    exact ⟨_, r, e, rbr'⟩
  | some e =>
    obtain ⟨kb, ψ, hb, hh⟩ := firstBnd_spec hf
    obtain ⟨-, hcl, hs, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ e hb
    have eb : EqTm S k .one [] (.con d c q (Tm.ofList X) rs) (Ctor.bndAt e q.toList X rs)
        (.data d (P.isub ρ)) := by
      have := EqTm.conBnd hD hC hb hh hqlist (by rw [toList_ofList]) ht
      rwa [toList_ofList] at this
    have hPl := (dataLit_rel hW hD hP hPP ρ).2.2.2.2.2.1
    have ebP : EqTm S k .one [] (.con d c (P.isub ρ) (Tm.ofList X) rs)
        (Ctor.bndAt e (P.isub ρ).toList X rs) (.data d (P.isub ρ)) := by
      have := EqTm.conBnd hD hC hb hh hPl (by rw [toList_ofList]) htP
      rwa [toList_ofList] at this
    have hrel := hyp.bndTy (by omega) hD hH hC hb hh hPρ hPPρ hX htP ha
    have ihCR : ∀ c' < c, CRSt S d D K P c' := by
      intro c' hc k' ρ C q q' X X' rs rs' hC ht ht' hrs ha
      exact con_rel hW hD hP hPP hH hyp c' ρ hC ht ht' hrs ha
    have ri := bndInterp_rel2 hW hD hP hPP H hC ihCR ihEC ρ q hql X rs hX ha hi
      (sizeOf e + 1) e (by omega) hs hcl hrel (HasTy.eqR eb) (HasTy.eqR ebP)
    have rb := HB ρ hC hb X rs hX hrs hsc hh ha hi
    have rcB := hyp.conBnd (by omega) hD hH hC hb hh hPρ hPPρ hX htP ha
    have rB := bnd_rel hW hD hP hPP ihCR hC (sizeOf e + 1) e (by omega) hs ρ
      hql hplen hX hX (forall2_ieq_refl _) ha hrel (HasTy.eqR eb) (HasTy.eqR ebP)
    have rcqB := RE2.trans hW hPPρ (RE2.symm hW hPPρ cr)
      (RE2.trans hW hPPρ rcB (RE2.symm hW hPPρ rB))
    have ri' := RE2.conv hW (H.mot k ρ _ _ (RE2.symm hW hPPρ rcqB)) ri
    have rb' := RE2.conv hW (H.mot k ρ _ _ cr) rb
    have r := RE2.trans hW (H.mot k ρ _ _ crSelf) ri' (RE2.symm hW (H.mot k ρ _ _ crSelf) rb')
    have ee := hE.elim_congr (sigClosed_of_wfSig hW) (spec_to_minimal hW ht)
      (spec_to_minimal hW (HasTy.eqR eb)) (spec_to_minimal_eq hW eb)
    have sr : Red S (.con d c q (Tm.ofList X) rs) (Ctor.bndAt e q.toList X rs) := by
      apply Red.step _ (.refl _)
      rw [step_con_some hD hC _ _ hf, toList_ofList]
    exact ⟨_, red_elim_scrut sr, minimal_to_spec_eq ee, r⟩

omit hW hD hH hyp hP hPP H HB in
theorem papps_isub2 {k' : ℕ} (f : Tm) (rs : List I) (κ : ISub k' k) :
    (Tm.papps f rs).isub κ = Tm.papps (f.isub κ) (rs.map (·.subst κ.τ)) :=
  papps_subst f rs Tm.var κ.τ

/-- Constructor computation for every higher inductive constructor, at every restriction. -/
theorem elimCon_compH : ∀ c, ECSt2 S d D K P M bs c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro k ρ C q X rs hC ht ha hi
    have hPρ := HasTy.isubS hW hP ρ
    have CI := con_inv hW hD hC ht hPρ
    have hX := CI.2.2.2.2.2.1
    have cr := con_rel hW hD hP hPP hH hyp c ρ hC ht ht (forall2_ieq_refl _) ha
    obtain ⟨m, hE⟩ := H.tyL k ρ
    have hty := minimal_to_spec (hE.elim_ty (spec_to_minimal hW ht))
    obtain ⟨_, _, _, rb⟩ := elimCon_stageH hW hD hH hyp hP hPP H HB hC ih ρ ht ha hi
    refine RE2.expandH hW (H.mot k ρ _ _ cr) hty (RE2.typed rb).2.1 ?_
    intro k' κ
    have htκ := HasTy.isubS hW ht κ
    rw [isub_conT, data_isub_comp] at htκ
    have haκ := args_restr hW hD hP hPP ρ hC hX hX ha κ
    have hiκ : ∀ i, i ∈ C.recPos → RE2 S k' ((M.isub (ρ.comp κ)).inst ((X.map (·.isub κ)).getD i .abort))
        (.elim d (P.isub (ρ.comp κ)) (M.isub (ρ.comp κ)) (bs.isub (ρ.comp κ)) ((X.map (·.isub κ)).getD i .abort))
        (.elim d (P.isub (ρ.comp κ)) (M.isub (ρ.comp κ)) (bs.isub (ρ.comp κ)) ((X.map (·.isub κ)).getD i .abort)) := by
      intro i hi'
      have R := RE2.isub hW (hi i hi') κ
      simpa only [getD_map_isub, isub_inst, isub_elim, Tm.isub_isub] using R
    obtain ⟨u, r, e, R⟩ := elimCon_stageH hW hD hH hyp hP hPP H HB hC ih (ρ.comp κ) htκ haκ hiκ
    refine ⟨u, ?_, ?_, ?_⟩
    · simpa only [isub_elim, isub_conT, Tm.isub_isub] using r
    · simpa only [isub_inst, isub_elim, isub_conT, Tm.isub_isub] using e
    · rw [isub_inst, Tm.isub_isub, isub_conT, papps_isub2,
        ecTm_isub d C c hE.hbs, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact R

end

end Model.Whnf
