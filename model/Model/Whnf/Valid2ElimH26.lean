import Model.Whnf.Valid2ElimH25

/-! # Constructor boundaries in the normalization induction -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k K : ℕ} (hW : WfSig S) {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (H : ElimRelH S d D K P M bs P M bs)
    (HB : ElimBndRel2 S d D K P M bs)
include hW hD hH hyp hP hPP H HB

/-- Elimination respects a constructor boundary from branch boundary agreement and computation. -/
theorem elimCon_bndH {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {kb : ℕ} {ψ : I} {e : Tm} (hb : C.bnd[kb]? = some (ψ, e))
    (ρ : ISub k K) {q : Tm} {X : List Tm} {rs : List I} (hh : I.Entails .one (Ctor.cofAt ψ rs))
    (ht : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ)))
    (ha : ∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X.getD i .abort))
    (hi : ∀ i, i ∈ C.recPos → RE2 S k ((M.isub ρ).inst (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))) :
    RE2 S k (.data d (P.isub ρ)) (.con d c q (Tm.ofList X) rs) (Ctor.bndAt e q.toList X rs) ∧
    RE2 S k ((M.isub ρ).inst (.con d c q (Tm.ofList X) rs))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (.con d c q (Tm.ofList X) rs))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (Ctor.bndAt e q.toList X rs)) := by
  have hPρ := HasTy.isubS hW hP ρ
  have hPPρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
  have CI := con_inv hW hD hC ht hPρ
  have hrs := CI.2.2.2.1
  have hsc := CI.2.2.2.2.1
  have hX := CI.2.2.2.2.2.1
  have htP := CI.2.2.2.2.2.2.1
  have hqlist := CI.2.2.2.2.2.2.2.2.1
  have hql := CI.2.2.2.2.2.2.2.2.2
  have hPl := (dataLit_rel hW hD hP hPP ρ).2.2.2.2.2.1
  have hplen : (P.isub ρ).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k (.data d (P.isub ρ)))
    rwa [dataD_eq hW hD] at this
  have cr := con_rel hW hD hP hPP hH hyp c ρ hC htP ht (forall2_ieq_refl _) ha
  have crSelf := con_rel hW hD hP hPP hH hyp c ρ hC ht ht (forall2_ieq_refl _) ha
  have eb : EqTm S k .one [] (.con d c q (Tm.ofList X) rs) (Ctor.bndAt e q.toList X rs)
      (.data d (P.isub ρ)) := by
    have := EqTm.conBnd hD hC hb hh hqlist (by rw [toList_ofList]) ht
    rwa [toList_ofList] at this
  have ebP : EqTm S k .one [] (.con d c (P.isub ρ) (Tm.ofList X) rs)
      (Ctor.bndAt e (P.isub ρ).toList X rs) (.data d (P.isub ρ)) := by
    have := EqTm.conBnd hD hC hb hh hPl (by rw [toList_ofList]) htP
    rwa [toList_ofList] at this
  have hrel := hyp.bndTy (by omega) hD hH hC hb hh hPρ hPPρ hX htP ha
  have ihCR : ∀ c' < c, CRSt S d D K P c' := by
    intro c' hc k' ρ C q q' X X' rs rs' hC ht ht' hrs ha
    exact con_rel hW hD hP hPP hH hyp c' ρ hC ht ht' hrs ha
  have ihEC : ∀ c' < c, ECSt2 S d D K P M bs c' :=
    fun c' _hc => elimCon_compH hW hD hH hyp hP hPP H HB c'
  obtain ⟨-, hcl, hs, -⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ e hb
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
  have EC := elimCon_compH hW hD hH hyp hP hPP H HB c ρ hC ht ha hi
  exact ⟨rcqB, RE2.trans hW (H.mot k ρ _ _ crSelf) (RE2.trans hW (H.mot k ρ _ _ crSelf) EC rb')
    (RE2.symm hW (H.mot k ρ _ _ crSelf) ri')⟩

end

end Model.Whnf
