import Model.Whnf.Valid2ElimH27

/-! # Constructor stages of the eliminator induction with normalization evidence -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k K : ℕ}

def ElimMotiveH (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k : ℕ) (g : Hom k K) (A x x' : Tm) : Prop :=
  EM1H S d D K P M bs k g A x x' ∧ EN1H S d D K P M bs k g A x

def ElimStageH (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm)
    (k : ℕ) (g : Hom k K) (A x x' : Tm) : Prop :=
  EMStageH S d D K P M bs k g A x x' ∧ EN2H S d D K P M bs k g A x

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
    {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hP hPP

/-- The argument relation of the specified constructor heads at a raw relation stage. -/
theorem ctorArgs_stageH (ρ : ISub k K) {t t' q q' : Tm} {c : ℕ} {C : Ctor} {X X' : List Tm} {rs rs' : List I}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k ρ.hom (.data d (P.isub ρ)) t t')
    (hC : D.ctors[c]? = some C)
    (ht : RedE S k (.data d (P.isub ρ)) t (.con d c q (Tm.ofList X) rs))
    (ht' : RedE S k (.data d (P.isub ρ)) t' (.con d c q' (Tm.ofList X') rs')) :
    ∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X'.getD i .abort) := by
  rcases DR2At_cases hW hD hP hPP ρ hat with
    ⟨c3, C3, q3, Z, rs3, q3', Z', rs3', hC3, hZl, hZ'l, hr3, hr3', -, -, -, -, -, hZ⟩ |
    ⟨_, _, _, _, _, _, _, _, -, hr3, -⟩
  · have f1 := RedW.unique hr3.1 ht.1
    have f2 := RedW.unique hr3'.1 ht'.1
    simp only [Tm.con.injEq] at f1 f2
    obtain ⟨-, rfl, -, eZ, -⟩ := f1
    obtain ⟨-, -, -, eZ', -⟩ := f2
    have eZ1 := congrArg Tm.toList eZ
    have eZ1' := congrArg Tm.toList eZ'
    simp only [toList_ofList] at eZ1 eZ1'
    subst Z Z'
    rw [hC] at hC3
    cases hC3
    exact hZ
  · cases RedW.unique hr3.1 ht.1

variable (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1)) {M bs : Tm}
    (HL : ElimRelH S d D K P M bs P M bs) (HB : ElimBndRel2 S d D K P M bs)
include hH hyp HL HB

/-- The constructor stage gives paired contracta and normalization of the left head. -/
theorem elimStage_conH {g : Hom k K} {A t t' ps q q' : Tm} {c : ℕ} {C : Ctor}
    {X X' : List Tm} {rs rs' : List I}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k g A t t')
    (hC : (dataD S d).ctors[c]? = some C) (hA : RedT S k A (.data d ps))
    (ht : RedE S k A t (.con d c q (Tm.ofList X) rs))
    (ht' : RedE S k A t' (.con d c q' (Tm.ofList X') rs'))
    (hl : X.length = C.args.length) (hl' : X'.length = C.args.length)
    (ihrec : ∀ j (hj : j < X.length) (hj' : j < X'.length), C.isRec j = true →
      ElimMotiveH S d D K P M bs k g (.data d ps) X[j] X'[j]) :
    ElimStageH S d D K P M bs k g A t t' := by
  have hc : D.ctors[c]? = some C := dataD_eq hW hD ▸ hC
  refine ⟨?_, ?_⟩
  · intro ρ hg hAe Q M' bs' H W W' hw hw'
    subst hg hAe
    obtain rfl := RedW.unique hw.1 ht.1
    obtain rfl := RedW.unique hw'.1 ht'.1
    have R := em2_conH hW hD hP hPP hat hC hA ht ht' hl hl'
      (fun j hj hj' hr => (ihrec j hj hj' hr).1) ρ rfl rfl Q M' bs' H c C q X rs q' X' rs' hc ht ht'
    have ha := ctorArgs_stageH hW hD hP hPP ρ hat hc ht ht'
    have haL := fun i hi => (args_self hW hD hP hPP ρ hc hl hl' ha i hi).2.1
    have htP := (con_inv hW hD hc (HasTy.eqR ht.2) (HasTy.isubS hW hP ρ)).2.2.2.2.2.2.1
    have cr := con_rel hW hD hP hPP hH hyp c ρ hc htP (HasTy.eqR ht.2) (forall2_ieq_refl _) haL
    rw [elimRedH_con hc, elimRedH_con hc]
    exact RE2.conv hW (HL.mot k ρ _ _ cr) R
  · intro ρ hg hAe W hw
    subst hg hAe
    obtain rfl : ps = P.isub ρ := redT_data_eq (Θ := ΘK S D d K P) hA
    obtain rfl := RedW.unique hw.1 ht.1
    have ha := ctorArgs_stageH hW hD hP hPP ρ hat hc ht ht'
    apply elimNorm_conH hW hD hH hyp hP hPP HL HB c ρ hc (HasTy.eqR ht.2)
      (fun i hi => (args_self hW hD hP hPP ρ hc hl hl' ha i hi).2.1)
    intro j hj
    obtain ⟨hjn, hr⟩ := mem_recPos hj
    have hj : j < X.length := by omega
    have hj' : j < X'.length := by omega
    rw [getD_eq_get' hj]
    exact (ihrec j hj hj' hr).2 ρ rfl rfl

end

end Model.Whnf
