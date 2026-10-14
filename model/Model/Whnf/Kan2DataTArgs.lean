import Model.Whnf.Kan2DataTStep

/-!
# Constructors with related arguments

Two constructor terms of a restriction of a literal inductive type without path constructors are related
when their arguments are related at the argument types instantiated by the left arguments
(`RE2_con_args`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hP hPP

omit hW hD hH hP hPP in
theorem getD_eq_get' {Y : List Tm} {i : ℕ} (hi : i < Y.length) : Y.getD i .abort = Y[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

omit hW hD hH hP hPP in
theorem getD_map_isub' {Y : List Tm} {i : ℕ} (hi : i < Y.length) (κ : ISub k' k) :
    (Y.map (·.isub κ)).getD i .abort = (Y.getD i .abort).isub κ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]; rfl

/-- The argument types at the left arguments of two constructors with related arguments are related to
those at the right arguments. -/
theorem argTy_rt2_args {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {Y Y' : List Tm}
    (hYl : Y.length = C.args.length) (hY'l : Y'.length = C.args.length)
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ (P.isub ρ').toList.reverse)) (Y.getD i .abort) (Y'.getD i .abort))
    {j : ℕ} (hj : j < C.args.length) :
    RT2 S k3 ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ (P.isub ρ').toList.reverse))
      ((C.argTy d D.params.length j).substList ((Y'.take j).reverse ++ (P.isub ρ').toList.reverse)) := by
  have hdD := dataD_eq hW hD
  have hTP : IsTyK S k3 (.data d (P.isub ρ')) := ⟨_, .inl (HasTy.isubS hW hP ρ')⟩
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW hTP; rwa [hdD] at this
  refine argTy_rt2 hW hD hP hPP hPP hPP ρ' hC hj (by simp; omega) (by simp; omega) fun i hi => ⟨fun hri => ?_, fun hri => ?_⟩
  · have := hargs i (by omega)
    rw [argTy_rec_inst hri hPl hplen (by simp; omega)] at this
    rwa [getD_take_lt hi, getD_take_lt hi]
  · have := hargs i (by omega)
    rwa [getD_take_lt hi, getD_take_lt hi, List.take_take, Nat.min_eq_left hi.le]

/-- Constructors with related arguments, at one stage. -/
theorem DR2At_con_args {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q q' : Tm}
    {Y Y' : List Tm} (hYl : Y.length = C.args.length) (hY'l : Y'.length = C.args.length)
    (hcT : HasTy S k3 .one [] (.con d c q (Tm.ofList Y) []) (.data d (P.isub ρ')))
    (he : EqTm S k3 .one [] (.con d c q (Tm.ofList Y) []) (.con d c q' (Tm.ofList Y') []) (.data d (P.isub ρ')))
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ (P.isub ρ').toList.reverse)) (Y.getD i .abort) (Y'.getD i .abort)) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
      (.data d (P.isub ρ')) (.con d c q (Tm.ofList Y) []) (.con d c q' (Tm.ofList Y') []) := by
  have hdD := dataD_eq hW hD
  have hTP : IsTyK S k3 (.data d (P.isub ρ')) := ⟨_, .inl (HasTy.isubS hW hP ρ')⟩
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW hTP; rwa [hdD] at this
  refine DR2At_con_of hW hD hH hP hPP ρ' hC hYl hY'l hcT
    ⟨redW_self (step_con_nonHIT hD hH hC _ _ _), EqTm.refl (HasTy.eqR he)⟩ he fun i hi hi' => ⟨fun hri => ?_, fun hri _ => ?_⟩
  · have := hargs i (by omega)
    rw [argTy_rec_inst hri hPl hplen (by simp; omega), getD_eq_get' hi,
      getD_eq_get' hi'] at this
    exact this
  · have := hargs i (by omega)
    rwa [getD_eq_get' hi, getD_eq_get' hi'] at this

/-- Constructors with related arguments are related. -/
theorem RE2_con_args {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q q' : Tm}
    {Y Y' : List Tm} (hYl : Y.length = C.args.length) (hY'l : Y'.length = C.args.length)
    (hcT : HasTy S k3 .one [] (.con d c q (Tm.ofList Y) []) (.data d (P.isub ρ')))
    (he : EqTm S k3 .one [] (.con d c q (Tm.ofList Y) []) (.con d c q' (Tm.ofList Y') []) (.data d (P.isub ρ')))
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ (P.isub ρ').toList.reverse)) (Y.getD i .abort) (Y'.getD i .abort)) :
    RE2 S k3 (.data d (P.isub ρ')) (.con d c q (Tm.ofList Y) []) (.con d c q' (Tm.ofList Y') []) := by
  have hS := sigClosed_of_wfSig hW
  have eP : ∀ {k4 : ℕ} (κ : ISub k4 k3), (Tm.data d (P.isub ρ')).isub κ = .data d (P.isub (ρ'.comp κ)) := by
    intro k4 κ; show Tm.data d ((P.isub ρ').isub κ) = _; rw [Tm.isub_isub]
  have eC : ∀ {k4 : ℕ} (κ : ISub k4 k3) (q0 : Tm) (Z : List Tm),
      (Tm.con d c q0 (Tm.ofList Z) []).isub κ = .con d c (q0.isub κ) (Tm.ofList (Z.map (·.isub κ))) [] := by
    intro k4 κ q0 Z; show Tm.con d c (q0.isub κ) ((Tm.ofList Z).isub κ) [] = _; rw [ofList_isub]
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  -- the argument types and the self-relations of the arguments
  have hT := fun j (hj : j < C.args.length) => argTy_rt2_args hW hD hH hP hPP ρ' hC hYl hY'l hargs hj
  have hYY : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ (P.isub ρ').toList.reverse)) (Y.getD i .abort) (Y.getD i .abort) := fun i hi =>
    RE2.trans hW (hT i hi) (hargs i hi) (RE2.symm hW (hT i hi) (hargs i hi))
  have hY'Y' : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Y'.take i).reverse ++ (P.isub ρ').toList.reverse)) (Y'.getD i .abort) (Y'.getD i .abort) := fun i hi =>
    RE2.conv hW (hT i hi) (RE2.trans hW (hT i hi) (RE2.symm hW (hT i hi) (hargs i hi)) (hargs i hi))
  -- restrictions of the relations of the arguments
  have rst : ∀ {Z Z' : List Tm}, Z.length = C.args.length → Z'.length = C.args.length →
      (∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((Z.take i).reverse ++ (P.isub ρ').toList.reverse)) (Z.getD i .abort) (Z'.getD i .abort)) →
      ∀ {k4 : ℕ} (κ : ISub k4 k3) (i : ℕ) (hi : i < C.args.length), RE2 S k4 ((C.argTy d D.params.length i).substList
        (((Z.map (·.isub κ)).take i).reverse ++ (P.isub (ρ'.comp κ)).toList.reverse))
        ((Z.map (·.isub κ)).getD i .abort) ((Z'.map (·.isub κ)).getD i .abort) := by
    intro Z Z' hZl hZ'l h k4 κ i hi
    have := RE2.isub hW (h i hi) κ
    rw [argTy_isub hS hD hC i Z hPl κ, Tm.isub_isub] at this
    rwa [getD_map_isub' (by omega) κ, getD_map_isub' (by omega) κ]
  have hstage : ∀ {Z Z' : List Tm} {qz qz' : Tm}, Z.length = C.args.length → Z'.length = C.args.length →
      HasTy S k3 .one [] (.con d c qz (Tm.ofList Z) []) (.data d (P.isub ρ')) →
      EqTm S k3 .one [] (.con d c qz (Tm.ofList Z) []) (.con d c qz' (Tm.ofList Z') []) (.data d (P.isub ρ')) →
      (∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((Z.take i).reverse ++ (P.isub ρ').toList.reverse)) (Z.getD i .abort) (Z'.getD i .abort)) →
      ∀ {k4 : ℕ} (κ : ISub k4 k3), DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
        (dataP2 S (ΘK S D d K P) (Hom.id K)) k4 (ρ'.hom.comp κ.hom) ((Tm.data d (P.isub ρ')).isub κ)
        ((Tm.con d c qz (Tm.ofList Z) []).isub κ) ((Tm.con d c qz' (Tm.ofList Z') []).isub κ) := by
    intro Z Z' qz qz' hZl hZ'l hz hez h k4 κ
    have hzκ := HasTy.isubS hW hz κ
    have heκ := EqTm.isubS hW hez κ
    rw [eP, eC] at hzκ heκ
    rw [eC] at heκ
    rw [eP, eC, eC, ← ISub.hom_comp]
    exact DR2At_con_args hW hD hH hP hPP (ρ'.comp κ) hC (by simp [hZl]) (by simp [hZ'l]) hzκ heκ
      (rst hZl hZ'l h κ)
  have hcT' := HasTy.eqR he
  refine (RE2_dataLit_iff hW hD hP ρ').2 ⟨⟨hcT, hcT', he⟩, .intro he (fun k4 κ => hstage hYl hY'l hcT he hargs κ)
    (fun k4 σ w hw k5 κ => ?_) (fun k4 σ w hw k5 κ => ?_)⟩
  · obtain rfl := RedW.unique hw (by rw [eC]; exact redW_self (step_con_nonHIT hD hH hC _ _ _))
    rw [← eC, Tm.isub_isub]
    exact hstage hYl hYl hcT (EqTm.refl hcT) hYY (σ.comp κ)
  · obtain rfl := RedW.unique hw (by rw [eC]; exact redW_self (step_con_nonHIT hD hH hC _ _ _))
    rw [← eC, Tm.isub_isub]
    exact hstage hY'l hY'l hcT' (EqTm.refl hcT') hY'Y' (σ.comp κ)

end lit

section wrap
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

theorem data_closed {k3 : ℕ} {P1 : Tm} {l : ℕ} (hP1 : HasTy S k3 .one [] (.data d P1) (.univ l)) :
    P1.closedB 0 k3 = true := by
  have := closed_of_ty hW hP1; simpa [Tm.closedB] using this

/-- The argument types at related prefixes of arguments and related parameters are related. -/
theorem argTy_rt2' {k3 : ℕ} {P1 Q2 : Tm} (hP1 : HasTy S k3 .one [] (.data d P1) (.univ D.level))
    (hP1P1 : RT2 S k3 (.data d P1) (.data d P1)) (hQ2 : RT2 S k3 (.data d P1) (.data d Q2))
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {j : ℕ} (hj : j < C.args.length) {A B : List Tm}
    (hAl : A.length = j) (hBl : B.length = j)
    (hrel : ∀ i (hi : i < j), RE2 S k3 ((C.argTy d D.params.length i).substList ((A.take i).reverse ++
      P1.toList.reverse)) (A.getD i .abort) (B.getD i .abort)) :
    RT2 S k3 ((C.argTy d D.params.length j).substList (A.reverse ++ P1.toList.reverse))
      ((C.argTy d D.params.length j).substList (B.reverse ++ Q2.toList.reverse)) := by
  have hdD := dataD_eq hW hD
  have hP1c := data_closed hW hD hP1
  have hQ2c : Q2.closedB 0 k3 = true := by
    have := closed_of_isTyK hW (Comp2_ty_base hQ2).2.2.1; simpa [Tm.closedB] using this
  have hPl : IsList P1 := by
    have := (dataLit_rel hW hD hP1 hP1P1 (ISub.id k3)).2.2.2.2.2.1; rwa [isub_id_of_closed hP1c] at this
  have hplen : P1.toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hP1⟩ : IsTyK S k3 (.data d P1)); rwa [hdD] at this
  have := argTy_rt2 hW hD hP1 hP1P1 hP1P1 hQ2 (ISub.id k3) hC hj hAl hBl (fun i hi => by
    rw [isub_id_of_closed hP1c]
    refine ⟨fun hri => ?_, fun hri => hrel i hi⟩
    have h := hrel i hi
    rwa [argTy_rec_inst hri hPl hplen (by simp; omega)] at h)
  rwa [isub_id_of_closed hP1c, isub_id_of_closed hQ2c] at this

/-- Transport along argument types at related prefixes of arguments and related parameters, from the
Kan properties of the argument types' codes. -/
theorem argLine_kanT {n' : ℕ} {P1 Q2 : Tm} (hP1 : HasTy S (n' + 1) .one [] (.data d P1) (.univ D.level))
    (hP1P1 : RT2 S (n' + 1) (.data d P1) (.data d P1)) (hQ2 : RT2 S (n' + 1) (.data d P1) (.data d Q2))
    (hArgK : KanShape S (n' + 1) (ΘK S D d (n' + 1) P1))
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {A B : List Tm} (hBl : B.length = A.length)
    (hAl : A.length < C.args.length) (hrr : C.isRec A.length = false)
    (hrel : ∀ i (hi : i < A.length), RE2 S (n' + 1) ((C.argTy d D.params.length i).substList ((A.take i).reverse ++
      P1.toList.reverse)) (A.getD i .abort) (B.getD i .abort)) :
    KanT2 S n' ((C.argTy d D.params.length A.length).substList (A.reverse ++ P1.toList.reverse))
      ((C.argTy d D.params.length A.length).substList (B.reverse ++ Q2.toList.reverse)) := by
  have hdD := dataD_eq hW hD
  have hP1c := data_closed hW hD hP1
  have hQ2c : Q2.closedB 0 (n' + 1) = true := by
    have := closed_of_isTyK hW (Comp2_ty_base hQ2).2.2.1; simpa [Tm.closedB] using this
  have hPl : IsList P1 := by
    have := (dataLit_rel hW hD hP1 hP1P1 (ISub.id (n' + 1))).2.2.2.2.2.1; rwa [isub_id_of_closed hP1c] at this
  have hplen : P1.toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hP1⟩ : IsTyK S (n' + 1) (.data d P1)); rwa [hdD] at this
  have hRR' := (dataLit_rel hW hD hP1 hQ2 (ISub.id (n' + 1))).1
  rw [isub_id_of_closed hP1c, isub_id_of_closed hQ2c] at hRR'
  have hRsem := semK_dataQ hW hD hP1 hP1P1 (ISub.id (n' + 1))
  rw [isub_id_of_closed hP1c] at hRsem
  have hA := argTy_code_rel hW hD hP1 (ISub.id (n' + 1)) hRR' hRsem hP1c hQ2c hC hBl
    (fun i hi hi' hri => by
      have h := hrel i hi
      rwa [argTy_rec_inst hri hPl hplen (by simp; omega), getD_eq_get' hi,
        getD_eq_get' hi'] at h)
    (fun i hi hi' hri => by
      have h := hrel i hi
      rwa [getD_eq_get' hi, getD_eq_get' hi'] at h)
    hAl hrr
  exact (kan_tyLook hW hD hArgK _ c A.length _ hA).2 rfl

end wrap

/-- Constructors with related arguments are related, at a literal type. -/
theorem RE2_con_args_id (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
    {k3 : ℕ} {P1 : Tm} (hP1 : HasTy S k3 .one [] (.data d P1) (.univ D.level)) (hPP : RT2 S k3 (.data d P1) (.data d P1))
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {Q1 : Tm} (Y Y' : List Tm)
    (hYl : Y.length = C.args.length) (hY'l : Y'.length = C.args.length)
    (hcT : HasTy S k3 .one [] (.con d c P1 (Tm.ofList Y) []) (.data d P1))
    (he : EqTm S k3 .one [] (.con d c P1 (Tm.ofList Y) []) (.con d c Q1 (Tm.ofList Y') []) (.data d P1))
    (hargs : ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ P1.toList.reverse)) (Y.getD i .abort) (Y'.getD i .abort)) :
    RE2 S k3 (.data d P1) (.con d c P1 (Tm.ofList Y) []) (.con d c Q1 (Tm.ofList Y') []) := by
  have hc1 : P1.closedB 0 k3 = true := data_closed hW hD hP1
  have := RE2_con_args hW hD hH hP1 hPP (ISub.id k3) hC (q := P1) (q' := Q1) hYl hY'l
    (by rw [isub_id_of_closed hc1]; exact hcT) (by rw [isub_id_of_closed hc1]; exact he)
    (fun i hi => by rw [isub_id_of_closed hc1]; exact hargs i hi)
  rwa [isub_id_of_closed hc1] at this


end

end Model.Whnf
