import Model.Whnf.HCCGen4
import Model.Whnf.Valid2TranspCon

/-!
# Composition of constructors

The binary validity of `hcompCon` for inductive types without path constructors. The rule's contractum
composes the arguments along the tube arguments `uargs` of the premise `u ≡ con uargs`, while the
redex steps to the contractum along the projections of `u`. The two are related at every stage by
`HCG.conRel` (compositions along related tube lists), and where the face holds by `face_con`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k : ℕ}

/-- The arguments of the `hcompCon` contractum as the telescope of the rule. -/
theorem gOuts_eq (d : ℕ) (D : DataDecl) (C : Ctor) (q : Tm) (φ : I) {us X : List Tm}
    (hul : us.length = C.args.length) (hXl : X.length = C.args.length) :
    Tm.hcompTele C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ 0 [] us X = gOuts d D C q φ us X := by
  have heqT := Meta.hcompTele_eq C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ us X us X 0 rfl rfl
    (by rw [hul, hXl])
  simp only [hXl, ← List.range_eq_range'] at heqT
  rw [show ([] : List Tm) = (Meta.hFills C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ us X 0).reverse
    from rfl]
  exact heqT

/-- The `hcompCon` contractum, restricted. -/
theorem gCon_isub (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {q : Tm} (hq : IsList q) (hql : q.toList.length = D.params.length) (φ : I)
    {us X : List Tm} (hul : us.length = C.args.length) (hXl : X.length = C.args.length) {k' : ℕ} (κ : ISub k' k) :
    (Tm.con d c q (Tm.ofList (gOuts d D C q φ us X)) []).isub κ =
      .con d c (q.isub κ) (Tm.ofList (gOuts d D C (q.isub κ) (φ.subst κ.τ) (us.map (·.isub κ.up))
        (X.map (·.isub κ)))) [] := by
  have hS := sigClosed_of_wfSig hW
  rw [← gOuts_eq d D C q φ hul hXl, ← gOuts_eq d D C (q.isub κ) (φ.subst κ.τ) (by simp [hul]) (by simp [hXl])]
  show Tm.con d c (q.isub κ) ((Tm.ofList _).isub κ) [] = _
  rw [ofList_isub]
  have h := hcompTele_subst (σ := Tm.var) (τ := κ.τ) (C := C) (argTy := C.argTy d D.params.length) (dataT := .data d q)
    (np := D.params.length) (fun j => argTy_closed hW hD hC j) (psL := q.dshift.toList)
    (by rw [dshift_eq, toList_subst hq]; simp [hql]) φ us X 0 [] rfl
  have e1 : q.dshift.toList.map (·.subst (dupS Tm.var) (I.up κ.τ)) = (q.isub κ).dshift.toList := by
    rw [← toList_subst (by rw [dshift_eq]; exact isList_subst hq _ _), dshift_dup_subst]; rfl
  have e2 : us.map (·.subst (dupS Tm.var) (I.up κ.τ)) = us.map (·.isub κ.up) := by
    simp only [show (dupS Tm.var : ℕ → Tm) = Tm.var from funext fun n => rfl]; rfl
  rw [e1, e2] at h
  exact congrArg (fun L => Tm.con d c (q.isub κ) (Tm.ofList L) []) h

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hP hPP

/-- An element related to a constructor reduces to the same constructor, with related arguments. -/
theorem conArgs {k3 : ℕ} (ρ3 : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q x : Tm} {Y : List Tm}
    (hx : RE2 S k3 (.data d (P.isub ρ3)) (.con d c q (Tm.ofList Y) []) x) :
    ∃ q' Z, RedE S k3 (.data d (P.isub ρ3)) x (.con d c q' (Tm.ofList Z) []) ∧ Y.length = C.args.length ∧
      Z.length = C.args.length ∧
      ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((Y.take i).reverse ++ (P.isub ρ3).toList.reverse)) (Y.getD i .abort) (Z.getD i .abort) := by
  obtain ⟨c1, C1, q1, Z1, q2, Z2, hC1, hZ1l, hZ2l, hr1, hr2, hZ⟩ := dataLit_argsU hW hD hH hP hPP ρ3 hx
  have e1 := RedW.unique hr1.1 (redW_self (step_con_nonHIT hD hH hC _ _ _))
  simp only [Tm.con.injEq] at e1
  obtain ⟨-, rfl, -, eY, -⟩ := e1
  have eY' := congrArg Tm.toList eY
  simp only [toList_ofList] at eY'
  subst eY'
  rw [hC] at hC1; cases hC1
  exact ⟨q2, Z2, hr2, hZ1l, hZ2l, hZ⟩

/-- The arguments of a constructor related to an element, against the projections of the element. -/
theorem projRel {k3 : ℕ} (ρ3 : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q x : Tm} {Y : List Tm}
    (hx : RE2 S k3 (.data d (P.isub ρ3)) (.con d c q (Tm.ofList Y) []) x) {j : ℕ} (hj : j < C.args.length) :
    RE2 S k3 ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ (P.isub ρ3).toList.reverse))
      (Y.getD j .abort) (proj d D (P.isub ρ3) c C j x) := by
  obtain ⟨q', Z, hw, hYl, hZl, hYZ⟩ := conArgs hW hD hH hP hPP ρ3 hC hx
  have hPρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ3
  have hxx := RE2.trans hW hPρ (RE2.symm hW hPρ hx) hx
  obtain ⟨-, p2, p3⟩ := projs_rel hW hD hH hP hPP hPP hPP ρ3 hxx hC hw.1 hj
  have hPl := (dataLit_rel hW hD hP hPP ρ3).2.2.2.2.2.1
  have hplen : (P.isub ρ3).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl (HasTy.isubS hW hP ρ3)⟩ : IsTyK S k3 (.data d (P.isub ρ3)))
    rwa [dataD_eq hW hD] at this
  have TX := argTy_rt2 hW hD hP hPP hPP hPP ρ3 hC hj (A := Y.take j) (B := Z.take j)
    (by simp [hYl]; omega) (by simp [hZl]; omega) (fun i hi => by
      have h := hYZ i (by omega)
      rw [getD_take_lt hi, getD_take_lt hi, List.take_take, Nat.min_eq_left hi.le]
      cases hri : C.isRec i
      · exact ⟨fun h' => (by cases h'), fun _ => h⟩
      · refine ⟨fun _ => ?_, fun h' => (by cases h')⟩
        rwa [argTy_rec_inst hri hPl hplen (by simp [hYl]; omega)] at h)
  have a1 := hYZ j hj
  have hXT := RE2.tyCode hW a1
  have hXZ := RT2.tyCode_r hW TX hXT
  have q1 := RE2.conv hW (RT2.symm hW hXT TX) (RE2.conv hW (RT2.symm hW hXZ p3)
    (RE2.symm hW (RT2.refl' hW hXZ p3) p2))
  exact RE2.trans hW (RT2.refl hW hXT TX) a1 q1

/-- The arguments of related constructors are related. -/
theorem conArgs2 {k3 : ℕ} (ρ3 : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q q' : Tm}
    {Y Y' : List Tm}
    (hx : RE2 S k3 (.data d (P.isub ρ3)) (.con d c q (Tm.ofList Y) []) (.con d c q' (Tm.ofList Y') [])) :
    Y.length = C.args.length ∧ ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((Y.take i).reverse ++ (P.isub ρ3).toList.reverse)) (Y.getD i .abort) (Y'.getD i .abort) := by
  obtain ⟨q2, Z, hw, hYl, -, h⟩ := conArgs hW hD hH hP hPP ρ3 hC hx
  have e := RedW.unique hw.1 (redW_self (step_con_nonHIT hD hH hC _ _ _))
  simp only [Tm.con.injEq] at e
  obtain ⟨-, -, -, eZ, -⟩ := e
  have eZ' := congrArg Tm.toList eZ
  simp only [toList_ofList] at eZ'
  subst eZ'
  exact ⟨hYl, h⟩

omit hD hH hP hPP in
/-- Compositions over related lines of the oracle, at a related type. -/
theorem hc2_of_oracle (hK : KanOracle2 S) {A L L' a a' : Tm} (hX : TyCode k (semK S k L)) (hLA : RT2 S k L A)
    (hLL' : RT2 S k L L') : HC2 S k A L L' a a' :=
  HC2.conv hW hLA hX (KanH2.at (hK.hcomp k L L' hLL') a a')

omit hW hD hH hP hPP in
theorem getD_map_dinst (L : List Tm) (i : ℕ) (r : I) :
    (L.map (·.dinst r)).getD i .abort = (L.getD i .abort).dinst r := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases L[i]? with _ | a <;> rfl

/-- The data of `HCG` for the contractum of the rule (tube arguments `Ys`) against the contractum of
the step (the projections of the tube). -/
theorem hcgAt (hK : KanOracle2 S) {k1 : ℕ} (ρ : ISub k1 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {u qs : Tm} {φ : I} {X Ys : List Tm} (hYl : Ys.length = C.args.length)
    (hty : HasTy S k1 .one [] (.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ)))
    (hYe : EqTm0 S (k1 + 1) (cof .one φ).shift [] u (.con d c (P.isub ρ).dshift (Tm.ofList Ys) [])
      (.data d (P.isub ρ).dshift))
    (hYr : ∀ k3 (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (φ.subst σ.τ)).holds →
      RE2 S k3 (.data d (P.isub (ρ.comp σ)))
        (.con d c (P.isub (ρ.comp σ)) (Tm.ofList (Ys.map (·.isub (ISub.cons r hr σ)))) []) ((u.isub σ.up).dinst r'))
    (hub : ∀ k3 (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds →
      RE2 S k3 (.data d (P.isub (ρ.comp σ))) ((u.isub σ.up).dinst .zero) ((Tm.con d c qs (Tm.ofList X) []).isub σ))
    (hbb : RE2 S k1 (.data d (P.isub ρ)) (.con d c qs (Tm.ofList X) []) (.con d c qs (Tm.ofList X) []))
    (he : EqTm S k1 .one [] (.con d c (P.isub ρ) (Tm.ofList (gOuts d D C (P.isub ρ) φ Ys X)) [])
      (.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ))) :
    HCG S d D K P P P k1 ρ c C X X φ φ Ys ((List.range C.args.length).map fun j => proj d D (P.isub ρ).dshift c C j u) := by
  have hS := sigClosed_of_wfSig hW
  have hpT : HasTy S k1 .one [] (.data d (P.isub ρ)) (.univ D.level) := HasTy.isubS hW hP ρ
  obtain ⟨l0, ⟨hdq, hφs, hut, hb, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨hXq, ebase, -, hXl⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb)) (TyEq.refl _) hpT
  have hcs : (cof .one φ).Scoped k1 := ⟨trivial, hφs⟩
  have hside' : EqTm S k1 (cof .one φ) [] (u.dinst .zero) (.con d c (P.isub ρ) (Tm.ofList X) []) (.data d (P.isub ρ)) :=
    (minimal_to_spec_eq hside).trans (EqTm.restrict hcs (ent_and_left _ _) ebase)
  have ePσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) := fun σ => by
    show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]
  have hPσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), RT2 S k3 (.data d (P.isub (ρ.comp σ))) (.data d (P.isub (ρ.comp σ))) :=
    fun σ => RT2.isub hW (tyCode_of_univ hW hP) hPP _
  have htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u := by
    intro k3 σ r r' hr hr' hE hh
    rw [ePσ]
    exact RE2.trans hW (hPσ σ) (RE2.symm hW (hPσ σ) (hYr k3 σ r r hr hr (I_eq_refl _) hh)) (hYr k3 σ r r' hr hr' hE hh)
  have hcan := tubeCanon_of hW hD hH hP ρ (TyEq.refl _) hpT htube
  obtain ⟨G1', G2', G3', G4'⟩ := hcompCon_premises hW hD hH hC hpT hφs hut hside' hXq hcan
  have hΦs : ((cof .one φ).shift).Scoped (k1 + 1) := KubusCore.I.scoped_shift hcs
  have hdq1 : HasTy0 S (k1 + 1) (cof .one φ).shift [] (.data d (P.isub ρ).dshift) (.univ D.level) :=
    HasTy0.restrict hΦs (ent_one _) (HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal hW hpT))
  obtain ⟨G1, -, -⟩ := con_retype0 hW hD hH hC hYe hdq1
  have H1 := PD.of hW hD hH hdq1
  -- the tube arguments at `0`, against the base's arguments
  have hdqc : HasTy0 S k1 (cof .one φ) [] (.data d (P.isub ρ)) (.univ D.level) :=
    HasTy0.restrict hcs (ent_and_left _ _) (spec_to_minimal hW hpT)
  have Hc := PD.of hW hD hH hdqc
  have eY0 : EqTm0 S k1 (cof .one φ) [] (.con d c (P.isub ρ) (Tm.ofList (Ys.map (·.dinst .zero))) [])
      (.con d c (P.isub ρ) (Tm.ofList X) []) (.data d (P.isub ρ)) := by
    have h1 := EqTm0.dsubst hS (Ψ := k1) (Φ := cof .one φ) (Γ := []) hYe (r := .zero) trivial
    have e2 : (Tm.con d c (P.isub ρ).dshift (Tm.ofList Ys) []).dinst .zero =
        .con d c (P.isub ρ) (Tm.ofList (Ys.map (·.dinst .zero))) [] := by
      show Tm.con d c ((P.isub ρ).dshift.dinst .zero) ((Tm.ofList Ys).dinst .zero) [] = _
      rw [dshift_dinst]; show Tm.con d c _ ((Tm.ofList Ys).subst _ _) [] = _; rw [ofList_subst]; rfl
    rw [e2, show (Tm.data d (P.isub ρ).dshift).dinst .zero = .data d (P.isub ρ) by
      show Tm.data d ((P.isub ρ).dshift.dinst .zero) = _; rw [dshift_dinst]] at h1
    exact (EqTm0.symm h1).trans (spec_to_minimal_eq hW hside')
  have hXqc : HasTele0 S k1 (cof .one φ) [] (Tm.ofList X) (C.argTys d D.params.length) (P.isub ρ).toList.reverse :=
    (con_retype0 hW hD hH hC (EqTm0.refl (HasTy0.restrict hcs (ent_and_left _ _)
      (spec_to_minimal hW (HasTy.eqR ebase)))) hdqc).1
  have hY0t := (con_retype0 hW hD hH hC eY0.symm hdqc).1
  have hpl := (dataLit_rel hW hD hP hPP ρ).2.2.2.2.2.1
  have hplen : (P.isub ρ).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hpT⟩ : IsTyK S k1 (.data d (P.isub ρ))); rwa [dataD_eq hW hD] at this
  have hbbA := conArgs2 hW hD hH hP hPP ρ hC hbb
  have hdq1o : HasTy0 S (k1 + 1) .one [] (.data d (P.isub ρ).dshift) (.univ D.level) :=
    HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal hW hpT)
  have H1o := PD.of hW hD hH hdq1o
  have prjEq : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) {j : ℕ} (hj : j < C.args.length),
      (((List.range C.args.length).map fun j => proj d D (P.isub ρ).dshift c C j u).getD j .abort).isub
        (ISub.cons r hr σ) = proj d D (P.isub (ρ.comp σ)) c C j ((u.isub σ.up).dinst r) := by
    intro k3 σ r hr j hj
    rw [show ((List.range C.args.length).map fun j => proj d D (P.isub ρ).dshift c C j u).getD j .abort =
      proj d D (P.isub ρ).dshift c C j u by simp [List.getD_eq_getElem?_getD, hj],
      proj_tube_isub hW hD hC hj H1o.hpsL H1o.hpl σ hr, Tm.isub_isub]
  have hXP := tyCode_of_univ hW hP
  have hXPσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), TyCode k3 (semK S k3 (.data d (P.isub (ρ.comp σ)))) :=
    fun σ => tyCode_of_univ hW (HasTy.isubS hW hP _)
  refine {
    hW := hW, hD := hD, hH := hH, hP := hP, hPP := hPP, hQ := hPP, hQ' := hPP, hArgK := kanShape_of_oracle hK _,
    hC := hC, hXl := hXl, hXl' := hXl, hul := hYl, hul' := by simp,
    hrecR := fun i hi hri => by
      have := hbbA.2 i hi; rwa [argTy_rec_inst hri hpl hplen (by simp; omega)] at this,
    hptR := fun i hi _ => hbbA.2 i hi,
    hrecH := fun i hi hri Q1 Q1' h1 h1' K2 σ => by
      have a := RT2.isub hW hXP h1 (ρ.comp σ)
      have a' := RT2.isub hW hXP h1' (ρ.comp σ)
      have hXQ := RT2.tyCode_r hW a (hXPσ σ)
      exact hc2_of_oracle hW hK hXQ (RT2.symm hW (hXPσ σ) a) (RT2.trans hW hXQ (RT2.symm hW (hXPσ σ) a) a'),
    h12 := ent_refl _, h21 := ent_refl _, hqT := hpT, hq'T := hpT, hφs := hφs, hφs' := hφs, hXq := hXq,
    hXq' := hXq, G1 := G1, G1' := G1', G3 := ?_, G3' := G3', G4 := fun i hi => ?_, G4' := fun i hi => by
      rw [show ((List.range C.args.length).map fun j => proj d D (P.isub ρ).dshift c C j u).getD i .abort =
        proj d D (P.isub ρ).dshift c C i u by simp [List.getD_eq_getElem?_getD, (by omega : i < C.args.length)]]
      exact G4' i hi,
    euu := fun i hi => con_args_eq hW hD hH H1 hC G1 G1' ((EqTm0.symm hYe).trans G2') hi,
    eLR := ?_, prj := fun σ r r' hr hr' hE hh j hj => ?_, prjs := fun σ r r' hr hr' hE hh j hj => ?_,
    prjb := fun σ hh j hj => ?_, prjb' := fun σ hh j hj => ?_ }
  · rw [show (Tm.ofList Ys).dinst .zero = Tm.ofList (Ys.map (·.dinst .zero)) by
      show (Tm.ofList Ys).subst _ _ = _; rw [ofList_subst]; rfl]
    refine EqTele0.ofList_of' (wf_of_eq eY0) _ _ _ _ (by simp [hYl, Ctor.argTys]) (by simp [hXl, Ctor.argTys])
      fun j a a' A ha ha' hA => ?_
    have hj : j < C.args.length := by
      have := (List.getElem?_eq_some_iff.1 hA).1; simpa [Ctor.argTys] using this
    rw [argTys_get hj] at hA; cases hA
    have h := con_args_eq hW hD hH Hc hC hY0t hXqc eY0 hj
    rw [List.getD_eq_getElem?_getD, ha, List.getD_eq_getElem?_getD, ha'] at h
    exact h
  · have h := con_args_eq hW hD hH Hc hC hXqc hY0t eY0.symm (j := i) (by omega)
    rw [getD_map_dinst, getD_eq_get hi] at h
    exact EqTm0.symm h
  · have e_hc := hcompCon_sound hW hD hH hC hty hcan
    rw [gOuts_eq d D C (P.isub ρ) φ (by simp) hXl] at e_hc
    exact he.trans e_hc
  · rw [prjEq σ r' hr' hj, ← getD_map_isub]
    exact projRel hW hD hH hP hPP (ρ.comp σ) hC (hYr _ σ r r' hr hr' hE hh) hj
  · have a := hYr _ σ r r' hr hr' hE hh
    have b := hYr _ σ r' r' hr' hr' (I_eq_refl _) hh
    have := (conArgs2 hW hD hH hP hPP (ρ.comp σ) hC (RE2.trans hW (hPσ σ) a (RE2.symm hW (hPσ σ) b))).2 j hj
    rwa [getD_map_isub, getD_map_isub] at this
  · have a := hYr _ σ .zero .zero trivial trivial (I_eq_refl _) hh
    have b := hub _ σ hh
    rw [show (Tm.con d c qs (Tm.ofList X) []).isub σ = .con d c (qs.isub σ) (Tm.ofList (X.map (·.isub σ))) [] by
      show Tm.con d c (qs.isub σ) ((Tm.ofList X).isub σ) [] = _; rw [ofList_isub]] at b
    have := (conArgs2 hW hD hH hP hPP (ρ.comp σ) hC (RE2.trans hW (hPσ σ) a b)).2 j hj
    rwa [getD_map_isub, getD_map_isub] at this
  · have b := hub _ σ hh
    rw [show (Tm.con d c qs (Tm.ofList X) []).isub σ = .con d c (qs.isub σ) (Tm.ofList (X.map (·.isub σ))) [] by
      show Tm.con d c (qs.isub σ) ((Tm.ofList X).isub σ) [] = _; rw [ofList_isub]] at b
    rw [prjEq σ .zero trivial hj, ← getD_map_isub]
    exact projRel hW hD hH hP hPP (ρ.comp σ) hC (RE2.symm hW (hPσ σ) b) hj

end lit

end

end Model.Whnf
