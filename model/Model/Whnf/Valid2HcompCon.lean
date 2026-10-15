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
theorem HC2.of_kan {A L L' a a' : Tm} (hX : TyCode k (semK S k L)) (hLA : RT2 S k L A)
    (hK : KanH2 S k L L') : HC2 S k A L L' a a' :=
  HC2.conv hW hLA hX (KanH2.at hK a a')

omit hW hD hH hP hPP in
theorem getD_map_dinst (L : List Tm) (i : ℕ) (r : I) :
    (L.map (·.dinst r)).getD i .abort = (L.getD i .abort).dinst r := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases L[i]? with _ | a <;> rfl

/-- The data of `HCG` for the contractum of the rule (tube arguments `Ys`) against the contractum of
the step (the projections of the tube). -/
theorem hcgAt {k1 : ℕ} (ρ : ISub k1 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
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
    hW := hW, hD := hD, hH := hH, hP := hP, hPP := hPP, hQ := hPP, hQ' := hPP,
    hC := hC, hXl := hXl, hXl' := hXl, hul := hYl, hul' := by simp,
    hrecR := fun i hi hri => by
      have := hbbA.2 i hi; rwa [argTy_rec_inst hri hpl hplen (by simp; omega)] at this,
    hptR := fun i hi _ => hbbA.2 i hi,
    hrecH := fun i hi hri Q1 Q1' h1 h1' K2 σ => by
      have a := RT2.isub hW hXP h1 (ρ.comp σ)
      have a' := RT2.isub hW hXP h1' (ρ.comp σ)
      have hXQ := RT2.tyCode_r hW a (hXPσ σ)
      have hQQ' := RT2.trans hW hXQ (RT2.symm hW (hXPσ σ) a) a'
      exact HC2.of_kan hW hXQ (RT2.symm hW (hXPσ σ) a)
        (kanH2_data hW hD hH hQQ' ⟨redW_self (step_data d _), TyEq.refl _⟩),
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

/-- The contractum of the rule at the tube arguments `Ys` is related to the composition of a
constructor. -/
theorem rel_hcompCon {k1 : ℕ} (ρ : ISub k1 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {u qs : Tm} {φ : I} {X Ys : List Tm} (hYl : Ys.length = C.args.length)
    (hty : HasTy S k1 .one [] (.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ)))
    (hrr : RE2 S k1 (.data d (P.isub ρ)) (.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
      (.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])))
    (hYe : ∀ k2 (κ : ISub k2 k1), EqTm0 S (k2 + 1) (cof .one (φ.subst κ.τ)).shift [] (u.isub κ.up)
      (.con d c (P.isub (ρ.comp κ)).dshift (Tm.ofList (Ys.map (·.isub κ.up))) []) (.data d (P.isub (ρ.comp κ)).dshift))
    (hYr : ∀ k3 (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) (φ.subst σ.τ)).holds →
      RE2 S k3 (.data d (P.isub (ρ.comp σ)))
        (.con d c (P.isub (ρ.comp σ)) (Tm.ofList (Ys.map (·.isub (ISub.cons r hr σ)))) []) ((u.isub σ.up).dinst r'))
    (hub : ∀ k3 (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds →
      RE2 S k3 (.data d (P.isub (ρ.comp σ))) ((u.isub σ.up).dinst .zero) ((Tm.con d c qs (Tm.ofList X) []).isub σ))
    (hbb : RE2 S k1 (.data d (P.isub ρ)) (.con d c qs (Tm.ofList X) []) (.con d c qs (Tm.ofList X) []))
    (he : EqTm S k1 .one [] (.con d c (P.isub ρ) (Tm.ofList (gOuts d D C (P.isub ρ) φ Ys X)) [])
      (.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ))) :
    RE2 S k1 (.data d (P.isub ρ)) (.con d c (P.isub ρ) (Tm.ofList (gOuts d D C (P.isub ρ) φ Ys X)) [])
      (.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) := by
  have hpT : HasTy S k1 .one [] (.data d (P.isub ρ)) (.univ D.level) := HasTy.isubS hW hP ρ
  obtain ⟨l0, ⟨-, hφs, -, hb, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨-, -, -, hXl⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb)) (TyEq.refl _) hpT
  have hpl := (dataLit_rel hW hD hP hPP ρ).2.2.2.2.2.1
  have hplen : (P.isub ρ).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hpT⟩ : IsTyK S k1 (.data d (P.isub ρ))); rwa [dataD_eq hW hD] at this
  refine RE2_conW hW hD hH hP hPP ρ hC (HasTy.eqL he) hrr he fun k2 κ => ?_
  have eP : (P.isub ρ).isub κ = P.isub (ρ.comp κ) := Tm.isub_isub _ _ _
  have eX : (Tm.con d c qs (Tm.ofList X) []).isub κ = .con d c (qs.isub κ) (Tm.ofList (X.map (·.isub κ))) [] := by
    show Tm.con d c (qs.isub κ) ((Tm.ofList X).isub κ) [] = _; rw [ofList_isub]
  have eR : (Tm.hcomp (.data d (P.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])).isub κ =
      .hcomp (.data d (P.isub (ρ.comp κ))) (φ.subst κ.τ) (u.isub κ.up)
        (.con d c (qs.isub κ) (Tm.ofList (X.map (·.isub κ))) []) := by
    rw [← eX, ← eP]; rfl
  rw [gCon_isub hW hD hC hpl hplen φ hYl hXl κ, eP, eR]
  have hty2 := HasTy.isubS hW hty κ
  rw [eR, show (Tm.data d (P.isub ρ)).isub κ = .data d (P.isub (ρ.comp κ)) by
    show Tm.data d ((P.isub ρ).isub κ) = _; rw [eP]] at hty2
  have he2 := EqTm.isubS hW he κ
  rw [gCon_isub hW hD hC hpl hplen φ hYl hXl κ, eP, eR, show (Tm.data d (P.isub ρ)).isub κ = .data d (P.isub (ρ.comp κ)) by
    show Tm.data d ((P.isub ρ).isub κ) = _; rw [eP]] at he2
  have hPσ : ∀ {k3 : ℕ} (σ : ISub k3 k2), RT2 S k3 (.data d (P.isub ((ρ.comp κ).comp σ)))
      (.data d (P.isub ((ρ.comp κ).comp σ))) := fun σ => RT2.isub hW (tyCode_of_univ hW hP) hPP _
  have hYr2 : ∀ k3 (σ : ISub k3 k2) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
      (ival (idEnv k3) ((φ.subst κ.τ).subst σ.τ)).holds →
      RE2 S k3 (.data d (P.isub ((ρ.comp κ).comp σ)))
        (.con d c (P.isub ((ρ.comp κ).comp σ)) (Tm.ofList ((Ys.map (·.isub κ.up)).map (·.isub (ISub.cons r hr σ))))
          []) (((u.isub κ.up).isub σ.up).dinst r') := by
    intro k3 σ r r' hr hr' hE hh
    have h := hYr k3 (κ.comp σ) r r' hr hr' hE (by rw [I_subst_comp]; exact hh)
    rw [ISub.comp_assoc, List.map_map]
    rw [show ((u.isub κ.up).isub σ.up) = u.isub (κ.comp σ).up by rw [Tm.isub_isub, ISub.up_comp]]
    rw [show ((·.isub (ISub.cons r hr σ)) ∘ (·.isub κ.up) : Tm → Tm) = (·.isub (ISub.cons r hr (κ.comp σ))) by
      funext t; simp only [Function.comp, Tm.isub_isub, ISub.up_comp_cons]]
    exact h
  have hub2 : ∀ k3 (σ : ISub k3 k2), (ival (idEnv k3) ((φ.subst κ.τ).subst σ.τ)).holds →
      RE2 S k3 (.data d (P.isub ((ρ.comp κ).comp σ))) (((u.isub κ.up).isub σ.up).dinst .zero)
        ((Tm.con d c (qs.isub κ) (Tm.ofList (X.map (·.isub κ))) []).isub σ) := by
    intro k3 σ hh
    have h := hub k3 (κ.comp σ) (by rw [I_subst_comp]; exact hh)
    rw [ISub.comp_assoc, show ((u.isub κ.up).isub σ.up) = u.isub (κ.comp σ).up by rw [Tm.isub_isub, ISub.up_comp],
      ← eX, Tm.isub_isub]
    exact h
  have hbb2 := RE2.isub hW hbb κ
  rw [eX, show (Tm.data d (P.isub ρ)).isub κ = .data d (P.isub (ρ.comp κ)) by
    show Tm.data d ((P.isub ρ).isub κ) = _; rw [eP]] at hbb2
  have H := hcgAt hW hD hH hP hPP (ρ.comp κ) hC (u := u.isub κ.up) (qs := qs.isub κ) (φ := φ.subst κ.τ)
    (X := X.map (·.isub κ)) (Ys := Ys.map (·.isub κ.up)) (by simp [hYl]) hty2 (hYe k2 κ) hYr2 hub2 hbb2 he2
  have R := H.conRel
  have hXl2 : (X.map (·.isub κ)).length = C.args.length := by simp [hXl]
  by_cases hf : I.Entails .one (φ.subst κ.τ)
  · have htube : Tube2 S k2 (.data d (P.isub (ρ.comp κ))) (φ.subst κ.τ) (u.isub κ.up) (u.isub κ.up) := by
      intro k3 σ r r' hr hr' hE hh
      rw [show (Tm.data d (P.isub (ρ.comp κ))).isub σ = .data d (P.isub ((ρ.comp κ).comp σ)) by
        show Tm.data d ((P.isub (ρ.comp κ)).isub σ) = _; rw [Tm.isub_isub]]
      exact RE2.trans hW (hPσ σ) (RE2.symm hW (hPσ σ) (hYr2 k3 σ r r hr hr (I_eq_refl _) hh))
        (hYr2 k3 σ r r' hr hr' hE hh)
    have F := face_con hW hD hH hP hPP hPP (ρ.comp κ) hC hf hty2 htube
    have F' := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP (ρ.comp κ)).1 F).2
    have F'' := DR2At.expandR hW F' (.step (step_hcomp_face hf) (.refl _)) (EqTm.hcompFace hf hty2)
    exact DR2At_trans hW (Hom.id K) (perP_ΘK hW hD hP) R F'' (argRelH_lit hW hD hH hP hPP (ρ.comp κ))
  · have hs := step_hcompCon (S := S) hD hH hC (ps := P.isub (ρ.comp κ)) (u := u.isub κ.up) (qs := qs.isub κ) hf
      (X.map (·.isub κ))
    rw [gOuts_eq d D C _ _ (by simp) hXl2] at hs
    exact DR2At.expandR hW R (.step hs (.refl _)) (he2.symm.trans H.eLR)

end lit

section valid
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
include hW hD hH
variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- **Composition of a constructor** of an inductive type without path constructors. -/
theorem valid_hcompCon {c : ℕ} {C : Ctor} {ps u qs uargs args T : Tm} {φ : I}
    (hC : D.ctors[c]? = some C) (hps : ps = Tm.ofList ps.toList) (hargs : args = Tm.ofList args.toList)
    (huargs : uargs = Tm.ofList uargs.toList)
    (h6 : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (h7 : HasTele0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse)
    (h8 : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (.con d c ps.dshift uargs []) (.data d ps.dshift))
    (h9 : EqTele0 S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse)
    (hv8 : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (.con d c ps.dshift uargs []) (.data d ps.dshift))
    (hv : Valid2 S Ψ Φ Γ (.hcomp (.data d ps) φ u (.con d c qs args []))
      (.hcomp (.data d ps) φ u (.con d c qs args [])) T)
    (hinv : HcompInv S Ψ Φ Γ (.data d ps) φ u (.con d c qs args []) T) :
    Valid2 S Ψ Φ Γ (.hcomp (.data d ps) φ u (.con d c qs args []))
      (.con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d ps) ps.dshift.toList φ 0 []
        uargs.toList args.toList)) []) T := by
  obtain ⟨l, hφ, hAV, huV, haV, hsV, htr, hA, hu, ha, hside⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele hA rfl
  rw [hD] at hD2; cases hD2
  have hdD : HasTy0 S Ψ Φ Γ (.data d ps) (.univ D.level) := HasTy0.data hD (hW.2 d D hD).1 hpt
  have hty0 : HasTy0 S Ψ Φ Γ (.hcomp (.data d ps) φ u (.con d c qs args [])) (.data d ps) :=
    HasTy0.hcomp hA hφ hu ha hside
  have heqD := EqTm0.hcompCon hD hH hC hps hargs huargs h6 h7 h8 h9 hty0
  have hvD := valid_hcomp hW hφ (ent_refl _) (ent_refl _) hAV huV haV hsV hsV hty0 hty0 (EqTm0.refl hty0)
    (EqTm0.refl hu)
  intro k γ
  refine ⟨(hv k γ).1, ?_⟩
  have key : RE2 S k (.data d (γ.R ps)) (γ.R (.con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length)
      (.data d ps) ps.dshift.toList φ 0 [] uargs.toList args.toList)) []))
      (γ.R (.hcomp (.data d ps) φ u (.con d c qs args []))) := by
    have hXR : γ.R args = Tm.ofList (args.toList.map γ.R) := by
      show args.subst γ.γ' γ.σ'.τ = _; conv_lhs => rw [hargs]
      exact ofList_subst _ _ _
    have hYR : (γ.up hW).R uargs = Tm.ofList (uargs.toList.map (γ.up hW).R) := by
      show uargs.subst _ _ = _; conv_lhs => rw [huargs]
      exact ofList_subst _ _ _
    have hYl : (uargs.toList.map (γ.up hW).R).length = C.args.length := by
      simpa [Ctor.argTys] using Meta.tele_length h7
    have hXl : (args.toList.map γ.R).length = C.args.length := by
      simpa [Ctor.argTys] using Meta.tele_length h6
    have hpsl : ps.toList.length = D.params.length := by simpa using Meta.tele_length hpt
    have eRedex : γ.R (.hcomp (.data d ps) φ u (.con d c qs args [])) = .hcomp (.data d (γ.R ps)) (φ.subst γ.σ'.τ)
        ((γ.up hW).R u) (.con d c (γ.R qs) (Tm.ofList (args.toList.map γ.R)) []) := by
      rw [← hXR]; rfl
    have eCon : γ.R (.con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (.data d ps)
        ps.dshift.toList φ 0 [] uargs.toList args.toList)) []) =
        .con d c (γ.R ps) (Tm.ofList (gOuts d D C (γ.R ps) (φ.subst γ.σ'.τ) (uargs.toList.map (γ.up hW).R)
          (args.toList.map γ.R))) [] := by
      rw [← gOuts_eq d D C _ _ hYl hXl]
      show Tm.con d c (γ.R ps) ((Tm.ofList _).subst γ.γ' γ.σ'.τ) [] = _
      rw [ofList_subst]
      have hps1 : IsList ps.dshift := by rw [dshift_eq]; exact isList_subst hps _ _
      have h := hcompTele_subst (σ := γ.γ') (τ := γ.σ'.τ) (C := C) (argTy := C.argTy d D.params.length)
        (dataT := .data d ps) (np := D.params.length) (fun j => argTy_closed hW hD hC j) (psL := ps.dshift.toList)
        (by rw [dshift_eq, toList_subst hps]; simp [hpsl]) φ uargs.toList args.toList 0 [] rfl
      rw [h, ← toList_subst hps1, dshift_dup_subst]
      rfl
    let cR := γ.diagR hW
    have hPT : HasTy S k .one [] (.data d (γ.R ps)) (.univ D.level) := cR.ty hW hdD
    have hPP : RT2 S k (.data d (γ.R ps)) (.data d (γ.R ps)) := hAV.ty hW cR
    have hPc : (γ.R ps).closedB 0 k = true := data_closed hW hD hPT
    have e0 : (γ.R ps).isub (ISub.id k) = γ.R ps := isub_id_of_closed hPc
    have hty : HasTy S k .one [] (.hcomp (.data d (γ.R ps)) (φ.subst γ.σ'.τ) ((γ.up hW).R u)
        (.con d c (γ.R qs) (Tm.ofList (args.toList.map γ.R)) [])) (.data d (γ.R ps)) := by
      have := cR.ty hW hty0; rw [← eRedex]; exact this
    have hrr := (hvD k cR).2
    change RE2 S k (.data d (γ.R ps)) (γ.R _) (γ.R _) at hrr
    rw [eRedex] at hrr
    have hbb := (haV k cR).2
    change RE2 S k (.data d (γ.R ps)) (.con d c (γ.R qs) (γ.R args) []) (.con d c (γ.R qs) (γ.R args) []) at hbb
    rw [hXR] at hbb
    have he := (cR.eq hW heqD).symm
    change EqTm S k .one [] (γ.R _) (γ.R _) (.data d (γ.R ps)) at he
    rw [eCon, eRedex] at he
    have eUp : ∀ (t : Tm), (cR.up hW).R t = (γ.up hW).R t := fun t => rfl
    have eConUp : ∀ {k2 : ℕ} (κ : ISub k2 k), ((γ.up hW).R (.con d c ps.dshift uargs [])).isub κ.up =
        .con d c ((γ.R ps).isub κ).dshift (Tm.ofList ((uargs.toList.map (γ.up hW).R).map (·.isub κ.up))) [] := by
      intro k2 κ
      show Tm.con d c ((ps.dshift.subst (dupS γ.γ') (I.up γ.σ'.τ)).isub κ.up) (((γ.up hW).R uargs).isub κ.up) [] = _
      rw [dshift_dup_subst, hYR, ofList_isub]
      show Tm.con d c ((γ.R ps).dshift.isub κ.up) _ [] = _
      rw [isub_dshift]
    have eDataUp : ∀ {k2 : ℕ} (κ : ISub k2 k), ((γ.up hW).R (.data d ps.dshift)).isub κ.up =
        .data d ((γ.R ps).isub κ).dshift := by
      intro k2 κ
      show Tm.data d ((ps.dshift.subst (dupS γ.γ') (I.up γ.σ'.τ)).isub κ.up) = _
      rw [dshift_dup_subst]
      show Tm.data d ((γ.R ps).dshift.isub κ.up) = _
      rw [isub_dshift]
    have hYe : ∀ k2 (κ : ISub k2 k), EqTm0 S (k2 + 1) (cof .one ((φ.subst γ.σ'.τ).subst κ.τ)).shift []
        (((γ.up hW).R u).isub κ.up)
        (.con d c ((γ.R ps).isub κ).dshift (Tm.ofList ((uargs.toList.map (γ.up hW).R).map (·.isub κ.up))) [])
        (.data d ((γ.R ps).isub κ).dshift) := by
      intro k2 κ
      have hφ' : (φ.subst (cR.restr hW κ).σ.τ).Scoped k2 := I.scoped_subst hφ (cR.restr hW κ).σ.sc
      have E := (sub_eq hS h8).2 (((cR.restr hW κ).tySubRCof hW hφ').dup hS)
      change EqTm0 S (k2 + 1) (cof .one (φ.subst (γ.σ'.comp κ).τ)).shift [] (((cR.restr hW κ).up hW).R u)
        (((cR.restr hW κ).up hW).R (.con d c ps.dshift uargs [])) (((cR.restr hW κ).up hW).R (.data d ps.dshift)) at E
      rw [CSub2.up_restr_R, CSub2.up_restr_R, CSub2.up_restr_R, eUp, eUp, eUp, eConUp, eDataUp, I_subst_comp] at E
      exact E
    have hXPR := tyCode_of_univ hW hPT
    have hPRσ : ∀ {k3 : ℕ} (σ : ISub k3 k), RT2 S k3 (.data d ((γ.R ps).isub σ)) (.data d ((γ.R ps).isub σ)) :=
      fun σ => RT2.isub hW hXPR hPP σ
    have hfσ : ∀ {k3 : ℕ} (σ : ISub k3 k), (ival (idEnv k3) ((φ.subst γ.σ'.τ).subst σ.τ)).holds →
        I.Entails .one (φ.subst (cR.restr hW σ).σ.τ) := by
      intro k3 σ hh
      change I.Entails .one (φ.subst (γ.σ'.comp σ).τ)
      rw [I_subst_comp]
      exact (holds_iff_entails (I.scoped_subst (I.scoped_subst hφ γ.σ'.sc) σ.sc)).1 hh
    have hYr : ∀ k3 (σ : ISub k3 k) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
        (ival (idEnv k3) ((φ.subst γ.σ'.τ).subst σ.τ)).holds →
        RE2 S k3 (.data d ((γ.R ps).isub σ))
          (.con d c ((γ.R ps).isub σ) (Tm.ofList ((uargs.toList.map (γ.up hW).R).map (·.isub (ISub.cons r hr σ)))) [])
          ((((γ.up hW).R u).isub σ.up).dinst r') := by
      intro k3 σ r r' hr hr' hE hh
      have h := (hv8 k3 (((cR.restr hW σ).cof (hfσ σ hh)).cons r' r hr' hr (I_eq_symm hE))).2
      rw [CSub2.L_cons hW, CSub2.L_cons hW, CSub2.R_cons hW] at h
      change RE2 S k3 ((((cR.restr hW σ).up hW).L (.data d ps.dshift)).dinst r') ((((cR.restr hW σ).up hW).L u).dinst r')
        ((((cR.restr hW σ).up hW).R (.con d c ps.dshift uargs [])).dinst r) at h
      rw [CSub2.up_restr_L, CSub2.up_restr_L, CSub2.up_restr_R] at h
      change RE2 S k3 ((((γ.up hW).R (.data d ps.dshift)).isub σ.up).dinst r') ((((γ.up hW).R u).isub σ.up).dinst r')
        ((((γ.up hW).R (.con d c ps.dshift uargs [])).isub σ.up).dinst r) at h
      rw [eConUp, eDataUp] at h
      have e1 : (Tm.data d ((γ.R ps).isub σ).dshift).dinst r' = .data d ((γ.R ps).isub σ) := by
        show Tm.data d (((γ.R ps).isub σ).dshift.dinst r') = _; rw [dshift_dinst]
      have e2 : (Tm.con d c ((γ.R ps).isub σ).dshift
          (Tm.ofList ((uargs.toList.map (γ.up hW).R).map (·.isub σ.up))) []).dinst r =
          .con d c ((γ.R ps).isub σ) (Tm.ofList ((uargs.toList.map (γ.up hW).R).map (·.isub (ISub.cons r hr σ)))) [] := by
        show Tm.con d c (((γ.R ps).isub σ).dshift.dinst r) ((Tm.ofList _).subst _ _) [] = _
        rw [dshift_dinst, ofList_subst, List.map_map]
        congr 3; funext t; exact isub_up_dinst t σ r hr
      rw [e1, e2] at h
      exact RE2.symm hW (hPRσ σ) h
    have hub : ∀ k3 (σ : ISub k3 k), (ival (idEnv k3) ((φ.subst γ.σ'.τ).subst σ.τ)).holds →
        RE2 S k3 (.data d ((γ.R ps).isub σ)) ((((γ.up hW).R u).isub σ.up).dinst .zero)
          ((Tm.con d c (γ.R qs) (Tm.ofList (args.toList.map γ.R)) []).isub σ) := by
      intro k3 σ hh
      have h := (hsV k3 ((cR.restr hW σ).cof (hfσ σ hh))).2
      change RE2 S k3 ((cR.restr hW σ).L (.data d ps)) ((cR.restr hW σ).L (u.dinst .zero))
        ((cR.restr hW σ).R (.con d c qs args [])) at h
      rw [CSub2.L_dinst hW, CSub2.up_restr_L, CSub2.restr_L, CSub2.restr_R] at h
      change RE2 S k3 ((Tm.data d (γ.R ps)).isub σ) ((((γ.up hW).R u).isub σ.up).dinst (I.zero.subst _))
        ((Tm.con d c (γ.R qs) (γ.R args) []).isub σ) at h
      rw [hXR, show (Tm.data d (γ.R ps)).isub σ = .data d ((γ.R ps).isub σ) from rfl] at h
      exact h
    have R := rel_hcompCon hW hD hH hPT hPP (ISub.id k) hC (u := (γ.up hW).R u) (qs := γ.R qs)
      (φ := φ.subst γ.σ'.τ) (X := args.toList.map γ.R) (Ys := uargs.toList.map (γ.up hW).R) hYl
      (by rw [e0]; exact hty) (by rw [e0]; exact hrr) (fun k2 κ => by rw [ISub.id_comp]; exact hYe k2 κ)
      (fun k3 σ r r' hr hr' hE hh => by rw [ISub.id_comp]; exact hYr k3 σ r r' hr hr' hE hh)
      (fun k3 σ hh => by rw [ISub.id_comp]; exact hub k3 σ hh) (by rw [e0]; exact hbb) (by rw [e0]; exact he)
    rw [e0] at R
    rw [eCon, eRedex]
    exact R
  have hX := hv.tyCode hW γ
  have k2 := htr k (γ.diagR hW) _ _ (RE2.symm hW (hAV.ty hW (γ.diagR hW)) key)
  exact RE2.trans hW (hv.tyLL hW γ) (hv k γ).2 (RE2.conv hW (RT2.symm hW hX (hv k γ).1) k2)

end valid

end

end Model.Whnf
