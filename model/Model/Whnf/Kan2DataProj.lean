import Model.Whnf.Kan2DataTube

/-!
# Projections out of related constructors

Arguments of judgmentally equal constructors of an inductive type without path constructors are
judgmentally equal (through the projections, `con_args_eq`), and the projections of a related
element are related to the arguments of its normal form (`proj_rel`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
include hW hD hH

/-- The arguments of judgmentally equal constructors are judgmentally equal. -/
theorem con_args_eq {Ψ : ℕ} {Φ : I} {q : Tm} (H : PD S Ψ Φ d D q) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    {Y Y' : List Tm}
    (hY : HasTele0 S Ψ Φ [] (Tm.ofList Y) (C.argTys d D.params.length) q.toList.reverse)
    (hY' : HasTele0 S Ψ Φ [] (Tm.ofList Y') (C.argTys d D.params.length) q.toList.reverse)
    (e : EqTm0 S Ψ Φ [] (.con d c q (Tm.ofList Y) []) (.con d c q (Tm.ofList Y') []) (.data d q))
    {j : ℕ} (hj : j < C.args.length) :
    EqTm0 S Ψ Φ [] (Y.getD j .abort) (Y'.getD j .abort)
      ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ q.toList.reverse)) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  obtain ⟨h1, h2, -⟩ := pre_eq hS hT hCt e
  have e1 := proj_con hS hW H hC hj H.hw hY
  have e2 := proj_con hS hW H hC hj H.hw hY'
  have e3 := proj_congr hS hW H hC hj e
  have eQ1 := projQ_con hS hW H hC hj H.hw hC hY
  have eQ2 := projQ_con hS hW H hC hj H.hw hC hY'
  rw [if_pos rfl] at eQ1 eQ2
  have eQ12 := HasTy0.inst_congr hS (projQ_typed hS hW H hC hj) h1 h2 e
  exact (EqTm0.symm e1).trans ((EqTm0.conv e3 eQ1).trans (EqTm0.conv e2
    ((EqTm0.symm eQ2).trans ((EqTm0.symm eQ12).trans eQ1))))

/-- Argument types at judgmentally equal prefixes and parameters are judgmentally equal. -/
theorem argTy_tyEq {p p' : Tm} (hpT : HasTy S k .one [] (.data d p) (.univ D.level))
    (hpT' : HasTy S k .one [] (.data d p') (.univ D.level)) (hpp : TyEq S k (.data d p) (.data d p'))
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {X Y : List Tm}
    (hX : HasTele0 S k .one [] (Tm.ofList X) (C.argTys d D.params.length) p.toList.reverse)
    (hYl : Y.length = X.length)
    (hXY : ∀ j (hj : j < X.length) (hj' : j < Y.length), EqTm0 S k .one [] Y[j] X[j]
      ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ p.toList.reverse)))
    {j : ℕ} (hj : j < Y.length) :
    TyEq S k ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ p'.toList.reverse))
      ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ p.toList.reverse)) := by
  have H := PD.of hW hD hH (spec_to_minimal hW hpT)
  have H' := PD.of hW hD hH (spec_to_minimal hW hpT')
  obtain ⟨hYt, -, eYX⟩ := tele_conv hW hD hC H.hpsL H.hpt H.hdata hX hYl hXY
  obtain ⟨l, epp⟩ := tyEq_eq hW hpp ⟨_, hpT'⟩
  obtain ⟨-, eR⟩ := args_retype hW hD hC H.hpsL H'.hpsL H.hpt H'.hpt (spec_to_minimal_eq hW epp) hYt
  obtain ⟨l', e2⟩ := eR j (by rw [toList_ofList]; exact hj)
  rw [toList_ofList] at e2
  exact (TyEq.symm (.inr ⟨l', minimal_to_spec_eq e2⟩)).trans hW (.inr ⟨_, minimal_to_spec_eq (eYX j hj)⟩)

end

/-- An argument type at a prefix and literal parameters, restricted. -/
theorem argTy_isub (hS : SigClosed S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) (j : ℕ) (L : List Tm) {p : Tm} (hp : p = Tm.ofList p.toList) (κ : ISub k' k) :
    ((C.argTy d D.params.length j).substList ((L.take j).reverse ++ p.toList.reverse)).isub κ =
      (C.argTy d D.params.length j).substList (((L.map (·.isub κ)).take j).reverse ++ (p.isub κ).toList.reverse) := by
  rw [substList_isub (argTy_closed hS hD hC j), List.map_append, List.map_reverse, List.map_reverse, List.map_take,
    toList_isub hp κ]


/-! ### The arguments of related elements of a literal inductive type -/

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hP hPP

/-- The arguments of a related pair of constructors in a literal inductive type, whose prefix is
related to itself, give related argument types. -/
theorem dataLit_argTy {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {Z Z' : List Tm}
    (hl : Z.length ≤ C.args.length) (hl' : Z'.length = Z.length)
    (hrec : ∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
        (.data d (P.isub ρ')) Z[i] Z'[i])
    (hpt : ∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k3 ρ'.hom c i ((Z.take i).map (semK S k3))
        ((C.argTy d (dataD S d).params.length i).substList ((Z.take i).reverse ++ (P.isub ρ').toList.reverse))
        Z[i] Z'[i])
    (hr : Z.length < C.args.length) (hrr : C.isRec Z.length = false) :
    (Comp2 S (tyLook (shapeV ((ΘK S D d K P).restr ((Hom.id K).comp ρ'.hom))) c Z.length (Z.map (semK S k3)))
      k3 k3 (Hom.id k3)).ty
      ((C.argTy d (dataD S d).params.length Z.length).substList (Z.reverse ++ (P.isub ρ').toList.reverse))
      ((C.argTy d (dataD S d).params.length Z.length).substList (Z.reverse ++ (P.isub ρ').toList.reverse)) := by
  have hdD := dataD_eq hW hD
  obtain ⟨-, -, hR, -, -, -, -⟩ := dataLit_rel hW hD hP hPP ρ'
  have hpc : (P.isub ρ').closedB 0 k3 = true := by
    have := closed_of_ty hW (HasTy.isubS hW hP ρ'); simpa [Tm.closedB] using this
  have hC' : (dataD S (ΘK S D d K P).idx).ctors[c]? = some C := by
    show (dataD S d).ctors[c]? = some C; rw [hdD]; exact hC
  obtain ⟨hrecd, hptd⟩ := prefix_refl hW (Hom.id K) (perP_ΘK hW hD hP) hR hpc hC' hl hl' hrec hpt
  exact argRelH_id (Hom.id K) hR hpc hpc hC' hr rfl hrr (fun i hi _ hri => hrecd i hi hri)
    (fun i hi _ hri => hptd i hi hri)

/-- Related point arguments, from their relation at the code of their type. -/
theorem dataP2_RE2 {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {Z Z' : List Tm}
    (hl : Z.length ≤ C.args.length) (hl' : Z'.length = Z.length)
    (hrec : ∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
        (.data d (P.isub ρ')) Z[i] Z'[i])
    (hpt : ∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k3 ρ'.hom c i ((Z.take i).map (semK S k3))
        ((C.argTy d (dataD S d).params.length i).substList ((Z.take i).reverse ++ (P.isub ρ').toList.reverse))
        Z[i] Z'[i])
    {j : ℕ} (hj : j < Z.length) (hj' : j < Z'.length) (hrj : C.isRec j = false) :
    RE2 S k3 ((C.argTy d (dataD S d).params.length j).substList ((Z.take j).reverse ++ (P.isub ρ').toList.reverse))
      Z[j] Z'[j] := by
  have hlj : (Z.take j).length = j := by simp; omega
  have hty := dataLit_argTy hW hD hH hP hPP ρ' hC (Z := Z.take j) (Z' := Z'.take j) (by simp; omega) (by simp; omega)
    (fun i hi hi' hri => by
      simp only [List.getElem_take]; exact hrec i (by simp at hi; omega) (by simp at hi'; omega) hri)
    (fun i hi hi' hri => by
      simp only [List.getElem_take, List.take_take]
      rw [Nat.min_eq_left (by simp at hi; omega)]
      exact hpt i (by simp at hi; omega) (by simp at hi'; omega) hri)
    (by rw [hlj]; omega) (by rw [hlj]; exact hrj)
  rw [hlj] at hty
  have x := hpt j hj hj' hrj
  unfold dataP2 at x
  have hb := Comp2_ty_base hty
  exact (Comp2_el_iff hb.1 hb.2.2.2.1).1 x

/-- The normal forms of related elements of a literal inductive type: constructors with related
arguments. -/
theorem dataLit_args {k3 : ℕ} (ρ' : ISub k3 K) {x x' : Tm} (hx : RE2 S k3 (.data d (P.isub ρ')) x x') :
    ∃ c C qs Z qs' Z', D.ctors[c]? = some C ∧ Z.length = C.args.length ∧ Z'.length = C.args.length ∧
      RedE S k3 (.data d (P.isub ρ')) x (.con d c qs (Tm.ofList Z) []) ∧
      RedE S k3 (.data d (P.isub ρ')) x' (.con d c qs' (Tm.ofList Z') []) ∧
      (∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = true →
        RE2 S k3 (.data d (P.isub ρ')) Z[i] Z'[i]) ∧
      (∀ i (hi : i < Z.length) (hi' : i < Z'.length), C.isRec i = false →
        RE2 S k3 ((C.argTy d D.params.length i).substList ((Z.take i).reverse ++ (P.isub ρ').toList.reverse))
          Z[i] Z'[i]) := by
  have hdD := dataD_eq hW hD
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP ρ').1 hx
  have hat := DR2.at_id hW (Θ := ΘK S D d K P) hdr
  cases hat with
  | con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    have hC' := hdD ▸ hC
    obtain rfl := redT_data_eq (Θ := ΘK S D d K P) hA
    have hrs0 := List.eq_nil_of_length_eq_zero (hrs.trans (nonHIT_ctor hH hC').1)
    have hrs0' := List.eq_nil_of_length_eq_zero (hrs'.trans (nonHIT_ctor hH hC').1)
    subst hrs0 hrs0'
    refine ⟨_, _, _, _, _, _, hC', hl, hl', ht, ht', fun i hi hi' hri => ?_, fun i hi hi' hri => ?_⟩
    · have h := hrec i hi hi' hri
      obtain ⟨he⟩ : Nonempty (EqTm S k3 .one [] _ _ (.data d (P.isub ρ'))) := by cases h with | intro he => exact ⟨he⟩
      exact (RE2_dataLit_iff hW hD hP ρ').2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, h⟩
    · have := dataP2_RE2 hW hD hH hP hPP ρ' hC' (by omega) (by omega) hrec hpt hi hi' hri
      rwa [hdD] at this
  | hcomp _ _ _ hH' =>
    have : D.isHIT = true := hdD ▸ hH'
    rw [hH] at this; cases this

/-- The normal form of a related element of a literal inductive type, restricted further, against
the normal form at the further restriction: constructors with related arguments. -/
theorem dataLit_coh {k3 : ℕ} (ρ' : ISub k3 K) {x x' : Tm} (hx : RE2 S k3 (.data d (P.isub ρ')) x x')
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs : Tm} {Z : List Tm}
    (hw : RedW S x (.con d c qs (Tm.ofList Z) [])) {k'' : ℕ} (κ : ISub k'' k3) :
    ∃ qs2 Z2, Z.length = C.args.length ∧ Z2.length = C.args.length ∧
      RedE S k'' (.data d (P.isub (ρ'.comp κ))) (x.isub κ) (.con d c qs2 (Tm.ofList Z2) []) ∧
      (∀ i (hi : i < Z.length) (hi' : i < Z2.length), C.isRec i = true →
        RE2 S k'' (.data d (P.isub (ρ'.comp κ))) (Z[i].isub κ) Z2[i]) ∧
      (∀ i (hi : i < Z.length) (hi' : i < Z2.length), C.isRec i = false →
        RE2 S k'' ((C.argTy d D.params.length i).substList
          (((Z.map (·.isub κ)).take i).reverse ++ (P.isub (ρ'.comp κ)).toList.reverse)) (Z[i].isub κ) Z2[i]) := by
  have hdD := dataD_eq hW hD
  have hxc := closed_of_ty hW (RE2.typed hx).1
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP ρ').1 hx
  cases hdr with
  | intro he hh hc hc' =>
    have h0 := hc k3 (ISub.id k3) _ (by rw [isub_id_of_closed hxc]; exact hw) k'' κ
    rw [ISub.id_comp, show (Tm.data d (P.isub ρ')).isub κ = .data d (P.isub (ρ'.comp κ)) by
      show Tm.data d ((P.isub ρ').isub κ) = _; rw [Tm.isub_isub],
      show (Tm.con d c qs (Tm.ofList Z) []).isub κ = .con d c (qs.isub κ) (Tm.ofList (Z.map (·.isub κ))) [] by
        show Tm.con d c (qs.isub κ) ((Tm.ofList Z).isub κ) [] = _; rw [ofList_isub],
      ← ISub.hom_comp] at h0
    cases h0 with
    | con hm hm' heq hC1 hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
      have e := RedW.unique ht.1 (redW_self (step_con_nonHIT hD hH hC _ _ _))
      simp only [Tm.con.injEq] at e
      obtain ⟨-, rfl, -, ea, rfl⟩ := e
      have ea' := congrArg Tm.toList ea
      simp only [toList_ofList] at ea'
      subst ea'
      obtain rfl := redT_data_eq (Θ := ΘK S D d K P) hA
      have hC1' := hdD ▸ hC1
      rw [hC] at hC1'; cases hC1'
      have hrs0' := List.eq_nil_of_length_eq_zero (hrs'.trans (nonHIT_ctor hH hC).1)
      subst hrs0'
      refine ⟨_, _, by simpa using hl, hl', ht', fun i hi hi' hri => ?_, fun i hi hi' hri => ?_⟩
      · have h := hrec i (by simpa using hi) hi' hri
        obtain ⟨he⟩ : Nonempty (EqTm S k'' .one [] _ _ (.data d (P.isub (ρ'.comp κ)))) := by
          cases h with | intro he => exact ⟨he⟩
        have := (RE2_dataLit_iff hW hD hP (ρ'.comp κ)).2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, h⟩
        simpa using this
      · have := dataP2_RE2 hW hD hH hP hPP (ρ'.comp κ) hC (le_of_eq hl) (hl'.trans hl.symm) hrec hpt
          (by simpa using hi) hi' hri
        rw [hdD] at this
        simpa using this
    | hcomp _ _ _ hH' =>
      have : D.isHIT = true := hdD ▸ hH'
      rw [hH] at this; cases this

/-- The argument types of the normal form of an element related to another are related to themselves. -/
theorem dataLit_tyRT2 {k3 : ℕ} (ρ' : ISub k3 K) {x x' : Tm} (hx : RE2 S k3 (.data d (P.isub ρ')) x x')
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs : Tm} {Z : List Tm}
    (hw : RedW S x (.con d c qs (Tm.ofList Z) [])) {j : ℕ} (hj : j < C.args.length) :
    RT2 S k3 ((C.argTy d D.params.length j).substList ((Z.take j).reverse ++ (P.isub ρ').toList.reverse))
      ((C.argTy d D.params.length j).substList ((Z.take j).reverse ++ (P.isub ρ').toList.reverse)) := by
  have hS := sigClosed_of_wfSig hW
  have hdD := dataD_eq hW hD
  have hpL := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP ρ').1 hx
  have hat := DR2.at_id hW (Θ := ΘK S D d K P) hdr
  cases hat with
  | con hm hm' heq hC1 hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    have e := RedW.unique ht.1 hw
    simp only [Tm.con.injEq] at e
    obtain ⟨-, rfl, -, ea, -⟩ := e
    have ea' := congrArg Tm.toList ea
    simp only [toList_ofList] at ea'
    have ea'' := ea'.symm
    subst ea''
    obtain rfl := redT_data_eq (Θ := ΘK S D d K P) hA
    have hC1' := hdD ▸ hC1
    rw [hC] at hC1'; cases hC1'
    have hTK : IsTyK S k3 (.data d (P.isub ρ')) := ⟨_, .inl (HasTy.isubS hW hP ρ')⟩
    have hlen := data_len_of hW hTK
    cases hrj : C.isRec j
    · have hlj : (Z.take j).length = j := by simp; omega
      have hty := dataLit_argTy hW hD hH hP hPP ρ' hC (Z := Z.take j) (Z' := Z.take j) (by simp; omega) rfl
        (fun i hi hi' hri => by
          have := (prefix_refl hW (Hom.id K) (perP_ΘK hW hD hP) (dataLit_rel hW hD hP hPP ρ').2.2.1
            (by have := closed_of_ty hW (HasTy.isubS hW hP ρ'); simpa [Tm.closedB] using this) hC1 (by omega)
            (by omega) hrec hpt).1 i (by simp at hi; omega) hri
          simpa using this)
        (fun i hi hi' hri => by
          have := (prefix_refl hW (Hom.id K) (perP_ΘK hW hD hP) (dataLit_rel hW hD hP hPP ρ').2.2.1
            (by have := closed_of_ty hW (HasTy.isubS hW hP ρ'); simpa [Tm.closedB] using this) hC1 (by omega)
            (by omega) hrec hpt).2 i (by simp at hi; omega) hri
          simp only [List.getElem_take, List.take_take]
          rw [Nat.min_eq_left (by simp at hi; omega)]
          exact this)
        (by rw [hlj]; omega) (by rw [hlj]; exact hrj)
      rw [hlj] at hty
      have := Comp2_ty_RT2 hty
      rwa [hdD] at this
    · rw [argTy_rec_inst hrj hpL (by rw [hdD] at hlen; exact hlen) (by simp; omega)]
      have := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
      exact this
  | hcomp _ _ _ hH' =>
    have : D.isHIT = true := hdD ▸ hH'
    rw [hH] at this; cases this

/-- The projections of a related element of a literal inductive type are related to the
arguments of its normal form. -/
theorem proj_rel {k3 : ℕ} (ρ' : ISub k3 K) {x x' : Tm} (hx : RE2 S k3 (.data d (P.isub ρ')) x x')
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs : Tm} {Z : List Tm}
    (hw : RedW S x (.con d c qs (Tm.ofList Z) [])) {q1 : Tm} (hq1 : TyEq S k3 (.data d (P.isub ρ')) (.data d q1))
    (hq1T : HasTy S k3 .one [] (.data d q1) (.univ D.level)) {j : ℕ} (hj : j < C.args.length) :
    RE2 S k3 ((C.argTy d D.params.length j).substList ((Z.take j).reverse ++ (P.isub ρ').toList.reverse))
      (proj d D q1 c C j x) (Z.getD j .abort) := by
  have hS := sigClosed_of_wfSig hW
  have hTT := dataLit_tyRT2 hW hD hH hP hPP ρ' hx hC hw hj
  have hpT : HasTy S k3 .one [] (.data d (P.isub ρ')) (.univ D.level) := HasTy.isubS hW hP ρ'
  have hxe : EqTm S k3 .one [] x (.con d c qs (Tm.ofList Z) []) (.data d (P.isub ρ')) := by
    obtain ⟨c', C', qs', Z0, -, -, -, -, -, h1, -, -, -⟩ := dataLit_args hW hD hH hP hPP ρ' hx
    have e := RedW.unique h1.1 hw
    rw [e] at h1
    exact h1.2
  -- the projection, against the argument
  have pc := fun {k5 : ℕ} {y q Zy : Tm} {L : List Tm} (hq : TyEq S k5 (.data d Zy) (.data d q))
      (hqT : HasTy S k5 .one [] (.data d q) (.univ D.level)) (hZyT : HasTy S k5 .one [] (.data d Zy) (.univ D.level))
      {qy : Tm} (hye : EqTm S k5 .one [] y (.con d c qy (Tm.ofList L) []) (.data d Zy)) =>
    (show HasTele0 S k5 .one [] (Tm.ofList L) (C.argTys d D.params.length) q.toList.reverse ∧
      EqTm0 S k5 .one [] (proj d D q c C j y) (L.getD j .abort)
        ((C.argTy d D.params.length j).substList ((L.take j).reverse ++ q.toList.reverse)) from by
      obtain ⟨hLt, he, -, -⟩ := con_retype hW hD hH hC hye hq hqT
      exact ⟨hLt, proj_canon hS hW (PD.of hW hD hH (spec_to_minimal hW hqT)) hC hLt (spec_to_minimal_eq hW he) hj⟩)
  obtain ⟨hZq, e0⟩ := pc hq1 hq1T hpT hxe
  obtain ⟨hZp, -, -, hZl⟩ := con_retype hW hD hH hC hxe (TyEq.refl _) hpT
  have eT : TyEq S k3 ((C.argTy d D.params.length j).substList ((Z.take j).reverse ++ q1.toList.reverse))
      ((C.argTy d D.params.length j).substList ((Z.take j).reverse ++ (P.isub ρ').toList.reverse)) :=
    argTy_tyEq hW hD hH hpT hq1T hq1 hC hZp rfl (fun i hi _ => by
      have := tele_get hZp i Z[i] _ (by rw [toList_ofList]; exact List.getElem?_eq_getElem hi)
        (argTys_get (by omega))
      rw [toList_ofList] at this
      exact EqTm0.refl this) (by omega)
  have e1 := (minimal_to_spec_eq e0).tyConv eT
  refine RE2.expandH hW hTT (HasTy.eqL e1) (HasTy.eqR e1) fun k'' κ => ?_
  obtain ⟨qs2, Z2, -, hZ2l, ht2, hrec2, hpt2⟩ := dataLit_coh hW hD hH hP hPP ρ' hx hC hw κ
  have H1 := PD.of hW hD hH (spec_to_minimal hW hq1T)
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have eP : (Tm.data d (P.isub ρ')).isub κ = .data d (P.isub (ρ'.comp κ)) := by
    show Tm.data d ((P.isub ρ').isub κ) = _; rw [Tm.isub_isub]
  have hTj : ((C.argTy d D.params.length j).substList ((Z.take j).reverse ++ (P.isub ρ').toList.reverse)).isub κ =
      (C.argTy d D.params.length j).substList (((Z.map (·.isub κ)).take j).reverse ++
        (P.isub (ρ'.comp κ)).toList.reverse) := by
    rw [argTy_isub hS hD hC j Z hPl κ, Tm.isub_isub]
  have hpκT : HasTy S k'' .one [] (.data d (P.isub (ρ'.comp κ))) (.univ D.level) := by
    have := HasTy.isubS hW hpT κ; rwa [eP] at this
  have hq1κ : TyEq S k'' (.data d (P.isub (ρ'.comp κ))) (.data d (q1.isub κ)) := by
    have := hq1.isub hW κ; rwa [eP] at this
  have hq1κT : HasTy S k'' .one [] (.data d (q1.isub κ)) (.univ D.level) := HasTy.isubS hW hq1T κ
  obtain ⟨-, e2⟩ := pc hq1κ hq1κT hpκT ht2.2
  have hxκ : EqTm S k'' .one [] (x.isub κ) (.con d c (qs.isub κ) (Tm.ofList (Z.map (·.isub κ))) [])
      (.data d (P.isub (ρ'.comp κ))) := by
    have := EqTm.isubS hW hxe κ
    rw [eP, show (Tm.con d c qs (Tm.ofList Z) []).isub κ = .con d c (qs.isub κ) (Tm.ofList (Z.map (·.isub κ))) [] by
      show Tm.con d c (qs.isub κ) ((Tm.ofList Z).isub κ) [] = _; rw [ofList_isub]] at this
    exact this
  obtain ⟨hZκ, -, -, -⟩ := con_retype hW hD hH hC hxκ (TyEq.refl _) hpκT
  have hPlκ := (dataLit_rel hW hD hP hPP (ρ'.comp κ)).2.2.2.2.2.1
  have hplκ : (P.isub (ρ'.comp κ)).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hpκT⟩ : IsTyK S k'' (.data d (P.isub (ρ'.comp κ))))
    rwa [dataD_eq hW hD] at this
  have hZ2Z : ∀ i (hi : i < (Z.map (·.isub κ)).length) (hi' : i < Z2.length), EqTm0 S k'' .one [] Z2[i]
      (Z.map (·.isub κ))[i] ((C.argTy d D.params.length i).substList
        (((Z.map (·.isub κ)).take i).reverse ++ (P.isub (ρ'.comp κ)).toList.reverse)) := by
    intro i hi hi'
    have hi0 : i < Z.length := by simpa using hi
    cases hri : C.isRec i
    · have := (RE2.typed (hpt2 i hi0 hi' hri)).2.2
      simpa using spec_to_minimal_eq hW this.symm
    · have := (RE2.typed (hrec2 i hi0 hi' hri)).2.2
      rw [argTy_rec_inst hri hPlκ hplκ (by simp; omega)]
      simpa using spec_to_minimal_eq hW this.symm
  have eT2 := argTy_tyEq hW hD hH hpκT hq1κT hq1κ hC hZκ (by simp; omega) hZ2Z (j := j) (by omega)
  refine ⟨Z2.getD j .abort, ?_, ?_, ?_⟩
  · rw [show (proj d D q1 c C j x).isub κ = proj d D (q1.isub κ) c C j (x.isub κ) from
      proj_dsubst hS hD hC hj H1.hpsL H1.hpl κ.τ x]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact red_proj hD hH hC hZ2l ht2.1.1 hj
  · rw [show (proj d D q1 c C j x).isub κ = proj d D (q1.isub κ) c C j (x.isub κ) from
      proj_dsubst hS hD hC hj H1.hpsL H1.hpl κ.τ x, hTj]
    exact (minimal_to_spec_eq e2).tyConv eT2
  · rw [hTj]
    have hTTκ := RT2.isub hW (tyCode_of_ty hW (HasTy.eqL e1)) hTT κ
    rw [hTj] at hTTκ
    have hj0 : j < Z.length := by omega
    have hj2 : j < Z2.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj0]
    simp only [Option.getD_some]
    cases hrj : C.isRec j
    · have := hpt2 j hj0 hj2 hrj
      exact RE2.symm hW hTTκ this
    · have := hrec2 j hj0 hj2 hrj
      rw [argTy_rec_inst hrj hPlκ hplκ (by simp; omega)] at hTTκ ⊢
      exact RE2.symm hW hTTκ this

end lit

end

end Model.Whnf
