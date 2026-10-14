import Model.Whnf.Kan2DataProj

/-!
# Constructors related to elements of a literal inductive type

Building the relation of a constructor (a stable weak-head normal form, in an inductive type without
path constructors) to an element: at one stage from its arguments (`DR2At_con_of`), and at all
stages (`RE2_conW`). Where the face of a composition holds, its `hcompCon` contractum is related to
the tube's end (`face_con`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-- A heterogeneous composition whose face holds reduces to its tube's end. -/
theorem red_comp_face {C u u0 : Tm} {ψ : I} (h : I.Entails .one ψ) :
    Red S (Tm.comp C ψ u u0) (u.dinst .one) := by
  rw [comp_eq]
  refine .step (step_hcomp_face h) (.step ?_ (.refl _))
  show step S (Tm.transp _ ((I.var 0).subst (I.inst0 .one)) _) = _
  exact step_transp_face (show I.Entails .one I.one from ent_refl _)


section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hP hPP

omit hH hPP in
theorem dataMem_lit {k3 : ℕ} (ρ' : ISub k3 K) {t : Tm} (ht : HasTy S k3 .one [] t (.data d (P.isub ρ'))) :
    dataMem S (ΘK S D d K P) (Hom.id K) k3 ρ'.hom t := by
  have := dataMem_of_ty hW (f := ρ'.hom) (semK_dataLit hW hD hP ρ') ht
  unfold dataMem at this ⊢
  rwa [Hom.id_comp, ← Hom.comp_id ρ'.hom]

/-- The argument clause of a literal inductive type at a restriction, for its own parameters. -/
theorem argRelH_lit {k3 : ℕ} (ρ' : ISub k3 K) :
    ∀ ps, RedT S k3 (.data d (P.isub ρ')) (.data d ps) →
      argRelH (ΘK S D d K P) (Hom.id K) S k3 ρ'.hom ps ps := by
  intro ps h
  obtain rfl := redT_data_eq (Θ := ΘK S D d K P) h
  exact (dataLit_rel hW hD hP hPP ρ').2.2.1

/-- The argument types at related argument prefixes of a literal inductive type are related. -/
theorem dataLit_argTy2 {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {Z Z' : List Tm}
    (hl' : Z'.length = Z.length)
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
      ((C.argTy d (dataD S d).params.length Z.length).substList (Z'.reverse ++ (P.isub ρ').toList.reverse)) := by
  have hdD := dataD_eq hW hD
  obtain ⟨-, -, hR, -, -, -, -⟩ := dataLit_rel hW hD hP hPP ρ'
  have hpc : (P.isub ρ').closedB 0 k3 = true := by
    have := closed_of_ty hW (HasTy.isubS hW hP ρ'); simpa [Tm.closedB] using this
  have hC' : (dataD S (ΘK S D d K P).idx).ctors[c]? = some C := by
    show (dataD S d).ctors[c]? = some C; rw [hdD]; exact hC
  exact argRelH_id (Hom.id K) hR hpc hpc hC' hr hl' hrr hrec hpt

/-- A constructor, related at one stage to an element whose normal form is the same constructor, from
the relations of their arguments. -/
theorem DR2At_con_of {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q qs' t : Tm}
    {Y Z : List Tm} (hYl : Y.length = C.args.length) (hZl : Z.length = C.args.length)
    (hcT : HasTy S k3 .one [] (.con d c q (Tm.ofList Y) []) (.data d (P.isub ρ')))
    (ht : RedE S k3 (.data d (P.isub ρ')) t (.con d c qs' (Tm.ofList Z) []))
    (he : EqTm S k3 .one [] (.con d c q (Tm.ofList Y) []) t (.data d (P.isub ρ')))
    (hargs : ∀ i (hi : i < Y.length) (hi' : i < Z.length),
      (C.isRec i = true → RE2 S k3 (.data d (P.isub ρ')) Y[i] Z[i]) ∧
      (C.isRec i = false →
        RT2 S k3 ((C.argTy d D.params.length i).substList ((Y.take i).reverse ++ (P.isub ρ').toList.reverse))
          ((C.argTy d D.params.length i).substList ((Z.take i).reverse ++ (P.isub ρ').toList.reverse)) →
        RE2 S k3 ((C.argTy d D.params.length i).substList ((Y.take i).reverse ++ (P.isub ρ').toList.reverse))
          Y[i] Z[i])) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
      (.data d (P.isub ρ')) (.con d c q (Tm.ofList Y) []) t := by
  have hdD := dataD_eq hW hD
  have hC' : (dataD S d).ctors[c]? = some C := by rw [hdD]; exact hC
  have hpl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  -- the relations of the arguments, by induction along them
  let Good : ℕ → Prop := fun j =>
    (∀ i (hi : i < Y.length) (hi' : i < Z.length), i < j → C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
        (.data d (P.isub ρ')) Y[i] Z[i]) ∧
    (∀ i (hi : i < Y.length) (hi' : i < Z.length), i < j → C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k3 ρ'.hom c i ((Y.take i).map (semK S k3))
        ((C.argTy d (dataD S d).params.length i).substList ((Y.take i).reverse ++ (P.isub ρ').toList.reverse))
        Y[i] Z[i])
  have key : ∀ j, j ≤ C.args.length → Good j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun i _ _ h => absurd h (Nat.not_lt_zero _), fun i _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      obtain ⟨g1, g2⟩ := ih (by omega)
      have hjY : j < Y.length := by omega
      have hjZ : j < Z.length := by omega
      refine ⟨fun i hi hi' hij hri => ?_, fun i hi hi' hij hri => ?_⟩
      · by_cases hlt : i < j
        · exact g1 i hi hi' hlt hri
        obtain rfl : i = j := by omega
        exact ((RE2_dataLit_iff hW hD hP ρ').1 ((hargs i hi hi').1 hri)).2
      · by_cases hlt : i < j
        · exact g2 i hi hi' hlt hri
        obtain rfl : i = j := by omega
        have hli : (Y.take i).length = i := by simp; omega
        have hty := dataLit_argTy2 hW hD hH hP hPP ρ' hC (Z := Y.take i) (Z' := Z.take i)
          (by simp; omega)
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take]; exact g1 i' (by simp at h1; omega) (by simp at h2; omega)
              (by simp at h1; omega) hri')
          (fun i' h1 h2 hri' => by
            simp only [List.getElem_take, List.take_take]
            rw [Nat.min_eq_left (by simp at h1; omega)]
            exact g2 i' (by simp at h1; omega) (by simp at h2; omega) (by simp at h1; omega) hri')
          (by rw [hli]; omega) (by rw [hli]; exact hri)
        rw [hli] at hty
        have hRT := Comp2_ty_RT2 hty
        rw [hdD] at hRT
        have hre := (hargs i hi hi').2 hri (by simpa using hRT)
        have hb := Comp2_ty_base hty
        unfold dataP2
        rw [hdD]
        rw [hdD] at hb
        exact (Comp2_el_iff hb.1 hb.2.2.2.1).2 (by simpa using hre)
  obtain ⟨g1, g2⟩ := key C.args.length (Nat.le_refl _)
  refine .con (dataMem_lit hW hD hP ρ' hcT) (dataMem_lit hW hD hP ρ' (HasTy.eqR he)) he hC'
    ⟨redW_self (step_data d _), TyEq.refl _⟩ hpl ⟨redW_self (step_con_nonHIT hD hH hC _ _ _), EqTm.refl hcT⟩ ht
    (by simp [(nonHIT_ctor hH hC).1]) (by simp [(nonHIT_ctor hH hC).1]) (fun _ _ _ h => by simp at h) (by simp)
    (by simp) hYl hZl (fun i hi hi' hri => g1 i hi hi' (by omega) hri) (fun i hi hi' hri => g2 i hi hi' (by omega) hri)

/-- A constructor related to an element at every stage is related to it. -/
theorem RE2_conW {k3 : ℕ} (ρ' : ISub k3 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q t : Tm} {Y : List Tm}
    (hcT : HasTy S k3 .one [] (.con d c q (Tm.ofList Y) []) (.data d (P.isub ρ')))
    (htt : RE2 S k3 (.data d (P.isub ρ')) t t)
    (he : EqTm S k3 .one [] (.con d c q (Tm.ofList Y) []) t (.data d (P.isub ρ')))
    (hat : ∀ k'' (κ : ISub k'' k3), DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k'' (ρ'.comp κ).hom (.data d (P.isub (ρ'.comp κ)))
      ((Tm.con d c q (Tm.ofList Y) []).isub κ) (t.isub κ)) :
    RE2 S k3 (.data d (P.isub ρ')) (.con d c q (Tm.ofList Y) []) t := by
  have eP : ∀ {k4 : ℕ} (κ : ISub k4 k3), (Tm.data d (P.isub ρ')).isub κ = .data d (P.isub (ρ'.comp κ)) := by
    intro k4 κ; show Tm.data d ((P.isub ρ').isub κ) = _; rw [Tm.isub_isub]
  obtain ⟨-, hdt⟩ := (RE2_dataLit_iff hW hD hP ρ').1 htt
  refine (RE2_dataLit_iff hW hD hP ρ').2 ⟨⟨hcT, HasTy.eqR he, he⟩, .intro he (fun k'' κ => ?_)
    (fun k' σ w hw k'' κ => ?_) ?_⟩
  · rw [eP, ← ISub.hom_comp]; exact hat k'' κ
  · have e1 : (Tm.con d c q (Tm.ofList Y) []).isub σ = .con d c (q.isub σ) (Tm.ofList (Y.map (·.isub σ))) [] := by
      show Tm.con d c (q.isub σ) ((Tm.ofList Y).isub σ) [] = _; rw [ofList_isub]
    have hw' := RedW.unique hw (by rw [e1]; exact redW_self (step_con_nonHIT hD hH hC _ _ _))
    rw [hw', ← e1, Tm.isub_isub, eP, ← ISub.hom_comp]
    have h := hat k'' (σ.comp κ)
    have hy := argRelH_lit hW hD hH hP hPP (ρ'.comp (σ.comp κ))
    have := DR2At_trans hW (Hom.id K) (perP_ΘK hW hD hP) h (DR2At_symm hW (Hom.id K) (perP_ΘK hW hD hP) h hy) hy
    rwa [← ISub.comp_assoc] at this ⊢
  · cases hdt with
    | intro _ _ _ hc' => exact hc'

section face
variable {Q : Tm} (hQ : RT2 S K (.data d P) (.data d Q))
include hQ

/-- Where the face of a composition holds, its `hcompCon` contractum is related to the tube's end. -/
theorem face_con {k1 : ℕ} (ρ : ISub k1 K) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs u : Tm}
    {X : List Tm} {φ : I} (hf : I.Entails .one φ)
    (hty : HasTy S k1 .one [] (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ)))
    (htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u) :
    RE2 S k1 (.data d (P.isub ρ)) (.con d c (Q.isub ρ) (Tm.ofList ((List.range C.args.length).map
      (Meta.hOut C (C.argTy d D.params.length) (.data d (Q.isub ρ)) (Q.isub ρ).dshift.toList φ
        ((List.range C.args.length).map fun j => proj d D (Q.isub ρ).dshift c C j u) X))) []) (u.dinst .one) := by
  have hS := sigClosed_of_wfSig hW
  set q := Q.isub ρ with hq
  set p := P.isub ρ with hp
  set Ac := C.argTy d D.params.length with hAc
  set us := (List.range C.args.length).map fun j => proj d D q.dshift c C j u with hus
  set Y := (List.range C.args.length).map (Meta.hOut C Ac (.data d q) q.dshift.toList φ us X) with hY
  -- typing
  obtain ⟨l0, ⟨hdq, hφs, hut, hb, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨D', hD', hqt⟩ := gen_data_tele hdq rfl
  rw [hD] at hD'; cases hD'
  have hqT : HasTy S k1 .one [] (.data d q) (.univ D.level) := minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hqt)
  have hpT : HasTy S k1 .one [] (.data d p) (.univ D.level) := HasTy.isubS hW hP ρ
  have hTPQ : TyEq S k1 (.data d p) (.data d q) := (Comp2_ty_base (RT2.isub hW (tyCode_of_univ hW hP) hQ ρ)).2.2.2.2.2
  have hcan := tubeCanon_of hW hD hH hP ρ hTPQ hqT htube
  have e_hc := hcompCon_sound hW hD hH hC hty hcan
  have e_face := EqTm.hcompFace hf hty
  obtain ⟨hXq, -, -, hXl⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb)) (TyEq.refl _) hqT
  have hul : us.length = C.args.length := by simp [us]
  have heqT := Meta.hcompTele_eq C Ac (.data d q) q.dshift.toList φ us X us X 0 rfl rfl (by rw [hul, hXl])
  simp only [hXl, ← List.range_eq_range'] at heqT
  rw [show ([] : List Tm) = (Meta.hFills C Ac (.data d q) q.dshift.toList φ us X 0).reverse from rfl, heqT] at e_hc
  have he : EqTm S k1 .one [] (.con d c q (Tm.ofList Y) []) (u.dinst .one) (.data d p) := e_hc.symm.trans e_face
  have hcT := HasTy.eqL he
  -- the face at every restriction
  have hfσ : ∀ {k4 : ℕ} (σ : ISub k4 k1), I.Entails .one (φ.subst σ.τ) := fun σ => by
    have := ent_subst hf σ.τ; simpa [I.subst] using this
  have hholds : ∀ {k4 : ℕ} (σ : ISub k4 k1), (ival (idEnv k4) (φ.subst σ.τ)).holds := fun σ =>
    (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 (hfσ σ)
  have huc : u.closedB 0 (k1 + 1) = true := closed_ty hut
  have hpc : (Tm.data d p).closedB 0 k1 = true := closed_of_ty hW hpT
  have hu1 := htube k1 (ISub.id k1) .one .one trivial trivial (I_eq_refl _) (hholds _)
  rw [isub_id_of_closed hpc, isub_up_id_of_closed huc] at hu1
  have H1 := PD.of hW hD hH (HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal hW hqT))
  refine RE2_conW hW hD hH hP hPP ρ hC hcT hu1 he fun k'' κ => ?_
  have eP : ∀ {k4 : ℕ} (σ : ISub k4 k1), (Tm.data d p).isub σ = .data d (P.isub (ρ.comp σ)) := by
    intro k4 σ; show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]
  have hu1κ := htube k'' κ .one .one trivial trivial (I_eq_refl _) (hholds κ)
  rw [eP] at hu1κ
  have eu1 : (u.dinst .one).isub κ = (u.isub κ.up).dinst .one := by rw [isub_dinst]; rfl
  rw [eu1]
  obtain ⟨c', C', qs', Z, -, -, hC', hZl, -, ht1, -, -, -⟩ := dataLit_args hW hD hH hP hPP (ρ.comp κ) hu1κ
  have ecκ : (Tm.con d c q (Tm.ofList Y) []).isub κ = .con d c (q.isub κ) (Tm.ofList (Y.map (·.isub κ))) [] := by
    show Tm.con d c (q.isub κ) ((Tm.ofList Y).isub κ) [] = _; rw [ofList_isub]
  have heκ := EqTm.isubS hW he κ
  rw [ecκ, eP, eu1] at heκ
  have hpκT : HasTy S k'' .one [] (.data d (P.isub (ρ.comp κ))) (.univ D.level) := HasTy.isubS hW hP (ρ.comp κ)
  have hqκT : HasTy S k'' .one [] (.data d (q.isub κ)) (.univ D.level) := HasTy.isubS hW hqT κ
  have hTκ : TyEq S k'' (.data d (P.isub (ρ.comp κ))) (.data d (q.isub κ)) := by
    have := hTPQ.isub hW κ; rwa [eP] at this
  -- the tube's end at `κ` is the constructor `c`
  obtain ⟨hZt, eZ, -, -⟩ := con_retype hW hD hH hC' ht1.2 (TyEq.refl _) hpκT
  have hcc : c = c' := con_tag hW hD hC hC' (nonHIT_ctor hH hC).2 (nonHIT_ctor hH hC').2 hqκT hpκT
    ((HasTy.eqL heκ).tyConv hTκ) (HasTy.eqR eZ) (heκ.trans eZ)
  subst hcc
  rw [hC] at hC'; cases hC'
  have hcTκ := HasTy.eqL heκ
  have hYl : (Y.map (·.isub κ)).length = C.args.length := by simp [Y]
  have hYlen : Y.length = C.args.length := by simp [Y]
  rw [ecκ]
  -- typing of the arguments
  obtain ⟨hYt, -, -, -⟩ := con_retype hW hD hH hC (EqTm.refl hcTκ) (TyEq.refl _) hpκT
  have hYi : ∀ i (hi : i < (Y.map (·.isub κ)).length), HasTy S k'' .one [] (Y.map (·.isub κ))[i]
      ((C.argTy d D.params.length i).substList (((Y.map (·.isub κ)).take i).reverse ++
        (P.isub (ρ.comp κ)).toList.reverse)) := by
    intro i hi
    have := tele_get hYt i _ _ (by rw [toList_ofList]; exact List.getElem?_eq_getElem hi)
      (argTys_get (by rw [hYl] at hi; exact hi))
    rw [toList_ofList] at this; exact minimal_to_spec this
  have hZi : ∀ i (hi : i < Z.length), HasTy S k'' .one [] Z[i]
      ((C.argTy d D.params.length i).substList ((Z.take i).reverse ++ (P.isub (ρ.comp κ)).toList.reverse)) := by
    intro i hi
    have := tele_get hZt i _ _ (by rw [toList_ofList]; exact List.getElem?_eq_getElem hi) (argTys_get (by omega))
    rw [toList_ofList] at this; exact minimal_to_spec this
  have hPLκ := (dataLit_rel hW hD hP hPP (ρ.comp κ)).2.2.2.2.2.1
  have hplκ : (P.isub (ρ.comp κ)).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hpκT⟩ : IsTyK S k'' (.data d (P.isub (ρ.comp κ))))
    rwa [dataD_eq hW hD] at this
  have Hκ := PD.of hW hD hH (spec_to_minimal hW hqκT)
  -- the projections of the tube's end, against its arguments
  have pr := fun {i : ℕ} (hi : i < C.args.length) =>
    proj_rel hW hD hH hP hPP (ρ.comp κ) hu1κ hC ht1.1 hTκ hqκT (j := i) hi
  have prσ : ∀ {i : ℕ} (hi : i < C.args.length) {k3 : ℕ} (κ' : ISub k3 k''),
      (proj d D (q.isub κ) c C i ((u.isub κ.up).dinst .one)).isub κ' =
        proj d D (q.isub (κ.comp κ')) c C i ((u.isub (κ.comp κ').up).dinst .one) := by
    intro i hi k3 κ'
    rw [show (proj d D (q.isub κ) c C i ((u.isub κ.up).dinst .one)).isub κ' =
      proj d D ((q.isub κ).isub κ') c C i (((u.isub κ.up).dinst .one).isub κ') from
      proj_dsubst hS hD hC hi Hκ.hpsL Hκ.hpl κ'.τ _]
    have e1 : ((u.isub κ.up).dinst .one).isub κ' = (u.isub (κ.comp κ').up).dinst .one := by
      rw [isub_dinst, Tm.isub_isub, ← ISub.up_comp]; rfl
    rw [e1, Tm.isub_isub]
  have tubeσ : ∀ {i : ℕ} (hi : i < C.args.length) {k3 : ℕ} (σ : ISub k3 k1),
      ((proj d D q.dshift c C i u).isub σ.up).dinst .one = proj d D (q.isub σ) c C i ((u.isub σ.up).dinst .one) := by
    intro i hi k3 σ
    rw [isub_up_dinst _ σ .one trivial]
    exact proj_tube_isub hW hD hC hi H1.hpsL H1.hpl σ (r := .one) trivial
  have hYget : ∀ i (hi : i < (Y.map (·.isub κ)).length), (Y.map (·.isub κ))[i] =
      (Meta.hOut C Ac (.data d q) q.dshift.toList φ us X i).isub κ := by
    intro i hi; simp [Y]
  have husi : ∀ i, i < C.args.length → us.getD i .abort = proj d D q.dshift c C i u := by
    intro i hi; simp [us, List.getD_eq_getElem?_getD, hi]
  refine DR2At_con_of hW hD hH hP hPP (ρ.comp κ) hC hYl hZl hcTκ ht1 heκ fun i hi hi' => ⟨fun hri => ?_, fun hri hRT => ?_⟩
  · -- a recursive argument: a composition whose face holds
    have hiC : i < C.args.length := by rw [hYl] at hi; exact hi
    have hRTP := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp κ)
    have tyY := hYi i hi
    rw [argTy_rec_inst hri hPLκ hplκ (by simp; omega)] at tyY
    have tyZ := hZi i hi'
    rw [argTy_rec_inst hri hPLκ hplκ (by simp; omega)] at tyZ
    refine RE2.expandH hW hRTP tyY tyZ fun k3 κ' => ?_
    have eY : ((Y.map (fun x : Tm => x.isub κ))[i]'hi).isub κ' = Tm.hcomp (.data d (q.isub (κ.comp κ'))) (φ.subst (κ.comp κ').τ)
        ((proj d D q.dshift c C i u).isub (κ.comp κ').up) ((X.getD i .abort).isub (κ.comp κ')) := by
      rw [hYget i hi, Tm.isub_isub]
      simp only [Meta.hOut, hri, if_true]
      rw [husi i hiC]; rfl
    have tyYσ := HasTy.isubS hW tyY κ'
    rw [eY] at tyYσ ⊢
    refine ⟨_, .step (step_hcomp_face (hfσ _)) (.refl _), EqTm.hcompFace (hfσ _) tyYσ, ?_⟩
    rw [tubeσ hiC, ← prσ hiC]
    have := RE2.isub hW (pr hiC) κ'
    rw [argTy_rec_inst hri hPLκ hplκ (by simp; omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] at this
    exact this
  · -- a point argument: a heterogeneous composition whose face holds
    have hiC : i < C.args.length := by rw [hYl] at hi; exact hi
    have tyY := hYi i hi
    have hXA : TyCode k'' (semK S k'' ((C.argTy d D.params.length i).substList
        (((Y.map (·.isub κ)).take i).reverse ++ (P.isub (ρ.comp κ)).toList.reverse))) := tyCode_of_ty hW tyY
    have hAA := RT2.refl hW hXA hRT
    have tyZ := (hZi i hi').tyConv (Comp2_ty_base (RT2.symm hW hXA hRT)).2.2.2.2.2
    refine RE2.expandH hW hAA tyY tyZ fun k3 κ' => ?_
    have eY : ((Y.map (fun x : Tm => x.isub κ))[i]'hi).isub κ' = Tm.comp
        ((Meta.hLine C Ac (.data d q) q.dshift.toList φ us X i).isub (κ.comp κ').up) (φ.subst (κ.comp κ').τ)
        ((proj d D q.dshift c C i u).isub (κ.comp κ').up) ((X.getD i .abort).isub (κ.comp κ')) := by
      rw [hYget i hi, Tm.isub_isub]
      simp only [Meta.hOut, hri, Bool.false_eq_true, if_false]
      rw [husi i hiC, comp_isub]
    have tyYσ := HasTy.isubS hW tyY κ'
    rw [eY] at tyYσ ⊢
    refine ⟨_, red_comp_face (hfσ _), minimal_to_spec_eq (comp_face hS (spec_to_minimal hW tyYσ) (hfσ _)), ?_⟩
    rw [tubeσ hiC, ← prσ hiC]
    have h1 := RE2.isub hW (pr hiC) κ'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'] at h1
    have hXB : TyCode k'' (semK S k'' ((C.argTy d D.params.length i).substList
        ((Z.take i).reverse ++ (P.isub (ρ.comp κ)).toList.reverse))) := RT2.tyCode_r hW hRT hXA
    exact RE2.conv hW (RT2.isub hW hXB (RT2.symm hW hXA hRT) κ') h1

end face

end lit

end

end Model.Whnf
