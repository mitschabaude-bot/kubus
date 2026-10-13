import Model.Canon.KanData

/-!
# Canonicity: transport of constructors (`transpCon`)

The arguments are transported along their argument types (instantiated at the parameter line and
the fillers of the earlier arguments); these lines are computable types by the computability of
the inductive type's line, given valid earlier arguments, and Kan by the induction on codes.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem ival_ieq {n : ℕ} (ρ : IEnv n) {r r' : I} (h : I.Eq r r') : ival ρ r = ival ρ r' := by
  ext p; exact h _

theorem ISub.hom_ieq {σ1 σ2 : ISub k' k} (h : ∀ i < k, I.Eq (σ1.τ i) (σ2.τ i)) : σ1.hom = σ2.hom := by
  funext j; exact ival_ieq _ (h _ (by omega))

variable (hW : WfSig S)
include hW

/-- The types of a point argument along `transpCon`: at the start of the line, the type of the
argument; at its end, the type of the transported argument. -/
theorem transpCon_pt_types {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} (hD : S[d]? = some (.data D))
    (hC : D.ctors[c]? = some C) {P' : Tm} {ψ : I} {as : List Tm} {l0 : ℕ}
    (hps : P' = Tm.ofList P'.toList)
    (htele : HasTele0 S k .one [] (Tm.ofList as) (C.argTys d D.params.length) (P'.dinst .zero).toList.reverse)
    (hL : HasTy0 S (k + 1) .one [] (.data d P') (.univ l0)) (hψ : ψ.Scoped k)
    (hc : EqTm0 S (k + 1) (cof .one ψ).shift [] (.data d P') ((Tm.data d P').dinst .zero).dshift (.univ l0))
    {j : ℕ} {A0 : Tm} (hA0 : C.args[j]? = some (.point A0)) :
    let Ac := C.argTy d D.params.length
    let Fall := Meta.tFills Ac P'.toList ψ as C.args.length
    let outs := (List.range C.args.length).map fun j => Tm.transp (Meta.tLine Ac P'.toList ψ as j) ψ (as.getD j .abort)
    EqTm S k .one [] ((Meta.tLine Ac P'.toList ψ as j).dinst .zero)
        (A0.substList ((as.take j).reverse ++ (P'.dinst .zero).toList.reverse)) (.univ D.level) ∧
      EqTm S k .one [] ((Meta.tLine Ac P'.toList ψ as j).dinst .one)
        (A0.substList ((outs.take j).reverse ++ (P'.dinst .one).toList.reverse)) (.univ D.level) := by
  intro Ac Fall outs
  have hS := sigClosed_of_wfSig hW
  have hjC : j < C.args.length := (List.getElem?_eq_some_iff.1 hA0).1
  have hal : as.length = C.args.length := by
    have := tele_length htele; rwa [toList_ofList, argTys_length] at this
  obtain ⟨T1, TO, E0, E1, -, -⟩ := transpCon_inv hS hW (htr_of hW d) hD hC hps htele hL hψ hc j hjC.le
  simp only [toList_ofList] at T1 TO E0 E1
  obtain ⟨D', hD', hptL⟩ := gen_data_tele hL rfl
  rw [hD] at hD'; cases hD'
  have hpl : P'.toList.length = D.params.length := by simpa using tele_length hptL
  have hw : Wf0 S k .one [] := Wf0.nil trivial
  have hf : ∀ (r : I), r.Scoped k → ∀ t B, HasTy0 S (k + 1) I.one.shift (Ctx.dshift []) t B →
      HasTy0 S k .one [] (t.subst Tm.var (I.inst0 r)) (B.subst Tm.var (I.inst0 r)) :=
    fun r hr t B h => HasTy0.dsubst hS h hr
  have hP := pt_typed hW (htr_of hW d) hD hC hA0
  have hpost : ∀ (σ : Nat → Tm) (τ' : Nat → I),
      (A0.ren (C.pointRen j) id).subst (fun x => (σ x).subst Tm.var τ') (fun i => (I.var i).subst τ') =
        ((A0.ren (C.pointRen j) id).subst σ I.var).subst Tm.var τ' :=
    fun σ τ' => (subst_subst _ _ _ _ _).symm
  have hAk : Ac j = A0 := by simp [Ac, Ctor.argTy, hA0]
  have hFt : Fall.take j = Meta.tFills Ac P'.toList ψ as j := by
    have := Meta.tFills_take Ac P'.toList ψ as j (C.args.length - j)
    rwa [show j + (C.args.length - j) = C.args.length by omega] at this
  have hFl : Fall.length = C.args.length := Meta.tFills_length _ _ _ _ _
  have hLeq : (A0.ren (C.pointRen j) id).subst (lsub (ptL C Fall P'.toList.reverse j) 0) I.var =
      Meta.tLine Ac P'.toList ψ as j := by
    rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var, hFt]
    show _ = (Ac j).substList _
    rw [hAk]
  have hP0t : HasTele0 S k .one [] (P'.dinst .zero) D.params [] := by
    have := HasTele0.post (I.inst0 .zero) hw (hf .zero trivial) hptL (params_closed hS hD)
    simpa using this
  have hpl0 : (P'.dinst .zero).toList.length = D.params.length := by simpa using tele_length hP0t
  have hP1t : HasTele0 S k .one [] (P'.dinst .one) D.params [] := by
    have := HasTele0.post (I.inst0 .one) hw (hf .one trivial) hptL (params_closed hS hD)
    simpa using this
  have hpl1 : (P'.dinst .one).toList.length = D.params.length := by simpa using tele_length hP1t
  have h0 : ∀ (τ σ : Nat → _), TySub S 0 .one [] k .one [] σ τ :=
    fun τ σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
  have hPP0 := tySub_params hS hD hP0t 0 (h0 I.var) _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hPP0
  have TA := tySub_points hS hW hD hC hPP0 (by simpa using htele) hpl0 j hjC.le
  simp only [toList_ofList] at TA

  have T10 := T1.post (I.inst0 .zero) hw (hf .zero trivial)
  have T11 := T1.post (I.inst0 .one) hw (hf .one trivial)
  have e0 := (sub_ty hS hP).2.2 T10 TA E0
  rw [hpost, hLeq, pt_inst hW hD hC hA0 (by omega) (by simp [hpl0]) 0 I.var] at e0
  have e1 := (sub_ty hS hP).2.2 T11 TO E1
  rw [hpost, hLeq, pt_inst hW hD hC hA0 (by simp; omega) (by simp [hpl1]) 0 I.var] at e1
  exact ⟨minimal_to_spec_eq e0, minimal_to_spec_eq e1⟩

/-- The computability clause of an inductive type's line for its argument types. -/
def ArgClause (S : Sig) {m : ℕ} (Θ : SData m) {n : ℕ} (f : Hom n m) (ps : Tm) : Prop :=
  ∀ k' (σ : ISub k' n) (c : ℕ) (C : Ctor) (args : List Tm), (dataD S Θ.idx).ctors[c]? = some C →
    args.length < C.args.length → C.isRec args.length = false →
    (∀ j (hj : j < args.length), C.isRec j = true →
      DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' σ.hom ((Tm.data Θ.idx ps).isub σ) args[j]) →
    (∀ j (hj : j < args.length), C.isRec j = false →
      dataP S Θ f k' σ.hom c j ((args.take j).map (semK S k'))
        ((C.argTy Θ.idx (dataD S Θ.idx).params.length j).substList ((args.take j).reverse ++ (ps.isub σ).toList.reverse))
        args[j]) →
    (Comp S (tyLook (shapeV (Θ.restr (f.comp σ.hom))) c args.length (args.map (semK S k'))) k' k' (Hom.id k')).ty
      ((C.argTy Θ.idx (dataD S Θ.idx).params.length args.length).substList (args.reverse ++ (ps.isub σ).toList.reverse))

/-- Transport of a constructor along a line of inductive types. -/
theorem transpCon_RE {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    (hcodeT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre →
      ∀ k3 (h3 : Hom (k3 + 1) n) (A : Tm), (Comp S (Θ.ty c j n g pre) n (k3 + 1) h3).ty A → KanT S k3 A)
    (hKR : KR S m (dataC Θ)) {k0 : ℕ} {f : Hom (k0 + 1) m} {P : Tm}
    (hT : (Comp S (dataC Θ) m (k0 + 1) f).ty (.data Θ.idx P)) (hall : ArgClause S Θ f P)
    (ρ : ISub (k + 1) (k0 + 1)) {c : ℕ} {C : Ctor} (hC : (dataD S Θ.idx).ctors[c]? = some C)
    (hp : (dataD S Θ.idx).params ≠ []) {ψ : I} {qs : Tm} {as : List Tm} {rs : List I}
    (htyT : HasTy S k .one [] (.transp (.data Θ.idx (P.isub ρ)) ψ (.con Θ.idx c qs (Tm.ofList as) rs))
      (.data Θ.idx ((P.isub ρ).dinst .one)))
    (hqL : TyEq S k (.data Θ.idx qs) (.data Θ.idx ((P.isub ρ).dinst .zero)))
    (hrecO : ∀ i (hi : i < as.length), C.isRec i = true →
      RE S k (.data Θ.idx ((P.isub ρ).dinst .one)) (.transp (.data Θ.idx (P.isub ρ)) ψ as[i]))
    (hrecF : ∀ i (hi : i < as.length), C.isRec i = true →
      RE S (k + 1) (.data Θ.idx (P.isub ρ)) (Tm.transpFill (.data Θ.idx (P.isub ρ)) ψ as[i]))
    (hptA : ∀ i (hi : i < as.length), C.isRec i = false →
      RE S k ((C.argTy Θ.idx (dataD S Θ.idx).params.length i).substList
        ((as.take i).reverse ++ ((P.isub ρ).dinst .zero).toList.reverse)) as[i]) :
    RE S k (.data Θ.idx ((P.isub ρ).dinst .one)) (.transp (.data Θ.idx (P.isub ρ)) ψ (.con Θ.idx c qs (Tm.ofList as) rs)) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l0, ⟨hLt, hψ, hc, hb0⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW htyT) rfl
  obtain ⟨D, hD, hPt⟩ := gen_data_tele hLt rfl
  have hdD := dataD_eq hW hD
  rw [hdD] at hC hp hptA
  set d := Θ.idx with hd
  set P' := P.isub ρ with hP'
  -- the constructor's arguments at the start of the line
  obtain ⟨hI, -⟩ := gen_conF hb0 rfl
  obtain ⟨-, D0, C0, hD0, hC0, hqs, hdq, hqt, haq, hrs, hrsc⟩ := hI
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  have hL0 := minimal_to_spec (HasTy0.dsubst hS (Φ := .one) (Γ := []) hLt (r := .zero) trivial)
  obtain ⟨lq, eq⟩ := tyEq_eq hW hqL ⟨_, hL0⟩
  have hPl : P' = Tm.ofList P'.toList := tele_isList hPt
  have hw : Wf0 S k .one [] := Wf0.nil trivial
  have hP0t : HasTele0 S k .one [] (P'.dinst .zero) D.params [] := by
    have := HasTele0.post (I.inst0 .zero) hw (fun t B h => HasTy0.dsubst hS h (r := .zero) trivial) hPt
      (params_closed hS hD)
    simpa using this
  have htp := (args_retype hW hD hC hqs (isList_subst hPl _ _) hqt hP0t (spec_to_minimal_eq hW eq) haq).1
  have eT := EqTm.transpCon hD hp hC hPl (by rw [toList_ofList]) (toFull_tele htp) htyT
  have hal : as.length = C.args.length := by
    have := tele_length htp; rwa [toList_ofList, argTys_length] at this
  have heq := Meta.transpTele_eq (C.argTy d D.params.length) P'.toList ψ as as 0 rfl
  simp only [hal, ← List.range_eq_range'] at heq
  rw [toList_ofList, show ([] : List Tm) = (Meta.tFills (C.argTy d D.params.length) P'.toList ψ as 0).reverse
    from rfl, heq] at eT
  set Ac := C.argTy d D.params.length with hAc
  set outs := (List.range C.args.length).map fun j => Tm.transp (Meta.tLine Ac P'.toList ψ as j) ψ (as.getD j .abort)
    with houts
  set Fall := Meta.tFills Ac P'.toList ψ as C.args.length with hFall
  have hpsT1 := minimal_to_spec (HasTy0.dsubst hS (Φ := .one) (Γ := []) hLt (r := .one) trivial)
  have hol : outs.length = C.args.length := by simp [outs]
  have hFl : Fall.length = C.args.length := Meta.tFills_length _ _ _ _ _
  have hP'l : P'.toList.length = D.params.length := by simpa using tele_length hPt
  -- the line at a recursive argument is the inductive type's line
  have hrecL : ∀ j, C.isRec j = true → Meta.tLine Ac P'.toList ψ as j = .data d P' := by
    intro j hr
    show (Ac j).substList _ = _
    rw [hAc, argTy_rec hr, Tm.substList,
      show (Tm.data d (Ctor.paramVars D.params.length j)).subst _ I.var =
        Tm.data d ((Ctor.paramVars D.params.length j).substList _) from rfl,
      Meta.paramVars_substList hPl hP'l (by simp [Meta.tFills_length])]
  have hFget : ∀ j, j < C.args.length → Fall.getD j .abort =
      Tm.transpFill (Meta.tLine Ac P'.toList ψ as j) ψ (as.getD j .abort) :=
    fun j hj => Meta.tFills_get _ _ _ _ hj
  have hFtake : ∀ j, j ≤ C.args.length → Fall.take j = Meta.tFills Ac P'.toList ψ as j := by
    intro j hj
    have := Meta.tFills_take Ac P'.toList ψ as j (C.args.length - j)
    rwa [show j + (C.args.length - j) = C.args.length by omega] at this
  have hasget : ∀ j (hj : j < as.length), as.getD j .abort = as[j] := by
    intro j hj; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  -- the invariant of `transpCon` (typing)
  obtain ⟨-, -, -, -, -, Tel⟩ := transpCon_inv hS hW (htr_of hW d) hD hC hPl (by simpa using htp) hLt hψ hc
    C.args.length (Nat.le_refl _)
  simp only [toList_ofList] at Tel
  have hTρ := (hKR (k0 + 1) f (k + 1) ρ (.data Θ.idx P) (.data Θ.idx P)).1 hT
  -- the typing of the transports of the point arguments
  have htrj : ∀ j, j < C.args.length → HasTy S k .one [] (.transp (Meta.tLine Ac P'.toList ψ as j) ψ (as.getD j .abort))
      ((Meta.tLine Ac P'.toList ψ as j).dinst .one) := by
    intro j hj
    have h1 := Tel j hj
    simp only [houts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some] at h1
    obtain ⟨lj, ⟨hLj, hψj, hcj, hbj⟩, -⟩ := gen_transpF h1 rfl
    exact minimal_to_spec (HasTy0.transp hLj hψj hcj hbj)
  -- the valid prefixes of fillers
  let Valid : ℕ → Prop := fun j =>
    (∀ i, i < j → C.isRec i = true → DR S d D (dataMem S Θ f) (dataP S Θ f) (k + 1) ρ.hom
      ((Tm.data d P).isub ρ) (Fall.getD i .abort)) ∧
    (∀ i, i < j → C.isRec i = false → dataP S Θ f (k + 1) ρ.hom c i ((Fall.take i).map (semK S (k + 1)))
      ((Ac i).substList ((Fall.take i).reverse ++ (P.isub ρ).toList.reverse)) (Fall.getD i .abort))
  unfold ArgClause at hall
  rw [hdD] at hall
  have hFi : ∀ i (hi : i < Fall.length), Fall[i] = Fall.getD i .abort := by
    intro i hi; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have clause : ∀ j, j < C.args.length → C.isRec j = false → Valid j →
      (Comp S (tyLook (shapeV (Θ.restr (f.comp ρ.hom))) c j ((Fall.take j).map (semK S (k + 1)))) (k + 1) (k + 1)
        (Hom.id (k + 1))).ty (Meta.tLine Ac P'.toList ψ as j) := by
    intro j hj hr hv
    have hlj : (Fall.take j).length = j := by simp [hFl]; omega
    have := hall (k + 1) ρ c C (Fall.take j) hC (by omega) (by rw [hlj]; exact hr)
      (fun i hi hri => by
        rw [hlj] at hi
        rw [List.getElem_take, hFi i (by omega)]; exact hv.1 i hi hri)
      (fun i hi hri => by
        rw [hlj] at hi
        rw [List.getElem_take, hFi i (by omega), List.take_take, Nat.min_eq_left hi.le]; exact hv.2 i hi hri)
    rw [hlj] at this
    show (Comp S _ (k + 1) (k + 1) (Hom.id (k + 1))).ty ((Ac j).substList _)
    rw [← hFtake j hj.le]; exact this
  have pointFacts : ∀ j (hj : j < C.args.length), C.isRec j = false → Valid j →
      RE S (k + 1) (Meta.tLine Ac P'.toList ψ as j) (Fall.getD j .abort) ∧
      RE S k ((Ac j).substList ((outs.take j).reverse ++ (P'.dinst .one).toList.reverse)) (outs.getD j .abort) := by
    intro j hj hr hv
    have hcl := clause j hj hr hv
    have hv' := validPre_of_ty hcl
    rw [tyLook_eq hv'] at hcl
    have hpv : Θ.PtValid c (k + 1) ((f.comp ρ.hom).comp (Hom.id (k + 1))) ((Fall.take j).map (semK S (k + 1))) :=
      ptValid_of_validPre hv'
    have KT := hcodeT c j (k + 1) _ _ hpv k (Hom.id (k + 1)) _ hcl
    have KTall : ∀ k3 (ρ3 : ISub (k3 + 1) (k + 1)), KanT S k3 ((Meta.tLine Ac P'.toList ψ as j).isub ρ3) :=
      fun k3 ρ3 => hcodeT c j (k + 1) _ _ hpv k3 _ _
        ((ihT c j (k + 1) _ _ hpv (k + 1) (Hom.id (k + 1)) (k3 + 1) ρ3 (Meta.tLine Ac P'.toList ψ as j)
          (Meta.tLine Ac P'.toList ψ as j)).1 hcl)
    obtain ⟨A0, hA0⟩ := argTy_point (C := C) hj hr
    have hAk : Ac j = A0 := by simp [hAc, Ctor.argTy, hA0]
    obtain ⟨e0, e1⟩ := transpCon_pt_types hW hD hC hPl (by simpa using htp) hLt hψ hc hA0
    have hjl : j < as.length := by omega
    have hin : RE S k ((Meta.tLine Ac P'.toList ψ as j).dinst .zero) (as.getD j .abort) := by
      have := hptA j hjl hr
      rw [hAk, ← hasget j hjl] at this
      exact this.conv_ty hW (.inr ⟨_, EqTm.symm e0⟩)
    have hF := RE_transpFill hW KTall (htrj j hj) hin
    rw [← hFget j hj] at hF
    have hout := KT ψ (as.getD j .abort) (htrj j hj) hin
    refine ⟨hF, ?_⟩
    rw [hAk]
    have hog : outs.getD j .abort = .transp (Meta.tLine Ac P'.toList ψ as j) ψ (as.getD j .abort) := by
      simp only [houts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
        Option.getD_some]
    rw [hog]
    exact hout.conv_ty hW (.inr ⟨_, e1⟩)
  have key : ∀ j, j ≤ C.args.length → Valid j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hj
      have hv := ih (by omega)
      refine ⟨fun i hi hri => ?_, fun i hi hri => ?_⟩
      · by_cases hij : i < j
        · exact hv.1 i hij hri
        obtain rfl : i = j := by omega
        rw [hFget i (by omega), hrecL i hri, hasget i (by omega)]
        have := DR_of_RE hW hTρ (hrecF i (by omega) hri)
        rwa [hdD] at this
      · by_cases hij : i < j
        · exact hv.2 i hij hri
        obtain rfl : i = j := by omega
        have hF := (pointFacts i (by omega) hri hv).1
        have hcl := clause i (by omega) hri hv
        rw [hFtake i (by omega)] at hcl
        unfold RE at hF; rw [← Comp_eq_semK hcl] at hF
        show (Comp S _ (k + 1) (k + 1) (Hom.id (k + 1))).el _ _
        rw [hFtake i (by omega)]
        exact hF
  have hV := key C.args.length (Nat.le_refl _)
  have hVj : ∀ j, j ≤ C.args.length → Valid j := fun j hj =>
    ⟨fun i hi hri => hV.1 i (by omega) hri, fun i hi hri => hV.2 i (by omega) hri⟩
  have hog : ∀ j (hj : j < outs.length), outs[j] = outs.getD j .abort := by
    intro j hj; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  refine (RE_con hW hD hpsT1 (isList_subst hPl _ _) hC hol hrs hrsc (HasTy.eqR eT) (fun j hj hr => ?_)
    (fun j hj hr => ?_)).conv hW (TyEq.refl _) (EqTm.symm eT)
  · have hjC : j < C.args.length := by omega
    rw [hog j hj]
    simp only [houts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hjC, Option.map_some,
      Option.getD_some]
    rw [List.getElem?_eq_getElem (show j < as.length by omega)]
    simp only [Option.getD_some]
    have := hrecO j (by omega) hr
    rwa [← hrecL j hr] at this
  · have hjC : j < C.args.length := by omega
    rw [hog j hj]
    exact (pointFacts j hjC hr (hVj j hjC.le)).2


/-- Transport along a restriction of a line of inductive types, by induction on the relation of
the transported element (at all its restrictions). -/
theorem transp_data_DR {Θ : SData m} (hΘ : Θ.Good)
    (ihT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre → KR S n (Θ.ty c j n g pre))
    (hcodeT : ∀ c j n (g : Hom n m) pre, Θ.PtValid c n g pre →
      ∀ k3 (h3 : Hom (k3 + 1) n) (A : Tm), (Comp S (Θ.ty c j n g pre) n (k3 + 1) h3).ty A → KanT S k3 A)
    (hKR : KR S m (dataC Θ)) {k0 : ℕ} {f : Hom (k0 + 1) m} {P : Tm}
    (hT : (Comp S (dataC Θ) m (k0 + 1) f).ty (.data Θ.idx P)) (hall : ArgClause S Θ f P) :
    ∀ {k' : ℕ} {g : Hom k' (k0 + 1)} {A t : Tm},
      DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t →
      ∀ k'' (σ' : ISub k'' k') (ρ : ISub (k'' + 1) (k0 + 1)),
      g.comp σ'.hom = (ρ.comp (ISub.cons .zero trivial (ISub.id k''))).hom →
      TyEq S k'' (A.isub σ') (.data Θ.idx ((P.isub ρ).dinst .zero)) → ∀ ψ : I,
      HasTy S k'' .one [] (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) (.data Θ.idx ((P.isub ρ).dinst .one)) →
      RE S k'' (.data Θ.idx ((P.isub ρ).dinst .one)) (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) := by
  have hS := sigClosed_of_wfSig hW
  have hMem : ∀ k1 (f1 : Hom k1 (k0 + 1)) t t' A, EqTm S k1 .one [] t t' A → dataMem S Θ f k1 f1 t →
      dataMem S Θ f k1 f1 t' := fun k1 f1 t t' A e hm => by unfold dataMem at hm ⊢; rwa [← semK_eq hW e]
  -- the common part: the face, and inductive types without parameters
  have common : ∀ {k' : ℕ} {g : Hom k' (k0 + 1)} {A t : Tm},
      DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t →
      ∀ k'' (σ' : ISub k'' k') (ρ : ISub (k'' + 1) (k0 + 1)),
      g.comp σ'.hom = (ρ.comp (ISub.cons .zero trivial (ISub.id k''))).hom →
      TyEq S k'' (A.isub σ') (.data Θ.idx ((P.isub ρ).dinst .zero)) → ∀ ψ : I,
      HasTy S k'' .one [] (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) (.data Θ.idx ((P.isub ρ).dinst .one)) →
      ∀ D, S[Θ.idx]? = some (.data D) → ((ival (idEnv k'') ψ).holds ∨ D.params = []) →
      RE S k'' (.data Θ.idx ((P.isub ρ).dinst .one)) (.transp (.data Θ.idx (P.isub ρ)) ψ (t.isub σ')) := by
    intro k' g A t hdr k'' σ' ρ hg hA ψ htyT D hD hcase
    obtain ⟨l0, ⟨hLt, hψ, hc, hbase⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW htyT) rfl
    obtain ⟨D', hD', hPt⟩ := gen_data_tele hLt rfl
    rw [hD] at hD'; cases hD'
    have hTρ := (hKR (k0 + 1) f (k'' + 1) ρ (.data Θ.idx P) (.data Θ.idx P)).1 hT
    have hT0 := ty_dinst hW hKR hTρ .zero trivial
    rw [Hom.comp_assoc, ← ISub.hom_comp, ← hg] at hT0
    have hdr' := DR.isub hW hΘ f ihT hdr k'' σ'
    have htRE : RE S k'' (.data Θ.idx ((P.isub ρ).dinst .zero)) (t.isub σ') :=
      RE_of_DR hW hT0 (DR.conv hW hMem hdr' hA (EqTm.refl ((hdr'.typed).tyConv hA)))
    rcases hcase with hh | hp
    · exact RE_transp_face hW htyT hh htRE
    · have e := EqTm.transpData0 hD hp htyT
      have hnil : P.isub ρ = .tnil := by
        have h1 := tele_isList hPt
        have h2 := tele_length hPt
        rw [hp] at h2
        rw [h1, List.eq_nil_of_length_eq_zero h2]; rfl
      rw [hnil] at htRE e ⊢
      exact htRE.conv hW (TyEq.refl _) (EqTm.symm e)
  intro k' g A t h
  induction h with
  | @con k' g A t qs c C args rs hm hC hrs hsc hqs hAeq he hlen hrec hpt ihrec =>
    sorry
  | @hcomp k' g A t qs u a ψ' hm hH hsc hn hqs hAeq he ha hu iha ihu =>
    intro k'' σ' ρ hg hA ψ htyT
    have hdr : DR S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP S Θ f) k' g A t := DR.hcomp hm hH hsc hn hqs hAeq he ha hu
    obtain ⟨l0, ⟨hLt, hψ, hc, hbase⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) (spec_to_minimal hW htyT) rfl
    obtain ⟨D, hD, hPt⟩ := gen_data_tele hLt rfl
    have hdD := dataD_eq hW hD
    by_cases hcase : (ival (idEnv k'') ψ).holds ∨ D.params = []
    · exact common hdr k'' σ' ρ hg hA ψ htyT D hD hcase
    have hp : D.params ≠ [] := fun h => hcase (.inr h)
    have hTρ := (hKR (k0 + 1) f (k'' + 1) ρ (.data Θ.idx P) (.data Θ.idx P)).1 hT
    have hT1 := ty_dinst hW hKR hTρ .one trivial
    -- the restricted composition
    have he' := EqTm.isubS hW he σ'
    have hAeq' := hAeq.isub hW σ'
    have hqL : TyEq S k'' (.data Θ.idx (qs.isub σ')) (.data Θ.idx ((P.isub ρ).dinst .zero)) := hAeq'.symm.trans hW hA
    have hL0 := minimal_to_spec (HasTy0.dsubst hS (Φ := .one) (Γ := []) hLt (r := .zero) trivial)
    obtain ⟨lq, eq⟩ := tyEq_eq hW hqL ⟨_, hL0⟩
    have hhq : HasTy S k'' .one [] (.hcomp (.data Θ.idx (qs.isub σ')) (ψ'.subst σ'.τ) (u.isub σ'.up) (a.isub σ'))
        (.data Θ.idx (qs.isub σ')) := (HasTy.eqR he').tyConv hAeq'
    obtain ⟨hh0, -⟩ := hcomp_retype hW hhq eq
    have htyT2 : HasTy S k'' .one [] (.transp (.data Θ.idx (P.isub ρ)) ψ
        (.hcomp (.data Θ.idx (qs.isub σ')) (ψ'.subst σ'.τ) (u.isub σ'.up) (a.isub σ')))
        (.data Θ.idx ((P.isub ρ).dinst .one)) :=
      HasTy.transp (minimal_to_spec hLt) hψ (minimal_to_spec_eq hc) ((HasTy.eqR he').tyConv hA)
    have eb := EqTm.transp htyT htyT2 (EqTm.refl (minimal_to_spec hLt)) (ent_refl _) (ent_refl _) (he'.tyConv hA)
    rw [hdD] at hH
    have eT := EqTm.transpHcomp hD hp hH hh0 htyT2
    have KH := kanH_data hW hKR hT1
    have hbase := iha k'' σ' ρ hg hqL ψ
      (HasTy.transp (minimal_to_spec hLt) hψ (minimal_to_spec_eq hc) ((HasTy.isubS hW ha.typed σ').tyConv hqL))
    refine (KH _ _ _ (HasTy.eqR eT) (fun k3 σ3 r hr hh3 => ?_) hbase).conv hW (TyEq.refl _)
      (EqTm.symm (EqTm.trans eb eT))
    obtain ⟨-, ⟨-, hψ', htube, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW (HasTy.eqR eT)) rfl
    have hT' := minimal_to_spec (HasTy0.isub hS (Ψ' := k3) (Φ' := .one) (τ := (ISub.cons r hr σ3).τ) htube
      (fun i hi => (ISub.cons r hr σ3).sc i hi) (ent_cof_cons hW hψ' r hr σ3 hh3) (Wf0.nil trivial))
    rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons, skip_isub (by rfl) (fun n => rfl)] at hT'
    rw [isub_up_dinst _ σ3 r hr, skip_isub (by rfl) (fun n => rfl)]
    have eP1 : (Tm.data Θ.idx ((P.isub ρ).dinst .one)).isub σ3 = .data Θ.idx ((P.isub (ρ.comp σ3.up)).dinst .one) := by
      show Tm.data Θ.idx (((P.isub ρ).dinst .one).isub σ3) = _
      rw [isub_dinst, Tm.isub_isub]; rfl
    have eP0 : (Tm.data Θ.idx ((P.isub ρ).dinst .zero)).isub σ3 = .data Θ.idx ((P.isub (ρ.comp σ3.up)).dinst .zero) := by
      show Tm.data Θ.idx (((P.isub ρ).dinst .zero).isub σ3) = _
      rw [isub_dinst, Tm.isub_isub]; rfl
    have eL : (Tm.data Θ.idx (P.isub ρ)).isub σ3.up = .data Θ.idx (P.isub (ρ.comp σ3.up)) := by
      show Tm.data Θ.idx ((P.isub ρ).isub σ3.up) = _
      rw [Tm.isub_isub]
    change HasTy S k3 .one [] _ ((Tm.data Θ.idx ((P.isub ρ).dinst .one)).isub σ3) at hT'
    show RE S k3 ((Tm.data Θ.idx ((P.isub ρ).dinst .one)).isub σ3) _
    have eu : (u.isub σ'.up).isub (ISub.cons r hr σ3) = (u.isub (σ'.comp σ3).up).dinst r := isub_isub_up_cons u σ' r hr σ3
    rw [eP1, eL, eu] at hT' ⊢
    have hcl : ((u.isub (σ'.comp σ3).up).dinst r).closedB 0 k3 = true := by
      have := closed_of_ty hW hT'; simp only [Tm.closedB, Bool.and_eq_true] at this; exact this.2
    have hq' := hqL.isub hW σ3
    rw [eP0] at hq'
    have key := ihu k3 (σ'.comp σ3) r hr (by rw [I_subst_comp]; exact hh3) k3 (ISub.id k3) (ρ.comp σ3.up) ?_ ?_
      (ψ.subst σ3.τ) (by rw [isub_id_of_closed hcl]; exact hT')
    · rwa [isub_id_of_closed hcl] at key
    · rw [ISub.hom_id, Hom.comp_id, ISub.hom_comp, ← Hom.comp_assoc, hg, ← ISub.hom_comp]
      congr 1
      rw [ISub.comp_assoc, cons0_comp, ← ISub.comp_assoc]
    · rw [Tm.isub_isub, ISub.comp_id, ← Tm.isub_isub]; exact hq'

end

end Model.Canon
