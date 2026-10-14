import Model.Whnf.Valid2Data
import Model.Whnf.Kan2DataTInd

/-!
# The eliminator of inductive types without path constructors

The binary counterpart of `Model/Canon/Elim.lean` (`RE_elim_DR`): eliminations of related elements
are related, by induction on the relation of the eliminated elements (`DR2`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

/-- Application through a Π-telescope. -/
theorem RE2_apps : ∀ (as as' : List Tm) {Δ prev : List Tm} {f f' base : Tm}, as.length = Δ.length →
    as'.length = as.length → RE2 S k ((Δ.foldr Tm.pi base).substList prev) f f' →
    (∀ j (hj : j < as.length) (hj' : j < as'.length) (hjΔ : j < Δ.length),
      RE2 S k (Δ[j].substList ((as.take j).reverse ++ prev)) as[j] as'[j]) →
    RE2 S k (base.substList (as.reverse ++ prev)) (Tm.apps f as) (Tm.apps f' as')
  | [], [], [], prev, f, f', base, _, _, hf, _ => by simpa [Tm.apps] using hf
  | a :: as, a' :: as', A :: Δ, prev, f, f', base, hl, hl', hf, ha => by
    rw [List.foldr_cons, pi_substList] at hf
    have h1 := RE2_pi_elim hW hf (by simpa using ha 0 (by simp) (by simp) (by simp))
    rw [up_slS_inst] at h1
    have := RE2_apps as as' (by simpa using hl) (by simpa using hl') h1 (fun j hj hj' hjΔ => by
      have := ha (j + 1) (by simp; omega) (by simp; omega) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this)
    simpa [Tm.apps, List.foldl, List.reverse_cons, List.append_assoc] using this
  | [], _ :: _, _, _, _, _, _, _, hl', _, _ => by simp at hl'
  | _ :: _, [], _, _, _, _, _, _, hl', _, _ => by simp at hl'
  | [], [], _ :: _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, _, hl, _, _, _ => by simp at hl

/-- The induction hypotheses of a branch at a constructor's arguments. -/
abbrev ihsOf (d : ℕ) (C : Ctor) (ps P bs : Tm) (X : List Tm) : List Tm :=
  C.recPos.map fun j => Tm.elim d ps P bs (X.getD j .abort)

omit hW in
theorem apps_append (f : Tm) (X Y : List Tm) : Tm.apps (Tm.apps f X) Y = Tm.apps f (X ++ Y) := by
  simp only [Tm.apps, List.foldl_append]

/-- The branches of related eliminations, applied to related arguments and the related eliminations of
the recursive arguments, are related. -/
theorem elimCon_rel {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {ps M bs ps' M' bs' b b' : Tm} (hpl : ps.toList.length = D.params.length)
    (hbr : RE2 S k (D.branchTy d c C ps M) b b') {X X' : List Tm} (hXl : X.length = C.args.length)
    (hX'l : X'.length = C.args.length)
    (hargs : ∀ i (hi : i < X.length) (hi' : i < X'.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ ps.toList.reverse)) X[i] X'[i])
    (hih : ∀ j (hj : j ∈ C.recPos), RE2 S k (M.inst (X.getD j .abort))
      (.elim d ps M bs (X.getD j .abort)) (.elim d ps' M' bs' (X'.getD j .abort))) :
    RE2 S k (M.inst (.con d c ps (Tm.ofList X) []))
      (Tm.apps b (X ++ ihsOf d C ps M bs X)) (Tm.apps b' (X' ++ ihsOf d C ps' M' bs' X')) := by
  have hS := sigClosed_of_wfSig hW
  have hdims := (nonHIT_ctor hH hC).1
  rw [Meta.branchTy_eq, hdims] at hbr
  have hbr0 : RE2 S k ((((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)).foldr Tm.pi
      (((List.range C.recPos.length).map (DataDecl.branchIhTy C M)).foldr Tm.pi
        (ipis 0 (DataDecl.branchBody d c C ps M)))).substList []) b b' := by rw [substList_nil]; exact hbr
  have h1 := RE2_apps hW X X' (by simp [hXl]) (by rw [hX'l, hXl]) hbr0 (fun j hj hj' hjΔ => by
    simp only [List.getElem_map, List.getElem_range, List.append_nil]
    rw [branchArgTy_substList hS hD hC hpl (by simp; omega)]
    exact hargs j hj hj')
  rw [List.append_nil] at h1
  have h2 := RE2_apps hW (ihsOf d C ps M bs X) (ihsOf d C ps' M' bs' X')
    (Δ := (List.range C.recPos.length).map (DataDecl.branchIhTy C M)) (by simp) (by simp) h1
    (fun s hs hs' hsΔ => by
      simp only [List.length_map, List.length_range] at hsΔ
      simp only [List.getElem_map, List.getElem_range]
      rw [branchIhTy_substList M hsΔ (by simp; omega) hXl]
      obtain ⟨hjn, hjr⟩ := mem_recPos (List.getElem_mem (l := C.recPos) hsΔ)
      have hgd : C.recPos.getD s 0 = C.recPos[s] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsΔ]; rfl
      simp only [ihsOf, List.getElem_map, hgd]
      exact hih _ (List.getElem_mem hsΔ))
  rw [substList_eq] at h2
  have hb := branchBody_inst (d := d) (c := c) (ps := ps) (P := M) (ihs := ihsOf d C ps M bs X) (args := X) (rs := [])
    (by simp) hXl (by simp [hdims])
  simp only [ipis, List.range_zero, List.foldl_nil] at h2
  rw [show (consIs [] I.var) = I.var from rfl] at hb
  rw [hb, apps_append, apps_append] at h2
  exact h2

/-! ### Reduction of eliminations -/

omit hW in
theorem red_elim_scrut {d : ℕ} {ps M bs t w : Tm} (h : Red S t w) :
    Red S (.elim d ps M bs t) (.elim d ps M bs w) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (by simp [step, hs]) ih

omit hW in
theorem step_elimCon {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {ps M bs qs b : Tm} {X : List Tm} (hb : bs.toList[c]? = some b) :
    step S (.elim d ps M bs (.con d c qs (Tm.ofList X) [])) = some (Tm.apps b (X ++ ihsOf d C ps M bs X)) := by
  have h0 := step_con_nonHIT (S := S) hD hH hC qs (Tm.ofList X) []
  simp only [step] at h0 ⊢
  rw [h0]
  simp [hD, hb, hC, toList_ofList, Tm.papps, ihsOf]

/-- An elimination of an element reduces, through the constructor normal form of the element, to the
branch applied to its arguments. -/
theorem elim_reduct {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false) {k : ℕ}
    {ps M bs : Tm} {m : ℕ} (hE : ElimPrem S k .one [] d D ps M bs m) {x : Tm}
    (hx : HasTy S k .one [] x (.data d ps)) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs : Tm} {Z : List Tm}
    (hw : RedE S k (.data d ps) x (.con d c qs (Tm.ofList Z) [])) :
    Red S (.elim d ps M bs x) (Tm.apps (bs.toList.getD c .abort) (Z ++ ihsOf d C ps M bs Z)) ∧
      EqTm S k .one [] (.elim d ps M bs x) (Tm.apps (bs.toList.getD c .abort) (Z ++ ihsOf d C ps M bs Z))
        (M.inst x) := by
  have hS := sigClosed_of_wfSig hW
  have hc' : c < bs.toList.length := by
    rw [hE.hlen]; exact (List.getElem?_eq_some_iff.1 hC).1
  have hb : bs.toList[c]? = some (bs.toList.getD c .abort) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc']; rfl
  refine ⟨(red_elim_scrut hw.1.1).trans (.step (step_elimCon hD hH hC hb) (.refl _)), ?_⟩
  have hpT := minimal_to_spec hE.hdata
  obtain ⟨htele, e, -, hZl⟩ := con_retype hW hD hH hC hw.2 (TyEq.refl _) hpT
  have ht0 := spec_to_minimal hW hx
  have hcp := spec_to_minimal hW (HasTy.eqR e)
  have e1 := hE.elim_congr hS ht0 hcp (spec_to_minimal_eq hW e)
  have e2 := EqTm.elimCon (T := M.inst (.con d c ps (Tm.ofList Z) [])) hD hC hb hE.hps
    (by rw [toList_ofList]) hE.hbs (toFull_tele htele) (minimal_to_spec (hE.elim_ty hcp))
  rw [toList_ofList] at e2
  have eP := HasTy0.inst_congr hS hE.hP hcp ht0 (EqTm0.symm (spec_to_minimal_eq hW e))
  exact (minimal_to_spec_eq e1).trans ((e2.tyConv (.inr ⟨m, minimal_to_spec_eq eP⟩)))

/-- Related eliminations: the right parameters, motive and branches, related to the left ones at all
restrictions, with the typing of both. -/
structure ElimRel (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs Q M' bs' : Tm) : Prop where
  dat : ∀ k1 (ρ : ISub k1 K), RT2 S k1 (.data d (P.isub ρ)) (.data d (Q.isub ρ))
  mot : ∀ k1 (ρ : ISub k1 K) (x x' : Tm), RE2 S k1 (.data d (P.isub ρ)) x x' →
    RT2 S k1 ((M.isub ρ).inst x) ((M'.isub ρ).inst x')
  br : ∀ k1 (ρ : ISub k1 K) (c : ℕ) (C : Ctor), D.ctors[c]? = some C →
    RE2 S k1 (D.branchTy d c C (P.isub ρ) (M.isub ρ)) ((bs.isub ρ).toList.getD c .abort)
      ((bs'.isub ρ).toList.getD c .abort)
  tyL : ∀ k1 (ρ : ISub k1 K), ∃ m, ElimPrem S k1 .one [] d D (P.isub ρ) (M.isub ρ) (bs.isub ρ) m
  tyR : ∀ k1 (ρ : ISub k1 K), ∃ m, ElimPrem S k1 .one [] d D (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) m

/-- The contractum of an elimination of a constructor with the arguments `X`. -/
abbrev ecTm (d : ℕ) (C : Ctor) (c : ℕ) (ps M bs : Tm) (X : List Tm) : Tm :=
  Tm.apps (bs.toList.getD c .abort) (X ++ ihsOf d C ps M bs X)

/-- The motive at the relation of eliminated elements, at all restrictions. -/
def EM1 (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm) (k1 : ℕ) (g : Hom k1 K) (A x x' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d (P.isub ρ) → ∀ Q M' bs', ElimRel S d D K P M bs Q M' bs' →
    RE2 S k1 ((M.isub ρ).inst x) (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x)
      (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) x')

/-- The motive at one stage: the contracta at the constructor normal forms are related. -/
def EM2 (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm) (k1 : ℕ) (g : Hom k1 K) (A v v' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d (P.isub ρ) → ∀ Q M' bs', ElimRel S d D K P M bs Q M' bs' →
  ∀ (c : ℕ) (C : Ctor) (qs : Tm) (X : List Tm) (qs' : Tm) (X' : List Tm), D.ctors[c]? = some C →
    RedE S k1 A v (.con d c qs (Tm.ofList X) []) → RedE S k1 A v' (.con d c qs' (Tm.ofList X') []) →
    RE2 S k1 ((M.isub ρ).inst (.con d c (P.isub ρ) (Tm.ofList X) []))
      (ecTm d C c (P.isub ρ) (M.isub ρ) (bs.isub ρ) X) (ecTm d C c (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) X')


omit hW in
theorem isub_elim {k' : ℕ} (d : ℕ) (ps M bs t : Tm) (σ : ISub k' k) :
    (Tm.elim d ps M bs t).isub σ = .elim d (ps.isub σ) (M.isub σ) (bs.isub σ) (t.isub σ) := by
  show Tm.elim d (ps.subst Tm.var σ.τ) (M.subst (Tm.up Tm.var) σ.τ) (bs.subst Tm.var σ.τ) (t.subst Tm.var σ.τ) = _
  rw [up_var]; rfl

omit hW in
theorem ecTm_isub {k' : ℕ} (d : ℕ) (C : Ctor) (c : ℕ) {ps M bs : Tm} (hbs : bs = Tm.ofList bs.toList)
    (X : List Tm) (σ : ISub k' k) :
    (ecTm d C c ps M bs X).isub σ = ecTm d C c (ps.isub σ) (M.isub σ) (bs.isub σ) (X.map (·.isub σ)) := by
  simp only [ecTm, ihsOf]
  show (Tm.apps _ _).subst Tm.var σ.τ = _
  rw [apps_subst, toList_isub hbs, List.map_append, List.map_map]
  congr 1
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases bs.toList[c]? <;> rfl
  · congr 1
    congr 1; funext j
    simp only [Function.comp]
    rw [show (Tm.elim d ps M bs (X.getD j .abort)).subst Tm.var σ.τ =
      (Tm.elim d ps M bs (X.getD j .abort)).isub σ from rfl, isub_elim]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases X[j]? <;> rfl

section lit
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hD hH hP hPP

/-- An element of a restriction of a literal inductive type is related to the constructor of its normal
form at the parameters of the type. -/
theorem conP_rel {k3 : ℕ} (ρ' : ISub k3 K) {y y' : Tm} (hy : RE2 S k3 (.data d (P.isub ρ')) y y')
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs : Tm} {Z : List Tm}
    (hw : RedE S k3 (.data d (P.isub ρ')) y (.con d c qs (Tm.ofList Z) [])) :
    RE2 S k3 (.data d (P.isub ρ')) (.con d c (P.isub ρ') (Tm.ofList Z) []) y := by
  have hPρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hyy := RE2.trans hW hPρ hy (RE2.symm hW hPρ hy)
  have r1 := RE2_whnf_con hW hD hH hP hPP ρ' hy hC hw
  have hPT := HasTy.isubS hW hP ρ'
  obtain ⟨-, e, -, hZl⟩ := con_retype hW hD hH hC hw.2 (TyEq.refl _) hPT
  -- the arguments of the normal form, related to themselves
  obtain ⟨c2, C2, qs2, Z2, qs2', Z2', hC2, hZ2l, hZ2'l, hr2, hr2', hZ2⟩ := dataLit_argsU hW hD hH hP hPP ρ' hyy
  have f1 := RedW.unique hr2.1 hw.1
  have f2 := RedW.unique hr2'.1 hw.1
  simp only [Tm.con.injEq] at f1 f2
  obtain ⟨-, rfl, -, eZ, -⟩ := f1
  obtain ⟨-, -, -, eZ', -⟩ := f2
  have eZ1 := congrArg Tm.toList eZ
  have eZ1' := congrArg Tm.toList eZ'
  simp only [toList_ofList] at eZ1 eZ1'
  subst eZ1 eZ1'
  rw [hC] at hC2; cases hC2
  have r2 := RE2_con_args hW hD hH hP hPP ρ' hC (q := P.isub ρ') (q' := qs) hZl hZl (HasTy.eqR e) (e.symm.trans hw.2) hZ2
  exact RE2.trans hW hPρ r2 r1
/-- The constructor case: the contracta of related constructors are related. -/
theorem em2_con {k1 : ℕ} {g : Hom k1 K} {M bs A t t' ps qs qs' : Tm} {c : ℕ} {C : Ctor} {args args' : List Tm}
    {rs rs' : List I}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K))
      k1 g A t t')
    (hC : (dataD S d).ctors[c]? = some C) (hA : RedT S k1 A (.data d ps))
    (ht : RedE S k1 A t (.con d c qs (Tm.ofList args) rs)) (ht' : RedE S k1 A t' (.con d c qs' (Tm.ofList args') rs'))
    (hl : args.length = C.args.length) (hl' : args'.length = C.args.length)
    (ihrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      EM1 S d D K P M bs k1 g (.data d ps) args[j] args'[j]) :
    EM2 S d D K P M bs k1 g A t t' := by
  intro ρ hg hAe Q M' bs' hER c2 C2 qs2 X2 qs2' X2' hC2 hr hr'
  subst hg hAe
  have hdD := dataD_eq hW hD
  have hC' : D.ctors[c]? = some C := hdD ▸ hC
  obtain rfl : ps = P.isub ρ := redT_data_eq (Θ := ΘK S D d K P) hA
  have e1 := RedW.unique hr.1 ht.1
  have e2 := RedW.unique hr'.1 ht'.1
  simp only [Tm.con.injEq] at e1 e2
  obtain ⟨-, rfl, rfl, eX, -⟩ := e1
  obtain ⟨-, -, rfl, eX', -⟩ := e2
  have eX1 := congrArg Tm.toList eX
  have eX1' := congrArg Tm.toList eX'
  simp only [toList_ofList] at eX1 eX1'
  subst X2 X2'
  rw [hC'] at hC2; cases hC2
  -- the arguments
  obtain ⟨c3, C3, q3, Z, q3', Z', hC3, hZl, hZ'l, hr3, hr3', hZ⟩ := DR2At_args hW hD hH hP hPP ρ hat
  have f1 := RedW.unique hr3.1 hr.1
  have f2 := RedW.unique hr3'.1 hr'.1
  simp only [Tm.con.injEq] at f1 f2
  obtain ⟨-, rfl, -, eZ, -⟩ := f1
  obtain ⟨-, -, -, eZ', -⟩ := f2
  have eZ1 := congrArg Tm.toList eZ
  have eZ1' := congrArg Tm.toList eZ'
  simp only [toList_ofList] at eZ1 eZ1'
  subst Z Z'
  rw [hC'] at hC3; cases hC3
  have hTP : IsTyK S k1 (.data d (P.isub ρ)) := ⟨_, .inl (HasTy.isubS hW hP ρ)⟩
  have hplen : (P.isub ρ).toList.length = D.params.length := by
    have := data_len_of hW hTP; rwa [hdD] at this
  refine elimCon_rel hW hD hH hC' hplen (hER.br k1 ρ _ C hC') hl hl' (fun i hi hi' => ?_) (fun j hj => ?_)
  · have := hZ i (by omega)
    rwa [getD_eq_get' hW hD hH hP hPP hi, getD_eq_get' hW hD hH hP hPP hi'] at this
  · obtain ⟨hjn, hjr⟩ := mem_recPos hj
    rw [getD_eq_get' hW hD hH hP hPP (show j < args.length by omega),
      getD_eq_get' hW hD hH hP hPP (show j < args'.length by omega)]
    exact ihrec j (by omega) (by omega) hjr ρ rfl rfl Q M' bs' hER

omit hW hD hH hP hPP in
theorem data_isub_comp {k1 k2 : ℕ} (ρ : ISub k1 K) (κ : ISub k2 k1) :
    (Tm.data d (P.isub ρ)).isub κ = .data d (P.isub (ρ.comp κ)) := by
  show Tm.data d ((P.isub ρ).isub κ) = _; rw [Tm.isub_isub]

/-- The intro case: eliminations of related elements, from the contracta of their normal forms at all
restrictions. -/
theorem em1_intro {M bs : Tm} (hRL : ElimRel S d D K P M bs P M bs) {k1 : ℕ} {g : Hom k1 K} {A x x' : Tm}
    (hdr : DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K))
      k1 g A x x')
    (ih : ∀ k' (σ : ISub k' k1), EM2 S d D K P M bs k' (g.comp σ.hom) (A.isub σ) (x.isub σ) (x'.isub σ))
    (ihc : ∀ k' (σ : ISub k' k1) w, RedW S (x.isub σ) w → ∀ k'' (ρ' : ISub k'' k'),
      EM2 S d D K P M bs k'' (g.comp (σ.comp ρ').hom) (A.isub (σ.comp ρ')) (w.isub ρ') (x.isub (σ.comp ρ'))) :
    EM1 S d D K P M bs k1 g A x x' := by
  intro ρ hg hAe Q M' bs' hER
  subst hg hAe
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the related elements
  have hxx : RE2 S k1 (.data d (P.isub ρ)) x x' := by
    have he : EqTm S k1 .one [] x x' (.data d (P.isub ρ)) := by cases hdr with | intro he => exact he
    exact (RE2_dataLit_iff hW hD hP ρ).2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, hdr⟩
  have hxκ : ∀ {k4 : ℕ} (κ : ISub k4 k1), RE2 S k4 (.data d (P.isub (ρ.comp κ))) (x.isub κ) (x'.isub κ) := by
    intro k4 κ
    have := RE2.isub hW hxx κ
    rwa [data_isub_comp] at this
  -- the normal forms
  have hw := fun k4 (κ : ISub k4 k1) => dataLit_argsU hW hD hH hP hPP (ρ.comp κ) (hxκ κ)
  choose c C qs Z qs' Z' hC hZl hZ'l hr hr' hZ using hw
  -- typings
  have hxxs : ∀ {k4 : ℕ} (κ : ISub k4 k1), RE2 S k4 (.data d (P.isub (ρ.comp κ))) (x.isub κ) (x.isub κ) := by
    intro k4 κ
    have hPκ := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp κ)
    exact RE2.trans hW hPκ (hxκ κ) (RE2.symm hW hPκ (hxκ κ))
  have eT : ∀ {k4 : ℕ} (κ : ISub k4 k1), ((M.isub ρ).inst x).isub κ = (M.isub (ρ.comp κ)).inst (x.isub κ) := by
    intro k4 κ; rw [isub_inst, Tm.isub_isub]
  have eL : ∀ {k4 : ℕ} (κ : ISub k4 k1),
      (Tm.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x).isub κ =
        .elim d (P.isub (ρ.comp κ)) (M.isub (ρ.comp κ)) (bs.isub (ρ.comp κ)) (x.isub κ) := by
    intro k4 κ; rw [isub_elim, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
  have eR : ∀ {k4 : ℕ} (κ : ISub k4 k1),
      (Tm.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) x').isub κ =
        .elim d (Q.isub (ρ.comp κ)) (M'.isub (ρ.comp κ)) (bs'.isub (ρ.comp κ)) (x'.isub κ) := by
    intro k4 κ; rw [isub_elim, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
  have hx'Q : ∀ {k4 : ℕ} (κ : ISub k4 k1), HasTy S k4 .one [] (x'.isub κ) (.data d (Q.isub (ρ.comp κ))) := fun κ =>
    (RE2.typed (hxκ κ)).2.1.tyConv (tyB (hER.dat _ (ρ.comp κ)))
  have hTT : ∀ {k4 : ℕ} (κ : ISub k4 k1), TyEq S k4 ((M'.isub (ρ.comp κ)).inst (x'.isub κ))
      ((M.isub (ρ.comp κ)).inst (x.isub κ)) := fun κ => TyEq.symm (tyB (hER.mot _ (ρ.comp κ) _ _ (hxκ κ)))
  obtain ⟨mL, hEL⟩ := hER.tyL k1 ρ
  obtain ⟨mR, hER'⟩ := hER.tyR k1 ρ
  have ht : HasTy S k1 .one [] (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x) ((M.isub ρ).inst x) :=
    minimal_to_spec (hEL.elim_ty (spec_to_minimal hW (RE2.typed hxx).1))
  have ht' : HasTy S k1 .one [] (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) x') ((M.isub ρ).inst x) := by
    have h := minimal_to_spec (hER'.elim_ty (spec_to_minimal hW ((RE2.typed hxx).2.1.tyConv (tyB (hER.dat k1 ρ)))))
    have := hTT (ISub.id k1)
    rw [ISub.comp_id, isub_id_of_closed (closed_of_ty hW (RE2.typed hxx).1),
      isub_id_of_closed (closed_of_ty hW (RE2.typed hxx).2.1)] at this
    exact h.tyConv this
  have hAA : RT2 S k1 ((M.isub ρ).inst x) ((M.isub ρ).inst x) := by
    have := hRL.mot k1 ρ x x (RE2.trans hW (RT2.isub hW (tyCode_of_univ hW hP) hPP ρ) hxx
      (RE2.symm hW (RT2.isub hW (tyCode_of_univ hW hP) hPP ρ) hxx))
    exact this
  refine RE2.expandBoth hW (tyCode_of_ty hW ht) hAA ht ht'
    (fun k4 κ => ecTm d (C k4 κ) (c k4 κ) (P.isub (ρ.comp κ)) (M.isub (ρ.comp κ)) (bs.isub (ρ.comp κ)) (Z k4 κ))
    (fun k4 κ => ecTm d (C k4 κ) (c k4 κ) (Q.isub (ρ.comp κ)) (M'.isub (ρ.comp κ)) (bs'.isub (ρ.comp κ)) (Z' k4 κ))
    (fun k4 κ => ?_) (fun k4 κ => ?_) (fun k4 κ k5 κ' => ?_)
  · obtain ⟨m4, hE4⟩ := hER.tyL k4 (ρ.comp κ)
    rw [eL, eT]
    exact elim_reduct hW hD hH hE4 (RE2.typed (hxκ κ)).1 (hC k4 κ) (hr k4 κ)
  · obtain ⟨m4, hE4⟩ := hER.tyR k4 (ρ.comp κ)
    rw [eR, eT]
    have hr4 : RedE S k4 (.data d (Q.isub (ρ.comp κ))) (x'.isub κ)
        (.con d (c k4 κ) (qs' k4 κ) (Tm.ofList (Z' k4 κ)) []) :=
      ⟨(hr' k4 κ).1, (hr' k4 κ).2.tyConv (tyB (hER.dat _ (ρ.comp κ)))⟩
    obtain ⟨r1, r2⟩ := elim_reduct hW hD hH hE4 (hx'Q κ) (hC k4 κ) hr4
    exact ⟨r1, r2.tyConv (hTT κ)⟩
  · have eT3 : (ρ.comp κ).comp κ' = ρ.comp (κ.comp κ') := ISub.comp_assoc _ _ _
    have ecn : (Tm.con d (c k4 κ) (qs k4 κ) (Tm.ofList (Z k4 κ)) []).isub κ' =
        .con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) [] := by
      show Tm.con d _ ((qs k4 κ).isub κ') ((Tm.ofList (Z k4 κ)).isub κ') [] = _; rw [ofList_isub]
    -- the restricted normal form, against the element at the further restriction
    have R0 : RE2 S k5 (.data d (P.isub (ρ.comp (κ.comp κ'))))
        (.con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) []) (x.isub (κ.comp κ')) := by
      have r0 := RE2.isub hW (RE2_whnf_con hW hD hH hP hPP _ (hxxs κ) (hC k4 κ) (hr k4 κ)) κ'
      rw [ecn, data_isub_comp, eT3, Tm.isub_isub] at r0
      exact r0
    -- the constructors agree
    obtain ⟨c3, C3, q3, W, q3', W', hC3, -, -, hr3, hr3', -⟩ := dataLit_argsU hW hD hH hP hPP _ R0
    have g1 := RedW.unique hr3.1 (redW_self (step_con_nonHIT hD hH (hC k4 κ) _ _ _))
    have g2 := RedW.unique hr3'.1 (hr k5 (κ.comp κ')).1
    simp only [Tm.con.injEq] at g1 g2
    obtain ⟨-, rfl, -, -, -⟩ := g1
    obtain ⟨-, hcc, -, -, -⟩ := g2
    have hcc' : c k5 (κ.comp κ') = c k4 κ := by rw [← hcc]
    have hCC : C k5 (κ.comp κ') = C k4 κ := by
      have h1 := hC k5 (κ.comp κ'); rw [hcc', hC k4 κ] at h1; exact (Option.some.inj h1).symm
    have RE1 : RedE S k5 (.data d (P.isub (ρ.comp (κ.comp κ'))))
        (.con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) [])
        (.con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) []) :=
      ⟨redW_self (step_con_nonHIT hD hH (hC k4 κ) _ _ _), EqTm.refl (RE2.typed R0).1⟩
    have RE2' : RedE S k5 (.data d (P.isub (ρ.comp (κ.comp κ')))) (x.isub (κ.comp κ'))
        (.con d (c k4 κ) (qs k5 (κ.comp κ')) (Tm.ofList (Z k5 (κ.comp κ'))) []) := by
      have h := hr k5 (κ.comp κ'); rw [hcc'] at h; exact h
    have RE3 : RedE S k5 (.data d (P.isub (ρ.comp (κ.comp κ')))) (x'.isub (κ.comp κ'))
        (.con d (c k4 κ) (qs' k5 (κ.comp κ')) (Tm.ofList (Z' k5 (κ.comp κ'))) []) := by
      have h := hr' k5 (κ.comp κ'); rw [hcc'] at h; exact h
    -- (R1) the restricted contractum, against the contractum at the further restriction
    have T1 := ihc k4 κ _ (hr k4 κ).1 k5 κ'
    rw [ecn, data_isub_comp] at T1
    have R1 := T1 (ρ.comp (κ.comp κ')) (by simp only [ISub.hom_comp]) rfl P M bs hRL
      (c k4 κ) (C k4 κ) _ _ _ _ (hC k4 κ) RE1 RE2'
    -- (R2) the contracta at the further restriction
    have T2 := ih k5 (κ.comp κ')
    rw [data_isub_comp] at T2
    have R2 := T2 (ρ.comp (κ.comp κ')) (by simp only [ISub.hom_comp]) rfl
      Q M' bs' hER (c k4 κ) (C k4 κ) _ _ _ _ (hC k4 κ) RE2' RE3
    -- the types
    have hPκ2 := RT2.isub hW (tyCode_of_univ hW hP) hPP (ρ.comp (κ.comp κ'))
    have R00 := RE2.trans hW hPκ2 R0 (RE2.symm hW hPκ2 R0)
    have C1 := RE2.trans hW hPκ2 (conP_rel hW hD hH hP hPP _ R00 (hC k4 κ) RE1) R0
    have C2 := conP_rel hW hD hH hP hPP _ (hxxs (κ.comp κ')) (hC k4 κ) RE2'
    have R1' := RE2.conv hW (hRL.mot k5 _ _ _ C1) R1
    have R2' := RE2.conv hW (hRL.mot k5 _ _ _ C2) R2
    have hTg := hRL.mot k5 _ _ _ (hxxs (κ.comp κ'))
    have hbs := (hER.tyL k4 (ρ.comp κ)).choose_spec.hbs
    show RE2 S k5 _ ((ecTm d (C k4 κ) (c k4 κ) (P.isub (ρ.comp κ)) (M.isub (ρ.comp κ)) (bs.isub (ρ.comp κ))
      (Z k4 κ)).isub κ') (ecTm d (C k5 (κ.comp κ')) (c k5 (κ.comp κ')) (Q.isub (ρ.comp (κ.comp κ')))
        (M'.isub (ρ.comp (κ.comp κ'))) (bs'.isub (ρ.comp (κ.comp κ'))) (Z' k5 (κ.comp κ')))
    rw [eT, ecTm_isub d (C k4 κ) (c k4 κ) hbs, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, eT3, hcc', hCC]
    exact RE2.trans hW hTg R1' R2'

/-- Eliminations of related elements of a literal inductive type, by induction on their relation. -/
theorem elim_DR2 {M bs : Tm} (hRL : ElimRel S d D K P M bs P M bs) : ∀ {k1 : ℕ} {g : Hom k1 K} {A x x' : Tm},
    DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 g A x x' →
    EM1 S d D K P M bs k1 g A x x' := by
  have hdD := dataD_eq hW hD
  intro k1 g A x x' h
  refine DR2.rec (motive_1 := fun k1 g A x x' _ => EM1 S d D K P M bs k1 g A x x')
    (motive_2 := fun k1 g A y y' _ => EM2 S d D K P M bs k1 g A y y') ?_ ?_ ?_ h
  · intro k1 g A x x' he h2 h3 h4 ih ihc _
    exact em1_intro hW hD hH hP hPP hRL (DR2.intro he h2 h3 h4) ih ihc
  · intro k1 g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec
    exact em2_con hW hD hH hP hPP (DR2At.con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt)
      hC hA ht ht' hl hl' ihrec
  · intro k1 g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH' _
    have : D.isHIT = true := hdD ▸ hH'
    rw [hH] at this; cases this

end lit

end

end Model.Whnf
