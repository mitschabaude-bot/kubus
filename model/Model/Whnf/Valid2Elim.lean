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
    rwa [getD_eq_get' hi, getD_eq_get' hi'] at this
  · obtain ⟨hjn, hjr⟩ := mem_recPos hj
    rw [getD_eq_get' (show j < args.length by omega),
      getD_eq_get' (show j < args'.length by omega)]
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

theorem CSub2.upL_restr {Ψ : ℕ} {Φ : I} {Γ : Ctx} (c : CSub2 S Ψ Φ Γ k) {k' : ℕ} (ρ : ISub k' k) (t : Tm) :
    t.subst (Tm.up (c.restr hW ρ).γ) (c.restr hW ρ).σ.τ = (t.subst (Tm.up c.γ) c.σ.τ).isub ρ := by
  simp only [CSub2.restr, Tm.isub, subst_subst, ISub.comp]
  apply subst_congr
  · intro x; cases x with
    | zero => rfl
    | succ x => exact (isub_shift (c.γ x) ρ).symm
  · intro i; rfl

theorem CSub2.upR_restr {Ψ : ℕ} {Φ : I} {Γ : Ctx} (c : CSub2 S Ψ Φ Γ k) {k' : ℕ} (ρ : ISub k' k) (t : Tm) :
    t.subst (Tm.up (c.restr hW ρ).γ') (c.restr hW ρ).σ'.τ = (t.subst (Tm.up c.γ') c.σ'.τ).isub ρ := by
  simp only [CSub2.restr, Tm.isub, subst_subst, ISub.comp]
  apply subst_congr
  · intro x; cases x with
    | zero => rfl
    | succ x => exact (isub_shift (c.γ' x) ρ).symm
  · intro i; rfl

section valid
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hD

/-- The premises of two eliminations with valid components, at a related substitution. -/
theorem elimRel_of {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' P P' bs bs' t t' T T' : Tm} {m : ℕ}
    (hty : HasTy0 S Ψ Φ Γ (.elim d ps P bs t) T) (hty' : HasTy0 S Ψ Φ Γ (.elim d ps' P' bs' t') T')
    (hps : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level))
    (hM : Valid2 S Ψ Φ (.data d ps :: Γ) P P' (.univ m))
    (hbr : ∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' → Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P))
    (c : CSub2 S Ψ Φ Γ k) :
    ElimRel S d D k (c.L ps) (P.subst (Tm.up c.γ) c.σ.τ) (c.L bs) (c.R ps') (P'.subst (Tm.up c.γ') c.σ'.τ) (c.R bs') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨D0, m0, hE0, -⟩ := gen_elimP hty rfl
  obtain ⟨D1, m1, hE1, -⟩ := gen_elimP hty' rfl
  have e0 : D0 = D := by have := hE0.hD; rw [hD] at this; cases this; rfl
  have e1 : D1 = D := by have := hE1.hD; rw [hD] at this; cases this; rfl
  rw [e0] at hE0; rw [e1] at hE1
  have hlen : ps.toList.length = D.params.length := by simpa using Meta.tele_length hE0.hpt
  refine ⟨fun k1 ρ => hps.tyRestr hW c ρ, fun k1 ρ x x' hx => ?_, fun k1 ρ cc C hC => ?_, fun k1 ρ => ?_,
    fun k1 ρ => ?_⟩
  · have ha : RE2 S k1 ((c.restr hW ρ).L (.data d ps)) x x' := by rw [CSub2.restr_L]; exact hx
    have := hM.ty hW ((c.restr hW ρ).ext hW (.data d ps) x x' ha
      (CSub2.tyRob_of hW (fun k c => hps.tySelf hW c) _))
    rw [subst_up_isub_inst, subst_up_isub_inst]
    exact this
  · have hcl : cc < D.ctors.length := (List.getElem?_eq_some_iff.1 hC).1
    obtain ⟨b, hb⟩ : ∃ b, bs.toList[cc]? = some b := ⟨_, List.getElem?_eq_getElem (by rw [hE0.hlen]; exact hcl)⟩
    obtain ⟨b', hb'⟩ : ∃ b, bs'.toList[cc]? = some b := ⟨_, List.getElem?_eq_getElem (by rw [hE1.hlen]; exact hcl)⟩
    have := ((hbr cc C b b' hC hb hb') k1 (c.restr hW ρ)).2
    have e := branchTy_subst hS hD hC hE0.hps hlen P (σ := (c.restr hW ρ).γ) (τ := (c.restr hW ρ).σ.τ)
    rw [show (c.restr hW ρ).L (D.branchTy d cc C ps P) = _ from e,
      show ps.subst (c.restr hW ρ).γ (c.restr hW ρ).σ.τ = (c.L ps).isub ρ from CSub2.restr_L hW c ρ ps,
      CSub2.upL_restr] at this
    have gL : ((c.L bs).isub ρ).toList.getD cc .abort = (c.restr hW ρ).L b := by
      rw [← CSub2.restr_L hW c ρ bs]
      show (bs.subst _ _).toList.getD cc .abort = _
      rw [toList_subst hE0.hbs]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hb]
    have gR : ((c.R bs').isub ρ).toList.getD cc .abort = (c.restr hW ρ).R b' := by
      rw [← CSub2.restr_R hW c ρ bs']
      show (bs'.subst _ _).toList.getD cc .abort = _
      rw [toList_subst hE1.hbs]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hb']
    rw [gL, gR]; exact this
  · have h := (c.restr hW ρ).ty hW hty
    obtain ⟨D'', m', hE', -⟩ := gen_elimP (spec_to_minimal hW h) rfl
    have hDD : D'' = D := by have := hE'.hD; rw [hD] at this; cases this; rfl
    rw [hDD] at hE'
    rw [show ps.subst (c.restr hW ρ).γ (c.restr hW ρ).σ.τ = (c.L ps).isub ρ from CSub2.restr_L hW c ρ ps,
      show bs.subst (c.restr hW ρ).γ (c.restr hW ρ).σ.τ = (c.L bs).isub ρ from CSub2.restr_L hW c ρ bs,
      CSub2.upL_restr] at hE'
    exact ⟨m', hE'⟩
  · have h := (c.restr hW ρ).tyR hW hty'
    obtain ⟨D'', m', hE', -⟩ := gen_elimP (spec_to_minimal hW h) rfl
    have hDD : D'' = D := by have := hE'.hD; rw [hD] at this; cases this; rfl
    rw [hDD] at hE'
    rw [show ps'.subst (c.restr hW ρ).γ' (c.restr hW ρ).σ'.τ = (c.R ps').isub ρ from CSub2.restr_R hW c ρ ps',
      show bs'.subst (c.restr hW ρ).γ' (c.restr hW ρ).σ'.τ = (c.R bs').isub ρ from CSub2.restr_R hW c ρ bs',
      CSub2.upR_restr] at hE'
    exact ⟨m', hE'⟩

/-- **Elimination** of an inductive type without path constructors, with valid components. -/
theorem valid_elim (hH : D.isHIT = false) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps ps' P P' bs bs' t t' : Tm} {m : ℕ}
    (hty : HasTy0 S Ψ Φ Γ (.elim d ps P bs t) (P.inst t)) (hty' : HasTy0 S Ψ Φ Γ (.elim d ps' P' bs' t') (P.inst t))
    (hps : Valid2 S Ψ Φ Γ (.data d ps) (.data d ps') (.univ D.level))
    (hM : Valid2 S Ψ Φ (.data d ps :: Γ) P P' (.univ m))
    (hbr : ∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' → Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P))
    (ht : Valid2 S Ψ Φ Γ t t' (.data d ps)) :
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps' P' bs' t') (P.inst t) := by
  obtain ⟨D0, m0, hE0, -⟩ := gen_elimP hty rfl
  obtain ⟨D1, m1, hE1, -⟩ := gen_elimP hty' rfl
  have e0 : D0 = D := by have := hE0.hD; rw [hD] at this; cases this; rfl
  have e1 : D1 = D := by have := hE1.hD; rw [hD] at this; cases this; rfl
  rw [e0] at hE0; rw [e1] at hE1
  have hpsL := valid_trans hW hps (valid_symm hW hps)
  have hML := valid_trans hW hM (valid_symm hW hM)
  have htL := valid_trans hW ht (valid_symm hW ht)
  have hbrL : ∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs.toList[c]? = some b' → Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P) := by
    intro cc C b b2 hC hb hb2
    rw [hb] at hb2; cases hb2
    have hcl : cc < D.ctors.length := (List.getElem?_eq_some_iff.1 hC).1
    obtain ⟨b', hb'⟩ : ∃ b, bs'.toList[cc]? = some b := ⟨_, List.getElem?_eq_getElem (by rw [hE1.hlen]; exact hcl)⟩
    have h := hbr cc C b b' hC hb hb'
    exact valid_trans hW h (valid_symm hW h)
  intro k c
  have hRL : ElimRel S d D k (c.L ps) (P.subst (Tm.up c.γ) c.σ.τ) (c.L bs) (c.L ps) (P.subst (Tm.up c.γ) c.σ.τ)
      (c.L bs) := elimRel_of hW hD hty hty hpsL hML hbrL (c.diagL hW)
  have hER := elimRel_of hW hD hty hty' hps hM hbr c
  have hP : HasTy S k .one [] (.data d (c.L ps)) (.univ D.level) := c.ty hW hE0.hdata
  have hPP : RT2 S k (.data d (c.L ps)) (.data d (c.L ps)) := hpsL.ty hW (c.diagL hW)
  have hx : RE2 S k (.data d (c.L ps)) (c.L t) (c.R t') := (ht k c).2
  have hpc : (c.L ps).closedB 0 k = true := by
    have := closed_of_ty hW hP; simpa [Tm.closedB] using this
  have hx' : RE2 S k (.data d ((c.L ps).isub (ISub.id k))) (c.L t) (c.R t') := by
    rw [isub_id_of_closed hpc]; exact hx
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP (ISub.id k)).1 hx'
  have T := elim_DR2 hW hD hH hP hPP hRL hdr (ISub.id k) rfl rfl _ _ _ hER
  have hcl := closed_of_ty hW (c.ty hW hty)
  have hcl' := closed_of_ty hW (c.tyR hW hty')
  simp only [CSub2.L, CSub2.R, Tm.subst, Tm.closedB, Bool.and_eq_true] at hcl hcl'
  rw [isub_id_of_closed hpc, isub_id_of_closed hcl.1.1.2, isub_id_of_closed hcl.1.2,
    isub_id_of_closed hcl'.1.1.1, isub_id_of_closed hcl'.1.1.2, isub_id_of_closed hcl'.1.2] at T
  refine ⟨?_, ?_⟩
  · have := hML.ty hW (c.ext hW (.data d ps) (c.L t) (c.R t) (htL k c).2
      (CSub2.tyRob_of hW (fun k c => hpsL.tySelf hW c) _))
    show RT2 S k ((P.inst t).subst c.γ c.σ.τ) ((P.inst t).subst c.γ' c.σ'.τ)
    rw [inst_subst_consT, inst_subst_consT]
    exact this
  · show RE2 S k ((P.inst t).subst c.γ c.σ.τ) _ _
    rw [inst_subst]
    exact T

omit hD in
/-- A computation rule, from a derivation of the equation: the right instances of `t` reduce to those
of `u`. -/
theorem valid_redE {Ψ : ℕ} {Φ : I} {Γ : Ctx} {t u T : Tm} (h : Valid2 S Ψ Φ Γ t t T) (hu : HasTy0 S Ψ Φ Γ u T)
    (heq : EqTm0 S Ψ Φ Γ t u T) (hr : ∀ k (c : CSub2 S Ψ Φ Γ k), Red S (c.R t) (c.R u)) :
    Valid2 S Ψ Φ Γ t u T := by
  refine valid_redR hW h hu fun k c k' σ => ?_
  rw [← CSub2.restr_R hW c σ, ← CSub2.restr_R hW c σ, ← CSub2.restr_L hW c σ]
  refine ⟨hr k' (c.restr hW σ), ?_⟩
  have e : EqTm S k' .one [] ((c.restr hW σ).R t) ((c.restr hW σ).R u) ((c.restr hW σ).R T) :=
    ((c.restr hW σ).diagR hW).eq hW heq
  exact e.tyConv (TyEq.symm (Comp2_ty_base (h k' (c.restr hW σ)).1).2.2.2.2.2)

/-- **Elimination of a constructor** of an inductive type without path constructors. -/
theorem valid_elimCon (hH : D.isHIT = false) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {c : ℕ} {C : Ctor} {ps P bs b qs args : Tm}
    {rs : List I} {T : Tm} (hC : D.ctors[c]? = some C) (hb : bs.toList[c]? = some b)
    (hal : args = Tm.ofList args.toList) (hbl : bs = Tm.ofList bs.toList)
    (hty : HasTy0 S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs)) T)
    (hu : HasTy0 S Ψ Φ Γ (Tm.papps (Tm.apps b (args.toList ++
      C.recPos.map fun k => .elim d ps P bs (args.toList.getD k .abort))) rs) T)
    (heq : EqTm0 S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs)) (Tm.papps (Tm.apps b (args.toList ++
      C.recPos.map fun k => .elim d ps P bs (args.toList.getD k .abort))) rs) T)
    (h : Valid2 S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs)) (.elim d ps P bs (.con d c qs args rs)) T) :
    Valid2 S Ψ Φ Γ (.elim d ps P bs (.con d c qs args rs))
      (Tm.papps (Tm.apps b (args.toList ++
        C.recPos.map fun k => .elim d ps P bs (args.toList.getD k .abort))) rs) T := by
  obtain ⟨-, -, -, hx⟩ := gen_elimP hty rfl
  obtain ⟨D1, C1, hD1, hC1, -, -, -, hrs⟩ := gen_con hx rfl
  rw [hD] at hD1; cases hD1
  rw [hC] at hC1; cases hC1
  rw [dims_of_not_hit hH hC, List.length_eq_zero_iff] at hrs
  subst hrs
  refine valid_redE hW h hu heq fun k c' => ?_
  have hX : c'.R args = Tm.ofList (args.toList.map c'.R) := by
    conv_lhs => rw [hal]
    exact ofList_subst _ _ _
  have hb' : (c'.R bs).toList[c]? = some (c'.R b) := by
    show (bs.subst _ _).toList[c]? = _
    rw [toList_subst hbl, List.getElem?_map, hb]; rfl
  have hs := step_elimCon hD hH hC (ps := c'.R ps) (M := P.subst (Tm.up c'.γ') c'.σ'.τ) (qs := c'.R qs)
    (X := args.toList.map c'.R) hb'
  rw [← hX] at hs
  refine .step hs ?_
  suffices e : Tm.apps (c'.R b) (args.toList.map c'.R ++
      ihsOf d C (c'.R ps) (P.subst (Tm.up c'.γ') c'.σ'.τ) (c'.R bs) (args.toList.map c'.R)) =
      (Tm.apps b (args.toList ++ C.recPos.map fun k => .elim d ps P bs (args.toList.getD k .abort))).subst c'.γ' c'.σ'.τ by
    rw [e]; exact .refl _
  rw [apps_subst, List.map_append, List.map_map]
  congr 2
  simp only [ihsOf, List.map_map]
  congr 1; funext j
  simp only [Function.comp]
  show Tm.elim d _ _ _ _ = Tm.elim d _ _ _ _
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases args.toList[j]? <;> rfl

/-- **Transport in an inductive type without parameters** is the identity. -/
theorem valid_transpData0 (hp : D.params = []) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps a T : Tm} {φ : I}
    (hu : HasTy0 S Ψ Φ Γ a T) (heq : EqTm0 S Ψ Φ Γ (.transp (.data d ps) φ a) a T)
    (h : Valid2 S Ψ Φ Γ (.transp (.data d ps) φ a) (.transp (.data d ps) φ a) T) :
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ a) a T := by
  refine valid_redE hW h hu heq fun k c => .step ?_ (.refl _)
  simp only [CSub2.R, Tm.subst, step]
  split
  · rfl
  · simp [hD, hp]

end valid


end

end Model.Whnf
