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

end lit

end

end Model.Whnf
