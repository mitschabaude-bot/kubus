import KubusCore.Meta.TranspCon
import KubusCore.Meta.KanTranspGlueAux

/-!
# Metatheory: typing the contractum of `hcompCon`

Composition in an inductive type without path constructors, componentwise (`Tm.hcompTele`):
recursive arguments by `hcomp`/`hfill` in the inductive type, point arguments by `comp`/`fill`
along their type lines, which are typed by the point argument clause of `DataDecl.Wf` over the
prefix signature (P11), carried to `S` by `htr`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## The fillers of `hcompTele` -/

/-- The fillers of the first `k` arguments (in order). -/
def hFills (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) : Nat → List Tm
  | 0 => []
  | k + 1 => hFills C A dT psL φ us as k ++
      [if C.isRec k then hfill dT φ (us.getD k .abort) (as.getD k .abort)
       else fill ((A k).substList ((hFills C A dT psL φ us as k).reverse ++ psL.reverse)) φ
         (us.getD k .abort) (as.getD k .abort)]

/-- The type line of (point) argument `k`. -/
def hLine (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) (k : Nat) : Tm :=
  (A k).substList ((hFills C A dT psL φ us as k).reverse ++ psL.reverse)

/-- The filler of argument `k`. -/
def hFill (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) (k : Nat) : Tm :=
  if C.isRec k then hfill dT φ (us.getD k .abort) (as.getD k .abort)
  else fill (hLine C A dT psL φ us as k) φ (us.getD k .abort) (as.getD k .abort)

/-- The composite of argument `k`. -/
def hOut (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm) (k : Nat) : Tm :=
  if C.isRec k then hcomp dT φ (us.getD k .abort) (as.getD k .abort)
  else comp (hLine C A dT psL φ us as k) φ (us.getD k .abort) (as.getD k .abort)

section
variable (C : Ctor) (A : Nat → Tm) (dT : Tm) (psL : List Tm) (φ : I) (us as : List Tm)

theorem hFills_succ (k : Nat) :
    hFills C A dT psL φ us as (k + 1) = hFills C A dT psL φ us as k ++ [hFill C A dT psL φ us as k] :=
  rfl

theorem hFills_length : ∀ k, (hFills C A dT psL φ us as k).length = k
  | 0 => rfl
  | k + 1 => by rw [hFills_succ, List.length_append, hFills_length k]; rfl

theorem hFills_take (k : Nat) :
    ∀ m, (hFills C A dT psL φ us as (k + m)).take k = hFills C A dT psL φ us as k
  | 0 => by rw [Nat.add_zero, List.take_of_length_le (by rw [hFills_length]; exact Nat.le_refl _)]
  | m + 1 => by
    rw [← Nat.add_assoc, hFills_succ, List.take_append_of_le_length (by rw [hFills_length]; omega)]
    exact hFills_take k m

theorem hFills_get {k n : Nat} (h : k < n) :
    (hFills C A dT psL φ us as n).getD k .abort = hFill C A dT psL φ us as k := by
  have := hFills_take C A dT psL φ us as (k + 1) (n - (k + 1))
  rw [show k + 1 + (n - (k + 1)) = n by omega, hFills_succ] at this
  have hl := hFills_length C A dT psL φ us as n
  rw [List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt (j := k + 1) (by omega), this,
    List.getElem?_append_right (by rw [hFills_length]; exact Nat.le_refl _), hFills_length]
  simp

theorem hcompTele_eq :
    ∀ (us' as' : List Tm) (k : Nat), us.drop k = us' → as.drop k = as' → us'.length = as'.length →
    Tm.hcompTele C A dT psL φ k (hFills C A dT psL φ us as k).reverse us' as' =
      (List.range' k as'.length).map (hOut C A dT psL φ us as)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hl | _ :: _, [], _, _, _, hl => by simp at hl
  | u :: us', a :: as', k, hu, ha, hl => by
    have hu0 : us.getD k .abort = u := by
      have := congrArg (fun l => l[0]?) hu
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      rw [List.getD_eq_getElem?_getD, this]; rfl
    have ha0 : as.getD k .abort = a := by
      have := congrArg (fun l => l[0]?) ha
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      rw [List.getD_eq_getElem?_getD, this]; rfl
    have hu1 : us.drop (k + 1) = us' := by rw [← List.drop_drop, hu]; rfl
    have ha1 : as.drop (k + 1) = as' := by rw [← List.drop_drop, ha]; rfl
    have ih := hcompTele_eq us' as' (k + 1) hu1 ha1 (by simpa using hl)
    rw [hFills_succ, List.reverse_append] at ih
    simp only [List.length_cons, List.range'_succ, List.map_cons]
    unfold hFill hOut hLine at *
    rw [hu0, ha0] at ih ⊢
    cases hr : C.isRec k <;> simp only [Tm.hcompTele, hr, if_true, if_false, Bool.false_eq_true] <;>
      simp only [hr, if_true, if_false, Bool.false_eq_true, List.reverse_cons, List.reverse_nil, List.nil_append] at ih <;>
      exact congrArg _ ih

end

/-! ## Componentwise equality of argument telescopes -/

theorem data_paramVars_substList {ps : Tm} (hps : IsList ps) {np : Nat} (hlen : ps.toList.length = np)
    {L : List Tm} {k : Nat} (hL : L.length = k) (d : Nat) :
    (data d (Ctor.paramVars np k)).substList (L ++ ps.toList.reverse) = data d ps := by
  rw [substList_eq]; simp only [Tm.subst]
  rw [← substList_eq, paramVars_substList hps hlen hL]

theorem eqtele_get_ne {Ψ Φ Γ} : ∀ {ts ts' Δ prev}, EqTele0 S Ψ Φ Γ ts ts' Δ prev → prev ≠ [] →
    ∀ (k : Nat) (a a' A : Tm), ts.toList[k]? = some a → ts'.toList[k]? = some a' → Δ[k]? = some A →
    EqTm0 S Ψ Φ Γ a a' (A.substList ((ts.toList.take k).reverse ++ prev))
  | _, _, _, _, .nil _, _ => fun k a a' A h => by simp [Tm.toList] at h
  | _, _, _, _, .cons h0 h1, _ => fun k a a' A ha ha' hA => by
    cases k with
    | zero =>
      simp only [Tm.toList, List.getElem?_cons_zero, Option.some.injEq] at ha ha' hA
      subst ha; subst ha'; subst hA; simpa using h0
    | succ k =>
      simp only [Tm.toList, List.getElem?_cons_succ] at ha ha' hA
      have := eqtele_get_ne h1 (by simp) k a a' A ha ha' hA
      simpa [Tm.toList, List.take_succ_cons] using this
  | _, _, _, _, .dataInj .., hne => absurd rfl hne

section
variable (hS : SigClosed S) (hW : WfSig S) {d : Nat}
  (htr : ∀ {Ψ' Φ' Γ' t A}, HasTy (S.take d) Ψ' Φ' Γ' t A → HasTy0 S Ψ' Φ' Γ' t A)
  {D : DataDecl} {c : Nat} {C : Ctor} (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
include hS hW htr hD hC

/-- Without parameters, a telescope equality may come from injectivity of an inductive type
whose parameter telescope is the argument telescope; its components are then equal by
injectivity at each position, the types agreeing by functionality of the point argument types. -/
theorem eqtele_get_inj {Ψ Φ Γ} {ps ts ts' : Tm} {d' : Nat} {D' : DataDecl} {l : Nat}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (hp0 : ps.toList = [])
    (hpt : HasTele0 S Ψ Φ Γ ps D.params []) (hts : IsList ts) (hts' : IsList ts')
    (hD' : S[d']? = some (.data D')) (hΔ : D'.params = C.argTys d D.params.length)
    (hp : HasTele0 S Ψ Φ Γ ts D'.params []) (hp' : HasTele0 S Ψ Φ Γ ts' D'.params [])
    (e : EqTm0 S Ψ Φ Γ (data d' ts) (data d' ts') (univ l)) :
    ∀ k, k ≤ C.args.length →
    EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C ts.toList ps.toList.reverse k) 0) I.var
      (lsub (ptL C ts'.toList ps.toList.reverse k) 0) I.var ∧
    ∀ j, j < k → ∀ (a a' A : Tm), ts.toList[j]? = some a → ts'.toList[j]? = some a' →
      (C.argTys d D.params.length)[j]? = some A →
      EqTm0 S Ψ Φ Γ a a' (A.substList ((ts.toList.take j).reverse ++ ps.toList.reverse)) := by
  have hw := wf_of_tele hpt
  have hR : ps.toList.reverse = [] := by rw [hp0]; rfl
  have hat : HasTele0 S Ψ Φ Γ ts (C.argTys d D.params.length) ps.toList.reverse := by
    rw [hR, ← hΔ]; exact hp
  have hat' : HasTele0 S Ψ Φ Γ ts' (C.argTys d D.params.length) ps.toList.reverse := by
    rw [hR, ← hΔ]; exact hp'
  have hal : ts.toList.length = C.args.length := by
    have := tele_length hat; rwa [argTys_length] at this
  have hal' : ts'.toList.length = C.args.length := by
    have := tele_length hat'; rwa [argTys_length] at this
  have h0 : ∀ (τ σ : Nat → _), TySub S 0 .one [] Ψ Φ Γ σ τ :=
    fun τ σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
  have hP0 := tySub_params hS hD hpt 0 (h0 I.var) _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hP0
  intro k hk
  induction k with
  | zero =>
    simp only [ptL, DataDecl.pointCtx, List.range_zero, List.filter_nil, List.map_nil, List.reverse_nil,
      List.nil_append]
    exact ⟨EqSub.of_eq hP0 (fun _ => rfl), fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨E, Tel⟩ := ih (by omega)
    have hkn : k < C.args.length := by omega
    have TA := tySub_points hS hW hD hC hP0 hat hpl k (by omega)
    have TA' := tySub_points hS hW hD hC hP0 hat' hpl k (by omega)
    have hak : ts.toList[k]? = some (ts.toList.getD k .abort) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hak' : ts'.toList[k]? = some (ts'.toList.getD k .abort) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hA : D'.params[k]? = some (C.argTy d D.params.length k) := by rw [hΔ]; exact argTys_get hkn
    have p1 := tele_get hat k _ _ hak (argTys_get hkn)
    have p2 := tele_get hat' k _ _ hak' (argTys_get hkn)
    -- the equality at position `k`, and its type
    have key : EqTm0 S Ψ Φ Γ (ts.toList.getD k .abort) (ts'.toList.getD k .abort)
        ((C.argTy d D.params.length k).substList ((ts.toList.take k).reverse ++ ps.toList.reverse)) ∧
        (C.isRec k = false → ∃ A0, C.args[k]? = some (.point A0) ∧
          C.argTy d D.params.length k = A0) := by
      cases hr : C.isRec k
      · obtain ⟨A0, hA0⟩ := point_of_not_rec hkn hr
        have hAk : C.argTy d D.params.length k = A0 := by simp [Ctor.argTy, hA0]
        refine ⟨?_, fun _ => ⟨A0, hA0, hAk⟩⟩
        have hP := pt_typed hW htr hD hC hA0
        have F := (sub_ty hS hP).2.2 TA TA' E
        rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var,
          pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var] at F
        rw [hAk] at p1 p2
        have p2' := HasTy0.conv p2 (EqTm0.symm F)
        rw [hR, List.append_nil] at p1 p2' ⊢
        rw [hAk]
        exact EqTm0.dataInjAt hD' hts hts' e hak hak' (by rw [hA, hAk]) p1 p2'
      · refine ⟨?_, fun h => by simp at h⟩
        have hAk : C.argTy d D.params.length k = data d (Ctor.paramVars D.params.length k) := argTy_rec' hr
        rw [hAk, data_paramVars_substList hps hpl (k := k) (by simp; omega)] at p1 p2 ⊢
        have eq : (data d (Ctor.paramVars D.params.length k)).substList (ts.toList.take k).reverse = data d ps := by
          have := data_paramVars_substList (L := (ts.toList.take k).reverse) hps hpl (k := k) (by simp; omega) d
          rwa [hR, List.append_nil] at this
        rw [← eq] at p1 p2 ⊢
        exact EqTm0.dataInjAt hD' hts hts' e hak hak' (by rw [hA, hAk]) p1 p2
    obtain ⟨hkey, hpt'⟩ := key
    refine ⟨?_, fun j hj a a' A ha ha' hA' => ?_⟩
    · rw [pointCtx_succ]
      cases hr : C.isRec k
      · simp only [hr, Bool.false_eq_true, if_false, ptL]
        obtain ⟨A0, hA0, hAk⟩ := hpt' hr
        have := E.cons (A := A0.ren (C.pointRen k) id) (a1 := ts.toList.getD k .abort)
          (a2 := ts'.toList.getD k .abort)
          (by rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var, ← hAk]; exact hkey)
        rw [consT_lsub, consT_lsub] at this; rw [hAk]; exact this
      · simp only [hr, if_true, ptL]; exact E
    · by_cases hjk : j = k
      · subst hjk
        rw [hak] at ha; rw [hak'] at ha'; rw [argTys_get hkn] at hA'
        cases ha; cases ha'; cases hA'; exact hkey
      · exact Tel j (by omega) a a' A ha ha' hA'

theorem eqtele_get_args {Ψ Φ Γ} {ps ts ts' : Tm}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length)
    (hpt : HasTele0 S Ψ Φ Γ ps D.params []) (hts : IsList ts) (hts' : IsList ts')
    (h : EqTele0 S Ψ Φ Γ ts ts' (C.argTys d D.params.length) ps.toList.reverse) :
    ∀ (k : Nat) (a a' A : Tm), ts.toList[k]? = some a → ts'.toList[k]? = some a' →
      (C.argTys d D.params.length)[k]? = some A →
      EqTm0 S Ψ Φ Γ a a' (A.substList ((ts.toList.take k).reverse ++ ps.toList.reverse)) := by
  by_cases hne : ps.toList.reverse ≠ []
  · exact eqtele_get_ne h hne
  have hR : ps.toList.reverse = [] := Classical.not_not.1 hne
  have hp0 : ps.toList = [] := by simpa using hR
  intro k a a' A ha ha' hA
  generalize hΔ : C.argTys d D.params.length = Δ at h hA
  generalize hprev : ps.toList.reverse = prev at h hR ⊢
  subst hR
  cases h with
  | nil => simp [Tm.toList] at ha
  | cons h0 h1 =>
    cases k with
    | zero =>
      simp only [Tm.toList, List.getElem?_cons_zero, Option.some.injEq] at ha ha' hA
      subst ha; subst ha'; subst hA; simpa using h0
    | succ k =>
      simp only [Tm.toList, List.getElem?_cons_succ] at ha ha' hA
      have := eqtele_get_ne h1 (by simp) k a a' A ha ha' hA
      simpa [Tm.toList, List.take_succ_cons] using this
  | dataInj hD' hp hp' e =>
    have hk : k < C.args.length := by
      have := (List.getElem?_eq_some_iff.1 hA).1
      rw [← hΔ, argTys_length] at this; exact this
    have := (eqtele_get_inj hS hW htr hD hC hps hpl hp0 hpt hts hts' hD' hΔ.symm hp hp' e (k + 1) hk).2 k
      (Nat.lt_succ_self k) a a' A ha ha' (by rw [hΔ]; exact hA)
    rwa [hprev] at this

/-! ## The induction along the arguments -/

variable {Ψ : Nat} {Φ : I} {Γ : Ctx} {ps uargs args : Tm} {φ : I} {l0 : Nat}
  (hps : ps = Tm.ofList ps.toList) (hargs : args = Tm.ofList args.toList)
  (huargs : uargs = Tm.ofList uargs.toList)
  (h6 : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
  (h7 : HasTele0 S (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length)
    ps.dshift.toList.reverse)
  (h9 : EqTele0 S Ψ (KubusCore.cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length)
    ps.toList.reverse)
  (hdT : HasTy0 S Ψ Φ Γ (data d ps) (Tm.univ l0)) (hφ : φ.Scoped Ψ)
include hps hargs huargs h6 h7 h9 hdT hφ

/-- The invariant after `k` arguments: the fillers and the composites as substitutions out of
the point context, related to the base and tube arguments, and the composites typed so far. -/
theorem hcompCon_inv :
    let A := C.argTy d D.params.length
    let us := uargs.toList
    let as := args.toList
    let R := ps.toList.reverse
    let R1 := ps.dshift.toList.reverse
    let Fall := hFills C A (data d ps) ps.dshift.toList φ us as C.args.length
    let osAll := (List.range C.args.length).map (hOut C A (data d ps) ps.dshift.toList φ us as)
    ∀ k, k ≤ C.args.length →
    TySub S 0 .one (D.pointCtx d C k) (Ψ + 1) Φ.shift Γ.dshift (lsub (ptL C Fall R1 k) 0) I.var ∧
    TySub S 0 .one (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C osAll R k) 0) I.var ∧
    EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ
      (fun x => (lsub (ptL C Fall R1 k) 0 x).subst Tm.var (I.inst0 .zero))
      (fun i => (I.var i).subst (I.inst0 .zero))
      (lsub (ptL C as R k) 0) I.var ∧
    EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ
      (fun x => (lsub (ptL C Fall R1 k) 0 x).subst Tm.var (I.inst0 .one))
      (fun i => (I.var i).subst (I.inst0 .one))
      (lsub (ptL C osAll R k) 0) I.var ∧
    EqSub S 0 (D.pointCtx d C k) (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift
      (lsub (ptL C Fall R1 k) 0) I.var (lsub (ptL C us R1 k) 0) I.var ∧
    (∀ j, j < k → HasTy0 S Ψ Φ Γ (osAll.getD j .abort) ((A j).substList ((osAll.take j).reverse ++ R))) := by
  intro A us as R R1 Fall osAll k hk
  -- common facts
  have hw : Wf0 S Ψ Φ Γ := wf_of_tele h6
  have hs : Φ.Scoped Ψ := scoped_of_wf hw
  have hXs : (KubusCore.cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ⟩
  have hXe : I.Entails (KubusCore.cof Φ φ).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hcs : (KubusCore.cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hce : I.Entails (KubusCore.cof Φ φ) Φ := ent_and_left _ _
  have hw1 : Wf0 S (Ψ + 1) Φ.shift Γ.dshift := wf_of_ty (HasTy0.dwk hS hdT)
  have hwc : Wf0 S (Ψ + 1) (KubusCore.cof Φ φ).shift Γ.dshift := hw1.restrict hXs hXe
  obtain ⟨D', hD', hpt⟩ := gen_data_tele hdT rfl
  rw [hD] at hD'; cases hD'
  have hpl : ps.toList.length = D.params.length := by simpa using tele_length hpt
  have hf : ∀ (r : I), r.Scoped Ψ → ∀ t B, HasTy0 S (Ψ + 1) Φ.shift Γ.dshift t B →
      HasTy0 S Ψ Φ Γ (t.subst Tm.var (I.inst0 r)) (B.subst Tm.var (I.inst0 r)) :=
    fun r hr t B h => HasTy0.dsubst hS h hr
  have hps1 : IsList ps.dshift := by rw [dshift_eq]; exact isList_subst hps _ _
  have hpt1 : HasTele0 S (Ψ + 1) Φ.shift Γ.dshift ps.dshift D.params [] := by
    have := HasTele0.post (fun i => .var (i + 1)) hw1
      (fun t B h => by rw [← dshift_eq, ← dshift_eq]; exact HasTy0.dwk hS h) hpt (params_closed hS hD)
    rw [← dshift_eq] at this; simpa using this
  have hpl1 : ps.dshift.toList.length = D.params.length := by simpa using tele_length hpt1
  have hdsh : ∀ r, R1.map (·.subst Tm.var (I.inst0 r)) = R := by
    intro r
    show (ps.dshift.toList.reverse).map _ = _
    rw [List.map_reverse, ← toList_subst hps1, dinst_eq, dshift_dinst]
  have h0 : ∀ {Ψ' Φ' Γ'} (τ σ : Nat → _), Wf0 S Ψ' Φ' Γ' → TySub S 0 .one [] Ψ' Φ' Γ' σ τ :=
    fun τ σ hw' => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw'
  have hP0 := tySub_params hS hD hpt 0 (h0 I.var · hw) _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hP0
  have hP1 := tySub_params hS hD hpt1 0 (h0 I.var · hw1) _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hP1
  have hpc : D.pointCtx d C 0 = D.paramCtx D.params.length := by simp [DataDecl.pointCtx]
  induction k with
  | zero =>
    simp only [ptL, hpc]
    refine ⟨hP1, hP0, ?_, ?_, EqSub.of_eq (hP1.restrict hXs hXe) (fun _ => rfl),
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · exact EqSub.of_eq (hP1.post _ hw (hf .zero trivial)) (fun x => by rw [lsub_post, hdsh])
    · exact EqSub.of_eq (hP1.post _ hw (hf .one trivial)) (fun x => by rw [lsub_post, hdsh])
  | succ k ih =>
    have hkn : k < C.args.length := by omega
    obtain ⟨T1, TO, E0, E1, Ec, Tel⟩ := ih (by omega)
    have hal : as.length = C.args.length := by
      have := tele_length h6; rwa [argTys_length] at this
    have hul : us.length = C.args.length := by
      have := tele_length h7; rwa [argTys_length] at this
    have hal' : args.toList.length = C.args.length := hal
    have hul' : uargs.toList.length = C.args.length := hul
    have hFl : Fall.length = C.args.length := hFills_length _ _ _ _ _ _ _ _
    have hFt : Fall.take k = hFills C A (data d ps) ps.dshift.toList φ us as k := by
      have := hFills_take C A (data d ps) ps.dshift.toList φ us as k (C.args.length - k)
      rwa [show k + (C.args.length - k) = C.args.length by omega] at this
    have hLk : hLine C A (data d ps) ps.dshift.toList φ us as k =
        (A k).substList ((Fall.take k).reverse ++ R1) := by rw [hFt]; rfl
    have hFk : Fall.getD k .abort = hFill C A (data d ps) ps.dshift.toList φ us as k :=
      hFills_get C A (data d ps) ps.dshift.toList φ us as hkn
    have hOk : osAll.getD k .abort = hOut C A (data d ps) ps.dshift.toList φ us as k := by
      simp only [osAll, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkn]; rfl
    have hOl : osAll.length = C.args.length := by simp [osAll]
    have hak : as[k]? = some (as.getD k .abort) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have huk : us[k]? = some (us.getD k .abort) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hatk := tele_get h6 k _ _ hak (argTys_get hkn)
    have hutk := tele_get h7 k _ _ huk (argTys_get hkn)
    -- the side condition, componentwise
    have hu0 : IsList (uargs.dinst .zero) := isList_subst huargs _ _
    have hu0l : (uargs.dinst .zero).toList = us.map (·.subst Tm.var (I.inst0 .zero)) :=
      toList_subst huargs _ _
    have hu0k : (uargs.dinst .zero).toList[k]? = some ((us.getD k .abort).dinst .zero) := by
      rw [hu0l, List.getElem?_map, huk]; rfl
    have hside := eqtele_get_args hS hW htr hD hC hps hpl (hpt.restrict hcs hce) hu0 hargs h9 k _ _ _
      hu0k hak (argTys_get hkn)
    have hcl := argTy_closed hS hD hC k
    have hsl : (A k).substList (((uargs.dinst .zero).toList.take k).reverse ++ R) =
        ((A k).substList ((us.take k).reverse ++ R1)).dinst .zero := by
      have hlen : ((us.take k).reverse ++ R1).length = D.params.length + k := by
        simp [R1, hpl1]; omega
      show _ = ((A k).substList _).subst Tm.var (I.inst0 .zero)
      rw [substList_subst (by rw [hlen]; exact hcl),
        List.map_append, hdsh, hu0l, ← List.map_take, ← List.map_reverse]
    rw [hsl] at hside
    have hTel : ∀ j, j < k + 1 → j ≠ k → HasTy0 S Ψ Φ Γ (osAll.getD j .abort)
        ((A j).substList ((osAll.take j).reverse ++ R)) :=
      fun j hj hjk => Tel j (by omega)
    rw [pointCtx_succ]
    cases hr : C.isRec k
    · simp only [hr, Bool.false_eq_true, if_false, ptL]
      obtain ⟨A0, hA0⟩ := point_of_not_rec hkn hr
      have hAk : C.argTy d D.params.length k = A0 := by simp [Ctor.argTy, hA0]
      rw [hAk]
      have hP := pt_typed hW htr hD hC hA0
      have hpost : ∀ (σ : Nat → Tm) (τ' : Nat → I),
          (A0.ren (C.pointRen k) id).subst (fun x => (σ x).subst Tm.var τ') (fun i => (I.var i).subst τ') =
            ((A0.ren (C.pointRen k) id).subst σ I.var).subst Tm.var τ' :=
        fun σ τ' => (subst_subst _ _ _ _ _).symm
      have hLeq : (A0.ren (C.pointRen k) id).subst (lsub (ptL C Fall R1 k) 0) I.var =
          hLine C A (data d ps) ps.dshift.toList φ us as k := by
        rw [pt_inst hW hD hC hA0 (by omega) (by simp [R1, hpl1]) 0 I.var, hLk]
        show _ = (C.argTy d D.params.length k).substList _
        rw [hAk]
      have hLt : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (hLine C A (data d ps) ps.dshift.toList φ us as k)
          (Tm.univ D.level) := by
        have := (sub_ty hS hP).2.1 T1; rw [hLeq] at this; exact this
      -- the tube argument, typed in the line
      have hP1c := hP1.restrict hXs hXe
      have TU := tySub_points hS hW hD hC hP1c h7 hpl1 k (by omega)
      have ecL := (sub_ty hS hP).2.2 (T1.restrict hXs hXe) TU Ec
      rw [hLeq, pt_inst hW hD hC hA0 (by omega) (by simp [hpl1]) 0 I.var] at ecL
      rw [hAk] at hutk hatk
      rw [show A k = A0 from hAk] at hside
      have hu := HasTy0.conv hutk (EqTm0.symm ecL)
      -- the base argument, typed at the start of the line
      have TA := tySub_points hS hW hD hC hP0 h6 hpl k (by omega)
      have T10 := T1.post (I.inst0 .zero) hw (hf .zero trivial)
      have e0 := (sub_ty hS hP).2.2 T10 TA E0
      rw [hpost, hLeq, pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var] at e0
      have ha := HasTy0.conv hatk (EqTm0.symm e0)
      -- the side condition, in the line
      have ecL0 := EqTm0.dsubst hS ecL (r := .zero) trivial
      have hside' := EqTm0.conv hside (EqTm0.symm ecL0)
      have hTF := fill_typed hS hLt hφ hu ha hside'
      have hout := comp_typed hS hLt hφ hu ha hside'
      have T11 := T1.post (I.inst0 .one) hw (hf .one trivial)
      have e1 := (sub_ty hS hP).2.2 T11 TO E1
      rw [hpost, hLeq] at e1
      have hout' := HasTy0.conv hout e1
      have hFk' : Fall.getD k .abort = fill (hLine C A (data d ps) ps.dshift.toList φ us as k) φ
          (us.getD k .abort) (as.getD k .abort) := by rw [hFk]; simp [hFill, hr]
      have hOk' : osAll.getD k .abort = comp (hLine C A (data d ps) ps.dshift.toList φ us as k) φ
          (us.getD k .abort) (as.getD k .abort) := by rw [hOk]; simp [hOut, hr]
      refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
      · have := T1.cons (A := A0.ren (C.pointRen k) id) (a := Fall.getD k .abort) (by rw [hLeq, hFk']; exact hTF.1)
        rw [consT_lsub] at this; exact this
      · have := TO.cons (A := A0.ren (C.pointRen k) id) (a := osAll.getD k .abort) (by rw [hOk']; exact hout')
        rw [consT_lsub] at this; exact this
      · have := E0.cons (A := A0.ren (C.pointRen k) id) (a1 := (Fall.getD k .abort).subst Tm.var (I.inst0 .zero))
          (a2 := as.getD k .abort) (by rw [hpost, hLeq, hFk']; exact hTF.2.1)
        simp only [consT_post, consT_lsub] at this; exact this
      · have := E1.cons (A := A0.ren (C.pointRen k) id) (a1 := (Fall.getD k .abort).subst Tm.var (I.inst0 .one))
          (a2 := osAll.getD k .abort) (by rw [hpost, hLeq, hFk', hOk']; exact hTF.2.2.1)
        simp only [consT_post, consT_lsub] at this; exact this
      · have := Ec.cons (A := A0.ren (C.pointRen k) id) (a1 := Fall.getD k .abort)
          (a2 := us.getD k .abort) (by rw [hLeq, hFk']; exact hTF.2.2.2)
        rw [consT_lsub, consT_lsub] at this; exact this
      · by_cases hjk : j = k
        · subst hjk
          rw [pt_inst hW hD hC hA0 (by simp [hOl]; omega) (by simp [R, hpl]) 0 I.var] at hout'
          show HasTy0 S Ψ Φ Γ _ ((C.argTy d D.params.length j).substList _)
          rw [hAk, hOk']; exact hout'
        · exact hTel j hj hjk
    · simp only [hr, if_true, ptL]
      refine ⟨T1, TO, E0, E1, Ec, fun j hj => ?_⟩
      by_cases hjk : j = k
      · subst hjk
        have hAk : C.argTy d D.params.length j = data d (Ctor.paramVars D.params.length j) := argTy_rec' hr
        have hdd : (data d ps).dshift = data d ps.dshift := rfl
        rw [hAk, data_paramVars_substList hps1 hpl1 (k := j) (by simp; omega)] at hutk
        rw [hAk, data_paramVars_substList hps hpl (k := j) (by simp; omega)] at hatk
        have hsd : ((data d (Ctor.paramVars D.params.length j)).substList ((us.take j).reverse ++ R1)).dinst .zero
            = data d ps := by
          rw [data_paramVars_substList hps1 hpl1 (k := j) (by simp; omega)]
          show data d (ps.dshift.dinst .zero) = _
          rw [dshift_dinst]
        rw [show A j = C.argTy d D.params.length j from rfl, hAk, hsd] at hside
        have hc := HasTy0.hcomp hdT hφ (by rw [hdd]; exact hutk) hatk hside
        rw [hOk]; simp only [hOut, hr, if_true]
        rw [show A j = C.argTy d D.params.length j from rfl, hAk,
          data_paramVars_substList hps hpl (k := j) (by simp [hOl]; omega)]
        exact hc
      · exact hTel j hj hjk

end

theorem dims_of_not_hit {D : DataDecl} {c : Nat} {C : Ctor} (h1 : D.isHIT = false)
    (h2 : D.ctors[c]? = some C) : C.dims = 0 := by
  simp only [DataDecl.isHIT, List.any_eq_false] at h1
  have := h1 C (List.mem_of_getElem? h2)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
  omega

theorem hcompCon_of (hS : SigClosed S) (hW : WfSig S) {Ψ Φ Γ d D c C ps φ u qs uargs args T}
    (htr : ∀ {Ψ' Φ' Γ' t A}, HasTy (S.take d) Ψ' Φ' Γ' t A → HasTy0 S Ψ' Φ' Γ' t A)
    (h0 : S[d]? = some (.data D)) (h1 : D.isHIT = false) (h2 : D.ctors[c]? = some C)
    (h3 : ps = Tm.ofList ps.toList) (h4 : args = Tm.ofList args.toList)
    (h5 : uargs = Tm.ofList uargs.toList)
    (h6 : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (h7 : HasTele0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse)
    (h8 : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (con d c ps.dshift uargs []) (data d ps.dshift))
    (h9 : EqTele0 S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse)
    (h10 : HasTy0 S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args [])) T) :
    HasTy0 S Ψ Φ Γ (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d ps)
      ps.dshift.toList φ 0 [] uargs.toList args.toList)) []) T := by
  obtain ⟨l0, ⟨hdT, hφ, -, -, -⟩, ch⟩ := gen_hcomp h10 rfl
  obtain ⟨-, -, -, -, -, Tel⟩ := hcompCon_inv hS hW htr h0 h2 h3 h4 h5 h6 h7 h9 hdT hφ _ (Nat.le_refl _)
  have hw : Wf0 S Ψ Φ Γ := wf_of_tele h6
  have hal : args.toList.length = C.args.length := by
    have := tele_length h6; rwa [argTys_length] at this
  have hul : uargs.toList.length = C.args.length := by
    have := tele_length h7; rwa [argTys_length] at this
  obtain ⟨D', hD', hpt⟩ := gen_data_tele hdT rfl
  rw [h0] at hD'; cases hD'
  have heq := hcompTele_eq C (C.argTy d D.params.length) (data d ps) ps.dshift.toList φ uargs.toList
    args.toList uargs.toList args.toList 0 rfl rfl (by rw [hul, hal])
  simp only [hal, ← List.range_eq_range'] at heq
  rw [show ([] : List Tm) = (hFills C (C.argTy d D.params.length) (data d ps) ps.dshift.toList φ uargs.toList
    args.toList 0).reverse from rfl, heq]
  refine ch.transport (HasTy0.con h0 h2 h3 (HasTy0.data h0 (hW.2 d D h0).1 hpt) hpt ?_
    (by rw [dims_of_not_hit h1 h2]; rfl) (by simp))
  apply HasTele0.ofList_of hw _ _ _ (by simp [argTys_length])
  intro k a B ha hB
  have hk : k < C.args.length := by
    have := (List.getElem?_eq_some_iff.1 ha).1; simpa using this
  rw [argTys_get hk] at hB; cases hB
  have := Tel k hk
  rw [List.getD_eq_getElem?_getD, ha] at this
  exact this

end KubusCore.Meta
