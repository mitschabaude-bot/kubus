import KubusCore.Meta.TranspCon

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

end

end KubusCore.Meta
