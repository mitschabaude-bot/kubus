import KubusCore.Meta.DataTele
import KubusCore.Meta.ConBnd
import KubusCore.Meta.KanTransp

/-!
# Metatheory: the contractum of `transpCon` is typed

The argument types along the parameter line are instances of the point argument types over
`D.pointCtx` (typed in the prefix signature by `DataDecl.Wf`), under the substitution sending
the parameters to the line and the earlier point arguments to their transport fillers.
Functionality of substitution relates the instances at the ends of the line and on `φ`
(parameters: `EqTm0.dataInjAt`).
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## The fillers of `transpTele` -/

/-- The transport fillers of the first `k` arguments (in order). -/
def tFills (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) : Nat → List Tm
  | 0 => []
  | k + 1 => tFills A psL φ as k ++
      [transpFill ((A k).substList ((tFills A psL φ as k).reverse ++ psL.reverse)) φ (as.getD k .abort)]

/-- The type line of argument `k`. -/
def tLine (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) (k : Nat) : Tm :=
  (A k).substList ((tFills A psL φ as k).reverse ++ psL.reverse)

theorem tFills_succ (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) (k : Nat) :
    tFills A psL φ as (k + 1) = tFills A psL φ as k ++ [transpFill (tLine A psL φ as k) φ (as.getD k .abort)] :=
  rfl

theorem tFills_length (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) :
    ∀ k, (tFills A psL φ as k).length = k
  | 0 => rfl
  | k + 1 => by rw [tFills_succ, List.length_append, tFills_length A psL φ as k]; rfl

theorem tFills_take (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) (k : Nat) :
    ∀ m, (tFills A psL φ as (k + m)).take k = tFills A psL φ as k
  | 0 => by rw [Nat.add_zero, List.take_of_length_le (by rw [tFills_length]; exact Nat.le_refl _)]
  | m + 1 => by
    rw [← Nat.add_assoc, tFills_succ, List.take_append_of_le_length (by rw [tFills_length]; omega)]
    exact tFills_take A psL φ as k m

theorem tFills_get (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) {k n : Nat} (h : k < n) :
    (tFills A psL φ as n).getD k .abort = transpFill (tLine A psL φ as k) φ (as.getD k .abort) := by
  have := tFills_take A psL φ as (k + 1) (n - (k + 1))
  rw [show k + 1 + (n - (k + 1)) = n by omega, tFills_succ] at this
  have hl := tFills_length A psL φ as n
  rw [List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt (j := k + 1) (by omega), this,
    List.getElem?_append_right (by rw [tFills_length]; exact Nat.le_refl _), tFills_length]
  simp

theorem transpTele_eq (A : Nat → Tm) (psL : List Tm) (φ : I) (as : List Tm) :
    ∀ (rest : List Tm) (k : Nat), as.drop k = rest →
    Tm.transpTele A psL φ k (tFills A psL φ as k).reverse rest =
      (List.range' k rest.length).map fun j => transp (tLine A psL φ as j) φ (as.getD j .abort)
  | [], _, _ => rfl
  | a :: rest, k, h => by
    have ha : as.getD k .abort = a := by
      have := congrArg (fun l => l[0]?) h
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
      rw [List.getD_eq_getElem?_getD, this]; rfl
    have h1 : as.drop (k + 1) = rest := by
      rw [← List.drop_drop, h]; rfl
    simp only [Tm.transpTele, List.length_cons, List.range'_succ, List.map_cons]
    rw [ha]
    congr 1
    have := transpTele_eq A psL φ as rest (k + 1) h1
    rw [tFills_succ, List.reverse_append, ha] at this
    exact this

/-! ## Point argument types -/

theorem point_of_not_rec {C : Ctor} {k : Nat} (hk : k < C.args.length) (hr : C.isRec k = false) :
    ∃ A, C.args[k]? = some (.point A) := by
  simp only [Ctor.isRec, List.getElem?_eq_getElem hk] at hr ⊢
  cases h : C.args[k] with
  | point A => exact ⟨A, rfl⟩
  | recur => simp [h] at hr

/-- A point argument type at the arguments `xs` and parameters `R` (most recent first), as an
instance of its type over the point context. -/
theorem pt_inst (hW : WfSig S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {k : Nat} {A : Tm}
    (hA : C.args[k]? = some (.point A)) {xs R : List Tm} (hk : k ≤ xs.length)
    (hR : R.length = D.params.length) (e : Nat) (τ : Nat → I) :
    (A.ren (C.pointRen k) id).subst (lsub (ptL C xs R k) e) τ = A.substList ((xs.take k).reverse ++ R) := by
  obtain ⟨hcl, -, hnr, -⟩ := ((hW.2 d D hD).2.2 c C hC).1 k A hA
  have hFl : ((xs.take k).reverse ++ R).length = k + D.params.length := by
    simp [hR]; omega
  rw [subst_ren, substList_eq_lsub,
    closed_subst_eq A _ 0 _ (fun y => lsub (ptL C xs R k) e (C.pointRen k y))
      _ I.var hcl (fun _ _ => rfl) (fun i hi => by omega)]
  apply subst_freeIn_congr
  intro y hy
  have hyl := freeIn_lt A _ _ _ hcl hy
  have hc : y < k → C.isRec (k - 1 - y) = false := by
    intro hy'
    simp only [Ctor.noRecDeps, List.all_eq_true, List.mem_range] at hnr
    have := hnr (k - 1 - y) (by omega)
    rw [show k - 1 - (k - 1 - y) = y by omega, hy] at this
    simpa using this
  have h1 := ptL_get C xs R k hk y (by rw [hR]; omega) hc
  have h2 : ((xs.take k).reverse ++ R)[y]? = some ((xs.take k).reverse ++ R)[y] :=
    List.getElem?_eq_getElem (by omega)
  rw [lsub_of_getElem? (h1.trans h2), lsub_lt (by omega)]

theorem pt_typed (hW : WfSig S) {d : Nat}
    (htr : ∀ {Ψ' Φ' Γ' t A}, HasTy (S.take d) Ψ' Φ' Γ' t A → HasTy0 S Ψ' Φ' Γ' t A)
    {D : DataDecl} {c : Nat} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {k : Nat} {A : Tm}
    (hA : C.args[k]? = some (.point A)) :
    HasTy0 S 0 .one (D.pointCtx d C k) (A.ren (C.pointRen k) id) (univ D.level) :=
  htr (((hW.2 d D hD).2.2 c C hC).1 k A hA).2.2.2.2

/-! ## Substitutions out of a context without interval variables -/

/-- Post-composing a substitution out of a context without interval variables with an interval
substitution preserving typing. -/
theorem TySub.post {Δ Ψ1 Φ1 Γ1 Ψ2 Φ2 Γ2 σ τ} (h : TySub S 0 .one Δ Ψ1 Φ1 Γ1 σ τ) (τ' : Nat → I)
    (hw : Wf0 S Ψ2 Φ2 Γ2)
    (hf : ∀ t A, HasTy0 S Ψ1 Φ1 Γ1 t A → HasTy0 S Ψ2 Φ2 Γ2 (t.subst Tm.var τ') (A.subst Tm.var τ')) :
    TySub S 0 .one Δ Ψ2 Φ2 Γ2 (fun x => (σ x).subst Tm.var τ') (fun i => (τ i).subst τ') where
  bound := fun i hi => absurd hi (Nat.not_lt_zero _)
  hscoped := scoped_of_wf hw
  ent := ent_one _
  look := fun x A hx => by
    have := hf _ _ (h.look x A hx)
    rwa [subst_subst] at this
  wf := hw

theorem EqSub.of_eq {Δ Ψ' Φ' Γ' σ1 τ1 σ2 τ2} (h : TySub S 0 .one Δ Ψ' Φ' Γ' σ1 τ1)
    (he : ∀ x, σ1 x = σ2 x) : EqSub S 0 Δ Ψ' Φ' Γ' σ1 τ1 σ2 τ2 :=
  ⟨fun x A hx => by rw [← he x]; exact EqTm0.refl (h.look x A hx), fun i hi => absurd hi (Nat.not_lt_zero _)⟩

theorem EqSub.restrict' {Δ Ψ' Φ' Γ' σ1 τ1 σ2 τ2 Ξ} (h : EqSub S 0 Δ Ψ' Φ' Γ' σ1 τ1 σ2 τ2)
    (hs : Ξ.Scoped Ψ') (he : I.Entails Ξ Φ') : EqSub S 0 Δ Ψ' Ξ Γ' σ1 τ1 σ2 τ2 :=
  ⟨fun x A hx => EqTm0.restrict hs he (h.1 x A hx), h.2⟩

theorem lsub_post (L : List Tm) (c : Nat) (τ' : Nat → I) (y : Nat) :
    (lsub L c y).subst Tm.var τ' = lsub (L.map (·.subst Tm.var τ')) c y := by
  simp only [lsub, List.getD_eq_getElem?_getD, List.getElem?_map, List.length_map]
  cases L[y]? <;> rfl

theorem ptL_post (C : Ctor) (as R : List Tm) (τ' : Nat → I) :
    ∀ k, (ptL C as R k).map (·.subst Tm.var τ') = ptL C (as.map (·.subst Tm.var τ')) (R.map (·.subst Tm.var τ')) k
  | 0 => rfl
  | k + 1 => by
    simp only [ptL]
    split
    · exact ptL_post C as R τ' k
    · simp only [List.map_cons, ptL_post C as R τ' k, List.getD_eq_getElem?_getD, List.getElem?_map]
      congr 1; cases as[k]? <;> rfl

/-! ## Parameters: injectivity as an equality of substitutions -/

theorem subst_lsub_closed {A : Tm} {L : List Tm} (h : A.closedB L.length 0 = true) (c : Nat) (τ : Nat → I) :
    A.subst (lsub L c) τ = A.substList L := by
  rw [substList_eq_lsub]
  exact closed_subst_eq A _ 0 _ _ _ _ h (fun x hx => by rw [lsub_lt hx, lsub_lt hx]) (fun i hi => by omega)

theorem eqSub_params (hS : SigClosed S) (hW : WfSig S) {d : Nat}
    (htr : ∀ {Ψ' Φ' Γ' t A}, HasTy (S.take d) Ψ' Φ' Γ' t A → HasTy0 S Ψ' Φ' Γ' t A)
    {D : DataDecl} (hD : S[d]? = some (.data D)) {Ψ' Φ' Γ'} {ps ps' : Tm} {l : Nat}
    (hps : ps = Tm.ofList ps.toList) (hps' : ps' = Tm.ofList ps'.toList)
    (e : EqTm0 S Ψ' Φ' Γ' (data d ps) (data d ps') (univ l))
    (ht : HasTele0 S Ψ' Φ' Γ' ps D.params []) (ht' : HasTele0 S Ψ' Φ' Γ' ps' D.params [])
    (c : Nat) (τ1 τ2 : Nat → I) :
    ∀ j, j ≤ D.params.length → EqSub S 0 (D.paramCtx j) Ψ' Φ' Γ'
      (lsub (ps.toList.take j).reverse c) τ1 (lsub (ps'.toList.take j).reverse c) τ2
  | 0, _ => ⟨fun x A hx => by simp [DataDecl.paramCtx, Ctx.lookup] at hx, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    have hw := wf_of_tele ht
    have hpl : ps.toList.length = D.params.length := by simpa using tele_length ht
    have hpl' : ps'.toList.length = D.params.length := by simpa using tele_length ht'
    have ih := eqSub_params hS hW htr hD hps hps' e ht ht' c τ1 τ2 j (by omega)
    have h0 : ∀ τ σ, TySub S 0 .one [] Ψ' Φ' Γ' σ τ :=
      fun τ σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
    have T1 := tySub_params hS hD ht c (h0 τ1) j (by omega)
    have T2 := tySub_params hS hD ht' c (h0 τ2) j (by omega)
    have hA : D.params[j]? = some D.params[j] := List.getElem?_eq_getElem (by omega)
    obtain ⟨-, -, lA, hAt⟩ := (hW.2 d D hD).2.1 j _ hA
    have hAt0 := htr hAt
    have hcl := hS.params d D j _ hD hA
    have F := (sub_ty hS hAt0).2.2 T1 T2 ih
    have hl1 : ((ps.toList.take j).reverse).length = j := by simp; omega
    have hl2 : ((ps'.toList.take j).reverse).length = j := by simp; omega
    rw [subst_lsub_closed (by rw [hl1]; exact hcl), subst_lsub_closed (by rw [hl2]; exact hcl)] at F
    have hp1 : ps.toList[j]? = some ps.toList[j] := List.getElem?_eq_getElem (by omega)
    have hp2 : ps'.toList[j]? = some ps'.toList[j] := List.getElem?_eq_getElem (by omega)
    have ha1 := tele_get ht j _ _ hp1 hA
    have ha2 := tele_get ht' j _ _ hp2 hA
    rw [List.append_nil] at ha1 ha2
    have ha2' := HasTy0.conv ha2 (EqTm0.symm F)
    have hinj := EqTm0.dataInjAt hD hps hps' e hp1 hp2 hA ha1 ha2'
    have := ih.cons (A := D.params[j]) (a1 := ps.toList[j]) (a2 := ps'.toList[j])
      (by rw [subst_lsub_closed (by rw [hl1]; exact hcl)]; exact hinj)
    rw [consT_lsub, consT_lsub] at this
    have ht1 : (ps.toList.take (j + 1)).reverse = ps.toList[j] :: (ps.toList.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
    have ht2 : (ps'.toList.take (j + 1)).reverse = ps'.toList[j] :: (ps'.toList.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
    rw [paramCtx_succ D (by omega), ht1, ht2]
    exact this

/-! ## Small facts -/

/-- `(t(0))⁺` as one interval substitution. -/
def τg : Nat → I := fun i => (I.inst0 .zero i).subst (fun i => .var (i + 1))

theorem dd_eq (t : Tm) : (t.dinst .zero).dshift = t.subst Tm.var τg := by
  rw [dshift_eq, Tm.dinst, Tm.dsubst, subst_subst]; rfl

theorem consT_post (a : Tm) (σ : Nat → Tm) (τ' : Nat → I) :
    consT (a.subst Tm.var τ') (fun x => (σ x).subst Tm.var τ') = fun x => (consT a σ x).subst Tm.var τ' := by
  funext x; cases x <;> rfl

theorem EqSub.congr2 {Ψs Δ Ψ' Φ' Γ' σ1 τ1 σ2 τ2 σ2'} (h : EqSub S Ψs Δ Ψ' Φ' Γ' σ1 τ1 σ2 τ2)
    (he : ∀ x, σ2 x = σ2' x) : EqSub S Ψs Δ Ψ' Φ' Γ' σ1 τ1 σ2' τ2 := by
  rw [show σ2' = σ2 from funext fun x => (he x).symm]; exact h

/-- A telescope under an interval substitution preserving typing. -/
theorem HasTele0.post {Ψ1 Φ1 Γ1 Ψ2 Φ2 Γ2} (τ' : Nat → I) (hw : Wf0 S Ψ2 Φ2 Γ2)
    (hf : ∀ t A, HasTy0 S Ψ1 Φ1 Γ1 t A → HasTy0 S Ψ2 Φ2 Γ2 (t.subst Tm.var τ') (A.subst Tm.var τ')) :
    ∀ {ts Δ prev}, HasTele0 S Ψ1 Φ1 Γ1 ts Δ prev →
    (∀ (k : Nat) (A : Tm), Δ[k]? = some A → A.closedB (prev.length + k) 0 = true) →
    HasTele0 S Ψ2 Φ2 Γ2 (ts.subst Tm.var τ') Δ (prev.map (·.subst Tm.var τ'))
  | _, _, _, .nil _, _ => .nil hw
  | _, _, _, .cons (A := A) (prev := prev) ha hs, hcl => by
    have h1 := hf _ _ ha
    rw [substList_subst (by simpa using hcl 0 A rfl)] at h1
    refine .cons h1 ?_
    have := HasTele0.post τ' hw hf hs (fun k B hB => by
      have := hcl (k + 1) B (by simpa using hB); simp only [List.length_cons]; rwa [Nat.add_assoc, Nat.add_comm 1 k])
    simpa using this

theorem params_closed (hS : SigClosed S) {d : Nat} {D : DataDecl} (hD : S[d]? = some (.data D)) :
    ∀ (k : Nat) (A : Tm), D.params[k]? = some A → A.closedB (([] : List Tm).length + k) 0 = true :=
  fun k A hA => by simpa using hS.params d D k A hD hA

/-! ## The induction along the arguments -/

section
variable (hS : SigClosed S) (hW : WfSig S) {d : Nat}
  (htr : ∀ {Ψ' Φ' Γ' t A}, HasTy (S.take d) Ψ' Φ' Γ' t A → HasTy0 S Ψ' Φ' Γ' t A)
  {D : DataDecl} {c : Nat} {C : Ctor} (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
  {Ψ : Nat} {Φ : I} {Γ : Ctx} {ps : Tm} {φ : I} {args : Tm} {l0 : Nat}
  (hps : ps = Tm.ofList ps.toList)
  (htele : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse)
  (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (data d ps) (univ l0)) (hφ : φ.Scoped Ψ)
  (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (data d ps) ((data d ps).dinst .zero).dshift (univ l0))
include hS hW htr hD hC hps htele hL hφ hc

/-- The invariant after `k` arguments: the fillers and the transported arguments, as
substitutions out of the point context, and the transported arguments typed so far. -/
theorem transpCon_inv :
    let A := C.argTy d D.params.length
    let as := args.toList
    let Fall := tFills A ps.toList φ as C.args.length
    let osAll := (List.range C.args.length).map fun j => transp (tLine A ps.toList φ as j) φ (as.getD j .abort)
    ∀ k, k ≤ C.args.length →
    TySub S 0 .one (D.pointCtx d C k) (Ψ + 1) Φ.shift Γ.dshift (lsub (ptL C Fall ps.toList.reverse k) 0) I.var ∧
    TySub S 0 .one (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C osAll (ps.dinst .one).toList.reverse k) 0) I.var ∧
    EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ
      (fun x => (lsub (ptL C Fall ps.toList.reverse k) 0 x).subst Tm.var (I.inst0 .zero))
      (fun i => (I.var i).subst (I.inst0 .zero))
      (lsub (ptL C as (ps.dinst .zero).toList.reverse k) 0) I.var ∧
    EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ
      (fun x => (lsub (ptL C Fall ps.toList.reverse k) 0 x).subst Tm.var (I.inst0 .one))
      (fun i => (I.var i).subst (I.inst0 .one))
      (lsub (ptL C osAll (ps.dinst .one).toList.reverse k) 0) I.var ∧
    EqSub S 0 (D.pointCtx d C k) (Ψ + 1) (cof Φ φ).shift Γ.dshift
      (lsub (ptL C Fall ps.toList.reverse k) 0) I.var
      (fun x => (lsub (ptL C Fall ps.toList.reverse k) 0 x).subst Tm.var τg) (fun i => (I.var i).subst τg) ∧
    (∀ j, j < k → HasTy0 S Ψ Φ Γ (osAll.getD j .abort)
      ((A j).substList ((osAll.take j).reverse ++ (ps.dinst .one).toList.reverse))) := by
  intro A as Fall osAll k hk
  -- common facts
  have hw : Wf0 S Ψ Φ Γ := wf_of_tele htele
  have hs : Φ.Scoped Ψ := scoped_of_wf hw
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := scoped_shift ⟨hs, hφ⟩
  have hXe : I.Entails (cof Φ φ).shift Φ.shift := ent_shift (ent_and_left _ _)
  have hw1 : Wf0 S (Ψ + 1) Φ.shift Γ.dshift := wf_of_ty hL
  have hwc : Wf0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift := hw1.restrict hXs hXe
  obtain ⟨D', hD', hptL⟩ := gen_data_tele hL rfl
  rw [hD] at hD'; cases hD'
  have hpl : ps.toList.length = D.params.length := by simpa using tele_length hptL
  have hf : ∀ (r : I), r.Scoped Ψ → ∀ t B, HasTy0 S (Ψ + 1) Φ.shift Γ.dshift t B →
      HasTy0 S Ψ Φ Γ (t.subst Tm.var (I.inst0 r)) (B.subst Tm.var (I.inst0 r)) :=
    fun r hr t B h => HasTy0.dsubst hS h hr
  have hfg : ∀ t B, HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift t B →
      HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (t.subst Tm.var τg) (B.subst Tm.var τg) := by
    intro t B h
    have := HasTy0.dwk hS (HasTy0.dsubst hS h (r := .zero) trivial)
    rwa [dd_eq, dd_eq] at this
  have hpsr : ∀ τ' : Nat → I, (ps.subst Tm.var τ').toList = ps.toList.map (·.subst Tm.var τ') :=
    fun τ' => toList_subst hps _ _
  have hpt1 : HasTele0 S Ψ Φ Γ (ps.dinst .one) D.params [] := by
    have := HasTele0.post (I.inst0 .one) hw (hf .one trivial) hptL (params_closed hS hD)
    simpa using this
  have hpl1 : (ps.dinst .one).toList.length = D.params.length := by simpa using tele_length hpt1
  have hpl0 : (ps.dinst .zero).toList.length = D.params.length := by
    show (ps.subst Tm.var _).toList.length = _; rw [hpsr]; simpa using hpl
  have hal : as.length = C.args.length := by
    have := tele_length htele; rwa [argTys_length] at this
  have hal' : args.toList.length = C.args.length := hal
  have h0 : ∀ {Ψ' Φ' Γ'} (τ σ : Nat → _), Wf0 S Ψ' Φ' Γ' → TySub S 0 .one [] Ψ' Φ' Γ' σ τ :=
    fun τ σ hw' => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw'
  have hpc : D.pointCtx d C 0 = D.paramCtx D.params.length := by simp [DataDecl.pointCtx]
  induction k with
  | zero =>
    simp only [ptL, hpc]
    have T1 := tySub_params hS hD hptL 0 (h0 I.var · hw1) _ (Nat.le_refl _)
    rw [List.take_of_length_le (by omega)] at T1
    have TO := tySub_params hS hD hpt1 0 (h0 I.var · hw) _ (Nat.le_refl _)
    rw [List.take_of_length_le (by omega)] at TO
    have hpost : ∀ τ' : Nat → I, ∀ x, (lsub ps.toList.reverse 0 x).subst Tm.var τ' =
        lsub (ps.subst Tm.var τ').toList.reverse 0 x := by
      intro τ' x; rw [lsub_post, hpsr, List.map_reverse]
    refine ⟨T1, TO, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · exact EqSub.of_eq (T1.post _ hw (hf .zero trivial)) (hpost _)
    · exact EqSub.of_eq (T1.post _ hw (hf .one trivial)) (hpost _)
    · have hptc := HasTele0.restrict hXs hXe hptL
      have hptg : HasTele0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (ps.subst Tm.var τg) D.params [] := by
        simpa using HasTele0.post τg hwc hfg hptc (params_closed hS hD)
      have e : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (data d ps) (data d (ps.subst Tm.var τg)) (univ l0) := by
        rw [← show ((data d ps).dinst .zero).dshift = data d (ps.subst Tm.var τg) from dd_eq _]; exact hc
      have hpsg : ps.subst Tm.var τg = Tm.ofList (ps.subst Tm.var τg).toList := isList_subst hps _ _
      have E := eqSub_params hS hW htr hD hps hpsg e hptc hptg 0 I.var (fun i => (I.var i).subst τg) _
        (Nat.le_refl _)
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by rw [hpsr, List.length_map]; omega)] at E
      exact E.congr2 (fun x => (hpost τg x).symm)
  | succ k ih =>
    have hkn : k < C.args.length := by omega
    obtain ⟨T1, TO, E0, E1, Ec, Tel⟩ := ih (by omega)
    have hpt0 : HasTele0 S Ψ Φ Γ (ps.dinst .zero) D.params [] := by
      have := HasTele0.post (I.inst0 .zero) hw (hf .zero trivial) hptL (params_closed hS hD)
      simpa using this
    have hP0 := tySub_params hS hD hpt0 0 (h0 I.var · hw) _ (Nat.le_refl _)
    rw [List.take_of_length_le (by omega)] at hP0
    have TA := tySub_points hS hW hD hC hP0 htele hpl0 k (by omega)
    have hFl : Fall.length = C.args.length := tFills_length _ _ _ _ _
    have hOl : osAll.length = C.args.length := by simp [osAll]
    have hFl' : (tFills A ps.toList φ as C.args.length).length = C.args.length := hFl
    have hOl' : ((List.range C.args.length).map fun j => transp (tLine A ps.toList φ as j) φ (as.getD j .abort)).length = C.args.length := hOl
    have hFt : Fall.take k = tFills A ps.toList φ as k := by
      have := tFills_take A ps.toList φ as k (C.args.length - k)
      rwa [show k + (C.args.length - k) = C.args.length by omega] at this
    have hLk : tLine A ps.toList φ as k = (A k).substList ((Fall.take k).reverse ++ ps.toList.reverse) := by
      rw [hFt]; rfl
    have hFk : Fall.getD k .abort = transpFill (tLine A ps.toList φ as k) φ (as.getD k .abort) :=
      tFills_get A ps.toList φ as hkn
    have hOk : osAll.getD k .abort = transp (tLine A ps.toList φ as k) φ (as.getD k .abort) := by
      simp only [osAll, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hkn]; rfl
    have hak : as[k]? = some (as.getD k .abort) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hatk := tele_get htele k _ _ hak (argTys_get hkn)
    have hTel : ∀ j, j < k + 1 → j ≠ k → HasTy0 S Ψ Φ Γ (osAll.getD j .abort)
        ((A j).substList ((osAll.take j).reverse ++ (ps.dinst .one).toList.reverse)) :=
      fun j hj hjk => Tel j (by omega)
    rw [pointCtx_succ]
    cases hr : C.isRec k
    · sorry
    · simp only [hr, if_true, ptL]
      refine ⟨T1, TO, E0, E1, Ec, fun j hj => ?_⟩
      by_cases hjk : j = k
      · subst hjk
        have hAk : A j = data d (Ctor.paramVars D.params.length j) := argTy_rec' hr
        have hps0 : IsList (ps.dinst .zero) := isList_subst hps _ _
        have hps1 : IsList (ps.dinst .one) := isList_subst hps _ _
        rw [show C.argTy d D.params.length j = data d (Ctor.paramVars D.params.length j) from hAk,
          substList_eq] at hatk
        simp only [Tm.subst] at hatk
        rw [← substList_eq, paramVars_substList hps0 hpl0 (by simp; omega)] at hatk
        have hLd : tLine A ps.toList φ as j = data d ps := by
          rw [hLk, hAk, substList_eq]; simp only [Tm.subst]
          rw [← substList_eq, paramVars_substList hps hpl (by simp; omega)]
        have := HasTy0.transp hL hφ hc hatk
        rw [hOk, hLd, hAk, substList_eq]; simp only [Tm.subst]
        rw [← substList_eq, paramVars_substList hps1 hpl1 (by simp; omega)]
        exact this
      · exact hTel j hj hjk

end

end KubusCore.Meta
