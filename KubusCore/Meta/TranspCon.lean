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

end KubusCore.Meta
