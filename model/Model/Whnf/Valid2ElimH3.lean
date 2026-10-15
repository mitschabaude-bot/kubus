import Model.Whnf.Valid2ElimH2
import Model.Whnf.Valid2Comp

/-!
# Closing substitutions for eliminator branch contexts

A computable Π telescope supplies the types needed to close its context with related arguments.
This also applies to the induction hypotheses in an eliminator branch.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- Substitute successive telescope arguments, with the last argument innermost. -/
def teleSub (X : List Tm) (γ : ℕ → Tm) : ℕ → Tm :=
  X.foldl (fun σ a => consT a σ) γ

theorem teleSub_cons (a : Tm) (X : List Tm) (γ : ℕ → Tm) :
    teleSub (a :: X) γ = teleSub X (consT a γ) := rfl

theorem teleSub_append (X Y : List Tm) (γ : ℕ → Tm) :
    teleSub (X ++ Y) γ = teleSub Y (teleSub X γ) := by
  exact List.foldl_append

/-- A telescope substitution is lookup in the reversed argument list, followed by the outer substitution. -/
theorem teleSub_eq (X : List Tm) (γ : ℕ → Tm) (i : ℕ) :
    teleSub X γ i = X.reverse.getD i (γ (i - X.length)) := by
  unfold teleSub
  rw [List.foldl_eq_foldr_reverse]
  have key : ∀ (L : List Tm) (i : ℕ), L.foldr consT γ i = L.getD i (γ (i - L.length)) := by
    intro L
    induction L with
    | nil => intro i; rfl
    | cons a L ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i =>
        simpa only [List.foldr_cons, consT, List.getD_cons_succ, List.length_cons, Nat.add_sub_add_right] using ih i
  simpa only [List.length_reverse] using key X.reverse i

theorem teleSub_lt (X : List Tm) (γ : ℕ → Tm) {i : ℕ} (hi : i < X.length) :
    teleSub X γ i = X.reverse[i]'(by simpa using hi) := by
  rw [teleSub_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  rfl

theorem teleSub_add (X : List Tm) (γ : ℕ → Tm) (i : ℕ) :
    teleSub X γ (i + X.length) = γ i := by
  rw [teleSub_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
  simp

/-- Change the presentation of a context without changing either substitution. -/
def CSub2.ctxEq {Δ : Ctx} (c : CSub2 S Ψ Φ Γ k) (h : Γ = Δ) : CSub2 S Ψ Φ Δ k :=
  { c with
    look := fun x A hx => c.look x A (h.symm ▸ hx)
    lookT := fun x A hx => c.lookT x A (h.symm ▸ hx) }

theorem consIs_wkIv (rs : List I) (τ : ℕ → I) (i : ℕ) :
    (wkIv rs.length i).subst (consIs rs τ) = τ i := by
  simp only [wkIv, I.subst, consIs_eq, List.length_reverse]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
  simp

/-- Instantiating the extra interval variables cancels interval weakening. -/
theorem wkI_consIs (t : Tm) (rs : List I) (γ : ℕ → Tm) (τ : ℕ → I) :
    (t.subst Tm.var (wkIv rs.length)).subst γ (consIs rs τ) = t.subst γ τ := by
  rw [subst_subst]
  exact subst_congr (fun _ => rfl) (consIs_wkIv rs τ) t

/-- Extend an interval substitution by a list of interval arguments. -/
def consListI (σ : ISub k Ψ) (rs : List I) (hrs : ∀ r ∈ rs, r.Scoped k) :
    ISub k (Ψ + rs.length) where
  τ := consIs rs σ.τ
  sc i hi := by
    rw [consIs_eq, List.getD_eq_getElem?_getD]
    cases h : rs.reverse[i]? with
    | none =>
      simp only [h, Option.getD_none]
      have hn := List.getElem?_eq_none_iff.1 h
      simp only [List.length_reverse] at hn
      exact σ.sc (i - rs.length) (by omega)
    | some r =>
      simp only [h, Option.getD_some]
      exact hrs r (List.mem_reverse.1 (List.mem_of_getElem? h))

  hi i hi := by
    rw [consIs_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using (show rs.length ≤ i by omega))]
    simp only [Option.getD_none]
    exact σ.hi _ (by omega)

theorem consIs_near {τ τ' : ℕ → I} (hτ : ∀ i, I.Eq (τ i) (τ' i))
    {rs rs' : List I} (hr : IEqL rs rs') :
    ∀ i, I.Eq (consIs rs τ i) (consIs rs' τ' i) := by
  induction hr generalizing τ τ' with
  | nil => exact hτ
  | @cons r r' rs rs' he hr ih =>
    apply ih
    intro i
    cases i with
    | zero => exact he
    | succ i => exact hτ i

/-- Close several interval binders at once. -/
def CSub2.consList (c : CSub2 S Ψ Φ Γ k) (rs rs' : List I) (hr : IEqL rs rs')
    (hrs : ∀ r ∈ rs, r.Scoped k) (hrs' : ∀ r ∈ rs', r.Scoped k) :
    CSub2 S (Ψ + rs.length) (Φ.ren (· + rs.length)) (ctxWkI rs.length Γ) k where
  σ := consListI c.σ rs hrs
  σ' := ⟨consIs rs' c.σ'.τ,
    fun i hi => (consListI c.σ' rs' hrs').sc i (by rw [← (ieqL_iff.1 hr).length_eq]; exact hi),
    fun i hi => (consListI c.σ' rs' hrs').hi i (by rw [← (ieqL_iff.1 hr).length_eq]; exact hi)⟩
  hσ := consIs_near c.hσ hr
  γ := c.γ
  γ' := c.γ'
  hγ := c.hγ
  hγ' := c.hγ'
  face := by
    simp only [consListI]
    rw [I_ren_add_eq, I_subst_subst]
    have e : (fun i => (wkIv rs.length i).subst (consIs rs c.σ.τ)) = c.σ.τ :=
      funext (consIs_wkIv rs c.σ.τ)
    rw [e]
    exact c.face
  look x A hx := by
    rw [lookup_wkI, Option.map_eq_some_iff] at hx
    obtain ⟨B, hB, rfl⟩ := hx
    simp only [consListI]
    rw [wkI_consIs]
    exact c.look x B hB
  lookT x A hx k' ρ τ1 τ2 h1 h2 b1 b2 := by
    rw [lookup_wkI, Option.map_eq_some_iff] at hx
    obtain ⟨B, hB, rfl⟩ := hx
    rw [subst_subst, subst_subst]
    let τ1' : ISub k' Ψ := ⟨fun i => τ1.τ (i + rs.length), fun i hi => τ1.sc _ (by omega), fun i hi => τ1.hi _ (by omega)⟩
    let τ2' : ISub k' Ψ := ⟨fun i => τ2.τ (i + rs.length), fun i hi => τ2.sc _ (by omega), fun i hi => τ2.hi _ (by omega)⟩
    apply c.lookT x B hB k' ρ τ1' τ2' (fun i => ?_) (fun i => ?_) b1 b2
    · have hh := h1 (i + rs.length)
      change I.Eq ((consIs rs c.σ.τ (i + rs.length)).subst ρ.τ) _ at hh
      change I.Eq ((wkIv rs.length i).subst (consIs rs c.σ.τ) |>.subst ρ.τ) _ at hh
      rw [consIs_wkIv] at hh
      exact hh
    · have hh := h2 (i + rs.length)
      change I.Eq ((consIs rs c.σ.τ (i + rs.length)).subst ρ.τ) _ at hh
      change I.Eq ((wkIv rs.length i).subst (consIs rs c.σ.τ) |>.subst ρ.τ) _ at hh
      rw [consIs_wkIv] at hh
      exact hh

/-- Closing the arguments of a weakened outer term cancels both weakenings. -/
theorem wkN_teleSub (t : Tm) (X : List Tm) (rs : List I) (γ : ℕ → Tm) (τ : ℕ → I) :
    (t.wkN X.length rs.length).subst (teleSub X γ) (consIs rs τ) = t.subst γ τ := by
  rw [wkN_eq, subst_subst]
  exact subst_congr (teleSub_add X γ) (consIs_wkIv rs τ) t

/-- The variables of a branch context instantiate to its arguments, hypotheses and interval arguments. -/
theorem branchVars_inst2 (C : Ctor) (X Y : List Tm) (rs : List I)
    (hX : X.length = C.args.length) (hY : Y.length = C.recPos.length) (hrs : rs.length = C.dims)
    (γ : ℕ → Tm) (τ : ℕ → I) :
    ((List.range C.args.length).map (fun j => Tm.var (C.recPos.length + C.args.length - 1 - j))).map
      (fun t => t.subst (teleSub (X ++ Y) γ) (consIs rs τ)) = X ∧
    ((List.range C.recPos.length).map (fun j => Tm.var (C.recPos.length - 1 - j))).map
      (fun t => t.subst (teleSub (X ++ Y) γ) (consIs rs τ)) = Y ∧
    ((List.range C.dims).map (fun j => I.var (C.dims - 1 - j))).map
      (fun r => r.subst (consIs rs τ)) = rs := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.ext_getElem (by simp [hX])
    intro j hj hj'
    simp only [List.getElem_map, List.getElem_range, Tm.subst]
    rw [teleSub_lt (X ++ Y) γ (by simp only [List.length_append, hX, hY]; omega), List.getElem_reverse, List.getElem_append_left (by simp only [List.length_append, hX, hY]; omega)]
    congr 1
    simp only [List.length_append, hX, hY]
    omega
  · apply List.ext_getElem (by simp [hY])
    intro j hj hj'
    simp only [List.getElem_map, List.getElem_range, Tm.subst]
    rw [teleSub_lt (X ++ Y) γ (by simp only [List.length_append, hX, hY]; omega), List.getElem_reverse, List.getElem_append_right (by simp [hX, hY]; omega)]
    congr 1
    simp only [List.length_append, hX, hY]
    omega
  · apply List.ext_getElem (by simp [hrs])
    intro j hj hj'
    simp only [List.getElem_map, List.getElem_range, I.subst, consIs_eq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    simp only [Option.getD_some, List.getElem_reverse]
    congr 1
    omega


/-- A branch application closes to the branch applied to the given arguments and hypotheses. -/
theorem branchApp_inst2 (C : Ctor) (b : Tm) (X Y : List Tm) (rs : List I)
    (hX : X.length = C.args.length) (hY : Y.length = C.recPos.length) (hrs : rs.length = C.dims)
    (γ : ℕ → Tm) (τ : ℕ → I) :
    (DataDecl.branchApp C b).subst (teleSub (X ++ Y) γ) (consIs rs τ) =
      Tm.papps (Tm.apps (b.subst γ τ) (X ++ Y)) rs := by
  unfold DataDecl.branchApp
  dsimp only
  rw [papps_subst, apps_subst]
  have hL : (X ++ Y).length = C.args.length + C.recPos.length := by simp [hX, hY]
  rw [← hL, ← hrs, wkN_teleSub]
  obtain ⟨hx, hy, hr⟩ := branchVars_inst2 C X Y rs hX hY hrs γ τ
  rw [← hrs] at hr
  rw [List.map_append, hx, hy, hr]

/-- The instantiated branch body is the motive at the instantiated constructor. -/
theorem branchBody_inst2 (d c : ℕ) (C : Ctor) (ps M : Tm) (X Y : List Tm) (rs : List I)
    (hX : X.length = C.args.length) (hY : Y.length = C.recPos.length) (hrs : rs.length = C.dims)
    (γ : ℕ → Tm) (τ : ℕ → I) :
    (DataDecl.branchBody d c C ps M).subst (teleSub (X ++ Y) γ) (consIs rs τ) =
      (M.subst (Tm.up γ) τ).inst (.con d c (ps.subst γ τ) (Tm.ofList X) rs) := by
  unfold DataDecl.branchBody
  dsimp only
  rw [subst_subst, subst_up_inst_eq]
  have hL : (X ++ Y).length = C.args.length + C.recPos.length := by simp [hX, hY]
  obtain ⟨hx, -, hr⟩ := branchVars_inst2 C X Y rs hX hY hrs γ τ
  apply subst_congr
  · intro j
    cases j with
    | zero =>
      simp only [Tm.subst, ofList_subst]
      rw [← hrs] at hr
      rw [← hL, ← hrs, wkN_teleSub, hx, hr]
      rfl
    | succ j =>
      simp only [Tm.subst, consT]
      rw [Nat.add_assoc, ← hL]
      exact teleSub_add (X ++ Y) γ j
  · intro i
    change (wkIv C.dims i).subst (consIs rs τ) = τ i
    rw [← hrs]
    exact consIs_wkIv rs τ i

/-- Instantiating a lifted outer substitution is the telescope substitution. -/
theorem subst_upN_teleSub (t : Tm) (X : List Tm) (γ : ℕ → Tm) (τ : ℕ → I) :
    (t.subst (upN X.length γ) τ).substList X.reverse = t.subst (teleSub X γ) τ := by
  rw [substList_eq, subst_subst]
  apply subst_congr
  · intro i
    by_cases hi : i < X.length
    · rw [upN_lt hi, Tm.subst, slS_lt (by simpa using hi), teleSub_lt X γ hi]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + X.length := ⟨i - X.length, by omega⟩
      rw [upN_add, ← substList_eq, teleSub_add]
      simpa only [List.length_reverse, wkN_eq] using wkN_substList (γ j) X.reverse
  · intro i
    exact I_subst_var _

variable (hW : WfSig S)
include hW

/-- The codomain of a related Π type is related in its extended context. -/
theorem piCod_rel {A B : Tm}
    (h : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L (.pi A B)) (c.R (.pi A B))) :
    ∀ k (c : CSub2 S Ψ Φ (A :: Γ) k), RT2 S k (c.L B) (c.R B) := by
  intro k c
  have hh := (RT2_pi_inv hW (h k (c.ren (· + 1) lookup_shift_ren))).2 _ _ c.head_rel
  simp only [CSub2.ren, subst_up_inst_eq, consT_succ_eq] at hh
  exact hh

/-- Close a computable Π telescope by related arguments. -/
def CSub2.foldPi : ∀ {Γ : Ctx} (Δ : List Tm) {B : Tm}
    (hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L (Δ.foldr Tm.pi B)) (c.R (Δ.foldr Tm.pi B)))
    (c : CSub2 S Ψ Φ Γ k) (X X' : List Tm), X.length = Δ.length → X'.length = X.length →
    (∀ j (hj : j < X.length) (hj' : j < X'.length) (hjΔ : j < Δ.length),
      RE2 S k (Δ[j].subst (teleSub (X.take j) c.γ) c.σ.τ) X[j] X'[j]) →
    CSub2 S Ψ Φ (Δ.reverse ++ Γ) k
  | _, [], _, _, c, [], [], _, _, _ => c
  | Γ, A :: Δ, B, hT, c, a :: X, a' :: X', hl, hl', ha => by
    have hA : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L A) (c.R A) :=
      fun k c => (RT2_pi_inv hW (hT k c)).1
    let c1 := c.ext hW A a a' (ha 0 (by simp) (by simp) (by simp)) (CSub2.tyRob_of hW hA c)
    have hB := piCod_rel hW hT
    have c2 := CSub2.foldPi (Γ := A :: Γ) Δ hB c1 X X' (by simpa using hl) (by simpa using hl')
      (fun j hj hj' hjΔ => by
        have hh := ha (j + 1) (by simp; omega) (by simp; omega) (by simp; omega)
        simpa only [List.getElem_cons_succ, List.take_succ_cons, teleSub_cons] using hh)
    exact c2.ctxEq (by simp only [List.reverse_cons, List.append_assoc, List.singleton_append])
  | _, [], _, _, _, _ :: _, _, hl, _, _ => by simp at hl
  | _, _ :: _, _, _, _, [], _, hl, _, _ => by simp at hl
  | _, [], _, _, _, [], _ :: _, _, hl', _ => by simp at hl'
  | _, _ :: _, _, _, _, _ :: _, [], _, hl', _ => by simp at hl'

/-- Closing a telescope preserves its interval substitutions and installs its arguments. -/
theorem CSub2.foldPi_sub : ∀ {Γ : Ctx} (Δ : List Tm) {B : Tm}
    (hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L (Δ.foldr Tm.pi B)) (c.R (Δ.foldr Tm.pi B)))
    (c : CSub2 S Ψ Φ Γ k) (X X' : List Tm) (hl : X.length = Δ.length) (hl' : X'.length = X.length)
    (ha : ∀ j (hj : j < X.length) (hj' : j < X'.length) (hjΔ : j < Δ.length),
      RE2 S k (Δ[j].subst (teleSub (X.take j) c.γ) c.σ.τ) X[j] X'[j]),
    let c1 := c.foldPi hW Δ hT X X' hl hl' ha
    c1.σ = c.σ ∧ c1.σ' = c.σ' ∧ c1.γ = teleSub X c.γ ∧ c1.γ' = teleSub X' c.γ'
  | _, [], _, _, c, [], [], _, _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | Γ, A :: Δ, B, hT, c, a :: X, a' :: X', hl, hl', ha => by
    have hA : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L A) (c.R A) :=
      fun k c => (RT2_pi_inv hW (hT k c)).1
    let c1 := c.ext hW A a a' (ha 0 (by simp) (by simp) (by simp)) (CSub2.tyRob_of hW hA c)
    have ih := CSub2.foldPi_sub Δ (piCod_rel hW hT) c1 X X' (by simpa using hl) (by simpa using hl')
      (fun j hj hj' hjΔ => by
        have hh := ha (j + 1) (by simp; omega) (by simp; omega) (by simp; omega)
        simpa only [List.getElem_cons_succ, List.take_succ_cons, teleSub_cons] using hh)
    exact ih
  | _, [], _, _, _, _ :: _, _, hl, _, _ => by simp at hl
  | _, _ :: _, _, _, _, [], _, hl, _, _ => by simp at hl
  | _, [], _, _, _, [], _ :: _, _, hl', _ => by simp at hl'
  | _, _ :: _, _, _, _, _ :: _, [], _, hl', _ => by simp at hl'

/-- Instantiate a valid branch equation with related telescope and interval arguments. -/
theorem Valid2.foldPi_inst {Δ : List Tm} {B t u A : Tm}
    (hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L (Δ.foldr Tm.pi B)) (c.R (Δ.foldr Tm.pi B)))
    (c : CSub2 S Ψ Φ Γ k) (X X' : List Tm) (hl : X.length = Δ.length) (hl' : X'.length = X.length)
    (ha : ∀ j (hj : j < X.length) (hj' : j < X'.length) (hjΔ : j < Δ.length),
      RE2 S k (Δ[j].subst (teleSub (X.take j) c.γ) c.σ.τ) X[j] X'[j])
    (rs rs' : List I) (hr : IEqL rs rs') (hrs : ∀ r ∈ rs, r.Scoped k) (hrs' : ∀ r ∈ rs', r.Scoped k)
    {ψ : I} (hh : I.Entails .one (ψ.subst (consIs rs c.σ.τ)))
    (h : Valid2 S (Ψ + rs.length) (cof (Φ.ren (· + rs.length)) ψ)
      (ctxWkI rs.length (Δ.reverse ++ Γ)) t u A) :
    RT2 S k (A.subst (teleSub X c.γ) (consIs rs c.σ.τ))
      (A.subst (teleSub X' c.γ') (consIs rs' c.σ'.τ)) ∧
    RE2 S k (A.subst (teleSub X c.γ) (consIs rs c.σ.τ))
      (t.subst (teleSub X c.γ) (consIs rs c.σ.τ))
      (u.subst (teleSub X' c.γ') (consIs rs' c.σ'.τ)) := by
  let cT := c.foldPi hW Δ hT X X' hl hl' ha
  obtain ⟨hσ, hσ', hγ, hγ'⟩ := c.foldPi_sub hW Δ hT X X' hl hl' ha
  let cI := cT.consList rs rs' hr hrs hrs'
  have hface : I.Entails .one (ψ.subst cI.σ.τ) := by
    change I.Entails .one (ψ.subst (consIs rs cT.σ.τ))
    rw [hσ]
    exact hh
  have H := h k (cI.cof hface)
  change RT2 S k (A.subst cT.γ (consIs rs cT.σ.τ)) (A.subst cT.γ' (consIs rs' cT.σ'.τ)) ∧
    RE2 S k (A.subst cT.γ (consIs rs cT.σ.τ)) (t.subst cT.γ (consIs rs cT.σ.τ))
      (u.subst cT.γ' (consIs rs' cT.σ'.τ)) at H
  rwa [hσ, hσ', hγ, hγ'] at H

end

end Model.Whnf
