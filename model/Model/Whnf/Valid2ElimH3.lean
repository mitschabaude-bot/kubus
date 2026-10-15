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
