import Model.Whnf.Valid2Data
import Model.Whnf.Kan2DataHITCon

/-!
# The argument types of nested constructors of boundaries, from the validity of their equations

`HITHyp2.bndTy` at an inductive type `d` follows from the validity (`Valid2`) of the derivations in the
signature before `d` (the equations `Ctor.bndTyped` of `DataDecl.Wf`), as given by the binary fundamental
lemma at that prefix, and from the validity of the declared types (`DeclHyp2`): the instances of the
boundary equations at a constructor's parameters, arguments and interval arguments are a related
substitution out of the point context, reindexed to the constructor's interval context (`CSub2.reindex`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k : ℕ}

/-! ### Contexts without interval variables -/

/-- The types of a context well-formed without interval variables have none. -/
theorem lookup_iclosed (hS : SigClosed S) {Γ : Ctx} (hΓ : Wf0 S 0 .one Γ) {x : ℕ} {A : Tm}
    (h : Γ.lookup x = some A) : A.closedB Γ.length 0 = true := by
  obtain ⟨l, hA⟩ := lookup_typed hS hΓ h
  exact ty_closedB hA

/-- A related substitution out of a context without interval variables, at an interval context. -/
def CSub2.reindex (hS : SigClosed S) {Γ : Ctx} (hΓ : Wf0 S 0 .one Γ) (c : CSub2 S 0 .one Γ k) {Ψ : ℕ} {Φ : I}
    (σ : ISub k Ψ) (hface : I.Entails .one (Φ.subst σ.τ)) : CSub2 S Ψ Φ Γ k where
  σ := σ
  σ' := σ
  hσ := INear.refl σ
  γ := c.γ
  γ' := c.γ'
  hγ := c.hγ
  hγ' := c.hγ'
  face := hface
  look x A h := by
    rw [closed_subst_eq A Γ.length 0 c.γ c.γ σ.τ c.σ.τ (lookup_iclosed hS hΓ h) (fun _ _ => rfl)
      (fun i hi => absurd hi (Nat.not_lt_zero _))]
    exact c.look x A h
  lookT x A h := by
    intro k' ρ τ1 τ2 _ _ b1 b2
    have hcl := lookup_iclosed hS hΓ h
    rw [closed_subst_eq A Γ.length 0 _ _ τ1.τ (c.σ.comp ρ).τ hcl (fun _ _ => rfl)
        (fun i hi => absurd hi (Nat.not_lt_zero _)),
      closed_subst_eq A Γ.length 0 _ _ τ2.τ (c.σ.comp ρ).τ hcl (fun _ _ => rfl)
        (fun i hi => absurd hi (Nat.not_lt_zero _))]
    exact c.lookT x A h k' ρ _ _ (INear.refl _) (INear.refl _) b1 b2

theorem CSub2.reindex_γ (hS : SigClosed S) {Γ : Ctx} (hΓ : Wf0 S 0 .one Γ) (c : CSub2 S 0 .one Γ k) {Ψ : ℕ} {Φ : I}
    (σ : ISub k Ψ) (hface : I.Entails .one (Φ.subst σ.τ)) :
    (c.reindex hS hΓ σ hface).γ = c.γ ∧ (c.reindex hS hΓ σ hface).γ' = c.γ' ∧
      (c.reindex hS hΓ σ hface).σ = σ ∧ (c.reindex hS hΓ σ hface).σ' = σ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The interval substitution of interval arguments. -/
def rsI (rs : List I) (hsc : ∀ r ∈ rs, r.Scoped k) : ISub k rs.length where
  τ i := if i < rs.length then rs.reverse.getD i .zero else .zero
  sc i hi := by
    simp only [hi, if_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < rs.reverse.length by simpa),
      Option.getD_some]
    exact hsc _ (List.mem_reverse.1 (List.getElem_mem _))
  hi i hi := by simp [show ¬ i < rs.length by omega]

theorem rsI_eq (rs : List I) (hsc : ∀ r ∈ rs, r.Scoped k) {i : ℕ} (hi : i < rs.length) :
    (rsI rs hsc).τ i = rsSub rs i := by
  simp only [rsI, hi, if_true, rsSub, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < rs.reverse.length by simpa), Option.getD_some]

/-! ### The parameter and point contexts are well-formed without interval variables -/

section wf
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

theorem wf_paramCtx : ∀ j, j ≤ D.params.length → Wf0 S 0 .one (D.paramCtx j)
  | 0, _ => by simpa [DataDecl.paramCtx] using (Wf0.nil (S := S) (Ψ := 0) (Φ := .one) trivial)
  | j + 1, hj => by
    have ih := wf_paramCtx j (by omega)
    rw [paramCtx_succ D (show j < D.params.length by omega)]
    rcases ((hW.2 d D hD).2.1 j _ (List.getElem?_eq_getElem (show j < D.params.length by omega))).2.2 with h | ⟨kk, hkk, he⟩
    · exact .cons (htr_of hW d h)
    · rw [he]
      exact .cons (HasTy0.univ (by have := (hW.2 d D hD).1; omega) ih)

theorem wf_pointCtx {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) :
    ∀ i, i ≤ C.args.length → Wf0 S 0 .one (D.pointCtx d C i)
  | 0, _ => by
    have : D.pointCtx d C 0 = D.paramCtx D.params.length := by simp [DataDecl.pointCtx]
    rw [this]; exact wf_paramCtx hW hD _ (Nat.le_refl _)
  | i + 1, hi => by
    have ih := wf_pointCtx hC i (by omega)
    rw [pointCtx_succ]
    split_ifs with hr
    · exact ih
    · obtain ⟨A0, hA0⟩ := point_of_not_rec (show i < C.args.length by omega) (by simpa using hr)
      have hAk : C.argTy d D.params.length i = A0 := by simp [Ctor.argTy, hA0]
      rw [hAk]
      exact .cons (pt_typed hW (htr_of hW d) hD hC hA0)

end wf

/-! ### Instances out of the point context -/

/-- A term over the arguments mentioning no recursive argument, instantiated through the point context. -/
theorem pt_inst_gen {C : Ctor} {n : ℕ} {t : Tm} (hm : C.mentionsRec n t = false) {Y R : List Tm}
    (hY : n ≤ Y.length) (τ : ℕ → I) :
    (t.ren (C.pointRen n) id).subst (lsub (ptL C Y R n) 0) τ = t.subst (lsub ((Y.take n).reverse ++ R) 0) τ := by
  rw [subst_ren]
  refine subst_freeIn_congr t _ _ τ fun y hy => ?_
  have hlen := ptL_length C Y R n
  have hrc := recCount_le C n
  have hFl : ((Y.take n).reverse ++ R).length = n + R.length := by simp; omega
  by_cases hyl : y < n + R.length
  · have hc : y < n → C.isRec (n - 1 - y) = false := by
      intro hyn
      unfold Ctor.mentionsRec at hm
      have := List.any_eq_false.1 hm y (List.mem_range.2 hyn)
      simp only [Bool.and_eq_true, not_and] at this
      cases h : C.isRec (n - 1 - y)
      · rfl
      · exact absurd hy (by simpa using this h)
    have h1 := ptL_get C Y R n hY y hyl hc
    have h2 : ((Y.take n).reverse ++ R)[y]? = some ((Y.take n).reverse ++ R)[y] :=
      List.getElem?_eq_getElem (by omega)
    rw [lsub_of_getElem? (h1.trans h2), lsub_lt (by omega)]
  · rw [pointRen_ge C (show n ≤ y by omega)]
    simp only [lsub, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (ptL C Y R n).length ≤ y - recCount C n by omega),
      List.getElem?_eq_none (show ((Y.take n).reverse ++ R).length ≤ y by omega), Option.getD_none, hFl]
    congr 1; omega

/-- The type of a point argument in the argument context, instantiated. -/
theorem argCtx_inst (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {x : ℕ} (hx : x < C.args.length)
    (hxr : C.isRec (C.args.length - 1 - x) = false) {Y R : List Tm} (hYl : Y.length = C.args.length)
    (hR : R.length = D.params.length) (τ : ℕ → I) :
    ∃ T, (D.argCtx d C C.args.length).lookup x = some T ∧
      T.subst (lsub ((Y.take C.args.length).reverse ++ R) 0) τ =
        (C.argTy d D.params.length (C.args.length - 1 - x)).substList ((Y.take (C.args.length - 1 - x)).reverse ++ R) := by
  set n := C.args.length
  obtain ⟨A0, hA0⟩ := point_of_not_rec (show n - 1 - x < C.args.length by omega) hxr
  have hAk : C.argTy d D.params.length (n - 1 - x) = A0 := by simp [Ctor.argTy, hA0]
  obtain ⟨hcl, -⟩ := ((hW.2 d D hD).2.2 c C hC).1 _ A0 hA0
  refine ⟨(C.argTy d D.params.length (n - 1 - x)).ren (· + (x + 1)) id, ?_, ?_⟩
  · rw [Ctx.lookup_eq, argCtx_lt D d C n x hx]; rfl
  rw [hAk, subst_ren, Tm.substList]
  refine closed_subst_eq A0 (D.params.length + (n - 1 - x)) 0 _ _ _ _ hcl (fun y hy => ?_)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
  have e : ((Y.take n).reverse ++ R).drop (x + 1) = (Y.take (n - 1 - x)).reverse ++ R := by
    rw [List.drop_append_of_le_length (by simp; omega), List.drop_reverse]
    simp only [List.length_take, Nat.min_eq_left (show n ≤ Y.length by omega), List.take_take]
    rw [Nat.min_eq_left (by omega), show n - (x + 1) = n - 1 - x by omega]
  have hL : y < ((Y.take (n - 1 - x)).reverse ++ R).length := by simp; omega
  simp only [lsub]
  rw [← e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.length_drop]
  rw [show x + 1 + y = y + (x + 1) by omega,
    List.getElem?_eq_getElem (show y + (x + 1) < ((Y.take n).reverse ++ R).length by simp; omega)]
  rfl

end

end Model.Whnf
