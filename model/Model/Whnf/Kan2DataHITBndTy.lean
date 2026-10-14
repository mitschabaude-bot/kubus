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

/-! ### The boundary instances -/

section inst
variable {d : ℕ} {D : DataDecl} {C : Ctor} {P1 : Tm} {Y : List Tm} {rs : List I} {τ : ℕ → I}
  (hYl : Y.length = C.args.length) (hPl : P1.toList.length = D.params.length)
  (hτ : ∀ i < C.dims, τ i = rsSub rs i)

include hYl in
/-- The instance through the point context of a term over the arguments mentioning no recursive argument. -/
theorem inst_pt {t : Tm} (hm : C.mentionsRec C.args.length t = false) :
    (t.ren (C.pointRen C.args.length) id).subst (lsub (ptL C Y P1.toList.reverse C.args.length) 0) τ =
      t.subst (lsub (Y.reverse ++ P1.toList.reverse) 0) τ := by
  rw [pt_inst_gen hm (by omega), List.take_of_length_le (by omega)]

include hYl hPl hτ in
/-- On terms over the parameters, arguments and interval variables of a constructor, the instance is the
boundary instance `Ctor.bndAt`. -/
theorem inst_bndAt {t : Tm} (hcl : t.closedB (D.params.length + C.args.length) C.dims = true) :
    t.subst (lsub (Y.reverse ++ P1.toList.reverse) 0) τ = Ctor.bndAt t P1.toList Y rs := by
  unfold Ctor.bndAt
  refine closed_subst_eq t _ _ _ _ _ _ hcl (fun x hx => ?_) (fun i hi => hτ i hi)
  have hx' : x < (Y.reverse ++ P1.toList.reverse).length := by simp; omega
  rw [lsub_lt hx']
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx', Option.getD_some]

include hYl hPl in
/-- The parameter variables instantiate to the parameters. -/
theorem inst_paramVars :
    (Ctor.paramVars D.params.length C.args.length).toList.reverse.map
      (·.subst (lsub (Y.reverse ++ P1.toList.reverse) 0) τ) = P1.toList.reverse := by
  rw [List.map_reverse, ← toList_subst (by unfold IsList Ctor.paramVars; rw [toList_ofList])]
  rw [paramVars_subst (ps := P1.toList) hPl (fun p hp => ?_), toList_ofList]
  have hL : C.args.length + D.params.length - 1 - p < (Y.reverse ++ P1.toList.reverse).length := by
    simp; omega
  rw [lsub_lt hL, List.getElem_append_right (by simp; omega), List.getElem_reverse]
  congr 1; simp; omega

end inst

/-! ### From the boundary equations to the boundary relation -/

section main
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {c : ℕ} {C : Ctor}
  (hC : D.ctors[c]? = some C) {ψ : I} {P1 : Tm} {Y : List Tm} {rs : List I} {τ : ℕ → I}
  (hYl : Y.length = C.args.length) (hPl : P1.toList.length = D.params.length)
  (hτ : ∀ i < C.dims, τ i = rsSub rs i)
  (hRT : ∀ T T', EqTm (S.take d) C.dims ψ (D.pointCtx d C C.args.length) T T' (.univ D.level) →
    RT2 S k (T.subst (lsub (ptL C Y P1.toList.reverse C.args.length) 0) τ)
      (T'.subst (lsub (ptL C Y P1.toList.reverse C.args.length) 0) τ))
include hW hD hC hYl hPl hτ hRT

set_option linter.unusedSectionVars false

mutual
theorem bndRel_of : ∀ (b : Tm),
    Ctor.bndTyped (S.take d) C.dims ψ (D.argCtx d C C.args.length) C (D.pointCtx d C C.args.length) D.level
      D.ctors d D.params.length b →
    b.closedB (D.params.length + C.args.length) C.dims = true →
    Ctor.simpleB D.ctors d D.params.length c C.args.length C b = true →
    bndRel S k d D.params.length C.args.length C D.ctors P1 P1 Y Y rs b
  | .con d' c' ps as rs', hT, hcl, hs => by
    unfold bndRel
    unfold Ctor.bndTyped at hT
    unfold Ctor.simpleB at hs
    obtain ⟨-, hacl, -⟩ := closedB_con hcl
    cases hC' : D.ctors[c']? with
    | none => trivial
    | some C' =>
      rw [hC'] at hT hs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨-, -⟩, rfl⟩, ⟨hal, -⟩, hsa⟩ := hs
      simp only
      have := bndRelArgs_of hC' as 0 [] hT hacl hsa (by omega) rfl (by simp)
      simpa using this
  | .var _, _, _, _ | .const _, _, _, _ | .univ _, _, _, _ | .pi _ _, _, _, _ | .lam _ _, _, _, _
  | .app _ _, _, _, _ | .sigma _ _, _, _, _ | .pair _ _, _, _, _ | .fst _, _, _, _ | .snd _, _, _, _
  | .path _ _ _, _, _, _ | .plam _, _, _, _ | .papp _ _, _, _, _ | .ipi _, _, _, _ | .split _ _ _ _, _, _, _
  | .abort, _, _, _ | .transp _ _ _, _, _, _ | .hcomp _ _ _ _, _, _, _ | .glue _ _ _ _, _, _, _
  | .glueEl _ _ _ _, _, _, _ | .unglue _ _ _, _, _, _ | .data _ _, _, _, _ | .elim _ _ _ _ _, _, _, _
  | .tcons _ _, _, _, _ | .tnil, _, _, _ => by unfold bndRel; trivial

theorem bndRelArgs_of {c' : ℕ} {C' : Ctor} (hC' : D.ctors[c']? = some C') : ∀ (as : Tm) (j : ℕ) (prev : List Tm),
    Ctor.bndTypedArgs (S.take d) C.dims ψ (D.argCtx d C C.args.length) C (D.pointCtx d C C.args.length) D.level
      D.ctors d D.params.length C' (Ctor.paramVars D.params.length C.args.length) j prev as →
    as.closedB (D.params.length + C.args.length) C.dims = true →
    Ctor.simpleArgs D.ctors d D.params.length c C.args.length C C' j as = true →
    j + as.toList.length = C'.args.length → prev.length = j →
    (∀ t ∈ prev, t.closedB (D.params.length + C.args.length) C.dims = true) →
    bndRelArgs S k d D.params.length C.args.length C D.ctors P1 P1 Y Y rs C' j
      (prev.map (Ctor.bndAt · P1.toList Y rs)) as
  | .tcons a as, j, prev, hT, hcl, hs, hlen, hpl, hpc => by
    unfold Ctor.bndTypedArgs at hT
    obtain ⟨hT1, hT2, hT3⟩ := hT
    simp only [Tm.closedB, Bool.and_eq_true] at hcl
    unfold Ctor.simpleArgs at hs
    simp only [Bool.and_eq_true] at hs
    obtain ⟨hs1, hs2⟩ := hs
    simp only [Tm.toList, List.length_cons] at hlen
    unfold bndRelArgs
    refine ⟨fun x hax hr hx => ?_, fun hr => ?_, ?_⟩
    · subst hax
      rw [hr] at hs1
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs1
      obtain ⟨T, hlk, hTe⟩ := argCtx_inst hW hD hC hx hs1.2 hYl (R := P1.toList.reverse) (by simp [hPl]) τ
      obtain ⟨hm1, hm2, heq⟩ := hT1 x T rfl hr hlk
      have h := hRT _ _ heq
      rw [List.take_of_length_le (by omega)] at hTe
      rw [inst_pt hYl hm1, inst_pt hYl hm2, hTe] at h
      obtain ⟨A0, hA0⟩ := point_of_not_rec (show j < C'.args.length by omega) hr
      have hAk : C'.argTy d D.params.length j = A0 := by simp [Ctor.argTy, hA0]
      obtain ⟨hA0c, -⟩ := ((hW.2 d D hD).2.2 c' C' hC').1 j A0 hA0
      rw [hAk, substList_subst (by
          rw [List.length_append, hpl, List.length_reverse, paramVars_toList, List.length_map, List.length_range,
            Nat.add_comm]; exact hA0c), List.map_append, inst_paramVars hYl hPl,
        List.map_congr_left (fun t ht => inst_bndAt hYl hPl hτ (hpc t ht))] at h
      rwa [hAk]
    · rw [hr] at hs1
      simp only [↓reduceIte] at hs1
      exact bndRel_of a (hT2 hr) hcl.1 hs1
    · have := bndRelArgs_of hC' as (j + 1) (a :: prev) hT3 hcl.2 hs2 (by omega) (by simp [hpl])
        (fun t ht => by
          rcases List.mem_cons.1 ht with rfl | ht
          · exact hcl.1
          · exact hpc t ht)
      simpa using this
  | .var _, _, _, _, _, _, _, _, _ | .const _, _, _, _, _, _, _, _, _ | .univ _, _, _, _, _, _, _, _, _
  | .pi _ _, _, _, _, _, _, _, _, _ | .lam _ _, _, _, _, _, _, _, _, _ | .app _ _, _, _, _, _, _, _, _, _
  | .sigma _ _, _, _, _, _, _, _, _, _ | .pair _ _, _, _, _, _, _, _, _, _ | .fst _, _, _, _, _, _, _, _, _
  | .snd _, _, _, _, _, _, _, _, _ | .path _ _ _, _, _, _, _, _, _, _, _ | .plam _, _, _, _, _, _, _, _, _
  | .papp _ _, _, _, _, _, _, _, _, _ | .ipi _, _, _, _, _, _, _, _, _ | .split _ _ _ _, _, _, _, _, _, _, _, _
  | .abort, _, _, _, _, _, _, _, _ | .transp _ _ _, _, _, _, _, _, _, _, _ | .hcomp _ _ _ _, _, _, _, _, _, _, _, _
  | .glue _ _ _ _, _, _, _, _, _, _, _, _ | .glueEl _ _ _ _, _, _, _, _, _, _, _, _
  | .unglue _ _ _, _, _, _, _, _, _, _, _ | .data _ _, _, _, _, _, _, _, _, _ | .con _ _ _ _ _, _, _, _, _, _, _, _, _
  | .elim _ _ _ _ _, _, _, _, _, _, _, _, _ | .tnil, _, _, _, _, _, _, _, _ => by unfold bndRelArgs; trivial
end

end main

/-! ### `HITHyp2.bndTy` from validity at the signature prefix -/

/-- A literal inductive type related to itself has parameters related to themselves. -/
theorem parRel2_self (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {P1 : Tm} {l : ℕ}
    (hP1 : HasTy S k .one [] (.data d P1) (.univ l)) (hPP : RT2 S k (.data d P1) (.data d P1)) :
    ParRel2 S k D P1.toList P1.toList := by
  obtain ⟨D', hD', hpt⟩ := gen_data_tele (spec_to_minimal hW hP1) rfl
  rw [hD] at hD'; cases hD'
  have hpl := tele_isList hpt
  have hPl : P1.toList.length = D.params.length := Meta.tele_length hpt
  have hpc : P1.closedB 0 k = true := by have := closed_of_ty hW hP1; simpa [Tm.closedB] using this
  have hpar := parRel2_of_RT2 hW hD hP1 hPP (ISub.id k)
  rw [isub_id_of_closed hpc] at hpar
  refine ⟨hPl, hPl, fun j hj _ hjD => ?_⟩
  have hty : ∀ t ∈ (P1.isub (ISub.id k)).toList, ∃ T, HasTy S k .one [] t T := by
    rw [isub_id_of_closed hpc]
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ⟨_, minimal_to_spec (tele_get hpt i _ _ (List.getElem?_eq_getElem hi)
      (List.getElem?_eq_getElem (show i < D.params.length by omega)))⟩
  have hLj : (P1.isub (ISub.id k)).toList[j]? = some P1.toList[j] := by
    rw [isub_id_of_closed hpc]; exact List.getElem?_eq_getElem hj
  have h := parRel2_inv hW hD hP1 hpl (ISub.id k) (by rwa [isub_id_of_closed hpc]) hty hLj
    (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hjD) fun kk hk => by
      have := tele_get hpt j _ _ (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hjD)
      rw [hk] at this
      exact EqTm.refl (minimal_to_spec this)
  rwa [isub_id_of_closed hpc] at h

/-- **`HITHyp2.bndTy` at an inductive type `d`** from the validity of the derivations of the signature
before `d` (the binary fundamental lemma at that prefix) and of the declared types up to `d`.
Only equations at `D.level` in the constructor's point context are used; the closing substitution
is diagonal in both parameters and point arguments. -/
theorem bndTy_of_valid (hW : WfSig S) {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor}
    (hV : ∀ {ψ T T'}, EqTm0 (S.take d) C.dims ψ (D.pointCtx d C C.args.length) T T' (.univ D.level) →
      Valid2 S C.dims ψ (D.pointCtx d C C.args.length) T T' (.univ D.level))
    (hDH : DeclHyp2 S (d + 1))
    {P1 : Tm} {Y : List Tm} {rs : List I} {kb : ℕ} {ψ : I} {b : Tm}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) (hb : C.bnd[kb]? = some (ψ, b))
    (hent : I.Entails .one (Ctor.cofAt ψ rs))
    (hP1 : HasTy S k .one [] (.data d P1) (.univ D.level)) (hPP : RT2 S k (.data d P1) (.data d P1))
    (hYl : Y.length = C.args.length)
    (hcon : HasTy S k .one [] (.con d c P1 (Tm.ofList Y) rs) (.data d P1))
    (hY : ∀ i, i < C.args.length → RE2 S k ((C.argTy d D.params.length i).substList
      ((Y.take i).reverse ++ P1.toList.reverse)) (Y.getD i .abort) (Y.getD i .abort)) :
    bndRel S k d D.params.length C.args.length C D.ctors P1 P1 Y Y rs b := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨-, -, -, hrsl, hsc, -⟩ := con_inv hW hD hC hcon hP1
  obtain ⟨hψs, hbcl, hsimp, -, hbt⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
  have hpar := parRel2_self hW hD hP1 hPP
  -- the related substitution out of the point context
  obtain ⟨cs0, hγ, hγ', -, -⟩ := csub2_points hW hD hDH hC hpar.1 hpar.1 hpar.2.2 (le_of_eq hYl) rfl
    (fun i hi _ _ => by
      have := hY i (by omega)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
      exact this) C.args.length (by omega)
  obtain ⟨σ, hστ⟩ : ∃ σ : ISub k C.dims, ∀ i < C.dims, σ.τ i = rsSub rs i := by
    rw [← hrsl]; exact ⟨rsI rs hsc, fun i hi => rsI_eq rs hsc hi⟩
  have hface : I.Entails .one (ψ.subst σ.τ) := by
    rw [Meta.subst_scoped_eq hψs hστ]; exact hent
  let cs := cs0.reindex hS (wf_pointCtx hW hD hC _ le_rfl) σ hface
  refine bndRel_of hW hD hC hYl hpar.1 hστ (fun T T' heq => ?_) b hbt hbcl hsimp
  have hv := (hV (spec_to_minimal_eq (wfSig_take hW d) heq) k cs).2
  have h := RE2_univ_ty hW hv
  change RT2 S k (T.subst cs0.γ σ.τ) (T'.subst cs0.γ' σ.τ) at h
  rwa [hγ, hγ'] at h

end

end Model.Whnf
