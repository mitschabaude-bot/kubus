import Model.Canon.Proj

/-!
# Canonicity: projections and faces

Face substitutions (`face_all`), the commutation of projections with interval substitutions, and
the conversion of argument telescopes along equal arguments.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig}

/-- On a face, a term equals its instance at the face's endpoints. -/
theorem face_all (hW : WfSig S) {Ψ : ℕ} {Ξ : I} {Γ : Ctx} {t A : Tm} {l : ℕ}
    (hA : HasTy0 S Ψ Ξ Γ A (.univ l) ∨ A = .univ l) (ht : HasTy0 S Ψ Ξ Γ t A) :
    ∀ (α : I.Face), (∀ p ∈ α, p.1 < Ψ) → I.Entails Ξ (I.ofFace α) →
      EqTm0 S Ψ Ξ Γ t (t.subst Tm.var (faceSub α)) A
  | [], _, _ => by
    rw [show faceSub [] = I.var from funext fun _ => rfl, subst_var]; exact EqTm0.refl ht
  | (i, e) :: α, hsc, he => by
    obtain ⟨hT, hC⟩ := wf_typed _ S rfl hW
    have hS := sigClosed_of_wfSig hW
    have hlit : I.Entails Ξ (I.lit i e) := ent_trans he (ent_and_left _ _)
    have hrest : I.Entails Ξ (I.ofFace α) := ent_trans he (ent_and_right _ _)
    have hi : i < Ψ := hsc _ (List.mem_cons_self ..)
    have e1 : EqTm0 S Ψ Ξ Γ t (t.dset i (I.ofDir e)) A := by
      rcases hA with hA | rfl
      · exact EqTm0.face hi hlit hA ht
      · exact EqTm0.faceU hi hlit ht
    have ht1 := (pre_eq hS hT hC e1).2.1
    have e2 := face_all hW hA ht1 α (fun p hp => hsc p (List.mem_cons_of_mem _ hp)) hrest
    have hc : (t.dset i (I.ofDir e)).subst Tm.var (faceSub α) = t.subst Tm.var (faceSub ((i, e) :: α)) := by
      rw [Tm.dset, Tm.dsubst, subst_subst]
      congr 1
      funext x; exact faceSub_cons_comp i e α (.var x)
    rw [hc] at e2
    exact e1.trans e2


/-! ## Argument telescopes along equal arguments -/

theorem EqTele0.ofList_of' {Ψ : ℕ} {Φ : I} {Γ : Ctx} (hw : Wf0 S Ψ Φ Γ) :
    ∀ (as as' Δ prev : List Tm), as.length = Δ.length → as'.length = Δ.length →
    (∀ (k : ℕ) (a a' A : Tm), as[k]? = some a → as'[k]? = some a' → Δ[k]? = some A →
      EqTm0 S Ψ Φ Γ a a' (A.substList ((as.take k).reverse ++ prev))) →
    EqTele0 S Ψ Φ Γ (Tm.ofList as) (Tm.ofList as') Δ prev
  | [], [], [], _, _, _, _ => .nil hw
  | a :: as, a' :: as', A :: Δ, prev, hl, hl', h => by
    refine .cons (by simpa using h 0 a a' A rfl rfl rfl)
      (EqTele0.ofList_of' hw as as' Δ (a :: prev) (by simpa using hl) (by simpa using hl') ?_)
    intro k b b' B hb hb' hB
    have := h (k + 1) b b' B (by simpa using hb) (by simpa using hb') (by simpa using hB)
    simpa using this
  | [], _ :: _, _, _, hl, hl', _ => by simp at hl hl'; omega
  | _ :: _, [], _, _, hl, hl', _ => by simp at hl hl'; omega
  | [], [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, hl, _, _ => by simp at hl

/-- Arguments judgmentally equal to typed arguments form a telescope, equal to them. -/
theorem tele_conv (hW : WfSig S) {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {ps : Tm}
    (hps : IsList ps) (hpt : HasTele0 S Ψ Φ Γ ps D.params []) {X Y : List Tm}
    (hX : HasTele0 S Ψ Φ Γ (Tm.ofList X) (C.argTys d D.params.length) ps.toList.reverse) (hYl : Y.length = X.length)
    (hXY : ∀ j (hj : j < X.length) (hj' : j < Y.length), EqTm0 S Ψ Φ Γ Y[j] X[j]
      ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ ps.toList.reverse))) :
    HasTele0 S Ψ Φ Γ (Tm.ofList Y) (C.argTys d D.params.length) ps.toList.reverse ∧
    EqTele0 S Ψ Φ Γ (Tm.ofList Y) (Tm.ofList X) (C.argTys d D.params.length) ps.toList.reverse := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  have hw := wf_of_tele hpt
  have hpl : ps.toList.length = D.params.length := by simpa using tele_length hpt
  have hXl : X.length = C.args.length := by
    have := tele_length hX; rwa [toList_ofList, argTys_length] at this
  have h0 : ∀ σ, TySub S 0 .one [] Ψ Φ Γ σ I.var :=
    fun σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
  have TP := tySub_params hS hD hpt 0 h0 _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at TP
  have hXget : ∀ j (hj : j < X.length), HasTy0 S Ψ Φ Γ X[j]
      ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ ps.toList.reverse)) := fun j hj => by
    have := tele_get hX j X[j] _ (by rw [toList_ofList]; exact List.getElem?_eq_getElem hj) (argTys_get (by omega))
    rwa [toList_ofList] at this
  have TX := tySub_pointsP hS hW hD hC TP (fun k hk _ => hXget k hk) hpl
  -- the induction along the arguments
  have key : ∀ k, k ≤ C.args.length →
      TySub S 0 .one (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C Y ps.toList.reverse k) 0) I.var ∧
      EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C Y ps.toList.reverse k) 0) I.var
        (lsub (ptL C X ps.toList.reverse k) 0) I.var ∧
      ∀ j (hj : j < k) (hj' : j < Y.length), HasTy0 S Ψ Φ Γ Y[j]
        ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ ps.toList.reverse)) ∧
        ∃ l', EqTm0 S Ψ Φ Γ ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ ps.toList.reverse))
          ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ ps.toList.reverse)) (.univ l') := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simpa [DataDecl.pointCtx, ptL] using TP, ?_, fun j hj _ => absurd hj (Nat.not_lt_zero _)⟩
      simpa [DataDecl.pointCtx, ptL] using EqSub.of_eq TP (fun _ => rfl) (τ2 := I.var)
    | succ k ih =>
      intro hk
      obtain ⟨TY, E, HY⟩ := ih (by omega)
      have hk' : k < C.args.length := by omega
      have hkX : k < X.length := by omega
      have hkY : k < Y.length := by omega
      have hxy := hXY k hkX hkY
      have hyX := (pre_eq hS hT hCt hxy).1
      have hap : HasTy0 S Ψ Φ Γ Y[k]
          ((C.argTy d D.params.length k).substList ((Y.take k).reverse ++ ps.toList.reverse)) ∧
          ∃ l', EqTm0 S Ψ Φ Γ ((C.argTy d D.params.length k).substList ((Y.take k).reverse ++ ps.toList.reverse))
            ((C.argTy d D.params.length k).substList ((X.take k).reverse ++ ps.toList.reverse)) (.univ l') := by
        cases hr : C.isRec k
        · obtain ⟨A, hA⟩ := point_of_not_rec hk' hr
          have hAk : C.argTy d D.params.length k = A := by simp [Ctor.argTy, hA]
          rw [hAk] at hyX ⊢
          have hP := pt_typed hW (htr_of hW d) hD hC hA
          have F := (sub_ty hS hP).2.2 TY (TX k (by omega) (by omega)) E
          rw [pt_inst hW hD hC hA (by omega) (by simp [hpl]) 0 I.var,
            pt_inst hW hD hC hA (by omega) (by simp [hpl]) 0 I.var] at F
          exact ⟨HasTy0.conv hyX (EqTm0.symm F), _, F⟩
        · have hsl : ∀ L, (Tm.data d (Ctor.paramVars D.params.length k)).substList L =
              Tm.data d ((Ctor.paramVars D.params.length k).substList L) := fun L => rfl
          simp only [argTy_rec hr, hsl] at hyX ⊢
          rw [Meta.paramVars_substList hps hpl (by simp; omega)] at hyX ⊢
          rw [Meta.paramVars_substList hps hpl (by simp; omega)]
          obtain ⟨l1, hdt⟩ : ∃ l1, HasTy0 S Ψ Φ Γ (.data d ps) (.univ l1) := by
            rcases pre_ty hS hT hCt hyX with ⟨l1, h⟩ | ⟨l1, h, -⟩
            · exact ⟨l1, h⟩
            · cases h
          exact ⟨hyX, _, EqTm0.refl hdt⟩
      have hFj : ∀ j (hj : j < k + 1) (hj' : j < Y.length), HasTy0 S Ψ Φ Γ Y[j]
          ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ ps.toList.reverse)) ∧
          ∃ l', EqTm0 S Ψ Φ Γ ((C.argTy d D.params.length j).substList ((Y.take j).reverse ++ ps.toList.reverse))
            ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ ps.toList.reverse)) (.univ l') := by
        intro j hj hj'
        by_cases hjk : j < k
        · exact HY j hjk hj'
        · obtain rfl : j = k := by omega
          exact hap
      rw [pointCtx_succ]
      cases hr : C.isRec k
      · simp only [hr, Bool.false_eq_true, if_false, ptL]
        obtain ⟨A, hA⟩ := point_of_not_rec hk' hr
        have hAk : C.argTy d D.params.length k = A := by simp [Ctor.argTy, hA]
        have hgY : Y.getD k .abort = Y[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkY]; rfl
        have hgX : X.getD k .abort = X[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkX]; rfl
        rw [hAk, hgY, hgX]
        obtain ⟨hapY, l', hapE⟩ := hap
        rw [hAk] at hapY hapE hxy
        refine ⟨?_, ?_, hFj⟩
        · have := TY.cons (A := A.ren (C.pointRen k) id) (a := Y[k])
            (by rw [pt_inst hW hD hC hA (by omega) (by simp [hpl]) 0 I.var]; exact hapY)
          rwa [consT_lsub] at this
        · have := E.cons (A := A.ren (C.pointRen k) id) (a1 := Y[k]) (a2 := X[k])
            (by rw [pt_inst hW hD hC hA (by omega) (by simp [hpl]) 0 I.var]; exact EqTm0.conv hxy (EqTm0.symm hapE))
          rwa [consT_lsub, consT_lsub] at this
      · simp only [hr, if_true, ptL]
        exact ⟨TY, E, hFj⟩
  obtain ⟨-, -, HY⟩ := key C.args.length (Nat.le_refl _)
  refine ⟨HasTele0.ofList_of hw Y _ _ (by simp [argTys_length]; omega) (fun k a A ha hA => ?_),
    EqTele0.ofList_of' hw Y X _ _ (by simp [argTys_length]; omega) (by simp [argTys_length]; omega)
      (fun k a a' A ha ha' hA => ?_)⟩
  · have hkY := (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    have hkC : k < C.args.length := by omega
    rw [argTys_get hkC, Option.some.injEq] at hA; subst hA
    exact (HY k hkC hkY).1
  · have hkY := (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha'
    have hkC : k < C.args.length := by omega
    rw [argTys_get hkC, Option.some.injEq] at hA; subst hA
    obtain ⟨-, l', e⟩ := HY k hkC hkY
    exact EqTm0.conv (hXY k (by omega) hkY) (EqTm0.symm e)

/-! ## Projections under interval substitutions -/

theorem upN_var : ∀ k, upN k Tm.var = Tm.var
  | 0 => rfl
  | k + 1 => by rw [upN, upN_var k, up_var]

theorem lams_dsubst (τ : ℕ → I) : ∀ (Ts : List Tm) (b : Tm),
    (lams Ts b).subst Tm.var τ = lams (Ts.map (·.subst Tm.var τ)) (b.subst Tm.var τ)
  | [], _ => rfl
  | T :: Ts, b => by
    show Tm.lam (T.subst Tm.var τ) ((lams Ts b).subst (Tm.up Tm.var) τ) = _
    rw [up_var, lams_dsubst τ Ts b]; rfl

theorem branchesOf_dsubst (hS : SigClosed S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) {ps P : Tm}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (body : ℕ → Ctor → Tm) (τ : ℕ → I) :
    (branchesOf D d ps P body).subst Tm.var τ =
      branchesOf D d (ps.subst Tm.var τ) (P.subst Tm.var τ) (fun c' C' => (body c' C').subst Tm.var τ) := by
  unfold branchesOf
  rw [ofList_subst]
  congr 1
  apply List.ext_getElem (by simp)
  intro c' h1 h2
  simp only [List.getElem_map, List.getElem_mapIdx]
  have hcl : c' < D.ctors.length := by simpa using h2
  have hc' : D.ctors[c']? = some D.ctors[c'] := List.getElem?_eq_getElem hcl
  rw [lams_dsubst, List.map_append, List.map_map, List.map_map]
  congr 2
  · apply List.map_congr_left; intro k hk
    simp only [Function.comp]
    have := branchArgTy_subst (σ := Tm.var) (τ := τ) (argTy_closed hS hD hc' k) hps hpl
    rwa [upN_var] at this
  · apply List.map_congr_left; intro s hs
    simp only [Function.comp]
    have := branchIhTy_subst (σ := Tm.var) (τ := τ) (List.mem_range.1 hs) P
    rwa [upN_var, up_var] at this

section
variable {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {j : ℕ}

theorem projQBody_dsubst (hS : SigClosed S) (hD : S[d]? = some (.data D)) (hcC : D.ctors[c]? = some C)
    (hj : j < C.args.length) {ps : Tm} (hps : IsList ps) (hpl : ps.toList.length = D.params.length)
    (τ : ℕ → I) (c' : ℕ) (C' : Ctor) :
    (projQBody d D.params.length C ps c j c' C').subst Tm.var τ = projQBody d D.params.length C (ps.subst Tm.var τ) c j c' C' := by
  unfold projQBody
  split
  · have hcl := argTy_closed hS hD hcC j
    rw [substList_subst (by simpa [argVarsE, Nat.min_eq_left hj.le, Nat.add_comm, hpl] using hcl), List.map_append]
    congr 2
    · conv => rhs; rw [← List.map_id (List.take j (argVarsE C.recPos.length C.args.length)).reverse]
      apply List.map_congr_left; intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take (List.mem_reverse.1 hx))
      rfl
    · rw [toList_subst hps, List.map_reverse]
  · show Tm.pi _ ((Tm.data d ps).subst (Tm.up Tm.var) τ) = _
    rw [up_var]; rfl


theorem projBody_dsubst {ps : Tm} (τ : ℕ → I) (c' : ℕ) (C' : Ctor) :
    (projBody d C ps c j c' C').subst Tm.var τ = projBody d C (ps.subst Tm.var τ) c j c' C' := by
  unfold projBody
  split
  · rfl
  · show Tm.lam _ ((Tm.var 0).subst (Tm.up Tm.var) τ) = _
    rw [up_var]; rfl

theorem projQ_dsubst (hS : SigClosed S) (hD : S[d]? = some (.data D)) (hcC : D.ctors[c]? = some C)
    (hj : j < C.args.length) {ps : Tm} (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (τ : ℕ → I) :
    (projQ d D ps c C j).subst Tm.var τ = projQ d D (ps.subst Tm.var τ) c C j := by
  unfold projQ
  show Tm.elim d (ps.subst Tm.var τ) ((Tm.univ D.level).subst (Tm.up Tm.var) τ)
    ((branchesOf D d ps (.univ D.level) (projQBody d D.params.length C ps c j)).subst Tm.var τ) (Tm.var 0) = _
  rw [branchesOf_dsubst hS hD hps hpl]
  congr 2
  funext c' C'
  exact projQBody_dsubst hS hD hcC hj hps hpl τ c' C'

theorem proj_dsubst (hS : SigClosed S) (hD : S[d]? = some (.data D)) (hcC : D.ctors[c]? = some C)
    (hj : j < C.args.length) {ps : Tm} (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (τ : ℕ → I)
    (t : Tm) :
    (proj d D ps c C j t).subst Tm.var τ = proj d D (ps.subst Tm.var τ) c C j (t.subst Tm.var τ) := by
  unfold proj
  show Tm.elim d (ps.subst Tm.var τ) ((projQ d D ps c C j).subst (Tm.up Tm.var) τ)
    ((branchesOf D d ps (projQ d D ps c C j) (projBody d C ps c j)).subst Tm.var τ) (t.subst Tm.var τ) = _
  rw [up_var, branchesOf_dsubst hS hD hps hpl, projQ_dsubst hS hD hcC hj hps hpl]
  congr 2
  funext c' C'
  exact projBody_dsubst τ c' C'

end

end

end Model.Canon
