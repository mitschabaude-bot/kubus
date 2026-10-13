import Model.Canon.FormersData

/-!
# Canonicity: retyping constructor arguments along equal parameters

Arguments of a constructor at parameters `qs` are arguments at judgmentally equal parameters
`ps`: the point argument types are instances of their types over the point context (typed in
the prefix signature), and the parameters are related by injectivity of inductive types.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

variable {S : Sig}

theorem tele_isList {Ψ : ℕ} {Φ : I} {Γ : Ctx} : ∀ {ts : Tm} {Δ prev : List Tm}, HasTele0 S Ψ Φ Γ ts Δ prev →
    ts = Tm.ofList ts.toList
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ h1 => by simp only [Tm.toList, Tm.ofList]; rw [← tele_isList h1]

theorem htr_of (hW : WfSig S) (d : ℕ) {Ψ Φ Γ t A} (h : HasTy (S.take d) Ψ Φ Γ t A) : HasTy0 S Ψ Φ Γ t A :=
  sigwk_ty (fun _ _ hj => (getElem?_take_some hj).2) (spec_to_minimal (wfSig_take hW d) h)

theorem args_retype (hW : WfSig S) {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {Ψ : ℕ} {Φ : I} {Γ : Ctx}
    {qs ps args : Tm} {l : ℕ} (hqs : qs = Tm.ofList qs.toList) (hps : ps = Tm.ofList ps.toList)
    (hq : HasTele0 S Ψ Φ Γ qs D.params []) (hp : HasTele0 S Ψ Φ Γ ps D.params [])
    (e : EqTm0 S Ψ Φ Γ (.data d qs) (.data d ps) (.univ l))
    (ha : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) qs.toList.reverse) :
    HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse ∧
      ∀ j (hj : j < args.toList.length), ∃ l', EqTm0 S Ψ Φ Γ
        ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ qs.toList.reverse))
        ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ ps.toList.reverse)) (.univ l') := by
  have hS := sigClosed_of_wfSig hW
  have hw := wf_of_tele hq
  have hql : qs.toList.length = D.params.length := by simpa using tele_length hq
  have hpl : ps.toList.length = D.params.length := by simpa using tele_length hp
  have hal : args.toList.length = C.args.length := by
    have := tele_length ha; rwa [argTys_length] at this
  have h0 : ∀ σ, TySub S 0 .one [] Ψ Φ Γ σ I.var :=
    fun σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
  have TPq := tySub_params hS hD hq 0 h0 _ (Nat.le_refl _)
  have TPp := tySub_params hS hD hp 0 h0 _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at TPq
  rw [List.take_of_length_le (by omega)] at TPp
  have Tq := tySub_points hS hW hD hC TPq ha hql
  have E0 := eqSub_params hS hW (htr_of hW d) hD hqs hps e hq hp 0 I.var I.var _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at E0
  -- the induction along the arguments
  have key : ∀ k, k ≤ C.args.length →
      TySub S 0 .one (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C args.toList ps.toList.reverse k) 0) I.var ∧
      EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C args.toList qs.toList.reverse k) 0) I.var
        (lsub (ptL C args.toList ps.toList.reverse k) 0) I.var ∧
      ∀ j (hj : j < k) (hj' : j < args.toList.length), HasTy0 S Ψ Φ Γ (args.toList[j]'hj')
        ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ ps.toList.reverse)) ∧
        ∃ l', EqTm0 S Ψ Φ Γ ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ qs.toList.reverse))
          ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ ps.toList.reverse)) (.univ l') := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simpa [DataDecl.pointCtx, ptL] using TPp, by simpa [DataDecl.pointCtx, ptL] using E0,
        fun j hj _ => absurd hj (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨Tp, E, Hp⟩ := ih (by omega)
      have hk' : k < C.args.length := by omega
      have hak : args.toList[k]? = some (args.toList[k]'(by omega)) := List.getElem?_eq_getElem _
      have haq := tele_get ha k _ _ hak (argTys_get hk')
      -- the argument at `ps`
      have hap : HasTy0 S Ψ Φ Γ (args.toList[k]'(by omega))
          ((C.argTy d D.params.length k).substList ((args.toList.take k).reverse ++ ps.toList.reverse)) ∧
          ∃ l', EqTm0 S Ψ Φ Γ ((C.argTy d D.params.length k).substList ((args.toList.take k).reverse ++ qs.toList.reverse))
            ((C.argTy d D.params.length k).substList ((args.toList.take k).reverse ++ ps.toList.reverse)) (.univ l') := by
        cases hr : C.isRec k
        · obtain ⟨A, hA⟩ := point_of_not_rec hk' hr
          have hAk : C.argTy d D.params.length k = A := by simp [Ctor.argTy, hA]
          rw [hAk] at haq ⊢
          have hP := pt_typed hW (htr_of hW d) hD hC hA
          have F := (sub_ty hS hP).2.2 (Tq k (by omega)) Tp E
          rw [pt_inst hW hD hC hA (by omega) (by simp [hql]) 0 I.var,
            pt_inst hW hD hC hA (by omega) (by simp [hpl]) 0 I.var] at F
          exact ⟨HasTy0.conv haq F, _, F⟩
        · have hsl : ∀ L, (Tm.data d (Ctor.paramVars D.params.length k)).substList L =
              Tm.data d ((Ctor.paramVars D.params.length k).substList L) := fun L => rfl
          simp only [argTy_rec hr, hsl] at haq ⊢
          rw [Meta.paramVars_substList hqs hql (by simp; omega)] at haq ⊢
          rw [Meta.paramVars_substList hps hpl (by simp; omega)]
          exact ⟨HasTy0.conv haq e, _, e⟩
      have hFj : ∀ j (hj : j < k + 1) (hj' : j < args.toList.length), HasTy0 S Ψ Φ Γ (args.toList[j]'hj')
          ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ ps.toList.reverse)) ∧
          ∃ l', EqTm0 S Ψ Φ Γ ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ qs.toList.reverse))
            ((C.argTy d D.params.length j).substList ((args.toList.take j).reverse ++ ps.toList.reverse)) (.univ l') := by
        intro j hj hj'
        by_cases hjk : j < k
        · exact Hp j hjk hj'
        · obtain rfl : j = k := by omega
          exact hap
      rw [pointCtx_succ]
      cases hr : C.isRec k
      · simp only [hr, Bool.false_eq_true, if_false, ptL]
        obtain ⟨A, hA⟩ := point_of_not_rec hk' hr
        have hAk : C.argTy d D.params.length k = A := by simp [Ctor.argTy, hA]
        have hgd : args.toList.getD k .abort = args.toList[k]'(by omega) := by
          rw [List.getD_eq_getElem?_getD, hak]; rfl
        rw [hAk, hgd]
        rw [hAk] at hap haq
        replace hap := hap.1
        refine ⟨?_, ?_, hFj⟩
        · have := Tp.cons (A := A.ren (C.pointRen k) id) (a := args.toList[k]'(by omega))
            (by rw [pt_inst hW hD hC hA (by omega) (by simp [hpl]) 0 I.var]; exact hap)
          rwa [consT_lsub] at this
        · have := E.cons (A := A.ren (C.pointRen k) id) (a1 := args.toList[k]'(by omega))
            (a2 := args.toList[k]'(by omega))
            (by rw [pt_inst hW hD hC hA (by omega) (by simp [hql]) 0 I.var]; exact EqTm0.refl haq)
          rwa [consT_lsub, consT_lsub] at this
      · simp only [hr, if_true, ptL]
        exact ⟨Tp, E, hFj⟩
  obtain ⟨-, -, H⟩ := key C.args.length (Nat.le_refl _)
  refine ⟨?_, fun j hj => (H j (by omega) hj).2⟩
  rw [tele_isList ha]
  refine HasTele0.ofList_of hw _ _ _ (by rw [argTys_length]; exact hal) fun k a A hak hA => ?_
  have hk : k < C.args.length := by rw [← argTys_length C d D.params.length]; exact (List.getElem?_eq_some_iff.1 hA).1
  rw [argTys_get hk] at hA
  obtain rfl := Option.some.inj hA
  obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.1 hak
  exact (H k hk (by omega)).1

end Model.Canon
