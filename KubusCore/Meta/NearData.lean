import KubusCore.Meta.Final

/-!
# Metatheory: telescopes of the inductive types along equal instantiations

Elementwise equal telescopes (`EqTeleS`, without `dataInj`), and the transfer of the parameter
and argument telescopes of an inductive type to equal instantiations (types of the parameters
and point arguments typed by `DataDecl.Wf`).
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- Elementwise equality of telescopes (the structural rules of `EqTele0`). -/
inductive EqTeleS (S : Sig) : Nat → I → Ctx → Tm → Tm → List Tm → List Tm → Prop
  | nil {Ψ Φ Γ prev} : Wf0 S Ψ Φ Γ → EqTeleS S Ψ Φ Γ .tnil .tnil [] prev
  | cons {Ψ Φ Γ a a' as as' A Δ prev} : EqTm0 S Ψ Φ Γ a a' (A.substList prev) →
      EqTeleS S Ψ Φ Γ as as' Δ (a :: prev) → EqTeleS S Ψ Φ Γ (.tcons a as) (.tcons a' as') (A :: Δ) prev

theorem EqTeleS.toEqTele0 {Ψ Φ Γ} : ∀ {ts ts' Δ prev}, EqTeleS S Ψ Φ Γ ts ts' Δ prev → EqTele0 S Ψ Φ Γ ts ts' Δ prev
  | _, _, _, _, .nil h => .nil h
  | _, _, _, _, .cons h hs => .cons h hs.toEqTele0

theorem EqTeleS.get {Ψ Φ Γ} : ∀ {ts ts' Δ prev}, EqTeleS S Ψ Φ Γ ts ts' Δ prev →
    ∀ (k : Nat) (a a' A : Tm), ts.toList[k]? = some a → ts'.toList[k]? = some a' → Δ[k]? = some A →
    EqTm0 S Ψ Φ Γ a a' (A.substList ((ts.toList.take k).reverse ++ prev))
  | _, _, _, _, .nil _ => fun k a a' A h _ _ => by simp [Tm.toList] at h
  | _, _, _, _, .cons h0 h1 => fun k a a' A ha ha' hA => by
    cases k with
    | zero =>
      simp only [Tm.toList, List.getElem?_cons_zero, Option.some.injEq] at ha ha' hA
      subst ha ha' hA; simpa using h0
    | succ k =>
      simp only [Tm.toList, List.getElem?_cons_succ] at ha ha' hA
      have := h1.get k a a' A ha ha' hA
      simpa [Tm.toList, List.take_succ_cons] using this

theorem EqTeleS.length' {Ψ Φ Γ} : ∀ {ts ts' Δ prev}, EqTeleS S Ψ Φ Γ ts ts' Δ prev →
    ts'.toList.length = Δ.length
  | _, _, _, _, .nil _ => rfl
  | _, _, _, _, .cons _ h1 => by simp [Tm.toList, h1.length']

theorem EqTeleS.isList' {Ψ Φ Γ} : ∀ {ts ts' Δ prev}, EqTeleS S Ψ Φ Γ ts ts' Δ prev →
    ts' = Tm.ofList ts'.toList
  | _, _, _, _, .nil _ => rfl
  | _, _, _, _, .cons _ h1 => by simp only [Tm.toList, Tm.ofList]; rw [← h1.isList']

/-- The prefix transfer from a well-formed signature. -/
theorem htr_of_wf (hW : WfSig S) {d : Nat} {D : DataDecl} (hD : S[d]? = some (.data D)) :
    ∀ {Ψ' Φ' Γ' t A}, HasTy (S.take d) Ψ' Φ' Γ' t A → HasTy0 S Ψ' Φ' Γ' t A := by
  intro Ψ' Φ' Γ' t A e
  have hd : d < S.length := (List.getElem?_eq_some_iff.1 hD).1
  obtain ⟨hT', hC'⟩ := wf_typed d (S.take d) (by simp [List.length_take]; omega) (wfSig_take hW d)
  have hinc : ∀ (j : Nat) (e : Entry), (S.take d)[j]? = some e → S[j]? = some e :=
    fun j e h => (getElem?_take_some h).2
  exact sigwk_ty hinc (spec_to_minimal_of (wfSig_take hW d) hT' hC' e)

/-! ## Parameters -/

theorem params_near (hS : SigClosed S) (hW : WfSig S) {d : Nat} {D : DataDecl} (hD : S[d]? = some (.data D))
    {Ψ Φ Γ} {ps ps' : Tm} (hpres : ∀ {t u A}, EqTm0 S Ψ Φ Γ t u A → HasTy0 S Ψ Φ Γ u A)
    (ht : HasTele0 S Ψ Φ Γ ps D.params []) (es : EqTeleS S Ψ Φ Γ ps ps' D.params []) (c : Nat)
    (τ τ' : Nat → I) :
    ∀ j, j ≤ D.params.length →
      TySub S 0 .one (D.paramCtx j) Ψ Φ Γ (lsub (ps'.toList.take j).reverse c) τ' ∧
      EqSub S 0 (D.paramCtx j) Ψ Φ Γ (lsub (ps.toList.take j).reverse c) τ (lsub (ps'.toList.take j).reverse c) τ' ∧
      ∀ (i : Nat) (A : Tm), i < j → D.params[i]? = some A →
        HasTy0 S Ψ Φ Γ (ps'.toList.getD i .abort) (A.substList (ps'.toList.take i).reverse)
  | 0, _ => by
    have hw := wf_of_tele ht
    refine ⟨?_, ⟨fun x A hx => by simp [DataDecl.paramCtx, Ctx.lookup] at hx, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
      fun i A hi => absurd hi (Nat.not_lt_zero _)⟩
    simpa [DataDecl.paramCtx] using
      (tySub_nil (S := S) (Ψs := 0) (Φs := .one) (σ := lsub [] c) (τ := τ') (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw)
  | j + 1, hj => by
    have hw := wf_of_tele ht
    have hpl : ps.toList.length = D.params.length := by simpa using tele_length ht
    have hpl' : ps'.toList.length = D.params.length := by simpa using es.length'
    obtain ⟨T2, E, hel⟩ := params_near hS hW hD hpres ht es c τ τ' j (by omega)
    have T1 := tySub_params hS hD ht c (fun σ => tySub_nil (Ψs := 0) (Φs := .one) (τ := τ) (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw) j (by omega)
    have hA : D.params[j]? = some D.params[j] := List.getElem?_eq_getElem (by omega)
    have hcl := hS.params d D j _ hD hA
    have hl1 : ((ps.toList.take j).reverse).length = j := by simp; omega
    have hl2 : ((ps'.toList.take j).reverse).length = j := by simp; omega
    have hp1 : ps.toList[j]? = some ps.toList[j] := List.getElem?_eq_getElem (by omega)
    have hp2 : ps'.toList[j]? = some ps'.toList[j] := List.getElem?_eq_getElem (by omega)
    have e := es.get j _ _ _ hp1 hp2 hA
    rw [List.append_nil] at e
    have ha2 := hpres e
    have ha2' : HasTy0 S Ψ Φ Γ ps'.toList[j] (D.params[j].substList (ps'.toList.take j).reverse) := by
      rcases ((hW.2 d D hD).2.1 j _ hA).2.2 with hAt | ⟨k, -, hAk⟩
      · have F := (sub_ty hS (htr_of_wf hW hD hAt)).2.2 T1 T2 E
        rw [subst_lsub_closed (by rw [hl1]; exact hcl), subst_lsub_closed (by rw [hl2]; exact hcl)] at F
        exact HasTy0.conv ha2 F
      · rw [hAk] at ha2 ⊢; exact ha2
    have ht1 : (ps.toList.take (j + 1)).reverse = ps.toList[j] :: (ps.toList.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
    have ht2 : (ps'.toList.take (j + 1)).reverse = ps'.toList[j] :: (ps'.toList.take j).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; simp
    have T2' := T2.cons (A := D.params[j]) (a := ps'.toList[j])
      (by rw [subst_lsub_closed (by rw [hl2]; exact hcl)]; exact ha2')
    have E' := E.cons (A := D.params[j]) (a1 := ps.toList[j]) (a2 := ps'.toList[j])
      (by rw [subst_lsub_closed (by rw [hl1]; exact hcl)]; exact e)
    rw [consT_lsub] at T2'
    rw [consT_lsub, consT_lsub] at E'
    rw [paramCtx_succ D (by omega), ht1, ht2]
    refine ⟨T2', E', fun i A hi hAi => ?_⟩
    by_cases hij : i = j
    · subst hij; rw [hA] at hAi; cases hAi
      rw [List.getD_eq_getElem?_getD, hp2]; exact ha2'
    · exact hel i A (by omega) hAi

theorem params_tele (hS : SigClosed S) (hW : WfSig S) {d : Nat} {D : DataDecl} (hD : S[d]? = some (.data D))
    {Ψ Φ Γ} {ps ps' : Tm} (hpres : ∀ {t u A}, EqTm0 S Ψ Φ Γ t u A → HasTy0 S Ψ Φ Γ u A)
    (ht : HasTele0 S Ψ Φ Γ ps D.params []) (es : EqTeleS S Ψ Φ Γ ps ps' D.params []) :
    HasTele0 S Ψ Φ Γ ps' D.params [] := by
  obtain ⟨-, -, hel⟩ := params_near hS hW hD hpres ht es 0 I.var I.var _ (Nat.le_refl _)
  rw [es.isList']
  apply HasTele0.ofList_of (wf_of_tele ht) _ _ _ es.length'
  intro k a A ha hA
  have hk : k < D.params.length := (List.getElem?_eq_some_iff.1 hA).1
  have := hel k A hk hA
  rw [List.getD_eq_getElem?_getD, ha] at this
  simpa using this

theorem tele_isList {Ψ Φ Γ} : ∀ {ts Δ prev}, HasTele0 S Ψ Φ Γ ts Δ prev → ts = Tm.ofList ts.toList
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ h1 => by simp only [Tm.toList, Tm.ofList]; rw [← tele_isList h1]

/-! ## Constructor arguments -/

theorem args_near (hS : SigClosed S) (hW : WfSig S) {d : Nat} {D : DataDecl} {c : Nat} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C)
    {Ψ Φ Γ} {ps ps' args args' : Tm} (hpres : ∀ {t u A}, EqTm0 S Ψ Φ Γ t u A → HasTy0 S Ψ Φ Γ u A)
    (ht : HasTele0 S Ψ Φ Γ ps D.params []) (es : EqTeleS S Ψ Φ Γ ps ps' D.params [])
    (hat : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (eas : EqTeleS S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse)
    {l : Nat} (edata : EqTm0 S Ψ Φ Γ (data d ps) (data d ps') (univ l)) :
    HasTele0 S Ψ Φ Γ args' (C.argTys d D.params.length) ps'.toList.reverse := by
  have hw := wf_of_tele ht
  have hpl : ps.toList.length = D.params.length := by simpa using tele_length ht
  have hpl' : ps'.toList.length = D.params.length := by simpa using es.length'
  have hal : args.toList.length = C.args.length := by
    have := tele_length hat; rwa [argTys_length] at this
  have hal' : args'.toList.length = C.args.length := by
    have := eas.length'; rwa [argTys_length] at this
  have hpsL := tele_isList ht
  have hpsL' := es.isList'
  have h0 : ∀ σ, TySub S 0 .one [] Ψ Φ Γ σ I.var :=
    fun σ => tySub_nil (fun i hi => absurd hi (Nat.not_lt_zero _)) (ent_one _) hw
  have hP := tySub_params hS hD ht 0 h0 _ (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at hP
  have key : ∀ k, k ≤ C.args.length →
      TySub S 0 .one (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C args'.toList ps'.toList.reverse k) 0) I.var ∧
      EqSub S 0 (D.pointCtx d C k) Ψ Φ Γ (lsub (ptL C args.toList ps.toList.reverse k) 0) I.var
        (lsub (ptL C args'.toList ps'.toList.reverse k) 0) I.var ∧
      ∀ i, i < k → HasTy0 S Ψ Φ Γ (args'.toList.getD i .abort)
        ((C.argTy d D.params.length i).substList ((args'.toList.take i).reverse ++ ps'.toList.reverse)) := by
    intro k hk
    induction k with
    | zero =>
      obtain ⟨T, E, -⟩ := params_near hS hW hD hpres ht es 0 I.var I.var _ (Nat.le_refl _)
      rw [List.take_of_length_le (show ps'.toList.length ≤ D.params.length by omega)] at T
      rw [List.take_of_length_le (show ps'.toList.length ≤ D.params.length by omega),
        List.take_of_length_le (show ps.toList.length ≤ D.params.length by omega)] at E
      have hpc : D.pointCtx d C 0 = D.paramCtx D.params.length := by simp [DataDecl.pointCtx]
      simp only [ptL, hpc]
      exact ⟨T, E, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      have hkn : k < C.args.length := by omega
      obtain ⟨T', E, Tel⟩ := ih (by omega)
      have TA := tySub_points hS hW hD hC hP hat hpl k (by omega)
      have ha1 : args.toList[k]? = some (args.toList.getD k .abort) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have ha2 : args'.toList[k]? = some (args'.toList.getD k .abort) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have e := eas.get k _ _ _ ha1 ha2 (argTys_get hkn)
      have ha2t := hpres e
      rw [pointCtx_succ]
      cases hr : C.isRec k
      · simp only [hr, Bool.false_eq_true, if_false, ptL]
        obtain ⟨A0, hA0⟩ := point_of_not_rec hkn hr
        have hAk : C.argTy d D.params.length k = A0 := by simp [Ctor.argTy, hA0]
        rw [hAk]
        have hP11 := pt_typed hW (htr_of_wf hW hD) hD hC hA0
        have F := (sub_ty hS hP11).2.2 TA T' E
        rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var,
          pt_inst hW hD hC hA0 (by omega) (by simp [hpl']) 0 I.var] at F
        rw [hAk] at e ha2t
        have ha2' := HasTy0.conv ha2t F
        have T'' := T'.cons (A := A0.ren (C.pointRen k) id) (a := args'.toList.getD k .abort)
          (by rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl']) 0 I.var]; exact ha2')
        have E' := E.cons (A := A0.ren (C.pointRen k) id) (a1 := args.toList.getD k .abort)
          (a2 := args'.toList.getD k .abort)
          (by rw [pt_inst hW hD hC hA0 (by omega) (by simp [hpl]) 0 I.var]; exact e)
        rw [consT_lsub] at T''
        rw [consT_lsub, consT_lsub] at E'
        refine ⟨T'', E', fun i hi => ?_⟩
        by_cases hik : i = k
        · subst hik; rw [hAk]; exact ha2'
        · exact Tel i (by omega)
      · simp only [hr, if_true, ptL]
        refine ⟨T', E, fun i hi => ?_⟩
        by_cases hik : i = k
        · subst hik
          have hAk := argTy_rec' (np := D.params.length) (d := d) hr
          rw [hAk, substList_eq] at e
          simp only [Tm.subst] at e
          rw [← substList_eq, paramVars_substList hpsL hpl (by simp; omega)] at e
          rw [hAk, substList_eq]; simp only [Tm.subst]
          rw [← substList_eq, paramVars_substList hpsL' hpl' (by simp; omega)]
          exact HasTy0.conv (hpres e) edata
        · exact Tel i (by omega)
  obtain ⟨-, -, Tel⟩ := key _ (Nat.le_refl _)
  rw [eas.isList']
  apply HasTele0.ofList_of hw _ _ _ (by rw [hal', argTys_length])
  intro k a A ha hA
  have hk : k < C.args.length := by
    have := (List.getElem?_eq_some_iff.1 hA).1; rwa [argTys_length] at this
  rw [argTys_get hk] at hA; cases hA
  have := Tel k hk
  rw [List.getD_eq_getElem?_getD, ha] at this
  exact this

end KubusCore.Meta
