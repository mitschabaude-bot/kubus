import Model.Whnf.Valid2ElimH9

/-!
# Elimination of simple boundary trees

The constructor computation property at earlier constructors identifies the boundary interpreter
with elimination, assuming computable induction hypotheses at its recursive leaves.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- Constructor computation, given computable recursive eliminations. -/
def ECSt2 (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm) (c : ℕ) : Prop :=
  ∀ {k : ℕ} (ρ : ISub k K) {C : Ctor} {q : Tm} {X : List Tm} {rs : List I}, D.ctors[c]? = some C →
    HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ)) →
    (∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X.getD i .abort)) →
    (∀ i, i ∈ C.recPos → RE2 S k ((M.isub ρ).inst (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))) →
    RE2 S k ((M.isub ρ).inst (.con d c q (Tm.ofList X) rs))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (.con d c q (Tm.ofList X) rs))
      (Tm.papps (ecTm d C c (P.isub ρ) (M.isub ρ) (bs.isub ρ) X) rs)

/-- Apply a related branch to related arguments and arbitrary related induction hypotheses. -/
theorem branchApp_rel2 (hW : WfSig S) {d c : ℕ} {D : DataDecl} {C : Ctor}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) {ps M b b' : Tm}
    (hpl : ps.toList.length = D.params.length) (hbr : RE2 S k (D.branchTy d c C ps M) b b')
    (X X' Y Y' : List Tm) (hX : X.length = C.args.length) (hX' : X'.length = C.args.length)
    (hY : Y.length = C.recPos.length) (hY' : Y'.length = C.recPos.length)
    (ha : ∀ i (hi : i < X.length) (hi' : i < X'.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ ps.toList.reverse)) X[i] X'[i])
    (hi : ∀ s (hs : s < C.recPos.length), RE2 S k (M.inst (X.getD (C.recPos.getD s 0) .abort))
      (Y.getD s .abort) (Y'.getD s .abort))
    {rs rs' : List I} (hrs : rs.length = C.dims) (he : IEqL rs rs')
    (hsc : ∀ r ∈ rs, r.Scoped k) (hsc' : ∀ r ∈ rs', r.Scoped k) :
    RE2 S k (M.inst (.con d c ps (Tm.ofList X) rs))
      (Tm.papps (Tm.apps b (X ++ Y)) rs) (Tm.papps (Tm.apps b' (X' ++ Y')) rs') := by
  rw [Meta.branchTy_eq] at hbr
  have hbr0 : RE2 S k ((((List.range C.args.length).map (DataDecl.branchArgTy d D.params.length C ps)).foldr Tm.pi
      (((List.range C.recPos.length).map (DataDecl.branchIhTy C M)).foldr Tm.pi
        (ipis C.dims (DataDecl.branchBody d c C ps M)))).substList []) b b' := by rw [substList_nil]; exact hbr
  have h1 := RE2_apps hW X X' (by simp [hX]) (by omega) hbr0 (fun j hj hj' hjΔ => by
    simp only [List.getElem_map, List.getElem_range, List.append_nil]
    rw [branchArgTy_substList (sigClosed_of_wfSig hW) hD hC hpl (by simp; omega)]
    exact ha j hj hj')
  rw [List.append_nil] at h1
  have h2 := RE2_apps hW Y Y' (Δ := (List.range C.recPos.length).map (DataDecl.branchIhTy C M))
    (by simp [hY]) (by omega) h1 (fun s hs hs' hsΔ => by
      simp only [List.length_map, List.length_range] at hsΔ
      simp only [List.getElem_map, List.getElem_range]
      rw [branchIhTy_substList M hsΔ (by simp; omega) hX]
      have R := hi s hsΔ
      rwa [getD_eq_get' hs, getD_eq_get' hs'] at R)
  rw [substList_eq] at h2
  have h3 := RE2_papps hW _ _ he hsc hsc' (by rw [hrs]; exact h2)
  rw [branchBody_inst (by rw [hY]) hX hrs, apps_append, apps_append] at h3
  exact h3

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
  {K : ℕ} {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
  (hPP : RT2 S K (.data d P) (.data d P))
  (H : ElimRelH S d D K P M bs P M bs)
include hW hD hP hPP H

/-- Elimination agrees with the boundary interpreter at simple trees of earlier constructors. -/
theorem bndInterp_rel2 {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    (ihCR : ∀ c' < c, CRSt S d D K P c') (ihEC : ∀ c' < c, ECSt2 S d D K P M bs c')
    {k : ℕ} (ρ : ISub k K) (q : Tm) (hql : q.toList.length = D.params.length) (X : List Tm) (rs : List I) (hX : X.length = C.args.length)
    (ha : ∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X.getD i .abort))
    (hi : ∀ i, i ∈ C.recPos → RE2 S k ((M.isub ρ).inst (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))
      (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (X.getD i .abort))) :
    ∀ (N : ℕ) (e : Tm), sizeOf e < N → Ctor.simpleB D.ctors d D.params.length c C.args.length C e = true →
      e.closedB (D.params.length + C.args.length) C.dims = true →
      bndRel S k d D.params.length C.args.length C D.ctors (P.isub ρ) (P.isub ρ) X X rs e →
      HasTy S k .one [] (Ctor.bndAt e q.toList X rs) (.data d (P.isub ρ)) →
      HasTy S k .one [] (Ctor.bndAt e (P.isub ρ).toList X rs) (.data d (P.isub ρ)) →
      RE2 S k ((M.isub ρ).inst (Ctor.bndAt e q.toList X rs))
        (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (Ctor.bndAt e q.toList X rs))
        (bndInterp2 d D C (P.isub ρ) (M.isub ρ) (bs.isub ρ) X rs e) := by
  have hPρ := HasTy.isubS hW hP ρ
  have hPl := (dataLit_rel hW hD hP hPP ρ).2.2.2.2.2.1
  have hplen : (P.isub ρ).toList.length = D.params.length := by
    have := data_len_of hW (⟨_, .inl hPρ⟩ : IsTyK S k (.data d (P.isub ρ)))
    rwa [dataD_eq hW hD] at this
  intro N
  induction N with
  | zero => intro e hsz; omega
  | succ N ih =>
    intro e hsz hs hcl hR ht htP
    cases e
    case var j =>
      simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
      rw [bndAt_var rs (by omega), bndInterp2_var, hX]
      exact hi _ (List.mem_filter.2 ⟨List.mem_range.2 (by omega), hs.2⟩)
    case con d' c' qs as ss =>
      obtain ⟨hdd, hcc, hqs, C', hC', hal, hrl, hsa, has⟩ := simpleB_con_inv hs
      subst d' qs
      let Z := as.toList.map (fun a => Ctor.bndAt a q.toList X rs)
      let ZP := as.toList.map (fun a => Ctor.bndAt a (P.isub ρ).toList X rs)
      let ss1 := ss.map (fun r => Ctor.cofAt r rs)
      have hZ : Z.length = C'.args.length := by simp [Z, hal]
      have eB : Ctor.bndAt (.con d c' (Ctor.paramVars D.params.length C.args.length) as ss)
          q.toList X rs = .con d c' (Tm.ofList q.toList) (Tm.ofList Z) ss1 := by
        rw [bndAt_con, bndAt_paramVars rs hql hX]
        conv => lhs; rw [has]
        rw [bndAt_ofList]
        rfl
      have eBP : Ctor.bndAt (.con d c' (Ctor.paramVars D.params.length C.args.length) as ss)
          (P.isub ρ).toList X rs = .con d c' (P.isub ρ) (Tm.ofList ZP) ss1 := by
        rw [bndAt_con, bndAt_paramVars rs hplen hX, ← hPl]
        conv => lhs; rw [has]
        rw [bndAt_ofList]
        rfl
      rw [eB] at ht ⊢
      rw [eBP] at htP
      have hRA : bndRelArgs S k d D.params.length C.args.length C D.ctors (P.isub ρ) (P.isub ρ)
          X X rs C' 0 [] as := by simpa only [bndRel, hC'] using hR
      have hrecBase : ∀ i (hai : i < as.toList.length), C'.isRec i = true →
          RE2 S k (.data d (P.isub ρ)) (Z.getD i .abort) (Z.getD i .abort) := by
        intro i hai hr
        have hs0 := (simpleArgs_get as 0 hsa i hai).1 (by simpa using hr)
        have hR0 := (bndRelArgs_get as 0 [] hRA i hai).2 (by simpa using hr)
        obtain ⟨-, hacl, -⟩ := closedB_con hcl
        have hc0 := closed_toList hacl _ (List.getElem_mem hai)
        have hty : HasTy S k .one [] (Z.getD i .abort) (.data d (P.isub ρ)) := by
          obtain ⟨htele, -⟩ := con_inv hW hD hC' ht hPρ
          have ht0 := HasTele0.get htele (k := i) (a := Z.getD i .abort)
            (by rw [toList_ofList, getD_eq_get' (show i < Z.length by simp [Z]; omega), List.getElem?_eq_getElem (by simp [Z]; omega)])
            (argTys_get (by omega))
          rw [argTy_rec_inst hr hPl hplen (by simp [toList_ofList]; omega)] at ht0
          exact minimal_to_spec ht0
        rw [show Z.getD i .abort = Ctor.bndAt as.toList[i] q.toList X rs by
          rw [getD_eq_get' (by simp [Z]; omega)]; simp only [Z, List.getElem_map]] at hty ⊢
        exact bnd_rel hW hD hP hPP ihCR hC N _ (by
          have := sizeOf_con_arg (d' := d) (c' := c') (ps0 := Ctor.paramVars D.params.length C.args.length)
            (rs0 := ss) (List.getElem_mem hai)
          omega) hs0 ρ hql hql hX hX (forall2_ieq_refl _) ha hR0 hty hty
      have hargsZ : ∀ i (_hi : i < C'.args.length), RE2 S k ((C'.argTy d D.params.length i).substList
          ((Z.take i).reverse ++ (P.isub ρ).toList.reverse)) (Z.getD i .abort) (Z.getD i .abort) := by
        intro i hi'
        have hai : i < as.toList.length := by omega
        cases hr : C'.isRec i
        · obtain ⟨x, hx, hxn, -⟩ := (simpleArgs_get as 0 hsa i hai).2 (by simpa using hr)
          have T := (bndRelArgs_get as 0 [] hRA i hai).1 x hx (by simpa using hr) hxn
          simp only [Nat.zero_add, List.append_nil] at T
          rw [List.map_take] at T
          obtain ⟨A0, hA0⟩ := ctor_point hi' hr
          have ec := argTy_point_congr hW hD hC' hA0 (args := ZP) (args' := Z)
            (by simp [ZP]; omega) (by simp [Z]; omega) (P.isub ρ).toList.reverse (by simp [hplen]) (by
              intro j hj hj' hjr
              obtain ⟨x', hx', hxn', -⟩ := (simpleArgs_get as 0 hsa j (by simpa [ZP] using hj)).2 (by simpa using hjr)
              simp only [ZP, Z, List.getElem_map, hx']
              rw [bndAt_var rs (by omega), bndAt_var rs (by omega)])
          have eA : C'.argTy d D.params.length i = A0 := by simp [Ctor.argTy, hA0]
          rw [eA] at T ⊢
          rw [ec]
          have R := RE2.conv hW T (ha (C.args.length - 1 - x) (by omega))
          have ez : Z.getD i .abort = X.getD (C.args.length - 1 - x) .abort := by
            rw [getD_eq_get' (by simp [Z]; omega)]
            simp only [Z, List.getElem_map]
            rw [hx, bndAt_var rs (by omega), hX]
          rw [ez]
          exact R
        · rw [argTy_rec_inst hr hPl hplen (by simp [Z]; omega)]
          exact hrecBase i hai hr
      have hrecPair : ∀ i (hai : i < as.toList.length), C'.isRec i = true →
          RE2 S k (.data d (P.isub ρ)) (Z.getD i .abort) (ZP.getD i .abort) := by
        intro i hai hr
        have hs0 := (simpleArgs_get as 0 hsa i hai).1 (by simpa using hr)
        have hR0 := (bndRelArgs_get as 0 [] hRA i hai).2 (by simpa using hr)
        have htL := (RE2.typed (hrecBase i hai hr)).1
        have htR : HasTy S k .one [] (ZP.getD i .abort) (.data d (P.isub ρ)) := by
          obtain ⟨htele, -⟩ := con_inv hW hD hC' htP hPρ
          have ht0 := HasTele0.get htele (k := i) (a := ZP.getD i .abort)
            (by rw [toList_ofList, getD_eq_get' (show i < ZP.length by simp [ZP]; omega), List.getElem?_eq_getElem (by simp [ZP]; omega)])
            (argTys_get (by omega))
          rw [argTy_rec_inst hr hPl hplen (by simp [toList_ofList, ZP]; omega)] at ht0
          exact minimal_to_spec ht0
        have ez : Z.getD i .abort = Ctor.bndAt as.toList[i] q.toList X rs := by
          rw [getD_eq_get' (by simp [Z]; omega)]; simp only [Z, List.getElem_map]
        have ezP : ZP.getD i .abort = Ctor.bndAt as.toList[i] (P.isub ρ).toList X rs := by
          rw [getD_eq_get' (by simp [ZP]; omega)]; simp only [ZP, List.getElem_map]
        rw [ez] at htL ⊢
        rw [ezP] at htR ⊢
        exact bnd_rel hW hD hP hPP ihCR hC N _ (by
          have := sizeOf_con_arg (d' := d) (c' := c') (ps0 := Ctor.paramVars D.params.length C.args.length)
            (rs0 := ss) (List.getElem_mem hai)
          omega) hs0 ρ hql hplen hX hX (forall2_ieq_refl _) ha hR0 htL htR
      have hargsZP : ∀ i (_hi : i < C'.args.length), RE2 S k ((C'.argTy d D.params.length i).substList
          ((Z.take i).reverse ++ (P.isub ρ).toList.reverse)) (Z.getD i .abort) (ZP.getD i .abort) := by
        intro i hi'
        cases hr : C'.isRec i
        · have R := hargsZ i hi'
          have hai : i < as.toList.length := by omega
          obtain ⟨x, hx, hxn, -⟩ := (simpleArgs_get as 0 hsa i hai).2 (by simpa using hr)
          have ez : ZP.getD i .abort = Z.getD i .abort := by
            rw [getD_eq_get' (by simp [ZP]; omega), getD_eq_get' (by simp [Z]; omega)]
            simp only [ZP, Z, List.getElem_map, hx]
            rw [bndAt_var rs (by omega), bndAt_var rs (by omega)]
          rwa [ez]
        · rw [argTy_rec_inst hr hPl hplen (by simp [Z]; omega)]
          exact hrecPair i (by omega) hr
      have hrecE : ∀ i (hai : i < as.toList.length), C'.isRec i = true →
          RE2 S k ((M.isub ρ).inst (Z.getD i .abort))
            (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) (Z.getD i .abort))
            (bndInterp2 d D C (P.isub ρ) (M.isub ρ) (bs.isub ρ) X rs (as.toList.getD i .abort)) := by
        intro i hai hr
        have hs0 := (simpleArgs_get as 0 hsa i hai).1 (by simpa using hr)
        have hR0 := (bndRelArgs_get as 0 [] hRA i hai).2 (by simpa using hr)
        obtain ⟨-, hacl, -⟩ := closedB_con hcl
        have hc0 := closed_toList hacl _ (List.getElem_mem hai)
        have hty := (RE2.typed (hrecBase i hai hr)).1
        rw [getD_eq_get' hai]
        have ez : Z.getD i .abort = Ctor.bndAt as.toList[i] q.toList X rs := by
          rw [getD_eq_get' (by simp [Z]; omega)]; simp only [Z, List.getElem_map]
        rw [ez] at hty ⊢
        exact ih _ (by
          have := sizeOf_con_arg (d' := d) (c' := c') (ps0 := Ctor.paramVars D.params.length C.args.length)
            (rs0 := ss) (List.getElem_mem hai)
          omega) hs0 hc0 hR0 hty (by
            have h := (RE2.typed (hrecPair i hai hr)).2.1
            simpa only [ZP, getD_eq_get' (show i < ZP.length by simp [ZP]; omega), List.getElem_map] using h)
      have r1 := ihEC c' hcc ρ hC' ht hargsZ (fun i hi' => by
        obtain ⟨hin, hir⟩ := mem_recPos hi'
        have R := hrecE i (by omega) hir
        have T := H.mot k ρ _ _ (hrecBase i (by omega) hir)
        exact RE2.trans hW T R (RE2.symm hW T R))
      obtain ⟨-, -, -, hrsl, hrsc, -, -, -, -⟩ := con_inv hW hD hC' ht hPρ
      let Y := C'.recPos.map (fun j => bndInterp2 d D C (P.isub ρ) (M.isub ρ) (bs.isub ρ) X rs (as.toList.getD j .abort))
      have r2 := branchApp_rel2 hW hD hC' hplen (H.br k ρ c' C' hC') Z ZP
        (ihsOf d C' (P.isub ρ) (M.isub ρ) (bs.isub ρ) Z) Y hZ (by simp [ZP, hal]) (by simp [ihsOf]) (by simp [Y])
        (fun i hi hi' => by
          have R := hargsZP i (by omega)
          simpa only [getD_eq_get' hi, getD_eq_get' hi'] using R)
        (fun s hs => by
          have hg : C'.recPos.getD s 0 = C'.recPos[s] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; rfl
          simp only [ihsOf, Y, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hs,
            Option.map_some, Option.getD_some, hg]
          obtain ⟨hin, hir⟩ := mem_recPos (List.getElem_mem hs)
          exact hrecE _ (by omega) hir)
        hrsl (ieqL_iff.2 (forall2_ieq_refl _)) hrsc hrsc
      have hBA : bndInterpArgs2 d D C (P.isub ρ) (M.isub ρ) (bs.isub ρ) X rs C' 0 as =
          C'.recPos.map (fun j => bndInterp2 d D C (P.isub ρ) (M.isub ρ) (bs.isub ρ) X rs (as.toList.getD j .abort)) := by
        conv => lhs; rw [has]
        rw [bndInterpArgs2_eqN, hal, ← recPos_eq_filter]
      have hc : c' < (bs.isub ρ).toList.length := by
        rw [(H.tyL k ρ).choose_spec.hlen]
        exact (List.getElem?_eq_some_iff.1 hC').1
      have hb : (bs.isub ρ).toList[c']? = some ((bs.isub ρ).toList.getD c' .abort) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; rfl
      rw [bndInterp2_con hC' hb, hBA]
      have htCanon := (con_inv hW hD hC' ht hPρ).2.2.2.2.2.2.1
      have rc := ihCR c' hcc ρ hC' htCanon ht (forall2_ieq_refl _) hargsZ
      exact RE2.trans hW (H.mot k ρ _ _ (ihCR c' hcc ρ hC' ht ht (forall2_ieq_refl _) hargsZ)) r1
        (RE2.conv hW (H.mot k ρ _ _ rc) r2)
    all_goals simp [Ctor.simpleB] at hs

end

end Model.Whnf
