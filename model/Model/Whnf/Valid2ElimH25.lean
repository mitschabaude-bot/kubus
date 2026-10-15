import Model.Whnf.Valid2ElimH24

/-! # Normalization of simple constructor boundary trees -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k K : ℕ}

/-- Normalization of a constructor, given normalization of its recursive arguments. -/
def ECNorm2 (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P M bs : Tm) (c : ℕ) : Prop :=
  ∀ {k : ℕ} (ρ : ISub k K) {C : Ctor} {q : Tm} {X : List Tm} {rs : List I}, D.ctors[c]? = some C →
    HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (P.isub ρ)) →
    (∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X.getD i .abort)) →
    (∀ i, i ∈ C.recPos → ElimNormH S d D K P M bs k ρ (X.getD i .abort)) →
    ElimNormH S d D K P M bs k ρ (.con d c q (Tm.ofList X) rs)

variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
    {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hP hPP

/-- Normalization of recursive leaves and earlier constructors gives normalization of a boundary tree. -/
theorem bndNormH {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
    (ihCR : ∀ c' < c, CRSt S d D K P c') (ihNC : ∀ c' < c, ECNorm2 S d D K P M bs c')
    (ρ : ISub k K) (q : Tm) (hql : q.toList.length = D.params.length) (X : List Tm) (rs : List I)
    (hX : X.length = C.args.length)
    (ha : ∀ i (_hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
      ((X.take i).reverse ++ (P.isub ρ).toList.reverse)) (X.getD i .abort) (X.getD i .abort))
    (Nh : ∀ i, i ∈ C.recPos → ElimNormH S d D K P M bs k ρ (X.getD i .abort)) :
    ∀ (N : ℕ) (e : Tm), sizeOf e < N → Ctor.simpleB D.ctors d D.params.length c C.args.length C e = true →
      e.closedB (D.params.length + C.args.length) C.dims = true →
      bndRel S k d D.params.length C.args.length C D.ctors (P.isub ρ) (P.isub ρ) X X rs e →
      HasTy S k .one [] (Ctor.bndAt e q.toList X rs) (.data d (P.isub ρ)) →
      HasTy S k .one [] (Ctor.bndAt e (P.isub ρ).toList X rs) (.data d (P.isub ρ)) →
      ElimNormH S d D K P M bs k ρ (Ctor.bndAt e q.toList X rs) := by
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
      rw [bndAt_var rs (by omega), hX]
      exact Nh _ (List.mem_filter.2 ⟨List.mem_range.2 (by omega), hs.2⟩)
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
      apply ihNC c' hcc ρ hC' ht hargsZ
      intro i hi
      obtain ⟨hjn, hir⟩ := mem_recPos hi
      have hai : i < as.toList.length := by omega
      have hs0 := (simpleArgs_get as 0 hsa i hai).1 (by simpa using hir)
      have hR0 := (bndRelArgs_get as 0 [] hRA i hai).2 (by simpa using hir)
      obtain ⟨-, hacl, -⟩ := closedB_con hcl
      have hc0 := closed_toList hacl _ (List.getElem_mem hai)
      have htL := (RE2.typed (hrecBase i hai hir)).1
      have htR : HasTy S k .one [] (ZP.getD i .abort) (.data d (P.isub ρ)) := by
        obtain ⟨htele, -⟩ := con_inv hW hD hC' htP hPρ
        have ht0 := HasTele0.get htele (k := i) (a := ZP.getD i .abort)
          (by rw [toList_ofList, getD_eq_get' (show i < ZP.length by simp [ZP]; omega),
            List.getElem?_eq_getElem (by simp [ZP]; omega)]) (argTys_get (by omega))
        rw [argTy_rec_inst hir hPl hplen (by simp [toList_ofList, ZP]; omega)] at ht0
        exact minimal_to_spec ht0
      have ez : Z.getD i .abort = Ctor.bndAt as.toList[i] q.toList X rs := by
        rw [getD_eq_get' (by simp [Z]; omega)]; simp only [Z, List.getElem_map]
      have ezP : ZP.getD i .abort = Ctor.bndAt as.toList[i] (P.isub ρ).toList X rs := by
        rw [getD_eq_get' (by simp [ZP]; omega)]; simp only [ZP, List.getElem_map]
      rw [ez] at htL ⊢
      rw [ezP] at htR
      exact ih _ (by
        have := sizeOf_con_arg (d' := d) (c' := c') (ps0 := Ctor.paramVars D.params.length C.args.length)
          (rs0 := ss) (List.getElem_mem hai)
        omega) hs0 hc0 hR0 htL htR
    all_goals simp [Ctor.simpleB] at hs

end

end Model.Whnf
