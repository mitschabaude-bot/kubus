import Model.Whnf.Boundary2Sub

/-! # Computability of the boundary evaluator -/

set_option autoImplicit false
namespace Model.Whnf.Boundary2
open KubusCore KubusCore.Meta Model.Canon Model.Whnf
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Sig} {k d N c : ℕ} {D : DataDecl} {P ps : Tm} {C : Ctor} {γ : ℕ → Tm}

section
variable (hW : WfSig S) (hD : S[d]? = some (.data D))
  (hP : HasTy S k .one [] (.data d P) (.univ D.level)) (hPP : RT2 S k (.data d P) (.data d P))
  (ih : ∀ c < N, CRSt S d D k P c)
include hW hD hP hPP ih

/-- The argument relations recorded by a computable tree. -/
theorem Comp.args {c : ℕ} {C : Ctor} {as : List Tm} {rs : List I}
    (hC : D.ctors[c]? = some C) (h : Comp S k d D P N γ I.var (.con d c ps (Tm.ofList as) rs)) :
    ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C (as.map (close d P γ I.var)) i)
      ((as.map (close d P γ I.var)).getD i .abort) ((as.map (close d P γ I.var)).getD i .abort) := by
  cases h with
  | con hc hC0 has hal ht hr hp =>
    rw [hC] at hC0; cases hC0
    simp only [toList_ofList] at hal hr hp
    intro i hi
    have hai : i < as.length := by omega
    rw [getD_eq_get' (by simp; omega), List.getElem_map]
    cases hri : C.isRec i
    · obtain ⟨j, hj, hR⟩ := hp i hai hri
      simpa only [closeArgs_ofList, hj, close, KubusCore.Boundary.eval] using hR
    · simp only [argAt]
      rw [argTy_rec_inst hri (p_lit hW hD hP hPP) (p_len hW hD hP) (by simp; omega)]
      exact (hr i hai hri).diag hW hD hP hPP ih

/-- Evaluate a simple boundary in any constructor algebra preserving computability. -/
theorem eval_rel (_hC : D.ctors[c]? = some C) (hcN : c ≤ N)
    (A : List Tm) (hA : A.length = C.args.length)
    (hAN : ∀ a ∈ A, NF D.ctors d ps k a) (rs : List I) (hrs : rs.length = C.dims)
    (har : ∀ i (hi : i < A.length), C.isRec i = true → Comp S k d D P N γ I.var A[i])
    (hap : ∀ i (hi : i < A.length), C.isRec i = false → ∃ j, A[i] = .var j)
    (hargs : ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C (A.map (close d P γ I.var)) i)
      ((A.map (close d P γ I.var)).getD i .abort) ((A.map (close d P γ I.var)).getD i .abort))
    (H : ℕ → List Tm → List I → Tm)
    (hH : ∀ c' < c, ∀ C', D.ctors[c']? = some C' → ∀ xs ss, (∀ x ∈ xs, NF D.ctors d ps k x) →
      Comp S k d D P N γ I.var (.con d c' ps (Tm.ofList xs) ss) →
      Comp S k d D P N γ I.var (H c' xs ss) ∧ NF D.ctors d ps k (H c' xs ss) ∧
      RE2 S k (.data d P) (close d P γ I.var (.con d c' ps (Tm.ofList xs) ss)) (close d P γ I.var (H c' xs ss))) :
    ∀ (M : ℕ) (a : Tm), sizeOf a < M →
      Ctor.simpleB D.ctors d D.params.length c C.args.length C a = true →
      a.closedB (D.params.length + C.args.length) C.dims = true →
      bndRel S k d D.params.length C.args.length C D.ctors P P
        (A.map (close d P γ I.var)) (A.map (close d P γ I.var)) rs a →
      HasTy S k .one [] (Ctor.bndAt a P.toList (A.map (close d P γ I.var)) rs) (.data d P) →
      Comp S k d D P N γ I.var
        (KubusCore.Boundary.eval H (fun j => A.reverse.getD j .abort) (fun i => rs.reverse.getD i .zero) a) ∧
      NF D.ctors d ps k (KubusCore.Boundary.eval H (fun j => A.reverse.getD j .abort) (fun i => rs.reverse.getD i .zero) a) ∧
      RE2 S k (.data d P) (Ctor.bndAt a P.toList (A.map (close d P γ I.var)) rs)
        (close d P γ I.var
          (KubusCore.Boundary.eval H (fun j => A.reverse.getD j .abort) (fun i => rs.reverse.getD i .zero) a)) := by
  let Y := A.map (close d P γ I.var)
  let E := KubusCore.Boundary.eval H (fun j => A.reverse.getD j .abort) (fun i => rs.reverse.getD i .zero)
  have hY : Y.length = C.args.length := by simp [Y, hA]
  have hPl := p_lit hW hD hP hPP
  have hplen := p_len hW hD hP
  have evvar : ∀ j (_hj : j < C.args.length), E (.var j) = A[C.args.length - 1 - j]'(by omega) := by
    intro j hj
    simp only [E, KubusCore.Boundary.eval, getD_eq_get' (show j < A.reverse.length by simp; omega), List.getElem_reverse, hA]
  intro M
  induction M with
  | zero => intro a h; omega
  | succ M ihM =>
    intro a hsz hs hcl hrel ht
    cases a with
    | var x =>
      simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
      change Comp S k d D P N γ I.var (E (.var x)) ∧ NF D.ctors d ps k (E (.var x)) ∧ RE2 S k (.data d P) _ (close d P γ I.var (E (.var x)))
      rw [evvar x hs.1, bndAt_var rs (by simp; omega)]
      have hcomp := har (C.args.length - 1 - x) (by omega) hs.2
      refine ⟨hcomp, hAN _ (List.getElem_mem (by omega)), ?_⟩
      simp only [List.length_map, hA]
      rw [getD_eq_get' (by simp; omega), List.getElem_map]
      exact hcomp.diag hW hD hP hPP ih
    | con d' c' ps0 as0 rs0 =>
      obtain ⟨hdd, hcc, hps0, C', hC', hal, hrl, hsa, has⟩ := simpleB_con_inv hs
      subst d' hps0
      let X := as0.toList.map (Ctor.bndAt · P.toList Y rs)
      let Z := as0.toList.map E
      let ss := rs0.map (·.subst (rsSub rs))
      have hX : X.length = C'.args.length := by simp [X, hal]
      have hZ : Z.length = C'.args.length := by simp [Z, hal]
      have eB : Ctor.bndAt (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) P.toList Y rs =
          .con d c' P (Tm.ofList X) ss := by
        rw [bndAt_con, bndAt_paramVars rs hplen hY, ← hPl, has, bndAt_ofList]
      have htX : HasTy S k .one [] (.con d c' P (Tm.ofList X) ss) (.data d P) := by change HasTy S k .one [] (Ctor.bndAt _ P.toList Y rs) _ at ht; rwa [eB] at ht
      have hrec : ∀ i (hi : i < as0.toList.length), C'.isRec i = true →
          Comp S k d D P N γ I.var (E as0.toList[i]) ∧ NF D.ctors d ps k (E as0.toList[i]) ∧
          RE2 S k (.data d P) (Ctor.bndAt as0.toList[i] P.toList Y rs) (close d P γ I.var (E as0.toList[i])) := by
        intro i hi hr
        have hs0 := (simpleArgs_get as0 0 hsa i hi).1 (by simpa using hr)
        have hb0 := (bndRelArgs_get as0 0 [] (by simpa only [bndRel, hC'] using hrel) i hi).2 (by simpa using hr)
        have hc0 : as0.toList[i].closedB (D.params.length + C.args.length) C.dims = true := by
          simp only [Tm.closedB, Bool.and_eq_true] at hcl
          exact closed_toList hcl.1.2 _ (List.getElem_mem hi)
        have ht0 : HasTy S k .one [] (Ctor.bndAt as0.toList[i] P.toList Y rs) (.data d P) := by
          obtain ⟨htele, -⟩ := con_inv hW hD hC' htX hP
          have g := HasTele0.get htele (k := i) (a := Ctor.bndAt as0.toList[i] P.toList Y rs)
            (by rw [toList_ofList, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl) (argTys_get (by omega))
          rw [argTy_rec_inst hr hPl hplen (by simp [toList_ofList]; omega)] at g
          exact minimal_to_spec g
        have hsize := sizeOf_con_arg (d' := d) (c' := c') (ps0 := Ctor.paramVars D.params.length C.args.length) (rs0 := rs0) (List.getElem_mem hi)
        exact ihM _ (by omega) hs0 hc0 hb0 ht0
      have hpt : ∀ i (hi : i < as0.toList.length), C'.isRec i = false → ∃ j,
          E as0.toList[i] = .var j ∧
          Ctor.bndAt as0.toList[i] P.toList Y rs = γ j ∧ RE2 S k (argAt d D P C' X i) (γ j) (γ j) := by
        intro i hi hr
        obtain ⟨x, hx, hxn, hcr⟩ := (simpleArgs_get as0 0 hsa i hi).2 (by simpa using hr)
        obtain ⟨j, hj⟩ := hap (C.args.length - 1 - x) (by omega) hcr
        have T := (bndRelArgs_get as0 0 [] (by simpa only [bndRel, hC'] using hrel) i hi).1 x hx (by simpa using hr) hxn
        simp only [Nat.zero_add, List.append_nil] at T
        have R := RE2.conv hW T (hargs (C.args.length - 1 - x) (by omega))
        have he : Y.getD (C.args.length - 1 - x) .abort = γ j := by
          change (A.map (close d P γ I.var)).getD (C.args.length - 1 - x) .abort = γ j
          rw [getD_eq_get' (by simp; omega), List.getElem_map, hj]
          rfl
        refine ⟨j, by rw [hx, evvar x hxn, hj], ?_, ?_⟩
        · rw [hx, bndAt_var rs (show x < Y.length by omega), hY, he]
        · change RE2 S k (argAt d D P C' X i) (γ j) (γ j)
          simpa only [argAt, X, List.map_take, ← he] using R
      have haXZ : ∀ i (_hi : i < C'.args.length), RE2 S k (argAt d D P C' X i) (X.getD i .abort) ((Z.map (close d P γ I.var)).getD i .abort) := by
        intro i hi
        have hai : i < as0.toList.length := by omega
        simp only [X, Z, getD_eq_get' (show i < (as0.toList.map (Ctor.bndAt · P.toList Y rs)).length by simpa using hai),
          getD_eq_get' (show i < ((as0.toList.map E).map (close d P γ I.var)).length by simpa using hai), List.getElem_map]
        cases hr : C'.isRec i
        · obtain ⟨j, hj, he, R⟩ := hpt i hai hr
          simpa only [he, hj, close, KubusCore.Boundary.eval] using R
        · simp only [argAt]
          rw [argTy_rec_inst hr hPl hplen (by simp; omega)]
          exact (hrec i hai hr).2.2
      have htZ := con_typed hW hD hP hPP hC' htX (by simp [Z, hal]) haXZ
      have hcompZ : Comp S k d D P N γ I.var (.con d c' ps (Tm.ofList Z) ss) := by
        refine Comp.con (by omega) hC' (by simp [toList_ofList]) (by simp [toList_ofList, hZ]) ?_ ?_ ?_
        · simpa only [close_id_con, closeArgs_ofList] using htZ
        · intro i hi hr
          simpa only [toList_ofList, Z, List.getElem_map] using (hrec i (by simpa [toList_ofList, Z] using hi) hr).1
        · intro i hi hr
          have hai : i < as0.toList.length := by simpa [toList_ofList, Z] using hi
          obtain ⟨j, hj, he, R⟩ := hpt i hai hr
          refine ⟨j, by simpa only [toList_ofList, Z, List.getElem_map] using hj, ?_⟩
          have RR' := RE2.conv hW (args_type hW hD hP hPP hC' hX (by simp [Z, hal]) haXZ i (by omega)) R
          simpa only [closeArgs_ofList] using RR'
      have Rcon := lower_con hW hP ih (by omega) hC' htX htZ (forall2_ieq_refl _) haXZ
      have hnZ : ∀ z ∈ Z, NF D.ctors d ps k z := by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
        cases hr : C'.isRec i
        · obtain ⟨j, hj, _, _⟩ := hpt i hi hr
          rw [hj]; exact .var j
        · exact (hrec i hi hr).2.1
      obtain ⟨hcompH, hnH, RH⟩ := hH c' hcc C' hC' Z ss hnZ hcompZ
      have eE : E (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) = H c' Z ss := by
        have haE : KubusCore.Boundary.evalArgs H (fun j => A.reverse.getD j .abort)
            (fun i => rs.reverse.getD i .zero) as0 = Z := by
          conv_lhs => rw [has]
          exact eval_ofList H _ _ _
        change H c' _ _ = H c' Z ss
        rw [haE]
        congr 1
        apply List.map_congr_left
        intro r hr
        exact interval_zero_default rs (by
          simp only [Tm.closedB, Bool.and_eq_true, List.all_eq_true] at hcl
          rw [hrs]; exact (I.scopedB_iff _ _).1 (hcl.2 r hr))
      change Comp S k d D P N γ I.var (E (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0)) ∧
        NF D.ctors d ps k (E (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0)) ∧ RE2 S k (.data d P) (Ctor.bndAt (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0) P.toList Y rs)
          (close d P γ I.var (E (.con d c' (Ctor.paramVars D.params.length C.args.length) as0 rs0)))
      rw [eE]
      refine ⟨hcompH, hnH, ?_⟩
      rw [eB]
      exact RE2.trans hW hPP Rcon (by simpa only [close_id_con, closeArgs_ofList] using RH)
    | _ => simp [Ctor.simpleB] at hs

end
end
end Model.Whnf.Boundary2
