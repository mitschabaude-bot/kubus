import Model.Whnf.Boundary2Normalize

/-! # Overlapping boundaries are related using earlier constructors -/
set_option autoImplicit false
namespace Model.Whnf.Boundary2
open KubusCore KubusCore.Meta Model.Canon Model.Whnf
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Sig} {k d c : ℕ} {D : DataDecl} {P : Tm} {C : Ctor}

section
variable (hW : WfSig S) (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hBT : BndTyping S d)
  (hP : HasTy S k .one [] (.data d P) (.univ D.level)) (hPP : RT2 S k (.data d P) (.data d P))
  (ih : ∀ c' < c, CRSt S d D k P c') (hCB : ∀ c' < c, CBRSt S d D c')
include hW hD hH hBT hP hPP ih hCB

/-- Each holding boundary is related to its normal form, without using boundary expansion for the current constructor. -/
theorem bnd_norm_rel (hC : D.ctors[c]? = some C) {Y : List Tm} {rs : List I} {kb : ℕ} {ψ : I} {b : Tm}
    (hb : C.bnd[kb]? = some (ψ, b)) (hent : I.Entails .one (Ctor.cofAt ψ rs))
    (hY : Y.length = C.args.length)
    (ht : HasTy S k .one [] (.con d c P (Tm.ofList Y) rs) (.data d P))
    (hargs : ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C Y i) (Y.getD i .abort) (Y.getD i .abort)) :
    let ps := Ctor.paramVars D.params.length C.args.length
    let t := norm D.ctors d ps c rs b
    Comp S k d D P c (argsEnv Y) I.var t ∧ NF D.ctors d ps k t ∧
      RE2 S k (.data d P) (Ctor.bndAt b P.toList Y rs) (close d P (argsEnv Y) I.var t) := by
  let ps := Ctor.paramVars D.params.length C.args.length
  let A := vars C.args.length
  let H := fun c' xs ss => if c' < c then KubusCore.Boundary.conNF D.ctors d ps c' xs ss else .abort
  have hAl : A.length = C.args.length := vars_len _
  have heY : A.map (close d P (argsEnv Y) I.var) = Y := close_vars Y hY
  have hN : ∀ a ∈ A, NF D.ctors d ps k a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    exact .var _
  have hrec : ∀ i (hi : i < A.length), C.isRec i = true → Comp S k d D P c (argsEnv Y) I.var A[i] := by
    intro i hi hr
    simp only [A, vars, List.getElem_map, List.getElem_range]
    apply Comp.var
    have R := hargs i (by omega)
    simp only [argAt] at R
    rw [argTy_rec_inst hr (p_lit hW hD hP hPP) (p_len hW hD hP) (by simp; omega)] at R
    have he : argsEnv Y (C.args.length - 1 - i) = Y.getD i .abort := by
      simp only [argsEnv]
      rw [getD_eq_get' (by simp; omega), List.getElem_reverse, getD_eq_get' (by omega)]
      congr 1; omega
    rwa [he]
  have hpoint : ∀ i (hi : i < A.length), C.isRec i = false → ∃ j, A[i] = .var j := by
    intro i hi _
    exact ⟨C.args.length - 1 - i, by simp [A, vars]⟩
  have CI := con_inv hW hD hC ht hP
  have hrs : rs.length = C.dims := CI.2.2.2.1
  obtain ⟨hψ, hbc, hs, _⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
  have hrel := hBT hD hH hC hb hent hP hPP hY ht hargs
  have hbt : HasTy S k .one [] (Ctor.bndAt b P.toList Y rs) (.data d P) := by
    have eqb := EqTm.conBnd hD hC hb hent (p_lit hW hD hP hPP) (by simp [toList_ofList]) ht
    exact HasTy.eqR (by simpa only [toList_ofList] using eqb)
  have hOracle : ∀ c' < c, ∀ C', D.ctors[c']? = some C' → ∀ xs ss, (∀ x ∈ xs, NF D.ctors d ps k x) →
      Comp S k d D P c (argsEnv Y) I.var (.con d c' ps (Tm.ofList xs) ss) →
      Comp S k d D P c (argsEnv Y) I.var (H c' xs ss) ∧ NF D.ctors d ps k (H c' xs ss) ∧
      RE2 S k (.data d P) (close d P (argsEnv Y) I.var (.con d c' ps (Tm.ofList xs) ss))
        (close d P (argsEnv Y) I.var (H c' xs ss)) := by
    intro c' hc' C' hC' xs ss hn hc
    simpa only [H, hc', ↓reduceIte] using conNF_rel hW hD hH hBT hP hPP ih hCB c' hc' C' hC' xs ss hn hc
  have ev := eval_rel hW hD hP hPP ih hC (by omega) A hAl hN rs hrs hrec hpoint
    (by simpa only [heY] using hargs) H hOracle (sizeOf b + 1) b (by omega) hs hbc
    (by simpa only [heY] using hrel) (by simpa only [heY] using hbt)
  have he : KubusCore.Boundary.eval H (fun j => A.reverse.getD j .abort) (fun i => rs.reverse.getD i .zero) b =
      norm D.ctors d ps c rs b := by
    exact eval_simple_congr H _ _ _ (fun j hj => vars_rev_get hj) (sizeOf b + 1) b (by omega) hs
  simpa only [heY, he] using ev

/-- The per-face syntactic check relates two holding boundaries using only earlier constructor relations. -/
theorem overlap_rel (hC : D.ctors[c]? = some C) {Y : List Tm} {rs : List I} {kb kb' : ℕ} {ψ ψ' : I} {b b' : Tm}
    (hb : C.bnd[kb]? = some (ψ, b)) (hb' : C.bnd[kb']? = some (ψ', b'))
    (hent : I.Entails .one (Ctor.cofAt ψ rs)) (hent' : I.Entails .one (Ctor.cofAt ψ' rs))
    (hY : Y.length = C.args.length)
    (ht : HasTy S k .one [] (.con d c P (Tm.ofList Y) rs) (.data d P))
    (hargs : ∀ i (_hi : i < C.args.length), RE2 S k (argAt d D P C Y i) (Y.getD i .abort) (Y.getD i .abort)) :
    RE2 S k (.data d P) (Ctor.bndAt b P.toList Y rs) (Ctor.bndAt b' P.toList Y rs) := by
  obtain ⟨htn, hn, R⟩ := bnd_norm_rel hW hD hH hBT hP hPP ih hCB hC hb hent hY ht hargs
  obtain ⟨htn', hn', R'⟩ := bnd_norm_rel hW hD hH hBT hP hPP ih hCB hC hb' hent' hY ht hargs
  have hrs := (con_inv hW hD hC ht hP).2.2.2.1
  have hh : (ival (renv (rs.map (ival (idEnv k)))) (.and ψ ψ')).holds := by
    have hhold : ∀ (ψ0 : I) (b0 : Tm) (kb0 : ℕ), C.bnd[kb0]? = some (ψ0, b0) →
        I.Entails .one (Ctor.cofAt ψ0 rs) → (ival (renv (rs.map (ival (idEnv k)))) ψ0).holds := by
      intro ψ0 b0 kb0 hb0 he0
      have hψ := (((hW.2 d D hD).2.2 c C hC).2.1 kb0 ψ0 b0 hb0).1
      have hh0 := entails_holds (ρ := idEnv k) he0 (show (ival (idEnv k) .one).holds from rfl)
      change (ival (idEnv k) (ψ0.subst (rsSub rs))).holds at hh0
      rw [← interval_zero_default rs (by rwa [hrs]), ival.subst, Model.Boundary.dims_env] at hh0
      exact hh0
    exact Model.holds_and.mpr ⟨hhold ψ b kb hb hent, hhold ψ' b' kb' hb' hent'⟩
  have hnnear := overlap_norm_near hW hD hC (List.mem_of_getElem? hb) (List.mem_of_getElem? hb') rs hh hn hn'
  have RR := htn.near hW hD hP hPP ih hnnear htn'.typed
  exact RE2.trans hW hPP R (RE2.trans hW hPP RR (RE2.symm hW hPP R'))

end
end
end Model.Whnf.Boundary2
