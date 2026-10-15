import Model.Whnf.Boundary2Hyp

/-! # Earlier boundary expansions validate syntactic normalization -/
set_option autoImplicit false
namespace Model.Whnf.Boundary2
open KubusCore KubusCore.Meta Model.Canon Model.Whnf
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Sig} {k d N : ℕ} {D : DataDecl} {P ps : Tm} {γ : ℕ → Tm}

section
variable (hW : WfSig S) (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hBT : BndTyping S d)
  (hP : HasTy S k .one [] (.data d P) (.univ D.level)) (hPP : RT2 S k (.data d P) (.data d P))
  (ih : ∀ c < N, CRSt S d D k P c) (hCB : ∀ c < N, CBRSt S d D c)
include hW hD hH hBT hP hPP ih hCB

/-- Normalize a constructor with normal, computable arguments. The only boundary relations used have constructor index below `N`. -/
theorem conNF_rel : ∀ c, c < N → ∀ C, D.ctors[c]? = some C → ∀ (A : List Tm) (rs : List I),
    (∀ a ∈ A, NF D.ctors d ps k a) →
    Comp S k d D P N γ I.var (.con d c ps (Tm.ofList A) rs) →
    Comp S k d D P N γ I.var (KubusCore.Boundary.conNF D.ctors d ps c A rs) ∧
    NF D.ctors d ps k (KubusCore.Boundary.conNF D.ctors d ps c A rs) ∧
    RE2 S k (.data d P) (close d P γ I.var (.con d c ps (Tm.ofList A) rs))
      (close d P γ I.var (KubusCore.Boundary.conNF D.ctors d ps c A rs)) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihC =>
    intro hcN C hC A rs hn hcomp
    have hargs := hcomp.args hW hD hP hPP ih hC
    have hdiag := hcomp.diag hW hD hP hPP ih
    have ht := hcomp.typed
    rw [close_id_con, closeArgs_ofList] at ht
    have CI := con_inv hW hD hC ht hP
    have hAl : A.length = C.args.length := by simpa using CI.2.2.2.2.2.1
    have hrsl : rs.length = C.dims := CI.2.2.2.1
    have hsc : ∀ r ∈ rs, r.Scoped k := CI.2.2.2.2.1
    have hcget : D.ctors.getD c default = C := by simp [List.getD_eq_getElem?_getD, hC]
    cases hf : C.bnd.find? (fun p => I.entails .one (p.1.subst fun i => rs.reverse.getD i .zero)) with
    | none =>
      have he : KubusCore.Boundary.conNF D.ctors d ps c A rs = .con d c ps (Tm.ofList A) rs := by
        rw [KubusCore.Boundary.conNF, hcget, hf]
      rw [he]
      exact ⟨hcomp, .con c A rs hn hsc (by simpa only [hcget] using hf), hdiag⟩
    | some p =>
      obtain ⟨ψ, b⟩ := p
      obtain ⟨kb, hb⟩ := List.getElem?_of_mem (List.mem_of_find?_eq_some hf)
      obtain ⟨hψ, hbc, hs, _⟩ := ((hW.2 d D hD).2.2 c C hC).2.1 kb ψ b hb
      have hent : I.Entails .one (Ctor.cofAt ψ rs) := by
        have he := List.find?_some hf
        change I.entails .one (ψ.subst fun i => rs.reverse.getD i .zero) = true at he
        rw [interval_zero_default rs (by rwa [hrsl])] at he
        exact he
      let Y := A.map (close d P γ I.var)
      have hY : Y.length = C.args.length := by simp [Y, hAl]
      have hPl := p_lit hW hD hP hPP
      have eqb : EqTm S k .one [] (.con d c P (Tm.ofList Y) rs) (Ctor.bndAt b P.toList Y rs) (.data d P) := by
        have he := EqTm.conBnd hD hC hb hent hPl (by simp [toList_ofList]) ht
        simpa only [toList_ofList] using he
      have hrel := hBT hD hH hC hb hent hP hPP hY ht hargs
      have har : ∀ i (hi : i < A.length), C.isRec i = true → Comp S k d D P N γ I.var A[i] := by
        cases hcomp with
        | con _ hC0 _ _ _ hr _ =>
          rw [hC] at hC0; cases hC0
          simpa only [toList_ofList] using hr
      have hap : ∀ i (hi : i < A.length), C.isRec i = false → ∃ j, A[i] = .var j := by
        cases hcomp with
        | con _ hC0 _ _ _ _ hp =>
          rw [hC] at hC0; cases hC0
          intro i hi hr
          obtain ⟨j, hj, _⟩ := hp i (by simpa only [toList_ofList] using hi) hr
          exact ⟨j, by simpa only [toList_ofList] using hj⟩
      let H := fun c' xs ss => if c' < c then KubusCore.Boundary.conNF D.ctors d ps c' xs ss else .abort
      have hH : ∀ c' < c, ∀ C', D.ctors[c']? = some C' → ∀ xs ss, (∀ x ∈ xs, NF D.ctors d ps k x) →
          Comp S k d D P N γ I.var (.con d c' ps (Tm.ofList xs) ss) →
          Comp S k d D P N γ I.var (H c' xs ss) ∧ NF D.ctors d ps k (H c' xs ss) ∧
          RE2 S k (.data d P) (close d P γ I.var (.con d c' ps (Tm.ofList xs) ss)) (close d P γ I.var (H c' xs ss)) := by
        intro c' hc' C' hC' xs ss hn' hcomp'
        simpa only [H, hc', ↓reduceIte] using ihC c' hc' (by omega) C' hC' xs ss hn' hcomp'
      obtain ⟨hbcomp, hbn, Rb⟩ := eval_rel hW hD hP hPP ih hC (by omega) A hAl hn rs hrsl har hap hargs H hH
        (sizeOf b + 1) b (by omega) hs hbc hrel (HasTy.eqR eqb)
      have he : KubusCore.Boundary.conNF D.ctors d ps c A rs =
          KubusCore.Boundary.eval H (fun j => A.reverse.getD j .abort) (fun i => rs.reverse.getD i .zero) b := by
        rw [KubusCore.Boundary.conNF, hcget, hf]
        rfl
      rw [he]
      refine ⟨hbcomp, hbn, ?_⟩
      have R0 := hCB c hcN hC hb hent hP hPP hY ht hargs
      rw [close_id_con, closeArgs_ofList]
      exact RE2.trans hW hPP R0 Rb

end
end
end Model.Whnf.Boundary2
