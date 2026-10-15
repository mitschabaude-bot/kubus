import Model.Whnf.Boundary2NF

/-! # Substitution in simple constructor trees -/

set_option autoImplicit false
namespace Model.Whnf.Boundary2
open KubusCore KubusCore.Meta Model.Canon Model.Whnf
noncomputable section
attribute [local instance] Classical.propDecidable

variable {d np n c : ℕ} {ctors : List Ctor} {C : Ctor} {P : Tm}

theorem eval_ofList (H : ℕ → List Tm → List I → Tm) (γ : ℕ → Tm) (τ : ℕ → I) (as : List Tm) :
    KubusCore.Boundary.evalArgs H γ τ (Tm.ofList as) = as.map (KubusCore.Boundary.eval H γ τ) := by
  induction as <;> simp_all [Tm.ofList, KubusCore.Boundary.evalArgs]

theorem close_id_con (γ : ℕ → Tm) (d' c : ℕ) (ps as : Tm) (rs : List I) :
    close d P γ I.var (.con d' c ps as rs) = .con d c P (Tm.ofList (closeArgs d P γ I.var as)) rs := by
  simp [close, KubusCore.Boundary.eval, I_subst_var, closeArgs]

theorem interval_zero_default (rs : List I) {r : I} (hr : r.Scoped rs.length) :
    r.subst (fun i => rs.reverse.getD i .zero) = r.subst (rsSub rs) := by
  apply subst_scoped_eq hr
  intro i hi
  simp only [rsSub, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < rs.reverse.length by simpa using hi), Option.getD_some]

/-- Changing unused term variables does not change a simple boundary evaluation. -/
theorem eval_simple_congr (H : ℕ → List Tm → List I → Tm) (σ σ' : ℕ → Tm) (τ : ℕ → I)
    (hσ : ∀ j < n, σ j = σ' j) :
    ∀ M a, sizeOf a < M → Ctor.simpleB ctors d np c n C a = true →
      KubusCore.Boundary.eval H σ τ a = KubusCore.Boundary.eval H σ' τ a := by
  intro M
  induction M with
  | zero => intro a h; omega
  | succ M ih =>
    intro a hsz hs
    cases a with
    | var j =>
      simp only [Ctor.simpleB, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact hσ j hs.1
    | con d' c' ps0 as0 rs0 =>
      obtain ⟨hdd, hcc, hps, C', hC', hal, hrl, hsa, has⟩ := simpleB_con_inv hs
      simp only [KubusCore.Boundary.eval]
      congr 1
      conv_lhs => arg 4; rw [has]
      conv_rhs => arg 4; rw [has]
      rw [eval_ofList, eval_ofList]
      apply List.map_congr_left
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨hr, hp⟩ := simpleArgs_get as0 0 hsa i hi
      cases hri : C'.isRec i
      · obtain ⟨j, hj, hjn, _⟩ := hp (by simpa using hri)
        rw [hj]; exact hσ j hjn
      · have hsize := sizeOf_con_arg (d' := d') (c' := c') (ps0 := ps0) (rs0 := rs0) (List.getElem_mem hi)
        exact ih _ (by omega) (hr (by simpa using hri))
    | _ => simp [Ctor.simpleB] at hs

def vars (n : ℕ) : List Tm := (List.range n).map (fun i => .var (n - 1 - i))

theorem vars_len (n : ℕ) : (vars n).length = n := by simp [vars]

theorem vars_rev_get {n j : ℕ} (hj : j < n) : (vars n).reverse.getD j .abort = .var j := by
  rw [getD_eq_get' (by simp [vars]; omega), List.getElem_reverse]
  simp only [vars, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
  congr 1; omega

def argsEnv (Y : List Tm) (j : ℕ) : Tm := Y.reverse.getD j .abort

theorem close_vars (Y : List Tm) {n : ℕ} (hY : Y.length = n) :
    (vars n).map (close d P (argsEnv Y) I.var) = Y := by
  apply List.ext_getElem (by simp [vars, hY])
  intro i hi hi'
  simp only [List.length_map, vars_len] at hi
  simp only [vars, List.getElem_map, List.getElem_range, close, KubusCore.Boundary.eval, argsEnv]
  rw [getD_eq_get' (by simp; omega), List.getElem_reverse]
  congr 1; omega

end
end Model.Whnf.Boundary2
