import Model.Whnf.Valid2ElimH4
import Model.Whnf.Kan2GlueT

/-!
# Motive lines for higher inductive eliminators

The line used by elimination of a formal composition is the motive evaluated at its filler.
Its computability and Kan evidence come from the universe premise for the motive.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- Evaluate a motive in the interval context of its argument line. -/
def motiveLine (M x : Tm) : Tm := M.subst (consSub x) (fun i => .var (i + 1))

theorem motiveLine_eq (M x : Tm) : motiveLine M x = M.dshift.inst x := by
  simp only [motiveLine, Tm.inst, dshift_eq, subst_subst]
  exact subst_congr (fun _ => rfl) (fun i => (I_subst_var _).symm) M

/-- A point of the motive line is the motive instantiated at that point. -/
theorem motiveLine_isub {k' : ℕ} (M x : Tm) (σ : ISub k' (k + 1)) :
    (motiveLine M x).isub σ = (M.isub σ.tail).inst (x.isub σ) := by
  simp only [motiveLine, Tm.isub, Tm.inst, subst_subst]
  apply subst_congr
  · intro i
    cases i <;> rfl
  · intro i
    exact (I_subst_var _).symm

variable (hW : WfSig S)
include hW

/-- Related argument lines give related motive lines. -/
theorem ElimRelH.lineRob {d : ℕ} {D : DataDecl} {K : ℕ} {P M bs Q M' bs' : Tm}
    (H : ElimRelH S d D K P M bs Q M' bs') (ρ : ISub k K) {x x' : Tm}
    (hx : ∀ k' (σ σ' : ISub k' (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k' (.data d (P.isub (ρ.comp σ.tail))) (x.isub σ) (x'.isub σ')) :
    LineRob S k (motiveLine (M.isub ρ) x) (motiveLine (M'.isub ρ) x') := by
  intro k' σ r r' hr hr' he
  rw [motiveLine_isub, motiveLine_isub, Tm.isub_isub, Tm.isub_isub]
  exact H.mot k' (ρ.comp σ) _ _ (hx k' (ISub.cons r hr σ) (ISub.cons r' hr' σ) rfl he)

/-- The motive line's own code is Kan at a related argument line. -/
theorem ElimRelH.lineKan {d : ℕ} {D : DataDecl} {K : ℕ} {P M bs Q M' bs' : Tm}
    (H : ElimRelH S d D K P M bs Q M' bs') (ρ : ISub k K) {x x' : Tm}
    (hx : RE2 S (k + 1) ((Tm.data d (P.isub ρ)).isub (ISub.wk k)) x x') :
    KanP2 S (k + 1) (semK S (k + 1) (motiveLine (M.isub ρ) x)) := by
  obtain ⟨m, hE⟩ := H.tyL k ρ
  have hMc : (M.isub ρ).closedB 1 k = true := closed_ty hE.hP
  have hh := H.kan (k + 1) (ρ.comp (ISub.wk k)) x x' (by
    simpa only [data_isub_comp] using hx)
  rw [← Tm.isub_isub, dshift_eq_isub_closed hMc, ← motiveLine_eq] at hh
  exact hh

end

end Model.Whnf
