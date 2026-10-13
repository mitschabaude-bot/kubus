import Model.SoundSig
import Model.Rules.Basic

/-!
# Consistency of Kubus Core

There is no closed term of `(X : U₀) → X` in a well-formed signature: applying it to the empty
type (a well-formed code of level 0) would give an element of the empty type.
-/

set_option autoImplicit false

namespace Model

open KubusCore

/-- The empty type is a small code. -/
theorem emptyC_mem_Vt (m : ℕ) : emptyC m ∈ Vt 0 := emptyC_mem_Vt' (by omega)

theorem consistent : KubusCore.Consistent := by
  intro S t hS ht
  have hok := sigOK_of_wfSig _ S rfl hS
  obtain ⟨-, -, -, hsem⟩ := sound_ty hok ht
  have hpt : IsPoint S .one [] 0 (fun _ => DM.zero 0) (fun _ => emptyC 0) :=
    ⟨by simp [DM.holds, ival.fn, I.eval], fun x A h => by simp [Ctx.lookup] at h,
      fun _ => isKV_mkKV _⟩
  obtain ⟨hmem, -⟩ := hsem 0 _ _ hpt
  rw [sem_pi (by rw [sem_univ]; exact isKV_univC 0)] at hmem
  simp only [El_piC, piElSet, mem_piEl, sem_univ] at hmem
  obtain ⟨-, hfun, -⟩ := hmem
  have hE : emptyC 0 ∈ El (res (Hom.id 0) (univC 0 0)) (Hom.id 0) := by
    rw [res_univC, El_univC, ZFSet.mem_sep]
    exact ⟨emptyC_mem_Vt 0, WFI.empty⟩
  have := (hfun 0 (Hom.id 0)).2 _ hE
  rw [res_univC] at hE
  simp only [famV, dat_res, Hom.comp_id, dat_lamV] at this
  rw [apZ_fnZ _ hE] at this
  simp [interp, TEnv.cons] at this

end Model
