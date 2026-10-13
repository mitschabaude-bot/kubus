import Model.Rules.PathLemmas

/-!
# Helpers for the rules of the Kan operations

The interpretation of `transp`/`hcomp` performs the code's operation when its side conditions
hold (good code, constant line on the face / typed tube, typed base). The typing rules make
these conditions hold at every point; the face and computation rules then read off the value
from the fibration structure `Fib` of the code.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem IEnv.ext_restr_snoc (ρ : IEnv m) (h : Hom k m) (r : DM k) :
    ρ.ext.restr (Hom.snoc h r) = (ρ.restr h).cons r := by
  funext i; cases i with
  | zero => exact lastVar_restr_snoc h r
  | succ i => simp only [IEnv.ext, IEnv.restr, IEnv.cons, DM.restr_restr, Hom.wk_comp_snoc]

theorem TEnv.restr_wk_snoc (γ : ℕ → V) (h : Hom k m) (r : DM k) :
    TEnv.restr (TEnv.restr γ (Hom.wk m)) (Hom.snoc h r) = TEnv.restr γ h := by
  rw [TEnv.restr_restr, Hom.wk_comp_snoc]

theorem holds_face_restr_iff {ρ : IEnv m} {φ : I} (h : Hom k m) :
    (Cof.restr (ival ρ φ).face h).holds ↔ (ival (ρ.restr h) φ).holds := by
  rw [ival.restr, DM.holds_iff_face_holds, DM.face_restr]

theorem isCof_ival_face (ρ : IEnv m) (φ : I) : Cof.IsCof (ival ρ φ).face := ⟨_, rfl⟩

/-- The tube of `hcomp A φ u a` at the point `(ρ, γ)`. -/
def tubeV (S : Sig) (u : Tm) (ρ : IEnv m) (γ : ℕ → V) : Tube m :=
  fun n h r => sem S u n ((ρ.restr h).cons r) (TEnv.restr γ h)

/-! ### transp -/

/-- The side conditions of `transp A φ a` at a point. -/
def TranspCond (S : Sig) (A : Tm) (φ : I) (a : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop :=
  TyCode (m + 1) (lineV S A m ρ γ) ∧ ConstOn (lineV S A m ρ γ) (Hom.id (m + 1)) (ival ρ φ).face ∧
    sem S a m ρ γ ∈ El (lineV S A m ρ γ) ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m)))

theorem sem_transp {A a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (h : TranspCond S A φ a m ρ γ) :
    sem S (.transp A φ a) m ρ γ = transpAt (lineV S A m ρ γ) (Hom.id (m + 1)) (ival ρ φ).face (sem S a m ρ γ) := by
  simp only [sem, interp]; exact if_pos h

theorem cond_of_sem_transp {A a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (h : sem S (.transp A φ a) m ρ γ ≠ ∅) : TranspCond S A φ a m ρ γ := by
  simp only [sem, interp] at h; split at h
  · assumption
  · exact absurd rfl h

/-- The premises of the `transp` rule give its side conditions at every point. -/
theorem transp_cond {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A a : Tm} {φ : I} {l : ℕ}
    (h0 : SemTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l))
    (h2 : SemEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (h3 : SemTy S Ψ Φ Γ a (A.dinst .zero)) {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) :
    TranspCond S A φ a m ρ γ ∧ Natural S A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)) ∧
      l ≤ maxLevel ∧ lineV S A m ρ γ ∈ Vt l ∧ WF l (m + 1) (lineV S A m ρ γ) := by
  have hwf : SemWf S Ψ Φ Γ := h3.1
  obtain ⟨hLmem, hN, hUty, -⟩ := h0.2.2.2 _ _ _ (hp.dext hwf)
  rw [sem_univ, mem_El_univ_iff] at hLmem
  have hl : l ≤ maxLevel := by unfold TyOK at hUty; rw [sem_univ] at hUty; exact hUty.univ_le
  refine ⟨⟨⟨l, hl, Or.inl ⟨hLmem.2, hLmem.1⟩⟩, ?_, ?_⟩, hN, hl, hLmem.1, hLmem.2⟩
  · intro n' h hh r
    rw [holds_face_restr_iff] at hh
    have hpr : IsPoint S (cof Φ φ) Γ n' (ρ.restr h) (TEnv.restr γ h) :=
      isPoint_cof_iff.2 ⟨hp.restr hwf h, hh⟩
    have key : ∀ r : DM n', res (Hom.snoc h r) (lineV S A m ρ γ) =
        sem S (A.dinst .zero) n' (ρ.restr h) (TEnv.restr γ h) := by
      intro r
      rw [← hN n' (Hom.snoc h r), IEnv.ext_restr_snoc, TEnv.restr_wk_snoc,
        h2.2.2 n' _ _ ((isPoint_dshift_iff (ρ := (ρ.restr h).cons r)).2 hpr), sem_dshift_cons]
    rw [Hom.id_comp, Hom.id_comp, key, key]
  · obtain ⟨hamem, -, -, -⟩ := h3.2.2.2 m ρ γ hp
    rw [sem_dinst, ival_zero, line_endpt hp.kv hN, El_res, Hom.comp_id] at hamem
    rw [Hom.id_comp]; exact hamem

/-! ### hcomp -/

/-- The side conditions of `hcomp A φ u a` at a point. -/
def HcompCond (S : Sig) (A : Tm) (φ : I) (u a : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop :=
  TyCode m (sem S A m ρ γ) ∧
    TubeOK (sem S A m ρ γ) (Hom.id m) (ival ρ φ).face (tubeV S u ρ γ) (sem S a m ρ γ) ∧
    sem S a m ρ γ ∈ El (sem S A m ρ γ) (Hom.id m)

theorem sem_hcomp {A u a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V} (h : HcompCond S A φ u a m ρ γ) :
    sem S (.hcomp A φ u a) m ρ γ =
      hcompAt (sem S A m ρ γ) (Hom.id m) (ival ρ φ).face (tubeV S u ρ γ) (sem S a m ρ γ) := by
  simp only [sem, interp]; exact if_pos h

theorem cond_of_sem_hcomp {A u a : Tm} {φ : I} {ρ : IEnv m} {γ : ℕ → V}
    (h : sem S (.hcomp A φ u a) m ρ γ ≠ ∅) : HcompCond S A φ u a m ρ γ := by
  simp only [sem, interp] at h; split at h
  · assumption
  · exact absurd rfl h

/-- The premises of the `hcomp` rule give its side conditions at every point. -/
theorem hcomp_cond {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A u a : Tm} {φ : I}
    (h2 : SemTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift)
    (h3 : SemTy S Ψ Φ Γ a A) (h4 : SemEq S Ψ (cof Φ φ) Γ (u.dinst .zero) a A)
    {ρ : IEnv m} {γ : ℕ → V} (hp : IsPoint S Φ Γ m ρ γ) : HcompCond S A φ u a m ρ γ := by
  have hwf : SemWf S Ψ Φ Γ := h3.1
  obtain ⟨hamem, hanat, hAty, hAnat⟩ := h3.2.2.2 m ρ γ hp
  have hpt : ∀ n (h : Hom n m) r, (Cof.restr (ival ρ φ).face h).holds →
      IsPoint S (cof Φ φ).shift Γ.dshift n ((ρ.restr h).cons r) (TEnv.restr γ h) := by
    intro n h r hh
    rw [holds_face_restr_iff] at hh
    exact isPoint_dshift_iff.2 (isPoint_cof_iff.2 ⟨hp.restr hwf h, hh⟩)
  refine ⟨hAty, ⟨fun n h r hh => ?_, fun n h r hh n' g => ?_, fun n h hh => ?_⟩, hamem⟩
  · have := (h2.2.2.2 n _ _ (hpt n h r hh)).1
    rw [sem_dshift_cons, hAnat n h, El_res, Hom.comp_id] at this
    rw [Hom.id_comp]; exact this
  · have := (h2.2.2.2 n _ _ (hpt n h r hh)).2.1 n' g
    simp only [tubeV]
    rw [← this, IEnv.cons_restr, IEnv.restr_restr, TEnv.restr_restr]
  · rw [holds_face_restr_iff] at hh
    have := h4.2.2 n _ _ (isPoint_cof_iff.2 ⟨hp.restr hwf h, hh⟩)
    simp only [tubeV]
    rw [sem_dinst, ival_zero] at this
    rw [this, hanat n h]

end

end Model
