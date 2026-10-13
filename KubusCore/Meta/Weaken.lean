import KubusCore.Meta.Ren

/-!
# Metatheory: weakening

The spec's primitive weakening rules `HasTy.wk`/`EqTm.wk` (by a term variable) and
`HasTy.dwk`/`EqTm.dwk` (by an interval variable) are admissible for the minimal judgments,
as instances of the renaming theorem.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- A well-formed context is well-formed under all interval weakenings and stronger
restrictions. -/
theorem wfAll_of_wf (hS : SigClosed S) : ∀ {Δ : Ctx} {Ψ Φ}, Wf0 S Ψ Φ Δ → WfAll S Ψ Φ Δ
  | [], _, _, .nil hs => fun k Φ'' hs' _ => Wf0.nil hs'
  | A :: Δ, Ψ, Φ, .cons hA => by
    have ih := wfAll_of_wf hS (wf_of_ty hA)
    intro k Φ'' hs he
    have hR : TyRen S Ψ Φ Δ (Ψ + k) Φ'' (ctxWkI k Δ) id (· + k) :=
      { inj := fun i j h => by simpa using h
        bound := fun i hi => by simp; omega
        hscoped := hs
        ent := he
        look := fun x B hx => by rw [lookup_wkI, id, hx]; rfl
        wf := ih.wk k he }
    have := (ren_ty hS hA).2 hR
    exact Wf0.cons this

theorem tyRen_id_wk (hS : SigClosed S) {Ψ Φ Γ B l} (hB : HasTy0 S Ψ Φ Γ B (Tm.univ l)) :
    TyRen S Ψ Φ Γ Ψ Φ (B :: Γ) Nat.succ id where
  inj i j h := h
  bound i hi := hi
  hscoped := scoped_of_ty hB
  ent := by rw [show rI id = I.var from rfl, I_subst_var]; exact ent_refl _
  look x A hx := by
    show Ctx.lookup (B :: Γ) (x + 1) = _
    simp only [Ctx.lookup, hx, Option.map_some, shift_eq]; rfl
  wf := wfAll_of_wf hS (Wf0.cons hB)

theorem shift_rn (t : Tm) : t.subst (rS Nat.succ) (rI id) = t.shift := by rw [shift_eq]; rfl

theorem dshift_rn (t : Tm) : t.subst (rS id) (rI Nat.succ) = t.dshift := by rw [dshift_eq]; rfl

/-- `HasTy.wk` is admissible. -/
theorem HasTy0.wk (hS : SigClosed S) {Ψ Φ Γ t A B l} (hB : HasTy0 S Ψ Φ Γ B (Tm.univ l))
    (h : HasTy0 S Ψ Φ Γ t A) : HasTy0 S Ψ Φ (B :: Γ) t.shift A.shift := by
  have := (ren_ty hS h).2 (tyRen_id_wk hS hB)
  rwa [shift_rn, shift_rn] at this

/-- `EqTm.wk` is admissible. -/
theorem EqTm0.wk (hS : SigClosed S) {Ψ Φ Γ t u A B l} (hB : HasTy0 S Ψ Φ Γ B (Tm.univ l))
    (h : EqTm0 S Ψ Φ Γ t u A) : EqTm0 S Ψ Φ (B :: Γ) t.shift u.shift A.shift := by
  have := (ren_eq hS h).2 (tyRen_id_wk hS hB)
  rwa [shift_rn, shift_rn, shift_rn] at this

theorem tyRen_dwk (hS : SigClosed S) {Ψ Φ Γ} (hw : Wf0 S Ψ Φ Γ) :
    TyRen S Ψ Φ Γ (Ψ + 1) Φ.shift Γ.dshift id Nat.succ where
  inj i j h := Nat.succ.inj h
  bound i hi := Nat.succ_lt_succ hi
  hscoped := scoped_shift (scoped_of_wf hw)
  ent := ent_refl _
  look x A hx := by
    rw [Ctx_dshift_eq, lookup_wkI]; simp only [id, hx]; rfl
  wf := by
    rw [Ctx_dshift_eq]
    exact (wfAll_of_wf hS hw).wk 1 (ent_refl _)

/-- `HasTy.dwk` is admissible. -/
theorem HasTy0.dwk (hS : SigClosed S) {Ψ Φ Γ t A} (h : HasTy0 S Ψ Φ Γ t A) :
    HasTy0 S (Ψ + 1) Φ.shift Γ.dshift t.dshift A.dshift := by
  have := (ren_ty hS h).2 (tyRen_dwk hS (wf_of_ty h))
  rwa [dshift_rn, dshift_rn] at this

/-- `EqTm.dwk` is admissible. -/
theorem EqTm0.dwk (hS : SigClosed S) {Ψ Φ Γ t u A} (h : EqTm0 S Ψ Φ Γ t u A) :
    EqTm0 S (Ψ + 1) Φ.shift Γ.dshift t.dshift u.dshift A.dshift := by
  have := (ren_eq hS h).2 (tyRen_dwk hS (wf_of_eq h))
  rwa [dshift_rn, dshift_rn, dshift_rn] at this

end KubusCore.Meta
