import KubusCore.Meta.HcompTyped

/-!
# Metatheory: derived rules for interval substitutions

Typing is stable under interval substitutions of a whole judgment (`HasTy0.isub`), and
interval substitutions that are equal in the free De Morgan algebra give equal results
(`HasTy0.ieq`), for contexts on which the two substitutions agree.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- Substitute interval variables in a context. -/
def ctxI (τ : Nat → I) (Γ : Ctx) : Ctx := Γ.map (·.subst Tm.var τ)

theorem lookup_ctxI (τ : Nat → I) (Γ : Ctx) (x : Nat) :
    (ctxI τ Γ).lookup x = (Γ.lookup x).map (·.subst Tm.var τ) :=
  lookup_map (fun t => shift_substI t τ) x

theorem tySub_I {Ψ Φ Γ Ψ' Φ' τ} (hb : ∀ i < Ψ, (τ i).Scoped Ψ') (he : I.Entails Φ' (Φ.subst τ))
    (hw : Wf0 S Ψ' Φ' (ctxI τ Γ)) : TySub S Ψ Φ Γ Ψ' Φ' (ctxI τ Γ) Tm.var τ :=
  { bound := hb, hscoped := scoped_of_wf hw, ent := he, wf := hw
    look := fun x A hx => HasTy0.var hw (by rw [lookup_ctxI, hx]; rfl) }

theorem HasTy0.isub (hS : SigClosed S) {Ψ Φ Γ t T Ψ' Φ' τ} (h : HasTy0 S Ψ Φ Γ t T)
    (hb : ∀ i < Ψ, (τ i).Scoped Ψ') (he : I.Entails Φ' (Φ.subst τ)) (hw : Wf0 S Ψ' Φ' (ctxI τ Γ)) :
    HasTy0 S Ψ' Φ' (ctxI τ Γ) (t.subst Tm.var τ) (T.subst Tm.var τ) :=
  (sub_ty hS h).2.1 (tySub_I hb he hw)

theorem EqTm0.isub (hS : SigClosed S) {Ψ Φ Γ t u T Ψ' Φ' τ} (h : EqTm0 S Ψ Φ Γ t u T)
    (hb : ∀ i < Ψ, (τ i).Scoped Ψ') (he : I.Entails Φ' (Φ.subst τ)) (hw : Wf0 S Ψ' Φ' (ctxI τ Γ)) :
    EqTm0 S Ψ' Φ' (ctxI τ Γ) (t.subst Tm.var τ) (u.subst Tm.var τ) (T.subst Tm.var τ) :=
  (sub_eq hS h).2 (tySub_I hb he hw)

/-- Interval substitutions equal in the free De Morgan algebra give equal results. -/
theorem HasTy0.ieq (hS : SigClosed S) {Ψ Φ Γ t T Ψ' Φ' τ1 τ2} (h : HasTy0 S Ψ Φ Γ t T)
    (hb1 : ∀ i < Ψ, (τ1 i).Scoped Ψ') (hb2 : ∀ i < Ψ, (τ2 i).Scoped Ψ')
    (he1 : I.Entails Φ' (Φ.subst τ1)) (he2 : I.Entails Φ' (Φ.subst τ2))
    (heq : ∀ i < Ψ, I.Eq (τ1 i) (τ2 i)) (hΓ : ctxI τ1 Γ = ctxI τ2 Γ) (hw : Wf0 S Ψ' Φ' (ctxI τ1 Γ)) :
    EqTm0 S Ψ' Φ' (ctxI τ1 Γ) (t.subst Tm.var τ1) (t.subst Tm.var τ2) (T.subst Tm.var τ1) := by
  have k1 := tySub_I hb1 he1 hw
  have k2 := tySub_I hb2 he2 (hΓ ▸ hw)
  rw [← hΓ] at k2
  exact (sub_ty hS h).2.2 k1 k2 ⟨fun x A hx => EqTm0.refl (k1.look x A hx), heq⟩

theorem ctxI_dshift (τ : Nat → I) (Γ : Ctx) (h : ∀ i, τ (i + 1) = .var (i + 1)) :
    ctxI τ Γ.dshift = Γ.dshift := by
  simp only [ctxI, Ctx.dshift, List.map_map]
  congr 1; funext t
  simp only [Function.comp, dshift_eq, subst_subst]
  exact subst_congr (fun n => rfl) (fun i => by simp only [I.subst, h]) t

end KubusCore.Meta
