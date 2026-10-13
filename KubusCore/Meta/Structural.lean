import KubusCore.Meta.Substitution

/-!
# Metatheory: the spec's structural rules for the minimal judgments

Single substitution of a term variable (`HasTy.subst`, `EqTm.subst`) and of an interval
variable (`HasTy.dsubst`, `EqTm.dsubst`), as instances of the substitution theorem.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- The identity substitution. -/
theorem tySub_id {Ψ Φ Γ} (hw : Wf0 S Ψ Φ Γ) : TySub S Ψ Φ Γ Ψ Φ Γ Tm.var I.var :=
  { bound := fun i hi => hi
    hscoped := scoped_of_wf hw
    ent := by rw [I_subst_var]; exact ent_refl _
    look := fun x A hx => by rw [subst_var]; exact HasTy0.var hw hx
    wf := hw }

/-- Instantiating the interval variable 0 by `r` in a context that does not mention it. -/
theorem tySub_inst0 {Ψ Φ Γ} (hw : Wf0 S Ψ Φ Γ) {r : I} (hr : r.Scoped Ψ) :
    TySub S (Ψ + 1) Φ.shift Γ.dshift Ψ Φ Γ Tm.var (I.inst0 r) :=
  { bound := fun i hi => by
      cases i with
      | zero => exact hr
      | succ i => show i < Ψ; omega
    hscoped := scoped_of_wf hw
    ent := by
      have : Φ.shift.subst (I.inst0 r) = Φ := by
        simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var Φ
      rw [this]; exact ent_refl _
    look := fun x A hx => by
      rw [lookup_dshift, Option.map_eq_some_iff] at hx
      obtain ⟨A0, hA0, rfl⟩ := hx
      have : A0.dshift.subst Tm.var (I.inst0 r) = A0 := dshift_dinst A0 r
      rw [this]; exact HasTy0.var hw hA0
    wf := hw }

theorem dinst_eq (t : Tm) (r : I) : t.subst Tm.var (I.inst0 r) = t.dinst r := rfl

/-- A context well-formed after weakening by an interval variable is well-formed. -/
theorem wf_unshift (hS : SigClosed S) {Ψ Φ} : ∀ {Γ : Ctx}, Wf0 S (Ψ + 1) Φ.shift Γ.dshift → Wf0 S Ψ Φ Γ
  | [], h => Wf0.nil (scoped_unshift (scoped_of_wf h))
  | A :: Γ, Wf0.cons h => by
    have hw : Wf0 S Ψ Φ Γ := wf_unshift hS (wf_of_ty h)
    have := (sub_ty hS h).2.1 (tySub_inst0 hw (r := .zero) trivial)
    rw [dinst_eq, dshift_dinst] at this
    exact Wf0.cons this

/-- `HasTy.dsubst` is admissible. -/
theorem HasTy0.dsubst (hS : SigClosed S) {Ψ Φ Γ t A r} (h : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift t A)
    (hr : r.Scoped Ψ) : HasTy0 S Ψ Φ Γ (t.dinst r) (A.dinst r) :=
  (sub_ty hS h).2.1 (tySub_inst0 (wf_unshift hS (wf_of_ty h)) hr)

/-- `EqTm.dsubst` is admissible. -/
theorem EqTm0.dsubst (hS : SigClosed S) {Ψ Φ Γ t t' A r} (h : EqTm0 S (Ψ + 1) Φ.shift Γ.dshift t t' A)
    (hr : r.Scoped Ψ) : EqTm0 S Ψ Φ Γ (t.dinst r) (t'.dinst r) (A.dinst r) :=
  (sub_eq hS h).2 (tySub_inst0 (wf_unshift hS (wf_of_eq h)) hr)

theorem inst_eq (t a : Tm) : t.subst (consT a Tm.var) I.var = t.inst a := by
  simp only [Tm.inst]; apply subst_congr
  · intro n; cases n <;> rfl
  · intro i; rfl

/-- `HasTy.subst` is admissible. -/
theorem HasTy0.subst (hS : SigClosed S) {Ψ Φ Γ A B t a} (h : HasTy0 S Ψ Φ (A :: Γ) t B)
    (ha : HasTy0 S Ψ Φ Γ a A) : HasTy0 S Ψ Φ Γ (t.inst a) (B.inst a) := by
  have hσ := (tySub_id (wf_of_ty ha)).cons (A := A) (by rw [subst_var]; exact ha)
  have := (sub_ty hS h).2.1 hσ
  rwa [inst_eq, inst_eq] at this

/-- `EqTm.subst` with the same term substituted on both sides. -/
theorem EqTm0.subst1 (hS : SigClosed S) {Ψ Φ Γ A B t t' a} (h : EqTm0 S Ψ Φ (A :: Γ) t t' B)
    (ha : HasTy0 S Ψ Φ Γ a A) : EqTm0 S Ψ Φ Γ (t.inst a) (t'.inst a) (B.inst a) := by
  have hσ := (tySub_id (wf_of_ty ha)).cons (A := A) (by rw [subst_var]; exact ha)
  have := (sub_eq hS h).2 hσ
  rwa [inst_eq, inst_eq, inst_eq] at this

/-- Functionality of single substitution. -/
theorem HasTy0.inst_congr (hS : SigClosed S) {Ψ Φ Γ A B t a a'} (h : HasTy0 S Ψ Φ (A :: Γ) t B)
    (ha : HasTy0 S Ψ Φ Γ a A) (ha' : HasTy0 S Ψ Φ Γ a' A) (he : EqTm0 S Ψ Φ Γ a a' A) :
    EqTm0 S Ψ Φ Γ (t.inst a) (t.inst a') (B.inst a) := by
  have hw := wf_of_ty ha
  have h1 := (tySub_id hw).cons (A := A) (by rw [subst_var]; exact ha)
  have h2 := (tySub_id hw).cons (A := A) (by rw [subst_var]; exact ha')
  have hE : EqSub S Ψ (A :: Γ) Ψ Φ Γ (consT a Tm.var) I.var (consT a' Tm.var) I.var :=
    EqSub.cons ⟨fun x A hx => by rw [subst_var]; exact EqTm0.refl (HasTy0.var hw hx),
      fun i _ => I_eq_refl _⟩ (by rw [subst_var]; exact he)
  have := (sub_ty hS h).2.2 h1 h2 hE
  rwa [inst_eq, inst_eq, inst_eq] at this

/-- The spec's `EqTm.subst`, given that the right-hand sides are typed (a presupposition). -/
theorem EqTm0.subst (hS : SigClosed S) {Ψ Φ Γ A B t t' a a'} (h : EqTm0 S Ψ Φ (A :: Γ) t t' B)
    (ht' : HasTy0 S Ψ Φ (A :: Γ) t' B) (ha : HasTy0 S Ψ Φ Γ a A) (ha' : HasTy0 S Ψ Φ Γ a' A)
    (he : EqTm0 S Ψ Φ Γ a a' A) : EqTm0 S Ψ Φ Γ (t.inst a) (t'.inst a') (B.inst a) :=
  EqTm0.trans (EqTm0.subst1 hS h ha) (HasTy0.inst_congr hS ht' ha ha' he)

end KubusCore.Meta
