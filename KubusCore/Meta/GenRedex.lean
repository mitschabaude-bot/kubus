import KubusCore.Meta.Equiv

/-!
# Metatheory: generation lemmas for redexes

A typing of a `split`, `transp`, `hcomp` or `glue` element comes from its typing rule,
followed by conversions and cumulativity (`TyChainC`), along which typings can be transported.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- `X` and `Y` are connected by judgmental equalities at universes and cumulativity. -/
inductive TyChainC (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) : Tm → Tm → Prop
  | refl (X : Tm) : TyChainC S Ψ Φ Γ X X
  | step {X Y Z : Tm} {m : Nat} : EqTm0 S Ψ Φ Γ X Y (univ m) → TyChainC S Ψ Φ Γ Y Z →
      TyChainC S Ψ Φ Γ X Z
  | up {l : Nat} {Z : Tm} : l + 1 ≤ maxLevel → TyChainC S Ψ Φ Γ (univ (l + 1)) Z →
      TyChainC S Ψ Φ Γ (univ l) Z

theorem TyChainC.transport {Ψ Φ Γ X Y} : TyChainC S Ψ Φ Γ X Y → ∀ {t}, HasTy0 S Ψ Φ Γ t X →
    HasTy0 S Ψ Φ Γ t Y
  | .refl _, _, h => h
  | .step e ch, _, h => ch.transport (HasTy0.conv h e)
  | .up hl ch, _, h => ch.transport (HasTy0.cumul hl h)

theorem TyChainC.snoc {Ψ Φ Γ X Y Z m} : TyChainC S Ψ Φ Γ X Y → EqTm0 S Ψ Φ Γ Y Z (univ m) →
    TyChainC S Ψ Φ Γ X Z
  | .refl _, e => .step e (.refl _)
  | .step e' ch, e => .step e' (ch.snoc e)
  | .up hl ch, e => .up hl (ch.snoc e)

theorem TyChainC.trans {Ψ Φ Γ X Y Z} : TyChainC S Ψ Φ Γ X Y → TyChainC S Ψ Φ Γ Y Z →
    TyChainC S Ψ Φ Γ X Z
  | .refl _, h => h
  | .step e ch, h => .step e (ch.trans h)
  | .up hl ch, h => .up hl (ch.trans h)

theorem TyChainC.cumul {Ψ Φ Γ X l} (hl : l + 1 ≤ maxLevel) (ch : TyChainC S Ψ Φ Γ X (univ l)) :
    TyChainC S Ψ Φ Γ X (univ (l + 1)) := ch.trans (.up hl (.refl _))

theorem TyChainC.restrict {Ψ Φ Φ' Γ X Y} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    TyChainC S Ψ Φ Γ X Y → TyChainC S Ψ Φ' Γ X Y
  | .refl _ => .refl _
  | .step e ch => .step (EqTm0.restrict hs he e) (ch.restrict hs he)
  | .up hl ch => .up hl (ch.restrict hs he)

theorem gen_split {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {φ ψ t u} (ht : s = .split φ t ψ u) :
    ∃ A, (φ.Scoped Ψ ∧ ψ.Scoped Ψ ∧ I.Entails Φ (.or φ ψ) ∧ HasTy0 S Ψ (cof Φ φ) Γ t A ∧
      HasTy0 S Ψ (cof Φ ψ) Γ u A) ∧ TyChainC S Ψ Φ Γ A T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨x, hx, ch⟩ := gen_split h0 ht
    exact ⟨x, hx, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨A, ⟨h0, h1, h2', h4, h5⟩, ch⟩ := gen_split h2 ht
    exact ⟨A, ⟨h0, h1, ent_trans he h2', HasTy0.restrict ⟨hs, h0⟩ (ent_and_mono he (ent_refl _)) h4,
      HasTy0.restrict ⟨hs, h1⟩ (ent_and_mono he (ent_refl _)) h5⟩, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨x, hx, ch⟩ := gen_split h1 ht
    exact ⟨x, hx, ch.cumul h0⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split h0 h1 h2 _ h4 h5 _ => by cases ht; exact ⟨_, ⟨h0, h1, h2, h4, h5⟩, .refl _⟩
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_transpF {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {A φ a} (ht : s = .transp A φ a) :
    ∃ l, (HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (univ l) ∧ φ.Scoped Ψ ∧
      EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (univ l) ∧
      HasTy0 S Ψ Φ Γ a (A.dinst .zero)) ∧ TyChainC S Ψ Φ Γ (A.dinst .one) T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨x, hx, ch⟩ := gen_transpF h0 ht
    exact ⟨x, hx, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨l, ⟨h0, h1, h2', h3⟩, ch⟩ := gen_transpF h2 ht
    have hs' : (cof _ φ).Scoped Ψ := ⟨hs, h1⟩
    exact ⟨l, ⟨HasTy0.restrict (scoped_shift hs) (ent_shift he) h0, h1,
      EqTm0.restrict (scoped_shift hs') (ent_shift (ent_and_mono he (ent_refl _))) h2',
      HasTy0.restrict hs he h3⟩, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨x, hx, ch⟩ := gen_transpF h1 ht
    exact ⟨x, hx, ch.cumul h0⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp h0 h1 h2 h3 => by cases ht; exact ⟨_, ⟨h0, h1, h2, h3⟩, .refl _⟩
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_hcomp {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {A φ u a} (ht : s = .hcomp A φ u a) :
    ∃ l, (HasTy0 S Ψ Φ Γ A (univ l) ∧ φ.Scoped Ψ ∧
      HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift ∧ HasTy0 S Ψ Φ Γ a A ∧
      EqTm0 S Ψ (cof Φ φ) Γ (u.dinst .zero) a A) ∧ TyChainC S Ψ Φ Γ A T :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨x, hx, ch⟩ := gen_hcomp h0 ht
    exact ⟨x, hx, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨l, ⟨h0, h1, h2', h3, h4⟩, ch⟩ := gen_hcomp h2 ht
    have hs' : (cof _ φ).Scoped Ψ := ⟨hs, h1⟩
    exact ⟨l, ⟨HasTy0.restrict hs he h0, h1,
      HasTy0.restrict (scoped_shift hs') (ent_shift (ent_and_mono he (ent_refl _))) h2',
      HasTy0.restrict hs he h3, EqTm0.restrict hs' (ent_and_mono he (ent_refl _)) h4⟩,
      ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨x, hx, ch⟩ := gen_hcomp h1 ht
    exact ⟨x, hx, ch.cumul h0⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp h0 h1 h2 h3 h4 => by cases ht; exact ⟨_, ⟨h0, h1, h2, h3, h4⟩, .refl _⟩
  | .glue _ _ _ _ => by cases ht
  | .glueEl _ _ _ _ _ => by cases ht
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

theorem gen_glueEl {Ψ Φ Γ s G} (h : HasTy0 S Ψ Φ Γ s G) {φ e t a} (ht : s = .glueEl φ e t a) :
    ∃ A T l, (HasTy0 S Ψ Φ Γ (glue A φ T e) (univ l) ∧ HasTy0 S Ψ (cof Φ φ) Γ e (equiv T A) ∧
      HasTy0 S Ψ (cof Φ φ) Γ t T ∧ HasTy0 S Ψ Φ Γ a A) ∧ TyChainC S Ψ Φ Γ (glue A φ T e) G :=
  match h with
  | .var _ _ => by cases ht
  | .conv h0 h1 => by
    obtain ⟨A, T, l, x, ch⟩ := gen_glueEl h0 ht
    exact ⟨A, T, l, x, ch.snoc h1⟩
  | .restrict hs he h2 => by
    obtain ⟨A, T, l, ⟨h0, h1, h2', h3⟩, ch⟩ := gen_glueEl h2 ht
    have hφ := scoped_cof_right (scoped_of_ty h1)
    have hs' : (cof _ φ).Scoped Ψ := ⟨hs, hφ⟩
    exact ⟨A, T, l, ⟨HasTy0.restrict hs he h0, HasTy0.restrict hs' (ent_and_mono he (ent_refl _)) h1,
      HasTy0.restrict hs' (ent_and_mono he (ent_refl _)) h2', HasTy0.restrict hs he h3⟩, ch.restrict hs he⟩
  | .const _ _ => by cases ht
  | .univ _ _ => by cases ht
  | .cumul h0 h1 => by
    obtain ⟨A, T, l, x, ch⟩ := gen_glueEl h1 ht
    exact ⟨A, T, l, x, ch.cumul h0⟩
  | .pi _ _ => by cases ht
  | .lam _ _ => by cases ht
  | .app _ _ => by cases ht
  | .sigma _ _ => by cases ht
  | .pair _ _ _ => by cases ht
  | .fst _ => by cases ht
  | .snd _ => by cases ht
  | .path _ _ _ => by cases ht
  | .plam _ _ _ _ => by cases ht
  | .papp _ _ => by cases ht
  | .ipi _ _ => by cases ht
  | .ilam _ _ => by cases ht
  | .iapp _ _ => by cases ht
  | .split _ _ _ _ _ _ _ => by cases ht
  | .abort _ _ => by cases ht
  | .transp _ _ _ _ => by cases ht
  | .hcomp _ _ _ _ _ => by cases ht
  | .glue _ _ _ _ => by cases ht
  | .glueEl h0 h1 h2 h3 _ => by cases ht; exact ⟨_, _, _, ⟨h0, h1, h2, h3⟩, .refl _⟩
  | .unglue _ _ _ _ => by cases ht
  | .data _ _ _ => by cases ht
  | .con _ _ _ _ _ _ _ _ => by cases ht
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases ht

/-- The head of an elimination (the eliminated term). -/
def _root_.KubusCore.Tm.elimHead : Tm → Option Tm
  | .app f _ | .fst f | .snd f | .papp f _ | .unglue _ _ f | .elim _ _ _ _ f => some f
  | _ => none

/-- The head of a typed elimination is typed. -/
theorem gen_elimHead {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {p} (ht : s.elimHead = some p) :
    ∃ T', HasTy0 S Ψ Φ Γ p T' :=
  match h with
  | .var _ _ => by simp [Tm.elimHead] at ht
  | .conv h0 _ => gen_elimHead h0 ht
  | .restrict hs he h2 => by
    obtain ⟨T', h'⟩ := gen_elimHead h2 ht
    exact ⟨T', HasTy0.restrict hs he h'⟩
  | .const _ _ => by simp [Tm.elimHead] at ht
  | .univ _ _ => by simp [Tm.elimHead] at ht
  | .cumul _ h1 => gen_elimHead h1 ht
  | .pi _ _ => by simp [Tm.elimHead] at ht
  | .lam _ _ => by simp [Tm.elimHead] at ht
  | .app h0 _ => by simp [Tm.elimHead] at ht; subst ht; exact ⟨_, h0⟩
  | .sigma _ _ => by simp [Tm.elimHead] at ht
  | .pair _ _ _ => by simp [Tm.elimHead] at ht
  | .fst h0 => by simp [Tm.elimHead] at ht; subst ht; exact ⟨_, h0⟩
  | .snd h0 => by simp [Tm.elimHead] at ht; subst ht; exact ⟨_, h0⟩
  | .path _ _ _ => by simp [Tm.elimHead] at ht
  | .plam _ _ _ _ => by simp [Tm.elimHead] at ht
  | .papp h0 _ => by simp [Tm.elimHead] at ht; subst ht; exact ⟨_, h0⟩
  | .ipi _ _ => by simp [Tm.elimHead] at ht
  | .ilam _ _ => by simp [Tm.elimHead] at ht
  | .iapp h0 _ => by simp [Tm.elimHead] at ht; subst ht; exact ⟨_, h0⟩
  | .split _ _ _ _ _ _ _ => by simp [Tm.elimHead] at ht
  | .abort _ _ => by simp [Tm.elimHead] at ht
  | .transp _ _ _ _ => by simp [Tm.elimHead] at ht
  | .hcomp _ _ _ _ _ => by simp [Tm.elimHead] at ht
  | .glue _ _ _ _ => by simp [Tm.elimHead] at ht
  | .glueEl _ _ _ _ _ => by simp [Tm.elimHead] at ht
  | .unglue _ _ _ h3 => by simp [Tm.elimHead] at ht; subst ht; exact ⟨_, h3⟩
  | .data _ _ _ => by simp [Tm.elimHead] at ht
  | .con _ _ _ _ _ _ _ _ => by simp [Tm.elimHead] at ht
  | .elim _ _ _ _ _ _ _ _ _ h9 => by simp [Tm.elimHead] at ht; subst ht; exact ⟨_, h9⟩

end KubusCore.Meta
