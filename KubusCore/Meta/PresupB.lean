import KubusCore.Meta.KanU

/-!
# Metatheory: auxiliary notions for presupposition

`IsTypB`: a type is typed at a universe, or is a universe of bounded level. The bound makes the
levels of all type equations bounded (`IsTypB.lvl`), so that conversion chains can be collapsed
into one equation by cumulativity.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-- `A` is a type: typed at some universe, or a universe of level at most `maxLevel`. -/
def IsTypB (S : Sig) (Ψ : Nat) (Φ : I) (Γ : Ctx) (A : Tm) : Prop :=
  (∃ l, HasTy0 S Ψ Φ Γ A (univ l)) ∨ ∃ l, A = univ l ∧ l ≤ maxLevel

/-- Generation for universes: only levels below `maxLevel` are typed. -/
theorem gen_univ {Ψ Φ Γ s T} (h : HasTy0 S Ψ Φ Γ s T) {l} (hs : s = .univ l) : l + 1 ≤ maxLevel :=
  match h with
  | .var _ _ => by cases hs
  | .conv h0 h1 => gen_univ h0 hs
  | .restrict h0 h1 h2 => gen_univ h2 hs
  | .const _ _ => by cases hs
  | .univ h0 h1 => by cases hs; exact h0
  | .cumul h0 h1 => gen_univ h1 hs
  | .pi _ _ => by cases hs
  | .lam _ _ => by cases hs
  | .app _ _ => by cases hs
  | .sigma _ _ => by cases hs
  | .pair _ _ _ => by cases hs
  | .fst _ => by cases hs
  | .snd _ => by cases hs
  | .path _ _ _ => by cases hs
  | .plam _ _ _ _ => by cases hs
  | .papp _ _ => by cases hs
  | .ipi _ _ => by cases hs
  | .ilam _ _ => by cases hs
  | .iapp _ _ => by cases hs
  | .split _ _ _ _ _ _ _ => by cases hs
  | .abort _ _ => by cases hs
  | .transp _ _ _ _ => by cases hs
  | .hcomp _ _ _ _ _ => by cases hs
  | .glue _ _ _ _ => by cases hs
  | .glueEl _ _ _ _ _ => by cases hs
  | .unglue _ _ _ _ => by cases hs
  | .data _ _ _ => by cases hs
  | .con _ _ _ _ _ _ _ _ => by cases hs
  | .elim _ _ _ _ _ _ _ _ _ _ => by cases hs

theorem IsTypB.lvl {Ψ Φ Γ l} : IsTypB S Ψ Φ Γ (univ l) → l ≤ maxLevel
  | .inl ⟨_, h⟩ => Nat.le_of_succ_le (gen_univ h rfl)
  | .inr ⟨_, h, hl⟩ => by cases h; exact hl

theorem IsTypB.restrict {Ψ Φ Φ' Γ A} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ) :
    IsTypB S Ψ Φ Γ A → IsTypB S Ψ Φ' Γ A
  | .inl ⟨l, h⟩ => .inl ⟨l, HasTy0.restrict hs he h⟩
  | .inr h => .inr h

theorem IsTypB.toIsTyp {Ψ Φ Γ A} : IsTypB S Ψ Φ Γ A → IsTyp S Ψ Φ Γ A
  | .inl h => .inl h
  | .inr ⟨l, h, _⟩ => .inr ⟨l, h⟩

end KubusCore.Meta
