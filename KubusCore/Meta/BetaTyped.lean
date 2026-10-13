import KubusCore.Meta.PresupB

/-!
# Metatheory: contracta of the β-rules

Given the generation data of a redex (the introduction form at its natural type `X`, related
to the type `Y` the elimination expects by `Rel`), the contractum is typed. Injectivity of
type formers relates the components of `X` and `Y`; no-confusion handles chains through a
universe and `plam`s typed at path types versus `(i : I) → A`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem piBeta_of (hS : SigClosed S) {Ψ Φ Γ A t a X l A1 B1 T}
    (hI : IntroTy S Ψ Φ Γ (lam A t) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (r : Rel S Ψ Φ Γ X (pi A1 B1)) (hT1 : TB S Ψ Φ Γ (pi A1 B1)) (ha : HasTy0 S Ψ Φ Γ a A1)
    (ch : TyChainC S Ψ Φ Γ (B1.inst a) T) : HasTy0 S Ψ Φ Γ (t.inst a) T := by
  obtain ⟨B, l0, rfl, _, ht⟩ := hI
  obtain ⟨m, _, e⟩ := r.collapse hX hl rfl hT1 (fun k h => by cases h)
  have ha' := HasTy0.conv ha (EqTm0.symm (EqTm0.piInjDom e))
  exact ch.transport (HasTy0.conv (HasTy0.subst hS ht ha') (EqTm0.piInjCod e ha'))

theorem fstBeta_of {Ψ Φ Γ a b X l A1 B1 T}
    (hI : IntroTy S Ψ Φ Γ (pair a b) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (r : Rel S Ψ Φ Γ X (sigma A1 B1)) (hT1 : TB S Ψ Φ Γ (sigma A1 B1))
    (ch : TyChainC S Ψ Φ Γ A1 T) : HasTy0 S Ψ Φ Γ a T := by
  obtain ⟨A, B, l0, rfl, _, ha, _⟩ := hI
  obtain ⟨m, _, e⟩ := r.collapse hX hl rfl hT1 (fun k h => by cases h)
  exact ch.transport (HasTy0.conv ha (EqTm0.sigmaInjDom e))

theorem sndBeta_of (hS : SigClosed S) {Ψ Φ Γ a b X l A1 B1 T}
    (hI : IntroTy S Ψ Φ Γ (pair a b) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (r : Rel S Ψ Φ Γ X (sigma A1 B1)) (hT1 : TB S Ψ Φ Γ (sigma A1 B1))
    (ch : TyChainC S Ψ Φ Γ (B1.inst (fst (pair a b))) T) : HasTy0 S Ψ Φ Γ b T := by
  obtain ⟨A, B, l0, rfl, hp, ha, hb⟩ := hI
  have hT1' := hT1
  obtain ⟨m, _, e⟩ := r.collapse hX hl rfl hT1 (fun k h => by cases h)
  rcases hT1' with ⟨l1, _, hs1⟩ | ⟨k, h, _⟩
  · have hB1 := HasTy0.sigmaCod hS hs1
    have ha1 := HasTy0.conv ha (EqTm0.sigmaInjDom e)
    have hpair := HasTy0.conv (HasTy0.pair hp ha hb) e
    have hf := HasTy0.fst hpair
    have e1 := EqTm0.sigmaInjCod e ha
    have e2 := HasTy0.inst_congr hS hB1 ha1 hf (EqTm0.symm (EqTm0.fstBeta hf))
    exact ch.transport (HasTy0.conv (HasTy0.conv hb e1) e2)
  · cases h

theorem pathBeta_of (hS : SigClosed S) {Ψ Φ Γ t r X l Y A1 T}
    (hI : IntroTy S Ψ Φ Γ (plam t) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (hY : (∃ a1 b1, Y = path A1 a1 b1) ∨ Y = ipi A1) (hr : r.Scoped Ψ)
    (rel : Rel S Ψ Φ Γ X Y) (hT1 : TB S Ψ Φ Γ Y)
    (ch : TyChainC S Ψ Φ Γ (A1.dinst r) T) : HasTy0 S Ψ Φ Γ (t.dinst r) T := by
  have hYu : ∀ k, Y ≠ univ k := fun k h => by rcases hY with ⟨_, _, rfl⟩ | rfl <;> cases h
  obtain ⟨l1, hl1, hYt⟩ : ∃ l1, l1 ≤ maxLevel ∧ HasTy0 S Ψ Φ Γ Y (univ l1) := by
    rcases hT1 with h | ⟨k, h, _⟩
    · exact h
    · exact absurd h (hYu k)
  have hA1 : HasTy0 S Ψ Φ Γ (A1.dinst r) (univ l1) := by
    rcases hY with ⟨a1, b1, rfl⟩ | rfl
    · exact HasTy0.dsubst hS (HasTy0.pathLine hS hYt) hr
    · exact HasTy0.dsubst hS (HasTy0.ipiLine hS hYt) hr
  have hle := Nat.max_le.2 ⟨hl, hl1⟩
  -- the line of the natural type at `r`, and its equation with `A1` at `r`
  obtain ⟨A, hAt, k, eA⟩ : ∃ A, HasTy0 S (Ψ + 1) Φ.shift Γ.dshift t A ∧
      ∃ k, EqTm0 S Ψ Φ Γ (A.dinst r) (A1.dinst r) (univ k) := by
    obtain ⟨m, _, e⟩ := rel.collapse hX hl (by rcases hI with ⟨_, _, _, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> rfl)
      (.inl ⟨l1, hl1, hYt⟩) hYu
    rcases hI with ⟨A, a, b, l0, rfl, _, ht, _, _⟩ | ⟨A, l0, rfl, _, ht⟩
    · have hAr := HasTy0.dsubst hS (HasTy0.pathLine hS hX) hr
      refine ⟨A, ht, ?_⟩
      rcases hY with ⟨a1, b1, rfl⟩ | rfl
      · exact ⟨m, EqTm0.pathInjLine e hr⟩
      · exact ⟨_, EqTm0.noConf (X := path A a b) (Y := ipi A1) rfl e
          (hAr.lift (Nat.le_max_left _ _) hle) (hA1.lift (Nat.le_max_right _ _) hle)⟩
    · have hAr := HasTy0.dsubst hS (HasTy0.ipiLine hS hX) hr
      refine ⟨A, ht, ?_⟩
      rcases hY with ⟨a1, b1, rfl⟩ | rfl
      · exact ⟨_, EqTm0.noConf (X := ipi A) (Y := path A1 a1 b1) rfl e
          (hAr.lift (Nat.le_max_left _ _) hle) (hA1.lift (Nat.le_max_right _ _) hle)⟩
      · exact ⟨m, EqTm0.ipiInj e hr⟩
  exact ch.transport (HasTy0.conv (HasTy0.dsubst hS hAt hr) eA)

end KubusCore.Meta
