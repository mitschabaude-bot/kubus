import Model.Whnf.CSub2

/-!
# Semantic validity of judgments

`Valid2 S Ψ Φ Γ t u A`: at every related closing substitution, the instances of `A` are related types
and the left instance of `t` is related to the right instance of `u`. The fundamental lemma shows
that every derivable equation is valid; this file has the validity of the structural rules and of the
rules of the type formers without Kan operations.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-- Semantic validity of an equation. -/
def Valid2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t u A : Tm) : Prop :=
  ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L A) (c.R A) ∧ RE2 S k (c.L A) (c.L t) (c.R u)

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem Valid2.tyCode {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) (c : CSub2 S Ψ Φ Γ k) :
    TyCode k (semK S k (c.L A)) :=
  RE2.tyCode hW (h k c).2

/-- The right instances, related at the left type. -/
theorem Valid2.right {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) (c : CSub2 S Ψ Φ Γ k) :
    RE2 S k (c.L A) (c.R t) (c.R u) :=
  RE2.conv hW (RT2.symm hW (h.tyCode hW c) (h k c).1) (h k (c.diagR hW)).2

theorem valid_symm {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) : Valid2 S Ψ Φ Γ u t A := by
  intro k c
  obtain ⟨hT, h1⟩ := h k c
  have hX := h.tyCode hW c
  have hTL := RT2.refl hW hX hT
  have h2 := (h k (c.diagL hW)).2
  have h3 := h.right hW c
  refine ⟨hT, ?_⟩
  exact RE2.trans hW hTL (RE2.symm hW hTL h2) (RE2.trans hW hTL h1 (RE2.symm hW hTL h3))

theorem valid_trans {t u v A : Tm} (h1 : Valid2 S Ψ Φ Γ t u A) (h2 : Valid2 S Ψ Φ Γ u v A) :
    Valid2 S Ψ Φ Γ t v A := by
  intro k c
  obtain ⟨hT, a⟩ := h1 k c
  have hTL := RT2.refl hW (h1.tyCode hW c) hT
  exact ⟨hT, RE2.trans hW hTL a (h2.right hW c)⟩

/-- A valid type, at the universe. -/
theorem Valid2.ty {A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ A B (.univ l)) (c : CSub2 S Ψ Φ Γ k) :
    RT2 S k (c.L A) (c.R B) :=
  RE2_univ_ty hW (h k c).2

theorem valid_conv {t u A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ t u A) (hAB : Valid2 S Ψ Φ Γ A B (.univ l)) :
    Valid2 S Ψ Φ Γ t u B := by
  intro k c
  obtain ⟨hT, a⟩ := h k c
  have hX := h.tyCode hW c
  have hLR := hAB.ty hW c
  have hLL := hAB.ty hW (c.diagL hW)
  refine ⟨RT2.trans hW (RT2.semK_eq hW hLL ▸ hX) (RT2.symm hW hX hLL) hLR, RE2.conv hW hLL a⟩

theorem valid_restrict {Φ' : I} {t u A : Tm} (he : I.Entails Φ' Φ) (h : Valid2 S Ψ Φ Γ t u A) :
    Valid2 S Ψ Φ' Γ t u A := fun k c => h k (c.restrictTo he)

theorem valid_var {x : ℕ} {A : Tm} (h : Γ.lookup x = some A) : Valid2 S Ψ Φ Γ (.var x) (.var x) A :=
  fun k c => ⟨c.lookT x A h, c.look x A h⟩

theorem valid_univ {l : ℕ} (hl : l + 1 ≤ maxLevel) : Valid2 S Ψ Φ Γ (.univ l) (.univ l) (.univ (l + 1)) := by
  intro k c
  have hty : HasTy S k .one [] (.univ l) (.univ (l + 1)) := HasTy.univ hl (Wf.nil trivial)
  exact ⟨RT2_univ hW, RE2_univ_of hW ⟨hty, hty, EqTm.refl hty⟩ (RT2_univ hW)⟩

theorem valid_cumul {A B : Tm} {l : ℕ} (hl : l + 1 ≤ maxLevel) (h : Valid2 S Ψ Φ Γ A B (.univ l)) :
    Valid2 S Ψ Φ Γ A B (.univ (l + 1)) := by
  intro k c
  obtain ⟨he, hm, hrt⟩ := (RE2_univ_iff hW).1 (h k c).2
  refine ⟨RT2_univ hW, (RE2_univ_iff hW).2 ⟨⟨HasTy.cumul hl he.1, HasTy.cumul hl he.2.1, EqTm.cumul hl he.2.2⟩,
    ?_, hrt⟩⟩
  have hm' := ZFSet.mem_sep.1 hm
  exact ZFSet.mem_sep.2 ⟨Vt_subset_succ l (by unfold maxLevel at hl; omega) hm'.1, hm'.2.cumul⟩

end

end Model.Whnf
