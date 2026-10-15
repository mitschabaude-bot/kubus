import Model.Whnf.Fund2Aux
import Model.Whnf.Valid2ConH

/-! # Structural inversion data for higher inductive eliminators -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} (hW : WfSig S) {Ψ : ℕ} {Φ : I} {Γ : Ctx} {d : ℕ} {ps P bs t T : Tm}
include hW

theorem ElimInv2.conv {T' : Tm} {l : ℕ} (h : ElimInv2 S Ψ Φ Γ d ps P bs t T)
    (hT : Valid2 S Ψ Φ Γ T T' (.univ l)) : ElimInv2 S Ψ Φ Γ d ps P bs t T' := by
  obtain ⟨D, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hl, hbr, hbd, ht, htr⟩ := h
  exact ⟨D, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hl, hbr, hbd, ht, htr.trans (ElTr2.of_valid hW hT)⟩

theorem ElimInv2.restrict {Φ' : I} (hs : Φ'.Scoped Ψ) (he : I.Entails Φ' Φ)
    (h : ElimInv2 S Ψ Φ Γ d ps P bs t T) : ElimInv2 S Ψ Φ' Γ d ps P bs t T := by
  obtain ⟨D, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hl, hbr, hbd, ht, htr⟩ := h
  exact ⟨D, m, hd, hp, HasTele0.restrict hs he hpt, VTele2.restrict hW he hvp, valid_restrict hW he hvd, HasTy0.restrict hs he hpm, valid_restrict hW he hvm, hbs, hl,
    (fun c C b hc hb => valid_restrict hW he (hbr c C b hc hb)),
    (fun c C b kb ψ e hc hb hk => valid_restrict hW (ent_and_mono (ent_ren he (· + C.dims)) (ent_refl _))
      (hbd c C b kb ψ e hc hb hk)), HasTy0.restrict hs he ht, htr.restrict he⟩

theorem ElimInv2.cumul {l : ℕ} (hl : l + 1 ≤ maxLevel)
    (h : ElimInv2 S Ψ Φ Γ d ps P bs t (.univ l)) : ElimInv2 S Ψ Φ Γ d ps P bs t (.univ (l + 1)) := by
  obtain ⟨D, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hlen, hbr, hbd, ht, htr⟩ := h
  exact ⟨D, m, hd, hp, hpt, hvp, hvd, hpm, hvm, hbs, hlen, hbr, hbd, ht, htr.trans (ElTr2.cumul hW hl)⟩

end

end Model.Whnf
