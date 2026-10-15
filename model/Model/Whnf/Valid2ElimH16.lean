import Model.Whnf.Valid2ElimH15

/-!
# Fillers from the formal composition premises

The two composition typings supply the filler typings. Pointwise tube relatedness supplies tube
equality on the face, and the stored boundary relations supply filler coherence.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ} (hW : WfSig S)
include hW

/-- Typed, related fillers of formal compositions, with the original type annotations. -/
theorem hfill_formal_rel2 {A A' u u' a a' : Tm} {φ φ' : I} {l l' : ℕ}
    (hA : HasTy S k .one [] A (.univ l)) (hA' : HasTy S k .one [] A' (.univ l'))
    (hAA' : RT2 S k A A') (hK : KanP2 S k (semK S k A))
    (ht : HasTy S k .one [] (.hcomp A φ u a) A)
    (ht' : HasTy S k .one [] (.hcomp A' φ' u' a') A)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (hu : TubeD S k A φ u u')
    (ha : RE2 S k A a a') (hb : HcompBnd2 S k A φ u a) (hb' : HcompBnd2 S k A φ' u' a') :
    HasTy S (k + 1) .one [] (Tm.hfill A φ u a) A.dshift ∧
    HasTy S (k + 1) .one [] (Tm.hfill A' φ' u' a') A.dshift ∧
    EqTm S (k + 1) .one [] (Tm.hfill A φ u a) (Tm.hfill A' φ' u' a') A.dshift ∧
    ∀ k' (σ σ' : ISub k' (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
      RE2 S k' (A.dshift.isub σ) ((Tm.hfill A φ u a).isub σ) ((Tm.hfill A' φ' u' a').isub σ') := by
  have hS := sigClosed_of_wfSig hW
  have eA := (Comp2_ty_base hAA').2.2.2.2.2
  have eTop := eqTop hW eA hA
  have eAd : TyEq S (k + 1) A.dshift A'.dshift :=
    .inr ⟨maxLevel, minimal_to_spec_eq (EqTm0.dwk hS (spec_to_minimal_eq hW eTop))⟩
  obtain ⟨l0, ⟨hAt, hs, hut, hat, hbt⟩, -⟩ := gen_hcomp (spec_to_minimal hW ht) rfl
  have htR := ht'.tyConv eA
  obtain ⟨l0', ⟨hAt', hs', hut', hat', hbt'⟩, -⟩ := gen_hcomp (spec_to_minimal hW htR) rfl
  have F := hfill_typed hS hAt hs hut hat hbt
  have F' := hfill_typed hS hAt' hs' hut' hat' hbt'
  have hF := minimal_to_spec F.1
  have hF' := (minimal_to_spec F'.1).tyConv eAd.symm
  have huL : HasTy S (k + 1) (cof .one φ).shift [] u A.dshift := minimal_to_spec hut
  have eAdr := minimal_to_spec_eq (EqTm0.restrict (KubusCore.I.scoped_shift (show (cof .one φ').Scoped k from ⟨trivial, hs'⟩))
    (ent_one _) (EqTm0.symm (EqTm0.dwk hS (spec_to_minimal_eq hW eTop))))
  have huR : HasTy S (k + 1) (cof .one φ).shift [] u' A.dshift :=
    HasTy.restrict (KubusCore.I.scoped_shift ⟨trivial, hs⟩)
      (ent_shift (ent_and_mono (ent_refl _) h12)) (HasTy.conv (minimal_to_spec hut') eAdr)
  have heu := TubeD.eq hW hs hA huL huR hu
  have eA0 : A = A' ∨ ∃ l, EqTm0 S k .one [] A A' (.univ l) := by
    rcases eA with e | ⟨l, e⟩
    · exact .inl e
    · exact .inr ⟨l, spec_to_minimal_eq hW e⟩
  have he := minimal_to_spec_eq (hfill_cong hW F.1 (spec_to_minimal hW hF') eA0
    (spec_to_minimal_eq hW heu) (spec_to_minimal_eq hW (RE2.typed ha).2.2) h12 h21)
  have hu2 := TubeD.toTube2 hW (RT2.refl hW (tyCode_of_univ hW hA) hAA') h12 ht ht' hu
  exact ⟨hF, hF', he, fun k' σ σ' et e0 =>
    hfill_rel_code hW hA hAA' hK hs hs' heu hF hF' he h12 h21 hu2 ha hb hb' σ σ' et e0⟩

end

end Model.Whnf
