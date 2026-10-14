import Model.Whnf.Kan2DataHITInd2

/-!
# Transport of a constructor, including at its boundaries

The transport of a constructor is related to its `transpCon` contractum. Where a boundary holds,
transport first reduces its base to that boundary; `bnd_transp` compares this with the boundary at the
transported arguments. All Kan assumptions are contained in the local data `TC`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k d : ℕ} {D : DataDecl} {PL q : Tm} {φ : I} {c : ℕ} {C : Ctor}
  {X : List Tm} {rs : List I}

namespace TC

/-- A reduct of transport of a constructor, related to the contractum even where a boundary holds. -/
theorem transp_redH (H : TC S k d D PL PL φ φ c C q q X X rs rs)
    (hH : D.isHIT = true) (hyp : HITHyp2 S) :
    ∃ u, Red S (.transp (.data d PL) φ (.con d c q (Tm.ofList X) rs)) u ∧
      EqTm S k .one [] (.transp (.data d PL) φ (.con d c q (Tm.ofList X) rs)) u (.data d (PL.dinst .one)) ∧
      RE2 S k (.data d (PL.dinst .one)) u (tConR d D c C PL φ X rs) := by
  have hW := H.hW
  obtain ⟨eT, -, -, -, hXl, -, -, -, -, -, hPc, -⟩ := H.basic
  obtain ⟨hd1, s1, -, -, -⟩ := H.end_data
  by_cases hf : I.Entails .one φ
  · exact ⟨_, .step (step_transp_face hf) (.refl _), EqTm.transpFace hf H.hty,
      RE2.symm hW s1 (H.tcon_faceH hH hyp hf)⟩
  cases hb : firstBnd C.bnd rs with
  | none =>
    exact ⟨_, .step (step_transp_conR H.hD H.hp H.hC hf hXl (step_con_none H.hD H.hC _ _ hb)) (.refl _),
      eT, H.rel⟩
  | some b =>
    obtain ⟨kb, ψ, hbb, hent⟩ := firstBnd_spec hb
    obtain ⟨-, hbc, hs, -⟩ := ((hW.2 d D H.hD).2.2 c C H.hC).2.1 kb ψ b hbb
    have hd0 : HasTy S k .one [] (.data d (PL.dinst .zero)) (.univ D.level) := by
      have h := HasTy.isubS hW H.hPL (ISub.cons .zero trivial (ISub.id k))
      rwa [show (Tm.data d PL).isub (ISub.cons .zero trivial (ISub.id k)) =
        .data d (PL.isub (ISub.cons .zero trivial (ISub.id k))) from rfl,
        isub_cons_id_of_closed hPc] at h
    obtain ⟨-, ⟨-, -, -, ht⟩, -⟩ := gen_transpF (spec_to_minimal hW H.hty) rfl
    have hct : HasTy S k .one [] (.con d c q (Tm.ofList X) rs) (.data d (PL.dinst .zero)) := minimal_to_spec ht
    have CI := con_inv hW H.hD H.hC hct hd0
    have eqb := EqTm.conBnd H.hD H.hC hbb hent CI.2.2.2.2.2.2.2.2.1 (by rw [toList_ofList]) hct
    rw [toList_ofList] at eqb
    obtain ⟨htb, etb⟩ := transp_rebase hW H.hty eqb
    have BIb : BI S d D c C rs b := fun {_} => BI_top hW H.hD hH hyp H.hC CI.2.2.2.1 hbb hent
    have BT := bnd_transp hW H.hD hH hyp c C H.hC b hs hbc H BIb htb
    obtain ⟨hcO, hO⟩ := H.outs_inst
    have CB := hyp.conBnd H.hD hH H.hC hbb hent hd1 s1 (tOuts_length _ _ _ _ _ _) hcO hO
    have st : step S (.con d c q (Tm.ofList X) rs) = some (Ctor.bndAt b q.toList X rs) := by
      rw [step_con_some H.hD H.hC _ _ hb, toList_ofList]
    exact ⟨_, red_transp_base H.hD H.hp hf (.step st (.refl _)), etb,
      RE2.trans hW s1 BT (RE2.symm hW s1 CB)⟩

/-- Transport of a HIT constructor is related to its contractum at every restriction. -/
theorem transp_relH (H : TC S k d D PL PL φ φ c C q q X X rs rs)
    (hH : D.isHIT = true) (hyp : HITHyp2 S) :
    RE2 S k (.data d (PL.dinst .one)) (.transp (.data d PL) φ (.con d c q (Tm.ofList X) rs))
      (tConR d D c C PL φ X rs) := by
  have hW := H.hW
  obtain ⟨eT, -, -, -, hXl, -, hPl, -, hPlen, -, -, -⟩ := H.basic
  obtain ⟨-, s1, -, -, -⟩ := H.end_data
  refine RE2.expandH hW s1 H.hty (HasTy.eqR eT) fun k' σ => ?_
  obtain ⟨u, hr, he, hu⟩ := (H.isubH hH hyp (forall2_ieq_refl rs) σ).transp_redH hH hyp
  have eR := tConR_isub hW H.hD H.hC (φ := φ) (rs := rs) hPl hPlen hXl σ
  have eA : (Tm.data d (PL.dinst .one)).isub σ = .data d ((PL.isub σ.up).dinst .one) := by
    show Tm.data d ((PL.dinst .one).isub σ) = _; rw [isub_dinst]; rfl
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa only [isub_transp, isub_conT] using hr
  · simpa only [isub_transp, isub_conT, eA] using he
  · rw [eA, eR]; exact hu

end TC

end

end Model.Whnf
