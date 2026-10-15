import Model.Whnf.Valid2ElimH31

/-! # The binary logical relation of higher inductive eliminations -/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {K : ℕ} (hW : WfSig S) {d : ℕ} {D : DataDecl}
    (hD : S[d]? = some (.data D)) (hH : D.isHIT = true) (hyp : HITHyp2 S (d + 1))
    {P M bs : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P)) (HL : ElimRelH S d D K P M bs P M bs)
    (HB : ElimBndRel2 S d D K P M bs)
include hW hD hH hyp hP hPP HL HB

/-- The introduction case of the raw induction, from head stages at all restrictions. -/
theorem elimMotive_introH {k : ℕ} {g : Hom k K} {A x x' : Tm}
    (hdr : DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k g A x x')
    (ih : ∀ k' (σ : ISub k' k), ElimStageH S d D K P M bs k' (g.comp σ.hom)
      (A.isub σ) (x.isub σ) (x'.isub σ))
    (ihc : ∀ k' (σ : ISub k' k) W, RedW S (x.isub σ) W → ∀ k'' (τ : ISub k'' k'),
      ElimStageH S d D K P M bs k'' (g.comp (σ.comp τ).hom) (A.isub (σ.comp τ))
        (W.isub τ) (x.isub (σ.comp τ))) :
    ElimMotiveH S d D K P M bs k g A x x' := by
  have run : ∀ (ρ : ISub k K), g = ρ.hom → A = .data d (P.isub ρ) →
      ElimNormH S d D K P M bs k ρ x ∧
      ∀ Q M' bs', ElimRelH S d D K P M bs Q M' bs' →
        RE2 S k ((M.isub ρ).inst x) (.elim d (P.isub ρ) (M.isub ρ) (bs.isub ρ) x)
          (.elim d (Q.isub ρ) (M'.isub ρ) (bs'.isub ρ) x') := by
    intro ρ hg hAe
    subst hg hAe
    have hx := DR2_lit_toRE2 hW hD hP ρ hdr
    have I : ∀ k' (σ : ISub k' k), ElimStageH S d D K P M bs k' (ρ.comp σ).hom
        (.data d (P.isub (ρ.comp σ))) (x.isub σ) (x'.isub σ) := by
      intro k' σ
      simpa only [ISub.hom_comp, data_isub_comp] using ih k' σ
    have C : ∀ k' (σ : ISub k' k) W, RedW S (x.isub σ) W → ∀ k'' (τ : ISub k'' k'),
        ElimStageH S d D K P M bs k'' ((ρ.comp σ).comp τ).hom
          (.data d (P.isub ((ρ.comp σ).comp τ))) (W.isub τ) (x.isub (σ.comp τ)) := by
      intro k' σ W hw k'' τ
      simpa only [ISub.hom_comp, data_isub_comp, ISub.comp_assoc, Hom.comp_assoc] using ihc k' σ W hw k'' τ
    exact ⟨elimNorm_introH hW hD hH hyp hP hPP HL hx I C,
      fun Q M' bs' H => elimPair_introH hW hD hH hyp hP hPP HL hx I C H⟩
  exact ⟨fun ρ hg hAe => (run ρ hg hAe).2, fun ρ hg hAe => (run ρ hg hAe).1⟩

/-- Eliminations of related HIT elements are related, by induction on their binary relation. -/
theorem elim_DR2H : ∀ {k : ℕ} {g : Hom k K} {A x x' : Tm},
    DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K))
      (dataP2 S (ΘK S D d K P) (Hom.id K)) k g A x x' →
    ElimMotiveH S d D K P M bs k g A x x' := by
  intro k g A x x' h
  refine DR2.rec (motive_1 := fun k g A x x' _ => ElimMotiveH S d D K P M bs k g A x x')
    (motive_2 := fun k g A x x' _ => ElimStageH S d D K P M bs k g A x x') ?_ ?_ ?_ h
  · intro k g A x x' he hst hc hc' ih ihc _
    exact elimMotive_introH hW hD hH hyp hP hPP HL HB (.intro he hst hc hc') ih ihc
  · intro k g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec
    exact elimStage_conH hW hD hP hPP hH hyp HL HB
      (.con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt)
      hC hA ht ht' hl hl' ihrec
  · intro k g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH' hA hpl ht ht' hs hs' h12 h21 ha hu hb hb' iha ihu ihb _
    exact elimStage_hcompH hW hD hP hH hPP HL hA ht ht' h12 h21 ha hu hb hb' iha ihu ihb

end

end Model.Whnf
