import Model.Whnf.Kan2DataGen

/-!
# The binary composition at higher inductive types

At a higher inductive type, a composition whose face does not hold is a formal composition (a weak-head
normal form), related by the `hcomp` clause of the relation (`hit_stage`); where the face holds, it
reduces to the tube's end. This gives composition at the literal types (`kanH2_litHIT`), and through
`kanH2_data_gen` at all types whose normal form is a higher inductive type (`kanH2_dataHIT`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section dr
variable (hW : WfSig S) {k0 : ℕ} {Θ : SData m} {f : Hom k0 m} {d : ℕ} {D : DataDecl} {g : Hom k k0}
include hW

/-- A related element of an inductive type at a stage, through a reduct on the left. -/
theorem DR2At.expandL {A t t' u : Tm} (h : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A u t')
    (r : Red S t u) (e : EqTm S k .one [] t u A) : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t t' := by
  cases h with
  | con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    exact .con (by unfold dataMem at hm ⊢; rwa [semK_eq hW e]) hm' (e.trans heq) hC hA hpl
      (RedE.of_red r e ht) ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt
  | hcomp hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu hb hb' =>
    exact .hcomp (by unfold dataMem at hm ⊢; rwa [semK_eq hW e]) hm' (e.trans heq) hH hA hpl
      (RedE.of_red r e ht) ht' hs hs' h12 h21 ha hu hb hb'

end dr

/-- Boundary coherence persists under restriction. -/
theorem HcompBnd2.isub {A u a : Tm} {φ : I} (h : HcompBnd2 S k A φ u a) (σ : ISub k' k) :
    HcompBnd2 S k' (A.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ) := by
  intro k'' ρ hh
  have := h k'' (σ.comp ρ) (by rwa [I_subst_comp])
  rwa [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]

section hit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hP hPP

/-- Related formal compositions at a restriction of a literal higher inductive type, at one stage. -/
theorem hit_at {k1 : ℕ} (ρ : ISub k1 K) {Q1 Q2 u u' a a' : Tm} {φ φ' : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k1 .one [] (.hcomp (.data d Q1) φ u a) (.data d (P.isub ρ)))
    (hty' : HasTy S k1 .one [] (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (heq : EqTm S k1 .one [] (.hcomp (.data d Q1) φ u a) (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u')
    (haa : RE2 S k1 (.data d (P.isub ρ)) a a')
    (hb : HcompBnd2 S k1 (.data d (P.isub ρ)) φ u a)
    (hb' : HcompBnd2 S k1 (.data d (P.isub ρ)) φ' u' a') :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 ρ.hom
      (.data d (P.isub ρ)) (.hcomp (.data d Q1) φ u a) (.hcomp (.data d Q2) φ' u' a') := by
  obtain ⟨-, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨-, ⟨-, hφs', -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl
  have hdD := dataD_eq hW hD
  have hn' : ¬ I.Entails .one φ' := fun h => hn (ent_trans h h21)
  have hpl := (dataLit_rel hW hD hP hPP ρ).2.2.2.2.2.1
  refine .hcomp (dataMem_lit hW hD hP ρ hty) (dataMem_lit hW hD hP ρ hty') heq (hdD ▸ hH)
    ⟨redW_self (step_data d _), TyEq.refl _⟩ hpl ⟨redW_self (step_hcomp_HIT hD hH hn), EqTm.refl hty⟩
    ⟨redW_self (step_hcomp_HIT hD hH hn'), EqTm.refl hty'⟩ hφs hφs' h12 h21
    ((RE2_dataLit_iff hW hD hP ρ).1 haa).2 (fun k' σ r hr hh => ?_)
    (fun k' σ hh => ?_) (fun k' σ hh => ?_)
  · have h1 := htube k' σ r r hr hr (I_eq_refl _) hh
    rw [show (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) by
      show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]] at h1 ⊢
    have := ((RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1).2
    rwa [ISub.hom_comp] at this
  · have h1 := hb k' σ hh
    rw [show (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) by
      show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]] at h1 ⊢
    have := ((RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1).2
    rwa [ISub.hom_comp] at this
  · have h1 := hb' k' σ hh
    rw [show (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) by
      show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]] at h1 ⊢
    have := ((RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1).2
    rwa [ISub.hom_comp] at this

/-- Related compositions at a restriction of a literal higher inductive type, at all further stages. -/
theorem hit_stage {k1 : ℕ} (ρ : ISub k1 K) {Q1 Q2 u u' a a' : Tm} {φ φ' : I}
    (hty : HasTy S k1 .one [] (.hcomp (.data d Q1) φ u a) (.data d (P.isub ρ)))
    (hty' : HasTy S k1 .one [] (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (heq : EqTm S k1 .one [] (.hcomp (.data d Q1) φ u a) (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u')
    (haa : RE2 S k1 (.data d (P.isub ρ)) a a')
    (hb : HcompBnd2 S k1 (.data d (P.isub ρ)) φ u a)
    (hb' : HcompBnd2 S k1 (.data d (P.isub ρ)) φ' u' a') (k' : ℕ) (σ : ISub k' k1) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k'
      (ρ.hom.comp σ.hom) ((Tm.data d (P.isub ρ)).isub σ) ((Tm.hcomp (.data d Q1) φ u a).isub σ)
      ((Tm.hcomp (.data d Q2) φ' u' a').isub σ) := by
  obtain ⟨-, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have eP : (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) := by
    show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]
  have htyσ := HasTy.isubS hW hty σ
  have htyσ' := HasTy.isubS hW hty' σ
  have heqσ := EqTm.isubS hW heq σ
  have htubeσ := htube.isub σ
  have haaσ := RE2.isub hW haa σ
  have hbσ := hb.isub σ
  have hbσ' := hb'.isub σ
  rw [eP] at htyσ htyσ' heqσ htubeσ haaσ hbσ hbσ' ⊢
  rw [← ISub.hom_comp]
  simp only [isub_hcomp] at htyσ htyσ' heqσ ⊢
  by_cases hf : I.Entails .one (φ.subst σ.τ)
  · -- the face holds: the tube's ends
    have hf' : I.Entails .one (φ'.subst σ.τ) := ent_trans hf (ent_subst h12 _)
    have hh := (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 hf
    have h1 := htube k' σ .one .one trivial trivial (I_eq_refl _) hh
    rw [eP] at h1
    have hat := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1).2
    refine DR2At.expandL hW (DR2At.expandR hW hat (.step (step_hcomp_face hf') (.refl _))
      (EqTm.hcompFace hf' htyσ')) (.step (step_hcomp_face hf) (.refl _)) (EqTm.hcompFace hf htyσ)
  · exact hit_at hW hD hH hP hPP (ρ.comp σ) hf htyσ htyσ' heqσ (ent_subst h12 _) (ent_subst h21 _) htubeσ haaσ hbσ hbσ'

/-- The coherence clause of a composition at a restriction of a literal higher inductive type: its
normal forms, restricted, are related to its restrictions. -/
theorem hit_coh {k1 : ℕ} (ρ : ISub k1 K) {Q1 u a : Tm} {φ : I}
    (hty : HasTy S k1 .one [] (.hcomp (.data d Q1) φ u a) (.data d (P.isub ρ)))
    (htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u) (haa : RE2 S k1 (.data d (P.isub ρ)) a a)
    (hb : HcompBnd2 S k1 (.data d (P.isub ρ)) φ u a) :
    ∀ k' (σ : ISub k' k1) w, RedW S ((Tm.hcomp (.data d Q1) φ u a).isub σ) w → ∀ k'' (ρ' : ISub k'' k'),
      DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k''
        (ρ.hom.comp (σ.comp ρ').hom) ((Tm.data d (P.isub ρ)).isub (σ.comp ρ')) (w.isub ρ')
        ((Tm.hcomp (.data d Q1) φ u a).isub (σ.comp ρ')) := by
  intro k' σ w hw k'' ρ'
  obtain ⟨-, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hτ0 : ∀ {x : I}, x.subst (σ.comp ρ').τ = (x.subst σ.τ).subst ρ'.τ := fun {x} => I_subst_comp x σ ρ'
  have htyσ := HasTy.isubS hW hty σ
  simp only [isub_hcomp] at htyσ hw
  by_cases hf : I.Entails .one (φ.subst σ.τ)
  · -- the face holds: the normal form is that of the tube's end
    have hw1 := red_redW (.step (step_hcomp_face hf) (.refl _)) hw
    have hh := (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 hf
    have h1 := htube k' σ .one .one trivial trivial (I_eq_refl _) hh
    have eP : (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) := by
      show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]
    rw [eP] at h1
    have hu1c := closed_of_ty hW (RE2.typed h1).1
    obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1
    cases hdr with
    | intro he hh0 hc hc' =>
      have h2 := hc k' (ISub.id k') w (by rw [isub_id_of_closed hu1c]; exact hw1) k'' ρ'
      rw [ISub.id_comp] at h2
      have hf2 : I.Entails .one (φ.subst (σ.comp ρ').τ) := by rw [hτ0]; exact ent_one_subst hf ρ'.τ
      have htyτ := HasTy.isubS hW hty (σ.comp ρ')
      simp only [isub_hcomp] at htyτ ⊢
      have e1 : ((u.isub σ.up).dinst .one).isub ρ' = (u.isub (σ.comp ρ').up).dinst .one := by
        rw [isub_dinst, Tm.isub_isub, ← ISub.up_comp]; rfl
      rw [e1, show (Tm.data d (P.isub (ρ.comp σ))).isub ρ' = (Tm.data d (P.isub ρ)).isub (σ.comp ρ') by
        show Tm.data d ((P.isub (ρ.comp σ)).isub ρ') = Tm.data d ((P.isub ρ).isub (σ.comp ρ'))
        rw [Tm.isub_isub, Tm.isub_isub, ISub.comp_assoc]] at h2
      simp only [ISub.hom_comp, Hom.comp_assoc] at h2 ⊢
      exact DR2At.expandR hW h2 (.step (step_hcomp_face hf2) (.refl _)) (EqTm.hcompFace hf2 htyτ)
  · -- the face does not hold: the composition is normal
    obtain rfl := RedW.unique hw (redW_self (step_hcomp_HIT hD hH hf))
    have := hit_stage hW hD hH hP hPP ρ hty hty (EqTm.refl hty) (ent_refl _) (ent_refl _) htube haa hb hb k'' (σ.comp ρ')
    rw [isub_hcomp] at this
    simp only [isub_hcomp, Tm.isub_isub, ← ISub.up_comp, ← hτ0]
    exact this

/-- Composition at a restriction of a literal higher inductive type. -/
theorem kanH2_litHIT {k1 : ℕ} (ρ : ISub k1 K) (Q1 Q2 a a' : Tm) :
    HC2 S k1 (.data d (P.isub ρ)) (.data d Q1) (.data d Q2) a a' := by
  intro φ φ' u u' hty hty' heq hteq h12 h21 htube haa hbd hbd'
  obtain ⟨-, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hAσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), RT2 S k3 ((Tm.data d (P.isub ρ)).isub σ) ((Tm.data d (P.isub ρ)).isub σ) :=
    fun σ => RT2.isub hW (tyCode_of_univ hW (HasTy.isubS hW hP ρ)) (RT2.isub hW (tyCode_of_univ hW hP) hPP ρ) σ
  have hA : RT2 S k1 (.data d (P.isub ρ)) (.data d (P.isub ρ)) := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
  have tS : Tube2 S k1 (.data d (P.isub ρ)) φ u u := fun k3 σ r r' hr hr' hE hh =>
    RE2.trans hW (hAσ σ) (htube k3 σ r r' hr hr' hE hh) (RE2.symm hW (hAσ σ) (htube k3 σ r' r' hr' hr' (I_eq_refl _) hh))
  have tS' : Tube2 S k1 (.data d (P.isub ρ)) φ' u' u' := fun k3 σ r r' hr hr' hE hh' => by
    have hh : (ival (idEnv k3) (φ.subst σ.τ)).holds := by
      have hφs' := (gen_hcomp (spec_to_minimal hW hty') rfl).choose_spec.1.2.1
      rw [holds_iff_entails (I.scoped_subst hφs σ.sc)]
      exact ent_trans ((holds_iff_entails (I.scoped_subst hφs' σ.sc)).1 hh') (ent_subst h21 σ.τ)
    exact RE2.trans hW (hAσ σ) (RE2.symm hW (hAσ σ) (htube k3 σ r r hr hr (I_eq_refl _) hh))
      (htube k3 σ r r' hr hr' hE hh)
  have hbl : HcompBnd2 S k1 (.data d (P.isub ρ)) φ u a := fun k3 σ hh =>
    RE2.trans hW (hAσ σ) (hbd k3 σ hh) (RE2.symm hW (hAσ σ) (RE2.isub hW haa σ))
  have hbr : HcompBnd2 S k1 (.data d (P.isub ρ)) φ' u' a' := by
    intro k3 σ hh'
    have hφs' := (gen_hcomp (spec_to_minimal hW hty') rfl).choose_spec.1.2.1
    have hh : (ival (idEnv k3) (φ.subst σ.τ)).holds := by
      rw [holds_iff_entails (I.scoped_subst hφs σ.sc)]
      exact ent_trans ((holds_iff_entails (I.scoped_subst hφs' σ.sc)).1 hh') (ent_subst h21 σ.τ)
    exact RE2.trans hW (hAσ σ) (RE2.symm hW (hAσ σ) (hbd' k3 σ hh)) (RE2.isub hW haa σ)
  refine (RE2_dataLit_iff hW hD hP ρ).2 ⟨⟨hty, hty', heq⟩, .intro heq
    (fun k' σ => hit_stage hW hD hH hP hPP ρ hty hty' heq h12 h21 htube haa hbl hbr k' σ)
    (hit_coh hW hD hH hP hPP ρ hty tS (RE2.trans hW hA haa (RE2.symm hW hA haa)) hbl)
    (hit_coh hW hD hH hP hPP ρ hty' tS' (RE2.trans hW hA (RE2.symm hW hA haa) haa) hbr)⟩

end hit

section gen
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
include hW hD hH

/-- Composition at a pair of related types whose normal forms are a higher inductive type. -/
theorem kanH2_dataHIT {T T' ps : Tm} (hTT : RT2 S k T T') (hR : RedT S k T (.data d ps)) : KanH2 S k T T' :=
  kanH2_data_gen hW hD hTT hR fun k1 _ P1 Q1 hP1 _ hPP _ a a' => by
    have h := kanH2_litHIT hW hD hH hP1 hPP (ISub.id k1) P1 Q1 a a'
    have hPc : P1.closedB 0 k1 = true := by have := closed_of_ty hW hP1; simpa [Tm.closedB] using this
    rwa [isub_id_of_closed hPc] at h

end gen

end

end Model.Whnf
