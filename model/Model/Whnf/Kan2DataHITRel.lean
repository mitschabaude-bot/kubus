import Model.Whnf.Kan2DataHITStep

/-!
# Related elements of literal inductive types, in general

The normal forms of related elements at one stage (`DR2At_cases`): constructors (with interval
arguments) with related arguments, or (at higher inductive types) formal compositions with related
bases and tubes.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hP hPP

/-- The normal forms of related elements at one stage of a literal inductive type. -/
theorem DR2At_cases {k3 : ℕ} (ρ' : ISub k3 K) {x x' : Tm}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
      (.data d (P.isub ρ')) x x') :
    (∃ c C qs Z rs qs' Z' rs', D.ctors[c]? = some C ∧ Z.length = C.args.length ∧ Z'.length = C.args.length ∧
      RedE S k3 (.data d (P.isub ρ')) x (.con d c qs (Tm.ofList Z) rs) ∧
      RedE S k3 (.data d (P.isub ρ')) x' (.con d c qs' (Tm.ofList Z') rs') ∧
      rs.length = C.dims ∧ rs'.length = C.dims ∧
      (∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r') ∧
      (∀ r ∈ rs, r.Scoped k3) ∧ (∀ r ∈ rs', r.Scoped k3) ∧
      ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((Z.take i).reverse ++ (P.isub ρ').toList.reverse)) (Z.getD i .abort) (Z'.getD i .abort)) ∨
    (∃ qs ψ u a qs' ψ' u' a', D.isHIT = true ∧
      RedE S k3 (.data d (P.isub ρ')) x (.hcomp (.data d qs) ψ u a) ∧
      RedE S k3 (.data d (P.isub ρ')) x' (.hcomp (.data d qs') ψ' u' a') ∧
      ψ.Scoped k3 ∧ ψ'.Scoped k3 ∧ I.Entails ψ ψ' ∧ I.Entails ψ' ψ ∧
      RE2 S k3 (.data d (P.isub ρ')) a a' ∧
      ∀ k4 (σ : ISub k4 k3) (r : I), r.Scoped k4 → (ival (idEnv k4) (ψ.subst σ.τ)).holds →
        RE2 S k4 (.data d (P.isub (ρ'.comp σ))) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r)) := by
  have hdD := dataD_eq hW hD
  have hTP : IsTyK S k3 (.data d (P.isub ρ')) := ⟨_, .inl (HasTy.isubS hW hP ρ')⟩
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW hTP; rwa [hdD] at this
  have toRE : ∀ {k4 : ℕ} (ρ4 : ISub k4 K) {y y' : Tm},
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k4 ρ4.hom
        (.data d (P.isub ρ4)) y y' → RE2 S k4 (.data d (P.isub ρ4)) y y' := by
    intro k4 ρ4 y y' h
    obtain ⟨he⟩ : Nonempty (EqTm S k4 .one [] _ _ (.data d (P.isub ρ4))) := by cases h with | intro he => exact ⟨he⟩
    exact (RE2_dataLit_iff hW hD hP ρ4).2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, h⟩
  cases hat with
  | @con _ _ _ _ _ ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    have hC' := hdD ▸ hC
    obtain rfl := redT_data_eq (Θ := ΘK S D d K P) hA
    refine .inl ⟨c, C, qs, args, rs, qs', args', rs', hC', hl, hl', ht, ht', hrs, hrs', hreq, hsc, hsc', fun i hi => ?_⟩
    rw [getD_eq_get' (by omega), getD_eq_get' (by omega)]
    cases hri : C.isRec i
    · have := dataP2_RE2 hW hD hP hPP ρ' hC' (by omega) (by omega) hrec hpt (show i < _ by omega)
        (show i < _ by omega) hri
      rwa [hdD] at this
    · rw [argTy_rec_inst hri hPl hplen (by simp; omega)]
      exact toRE ρ' (hrec i (by omega) (by omega) hri)
  | @hcomp _ _ _ _ _ ps qs qs' u u' a a' ψ ψ' hm hm' heq hH' hA hpl ht ht' hs hs' h12 h21 ha hu =>
    obtain rfl := redT_data_eq (Θ := ΘK S D d K P) hA
    refine .inr ⟨qs, ψ, u, a, qs', ψ', u', a', hdD ▸ hH', ht, ht', hs, hs', h12, h21, toRE ρ' ha,
      fun k4 σ r hr hh => ?_⟩
    have h := hu k4 σ r hr hh
    rw [show (Tm.data d (P.isub ρ')).isub σ = .data d (P.isub (ρ'.comp σ)) by
      show Tm.data d ((P.isub ρ').isub σ) = _; rw [Tm.isub_isub], ← ISub.hom_comp] at h
    exact toRE (ρ'.comp σ) h

/-- An element is related to its normal form, when that is related to itself. -/
theorem RE2_whnf {k3 : ℕ} (ρ' : ISub k3 K) {y y' w : Tm} (hy : RE2 S k3 (.data d (P.isub ρ')) y y')
    (hw : RedE S k3 (.data d (P.isub ρ')) y w) (hww : RE2 S k3 (.data d (P.isub ρ')) w w) :
    RE2 S k3 (.data d (P.isub ρ')) w y := by
  have hPρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hyy := RE2.trans hW hPρ hy (RE2.symm hW hPρ hy)
  have hyc := closed_of_ty hW (RE2.typed hy).1
  obtain ⟨-, hdy⟩ := (RE2_dataLit_iff hW hD hP ρ').1 hyy
  obtain ⟨-, hdw⟩ := (RE2_dataLit_iff hW hD hP ρ').1 hww
  refine (RE2_dataLit_iff hW hD hP ρ').2 ⟨⟨(RE2.typed hww).1, (RE2.typed hy).1, hw.2.symm⟩, ?_⟩
  cases hdy with
  | intro _ _ hc hc' =>
    cases hdw with
    | intro _ _ hcw _ =>
      refine .intro hw.2.symm (fun k'' κ => ?_) hcw hc'
      have := hc k3 (ISub.id k3) w (by rw [isub_id_of_closed hyc]; exact hw.1) k'' κ
      rwa [ISub.id_comp] at this

end lit

/-- Tubes related at each point (of each restriction where the face holds). -/
def TubeD (S : Sig) (k : ℕ) (A : Tm) (φ : I) (u u' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' (A.isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r)

theorem TubeD.isub {T u u' : Tm} {φ : I} (h : TubeD S k T φ u u') (σ : ISub k' k) :
    TubeD S k' (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (u'.isub σ.up) := by
  intro k'' ρ r hr hh
  have := h k'' (σ.comp ρ) r hr (by rwa [I_subst_comp])
  rwa [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]

section hitD
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hP hPP

/-- Related formal compositions at a restriction of a literal higher inductive type, at one stage. -/
theorem hit_atD {k1 : ℕ} (ρ : ISub k1 K) {Q1 Q2 u u' a a' : Tm} {φ φ' : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k1 .one [] (.hcomp (.data d Q1) φ u a) (.data d (P.isub ρ)))
    (hty' : HasTy S k1 .one [] (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (heq : EqTm S k1 .one [] (.hcomp (.data d Q1) φ u a) (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : TubeD S k1 (.data d (P.isub ρ)) φ u u')
    (haa : RE2 S k1 (.data d (P.isub ρ)) a a') :
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
  have h1 := htube k' σ r hr hh
  rw [show (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) by
    show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]] at h1 ⊢
  have := ((RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1).2
  rwa [ISub.hom_comp] at this

/-- Related compositions at a restriction of a literal higher inductive type, at all further stages. -/
theorem hit_stageD {k1 : ℕ} (ρ : ISub k1 K) {Q1 Q2 u u' a a' : Tm} {φ φ' : I}
    (hty : HasTy S k1 .one [] (.hcomp (.data d Q1) φ u a) (.data d (P.isub ρ)))
    (hty' : HasTy S k1 .one [] (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (heq : EqTm S k1 .one [] (.hcomp (.data d Q1) φ u a) (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : TubeD S k1 (.data d (P.isub ρ)) φ u u')
    (haa : RE2 S k1 (.data d (P.isub ρ)) a a') (k' : ℕ) (σ : ISub k' k1) :
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
  rw [eP] at htyσ htyσ' heqσ htubeσ haaσ ⊢
  rw [← ISub.hom_comp]
  simp only [isub_hcomp] at htyσ htyσ' heqσ ⊢
  by_cases hf : I.Entails .one (φ.subst σ.τ)
  · -- the face holds: the tube's ends
    have hf' : I.Entails .one (φ'.subst σ.τ) := ent_trans hf (ent_subst h12 _)
    have hh := (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 hf
    have h1 := htube k' σ .one trivial hh
    rw [eP] at h1
    have hat := DR2.at_id hW (Θ := ΘK S D d K P) ((RE2_dataLit_iff hW hD hP (ρ.comp σ)).1 h1).2
    refine DR2At.expandL hW (DR2At.expandR hW hat (.step (step_hcomp_face hf') (.refl _))
      (EqTm.hcompFace hf' htyσ')) (.step (step_hcomp_face hf) (.refl _)) (EqTm.hcompFace hf htyσ)
  · exact hit_atD hW hD hH hP hPP (ρ.comp σ) hf htyσ htyσ' heqσ (ent_subst h12 _) (ent_subst h21 _) htubeσ haaσ

/-- The coherence clause of a composition at a restriction of a literal higher inductive type: its
normal forms, restricted, are related to its restrictions. -/
theorem hit_cohD {k1 : ℕ} (ρ : ISub k1 K) {Q1 u a : Tm} {φ : I}
    (hty : HasTy S k1 .one [] (.hcomp (.data d Q1) φ u a) (.data d (P.isub ρ)))
    (htube : TubeD S k1 (.data d (P.isub ρ)) φ u u) (haa : RE2 S k1 (.data d (P.isub ρ)) a a) :
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
    have h1 := htube k' σ .one trivial hh
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
    have := hit_stageD hW hD hH hP hPP ρ hty hty (EqTm.refl hty) (ent_refl _) (ent_refl _) htube haa k'' (σ.comp ρ')
    rw [isub_hcomp] at this
    simp only [isub_hcomp, Tm.isub_isub, ← ISub.up_comp, ← hτ0]
    exact this

/-- Related formal compositions at a restriction of a literal higher inductive type, from tubes related at
each point and related bases. -/
theorem hcomp_relD {k1 : ℕ} (ρ : ISub k1 K) {Q1 Q2 u u' a a' : Tm} {φ φ' : I}
    (hty : HasTy S k1 .one [] (.hcomp (.data d Q1) φ u a) (.data d (P.isub ρ)))
    (hty' : HasTy S k1 .one [] (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (heq : EqTm S k1 .one [] (.hcomp (.data d Q1) φ u a) (.hcomp (.data d Q2) φ' u' a') (.data d (P.isub ρ)))
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : TubeD S k1 (.data d (P.isub ρ)) φ u u')
    (tS : TubeD S k1 (.data d (P.isub ρ)) φ u u) (tS' : TubeD S k1 (.data d (P.isub ρ)) φ' u' u')
    (haa : RE2 S k1 (.data d (P.isub ρ)) a a') :
    RE2 S k1 (.data d (P.isub ρ)) (.hcomp (.data d Q1) φ u a) (.hcomp (.data d Q2) φ' u' a') := by
  have hA : RT2 S k1 (.data d (P.isub ρ)) (.data d (P.isub ρ)) := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ
  exact (RE2_dataLit_iff hW hD hP ρ).2 ⟨⟨hty, hty', heq⟩, .intro heq
    (fun k' σ => hit_stageD hW hD hH hP hPP ρ hty hty' heq h12 h21 htube haa k' σ)
    (hit_cohD hW hD hH hP hPP ρ hty tS (RE2.trans hW hA haa (RE2.symm hW hA haa)))
    (hit_cohD hW hD hH hP hPP ρ hty' tS' (RE2.trans hW hA (RE2.symm hW hA haa) haa))⟩

end hitD

end

end Model.Whnf
