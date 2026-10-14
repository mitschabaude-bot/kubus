import Model.Whnf.Kan2SigmaT

/-!
# The binary composition at Σ-types
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

theorem step_hcomp_sigma {A B u a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.hcomp (.sigma A B) φ u a) = some (Tm.hcompSigma A B φ u a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

variable (hW : WfSig S)
include hW

/-- The first projection of a composition in a Σ-type whose face does not hold. -/
theorem fst_hcomp_sigma {T A2 B2 u a0 : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : RedT S k T (.sigma A2 B2)) :
    Red S (.fst (.hcomp T φ u a0)) (.hcomp A2 φ (.fst u) (.fst a0)) ∧
    EqTm S k .one [] (.fst (.hcomp T φ u a0)) (.hcomp A2 φ (.fst u) (.fst a0)) A2 := by
  have e1 := eq_hcomp_ty hW hty hR.2
  have e2 := EqTm.hcompSigma (HasTy.eqR e1)
  have e3 := (e1.trans e2).tyConv hR.2
  have e4 := EqTm.fst e3
  simp only [Tm.hcompSigma] at e4
  have e5 := EqTm.fstBeta (HasTy.eqR e4)
  refine ⟨(red_fst ((red_hcomp_ty hn hR.1.1).trans (.step (step_hcomp_sigma hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rfl

/-- The second projection of a composition in a Σ-type whose face does not hold. -/
theorem snd_hcomp_sigma {T A2 B2 u a0 : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : RedT S k T (.sigma A2 B2)) :
    Red S (.snd (.hcomp T φ u a0))
      (Tm.comp (B2.dshift.inst (Tm.hfill A2 φ (.fst u) (.fst a0))) φ (.snd u) (.snd a0)) ∧
    EqTm S k .one [] (.snd (.hcomp T φ u a0))
      (Tm.comp (B2.dshift.inst (Tm.hfill A2 φ (.fst u) (.fst a0))) φ (.snd u) (.snd a0))
      (B2.inst (.fst (.hcomp T φ u a0))) := by
  have e1 := eq_hcomp_ty hW hty hR.2
  have e2 := EqTm.hcompSigma (HasTy.eqR e1)
  have e3 := (e1.trans e2).tyConv hR.2
  have e4 := EqTm.snd e3
  simp only [Tm.hcompSigma] at e4
  have e5 := EqTm.sndBeta (HasTy.eqR e4)
  refine ⟨(red_snd ((red_hcomp_ty hn hR.1.1).trans (.step (step_hcomp_sigma hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rfl


/-- The first projections of compositions in Σ-types. -/
theorem kanH2_sigma_fst {T T' : Tm} (hP : SigmaStr S k T T')
    (hIH : ∀ k' (ρ : ISub k' k) A1 B1, RedT S k' (T.isub ρ) (.sigma A1 B1) →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' (A1.isub ρ') X' → KanH2 S k'' (A1.isub ρ') X')
    {φ φ' : I} {u u' a0 a0' : Tm} (hty : HasTy S k .one [] (.hcomp T φ u a0) T)
    (hty' : HasTy S k .one [] (.hcomp T' φ' u' a0') T)
    (heq : EqTm S k .one [] (.hcomp T φ u a0) (.hcomp T' φ' u' a0') T)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k T φ u u') (ha0 : RE2 S k T a0 a0')
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) ((u.isub σ.up).dinst .zero) (a0'.isub σ))
    (hbd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (a0.isub σ) ((u'.isub σ.up).dinst .zero))
    {A1 B1 : Tm} (hR : RedT S k T (.sigma A1 B1)) :
    RE2 S k A1 (.fst (.hcomp T φ u a0)) (.fst (.hcomp T' φ' u' a0')) := by
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hTK : IsTyK S k T := isTyK_of_ty hW hty
  have hTc : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTK)
  choose A2 B2 A2' B2' hw using hP.whnf
  have hR0 : RedT S k (T.isub (ISub.id k)) (.sigma A1 B1) := by rw [hTc]; exact hR
  have hA1e : A2 k (ISub.id k) = A1 := by
    have := RedW.unique (hw k (ISub.id k)).1.1 hR0.1; injection this
  have hXA : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' (A2 k' ρ)) := fun k' ρ => by
    obtain ⟨l, h⟩ := sigmaW_typed hW (hTK.isub hW ρ) (hw k' ρ).1
    exact tyCode_of_univ hW (HasTy.sigmaDom h)
  have hCY : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A2 k' ρ) := by
    intro k' ρ
    rw [← hA1e]
    exact (hP.coh k (ISub.id k) k' ρ _ _ _ _ (hw k (ISub.id k)).1 (by rw [ISub.id_comp]; exact (hw k' ρ).1)).1
  have hX : TyCode k (semK S k A1) := by rw [← hA1e]; exact hXA _ _
  have hXY : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' (A1.isub ρ)) := fun k' ρ =>
    RT2.tyCode_l hW (hCY k' ρ) (hXA _ _)
  have hYY : RT2 S k A1 A1 := by
    have := (hw k (ISub.id k)).2.2.1; rw [hA1e] at this; exact RT2.refl hW hX this
  have hel : ∀ k' (ρ : ISub k' k) f f', RE2 S k' (T.isub ρ) f f' →
      RE2 S k' (A1.isub ρ) (.fst f) (.fst f') := fun k' ρ f f' h =>
    RE2.conv' hW (hCY k' ρ) (hP.elim k' ρ _ _ f f' (hw k' ρ).1 h).1 (hXY k' ρ)
  have hcoh : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'), RT2 S k'' ((A2 k' ρ).isub ρ') (A2 k'' (ρ.comp ρ')) :=
    fun k' ρ k'' ρ' => (hP.coh k' ρ k'' ρ' _ _ _ _ (hw k' ρ).1 (hw k'' (ρ.comp ρ')).1).1
  have hE0 : EqTm S k .one [] (.fst (.hcomp T φ u a0)) (.fst (.hcomp T' φ' u' a0')) A1 :=
    EqTm.fst (heq.tyConv hR.2)
  have hfst_up : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I),
      ((Tm.fst (u.isub ρ.up)).isub θ.up).dinst x = .fst ((u.isub (ρ.comp θ).up).dinst x) := by
    intro k' ρ k3 θ x
    show Tm.fst (((u.isub ρ.up).isub θ.up).dinst x) = _
    rw [Tm.isub_isub, ← ISub.up_comp]
  have hfst_up' : ∀ k' (ρ : ISub k' k) k3 (θ : ISub k3 k') (x : I),
      ((Tm.fst (u'.isub ρ.up)).isub θ.up).dinst x = .fst ((u'.isub (ρ.comp θ).up).dinst x) := by
    intro k' ρ k3 θ x
    show Tm.fst (((u'.isub ρ.up).isub θ.up).dinst x) = _
    rw [Tm.isub_isub, ← ISub.up_comp]
  have H := kanH2_elim_core hW hφs (fun k' ρ x => .fst x) (fun k' ρ x => .fst x)
    (fun k' ρ => A2 k' ρ) (fun k' ρ => A2' k' ρ)
    (fun k' ρ => .fst (u.isub ρ.up)) (fun k' ρ => .fst (u'.isub ρ.up))
    (fun k' ρ => .fst (a0.isub ρ)) (fun k' ρ => .fst (a0'.isub ρ))
    (fun k' ρ => φ.subst ρ.τ) (fun k' ρ => φ'.subst ρ.τ)
    hX hYY (HasTy.fst (hty.tyConv hR.2)) (HasTy.eqR hE0) hE0
    (fun k' ρ k'' ρ' x => rfl) (fun k' ρ k'' ρ' x => rfl)
    (fun k' ρ => ?_) (fun k' ρ => ?_) hel
    (fun k' ρ k'' ρ' hf2 => by
      show I.Entails .one ((φ.subst ρ.τ).subst ρ'.τ); rw [← I_subst_comp]; exact hf2)
    (fun k' ρ k'' ρ' _ => by
      show I.Entails ((φ.subst ρ.τ).subst ρ'.τ) (φ'.subst (ρ.comp ρ').τ) ∧
        I.Entails (φ'.subst (ρ.comp ρ').τ) ((φ.subst ρ.τ).subst ρ'.τ)
      rw [← I_subst_comp]; exact ⟨ent_subst h12 _, ent_subst h21 _⟩)
    (fun k' ρ k'' ρ' _ hf2 => by
      show RE2 S k'' _ (((Tm.fst (u.isub ρ.up)).isub ρ'.up).dinst .one) _
      rw [hfst_up]
      exact hel k'' (ρ.comp ρ') _ _ (htube k'' (ρ.comp ρ') .one .one trivial trivial (I_eq_refl _)
        ((holds_iff_entails (I.scoped_subst hφs (ρ.comp ρ').sc)).2 hf2)))
    (fun k' ρ k'' ρ' _ k3 σ3 x x' hx hx' hEx hh => by
      show RE2 S k3 _ ((((Tm.fst (u.isub ρ.up)).isub ρ'.up).isub σ3.up).dinst x)
        (((Tm.fst (u'.isub (ρ.comp ρ').up)).isub σ3.up).dinst x')
      rw [show (((Tm.fst (u.isub ρ.up)).isub ρ'.up).isub σ3.up) = (Tm.fst (u.isub ρ.up)).isub (ρ'.comp σ3).up by
        rw [Tm.isub_isub, ← ISub.up_comp], hfst_up, hfst_up', Tm.isub_isub, ISub.comp_assoc]
      refine hel k3 _ _ _ (htube k3 _ x x' hx hx' hEx ?_)
      rw [I_subst_comp, I_subst_comp]; exact hh)
    (fun k' ρ k'' ρ' _ => by
      show RE2 S k'' _ (.fst ((a0.isub ρ).isub ρ')) _
      rw [Tm.isub_isub]; exact hel k'' (ρ.comp ρ') _ _ (RE2.isub hW ha0 _))
    (fun k' ρ k'' ρ' _ k3 σ3 hh => by
      show RE2 S k3 _ ((((Tm.fst (u.isub ρ.up)).isub ρ'.up).isub σ3.up).dinst .zero)
        (.fst ((a0'.isub (ρ.comp ρ')).isub σ3))
      rw [show (((Tm.fst (u.isub ρ.up)).isub ρ'.up).isub σ3.up) = (Tm.fst (u.isub ρ.up)).isub (ρ'.comp σ3).up by
        rw [Tm.isub_isub, ← ISub.up_comp], hfst_up, Tm.isub_isub, Tm.isub_isub, ISub.comp_assoc]
      refine hel k3 _ _ _ (hbd k3 _ ?_)
      rw [I_subst_comp, I_subst_comp]; exact hh)
    (fun k' ρ k'' ρ' _ k3 σ3 hh => by
      show RE2 S k3 _ (.fst (((a0.isub ρ).isub ρ').isub σ3))
        (((Tm.fst (u'.isub (ρ.comp ρ').up)).isub σ3.up).dinst .zero)
      rw [hfst_up', Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ISub.comp_assoc]
      refine hel k3 _ _ _ (hbd' k3 _ ?_)
      rw [I_subst_comp, I_subst_comp]; exact hh)
    (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' _ => ?_) h12 h21 htube
  · exact H
  · have hρ : HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (T.isub ρ) :=
      HasTy.isubS hW hty ρ
    have e := TyEq.symm (Comp2_ty_base (hCY k' ρ)).2.2.2.2.2
    have eT : TyEq S k' (T.isub ρ) (.sigma (A1.isub ρ) (B1.isub ρ)) := by
      have := hR.2.isub hW ρ; rwa [isub_sigma] at this
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · exact ⟨red_fst (.step (step_hcomp_face hf) (.refl _)), EqTm.fst ((EqTm.hcompFace hf hρ).tyConv eT)⟩
    · obtain ⟨a, b⟩ := fst_hcomp_sigma hW hf hρ (hw k' ρ).1
      exact ⟨a, b.tyConv e⟩
  · have hρ : HasTy S k' .one [] (.hcomp (T'.isub ρ) (φ'.subst ρ.τ) (u'.isub ρ.up) (a0'.isub ρ)) (T'.isub ρ) :=
      (HasTy.isubS hW hty' ρ).tyConv (hP.tyEq.isub hW ρ)
    have eT : TyEq S k' (T'.isub ρ) (.sigma (A1.isub ρ) (B1.isub ρ)) := by
      have := (TyEq.trans hW (TyEq.symm hP.tyEq) hR.2).isub hW ρ; rwa [isub_sigma] at this
    have e := TyEq.trans hW (TyEq.symm (Comp2_ty_base (hw k' ρ).2.2.1).2.2.2.2.2)
      (TyEq.symm (Comp2_ty_base (hCY k' ρ)).2.2.2.2.2)
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · exact ⟨red_fst (.step (step_hcomp_face hf) (.refl _)), EqTm.fst ((EqTm.hcompFace hf hρ).tyConv eT)⟩
    · obtain ⟨a, b⟩ := fst_hcomp_sigma hW hf hρ (hw k' ρ).2.1
      exact ⟨a, b.tyConv e⟩
  · have c1 := hcoh k' ρ k'' ρ'
    exact RT2.trans hW (RT2.tyCode_l hW c1 (hXA _ _)) c1 (RT2.symm hW (hXY k'' _) (hCY k'' (ρ.comp ρ')))
  · have c1 := hcoh k' ρ k'' ρ'
    exact hIH k' ρ (A2 k' ρ) (B2 k' ρ) (hw k' ρ).1 k'' ρ' _
      (RT2.trans hW (RT2.tyCode_l hW c1 (hXA _ _)) c1 (hw k'' (ρ.comp ρ')).2.2.1)

end

end Model.Whnf
