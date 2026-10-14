import Model.Whnf.Kan2DataH

/-!
# The binary composition at inductive types without path constructors: the induction

The motives of the induction over the relation of the base (`DM1` for the relation, at all
restrictions; `DM2` for the relation at one stage), and the coherence of the compositions'
normal forms (`coh_side`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section
variable (hW : WfSig S)
include hW

/-- The hypotheses of a composition, restricted. -/
theorem HC2R_isub {A L L' a a' : Tm} {R : Tm → Tm → Prop} (σ : ISub k' k)
    (h : HC2R S k' (A.isub σ) (L.isub σ) (L'.isub σ) (a.isub σ) (a'.isub σ) R) :
    HC2R S k A L L' a a' (fun x y => R (x.isub σ) (y.isub σ)) := by
  intro φ φ' u u' hty hty' heq hteq h12 h21 htube haa hbd hbd'
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have := EqTm.cofIsub hW hφs hteq σ
  rw [isub_dshift] at this
  exact h (φ.subst σ.τ) (φ'.subst σ.τ) (u.isub σ.up) (u'.isub σ.up) (HasTy.isubS hW hty σ) (HasTy.isubS hW hty' σ)
    (EqTm.isubS hW heq σ) this (ent_subst h12 σ.τ) (ent_subst h21 σ.τ) (htube.isub σ) (RE2.isub hW haa σ)
    (bdry_isub hbd σ) (bdry_isub' hbd' σ)

end

/-- The motive at the relation of an inductive type at all restrictions: composition over the
restricted related elements. -/
def DM1 (S : Sig) (d : ℕ) {K : ℕ} (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A x x' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d (P.isub ρ) → ∀ (Q Q' : Tm),
    RT2 S K (.data d P) (.data d Q) → RT2 S K (.data d P) (.data d Q') → ∀ K2 (σ : ISub K2 k1),
    HC2 S K2 (.data d (P.isub (ρ.comp σ))) (.data d (Q.isub (ρ.comp σ))) (.data d (Q'.isub (ρ.comp σ)))
      (x.isub σ) (x'.isub σ)

/-- The motive at the relation of an inductive type at one stage: composition over the related elements,
related at that stage. -/
def DM2 (S : Sig) (d : ℕ) (D : DataDecl) {K : ℕ} (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A y y' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d (P.isub ρ) → ∀ (Q Q' : Tm),
    RT2 S K (.data d P) (.data d Q) → RT2 S K (.data d P) (.data d Q') →
    HC2R S k1 (.data d (P.isub ρ)) (.data d (Q.isub ρ)) (.data d (Q'.isub ρ)) y y'
      (DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 g
        (.data d (P.isub ρ)))

section side
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
  (hArgK : ∀ c j n (g : Hom n K) pre, (ΘK S D d K P).PtValid c n g pre → KanP2 S n ((ΘK S D d K P).ty c j n g pre))
include hW hD hH hP hPP hArgK

theorem eDσ (R : Tm) {k1 : ℕ} (ρ : ISub k1 K) {k3 : ℕ} (σ : ISub k3 k1) :
    (Tm.data d (R.isub ρ)).isub σ = .data d (R.isub (ρ.comp σ)) := by
  show Tm.data d ((R.isub ρ).isub σ) = _; rw [Tm.isub_isub]

/-- A composition over a base with a constructor normal form reduces to the `hcompCon` contractum. -/
theorem hcomp_red_con {k3 : ℕ} {Q1 : Tm} (hQ1 : RT2 S K (.data d P) (.data d Q1)) (ρ3 : ISub k3 K) {c : ℕ} {C : Ctor}
    (hC : D.ctors[c]? = some C) {φ1 : I} {u1 x1 qs : Tm} {X : List Tm} (hn : ¬ I.Entails .one φ1)
    (hty : HasTy S k3 .one [] (.hcomp (.data d (Q1.isub ρ3)) φ1 u1 x1) (.data d (P.isub ρ3)))
    (ht : RedE S k3 (.data d (P.isub ρ3)) x1 (.con d c qs (Tm.ofList X) [])) :
    HasTy S k3 .one [] (.hcomp (.data d (Q1.isub ρ3)) φ1 u1 (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ3)) ∧
    EqTm S k3 .one [] (.hcomp (.data d (Q1.isub ρ3)) φ1 u1 x1)
      (.hcomp (.data d (Q1.isub ρ3)) φ1 u1 (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ3)) ∧
    Red S (.hcomp (.data d (Q1.isub ρ3)) φ1 u1 x1) (.hcomp (.data d (Q1.isub ρ3)) φ1 u1 (.con d c qs (Tm.ofList X) [])) := by
  have hS := sigClosed_of_wfSig hW
  have hXP := tyCode_of_univ hW hP
  obtain ⟨l0, ⟨hL, hφs, hu, hy, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hdq := (Comp2_ty_base (RT2.isub hW hXP hQ1 ρ3)).2.2.2.2.2
  have hQP : TyEq S k3 (.data d (Q1.isub ρ3)) (.data d (P.isub ρ3)) := TyEq.symm hdq
  have eyQ := spec_to_minimal_eq hW (ht.2.tyConv hdq)
  have hT0 := wf_typed _ S rfl hW
  have hcon := (pre_eq hS hT0.1 hT0.2 eyQ).2.1
  have hcs : (cof .one φ1).Scoped k3 := ⟨trivial, hφs⟩
  have hside2 := hside.trans (EqTm0.restrict hcs (ent_and_left _ _) eyQ)
  have hHL := HasTy0.hcomp hL hφs hu hcon hside2
  have hty0 := HasTy0.hcomp hL hφs hu hy hside
  exact ⟨(minimal_to_spec hHL).tyConv hQP, (EqTm.hcomp (minimal_to_spec hty0) (minimal_to_spec hHL)
    (EqTm.refl (minimal_to_spec hL)) (ent_refl _) (ent_refl _) (EqTm.refl (minimal_to_spec hu))
    (minimal_to_spec_eq eyQ)).tyConv hQP, red_hcomp_base hD hH hn ht.1.1⟩

/-- The coherence of the normal forms of a composition over a related element, given the
compositions over the coherence data of the element at one stage. -/
theorem coh_side {k1 : ℕ} (ρ : ISub k1 K) {Q1 : Tm} (hQ1 : RT2 S K (.data d P) (.data d Q1)) {x1 : Tm}
    (hx1 : RE2 S k1 (.data d (P.isub ρ)) x1 x1)
    (ihc : ∀ k' (τ : ISub k' k1) w, RedW S (x1.isub τ) w → ∀ k'' (ρ' : ISub k'' k'),
      DM2 S d D P k'' (ρ.hom.comp (τ.comp ρ').hom) (.data d (P.isub (ρ.comp (τ.comp ρ')))) (w.isub ρ')
        (x1.isub (τ.comp ρ')))
    {φ1 : I} {u1 : Tm} (hty1 : HasTy S k1 .one [] (.hcomp (.data d (Q1.isub ρ)) φ1 u1 x1) (.data d (P.isub ρ)))
    (htube1 : Tube2 S k1 (.data d (P.isub ρ)) φ1 u1 u1)
    (hbd1 : ∀ k' (σ : ISub k' k1), (ival (idEnv k') (φ1.subst σ.τ)).holds →
      RE2 S k' ((Tm.data d (P.isub ρ)).isub σ) ((u1.isub σ.up).dinst .zero) (x1.isub σ))
    {K3 : ℕ} (τ : ISub K3 k1) (w : Tm) (hw : RedW S ((Tm.hcomp (.data d (Q1.isub ρ)) φ1 u1 x1).isub τ) w)
    {K4 : ℕ} (ρ' : ISub K4 K3) :
    DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) K4
      (ρ.hom.comp (τ.comp ρ').hom) ((Tm.data d (P.isub ρ)).isub (τ.comp ρ')) (w.isub ρ')
      ((Tm.hcomp (.data d (Q1.isub ρ)) φ1 u1 x1).isub (τ.comp ρ')) := by
  have hS := sigClosed_of_wfSig hW
  have hXP := tyCode_of_univ hW hP
  obtain ⟨l0, ⟨-, hφs, hu, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty1) rfl
  have huc : u1.closedB 0 (k1 + 1) = true := closed_ty hu
  have eH : ∀ {k3 : ℕ} (σ : ISub k3 k1), (Tm.hcomp (.data d (Q1.isub ρ)) φ1 u1 x1).isub σ =
      .hcomp (.data d (Q1.isub (ρ.comp σ))) (φ1.subst σ.τ) (u1.isub σ.up) (x1.isub σ) := by
    intro k3 σ; rw [isub_hcomp, eDσ hW hD hH hP hPP hArgK Q1 ρ σ]
  have ePσ := fun {k3 : ℕ} (σ : ISub k3 k1) => eDσ hW hD hH hP hPP hArgK P ρ σ
  have hPσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), RT2 S k3 (.data d (P.isub (ρ.comp σ))) (.data d (P.isub (ρ.comp σ))) :=
    fun σ => RT2.isub hW hXP hPP (ρ.comp σ)
  have hfσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), I.Entails .one (φ1.subst σ.τ) → (ival (idEnv k3) (φ1.subst σ.τ)).holds :=
    fun σ h => (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 h
  rw [eH, ePσ, ← ISub.hom_comp]
  rw [eH] at hw
  by_cases hfτ : I.Entails .one (φ1.subst τ.τ)
  · -- the face holds at `τ`
    have hfτρ : I.Entails .one (φ1.subst (τ.comp ρ').τ) := by rw [I_subst_comp]; exact ent_subst hfτ _
    have hw' := red_redW (.step (step_hcomp_face hfτ) (.refl _)) hw
    have h1 := htube1 K3 τ .one .one trivial trivial (I_eq_refl _) (hfσ τ hfτ)
    rw [ePσ] at h1
    obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP (ρ.comp τ)).1 h1
    have hc1 := (closed_of_ty hW (RE2.typed h1).1)
    cases hdr with
    | intro _ _ hc _ =>
      have := hc K3 (ISub.id K3) w (by rw [isub_id_of_closed hc1]; exact hw') K4 ρ'
      rw [ISub.id_comp, eDσ hW hD hH hP hPP hArgK P (ρ.comp τ) ρ', ← ISub.hom_comp, ISub.comp_assoc,
        show ((u1.isub τ.up).dinst .one).isub ρ' = (u1.isub (τ.comp ρ').up).dinst .one by
          rw [isub_dinst, Tm.isub_isub, ← ISub.up_comp]; rfl] at this
      have htyτρ := HasTy.isubS hW hty1 (τ.comp ρ')
      rw [eH, ePσ] at htyτρ
      exact DR2At.expandR hW this (.step (step_hcomp_face hfτρ) (.refl _)) (EqTm.hcompFace hfτρ htyτρ)
  · -- the face does not hold at `τ`: the normal form is the `hcompCon` contractum
    have hxτ : RE2 S K3 (.data d (P.isub (ρ.comp τ))) (x1.isub τ) (x1.isub τ) := by
      have := RE2.isub hW hx1 τ; rwa [ePσ] at this
    obtain ⟨c, C, qs, X, -, -, hC, hXl, -, ht, -, -, -⟩ := dataLit_args hW hD hH hP hPP (ρ.comp τ) hxτ
    have htyτ := HasTy.isubS hW hty1 τ
    rw [eH, ePσ] at htyτ
    obtain ⟨hHc, eHc, rHc⟩ := hcomp_red_con hW hD hH hP hPP hArgK hQ1 (ρ.comp τ) hC hfτ htyτ ht
    have hQl := (dataLit_rel hW hD hP hQ1 (ρ.comp τ)).2.2.2.2.2.2
    have hQlen : (Q1.isub (ρ.comp τ)).toList.length = D.params.length := by
      have := data_len_of hW (((Comp2_ty_base hQ1).2.2.1).isub hW (ρ.comp τ)); rwa [dataD_eq hW hD] at this
    have hwe : w = .con d c (Q1.isub (ρ.comp τ)) (Tm.ofList (conOuts d D c C (Q1.isub (ρ.comp τ)) (φ1.subst τ.τ)
        (u1.isub τ.up) X)) [] :=
      RedW.unique hw ⟨rHc.trans (.step (step_hcompCon' hD hH hC hfτ hXl) (.refl _)),
        step_con_nonHIT hD hH hC _ _ _⟩
    subst hwe
    have econ : (Tm.con d c (Q1.isub (ρ.comp τ)) (Tm.ofList (conOuts d D c C (Q1.isub (ρ.comp τ)) (φ1.subst τ.τ)
        (u1.isub τ.up) X)) []).isub ρ' = .con d c (Q1.isub (ρ.comp (τ.comp ρ')))
        (Tm.ofList (conOuts d D c C (Q1.isub (ρ.comp (τ.comp ρ'))) ((φ1.subst τ.τ).subst ρ'.τ)
          ((u1.isub τ.up).isub ρ'.up) (X.map (·.isub ρ')))) [] := by
      show Tm.con d c ((Q1.isub (ρ.comp τ)).isub ρ') ((Tm.ofList _).isub ρ') [] = _
      rw [ofList_isub, conOuts_isub hW hD hC hQl hQlen hXl ρ', Tm.isub_isub, ISub.comp_assoc]
    rw [econ]
    have eφ : (φ1.subst τ.τ).subst ρ'.τ = φ1.subst (τ.comp ρ').τ := by rw [I_subst_comp]
    have eu : (u1.isub τ.up).isub ρ'.up = u1.isub (τ.comp ρ').up := by rw [Tm.isub_isub, ← ISub.up_comp]
    rw [eφ, eu]
    -- the composition over the restricted normal form of the base
    have econX : (Tm.con d c qs (Tm.ofList X) []).isub ρ' = .con d c (qs.isub ρ') (Tm.ofList (X.map (·.isub ρ'))) [] := by
      show Tm.con d c (qs.isub ρ') ((Tm.ofList X).isub ρ') [] = _; rw [ofList_isub]
    have hHcρ := HasTy.isubS hW hHc ρ'
    rw [isub_hcomp, econX, eDσ hW hD hH hP hPP hArgK Q1 (ρ.comp τ) ρ', eDσ hW hD hH hP hPP hArgK P (ρ.comp τ) ρ',
      ISub.comp_assoc, eφ, eu] at hHcρ
    have htyτρ := HasTy.isubS hW hty1 (τ.comp ρ')
    rw [eH, ePσ] at htyτρ
    have htubeτρ : Tube2 S K4 (.data d (P.isub (ρ.comp (τ.comp ρ')))) (φ1.subst (τ.comp ρ').τ) (u1.isub (τ.comp ρ').up)
        (u1.isub (τ.comp ρ').up) := by
      have := htube1.isub (τ.comp ρ'); rwa [ePσ] at this
    by_cases hf2 : I.Entails .one (φ1.subst (τ.comp ρ').τ)
    · -- the face holds at the further restriction
      have hfc := face_con hW hD hH hP hPP hQ1 (ρ.comp (τ.comp ρ')) hC hf2 hHcρ htubeτρ
      obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP (ρ.comp (τ.comp ρ'))).1 hfc
      exact DR2At.expandR hW (DR2.at_id hW (Θ := ΘK S D d K P) hdr) (.step (step_hcomp_face hf2) (.refl _))
        (EqTm.hcompFace hf2 htyτρ)
    · -- the composition over the coherence datum of the base
      have hD2 := ihc K3 τ _ ht.1 K4 ρ' (ρ.comp (τ.comp ρ')) (ISub.hom_comp _ _).symm rfl Q1 Q1 hQ1 hQ1
      rw [econX] at hD2
      obtain ⟨-, ⟨-, hφs2, hu2, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW htyτρ) rfl
      have hQP : TyEq S K4 (.data d (Q1.isub (ρ.comp (τ.comp ρ')))) (.data d (P.isub (ρ.comp (τ.comp ρ')))) :=
        TyEq.symm (Comp2_ty_base (RT2.isub hW hXP hQ1 (ρ.comp (τ.comp ρ')))).2.2.2.2.2
      obtain ⟨lQ, eQP⟩ := tyEq_eq hW hQP ⟨_, HasTy.isubS hW hP (ρ.comp (τ.comp ρ'))⟩
      have hut2 : HasTy S (K4 + 1) (cof .one (φ1.subst (τ.comp ρ').τ)).shift [] (u1.isub (τ.comp ρ').up)
          (Tm.data d (P.isub (ρ.comp (τ.comp ρ')))).dshift :=
        HasTy.conv (minimal_to_spec hu2) (EqTm.toCof hφs2 (EqTm.dwk eQP))
      -- the base's normal form against the base
      have hcx := RE2_whnf_con hW hD hH hP hPP (ρ.comp τ) hxτ hC ht
      have hcxρ := RE2.isub hW hcx ρ'
      rw [econX, eDσ hW hD hH hP hPP hArgK P (ρ.comp τ) ρ', ISub.comp_assoc, Tm.isub_isub] at hcxρ
      have hPρ'' := hPσ (τ.comp ρ')
      have eHcρ := EqTm.isubS hW eHc ρ'
      rw [isub_hcomp, isub_hcomp, econX, eDσ hW hD hH hP hPP hArgK Q1 (ρ.comp τ) ρ',
        eDσ hW hD hH hP hPP hArgK P (ρ.comp τ) ρ', ISub.comp_assoc, eφ, eu, Tm.isub_isub] at eHcρ
      have hbd2 : ∀ k5 (κ : ISub k5 K4), (ival (idEnv k5) ((φ1.subst (τ.comp ρ').τ).subst κ.τ)).holds →
          RE2 S k5 ((Tm.data d (P.isub (ρ.comp (τ.comp ρ')))).isub κ)
            (((u1.isub (τ.comp ρ').up).isub κ.up).dinst .zero) ((x1.isub (τ.comp ρ')).isub κ) := by
        intro k5 κ hh
        have := bdry_isub hbd1 (τ.comp ρ') k5 κ hh
        rwa [ePσ] at this
      have hDA := hD2 _ _ _ _ hHcρ htyτρ eHcρ.symm (EqTm.refl hut2)
        (ent_refl _) (ent_refl _) htubeτρ hcxρ hbd2
        (fun k5 κ hh => RE2.trans hW (RT2.isub hW (RE2.tyCode hW hcxρ) hPρ'' κ) (RE2.isub hW hcxρ κ)
          (RE2.symm hW (RT2.isub hW (RE2.tyCode hW hcxρ) hPρ'' κ) (hbd2 k5 κ hh)))
      rw [← ISub.hom_comp] at hDA
      have hXl' : (X.map (·.isub ρ')).length = C.args.length := by simp [hXl]
      have hq1T : HasTy S K4 .one [] (.data d (Q1.isub (ρ.comp (τ.comp ρ')))) (.univ D.level) := by
        obtain ⟨l, hq | hq⟩ := ((Comp2_ty_base hQ1).2.2.1).isub hW (ρ.comp (τ.comp ρ'))
        · obtain ⟨D', hD', hpt⟩ := gen_data_tele (spec_to_minimal hW hq) rfl
          rw [hD] at hD'; cases hD'
          exact minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hpt)
        · cases hq
      have hcan := tubeCanon_of hW hD hH hP (ρ.comp (τ.comp ρ')) (TyEq.symm hQP) hq1T htubeτρ
      have e := hcompCon_sound hW hD hH hC hHcρ hcan
      refine DR2At.redL hW hDA (.step (step_hcompCon' hD hH hC hf2 hXl') (.refl _)) ?_
      rw [conOuts_eq_tele _ _ _ _ hXl']
      exact e

end side

end

end Model.Whnf
