import Model.Whnf.PerAll

/-!
# The binary relation at the type formers, for closed types

Formation, introduction and elimination of related closed types and elements, in terms of `RT2`
and `RE2` (the relations at the code of the left type).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' m : ℕ}

variable (hW : WfSig S)
include hW

/-! ### Basic properties of `RT2` and `RE2` -/

theorem perK {X : V} (hX : TyCode k X) : PERP (Comp2 S X k k (Hom.id k)) := per2_tyCode hW hX k (Hom.id k)

theorem RT2.semK_eq {A A' : Tm} (h : RT2 S k A A') : semK S k A' = semK S k A :=
  (semK_tyEq hW (Comp2_ty_base h).2.2.2.2.2).symm

theorem RT2.symm {A A' : Tm} (hX : TyCode k (semK S k A)) (h : RT2 S k A A') : RT2 S k A' A := by
  unfold RT2 at h ⊢; rw [RT2.semK_eq hW h]; exact (perK hW hX).symTy h

theorem RT2.trans {A A' A'' : Tm} (hX : TyCode k (semK S k A)) (h : RT2 S k A A') (h' : RT2 S k A' A'') :
    RT2 S k A A'' := by
  unfold RT2 at h h' ⊢; rw [RT2.semK_eq hW h] at h'; exact (perK hW hX).transTy h h'

theorem RT2.refl {A A' : Tm} (hX : TyCode k (semK S k A)) (h : RT2 S k A A') : RT2 S k A A :=
  (perK hW hX).reflTy h

theorem RT2.refl' {A A' : Tm} (hX : TyCode k (semK S k A)) (h : RT2 S k A A') : RT2 S k A' A' :=
  RT2.trans hW (RT2.semK_eq hW h ▸ hX) (RT2.symm hW hX h) h

omit hW in
theorem RE2.typed {A t t' : Tm} (h : RE2 S k A t t') : EB S k A t t' := (Comp2_el h).1

theorem RE2.tyCode {A t t' : Tm} (h : RE2 S k A t t') : TyCode k (semK S k A) :=
  tyCode_of_ty hW (RE2.typed h).1

theorem RE2.symm {A A' t t' : Tm} (hA : RT2 S k A A') (h : RE2 S k A t t') : RE2 S k A t' t :=
  (perK hW (RE2.tyCode hW h)).symEl hA h

theorem RE2.trans {A A' t t' t'' : Tm} (hA : RT2 S k A A') (h : RE2 S k A t t') (h' : RE2 S k A t' t'') :
    RE2 S k A t t'' :=
  (perK hW (RE2.tyCode hW h)).transEl hA h h'

theorem RE2.conv {A A' t t' : Tm} (hA : RT2 S k A A') (h : RE2 S k A t t') : RE2 S k A' t t' := by
  have := (perK hW (RE2.tyCode hW h)).conv hA h
  unfold RE2; rw [RT2.semK_eq hW hA]; exact this

theorem RT2.isub {A A' : Tm} (hX : TyCode k (semK S k A)) (h : RT2 S k A A') (σ : ISub k' k) :
    RT2 S k' (A.isub σ) (A'.isub σ) := by
  have hA := (Comp2_ty_base h).2.1
  unfold RT2 at h ⊢
  have := ((kr2_tyCode hW hX) k (Hom.id k) k' σ A A' A A).1 h
  rw [Hom.id_comp, Comp2_eq_res (IsKV.ne_empty hX.fib.kv)] at this
  rwa [semK_isubTy hW hA]

theorem RE2.isub {A t t' : Tm} (h : RE2 S k A t t') (σ : ISub k' k) :
    RE2 S k' (A.isub σ) (t.isub σ) (t'.isub σ) := by
  have hX := RE2.tyCode hW h
  have hA := isTyK_of_ty hW (RE2.typed h).1
  unfold RE2 at h ⊢
  have := ((kr2_tyCode hW hX) k (Hom.id k) k' σ A A t t').2 h
  rw [Hom.id_comp, Comp2_eq_res (IsKV.ne_empty hX.fib.kv)] at this
  rwa [semK_isubTy hW hA]

/-- The relations of a type's code at a restriction are those of the restricted type. -/
theorem Comp2_res_el {A : Tm} {l : ℕ} (hA : HasTy S k .one [] A (.univ l)) (σ : ISub k' k) :
    Comp2 S (semK S k A) k k' σ.hom = Comp2 S (semK S k' (A.isub σ)) k' k' (Hom.id k') := by
  rw [semK_isubS hW hA, Comp2_eq_res (semK_ne hW hA)]

/-! ### Universes -/

theorem RE2_univ_iff {l : ℕ} {T T' : Tm} :
    RE2 S k (.univ l) T T' ↔ EB S k (.univ l) T T' ∧ semK S k T ∈ ZFSet.sep (WF l k) (Vt l) ∧ RT2 S k T T' := by
  unfold RE2 RT2
  rw [show semK S k (.univ l) = univC k l from rfl, Comp2_univC]
  constructor
  · rintro ⟨he, -, hm, hrt⟩; exact ⟨he, hm, hrt⟩
  · rintro ⟨he, hm, hrt⟩
    refine ⟨he, ?_, hm, hrt⟩
    rw [res_id (isKV_univC _), El_univC]; exact hm

theorem RE2_univ_of {l : ℕ} {T T' : Tm} (he : EB S k (.univ l) T T') (hrt : RT2 S k T T') :
    RE2 S k (.univ l) T T' := by
  refine (RE2_univ_iff hW).2 ⟨he, ?_, hrt⟩
  have := mem_of_ty hW he.1
  rwa [show semK S k (.univ l) = univC k l from rfl, El_univC] at this

theorem RE2_univ_ty {l : ℕ} {T T' : Tm} (h : RE2 S k (.univ l) T T') : RT2 S k T T' :=
  ((RE2_univ_iff hW).1 h).2.2

/-- The type relation of a universe: both sides reduce to it at every restriction. -/
theorem RT2_univ {l : ℕ} : RT2 S k (.univ l) (.univ l) := by
  unfold RT2
  rw [show semK S k (.univ l) = univC k l from rfl, Comp2_univC]
  refine ⟨⟨⟨l, .inr rfl⟩, ⟨l, .inr rfl⟩, ?_, ?_, TyEq.refl _⟩, fun k' σ => ?_⟩
  · rw [res_id (isKV_univC _)]; rfl
  · rw [res_id (isKV_univC _)]; rfl
  · exact ⟨⟨redW_self rfl, TyEq.refl _⟩, ⟨redW_self rfl, TyEq.refl _⟩⟩

/-! ### `Π` -/

/-- The code of a family at an argument. -/
theorem fam_code_eq2 {A B a : Tm} {l : ℕ} (hA : HasTy S k .one [] A (.univ l)) (σ : ISub k' k)
    (ha : HasTy S k' .one [] a (A.isub σ)) :
    apZ (dat (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a))
      k' σ.hom) (semK S k' a) = semK S k' ((B.isub σ).inst a) := by
  have hamem : semK S k' a ∈ El (semK S k A) σ.hom := by
    have := mem_of_ty hW ha
    rwa [semK_isubS hW hA, El_res, Hom.comp_id] at this
  unfold famV
  rw [dat_lamV, apZ_fnZ _ hamem, sem_fam_eq hW ha σ]

omit hW in
theorem cod_ty (hW : WfSig S) {A B a : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A B) (.univ l))
    (ha : HasTy S k .one [] a A) : HasTy S k .one [] (B.inst a) (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  have := HasTy0.subst hS (HasTy0.piCod hS (spec_to_minimal hW hpi)) (spec_to_minimal hW ha)
  exact minimal_to_spec this

omit hW in
theorem codS_ty (hW : WfSig S) {A B a : Tm} {l : ℕ} (hs : HasTy S k .one [] (.sigma A B) (.univ l))
    (ha : HasTy S k .one [] a A) : HasTy S k .one [] (B.inst a) (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  have := HasTy0.subst hS (HasTy0.sigmaCod hS (spec_to_minimal hW hs)) (spec_to_minimal hW ha)
  exact minimal_to_spec this

/-- Related codomains at related arguments, within one family, from those across two families. -/
theorem cod_self {A A' B B' : Tm} {l : ℕ} (hA0 : HasTy S k .one [] A (.univ l))
    (hcod : ∀ a, HasTy S k .one [] a A → HasTy S k .one [] (B.inst a) (.univ l))
    (hA : RT2 S k A A')
    (hB : ∀ a a', RE2 S k A a a' → RT2 S k (B.inst a) (B'.inst a')) {a a' : Tm} (ha : RE2 S k A a a') :
    RT2 S k (B.inst a) (B.inst a') ∧ RT2 S k (B'.inst a) (B'.inst a') := by
  have P := perK hW (tyCode_of_univ hW hA0)
  have ha' := P.reflEl' hA ha
  have haa := P.reflEl hA ha
  have hX := tyCode_of_univ hW (hcod a (RE2.typed ha).1)
  have hX' := tyCode_of_univ hW (hcod a' (RE2.typed ha).2.1)
  have h1 := hB a a' ha
  have h2 := hB a' a' ha'
  have h3 := hB a a haa
  have hX'' : TyCode k (semK S k (B'.inst a)) := RT2.semK_eq hW h3 ▸ hX
  exact ⟨RT2.trans hW hX h1 (RT2.symm hW hX' h2), RT2.trans hW hX'' (RT2.symm hW hX h3) h1⟩

theorem RT2_pi_intro {A B A' B' : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A B) (.univ l))
    (hpi' : HasTy S k .one [] (.pi A' B') (.univ l)) (he : EqTm S k .one [] (.pi A B) (.pi A' B') (.univ l))
    (hA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A'.isub σ))
    (hB : ∀ k' (σ : ISub k' k) a a', RE2 S k' (A.isub σ) a a' → RT2 S k' ((B.isub σ).inst a) ((B'.isub σ).inst a')) :
    RT2 S k (.pi A B) (.pi A' B') := by
  have hA0 := HasTy.piDom hpi
  have hAσ := fun k' (σ : ISub k' k) => HasTy.isubS hW hA0 σ
  have hXσ := fun k' (σ : ISub k' k) => tyCode_of_univ hW (hAσ k' σ)
  have hcod : ∀ k' (σ : ISub k' k) a, HasTy S k' .one [] a (A.isub σ) →
      HasTy S k' .one [] ((B.isub σ).inst a) (.univ l) :=
    fun k' σ a ha => cod_ty hW (by have := HasTy.isubS hW hpi σ; rwa [isub_pi] at this) ha
  have hself := fun k' (σ : ISub k' k) {a a' : Tm} (ha : RE2 S k' (A.isub σ) a a') =>
    cod_self hW (hAσ k' σ) (hcod k' σ) (hA k' σ) (hB k' σ) ha
  have hsem' : semK S k (.pi A' B') = semK S k (.pi A B) := (semK_eq hW he).symm
  unfold RT2
  rw [semK_piT hW hpi, Comp2_piC _ _ (semK_ne hW hA0)]
  refine ⟨⟨⟨l, .inl hpi⟩, ⟨l, .inl hpi'⟩, ?_, ?_, .inr ⟨l, he⟩⟩, fun k' σ => ?_, ?_, ?_⟩
  · rw [← semK_piT hW hpi, res_id (kv_semK_of_univ hW hpi)]
  · rw [hsem', ← semK_piT hW hpi, res_id (kv_semK_of_univ hW hpi)]
  · refine ⟨A.isub σ, B.isub σ, A'.isub σ, B'.isub σ, ?_, ?_, ?_, fun a a' ha => ?_⟩
    · rw [isub_pi]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [isub_pi]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [Hom.id_comp, Comp2_res_el hW hA0]; exact hA k' σ
    · rw [Hom.id_comp, Comp2_res_el hW hA0] at ha
      rw [Hom.id_comp, fam_code_eq2 hW hA0 σ (RE2.typed ha).1]
      exact hB k' σ a a' ha
  · intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
    rw [isub_pi] at h1 h2
    obtain ⟨rfl, rfl⟩ : A.isub σ = A1 ∧ B.isub σ = B1 := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
    obtain ⟨rfl, rfl⟩ : A.isub (σ.comp σ') = A2 ∧ B.isub (σ.comp σ') = B2 := by
      have := RedW.unique (redW_self rfl) h2.1; injection this; constructor <;> assumption
    rw [Tm.isub_isub, Tm.isub_isub, Hom.id_comp, Comp2_res_el hW hA0]
    refine ⟨RT2.refl hW (hXσ _ _) (hA k2 (σ.comp σ')), fun a a' ha => ?_⟩
    rw [fam_code_eq2 hW hA0 _ (RE2.typed ha).1]
    exact (hself k2 (σ.comp σ') ha).1
  · intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
    rw [isub_pi] at h1 h2
    obtain ⟨rfl, rfl⟩ : A'.isub σ = A1 ∧ B'.isub σ = B1 := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
    obtain ⟨rfl, rfl⟩ : A'.isub (σ.comp σ') = A2 ∧ B'.isub (σ.comp σ') = B2 := by
      have := RedW.unique (redW_self rfl) h2.1; injection this; constructor <;> assumption
    rw [Tm.isub_isub, Tm.isub_isub, Hom.id_comp, Comp2_res_el hW hA0]
    have hAA := hA k2 (σ.comp σ')
    have P := perK hW (hXσ k2 (σ.comp σ'))
    refine ⟨P.reflTy' hAA, fun a a' ha => ?_⟩
    have ha' : RE2 S k2 (A.isub (σ.comp σ')) a a' := P.conv (P.symTy hAA) ha
    rw [fam_code_eq2 hW hA0 _ (RE2.typed ha').1]
    have h3 := hB k2 (σ.comp σ') a a (P.reflEl hAA ha')
    have := (hself k2 (σ.comp σ') ha').2
    unfold RT2 at this h3
    rw [RT2.semK_eq hW h3] at this
    exact this

theorem RT2_sigma_intro {A B A' B' : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A B) (.univ l))
    (hsig' : HasTy S k .one [] (.sigma A' B') (.univ l)) (he : EqTm S k .one [] (.sigma A B) (.sigma A' B') (.univ l))
    (hA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A'.isub σ))
    (hB : ∀ k' (σ : ISub k' k) a a', RE2 S k' (A.isub σ) a a' → RT2 S k' ((B.isub σ).inst a) ((B'.isub σ).inst a')) :
    RT2 S k (.sigma A B) (.sigma A' B') := by
  have hA0 := HasTy.sigmaDom hsig
  have hAσ := fun k' (σ : ISub k' k) => HasTy.isubS hW hA0 σ
  have hXσ := fun k' (σ : ISub k' k) => tyCode_of_univ hW (hAσ k' σ)
  have hcod : ∀ k' (σ : ISub k' k) a, HasTy S k' .one [] a (A.isub σ) →
      HasTy S k' .one [] ((B.isub σ).inst a) (.univ l) :=
    fun k' σ a ha => codS_ty hW (by have := HasTy.isubS hW hsig σ; rwa [isub_sigma] at this) ha
  have hself := fun k' (σ : ISub k' k) {a a' : Tm} (ha : RE2 S k' (A.isub σ) a a') =>
    cod_self hW (hAσ k' σ) (hcod k' σ) (hA k' σ) (hB k' σ) ha
  have hsem' : semK S k (.sigma A' B') = semK S k (.sigma A B) := (semK_eq hW he).symm
  unfold RT2
  rw [semK_sigmaT hW hsig, Comp2_sigmaC _ _ (semK_ne hW hA0)]
  refine ⟨⟨⟨l, .inl hsig⟩, ⟨l, .inl hsig'⟩, ?_, ?_, .inr ⟨l, he⟩⟩, fun k' σ => ?_, ?_, ?_⟩
  · rw [← semK_sigmaT hW hsig, res_id (kv_semK_of_univ hW hsig)]
  · rw [hsem', ← semK_sigmaT hW hsig, res_id (kv_semK_of_univ hW hsig)]
  · refine ⟨A.isub σ, B.isub σ, A'.isub σ, B'.isub σ, ?_, ?_, ?_, fun a a' ha => ?_⟩
    · rw [isub_sigma]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [isub_sigma]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [Hom.id_comp, Comp2_res_el hW hA0]; exact hA k' σ
    · rw [Hom.id_comp, Comp2_res_el hW hA0] at ha
      rw [Hom.id_comp, fam_code_eq2 hW hA0 σ (RE2.typed ha).1]
      exact hB k' σ a a' ha
  · intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
    rw [isub_sigma] at h1 h2
    obtain ⟨rfl, rfl⟩ : A.isub σ = A1 ∧ B.isub σ = B1 := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
    obtain ⟨rfl, rfl⟩ : A.isub (σ.comp σ') = A2 ∧ B.isub (σ.comp σ') = B2 := by
      have := RedW.unique (redW_self rfl) h2.1; injection this; constructor <;> assumption
    rw [Tm.isub_isub, Tm.isub_isub, Hom.id_comp, Comp2_res_el hW hA0]
    refine ⟨RT2.refl hW (hXσ _ _) (hA k2 (σ.comp σ')), fun a a' ha => ?_⟩
    rw [fam_code_eq2 hW hA0 _ (RE2.typed ha).1]
    exact (hself k2 (σ.comp σ') ha).1
  · intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
    rw [isub_sigma] at h1 h2
    obtain ⟨rfl, rfl⟩ : A'.isub σ = A1 ∧ B'.isub σ = B1 := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
    obtain ⟨rfl, rfl⟩ : A'.isub (σ.comp σ') = A2 ∧ B'.isub (σ.comp σ') = B2 := by
      have := RedW.unique (redW_self rfl) h2.1; injection this; constructor <;> assumption
    rw [Tm.isub_isub, Tm.isub_isub, Hom.id_comp, Comp2_res_el hW hA0]
    have hAA := hA k2 (σ.comp σ')
    have P := perK hW (hXσ k2 (σ.comp σ'))
    refine ⟨P.reflTy' hAA, fun a a' ha => ?_⟩
    have ha' : RE2 S k2 (A.isub (σ.comp σ')) a a' := P.conv (P.symTy hAA) ha
    rw [fam_code_eq2 hW hA0 _ (RE2.typed ha').1]
    have h3 := hB k2 (σ.comp σ') a a (P.reflEl hAA ha')
    have := (hself k2 (σ.comp σ') ha').2
    unfold RT2 at this h3
    rw [RT2.semK_eq hW h3] at this
    exact this

theorem RE2_sigma_intro {A B p p' : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A B) (.univ l))
    (hp : EB S k (.sigma A B) p p') (h1 : RE2 S k A (.fst p) (.fst p'))
    (h2 : RE2 S k (B.inst (.fst p)) (.snd p) (.snd p')) :
    RE2 S k (.sigma A B) p p' := by
  have hA0 := HasTy.sigmaDom hsig
  unfold RE2
  rw [semK_sigmaT hW hsig, Comp2_sigmaC _ _ (semK_ne hW hA0)]
  refine ⟨hp, ?_, hp, fun k' σ => ⟨A.isub σ, B.isub σ, by rw [isub_sigma]; exact ⟨redW_self rfl, TyEq.refl _⟩,
    ?_, ?_⟩⟩
  · rw [← semK_sigmaT hW hsig, res_id (kv_semK_of_univ hW hsig)]; exact mem_of_ty hW hp.1
  · simp only [ISub.id_comp, Hom.id_comp]
    rw [Comp2_res_el hW hA0]
    have := RE2.isub hW h1 σ
    rwa [isub_fst, isub_fst] at this
  · simp only [ISub.id_comp, ISub.hom_id, Hom.id_comp]
    have h1σ := RE2.isub hW h1 σ
    rw [isub_fst] at h1σ
    rw [fam_code_eq2 hW hA0 σ (RE2.typed h1σ).1]
    have := RE2.isub hW h2 σ
    rwa [isub_inst, isub_snd, isub_snd, isub_fst] at this

theorem RE2_sigma_elim {A B p p' : Tm} (hp : RE2 S k (.sigma A B) p p') :
    RE2 S k A (.fst p) (.fst p') ∧ RE2 S k (B.inst (.fst p)) (.snd p) (.snd p') := by
  have hpt := (RE2.typed hp).1
  obtain ⟨l, hsig⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpt) (TyEq.refl _) (fun l h => by cases h)
  have hA := HasTy.sigmaDom hsig
  have hcl := closed_of_ty hW hsig
  unfold RE2 at hp
  rw [semK_sigmaT hW hsig, Comp2_sigmaC _ _ (semK_ne hW hA)] at hp
  obtain ⟨hE, -, -, hall⟩ := hp
  obtain ⟨A1, B1, h0, h1, h2⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed hcl] at h0
  obtain ⟨rfl, rfl⟩ : A = A1 ∧ B = B1 := by
    have := RedW.unique (redW_self rfl) h0.1; injection this; constructor <;> assumption
  simp only [ISub.id_comp, ISub.hom_id, Hom.comp_id] at h1 h2
  rw [isub_id_of_closed (closed_of_ty hW hE.1), isub_id_of_closed (closed_of_ty hW hE.2.1)] at h1 h2
  refine ⟨h1, ?_⟩
  have hfam := fam_code_eq2 (B := B) hW hA (ISub.id k)
    (by rw [isub_id_of_closed (closed_of_ty hW hA)]; exact (RE2.typed h1).1)
  rw [ISub.hom_id, isub_id_of_closed (show B.closedB 1 k = true by
    simp only [Tm.closedB, Bool.and_eq_true] at hcl; exact hcl.2)] at hfam
  rw [hfam] at h2
  exact h2

theorem RE2_pi_intro {A B f f' : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A B) (.univ l))
    (hf : EB S k (.pi A B) f f')
    (happ : ∀ k' (σ : ISub k' k) a a', RE2 S k' (A.isub σ) a a' →
      RE2 S k' ((B.isub σ).inst a) (.app (f.isub σ) a) (.app (f'.isub σ) a')) :
    RE2 S k (.pi A B) f f' := by
  have hA0 := HasTy.piDom hpi
  unfold RE2
  rw [semK_piT hW hpi, Comp2_piC _ _ (semK_ne hW hA0)]
  refine ⟨hf, ?_, hf, fun k' σ => ⟨A.isub σ, B.isub σ, by rw [isub_pi]; exact ⟨redW_self rfl, TyEq.refl _⟩,
    fun a a' ha => ?_⟩⟩
  · rw [← semK_piT hW hpi, res_id (kv_semK_of_univ hW hpi)]; exact mem_of_ty hW hf.1
  simp only [ISub.id_comp, Hom.id_comp, ISub.hom_id] at ha ⊢
  rw [Comp2_res_el hW hA0] at ha
  rw [fam_code_eq2 hW hA0 σ (RE2.typed ha).1]
  exact happ k' σ a a' ha

theorem RE2_pi_elim {A B f f' a a' : Tm} (hf : RE2 S k (.pi A B) f f') (ha : RE2 S k A a a') :
    RE2 S k (B.inst a) (.app f a) (.app f' a') := by
  have hft := (RE2.typed hf).1
  obtain ⟨l, hpi⟩ := ty_of_tyEq hW (isTyK_of_ty hW hft) (TyEq.refl _) (fun l h => by cases h)
  have hA := HasTy.piDom hpi
  have hcl := closed_of_ty hW hpi
  unfold RE2 at hf
  rw [semK_piT hW hpi, Comp2_piC _ _ (semK_ne hW hA)] at hf
  obtain ⟨hE, -, -, hall⟩ := hf
  obtain ⟨A1, B1, h1, h2⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed hcl] at h1
  obtain ⟨rfl, rfl⟩ : A = A1 ∧ B = B1 := by
    have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
  simp only [ISub.id_comp, ISub.hom_id, Hom.comp_id] at h2
  have := h2 a a' (by unfold RE2 at ha; exact ha)
  have hfam := fam_code_eq2 (B := B) hW hA (ISub.id k)
    (by rw [isub_id_of_closed (closed_of_ty hW hA)]; exact (RE2.typed ha).1)
  rw [ISub.hom_id, isub_id_of_closed (show B.closedB 1 k = true by
    simp only [Tm.closedB, Bool.and_eq_true] at hcl; exact hcl.2)] at hfam
  rw [isub_id_of_closed (closed_of_ty hW hE.1), isub_id_of_closed (closed_of_ty hW hE.2.1), hfam] at this
  exact this

/-! ### Path types and `(i : I) → L` -/

/-- The relations of a line's code at a point of a restriction are those of the line's instance there. -/
theorem Comp2_res_line {L : Tm} {l : ℕ} (hL : HasTy S (k + 1) .one [] L (.univ l)) (σ : ISub k' k) (r : I)
    (hr : r.Scoped k') :
    Comp2 S (semK S (k + 1) L) (k + 1) k' ((Hom.lift (Hom.id k)).comp (ISub.cons r hr σ).hom) =
      Comp2 S (semK S k' ((L.isub σ.up).dinst r)) k' k' (Hom.id k') := by
  rw [Hom.lift_id, Hom.id_comp, Comp2_res_el hW hL, isub_up_dinst _ _ _ hr]

theorem Comp2_res_up {L : Tm} {l : ℕ} (hL : HasTy S (k + 1) .one [] L (.univ l)) (σ : ISub k' k) :
    Comp2 S (semK S (k + 1) L) (k + 1) (k' + 1) ((Hom.lift (Hom.id k)).comp σ.up.hom) =
      Comp2 S (semK S (k' + 1) (L.isub σ.up)) (k' + 1) (k' + 1) (Hom.id (k' + 1)) := by
  rw [Hom.lift_id, Hom.id_comp, Comp2_res_el hW hL]

theorem RT2_path_intro {L a b L' a' b' : Tm} {l : ℕ} (hpath : HasTy S k .one [] (.path L a b) (.univ l))
    (hpath' : HasTy S k .one [] (.path L' a' b') (.univ l))
    (he : EqTm S k .one [] (.path L a b) (.path L' a' b') (.univ l))
    (hL : ∀ k' (σ : ISub k' k), RT2 S (k' + 1) (L.isub σ.up) (L'.isub σ.up))
    (hLr : ∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
      RT2 S k' ((L.isub σ.up).dinst r) ((L'.isub σ.up).dinst r'))
    (ha : RE2 S k (L.dinst .zero) a a') (hb : RE2 S k (L.dinst .one) b b') :
    RT2 S k (.path L a b) (.path L' a' b') := by
  have hL0 := HasTy.pathLine hpath
  have hX := fun k' (σ : ISub k' k) => tyCode_of_univ hW (HasTy.isubS hW hL0 σ.up)
  have hsem' : semK S k (.path L' a' b') = semK S k (.path L a b) := (semK_eq hW he).symm
  unfold RT2
  rw [semK_pathT hW hpath, Comp2_pathC _ _ _ (semK_ne hW hL0)]
  refine ⟨⟨⟨l, .inl hpath⟩, ⟨l, .inl hpath'⟩, ?_, ?_, .inr ⟨l, he⟩⟩, fun k' σ => ?_, ?_, ?_⟩
  · rw [← semK_pathT hW hpath, res_id (kv_semK_of_univ hW hpath)]
  · rw [hsem', ← semK_pathT hW hpath, res_id (kv_semK_of_univ hW hpath)]
  · refine ⟨L.isub σ.up, a.isub σ, b.isub σ, L'.isub σ.up, a'.isub σ, b'.isub σ, ?_, ?_, ?_,
      fun r r' hr hr' hE => ?_, ?_, ?_⟩
    · rw [isub_path]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [isub_path]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [Comp2_res_up hW hL0]; exact hL k' σ
    · rw [Comp2_res_line hW hL0]; exact hLr k' σ r r' hr hr' hE
    · rw [Comp2_res_line hW hL0]
      have := RE2.isub hW ha σ; rwa [isub_dinst] at this
    · rw [Comp2_res_line hW hL0]
      have := RE2.isub hW hb σ; rwa [isub_dinst] at this
  · intro k1 σ k2 σ' L1 b0 b1 L2 c0 c1 h1 h2
    rw [isub_path] at h1 h2
    obtain ⟨rfl, -⟩ : L.isub σ.up = L1 ∧ True := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; exact ⟨by assumption, trivial⟩
    obtain ⟨rfl, -⟩ : L.isub (σ.comp σ').up = L2 ∧ True := by
      have := RedW.unique (redW_self rfl) h2.1; injection this; exact ⟨by assumption, trivial⟩
    rw [Tm.isub_isub, ← ISub.up_comp, Comp2_res_up hW hL0]
    exact RT2.refl hW (hX _ _) (hL k2 (σ.comp σ'))
  · intro k1 σ k2 σ' L1 b0 b1 L2 c0 c1 h1 h2
    rw [isub_path] at h1 h2
    obtain ⟨rfl, -⟩ : L'.isub σ.up = L1 ∧ True := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; exact ⟨by assumption, trivial⟩
    obtain ⟨rfl, -⟩ : L'.isub (σ.comp σ').up = L2 ∧ True := by
      have := RedW.unique (redW_self rfl) h2.1; injection this; exact ⟨by assumption, trivial⟩
    rw [Tm.isub_isub, ← ISub.up_comp, Comp2_res_up hW hL0]
    have := RT2.refl' hW (hX _ _) (hL k2 (σ.comp σ'))
    unfold RT2 at this; rwa [RT2.semK_eq hW (hL k2 (σ.comp σ'))] at this

theorem RE2_path_intro {L a b p p' : Tm} {l : ℕ} (hpath : HasTy S k .one [] (.path L a b) (.univ l))
    (hp : EB S k (.path L a b) p p')
    (happ : ∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
      RE2 S k' ((L.isub σ.up).dinst r) (.papp (p.isub σ) r) (.papp (p'.isub σ) r'))
    (h0 : RE2 S k (L.dinst .zero) (.papp p .zero) a) (h1 : RE2 S k (L.dinst .one) (.papp p .one) b) :
    RE2 S k (.path L a b) p p' := by
  have hL0 := HasTy.pathLine hpath
  unfold RE2
  rw [semK_pathT hW hpath, Comp2_pathC _ _ _ (semK_ne hW hL0)]
  refine ⟨hp, ?_, hp, fun k' σ => ⟨L.isub σ.up, a.isub σ, b.isub σ,
    by rw [isub_path]; exact ⟨redW_self rfl, TyEq.refl _⟩, fun r r' hr hr' hE => ?_, ?_, ?_⟩⟩
  · rw [← semK_pathT hW hpath, res_id (kv_semK_of_univ hW hpath)]; exact mem_of_ty hW hp.1
  · simp only [ISub.id_comp]
    rw [Comp2_res_line hW hL0]; exact happ k' σ r r' hr hr' hE
  · simp only [ISub.id_comp]
    rw [Comp2_res_line hW hL0]
    have := RE2.isub hW h0 σ; rwa [isub_dinst, isub_papp] at this
  · simp only [ISub.id_comp]
    rw [Comp2_res_line hW hL0]
    have := RE2.isub hW h1 σ; rwa [isub_dinst, isub_papp] at this

theorem RE2_path_elim {L a b p p' : Tm} (hp : RE2 S k (.path L a b) p p') :
    (∀ (r r' : I), r.Scoped k → r'.Scoped k → I.Eq r r' → RE2 S k (L.dinst r) (.papp p r) (.papp p' r')) ∧
    RE2 S k (L.dinst .zero) (.papp p .zero) a ∧ RE2 S k (L.dinst .one) (.papp p .one) b := by
  have hpt := (RE2.typed hp).1
  obtain ⟨l, hpath⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpt) (TyEq.refl _) (fun l h => by cases h)
  have hL := HasTy.pathLine hpath
  have hcl := closed_of_ty hW hpath
  unfold RE2 at hp
  rw [semK_pathT hW hpath, Comp2_pathC _ _ _ (semK_ne hW hL)] at hp
  obtain ⟨hE, -, -, hall⟩ := hp
  obtain ⟨L1, b0, b1, h0, h1, h2, h3⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed hcl] at h0
  obtain ⟨rfl, rfl, rfl⟩ : L = L1 ∧ a = b0 ∧ b = b1 := by
    have := RedW.unique (redW_self rfl) h0.1; injection this
    exact ⟨by assumption, by assumption, by assumption⟩
  simp only [ISub.id_comp] at h1 h2 h3
  have hLc : L.isub (ISub.id k).up = L := isub_up_id_of_closed (closed_of_ty hW hL)
  rw [isub_id_of_closed (closed_of_ty hW hE.1)] at h1 h2 h3
  rw [isub_id_of_closed (closed_of_ty hW hE.2.1)] at h1
  refine ⟨fun r r' hr hr' hE' => ?_, ?_, ?_⟩
  · have := h1 r r' hr hr' hE'
    rw [Comp2_res_line hW hL, hLc] at this; exact this
  · rw [Comp2_res_line hW hL, hLc] at h2; exact h2
  · rw [Comp2_res_line hW hL, hLc] at h3; exact h3

theorem ipi_line {L : Tm} {l : ℕ} (hipi : HasTy S k .one [] (.ipi L) (.univ l)) :
    HasTy S (k + 1) .one [] L (.univ l) :=
  minimal_to_spec (HasTy0.ipiLine (sigClosed_of_wfSig hW) (spec_to_minimal hW hipi))

theorem RT2_ipi_intro {L L' : Tm} {l : ℕ} (hipi : HasTy S k .one [] (.ipi L) (.univ l))
    (hipi' : HasTy S k .one [] (.ipi L') (.univ l)) (he : EqTm S k .one [] (.ipi L) (.ipi L') (.univ l))
    (hL : ∀ k' (σ : ISub k' k), RT2 S (k' + 1) (L.isub σ.up) (L'.isub σ.up))
    (hLr : ∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
      RT2 S k' ((L.isub σ.up).dinst r) ((L'.isub σ.up).dinst r')) :
    RT2 S k (.ipi L) (.ipi L') := by
  have hL0 := ipi_line hW hipi
  have hX := fun k' (σ : ISub k' k) => tyCode_of_univ hW (HasTy.isubS hW hL0 σ.up)
  have hsem' : semK S k (.ipi L') = semK S k (.ipi L) := (semK_eq hW he).symm
  unfold RT2
  rw [semK_ipiT hW hipi, Comp2_ipiC _ (semK_ne hW hL0)]
  refine ⟨⟨⟨l, .inl hipi⟩, ⟨l, .inl hipi'⟩, ?_, ?_, .inr ⟨l, he⟩⟩, fun k' σ => ?_, ?_, ?_⟩
  · rw [← semK_ipiT hW hipi, res_id (kv_semK_of_univ hW hipi)]
  · rw [hsem', ← semK_ipiT hW hipi, res_id (kv_semK_of_univ hW hipi)]
  · refine ⟨L.isub σ.up, L'.isub σ.up, ?_, ?_, ?_, fun r r' hr hr' hE => ?_⟩
    · rw [isub_ipi]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [isub_ipi]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · rw [Comp2_res_up hW hL0]; exact hL k' σ
    · rw [Comp2_res_line hW hL0]; exact hLr k' σ r r' hr hr' hE
  · intro k1 σ k2 σ' L1 L2 h1 h2
    rw [isub_ipi] at h1 h2
    obtain rfl : L.isub σ.up = L1 := by have := RedW.unique (redW_self rfl) h1.1; injection this
    obtain rfl : L.isub (σ.comp σ').up = L2 := by have := RedW.unique (redW_self rfl) h2.1; injection this
    rw [Tm.isub_isub, ← ISub.up_comp, Comp2_res_up hW hL0]
    exact RT2.refl hW (hX _ _) (hL k2 (σ.comp σ'))
  · intro k1 σ k2 σ' L1 L2 h1 h2
    rw [isub_ipi] at h1 h2
    obtain rfl : L'.isub σ.up = L1 := by have := RedW.unique (redW_self rfl) h1.1; injection this
    obtain rfl : L'.isub (σ.comp σ').up = L2 := by have := RedW.unique (redW_self rfl) h2.1; injection this
    rw [Tm.isub_isub, ← ISub.up_comp, Comp2_res_up hW hL0]
    have := RT2.refl' hW (hX _ _) (hL k2 (σ.comp σ'))
    unfold RT2 at this; rwa [RT2.semK_eq hW (hL k2 (σ.comp σ'))] at this

theorem RE2_ipi_intro {L p p' : Tm} {l : ℕ} (hipi : HasTy S k .one [] (.ipi L) (.univ l))
    (hp : EB S k (.ipi L) p p')
    (happ : ∀ k' (σ : ISub k' k) (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
      RE2 S k' ((L.isub σ.up).dinst r) (.papp (p.isub σ) r) (.papp (p'.isub σ) r')) :
    RE2 S k (.ipi L) p p' := by
  have hL0 := ipi_line hW hipi
  unfold RE2
  rw [semK_ipiT hW hipi, Comp2_ipiC _ (semK_ne hW hL0)]
  refine ⟨hp, ?_, hp, fun k' σ => ⟨L.isub σ.up, by rw [isub_ipi]; exact ⟨redW_self rfl, TyEq.refl _⟩,
    fun r r' hr hr' hE => ?_⟩⟩
  · rw [← semK_ipiT hW hipi, res_id (kv_semK_of_univ hW hipi)]; exact mem_of_ty hW hp.1
  · simp only [ISub.id_comp]
    rw [Comp2_res_line hW hL0]; exact happ k' σ r r' hr hr' hE

theorem RE2_ipi_elim {L p p' : Tm} (hp : RE2 S k (.ipi L) p p') :
    ∀ (r r' : I), r.Scoped k → r'.Scoped k → I.Eq r r' → RE2 S k (L.dinst r) (.papp p r) (.papp p' r') := by
  have hpt := (RE2.typed hp).1
  obtain ⟨l, hipi⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpt) (TyEq.refl _) (fun l h => by cases h)
  have hL := ipi_line hW hipi
  have hcl := closed_of_ty hW hipi
  unfold RE2 at hp
  rw [semK_ipiT hW hipi, Comp2_ipiC _ (semK_ne hW hL)] at hp
  obtain ⟨hE, -, -, hall⟩ := hp
  obtain ⟨L1, h0, h1⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed hcl] at h0
  obtain rfl : L = L1 := by have := RedW.unique (redW_self rfl) h0.1; injection this
  simp only [ISub.id_comp] at h1
  have hLc : L.isub (ISub.id k).up = L := isub_up_id_of_closed (closed_of_ty hW hL)
  rw [isub_id_of_closed (closed_of_ty hW hE.1), isub_id_of_closed (closed_of_ty hW hE.2.1)] at h1
  intro r r' hr hr' hE'
  have := h1 r r' hr hr' hE'
  rw [Comp2_res_line hW hL, hLc] at this; exact this


/-! ### Inversion of related `Π` and `Σ` types -/

theorem RT2_pi_inv {A B A' B' : Tm} (h : RT2 S k (.pi A B) (.pi A' B')) :
    RT2 S k A A' ∧ ∀ a a', RE2 S k A a a' → RT2 S k (B.inst a) (B'.inst a') := by
  have hb := Comp2_ty_base h
  obtain ⟨l, hpi⟩ := ty_of_tyEq hW hb.2.1 (TyEq.refl _) (fun l h => by cases h)
  have hA := HasTy.piDom hpi
  have hcl := closed_of_ty hW hpi
  simp only [Tm.closedB, Bool.and_eq_true] at hcl
  unfold RT2 at h
  rw [semK_piT hW hpi] at h
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := piC_at (IsKV.ne_empty (kv_semK_of_univ hW hA)) hW h
  obtain ⟨rfl, rfl⟩ : A = A1 ∧ B = B1 := by
    have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A' = A1' ∧ B' = B1' := by
    have := RedW.unique (redW_self rfl) h2.1; injection this; constructor <;> assumption
  refine ⟨h3, fun a a' ha => ?_⟩
  have := h4 a a' ha
  have hfam := fam_code_eq2 (B := B) hW hA (ISub.id k) (by rw [isub_id_of_closed hcl.1]; exact (RE2.typed ha).1)
  rw [ISub.hom_id, isub_id_of_closed hcl.2] at hfam
  rw [hfam] at this
  exact this

theorem RT2_sigma_inv {A B A' B' : Tm} (h : RT2 S k (.sigma A B) (.sigma A' B')) :
    RT2 S k A A' ∧ ∀ a a', RE2 S k A a a' → RT2 S k (B.inst a) (B'.inst a') := by
  have hb := Comp2_ty_base h
  obtain ⟨l, hs⟩ := ty_of_tyEq hW hb.2.1 (TyEq.refl _) (fun l h => by cases h)
  have hA := HasTy.sigmaDom hs
  have hcl := closed_of_ty hW hs
  simp only [Tm.closedB, Bool.and_eq_true] at hcl
  unfold RT2 at h
  rw [semK_sigmaT hW hs] at h
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := sigmaC_at (IsKV.ne_empty (kv_semK_of_univ hW hA)) hW h
  obtain ⟨rfl, rfl⟩ : A = A1 ∧ B = B1 := by
    have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A' = A1' ∧ B' = B1' := by
    have := RedW.unique (redW_self rfl) h2.1; injection this; constructor <;> assumption
  refine ⟨h3, fun a a' ha => ?_⟩
  have := h4 a a' ha
  have hfam := fam_code_eq2 (B := B) hW hA (ISub.id k) (by rw [isub_id_of_closed hcl.1]; exact (RE2.typed ha).1)
  rw [ISub.hom_id, isub_id_of_closed hcl.2] at hfam
  rw [hfam] at this
  exact this


/-! ### Inversion of related path types and `(i : I) → L` types -/

theorem RT2_path_inv {L a b L' a' b' : Tm} (h : RT2 S k (.path L a b) (.path L' a' b')) :
    RT2 S (k + 1) L L' ∧
    (∀ r r', r.Scoped k → r'.Scoped k → I.Eq r r' → RT2 S k (L.dinst r) (L'.dinst r')) ∧
    RE2 S k (L.dinst .zero) a a' ∧ RE2 S k (L.dinst .one) b b' := by
  have hb := Comp2_ty_base h
  obtain ⟨l, hpath⟩ := ty_of_tyEq hW hb.2.1 (TyEq.refl _) (fun l h => by cases h)
  have hL := HasTy.pathLine hpath
  have hLc : L.isub (ISub.id k).up = L := isub_up_id_of_closed (closed_of_ty hW hL)
  unfold RT2 at h
  rw [semK_pathT hW hpath, Comp2_pathC _ _ _ (semK_ne hW hL)] at h
  obtain ⟨-, hall, -⟩ := h
  obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, h4, h5, h6⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed (closed_of_ty hW hpath)] at h1
  rw [isub_id_of_closed (closed_of_isTyK hW hb.2.2.1)] at h2
  obtain ⟨rfl, rfl, rfl⟩ : L = L1 ∧ a = b0 ∧ b = b1 := by
    have := RedW.unique (redW_self rfl) h1.1; injection this
    exact ⟨by assumption, by assumption, by assumption⟩
  obtain ⟨rfl, rfl, rfl⟩ : L' = L1' ∧ a' = b0' ∧ b' = b1' := by
    have := RedW.unique (redW_self rfl) h2.1; injection this
    exact ⟨by assumption, by assumption, by assumption⟩
  rw [Comp2_res_up hW hL, hLc] at h3
  rw [Comp2_res_line hW hL, hLc] at h5 h6
  refine ⟨h3, fun r r' hr hr' hE => ?_, h5, h6⟩
  have := h4 r r' hr hr' hE
  rw [Comp2_res_line hW hL, hLc] at this
  exact this

theorem RT2_ipi_inv {L L' : Tm} (h : RT2 S k (.ipi L) (.ipi L')) :
    RT2 S (k + 1) L L' ∧ ∀ r r', r.Scoped k → r'.Scoped k → I.Eq r r' → RT2 S k (L.dinst r) (L'.dinst r') := by
  have hb := Comp2_ty_base h
  obtain ⟨l, hipi⟩ := ty_of_tyEq hW hb.2.1 (TyEq.refl _) (fun l h => by cases h)
  have hL := ipi_line hW hipi
  have hLc : L.isub (ISub.id k).up = L := isub_up_id_of_closed (closed_of_ty hW hL)
  unfold RT2 at h
  rw [semK_ipiT hW hipi, Comp2_ipiC _ (semK_ne hW hL)] at h
  obtain ⟨-, hall, -⟩ := h
  obtain ⟨L1, L1', h1, h2, h3, h4⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed (closed_of_ty hW hipi)] at h1
  rw [isub_id_of_closed (closed_of_isTyK hW hb.2.2.1)] at h2
  obtain rfl : L = L1 := by have := RedW.unique (redW_self rfl) h1.1; injection this
  obtain rfl : L' = L1' := by have := RedW.unique (redW_self rfl) h2.1; injection this
  rw [Comp2_res_up hW hL, hLc] at h3
  refine ⟨h3, fun r r' hr hr' hE => ?_⟩
  have := h4 r r' hr hr' hE
  rw [Comp2_res_line hW hL, hLc] at this
  exact this

end

end Model.Whnf
