import Model.Canon.Closed

/-!
# Canonicity: computability at the type formers, for closed types

Introduction and elimination of computable elements of `Π`-types (and the other formers), in
terms of closed syntax at a stage.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

variable (hW : WfSig S)
include hW

theorem kv_semK_of_univ {A : Tm} {l : ℕ} (h : HasTy S k .one [] A (.univ l)) : IsKV k (semK S k A) := by
  have := mem_of_ty hW h
  rw [show semK S k (.univ l) = univC k l from rfl, El_univC] at this
  exact (ZFSet.mem_sep.1 this).2.fib.kv

/-- The value of a closed term instantiating a family. -/
theorem sem_fam_eq {B a T : Tm} (ha : HasTy S k' .one [] a T) (σ : ISub k' k) :
    sem S B k' ((idEnv k).restr σ.hom) (TEnv.cons (TEnv.restr (γ0 k) σ.hom) (semK S k' a)) =
      semK S k' ((B.isub σ).inst a) := by
  have hna := natural_of_ty hW ha
  have h1 : semK S k' ((B.isub σ).inst a) = sem S (B.isub σ) k' (idEnv k') (TEnv.cons (γ0 k') (semK S k' a)) := by
    unfold semK
    rw [Tm.inst, sem_subst S _ k' _ _ _ _ (fun x => by cases x <;> [exact hna; exact natural_var S _ _ _])]
    simp only [ival.var]
    congr 1
    funext x; cases x <;> rfl
  rw [h1, show (B.isub σ) = B.dsubst σ.τ from rfl, sem_dsubst, env_isub, γ0_restr]

theorem semK_piT {A B : Tm} {l : ℕ} (h : HasTy S k .one [] (.pi A B) (.univ l)) :
    semK S k (.pi A B) = piC k (semK S k A)
      (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) := by
  unfold semK; rw [sem_pi (kv_semK_of_univ hW (HasTy.piDom h))]

theorem semK_ne {A : Tm} {l : ℕ} (h : HasTy S k .one [] A (.univ l)) : semK S k A ≠ ∅ :=
  IsKV.ne_empty (kv_semK_of_univ hW h)

/-- Computable elements of a type, at the type's code restricted: the computable elements of
the restricted type. -/
theorem Comp_res_el {A : Tm} {l : ℕ} (hA : HasTy S k .one [] A (.univ l)) (σ : ISub k' k) :
    Comp S (semK S k A) k k' σ.hom = Comp S (semK S k' (A.isub σ)) k' k' (Hom.id k') := by
  rw [semK_isubS hW hA, Comp_eq_res (semK_ne hW hA)]

theorem RE_pi_intro {A B f : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A B) (.univ l))
    (hf : HasTy S k .one [] f (.pi A B))
    (happ : ∀ k' (σ : ISub k' k) a, RE S k' (A.isub σ) a → RE S k' ((B.isub σ).inst a) (.app (f.isub σ) a)) :
    RE S k (.pi A B) f := by
  have hA := HasTy.piDom hpi
  unfold RE
  rw [semK_piT hW hpi, Comp_piC _ _ (semK_ne hW hA)]
  refine ⟨hf, ?_, hf, A, B, TyEq.refl _, fun k' σ a ha => ?_⟩
  · rw [← semK_piT hW hpi, res_id (kv_semK_of_univ hW hpi)]; exact mem_of_ty hW hf
  simp only [ISub.id_comp, Hom.id_comp, ISub.hom_id] at ha ⊢
  rw [Comp_res_el hW hA] at ha
  have hamem : semK S k' a ∈ El (semK S k A) σ.hom := by
    have := (Comp_el_typed ha).2
    rwa [El_res, Hom.comp_id, semK_isubS hW hA, El_res, Hom.comp_id] at this
  unfold famV
  rw [dat_lamV, apZ_fnZ _ hamem, sem_fam_eq hW (Comp_el_typed ha).1 σ]
  exact happ k' σ a ha

theorem RE_pi_elim {A B f a : Tm} (hf : RE S k (.pi A B) f) (ha : RE S k A a) :
    RE S k (B.inst a) (.app f a) := by
  have hft := (Comp_el_typed hf).1
  obtain ⟨l, hpi⟩ := ty_of_tyEq hW (isTyK_of_ty hW hft) (TyEq.refl _) (fun l h => by cases h)
  have hA := HasTy.piDom hpi
  unfold RE at hf
  rw [semK_piT hW hpi, Comp_piC _ _ (semK_ne hW hA)] at hf
  obtain ⟨-, -, -, A1, B1, hE, hall⟩ := hf
  have hcl : (Tm.pi A1 B1).closedB 0 k = true := by
    rcases hE with h | ⟨l', h⟩
    · rw [← h]; exact closed_of_ty hW hpi
    · exact closed_of_ty hW (HasTy.eqR h)
  simp only [Tm.closedB, Bool.and_eq_true] at hcl
  have hA1 : A1.isub (ISub.id k) = A1 := isub_id_of_closed hcl.1
  have hB1 : B1.isub (ISub.id k) = B1 := isub_id_of_closed hcl.2
  have hf1 : f.isub (ISub.id k) = f := isub_id_of_closed (closed_of_ty hW hft)
  have hAA1 : TyEq S k A A1 := by
    rcases hE with h | ⟨l', h⟩
    · cases h; exact TyEq.refl _
    · exact .inr ⟨l', EqTm.piInjDom h⟩
  have hBB1 : TyEq S k (B1.inst a) (B.inst a) := by
    rcases hE with h | ⟨l', h⟩
    · cases h; exact TyEq.refl _
    · exact .inr ⟨l', EqTm.symm (EqTm.piInjCod h (Comp_el_typed ha).1)⟩
  have ha1 := ha.conv_ty hW hAA1
  have := hall k (ISub.id k) a (by
    simp only [ISub.id_comp, ISub.hom_id, Hom.comp_id, hA1]
    unfold RE at ha1; rwa [← semK_tyEq hW hAA1] at ha1)
  simp only [ISub.id_comp, ISub.hom_id, Hom.comp_id, hB1, hf1] at this
  have hamem : semK S k a ∈ El (semK S k A) (Hom.id k) := by
    have := (Comp_el_typed ha).2; rwa [El_res, Hom.comp_id] at this
  unfold famV at this
  rw [dat_lamV, apZ_fnZ _ hamem] at this
  have e := sem_fam_eq hW (B := B) (Comp_el_typed ha).1 (ISub.id k)
  have hBc := closed_of_ty hW hpi
  simp only [Tm.closedB, Bool.and_eq_true] at hBc
  rw [ISub.hom_id, isub_id_of_closed hBc.2] at e
  rw [e] at this
  exact (show RE S k (B1.inst a) (.app f a) from by
    unfold RE; rwa [← semK_tyEq hW hBB1] at this).conv_ty hW hBB1

theorem semK_sigmaT {A B : Tm} {l : ℕ} (h : HasTy S k .one [] (.sigma A B) (.univ l)) :
    semK S k (.sigma A B) = sigmaC k (semK S k A)
      (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) := by
  unfold semK; rw [sem_sigma (kv_semK_of_univ hW (HasTy.sigmaDom h))]

/-- The family code of a closed `Σ`/`Π` type, at a computable argument. -/
theorem fam_code_eq {A B a : Tm} {l : ℕ} (hA : HasTy S k .one [] A (.univ l)) (σ : ISub k' k)
    (ha : RE S k' (A.isub σ) a) :
    apZ (dat (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a))
      k' σ.hom) (semK S k' a) = semK S k' ((B.isub σ).inst a) := by
  have hamem : semK S k' a ∈ El (semK S k A) σ.hom := by
    have := (Comp_el_typed ha).2
    rwa [El_res, Hom.comp_id, semK_isubS hW hA, El_res, Hom.comp_id] at this
  unfold famV
  rw [dat_lamV, apZ_fnZ _ hamem, sem_fam_eq hW (Comp_el_typed ha).1 σ]

theorem RE_sigma_intro {A B p : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A B) (.univ l))
    (hp : HasTy S k .one [] p (.sigma A B)) (h1 : RE S k A (.fst p)) (h2 : RE S k (B.inst (.fst p)) (.snd p)) :
    RE S k (.sigma A B) p := by
  have hA := HasTy.sigmaDom hsig
  unfold RE
  rw [semK_sigmaT hW hsig, Comp_sigmaC _ _ (semK_ne hW hA)]
  refine ⟨hp, ?_, hp, A, B, TyEq.refl _, fun k' σ => ?_⟩
  · rw [← semK_sigmaT hW hsig, res_id (kv_semK_of_univ hW hsig)]; exact mem_of_ty hW hp
  simp only [ISub.id_comp, Hom.id_comp, ISub.hom_id]
  have h1σ := h1.isub hW σ
  rw [isub_fst] at h1σ
  refine ⟨by rw [Comp_res_el hW hA]; exact h1σ, ?_⟩
  rw [fam_code_eq hW hA σ h1σ]
  have := h2.isub hW σ
  rwa [isub_inst, isub_snd, isub_fst] at this

theorem RE_sigma_elim {A B p : Tm} (hp : RE S k (.sigma A B) p) :
    RE S k A (.fst p) ∧ RE S k (B.inst (.fst p)) (.snd p) := by
  have hpt := (Comp_el_typed hp).1
  obtain ⟨l, hsig⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpt) (TyEq.refl _) (fun l h => by cases h)
  have hA := HasTy.sigmaDom hsig
  unfold RE at hp
  rw [semK_sigmaT hW hsig, Comp_sigmaC _ _ (semK_ne hW hA)] at hp
  obtain ⟨-, -, -, A1, B1, hE, hall⟩ := hp
  have hcl : (Tm.sigma A1 B1).closedB 0 k = true := by
    rcases hE with h | ⟨l', h⟩
    · rw [← h]; exact closed_of_ty hW hsig
    · exact closed_of_ty hW (HasTy.eqR h)
  simp only [Tm.closedB, Bool.and_eq_true] at hcl
  have hp1 : p.isub (ISub.id k) = p := isub_id_of_closed (closed_of_ty hW hpt)
  have hA1 : A1.isub (ISub.id k) = A1 := isub_id_of_closed hcl.1
  have hB1 : B1.isub (ISub.id k) = B1 := isub_id_of_closed hcl.2
  have hAA1 : TyEq S k A A1 := by
    rcases hE with h | ⟨l', h⟩
    · cases h; exact TyEq.refl _
    · exact .inr ⟨l', EqTm.sigmaInjDom h⟩
  obtain ⟨h1, h2⟩ := hall k (ISub.id k)
  simp only [ISub.id_comp, ISub.hom_id, Hom.comp_id, hA1, hB1, hp1] at h1 h2
  have h1' : RE S k A1 (.fst p) := by unfold RE; rwa [← semK_tyEq hW hAA1]
  have hfst := h1'.conv_ty hW hAA1.symm
  refine ⟨hfst, ?_⟩
  have hBB1 : TyEq S k (B1.inst (.fst p)) (B.inst (.fst p)) := by
    rcases hE with h | ⟨l', h⟩
    · cases h; exact TyEq.refl _
    · exact .inr ⟨l', EqTm.symm (EqTm.sigmaInjCod h (Comp_el_typed hfst).1)⟩
  have hfam := fam_code_eq hW (B := B) hA (ISub.id k) (by rw [isub_id_of_closed (closed_of_ty hW hA)]; exact hfst)
  have hBc := closed_of_ty hW hsig
  simp only [Tm.closedB, Bool.and_eq_true] at hBc
  rw [ISub.hom_id, isub_id_of_closed hBc.2] at hfam
  rw [hfam] at h2
  exact (show RE S k (B1.inst (.fst p)) (.snd p) from by
    unfold RE; rwa [← semK_tyEq hW hBB1] at h2).conv_ty hW hBB1

theorem RT_pi_intro {A B : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A B) (.univ l))
    (hA : ∀ k' (σ : ISub k' k), RT S k' (A.isub σ))
    (hB : ∀ k' (σ : ISub k' k) a, RE S k' (A.isub σ) a → RT S k' ((B.isub σ).inst a)) :
    RT S k (.pi A B) := by
  have hA0 := HasTy.piDom hpi
  unfold RT
  rw [semK_piT hW hpi, Comp_piC _ _ (semK_ne hW hA0)]
  refine ⟨⟨⟨l, .inl hpi⟩, ?_⟩, A, B, TyEq.refl _, fun k' σ => ?_⟩
  · rw [← semK_piT hW hpi, res_id (kv_semK_of_univ hW hpi)]
  simp only [Hom.id_comp, Comp_res_el hW hA0]
  refine ⟨hA k' σ, fun a ha => ?_⟩
  rw [fam_code_eq hW hA0 σ ha]; exact hB k' σ a ha

theorem RT_sigma_intro {A B : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A B) (.univ l))
    (hA : ∀ k' (σ : ISub k' k), RT S k' (A.isub σ))
    (hB : ∀ k' (σ : ISub k' k) a, RE S k' (A.isub σ) a → RT S k' ((B.isub σ).inst a)) :
    RT S k (.sigma A B) := by
  have hA0 := HasTy.sigmaDom hsig
  unfold RT
  rw [semK_sigmaT hW hsig, Comp_sigmaC _ _ (semK_ne hW hA0)]
  refine ⟨⟨⟨l, .inl hsig⟩, ?_⟩, A, B, TyEq.refl _, fun k' σ => ?_⟩
  · rw [← semK_sigmaT hW hsig, res_id (kv_semK_of_univ hW hsig)]
  simp only [Hom.id_comp, Comp_res_el hW hA0]
  refine ⟨hA k' σ, fun a ha => ?_⟩
  rw [fam_code_eq hW hA0 σ ha]; exact hB k' σ a ha

end

end Model.Canon
