import Model.Whnf.Kan2Line

/-!
# The binary Kan operations at Σ-types
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The structure of a pair of related types whose normal forms are Σ-types. -/
structure SigmaStr (S : Sig) (k : ℕ) (T T' : Tm) : Prop where
  tyEq : TyEq S k T T'
  whnf : ∀ k' (ρ : ISub k' k), ∃ A1 B1 A1' B1', RedT S k' (T.isub ρ) (.sigma A1 B1) ∧
    RedT S k' (T'.isub ρ) (.sigma A1' B1') ∧ RT2 S k' A1 A1' ∧ ∀ a a', RE2 S k' A1 a a' → RT2 S k' (B1.inst a) (B1'.inst a')
  coh : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') A1 B1 A2 B2, RedT S k' (T.isub ρ) (.sigma A1 B1) →
    RedT S k'' (T.isub (ρ.comp ρ')) (.sigma A2 B2) →
    RT2 S k'' (A1.isub ρ') A2 ∧ ∀ a a', RE2 S k'' (A1.isub ρ') a a' → RT2 S k'' ((B1.isub ρ').inst a) (B2.inst a')
  coh' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') A1 B1 A2 B2, RedT S k' (T'.isub ρ) (.sigma A1 B1) →
    RedT S k'' (T'.isub (ρ.comp ρ')) (.sigma A2 B2) →
    RT2 S k'' (A1.isub ρ') A2 ∧ ∀ a a', RE2 S k'' (A1.isub ρ') a a' → RT2 S k'' ((B1.isub ρ').inst a) (B2.inst a')
  elim : ∀ k' (ρ : ISub k' k) A1 B1 f f', RedT S k' (T.isub ρ) (.sigma A1 B1) → RE2 S k' (T.isub ρ) f f' →
    RE2 S k' A1 (.fst f) (.fst f') ∧ RE2 S k' (B1.inst (.fst f)) (.snd f) (.snd f')

variable (hW : WfSig S)
include hW

theorem SigmaStr_of {T T' A B : Tm} {l : ℕ} (h : RT2 S k T T') (hR : RedT S k T (.sigma A B))
    (hsig : HasTy S k .one [] (.sigma A B) (.univ l)) : SigmaStr S k T T' := by
  have hAne := semK_ne hW (HasTy.sigmaDom hsig)
  have hX : semK S k T = sigmaC k (semK S k A)
      (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) :=
    (semK_tyEq hW hR.2).trans (semK_sigmaT hW hsig)
  have hT := h
  unfold RT2 at hT
  rw [hX, Comp2_sigmaC _ _ hAne] at hT
  obtain ⟨hbase, hall, hcoh, hcoh', -, -⟩ := hT
  refine ⟨hbase.2.2.2.2, fun k' ρ => ?_, fun k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 => ?_,
    fun k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 => ?_, fun k' ρ A1 B1 f f' h1 hf => ?_⟩
  · obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' ρ
    refine ⟨A1, B1, A1', B1', h1, h2, Comp2_ty_RT2 h3, fun a a' ha => Comp2_ty_RT2 (h4 a a' ?_)⟩
    exact (Comp2_el_iff hAne (Comp2_ty_base h3).2.2.2.1).2 ha
  · obtain ⟨c1, c2⟩ := hcoh k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2
    refine ⟨Comp2_ty_RT2 c1, fun a a' ha => Comp2_ty_RT2 (c2 a a' ?_)⟩
    exact (Comp2_el_iff hAne (Comp2_ty_base c1).2.2.2.1).2 ha
  · obtain ⟨c1, c2⟩ := hcoh' k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2
    refine ⟨Comp2_ty_RT2 c1, fun a a' ha => Comp2_ty_RT2 (c2 a a' ?_)⟩
    exact (Comp2_el_iff hAne (Comp2_ty_base c1).2.2.2.1).2 ha
  · have hTρ : semK S k' (T.isub ρ) = res ρ.hom (semK S k T) :=
      semK_isubTy hW (Comp2_ty_base (show RT2 S k T T' from h)).2.1 ρ
    have hf2 : (Comp2 S (sigmaC k (semK S k A) (famV k (semK S k A) fun k' g a =>
        sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a))) k k' ρ.hom).el (T.isub ρ) f f' := by
      rw [Comp2_eq_res (show sigmaC k (semK S k A) (famV k (semK S k A) fun k' g a =>
        sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) ≠ ∅ from mkKV_ne_empty _), ← hX, ← hTρ]
      exact hf
    obtain ⟨A3, B3, h3, hfst, hsnd⟩ := sigmaC_el_at hAne hW hf2
    obtain ⟨rfl, rfl⟩ : A3 = A1 ∧ B3 = B1 := by
      have := RedW.unique h3.1 h1.1; injection this; constructor <;> assumption
    obtain ⟨A4, B4, A4', B4', h4, -, hd, hc⟩ := hall k' ρ
    obtain ⟨rfl, rfl⟩ : A4 = A3 ∧ B4 = B3 := by
      have := RedW.unique h4.1 h1.1; injection this; constructor <;> assumption
    have hb := Comp2_ty_base hd
    rw [Hom.id_comp] at hd
    refine ⟨(Comp2_el_iff hAne (by rw [Hom.id_comp] at hb; exact hb.2.2.2.1)).1 hfst, ?_⟩
    have haa : (Comp2 S (semK S k A) k k' ρ.hom).el A4 (.fst f) (.fst f) :=
      (per2_tyCode hW (tyCode_of_univ hW (HasTy.sigmaDom hsig)) k' _ |>.reflEl) hd hfst
    have hcb := Comp2_ty_base (hc _ _ (by rw [Hom.id_comp]; exact haa))
    rw [Hom.id_comp] at hcb
    exact (Comp2_el_iff hcb.1 hcb.2.2.2.1).1 hsnd

theorem SigmaStr.isub {T T' : Tm} (hP : SigmaStr S k T T') (σ : ISub k' k) :
    SigmaStr S k' (T.isub σ) (T'.isub σ) where
  tyEq := hP.tyEq.isub hW σ
  whnf k'' ρ := by simpa only [Tm.isub_isub] using hP.whnf k'' (σ.comp ρ)
  coh k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh k1 (σ.comp ρ) k2 ρ' A1 B1 A2 B2 h1 h2
  coh' k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh' k1 (σ.comp ρ) k2 ρ' A1 B1 A2 B2 h1 h2
  elim k1 ρ A1 B1 f f' h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    exact hP.elim k1 (σ.comp ρ) A1 B1 f f' h1 h2

/-- Related elements of a type whose normal form is a Σ-type, through their projections. -/
theorem RE2_sigmaW_intro {T A B t t' : Tm} {l : ℕ} (hTT : RT2 S k T T) (hR : RedT S k T (.sigma A B))
    (hsig : HasTy S k .one [] (.sigma A B) (.univ l)) (hE : EB S k T t t')
    (hpr : ∀ k' (ρ : ISub k' k) A1 B1, RedT S k' (T.isub ρ) (.sigma A1 B1) →
      RE2 S k' A1 (.fst (t.isub ρ)) (.fst (t'.isub ρ)) ∧
      RE2 S k' (B1.inst (.fst (t.isub ρ))) (.snd (t.isub ρ)) (.snd (t'.isub ρ))) :
    RE2 S k T t t' := by
  have hAne := semK_ne hW (HasTy.sigmaDom hsig)
  have hX : semK S k T = sigmaC k (semK S k A)
      (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) :=
    (semK_tyEq hW hR.2).trans (semK_sigmaT hW hsig)
  have hT := hTT
  unfold RT2 at hT
  rw [hX, Comp2_sigmaC _ _ hAne] at hT
  obtain ⟨-, hall, -, -⟩ := hT
  unfold RE2
  rw [hX, Comp2_sigmaC _ _ hAne]
  refine ⟨hE, ?_, hE, fun k' ρ => ?_⟩
  · rw [← hX, res_id (by rw [hX]; exact isKV_mkKV _)]; exact mem_of_ty hW hE.1
  obtain ⟨A1, B1, A1', B1', h1, -, hd, hc⟩ := hall k' ρ
  obtain ⟨p1, p2⟩ := hpr k' ρ A1 B1 h1
  refine ⟨A1, B1, h1, ?_, ?_⟩
  · simp only [ISub.id_comp, Hom.id_comp] at hd ⊢
    exact (Comp2_el_iff hAne (Comp2_ty_base hd).2.2.2.1).2 p1
  · simp only [ISub.id_comp, Hom.id_comp] at hd hc ⊢
    have haa := (per2_tyCode hW (tyCode_of_univ hW (HasTy.sigmaDom hsig)) k' ρ.hom).reflEl hd
      ((Comp2_el_iff hAne (Comp2_ty_base hd).2.2.2.1).2 p1)
    have hcb := Comp2_ty_base (hc _ _ haa)
    rw [ISub.hom_id]
    exact (Comp2_el_iff hcb.1 hcb.2.2.2.1).2 p2

end

end Model.Whnf
