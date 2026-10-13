import Model.Whnf.Unfold2

/-!
# PER properties of the relations of `Π`, `Σ` and path types, from those of their parts

Stated for families of packs (`D` for the domain, `C` for the codomain at an argument), so that they
apply to the codes of the type formers and to the relations of `equiv T A` in Glue types.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- The PER properties of a pair of relations. -/
structure PERP (R : Pack2) : Prop where
  symTy : ∀ {A A'}, R.ty A A' → R.ty A' A
  transTy : ∀ {A A' A''}, R.ty A A' → R.ty A' A'' → R.ty A A''
  symEl : ∀ {A A' t t'}, R.ty A A' → R.el A t t' → R.el A t' t
  transEl : ∀ {A A' t t' t''}, R.ty A A' → R.el A t t' → R.el A t' t'' → R.el A t t''
  conv : ∀ {A A' t t'}, R.ty A A' → R.el A t t' → R.el A' t t'

namespace PERP
variable {R : Pack2} (h : PERP R)
include h

theorem reflTy {A A' : Tm} (hA : R.ty A A') : R.ty A A := h.transTy hA (h.symTy hA)
theorem reflTy' {A A' : Tm} (hA : R.ty A A') : R.ty A' A' := h.transTy (h.symTy hA) hA
theorem reflEl {A A' t t' : Tm} (hA : R.ty A A') (ht : R.el A t t') : R.el A t t :=
  h.transEl hA ht (h.symEl hA ht)
theorem reflEl' {A A' t t' : Tm} (hA : R.ty A A') (ht : R.el A t t') : R.el A t' t' :=
  h.transEl hA (h.symEl hA ht) ht
end PERP

theorem EB.symm {A t t' : Tm} (h : EB S k A t t') : EB S k A t' t := ⟨h.2.1, h.1, EqTm.symm h.2.2⟩
theorem EB.trans {A t t' t'' : Tm} (h : EB S k A t t') (h' : EB S k A t' t'') : EB S k A t t'' :=
  ⟨h.1, h'.2.1, h.2.2.trans h'.2.2⟩
theorem EB.conv {A A' t t' : Tm} (h : EB S k A t t') (e : TyEq S k A A') : EB S k A' t t' :=
  ⟨h.1.tyConv e, h.2.1.tyConv e, h.2.2.tyConv e⟩



section family
variable (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
  (hD : ∀ k' (σ : ISub k' k), PERP (D k' σ))
  (hC : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → PERP (C k' σ a k' (ISub.id k')))
  (hCa : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → C k' σ a = C k' σ a')

include hD hC hCa in
/-- Conversion of the codomains at related arguments, within the family of one side. -/
theorem cod_conv {k' : ℕ} {σ : ISub k' k} {A1 A1' B1 B1' : Tm} (hAA : (D k' σ).ty A1 A1')
    (hBB : ∀ a a', (D k' σ).el A1 a a' → (C k' σ a k' (ISub.id k')).ty (B1.inst a) (B1'.inst a'))
    {a a' : Tm} (ha : (D k' σ).el A1 a a') : (C k' σ a k' (ISub.id k')).ty (B1.inst a') (B1.inst a) := by
  have P := hD k' σ
  have ha' := P.symEl hAA ha
  have h1 := hBB a' a ha'
  rw [hCa k' σ _ a' a ha'] at h1
  have h2 := hBB a a (P.reflEl hAA ha)
  exact (hC k' σ _ a a' ha).transTy h1 ((hC k' σ _ a a' ha).symTy h2)

end family

section pi
variable (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
  (hD : ∀ k' (σ : ISub k' k), PERP (D k' σ))
  (hC : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → PERP (C k' σ a k' (ISub.id k')))
  (hCa : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → C k' σ a = C k' σ a')
include hD hC hCa

/-- The element relation of a `Π` family. -/
abbrev piEl (A t t' : Tm) : Prop :=
  piE2 S (fun k' σ => (D k' σ).el) (fun k' σ a k'' σ' => (C k' σ a k'' σ').el) k (ISub.id k) A t t'

/-- The type relation of a `Π` family. -/
def piT (A A' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1', RedW S (A.isub σ) (.pi A1 B1) ∧ RedW S (A'.isub σ) (.pi A1' B1') ∧
    (D k' σ).ty A1 A1' ∧ ∀ a a', (D k' σ).el A1 a a' → (C k' σ a k' (ISub.id k')).ty (B1.inst a) (B1'.inst a')

theorem pi_symTy {A A' : Tm} (hT : piT (S := S) D C A A') : piT (S := S) D C A' A := by
  intro k' σ
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hT k' σ
  have P := hD k' σ
  refine ⟨A1', B1', A1, B1, h2, h1, P.symTy h3, fun a a' ha => ?_⟩
  have ha' : (D k' σ).el A1 a' a := P.conv (P.symTy h3) (P.symEl (P.symTy h3) ha)
  have := (hC k' σ _ a' a ha').symTy (h4 a' a ha')
  rwa [hCa k' σ _ a' a ha'] at this

theorem pi_transTy {A A' A'' : Tm} (hT : piT (S := S) D C A A') (hT' : piT (S := S) D C A' A'') :
    piT (S := S) D C A A'' := by
  intro k' σ
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hT k' σ
  obtain ⟨A2, B2, A2', B2', h1', h2', h3', h4'⟩ := hT' k' σ
  obtain ⟨rfl, rfl⟩ : A1' = A2 ∧ B1' = B2 := by
    have := RedW.unique h2 h1'; injection this with e1 e2; exact ⟨e1, e2⟩
  have P := hD k' σ
  refine ⟨A1, B1, A2', B2', h1, h2', P.transTy h3 h3', fun a a' ha => ?_⟩
  have ha2 : (D k' σ).el A1' a' a' := P.conv h3 (P.reflEl' (P.transTy h3 h3') ha)
  have e1 := h4 a a' (P.conv (P.reflTy h3) ha)
  have e2 := h4' a' a' ha2
  rw [← hCa k' σ _ a a' ha] at e2
  exact (hC k' σ _ a a' ha).transTy e1 e2

theorem pi_symEl {A A' t t' : Tm} (hT : piT (S := S) D C A A') (ht : piEl (S := S) D C A t t') :
    piEl (S := S) D C A t' t := by
  obtain ⟨he, hall⟩ := ht
  refine ⟨he.symm, fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hr, hel⟩ := hall k'' σ'
  obtain ⟨A1x, B1x, A1', B1', hrx, -, h3, h4⟩ := hT k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
  refine ⟨A1x, B1x, hr, fun a a' ha => ?_⟩
  simp only [ISub.id_comp] at ha hel ⊢
  have P := hD k'' σ'
  have ha' := P.symEl h3 ha
  have x := hel a' a ha'
  have y := (hC k'' σ' _ a' a ha').symEl (h4 a' a ha') x
  have c := (hC k'' σ' _ a' a ha').symTy (cod_conv D C hD hC hCa h3 h4 ha')
  have := (hC k'' σ' _ a' a ha').conv c y
  rwa [hCa k'' σ' _ a' a ha'] at this

theorem pi_transEl {A A' t t' t'' : Tm} (hT : piT (S := S) D C A A') (ht : piEl (S := S) D C A t t')
    (ht' : piEl (S := S) D C A t' t'') : piEl (S := S) D C A t t'' := by
  obtain ⟨he, hall⟩ := ht
  obtain ⟨he', hall'⟩ := ht'
  refine ⟨he.trans he', fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hr, hel⟩ := hall k'' σ'
  obtain ⟨A1x, B1x, hrx, hel'⟩ := hall' k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
  obtain ⟨A1y, B1y, A1', B1', hry, -, h3, h4⟩ := hT k'' σ'
  obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
    have := RedW.unique hry hr; injection this with e1 e2; exact ⟨e1, e2⟩
  refine ⟨A1y, B1y, hr, fun a a' ha => ?_⟩
  simp only [ISub.id_comp] at ha hel hel' ⊢
  have P := hD k'' σ'
  have x := hel a a' ha
  have y := hel' a' a' (P.reflEl' h3 ha)
  rw [← hCa k'' σ' _ a a' ha] at y
  have c := cod_conv D C hD hC hCa h3 h4 ha
  exact (hC k'' σ' _ a a' ha).transEl (h4 a a' ha) x ((hC k'' σ' _ a a' ha).conv c y)

omit hCa in
theorem pi_conv {A A' t t' : Tm} (hT : piT (S := S) D C A A') (hE : TyEq S k A A')
    (ht : piEl (S := S) D C A t t') : piEl (S := S) D C A' t t' := by
  obtain ⟨he, hall⟩ := ht
  refine ⟨he.conv hE, fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hr, hel⟩ := hall k'' σ'
  obtain ⟨A1x, B1x, A1', B1', hrx, hr', h3, h4⟩ := hT k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
  refine ⟨A1', B1', hr', fun a a' ha => ?_⟩
  simp only [ISub.id_comp] at ha hel ⊢
  have P := hD k'' σ'
  have ha1 := P.conv (P.symTy h3) ha
  have x := hel a a' ha1
  exact (hC k'' σ' _ a a' ha1).conv (h4 a a (P.reflEl (P.reflTy h3) ha1)) x

end pi

end

end Model.Whnf
