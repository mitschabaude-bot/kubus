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

section sigma
variable (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
  (hD : ∀ k' (σ : ISub k' k), PERP (D k' σ))
  (hC : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → PERP (C k' σ a k' (ISub.id k')))
  (hCa : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → C k' σ a = C k' σ a')
include hD hC hCa

/-- The element relation of a `Σ` family. -/
abbrev sigEl (A t t' : Tm) : Prop :=
  sigmaE2 S (fun k' σ => (D k' σ).el) (fun k' σ a k'' σ' => (C k' σ a k'' σ').el) k (ISub.id k) A t t'

/-- The type relation of a `Σ` family. -/
def sigT (A A' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1', RedW S (A.isub σ) (.sigma A1 B1) ∧ RedW S (A'.isub σ) (.sigma A1' B1') ∧
    (D k' σ).ty A1 A1' ∧ ∀ a a', (D k' σ).el A1 a a' → (C k' σ a k' (ISub.id k')).ty (B1.inst a) (B1'.inst a')

theorem sig_symTy {A A' : Tm} (hT : sigT (S := S) D C A A') : sigT (S := S) D C A' A := by
  intro k' σ
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hT k' σ
  have P := hD k' σ
  refine ⟨A1', B1', A1, B1, h2, h1, P.symTy h3, fun a a' ha => ?_⟩
  have ha' : (D k' σ).el A1 a' a := P.conv (P.symTy h3) (P.symEl (P.symTy h3) ha)
  have := (hC k' σ _ a' a ha').symTy (h4 a' a ha')
  rwa [hCa k' σ _ a' a ha'] at this

theorem sig_transTy {A A' A'' : Tm} (hT : sigT (S := S) D C A A') (hT' : sigT (S := S) D C A' A'') :
    sigT (S := S) D C A A'' := by
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

theorem sig_symEl {A A' t t' : Tm} (hT : sigT (S := S) D C A A') (ht : sigEl (S := S) D C A t t') :
    sigEl (S := S) D C A t' t := by
  obtain ⟨he, hall⟩ := ht
  refine ⟨he.symm, fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hr, hfst, hsnd⟩ := hall k'' σ'
  obtain ⟨A1x, B1x, A1', B1', hrx, -, h3, h4⟩ := hT k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
  simp only [ISub.id_comp] at hfst hsnd ⊢
  have P := hD k'' σ'
  refine ⟨A1x, B1x, hr, P.symEl h3 hfst, ?_⟩
  have y := (hC k'' σ' _ _ _ hfst).symEl (h4 _ _ (P.reflEl h3 hfst)) hsnd
  have c := (hC k'' σ' _ _ _ hfst).symTy (cod_conv D C hD hC hCa h3 h4 hfst)
  have := (hC k'' σ' _ _ _ hfst).conv c y
  rwa [hCa k'' σ' _ _ _ hfst] at this

theorem sig_transEl {A A' t t' t'' : Tm} (hT : sigT (S := S) D C A A') (ht : sigEl (S := S) D C A t t')
    (ht' : sigEl (S := S) D C A t' t'') : sigEl (S := S) D C A t t'' := by
  obtain ⟨he, hall⟩ := ht
  obtain ⟨he', hall'⟩ := ht'
  refine ⟨he.trans he', fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hr, hfst, hsnd⟩ := hall k'' σ'
  obtain ⟨A1x, B1x, hrx, hfst', hsnd'⟩ := hall' k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
  obtain ⟨A1y, B1y, A1', B1', hry, -, h3, h4⟩ := hT k'' σ'
  obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
    have := RedW.unique hry hr; injection this with e1 e2; exact ⟨e1, e2⟩
  simp only [ISub.id_comp] at hfst hsnd hfst' hsnd' ⊢
  have P := hD k'' σ'
  refine ⟨A1y, B1y, hr, P.transEl h3 hfst hfst', ?_⟩
  rw [← hCa k'' σ' _ _ _ hfst] at hsnd'
  have c := cod_conv D C hD hC hCa h3 h4 hfst
  exact (hC k'' σ' _ _ _ hfst).transEl (h4 _ _ (P.reflEl h3 hfst)) hsnd ((hC k'' σ' _ _ _ hfst).conv c hsnd')

omit hCa in
theorem sig_conv {A A' t t' : Tm} (hT : sigT (S := S) D C A A') (hE : TyEq S k A A')
    (ht : sigEl (S := S) D C A t t') : sigEl (S := S) D C A' t t' := by
  obtain ⟨he, hall⟩ := ht
  refine ⟨he.conv hE, fun k'' σ' => ?_⟩
  obtain ⟨A1, B1, hr, hfst, hsnd⟩ := hall k'' σ'
  obtain ⟨A1x, B1x, A1', B1', hrx, hr', h3, h4⟩ := hT k'' σ'
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
  simp only [ISub.id_comp] at hfst hsnd ⊢
  have P := hD k'' σ'
  exact ⟨A1', B1', hr', P.conv h3 hfst, (hC k'' σ' _ _ _ hfst).conv (h4 _ _ (P.reflEl h3 hfst)) hsnd⟩

end sigma

section path
variable (Lp : (k' : ℕ) → ISub k' (k + 1) → Pack2) (hL : ∀ k' (σ : ISub k' (k + 1)), PERP (Lp k' σ))
  (hLt : ∀ k' (σ : ISub k' k) (L1 L1' : Tm), (Lp (k' + 1) σ.up).ty L1 L1' → ∀ (r : I) (hr : r.Scoped k'),
    (Lp k' (ISub.cons r hr σ)).ty (L1.dinst r) (L1'.dinst r))
include hL hLt

/-- The element relation of path types over a family of lines. -/
abbrev pathEl (A t t' : Tm) : Prop := pathE2 S (fun k' σ => (Lp k' σ).el) k (ISub.id k) A t t'

/-- The type relation of path types over a family of lines. -/
def pathT (A A' : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), ∃ L1 b0 b1 L1' b0' b1',
    RedW S (A.isub σ) (.path L1 b0 b1) ∧ RedW S (A'.isub σ) (.path L1' b0' b1') ∧
    (Lp (k' + 1) σ.up).ty L1 L1' ∧
    (Lp k' (ISub.cons .zero trivial σ)).el (L1.dinst .zero) b0 b0' ∧
    (Lp k' (ISub.cons .one trivial σ)).el (L1.dinst .one) b1 b1'

theorem path_symTy {A A' : Tm} (hT : pathT (S := S) Lp A A') : pathT (S := S) Lp A' A := by
  intro k' σ
  obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, h4, h5⟩ := hT k' σ
  have P0 := hL k' (ISub.cons .zero trivial σ)
  have P1 := hL k' (ISub.cons .one trivial σ)
  have c0 := hLt k' σ _ _ h3 .zero trivial
  have c1 := hLt k' σ _ _ h3 .one trivial
  exact ⟨L1', b0', b1', L1, b0, b1, h2, h1, (hL _ _).symTy h3, P0.conv c0 (P0.symEl c0 h4),
    P1.conv c1 (P1.symEl c1 h5)⟩

theorem path_transTy {A A' A'' : Tm} (hT : pathT (S := S) Lp A A') (hT' : pathT (S := S) Lp A' A'') :
    pathT (S := S) Lp A A'' := by
  intro k' σ
  obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, h4, h5⟩ := hT k' σ
  obtain ⟨L2, c0, c1, L2', c0', c1', h1', h2', h3', h4', h5'⟩ := hT' k' σ
  obtain ⟨rfl, rfl, rfl⟩ : L1' = L2 ∧ b0' = c0 ∧ b1' = c1 := by
    have := RedW.unique h2 h1'; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
  have P0 := hL k' (ISub.cons .zero trivial σ)
  have P1 := hL k' (ISub.cons .one trivial σ)
  have d0 := hLt k' σ _ _ h3 .zero trivial
  have d1 := hLt k' σ _ _ h3 .one trivial
  exact ⟨L1, b0, b1, L2', c0', c1', h1, h2', (hL _ _).transTy h3 h3',
    P0.transEl d0 h4 (P0.conv (P0.symTy d0) h4'), P1.transEl d1 h5 (P1.conv (P1.symTy d1) h5')⟩

theorem path_symEl {A A' t t' : Tm} (hT : pathT (S := S) Lp A A') (ht : pathEl (S := S) Lp A t t') :
    pathEl (S := S) Lp A t' t := by
  obtain ⟨he, hall⟩ := ht
  refine ⟨he.symm, fun k'' σ' => ?_⟩
  obtain ⟨L1, b0, b1, hr, hel⟩ := hall k'' σ'
  obtain ⟨L1x, b0x, b1x, L1', b0', b1', hrx, -, h3, -⟩ := hT k'' σ'
  obtain ⟨rfl, rfl, rfl⟩ : L1x = L1 ∧ b0x = b0 ∧ b1x = b1 := by
    have := RedW.unique hrx hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
  refine ⟨L1x, b0x, b1x, hr, fun r hr' => ?_⟩
  have := hel r hr'
  simp only [ISub.id_comp] at this ⊢
  exact (hL _ _).symEl (hLt k'' σ' _ _ h3 r hr') this

theorem path_transEl {A A' t t' t'' : Tm} (hT : pathT (S := S) Lp A A') (ht : pathEl (S := S) Lp A t t')
    (ht' : pathEl (S := S) Lp A t' t'') : pathEl (S := S) Lp A t t'' := by
  obtain ⟨he, hall⟩ := ht
  obtain ⟨he', hall'⟩ := ht'
  refine ⟨he.trans he', fun k'' σ' => ?_⟩
  obtain ⟨L1, b0, b1, hr, hel⟩ := hall k'' σ'
  obtain ⟨L1x, b0x, b1x, hrx, hel'⟩ := hall' k'' σ'
  obtain ⟨rfl, rfl, rfl⟩ : L1x = L1 ∧ b0x = b0 ∧ b1x = b1 := by
    have := RedW.unique hrx hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
  obtain ⟨L1y, b0y, b1y, L1', b0', b1', hry, -, h3, -⟩ := hT k'' σ'
  obtain ⟨rfl, rfl, rfl⟩ : L1y = L1x ∧ b0y = b0x ∧ b1y = b1x := by
    have := RedW.unique hry hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
  refine ⟨L1y, b0y, b1y, hr, fun r hr' => ?_⟩
  have x := hel r hr'
  have y := hel' r hr'
  simp only [ISub.id_comp] at x y ⊢
  exact (hL _ _).transEl (hLt k'' σ' _ _ h3 r hr') x y

theorem path_conv {A A' t t' : Tm} (hT : pathT (S := S) Lp A A') (hE : TyEq S k A A')
    (ht : pathEl (S := S) Lp A t t') : pathEl (S := S) Lp A' t t' := by
  obtain ⟨he, hall⟩ := ht
  refine ⟨he.conv hE, fun k'' σ' => ?_⟩
  obtain ⟨L1, b0, b1, hr, hel⟩ := hall k'' σ'
  obtain ⟨L1x, b0x, b1x, L1', b0', b1', hrx, hr2, h3, -⟩ := hT k'' σ'
  obtain ⟨rfl, rfl, rfl⟩ : L1x = L1 ∧ b0x = b0 ∧ b1x = b1 := by
    have := RedW.unique hrx hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
  refine ⟨L1', b0', b1', hr2, fun r hr' => ?_⟩
  have x := hel r hr'
  simp only [ISub.id_comp] at x ⊢
  exact (hL _ _).conv (hLt k'' σ' _ _ h3 r hr') x

end path

variable (hW : WfSig S)
include hW

/-- The pack of a `Π` family, with judgmentally equal types. -/
def piPack (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2) :
    Pack2 := ⟨fun A A' => TyEq S k A A' ∧ piT (S := S) D C A A', piEl (S := S) D C⟩

theorem piPack_per (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
    (hD : ∀ k' (σ : ISub k' k), PERP (D k' σ))
    (hC : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → PERP (C k' σ a k' (ISub.id k')))
    (hCa : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → C k' σ a = C k' σ a') :
    PERP (piPack (S := S) D C) :=
  ⟨fun hT => ⟨hT.1.symm, pi_symTy D C hD hC hCa hT.2⟩,
    fun hT hT' => ⟨hT.1.trans hW hT'.1, pi_transTy D C hD hC hCa hT.2 hT'.2⟩,
    fun hT ht => pi_symEl D C hD hC hCa hT.2 ht,
    fun hT ht ht' => pi_transEl D C hD hC hCa hT.2 ht ht',
    fun hT ht => pi_conv D C hD hC hT.2 hT.1 ht⟩

/-- The pack of a `Σ` family, with judgmentally equal types. -/
def sigPack (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2) :
    Pack2 := ⟨fun A A' => TyEq S k A A' ∧ sigT (S := S) D C A A', sigEl (S := S) D C⟩

theorem sigPack_per (D : (k' : ℕ) → ISub k' k → Pack2) (C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2)
    (hD : ∀ k' (σ : ISub k' k), PERP (D k' σ))
    (hC : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → PERP (C k' σ a k' (ISub.id k')))
    (hCa : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → C k' σ a = C k' σ a') :
    PERP (sigPack (S := S) D C) :=
  ⟨fun hT => ⟨hT.1.symm, sig_symTy D C hD hC hCa hT.2⟩,
    fun hT hT' => ⟨hT.1.trans hW hT'.1, sig_transTy D C hD hC hCa hT.2 hT'.2⟩,
    fun hT ht => sig_symEl D C hD hC hCa hT.2 ht,
    fun hT ht ht' => sig_transEl D C hD hC hCa hT.2 ht ht',
    fun hT ht => sig_conv D C hD hC hT.2 hT.1 ht⟩

/-- The pack of path types over a family of lines, with judgmentally equal types. -/
def pathPack (Lp : (k' : ℕ) → ISub k' (k + 1) → Pack2) : Pack2 :=
  ⟨fun A A' => TyEq S k A A' ∧ pathT (S := S) Lp A A', pathEl (S := S) Lp⟩

theorem pathPack_per (Lp : (k' : ℕ) → ISub k' (k + 1) → Pack2) (hL : ∀ k' (σ : ISub k' (k + 1)), PERP (Lp k' σ))
    (hLt : ∀ k' (σ : ISub k' k) (L1 L1' : Tm), (Lp (k' + 1) σ.up).ty L1 L1' → ∀ (r : I) (hr : r.Scoped k'),
      (Lp k' (ISub.cons r hr σ)).ty (L1.dinst r) (L1'.dinst r)) :
    PERP (pathPack (S := S) Lp) :=
  ⟨fun hT => ⟨hT.1.symm, path_symTy Lp hL hLt hT.2⟩,
    fun hT hT' => ⟨hT.1.trans hW hT'.1, path_transTy Lp hL hLt hT.2 hT'.2⟩,
    fun hT ht => path_symEl Lp hL hLt hT.2 ht,
    fun hT ht ht' => path_transEl Lp hL hLt hT.2 ht ht',
    fun hT ht => path_conv Lp hL hLt hT.2 hT.1 ht⟩

end

end Model.Whnf
