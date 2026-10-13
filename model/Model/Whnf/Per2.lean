import Model.Whnf.Data2
import Model.Whnf.Pack2
import Model.Canon.KanDerived

/-!
# The binary relation is a partial equivalence

Symmetry and transitivity of related types and elements, and transfer of related elements along
related types, by induction on codes.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-- The PER properties for a code at all its restrictions. -/
def PER2 (S : Sig) (m : ℕ) (X : V) : Prop := ∀ k (f : Hom k m), PERP (Comp2 S X m k f)

variable (hW : WfSig S)
include hW


omit hW in
theorem base_symm {X : V} {A A' : Tm}
    (h : IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = X ∧ semK S k A' = X ∧ TyEq S k A A') :
    IsTyK S k A' ∧ IsTyK S k A ∧ semK S k A' = X ∧ semK S k A = X ∧ TyEq S k A' A :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.symm⟩

theorem base_trans {X : V} {A A' A'' : Tm}
    (h : IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = X ∧ semK S k A' = X ∧ TyEq S k A A')
    (h' : IsTyK S k A' ∧ IsTyK S k A'' ∧ semK S k A' = X ∧ semK S k A'' = X ∧ TyEq S k A' A'') :
    IsTyK S k A ∧ IsTyK S k A'' ∧ semK S k A = X ∧ semK S k A'' = X ∧ TyEq S k A A'' :=
  ⟨h.1, h'.2.1, h.2.2.1, h'.2.2.2.1, h.2.2.2.2.trans hW h'.2.2.2.2⟩

/-- The relations of the fibres of a family of codes, at related arguments, share their code. -/
theorem fib_code {A : V} {f : Hom k m} {A1 a a' : Tm} (h : (Comp2 S A m k f).el A1 a a') :
    semK S k a = semK S k a' := semK_eq hW (Comp2_el h).1.2.2

omit hW in
theorem fib_mem {A : V} {f : Hom k m} {A1 a a' : Tm} (h : (Comp2 S A m k f).el A1 a a') :
    semK S k a ∈ El A f := by
  have := (Comp2_el h).2; rwa [El_res, Hom.comp_id] at this

/-- The PER properties at a `Π` code. -/
theorem per2_piC {A B : V} (hA : A ≠ ∅) (ihA : PER2 S m A)
    (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a)) : PER2 S m (piC m A B) := by
  intro k f
  rw [Comp2_piC A B hA]
  let D : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ => Comp2 S A m k' (f.comp σ.hom)
  let C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2 := fun k' σ a k'' σ' =>
    Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k'' σ'.hom
  have hD : ∀ k' (σ : ISub k' k), PERP (D k' σ) := fun k' σ => ihA k' _
  have hC : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → PERP (C k' σ a k' (ISub.id k')) :=
    fun k' σ _ _ _ ha => ihB k' _ _ (fib_mem ha) k' _
  have hCa : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → C k' σ a = C k' σ a' := by
    intro k' σ _ a a' ha; simp only [C, fib_code hW ha]
  have eT : ∀ T T', (∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1',
      RedW S (T.isub σ) (.pi A1 B1) ∧ RedW S (T'.isub σ) (.pi A1' B1') ∧
      (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1' ∧
        ∀ a a', (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
          (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a) (B1'.inst a')) ↔
      piT (S := S) D C T T' := by
    intro T T'; simp only [piT, D, C, ISub.hom_id]
  refine ⟨fun {T T'} hT => ⟨base_symm hT.1, (eT T' T).2 (pi_symTy D C hD hC hCa ((eT T T').1 hT.2))⟩,
    fun {T T' T''} hT hT' => ⟨base_trans hW hT.1 hT'.1,
      (eT T T'').2 (pi_transTy D C hD hC hCa ((eT T T').1 hT.2) ((eT T' T'').1 hT'.2))⟩,
    fun {T T' t t'} hT ht => ?_, fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    exact ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, pi_symEl D C hD hC hCa ((eT T T').1 hT.2) hpi⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    obtain ⟨he', -, hpi'⟩ := ht'
    exact ⟨he.trans he', hmem, pi_transEl D C hD hC hCa ((eT T T').1 hT.2) hpi hpi'⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    exact ⟨he.conv hT.1.2.2.2.2, hmem, pi_conv D C hD hC ((eT T T').1 hT.2) hT.1.2.2.2.2 hpi⟩

/-- The PER properties at a `Σ` code. -/
theorem per2_sigmaC {A B : V} (hA : A ≠ ∅) (ihA : PER2 S m A)
    (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a)) : PER2 S m (sigmaC m A B) := by
  intro k f
  rw [Comp2_sigmaC A B hA]
  -- the fibres
  have hB : ∀ k' (σ : ISub k' k) {A1 a a' : Tm}, (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
      PERP (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')) :=
    fun k' σ _ _ _ ha => ihB k' _ _ (fib_mem ha) k' (Hom.id k')
  -- conversion of the codomains at related arguments, within the family of one side
  have codConv : ∀ k' (σ : ISub k' k) {A1 A1' B1 B1' : Tm} (hAA : (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1')
      (hBB : ∀ a a', (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
        (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a) (B1'.inst a'))
      {a a' : Tm} (ha : (Comp2 S A m k' (f.comp σ.hom)).el A1 a a'),
      (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a') (B1.inst a) := by
    intro k' σ A1 A1' B1 B1' hAA hBB a a' ha
    have P := ihA k' (f.comp σ.hom)
    have ha' := P.symEl hAA ha
    have h1 := hBB a' a ha'
    rw [← fib_code hW ha] at h1
    have h2 := hBB a a (P.reflEl hAA ha)
    exact (hB k' σ ha).transTy h1 ((hB k' σ ha).symTy h2)
  refine ⟨fun {T T'} hT => ?_, fun {T T' T''} hT hT' => ?_, fun {T T' t t'} hT ht => ?_,
    fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · -- symmetry of types
    obtain ⟨hb, hall⟩ := hT
    refine ⟨base_symm hb, fun k' σ => ?_⟩
    obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' σ
    have P := ihA k' (f.comp σ.hom)
    refine ⟨A1', B1', A1, B1, h2, h1, P.symTy h3, fun a a' ha => ?_⟩
    have ha' : (Comp2 S A m k' (f.comp σ.hom)).el A1 a' a := P.conv (P.symTy h3) (P.symEl (P.symTy h3) ha)
    have := (hB k' σ ha').symTy (h4 a' a ha')
    rwa [fib_code hW ha'] at this
  · -- transitivity of types
    obtain ⟨hb, hall⟩ := hT
    obtain ⟨hb', hall'⟩ := hT'
    refine ⟨base_trans hW hb hb', fun k' σ => ?_⟩
    obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' σ
    obtain ⟨A2, B2, A2', B2', h1', h2', h3', h4'⟩ := hall' k' σ
    obtain ⟨rfl, rfl⟩ : A1' = A2 ∧ B1' = B2 := by
      have := RedW.unique h2 h1'; injection this with e1 e2; exact ⟨e1, e2⟩
    have P := ihA k' (f.comp σ.hom)
    refine ⟨A1, B1, A2', B2', h1, h2', P.transTy h3 h3', fun a a' ha => ?_⟩
    have ha2 : (Comp2 S A m k' (f.comp σ.hom)).el A1' a' a' :=
      P.conv h3 (P.reflEl' (P.transTy h3 h3') ha)
    have e1 := h4 a a' (P.conv (P.reflTy h3) ha)
    have e2 := h4' a' a' ha2
    rw [← fib_code hW ha] at e2
    exact (hB k' σ ha).transTy e1 e2
  · -- symmetry of elements
    obtain ⟨he, hmem, -, hall⟩ := ht
    refine ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, he.symm, fun k'' σ' => ?_⟩
    obtain ⟨A1, B1, hr, hfst, hsnd⟩ := hall k'' σ'
    obtain ⟨A1x, B1x, A1', B1', hrx, -, h3, h4⟩ := hT.2 k'' σ'
    obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
      have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
    simp only [ISub.id_comp, ISub.hom_id] at hfst hsnd ⊢
    have P := ihA k'' (f.comp σ'.hom)
    refine ⟨A1x, B1x, hr, P.symEl h3 hfst, ?_⟩
    have y := (hB k'' σ' hfst).symEl (h4 _ _ (P.reflEl h3 hfst)) hsnd
    have c := (hB k'' σ' hfst).symTy (codConv k'' σ' h3 h4 hfst)
    have := (hB k'' σ' hfst).conv c y
    rwa [fib_code hW hfst] at this
  · -- transitivity of elements
    obtain ⟨he, hmem, -, hall⟩ := ht
    obtain ⟨he', -, -, hall'⟩ := ht'
    refine ⟨he.trans he', hmem, he.trans he', fun k'' σ' => ?_⟩
    obtain ⟨A1, B1, hr, hfst, hsnd⟩ := hall k'' σ'
    obtain ⟨A1x, B1x, hrx, hfst', hsnd'⟩ := hall' k'' σ'
    obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
      have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
    obtain ⟨A1y, B1y, A1', B1', hry, -, h3, h4⟩ := hT.2 k'' σ'
    obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
      have := RedW.unique hry hr; injection this with e1 e2; exact ⟨e1, e2⟩
    simp only [ISub.id_comp, ISub.hom_id] at hfst hsnd hfst' hsnd' ⊢
    have P := ihA k'' (f.comp σ'.hom)
    refine ⟨A1y, B1y, hr, P.transEl h3 hfst hfst', ?_⟩
    rw [← fib_code hW hfst] at hsnd'
    have c := codConv k'' σ' h3 h4 hfst
    exact (hB k'' σ' hfst).transEl (h4 _ _ (P.reflEl h3 hfst)) hsnd ((hB k'' σ' hfst).conv c hsnd')
  · -- transfer along related types
    obtain ⟨he, hmem, -, hall⟩ := ht
    have hTT := hT.1.2.2.2.2
    refine ⟨he.conv hTT, hmem, he.conv hTT, fun k'' σ' => ?_⟩
    obtain ⟨A1, B1, hr, hfst, hsnd⟩ := hall k'' σ'
    obtain ⟨A1x, B1x, A1', B1', hrx, hr', h3, h4⟩ := hT.2 k'' σ'
    obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
      have := RedW.unique hrx hr; injection this with e1 e2; exact ⟨e1, e2⟩
    simp only [ISub.id_comp, ISub.hom_id] at hfst hsnd ⊢
    have P := ihA k'' (f.comp σ'.hom)
    exact ⟨A1', B1', hr', P.conv h3 hfst,
      (hB k'' σ' hfst).conv (h4 _ _ (P.reflEl h3 hfst)) hsnd⟩

/-- A related pair of type lines, at a point. -/
theorem line_ty {L : V} (hL : KR2 S (m + 1) L) {f : Hom k m} (σ : ISub k' k) {L1 L1' : Tm}
    (h : (Comp2 S L (m + 1) (k' + 1) ((Hom.lift f).comp σ.up.hom)).ty L1 L1') (r : I) (hr : r.Scoped k') :
    (Comp2 S L (m + 1) k' ((Hom.lift f).comp (ISub.cons r hr σ).hom)).ty (L1.dinst r) (L1'.dinst r) := by
  obtain ⟨-, h1, h2, -⟩ := Comp2_ty_base h
  have := (hL _ _ k' (ISub.cons r hr (ISub.id k')) L1 L1' L1 L1).1 h
  rw [Hom.comp_assoc, ← ISub.hom_comp, ISub.up_comp_cons_id, isub_cons_id_of_closed (closed_of_isTyK hW h1),
    isub_cons_id_of_closed (closed_of_isTyK hW h2)] at this
  exact this

/-- The PER properties at a path code. -/
theorem per2_pathC {L a0 a1 : V} (hLne : L ≠ ∅) (hL : KR2 S (m + 1) L) (ihL : PER2 S (m + 1) L) :
    PER2 S m (pathC m L a0 a1) := by
  intro k f
  rw [Comp2_pathC L a0 a1 hLne]
  refine ⟨fun {T T'} hT => ?_, fun {T T' T''} hT hT' => ?_, fun {T T' t t'} hT ht => ?_,
    fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨hb, hall⟩ := hT
    refine ⟨base_symm hb, fun k' σ => ?_⟩
    obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, h4, h5⟩ := hall k' σ
    have P0 := ihL k' ((Hom.lift f).comp (ISub.cons .zero trivial σ).hom)
    have P1 := ihL k' ((Hom.lift f).comp (ISub.cons .one trivial σ).hom)
    have c0 := line_ty hW hL σ h3 .zero trivial
    have c1 := line_ty hW hL σ h3 .one trivial
    exact ⟨L1', b0', b1', L1, b0, b1, h2, h1, (ihL _ _).symTy h3, P0.conv c0 (P0.symEl c0 h4),
      P1.conv c1 (P1.symEl c1 h5)⟩
  · obtain ⟨hb, hall⟩ := hT
    obtain ⟨hb', hall'⟩ := hT'
    refine ⟨base_trans hW hb hb', fun k' σ => ?_⟩
    obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, h4, h5⟩ := hall k' σ
    obtain ⟨L2, c0, c1, L2', c0', c1', h1', h2', h3', h4', h5'⟩ := hall' k' σ
    obtain ⟨rfl, rfl, rfl⟩ : L1' = L2 ∧ b0' = c0 ∧ b1' = c1 := by
      have := RedW.unique h2 h1'; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
    have P0 := ihL k' ((Hom.lift f).comp (ISub.cons .zero trivial σ).hom)
    have P1 := ihL k' ((Hom.lift f).comp (ISub.cons .one trivial σ).hom)
    have d0 := line_ty hW hL σ h3 .zero trivial
    have d1 := line_ty hW hL σ h3 .one trivial
    exact ⟨L1, b0, b1, L2', c0', c1', h1, h2', (ihL _ _).transTy h3 h3',
      P0.transEl d0 h4 (P0.conv (P0.symTy d0) h4'), P1.transEl d1 h5 (P1.conv (P1.symTy d1) h5')⟩
  · obtain ⟨he, hmem, -, hall⟩ := ht
    refine ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, he.symm, fun k'' σ' => ?_⟩
    obtain ⟨L1, b0, b1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, b0x, b1x, L1', b0', b1', hrx, -, h3, -⟩ := hT.2 k'' σ'
    obtain ⟨rfl, rfl, rfl⟩ : L1x = L1 ∧ b0x = b0 ∧ b1x = b1 := by
      have := RedW.unique hrx hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
    refine ⟨L1x, b0x, b1x, hr, fun r hr' => ?_⟩
    have := hel r hr'
    simp only [ISub.id_comp] at this ⊢
    exact (ihL _ _).symEl (line_ty hW hL σ' h3 r hr') this
  · obtain ⟨he, hmem, -, hall⟩ := ht
    obtain ⟨he', -, -, hall'⟩ := ht'
    refine ⟨he.trans he', hmem, he.trans he', fun k'' σ' => ?_⟩
    obtain ⟨L1, b0, b1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, b0x, b1x, hrx, hel'⟩ := hall' k'' σ'
    obtain ⟨rfl, rfl, rfl⟩ : L1x = L1 ∧ b0x = b0 ∧ b1x = b1 := by
      have := RedW.unique hrx hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
    obtain ⟨L1y, b0y, b1y, L1', b0', b1', hry, -, h3, -⟩ := hT.2 k'' σ'
    obtain ⟨rfl, rfl, rfl⟩ : L1y = L1x ∧ b0y = b0x ∧ b1y = b1x := by
      have := RedW.unique hry hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
    refine ⟨L1y, b0y, b1y, hr, fun r hr' => ?_⟩
    have x := hel r hr'
    have y := hel' r hr'
    simp only [ISub.id_comp] at x y ⊢
    exact (ihL _ _).transEl (line_ty hW hL σ' h3 r hr') x y
  · obtain ⟨he, hmem, -, hall⟩ := ht
    have hTT := hT.1.2.2.2.2
    refine ⟨he.conv hTT, hmem, he.conv hTT, fun k'' σ' => ?_⟩
    obtain ⟨L1, b0, b1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, b0x, b1x, L1', b0', b1', hrx, hr2, h3, -⟩ := hT.2 k'' σ'
    obtain ⟨rfl, rfl, rfl⟩ : L1x = L1 ∧ b0x = b0 ∧ b1x = b1 := by
      have := RedW.unique hrx hr; injection this with e1 e2 e3; exact ⟨e1, e2, e3⟩
    refine ⟨L1', b0', b1', hr2, fun r hr' => ?_⟩
    have x := hel r hr'
    simp only [ISub.id_comp] at x ⊢
    exact (ihL _ _).conv (line_ty hW hL σ' h3 r hr') x

/-- The PER properties at a code `(i : I) → L`. -/
theorem per2_ipiC {L : V} (hLne : L ≠ ∅) (hL : KR2 S (m + 1) L) (ihL : PER2 S (m + 1) L) :
    PER2 S m (ipiC m L) := by
  intro k f
  rw [Comp2_ipiC L hLne]
  refine ⟨fun {T T'} hT => ?_, fun {T T' T''} hT hT' => ?_, fun {T T' t t'} hT ht => ?_,
    fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨hb, hall⟩ := hT
    refine ⟨base_symm hb, fun k' σ => ?_⟩
    obtain ⟨L1, L1', h1, h2, h3⟩ := hall k' σ
    exact ⟨L1', L1, h2, h1, (ihL _ _).symTy h3⟩
  · obtain ⟨hb, hall⟩ := hT
    obtain ⟨hb', hall'⟩ := hT'
    refine ⟨base_trans hW hb hb', fun k' σ => ?_⟩
    obtain ⟨L1, L1', h1, h2, h3⟩ := hall k' σ
    obtain ⟨L2, L2', h1', h2', h3'⟩ := hall' k' σ
    obtain rfl : L1' = L2 := by have := RedW.unique h2 h1'; injection this
    exact ⟨L1, L2', h1, h2', (ihL _ _).transTy h3 h3'⟩
  · obtain ⟨he, hmem, -, hall⟩ := ht
    refine ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, he.symm, fun k'' σ' => ?_⟩
    obtain ⟨L1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, L1', hrx, -, h3⟩ := hT.2 k'' σ'
    obtain rfl : L1x = L1 := by have := RedW.unique hrx hr; injection this
    refine ⟨L1x, hr, fun r hr' => ?_⟩
    have := hel r hr'
    simp only [ISub.id_comp] at this ⊢
    exact (ihL _ _).symEl (line_ty hW hL σ' h3 r hr') this
  · obtain ⟨he, hmem, -, hall⟩ := ht
    obtain ⟨he', -, -, hall'⟩ := ht'
    refine ⟨he.trans he', hmem, he.trans he', fun k'' σ' => ?_⟩
    obtain ⟨L1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, hrx, hel'⟩ := hall' k'' σ'
    obtain rfl : L1x = L1 := by have := RedW.unique hrx hr; injection this
    obtain ⟨L1y, L1', hry, -, h3⟩ := hT.2 k'' σ'
    obtain rfl : L1y = L1x := by have := RedW.unique hry hr; injection this
    refine ⟨L1y, hr, fun r hr' => ?_⟩
    have x := hel r hr'
    have y := hel' r hr'
    simp only [ISub.id_comp] at x y ⊢
    exact (ihL _ _).transEl (line_ty hW hL σ' h3 r hr') x y
  · obtain ⟨he, hmem, -, hall⟩ := ht
    have hTT := hT.1.2.2.2.2
    refine ⟨he.conv hTT, hmem, he.conv hTT, fun k'' σ' => ?_⟩
    obtain ⟨L1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, L1', hrx, hr2, h3⟩ := hT.2 k'' σ'
    obtain rfl : L1x = L1 := by have := RedW.unique hrx hr; injection this
    refine ⟨L1', hr2, fun r hr' => ?_⟩
    have x := hel r hr'
    simp only [ISub.id_comp] at x ⊢
    exact (ihL _ _).conv (line_ty hW hL σ' h3 r hr') x

theorem per2_emptyC : PER2 S m (emptyC m) := by
  intro k f
  rw [Comp2_emptyC]
  exact ⟨fun hT => base_symm hT, fun hT hT' => base_trans hW hT hT', fun _ h => h.elim, fun _ h => h.elim,
    fun _ h => h.elim⟩

theorem per2_univC {l : ℕ} (ih : ∀ m' X, WF l m' X → PER2 S m' X) : PER2 S m (univC m l) := by
  intro k f
  rw [Comp2_univC]
  refine ⟨fun {T T'} hT => ?_, fun {T T' T''} hT hT' => ?_, fun {T T' t t'} hT ht => ?_,
    fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · exact ⟨base_symm hT.1, fun k' σ => ⟨(hT.2 k' σ).2, (hT.2 k' σ).1⟩⟩
  · exact ⟨base_trans hW hT.1 hT'.1, fun k' σ => ⟨(hT.2 k' σ).1, (hT'.2 k' σ).2⟩⟩
  · obtain ⟨he, hmem, hm, hty⟩ := ht
    have es := semK_eq hW he.2.2
    have P := ih k _ (ZFSet.mem_sep.1 hm).2 k (Hom.id k)
    refine ⟨he.symm, by rw [← es]; exact hmem, by rw [← es]; exact hm, ?_⟩
    rw [← es]; exact P.symTy hty
  · obtain ⟨he, hmem, hm, hty⟩ := ht
    obtain ⟨he', -, -, hty'⟩ := ht'
    have es := semK_eq hW he.2.2
    have P := ih k _ (ZFSet.mem_sep.1 hm).2 k (Hom.id k)
    rw [← es] at hty'
    exact ⟨he.trans he', hmem, hm, P.transTy hty hty'⟩
  · obtain ⟨he, hmem, hm, hty⟩ := ht
    exact ⟨he.conv hT.1.2.2.2.2, hmem, hm, hty⟩

end

end Model.Whnf
