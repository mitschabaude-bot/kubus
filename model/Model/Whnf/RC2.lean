import Model.Whnf.Expand

/-!
# Closure under stable reduction

If `t` is related to `t'`, and every restriction of `t'` reduces to the corresponding restriction of
`u'`, then `t` is related to `u'`. The relations observe types and elements of inductive and Glue types
through weak-head normal forms, which `u'` shares with `t'`, and elements of the other types through
eliminations, which reduce along with `t'`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-- Closure under stable reduction on the right, at a code. -/
def RC2 (S : Sig) (m : ℕ) (X : V) : Prop :=
  ∀ k (f : Hom k m) (A A' B' t t' u' : Tm),
    ((Comp2 S X m k f).ty A A' → StableT S k A' B' → IsTyK S k B' → (Comp2 S X m k f).ty A B') ∧
    ((Comp2 S X m k f).ty A A → (Comp2 S X m k f).el A t t' → StableE S k A t' u' → HasTy S k .one [] u' A →
      (Comp2 S X m k f).el A t u')

theorem StableT.restr {A B : Tm} (h : StableT S k A B) (σ : ISub k' k) : StableT S k' (A.isub σ) (B.isub σ) := by
  intro k'' σ'; simp only [Tm.isub_isub]; exact h k'' (σ.comp σ')

theorem StableE.restr {A t u : Tm} (h : StableE S k A t u) (σ : ISub k' k) :
    StableE S k' (A.isub σ) (t.isub σ) (u.isub σ) := by
  intro k'' σ'; simp only [Tm.isub_isub]; exact h k'' (σ.comp σ')

variable (hW : WfSig S)
include hW

theorem StableT.at_id {A B : Tm} (h : StableT S k A B) (hA : IsTyK S k A) (hB : IsTyK S k B) :
    Red S A B ∧ TyEq S k A B := by
  have := h k (ISub.id k)
  rwa [isub_id_of_closed (closed_of_isTyK hW hA), isub_id_of_closed (closed_of_isTyK hW hB)] at this

theorem StableE.at_id {A t u : Tm} (h : StableE S k A t u) (hA : IsTyK S k A) (ht : HasTy S k .one [] t A)
    (hu : HasTy S k .one [] u A) : Red S t u ∧ EqTm S k .one [] t u A := by
  have := h k (ISub.id k)
  rwa [isub_id_of_closed (closed_of_isTyK hW hA), isub_id_of_closed (closed_of_ty hW ht),
    isub_id_of_closed (closed_of_ty hW hu)] at this

/-- The base clause, along a stable reduction on the right. -/
theorem base_rc {X : V} {f : Hom k m} {A A' B' : Tm} (hB : IsTyK S k B')
    (h : IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = res f X ∧ semK S k A' = res f X ∧ TyEq S k A A')
    (hs : StableT S k A' B') :
    IsTyK S k A ∧ IsTyK S k B' ∧ semK S k A = res f X ∧ semK S k B' = res f X ∧ TyEq S k A B' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e := (hs.at_id hW h2 hB).2
  exact ⟨h1, hB, h3, (semK_tyEq hW e).symm.trans h4, h5.trans hW e⟩

/-- Related elements, along a stable reduction on the right. -/
theorem EB.rc {A t t' u : Tm} (h : EB S k A t t') (hs : StableE S k A t' u) (hu : HasTy S k .one [] u A) :
    EB S k A t u :=
  ⟨h.1, hu, h.2.2.trans (hs.at_id hW (isTyK_of_ty hW h.1) h.2.1 hu).2⟩

theorem RedT.stable {A B W : Tm} (hs : StableT S k A B) (σ : ISub k' k) (h : RedT S k' (A.isub σ) W) :
    RedT S k' (B.isub σ) W :=
  RedT.to_red hW (hs k' σ).1 (hs k' σ).2 h

theorem RedT.stable' {A B W : Tm} (hs : StableT S k A B) (σ : ISub k' k) (h : RedT S k' (B.isub σ) W) :
    RedT S k' (A.isub σ) W :=
  RedT.of_red hW (hs k' σ).1 (hs k' σ).2 h

/-- The codomains of a `Π` or `Σ` type at judgmentally equal arguments. -/
theorem cod_inst_eq {A1 B1 a a' : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A1 B1) (.univ l))
    (e : EqTm S k .one [] a a' A1) : EqTm S k .one [] (B1.inst a) (B1.inst a') (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  exact minimal_to_spec_eq (HasTy0.inst_congr hS (HasTy0.piCod hS (spec_to_minimal hW hpi))
    (spec_to_minimal hW (HasTy.eqL e)) (spec_to_minimal hW (HasTy.eqR e)) (spec_to_minimal_eq hW e))

theorem cod_inst_eqS {A1 B1 a a' : Tm} {l : ℕ} (hs : HasTy S k .one [] (.sigma A1 B1) (.univ l))
    (e : EqTm S k .one [] a a' A1) : EqTm S k .one [] (B1.inst a) (B1.inst a') (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  exact minimal_to_spec_eq (HasTy0.inst_congr hS (HasTy0.sigmaCod hS (spec_to_minimal hW hs))
    (spec_to_minimal hW (HasTy.eqL e)) (spec_to_minimal hW (HasTy.eqR e)) (spec_to_minimal_eq hW e))


/-- The normal form of a typed type is typed. -/
theorem redT_ty {T W : Tm} (hT : IsTyK S k T) (h : RedT S k T W) (hW' : ∀ l, W ≠ .univ l) :
    ∃ l, HasTy S k .one [] W (.univ l) :=
  ty_of_tyEq hW hT h.2 hW'

/-! ### `Π` and `Σ` -/

section pisig
variable {A B : V} (hA : A ≠ ∅)
include hA

theorem rcTy_piC {f : Hom k m} {T T' B' : Tm} (h : (Comp2 S (piC m A B) m k f).ty T T') (hs : StableT S k T' B')
    (hB : IsTyK S k B') : (Comp2 S (piC m A B) m k f).ty T B' := by
  rw [Comp2_piC A B hA] at h ⊢
  obtain ⟨hb, hall, hc, hc', hk, hk'⟩ := h
  refine ⟨base_rc hW hB hb hs, fun k' σ => ?_, hc, fun k1 σ k2 σ' A1 B1 A2 B2 h1 h2 =>
    hc' k1 σ k2 σ' A1 B1 A2 B2 (RedT.stable' hW hs σ h1) (RedT.stable' hW hs _ h2), hk, fun k' σ A1 B1 hR => hk' k' σ A1 B1 (RedT.stable' hW hs σ hR)⟩
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' σ
  exact ⟨A1, B1, A1', B1', h1, RedT.stable hW hs σ h2, h3, h4⟩

theorem rcTy_sigmaC {f : Hom k m} {T T' B' : Tm} (h : (Comp2 S (sigmaC m A B) m k f).ty T T') (hs : StableT S k T' B')
    (hB : IsTyK S k B') : (Comp2 S (sigmaC m A B) m k f).ty T B' := by
  rw [Comp2_sigmaC A B hA] at h ⊢
  obtain ⟨hb, hall, hc, hc', hk, hk'⟩ := h
  refine ⟨base_rc hW hB hb hs, fun k' σ => ?_, hc, fun k1 σ k2 σ' A1 B1 A2 B2 h1 h2 =>
    hc' k1 σ k2 σ' A1 B1 A2 B2 (RedT.stable' hW hs σ h1) (RedT.stable' hW hs _ h2), hk, fun k' σ A1 B1 hR => hk' k' σ A1 B1 (RedT.stable' hW hs σ hR)⟩
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' σ
  exact ⟨A1, B1, A1', B1', h1, RedT.stable hW hs σ h2, h3, h4⟩

theorem rcEl_piC (rcB : ∀ k (f : Hom k m), ∀ a ∈ El A f, RC2 S k (apZ (dat B k f) a))
    (perB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a))
    {f : Hom k m} {T t t' u' : Tm} (hTT : (Comp2 S (piC m A B) m k f).ty T T)
    (h : (Comp2 S (piC m A B) m k f).el T t t') (hs : StableE S k T t' u')
    (hu : HasTy S k .one [] u' T) : (Comp2 S (piC m A B) m k f).el T t u' := by
  rw [Comp2_piC A B hA] at h hTT ⊢
  have hTall := hTT.2.1
  obtain ⟨hE, hmem, -, hall⟩ := h
  have hE' := EB.rc hW hE hs hu
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨A1, B1, hR, hcod⟩ := hall k1 σ1
  refine ⟨A1, B1, hR, fun a a' ha => ?_⟩
  simp only [ISub.id_comp, ISub.hom_id] at ha hcod ⊢
  have x := hcod a a' ha
  obtain ⟨l1, hpi⟩ := redT_ty hW ((isTyK_of_ty hW hE.1).isub hW σ1) hR (fun l h => by cases h)
  have ea : EqTm S k1 .one [] a' a A1 := ((Comp2_el ha).1.2.2).symm
  have hu1 : HasTy S k1 .one [] (u'.isub σ1) (.pi A1 B1) := (HasTy.isubS hW hu σ1).tyConv hR.2
  have hBB : (Comp2 S (apZ (dat B k1 (f.comp σ1.hom)) (semK S k1 a)) k1 k1 (Hom.id k1)).ty (B1.inst a) (B1.inst a) := by
    obtain ⟨A1x, B1x, A1y, B1y, hx, hy, hAA, hB⟩ := hTall k1 σ1
    obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
      have := RedW.unique hx.1 hR.1; injection this; constructor <;> assumption
    obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
      have := RedW.unique hy.1 hR.1; injection this; constructor <;> assumption
    exact (perB k1 _ _ (fib_mem ha) k1 (Hom.id k1)).reflTy (hB a a' ha)
  refine (rcB k1 _ _ (fib_mem ha) k1 (Hom.id k1) (B1.inst a) (B1.inst a) (B1.inst a) _ _ _).2 hBB x (fun k3 σ3 => ?_)
    ((HasTy.app hu1 (Comp2_el ha).1.2.1).tyConv (.inr ⟨l1, cod_inst_eq hW hpi ea⟩))
  have hs3 := hs k3 (σ1.comp σ3)
  have hTy : TyEq S k3 (T.isub (σ1.comp σ3)) (.pi (A1.isub σ3) (B1.isub σ3)) := by
    have := hR.2.isub hW σ3; rwa [Tm.isub_isub, isub_pi] at this
  have hpiσ := HasTy.isubS hW hpi σ3
  rw [isub_pi] at hpiσ
  rw [isub_app, isub_app, Tm.isub_isub, Tm.isub_isub, isub_inst]
  refine ⟨red_app _ hs3.1, ?_⟩
  exact (EqTm.app (hs3.2.tyConv hTy) (EqTm.refl (HasTy.isubS hW (Comp2_el ha).1.2.1 σ3))).tyConv
    (.inr ⟨l1, cod_inst_eq hW hpiσ (EqTm.isubS hW ea σ3)⟩)

theorem rcEl_sigmaC (rcA : RC2 S m A) (perA : PER2 S m A)
    (rcB : ∀ k (f : Hom k m), ∀ a ∈ El A f, RC2 S k (apZ (dat B k f) a))
    (perB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a))
    {f : Hom k m} {T t t' u' : Tm} (hTT : (Comp2 S (sigmaC m A B) m k f).ty T T)
    (h : (Comp2 S (sigmaC m A B) m k f).el T t t') (hs : StableE S k T t' u')
    (hu : HasTy S k .one [] u' T) : (Comp2 S (sigmaC m A B) m k f).el T t u' := by
  rw [Comp2_sigmaC A B hA] at h hTT ⊢
  have hTall := hTT.2.1
  obtain ⟨hE, hmem, -, hall⟩ := h
  have hE' := EB.rc hW hE hs hu
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨A1, B1, hR, hfst, hsnd⟩ := hall k1 σ1
  simp only [ISub.id_comp, ISub.hom_id] at hfst hsnd ⊢
  obtain ⟨A1x, B1x, A1y, B1y, hx, hy, hAA, hB⟩ := hTall k1 σ1
  obtain ⟨rfl, rfl⟩ : A1 = A1x ∧ B1 = B1x := by
    have := RedW.unique hR.1 hx.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1 = A1y ∧ B1 = B1y := by
    have := RedW.unique hR.1 hy.1; injection this; constructor <;> assumption
  obtain ⟨l1, hsig⟩ := redT_ty hW ((isTyK_of_ty hW hE.1).isub hW σ1) hR (fun l h => by cases h)
  have hu1 : HasTy S k1 .one [] (u'.isub σ1) (.sigma A1 B1) := (HasTy.isubS hW hu σ1).tyConv hR.2
  have hTy : ∀ k3 (σ3 : ISub k3 k1), TyEq S k3 (T.isub (σ1.comp σ3)) (.sigma (A1.isub σ3) (B1.isub σ3)) := by
    intro k3 σ3; have := hR.2.isub hW σ3; rwa [Tm.isub_isub, isub_sigma] at this
  -- the first projections
  have hfst' : (Comp2 S A m k1 (f.comp σ1.hom)).el A1 (.fst (t.isub σ1)) (.fst (u'.isub σ1)) := by
    refine (rcA k1 _ A1 A1 A1 _ _ _).2 ((perA k1 _).reflTy hAA) hfst (fun k3 σ3 => ?_) (HasTy.fst hu1)
    have hs3 := hs k3 (σ1.comp σ3)
    rw [isub_fst, isub_fst, Tm.isub_isub, Tm.isub_isub]
    exact ⟨red_fst hs3.1, EqTm.fst (hs3.2.tyConv (hTy k3 σ3))⟩
  refine ⟨A1, B1, hR, hfst', ?_⟩
  have hamem := fib_mem hfst
  have hfT := (Comp2_el hfst).1
  -- the type of the second projection, at the two first projections
  have ef : EqTm S k1 .one [] (.fst (t'.isub σ1)) (.fst (u'.isub σ1)) A1 := by
    have := (hs.at_id hW (isTyK_of_ty hW hE.1) hE.2.1 hu)
    have h0 := EqTm.isubS hW this.2 σ1
    exact EqTm.fst (h0.tyConv hR.2)
  have eB : EqTm S k1 .one [] (B1.inst (.fst (u'.isub σ1))) (B1.inst (.fst (t.isub σ1))) (.univ l1) :=
    cod_inst_eqS hW hsig ((hfT.2.2.trans ef).symm)
  have hBB := (perB k1 _ _ hamem k1 (Hom.id k1)).reflTy (hB _ _ hfst)
  refine (rcB k1 _ _ hamem k1 (Hom.id k1) (B1.inst (.fst (t.isub σ1))) (B1.inst (.fst (t.isub σ1)))
    (B1.inst (.fst (t.isub σ1))) _ _ _).2 hBB hsnd (fun k3 σ3 => ?_)
    ((HasTy.snd hu1).tyConv (.inr ⟨l1, eB⟩))
  have hs3 := hs k3 (σ1.comp σ3)
  have hsigσ := HasTy.isubS hW hsig σ3
  rw [isub_sigma] at hsigσ
  rw [isub_snd, isub_snd, Tm.isub_isub, Tm.isub_isub, isub_inst, isub_fst, Tm.isub_isub]
  refine ⟨red_snd hs3.1, ?_⟩
  have e2 := EqTm.snd (hs3.2.tyConv (hTy k3 σ3))
  have eB3 := EqTm.isubS hW eB σ3
  rw [isub_inst, isub_inst, isub_fst, isub_fst, Tm.isub_isub, Tm.isub_isub, isub_univ] at eB3
  have eB4 : EqTm S k3 .one [] ((B1.isub σ3).inst (.fst (t'.isub (σ1.comp σ3))))
      ((B1.isub σ3).inst (.fst (t.isub (σ1.comp σ3)))) (.univ l1) := by
    have := EqTm.isubS hW (hfT.2.2) σ3
    rw [isub_fst, isub_fst, Tm.isub_isub, Tm.isub_isub] at this
    exact cod_inst_eqS hW hsigσ this.symm
  exact e2.tyConv (.inr ⟨l1, eB4⟩)

end pisig


/-- A line at equal interval terms. -/
theorem line_dinst_eq {L : Tm} {l : ℕ} (hL : HasTy S (k + 1) .one [] L (.univ l)) {r r' : I} (hr : r.Scoped k)
    (hr' : r'.Scoped k) (he : I.Eq r r') : EqTm S k .one [] (L.dinst r) (L.dinst r') (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  exact minimal_to_spec_eq (HasTy0.dinst_congr hS (Φ := .one) (Γ := []) (spec_to_minimal hW hL) hr hr' he)

/-! ### Path types and `(i : I) → L` -/

section path
variable {L a0 a1 : V} (hLne : L ≠ ∅)
include hLne

theorem rcTy_pathC {f : Hom k m} {T T' B' : Tm} (h : (Comp2 S (pathC m L a0 a1) m k f).ty T T')
    (hs : StableT S k T' B') (hB : IsTyK S k B') : (Comp2 S (pathC m L a0 a1) m k f).ty T B' := by
  rw [Comp2_pathC L a0 a1 hLne] at h ⊢
  obtain ⟨hb, hall, hc, hc'⟩ := h
  refine ⟨base_rc hW hB hb hs, fun k' σ => ?_, hc, fun k1 σ k2 σ' L1 b0 b1 L2 c0 c1 h1 h2 =>
    hc' k1 σ k2 σ' L1 b0 b1 L2 c0 c1 (RedT.stable' hW hs σ h1) (RedT.stable' hW hs _ h2)⟩
  obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3⟩ := hall k' σ
  exact ⟨L1, b0, b1, L1', b0', b1', h1, RedT.stable hW hs σ h2, h3⟩

theorem rcTy_ipiC {f : Hom k m} {T T' B' : Tm} (h : (Comp2 S (ipiC m L) m k f).ty T T')
    (hs : StableT S k T' B') (hB : IsTyK S k B') : (Comp2 S (ipiC m L) m k f).ty T B' := by
  rw [Comp2_ipiC L hLne] at h ⊢
  obtain ⟨hb, hall, hc, hc'⟩ := h
  refine ⟨base_rc hW hB hb hs, fun k' σ => ?_, hc, fun k1 σ k2 σ' L1 L2 h1 h2 =>
    hc' k1 σ k2 σ' L1 L2 (RedT.stable' hW hs σ h1) (RedT.stable' hW hs _ h2)⟩
  obtain ⟨L1, L1', h1, h2, h3⟩ := hall k' σ
  exact ⟨L1, L1', h1, RedT.stable hW hs σ h2, h3⟩

omit hLne in
/-- Applications at equal interval terms, along a stable reduction of the right function. -/
theorem papp_stable {X L1 t' u' : Tm} {k1 : ℕ} (hs : StableE S k1 X t' u') (hX : TyEq S k1 X (.ipi L1) ∨
      ∃ b0 b1, TyEq S k1 X (.path L1 b0 b1)) (hL : ∃ l, HasTy S (k1 + 1) .one [] L1 (.univ l))
    {r r' : I} (hr : r.Scoped k1) (hr' : r'.Scoped k1) (he : I.Eq r r') :
    StableE S k1 (L1.dinst r) (.papp t' r') (.papp u' r') := by
  intro k3 σ3
  have hs3 := hs k3 σ3
  obtain ⟨l, hL⟩ := hL
  have hrσ := I.scoped_subst hr σ3.sc
  have hrσ' := I.scoped_subst hr' σ3.sc
  have hLσ := HasTy.isubS hW hL σ3.up
  have eL := line_dinst_eq hW hLσ hrσ' hrσ (I_eq_symm (I_eq_subst he σ3.τ))
  rw [isub_papp, isub_papp, isub_dinst]
  refine ⟨red_papp _ hs3.1, ?_⟩
  rcases hX with hX | ⟨b0, b1, hX⟩
  · have hTy := hX.isub hW σ3
    rw [isub_ipi] at hTy
    exact (EqTm.iapp (hs3.2.tyConv hTy) hrσ' hrσ' (I_eq_refl _)).tyConv (.inr ⟨l, eL⟩)
  · have hTy := hX.isub hW σ3
    rw [isub_path] at hTy
    exact (EqTm.papp (hs3.2.tyConv hTy) hrσ' hrσ' (I_eq_refl _)).tyConv (.inr ⟨l, eL⟩)

theorem rcEl_pathC (rcL : RC2 S (m + 1) L) (perL : PER2 S (m + 1) L) {f : Hom k m} {T t t' u' : Tm}
    (hTT : (Comp2 S (pathC m L a0 a1) m k f).ty T T)
    (h : (Comp2 S (pathC m L a0 a1) m k f).el T t t') (hs : StableE S k T t' u') (hu : HasTy S k .one [] u' T) :
    (Comp2 S (pathC m L a0 a1) m k f).el T t u' := by
  rw [Comp2_pathC L a0 a1 hLne] at h hTT ⊢
  have hTall := hTT.2.1
  obtain ⟨hE, hmem, -, hall⟩ := h
  have hE' := EB.rc hW hE hs hu
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨L1, b0, b1, hR, hp, e0, e1⟩ := hall k1 σ1
  refine ⟨L1, b0, b1, hR, fun r r' hr hr' he => ?_, e0, e1⟩
  simp only [ISub.id_comp] at hp ⊢
  obtain ⟨l1, hpath⟩ := redT_ty hW ((isTyK_of_ty hW hE.1).isub hW σ1) hR (fun l h => by cases h)
  have hu1 : HasTy S k1 .one [] (u'.isub σ1) (.path L1 b0 b1) := (HasTy.isubS hW hu σ1).tyConv hR.2
  have hL1 := HasTy.pathLine hpath
  have hLL : (Comp2 S L (m + 1) k1 ((Hom.lift f).comp (ISub.cons r hr σ1).hom)).ty (L1.dinst r) (L1.dinst r) := by
    obtain ⟨L1x, b0x, b1x, L1y, b0y, b1y, hx, hy, -, hrr, -, -⟩ := hTall k1 σ1
    obtain ⟨rfl, -, -⟩ : L1x = L1 ∧ True ∧ True := by
      have := RedW.unique hx.1 hR.1; injection this; exact ⟨by assumption, trivial, trivial⟩
    obtain ⟨rfl, -, -⟩ : L1y = L1x ∧ True ∧ True := by
      have := RedW.unique hy.1 hR.1; injection this; exact ⟨by assumption, trivial, trivial⟩
    exact (perL _ _).reflTy (hrr r r hr hr (I_eq_refl _))
  refine (rcL k1 _ (L1.dinst r) (L1.dinst r) (L1.dinst r) _ _ _).2 hLL (hp r r' hr hr' he)
    (papp_stable hW (hs.restr σ1) (.inr ⟨b0, b1, hR.2⟩) ⟨l1, hL1⟩ hr hr' he)
    ((HasTy.papp hu1 hr').tyConv (.inr ⟨l1, line_dinst_eq hW hL1 hr' hr (I_eq_symm he)⟩))

theorem rcEl_ipiC (rcL : RC2 S (m + 1) L) (perL : PER2 S (m + 1) L) {f : Hom k m} {T t t' u' : Tm}
    (hTT : (Comp2 S (ipiC m L) m k f).ty T T)
    (h : (Comp2 S (ipiC m L) m k f).el T t t') (hs : StableE S k T t' u') (hu : HasTy S k .one [] u' T) :
    (Comp2 S (ipiC m L) m k f).el T t u' := by
  rw [Comp2_ipiC L hLne] at h hTT ⊢
  have hTall := hTT.2.1
  obtain ⟨hE, hmem, -, hall⟩ := h
  have hE' := EB.rc hW hE hs hu
  refine ⟨hE', hmem, hE', fun k1 σ1 => ?_⟩
  obtain ⟨L1, hR, hp⟩ := hall k1 σ1
  refine ⟨L1, hR, fun r r' hr hr' he => ?_⟩
  simp only [ISub.id_comp] at hp ⊢
  obtain ⟨l1, hipi⟩ := redT_ty hW ((isTyK_of_ty hW hE.1).isub hW σ1) hR (fun l h => by cases h)
  have hu1 : HasTy S k1 .one [] (u'.isub σ1) (.ipi L1) := (HasTy.isubS hW hu σ1).tyConv hR.2
  have hL1 : HasTy S (k1 + 1) .one [] L1 (.univ l1) :=
    minimal_to_spec (HasTy0.ipiLine (sigClosed_of_wfSig hW) (spec_to_minimal hW hipi))
  have hLL : (Comp2 S L (m + 1) k1 ((Hom.lift f).comp (ISub.cons r hr σ1).hom)).ty (L1.dinst r) (L1.dinst r) := by
    obtain ⟨L1x, L1y, hx, hy, -, hrr⟩ := hTall k1 σ1
    obtain rfl : L1x = L1 := by have := RedW.unique hx.1 hR.1; injection this
    obtain rfl : L1y = L1x := by have := RedW.unique hy.1 hR.1; injection this
    exact (perL _ _).reflTy (hrr r r hr hr (I_eq_refl _))
  refine (rcL k1 _ (L1.dinst r) (L1.dinst r) (L1.dinst r) _ _ _).2 hLL (hp r r' hr hr' he)
    (papp_stable hW (hs.restr σ1) (.inl hR.2) ⟨l1, hL1⟩ hr hr' he)
    ((HasTy.iapp hu1 hr').tyConv (.inr ⟨l1, line_dinst_eq hW hL1 hr' hr (I_eq_symm he)⟩))

end path



/-! ### The empty type, universes and inductive types -/

theorem rc2_emptyC : RC2 S m (emptyC m) := by
  intro k f T T' B' t t' u'
  rw [Comp2_emptyC]
  exact ⟨fun h hs hB => base_rc hW hB h hs, fun _ h => h.elim⟩

theorem rc2_univC {l : ℕ} (ih : ∀ m' X, WF l m' X → RC2 S m' X) : RC2 S m (univC m l) := by
  intro k f T T' B' t t' u'
  rw [Comp2_univC]
  refine ⟨fun h hs hB => ⟨base_rc hW hB h.1 hs, fun k' σ => ⟨(h.2 k' σ).1, RedT.stable hW hs σ (h.2 k' σ).2⟩⟩,
    fun hTT h hs hu => ?_⟩
  obtain ⟨hE, hmem, hm, hty, hK⟩ := h
  refine ⟨EB.rc hW hE hs hu, hmem, hm, ?_, hK⟩
  have hWF : WF l k (semK S k t) := (ZFSet.mem_sep.1 hm).2
  have hU : ∀ k' (σ : ISub k' k), TyEq S k' (T.isub σ) (.univ l) := fun k' σ => (hTT.2 k' σ).1.2
  have hst : StableT S k t' u' := fun k' σ => ⟨(hs k' σ).1, .inr ⟨l, (hs k' σ).2.tyConv (hU k' σ)⟩⟩
  have hTid : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTT.1.1)
  have hu0 : HasTy S k .one [] u' (.univ l) := hu.tyConv (by have := hU k (ISub.id k); rwa [hTid] at this)
  exact (ih k _ hWF k (Hom.id k) t t' u' t t' u').1 hty hst (tyk hu0)

/-- Elements of an inductive type at a stage, along a reduction on the right. -/
theorem DR2At.redR {k0 : ℕ} {Θ : SData m} {f : Hom k0 m} {d : ℕ} {D : DataDecl} {g : Hom k k0} {A t t' u' : Tm}
    (h : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t t') (r : Red S t' u') (e : EqTm S k .one [] t' u' A) :
    DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t u' := by
  cases h with
  | con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    exact .con hm (by unfold dataMem at hm' ⊢; rwa [← semK_eq hW e]) (heq.trans e) hC hA hpl ht
      ⟨red_redW r ht'.1, e.symm.trans ht'.2⟩ hrs hrs' hreq hsc hsc' hl hl' hrec hpt
  | hcomp hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu =>
    exact .hcomp hm (by unfold dataMem at hm' ⊢; rwa [← semK_eq hW e]) (heq.trans e) hH hA hpl ht
      ⟨red_redW r ht'.1, e.symm.trans ht'.2⟩ hs hs' h12 h21 ha hu

theorem rc2_dataC {Θ : SData m} : RC2 S m (dataC Θ) := by
  intro k f T T' B' t t' u'
  rw [Comp2_dataC]
  refine ⟨fun h hs hB => ⟨base_rc hW hB h.1 hs, fun k' σ => ?_, h.2.2.1, fun k' σ k'' σ' ps1 ps2 h1 h2 => ?_⟩,
    fun _ h hs hu => ?_⟩
  · obtain ⟨ps, ps', h1, h2, rest⟩ := h.2.1 k' σ
    exact ⟨ps, ps', h1, RedT.stable hW hs σ h2, rest⟩
  · exact h.2.2.2 k' σ k'' σ' ps1 ps2 (RedT.of_red hW (hs k' σ).1 (hs k' σ).2 h1)
      (RedT.of_red hW (hs k'' (σ.comp σ')).1 (hs k'' (σ.comp σ')).2 h2)
  · obtain ⟨hE, hmem, -, hdr⟩ := h
    have hE' := EB.rc hW hE hs hu
    refine ⟨hE', hmem, hE', ?_⟩
    cases hdr with
    | intro he hh hc hc' =>
      refine .intro hE'.2.2 (fun k' σ => (hh k' σ).redR hW (hs k' σ).1 (hs k' σ).2) hc (fun k' σ w hw k'' ρ => ?_)
      exact (hc' k' σ w (redW_of_red (hs k' σ).1 hw) k'' ρ).redR hW (hs k'' (σ.comp ρ)).1 (hs k'' (σ.comp ρ)).2


/-! ### Glue types -/

section glue
variable {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
  (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
  (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
  (rcT : ∀ k (f : Hom k m), (φ.restr f).holds → RC2 S k (dat Tp k f))
include rcT

omit hW in
theorem glueLocT_rc {f : Hom k m} {k' : ℕ} (σ : ISub k' k) (hW : WfSig S) {Y Z Z' : Tm}
    (h : glueLocT S A Tp φ f k' σ Y Z) (hs : StableT S k' Z Z') (hZ : IsTyK S k' Z) (hZ' : IsTyK S k' Z') :
    glueLocT S A Tp φ f k' σ Y Z' := by
  unfold glueLocT at h ⊢
  split_ifs at h ⊢ with hh
  · exact (rcT k' _ hh k' (Hom.id k') Y Z Z' Y Y Y).1 h hs hZ'
  · obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', h1, h2, rest⟩ := h
    have hs0 := hs.at_id hW hZ hZ'
    exact ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', h1, RedT.to_red hW hs0.1 hs0.2 h2, rest⟩

omit hW in
theorem glueLocE_rc {f : Hom k m} {k' : ℕ} (σ : ISub k' k) (hW : WfSig S) {X y z z' : Tm}
    (hX : glueLocT S A Tp φ f k' σ X X) (h : glueLocE S A Tp φ f k' σ X y z) (hs : StableE S k' X z z')
    (hz : HasTy S k' .one [] z X) (hz' : HasTy S k' .one [] z' X) : glueLocE S A Tp φ f k' σ X y z' := by
  unfold glueLocT at hX
  unfold glueLocE at h ⊢
  split_ifs at h hX ⊢ with hh
  · exact (rcT k' _ hh k' (Hom.id k') X X X y z z').2 hX h hs hz'
  · obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', rest⟩ := h
    have hs0 := hs.at_id hW (isTyK_of_ty hW hz) hz hz'
    exact ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg,
      ⟨red_redW hs0.1 rg'.1, hs0.2.symm.trans rg'.2⟩, rest⟩

include hW hA hφ hTp hTkv

theorem rc2_glueC : RC2 S m (glueC m A φ Tp ep) := by
  intro k f T T' B' t t' u'
  by_cases hf : (φ.restr f).holds
  · rw [Comp2_glueC_at hφ hTp hTkv f, if_pos hf]
    exact rcT k f hf k (Hom.id k) T T' B' t t' u'
  rw [Comp2_glueC_f hA hφ hTp hTkv f hf]
  refine ⟨fun h hs hB => ?_, fun hTT h hs hu => ?_⟩
  · obtain ⟨hb, hall, hc, hc'⟩ := h
    refine ⟨base_rc hW hB hb hs, fun k' σ => glueLocT_rc rcT σ hW (hall k' σ) (hs.restr σ) (hb.2.1.isub hW σ)
      (hB.isub hW σ), hc, fun k' σ hn W hW' k'' ρ => ?_⟩
    exact glueLocT_rc rcT (σ.comp ρ) hW (hc' k' σ hn W (redW_of_red (hs k' σ).1 hW') k'' ρ)
      (hs.restr (σ.comp ρ)) (hb.2.1.isub hW _) (hB.isub hW _)
  · obtain ⟨hE, hmem, -, hall, hc, hc'⟩ := h
    have hE' := EB.rc hW hE hs hu
    have hT := hTT.2.1
    refine ⟨hE', hmem, hE', fun k' σ => glueLocE_rc rcT σ hW (hT k' σ) (hall k' σ) (hs.restr σ)
      (HasTy.isubS hW hE.2.1 σ) (HasTy.isubS hW hu σ), hc, fun k' σ hn w hw k'' ρ => ?_⟩
    obtain ⟨c1, c2⟩ := hc' k' σ hn w (redW_of_red (hs k' σ).1 hw) k'' ρ
    refine ⟨fun hh ψ e0 t0 a0 hwe => ?_, fun hh => glueLocE_rc rcT (σ.comp ρ) hW (hT k'' _) (c2 hh)
      (hs.restr (σ.comp ρ)) (HasTy.isubS hW hE.2.1 _) (HasTy.isubS hW hu _)⟩
    have hTτ := hT k'' (σ.comp ρ)
    unfold glueLocT at hTτ; rw [if_pos hh] at hTτ
    exact (rcT k'' _ hh k'' (Hom.id k'') (T.isub (σ.comp ρ)) (T.isub (σ.comp ρ)) (T.isub (σ.comp ρ)) _ _ _).2 hTτ
      (c1 hh ψ e0 t0 a0 hwe) (hs.restr (σ.comp ρ))
      (HasTy.isubS hW hu _)

end glue

end

end Model.Whnf
