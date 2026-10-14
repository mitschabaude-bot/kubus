import Model.Whnf.PerData

/-!
# Local head expansion

A term whose restrictions each reduce to a term related at that stage is related. Steps do not
commute with restriction, so the reducts are chosen per restriction. The coherence clauses of the
type relations make this work for types: the normal forms of a type at a restriction and at a
further restriction are related through those of the reducts.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-! ### Reduction -/

/-- Every restriction of `t` reduces to the corresponding restriction of `u`, judgmentally equal at `A`. -/
def StableE (S : Sig) (k : ℕ) (A t u : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), Red S (t.isub σ) (u.isub σ) ∧ EqTm S k' .one [] (t.isub σ) (u.isub σ) (A.isub σ)

/-- Every restriction of the type `A` reduces to the corresponding restriction of `B`. -/
def StableT (S : Sig) (k : ℕ) (A B : Tm) : Prop :=
  ∀ k' (σ : ISub k' k), Red S (A.isub σ) (B.isub σ) ∧ TyEq S k' (A.isub σ) (B.isub σ)


theorem red_redW {t u w : Tm} (h : Red S t u) (hw : RedW S t w) : RedW S u w := by
  induction h with
  | refl => exact hw
  | step hs _ ih =>
    obtain ⟨hr, hn⟩ := hw
    cases hr with
    | refl => unfold IsWhnf at hn; rw [hn] at hs; cases hs
    | step hs' r' => rw [hs] at hs'; cases hs'; exact ih ⟨r', hn⟩

theorem redW_of_red {t u w : Tm} (h : Red S t u) (hw : RedW S u w) : RedW S t w := ⟨h.trans hw.1, hw.2⟩

theorem red_app {t u : Tm} (a : Tm) (h : Red S t u) : Red S (.app t a) (.app u a) := by
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih =>
    refine .step ?_ ih
    cases t0 <;> simp_all [step]

theorem red_fst {t u : Tm} (h : Red S t u) : Red S (.fst t) (.fst u) := by
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih =>
    refine .step ?_ ih
    cases t0 <;> simp_all [step]

theorem red_snd {t u : Tm} (h : Red S t u) : Red S (.snd t) (.snd u) := by
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih =>
    refine .step ?_ ih
    cases t0 <;> simp_all [step]

theorem red_papp {t u : Tm} (r : I) (h : Red S t u) : Red S (.papp t r) (.papp u r) := by
  induction h with
  | refl => exact .refl _
  | @step t0 t1 t2 hs _ ih =>
    refine .step ?_ ih
    cases t0 <;> simp_all [step]

section
variable (hW : WfSig S)
include hW

theorem RedT.of_red {A B W : Tm} (h : Red S A B) (e : TyEq S k A B) (hB : RedT S k B W) : RedT S k A W :=
  ⟨redW_of_red h hB.1, (e.trans hW hB.2)⟩

theorem RedT.to_red {A B W : Tm} (h : Red S A B) (e : TyEq S k A B) (hA : RedT S k A W) : RedT S k B W :=
  ⟨red_redW h hA.1, (e.symm.trans hW hA.2)⟩

omit hW in
theorem RedE.of_red {A t u w : Tm} (h : Red S t u) (e : EqTm S k .one [] t u A) (hu : RedE S k A u w) :
    RedE S k A t w :=
  ⟨redW_of_red h hu.1, e.trans hu.2⟩

end

/-- Local head expansion at a code: a type (an element) is related if each of its restrictions
reduces to one related at that stage, and both sides are typed. -/
def HE2 (S : Sig) (m : ℕ) (X : V) : Prop :=
  ∀ k (f : Hom k m) (A A' t t' : Tm),
    (IsTyK S k A → IsTyK S k A' → (∀ k' (σ : ISub k' k), ∃ B, Red S (A.isub σ) B ∧ TyEq S k' (A.isub σ) B ∧
        (Comp2 S X m k' (f.comp σ.hom)).ty B (A'.isub σ)) → (Comp2 S X m k f).ty A A') ∧
    ((Comp2 S X m k f).ty A A → HasTy S k .one [] t A → HasTy S k .one [] t' A →
      (∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (A.isub σ) ∧
        (Comp2 S X m k' (f.comp σ.hom)).el (A.isub σ) u (t'.isub σ)) → (Comp2 S X m k f).el A t t')

section
variable (hW : WfSig S)
include hW

/-- The hypothesis of head expansion for types, at the identity. -/
theorem hypT_id {X : V} {f : Hom k m} {A A' : Tm} (hA : IsTyK S k A) (hA' : IsTyK S k A')
    (h : ∀ k' (σ : ISub k' k), ∃ B, Red S (A.isub σ) B ∧ TyEq S k' (A.isub σ) B ∧
      (Comp2 S X m k' (f.comp σ.hom)).ty B (A'.isub σ)) :
    ∃ B, Red S A B ∧ TyEq S k A B ∧ (Comp2 S X m k f).ty B A' := by
  obtain ⟨B, r, e, hB⟩ := h k (ISub.id k)
  rw [isub_id_of_closed (closed_of_isTyK hW hA), isub_id_of_closed (closed_of_isTyK hW hA'), ISub.hom_id,
    Hom.comp_id] at *
  exact ⟨B, r, e, hB⟩

/-- The hypothesis of head expansion for elements, at the identity. -/
theorem hypE_id {X : V} {f : Hom k m} {A t t' : Tm} (hA : IsTyK S k A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A)
    (h : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (A.isub σ) ∧
      (Comp2 S X m k' (f.comp σ.hom)).el (A.isub σ) u (t'.isub σ)) :
    ∃ u, Red S t u ∧ EqTm S k .one [] t u A ∧ (Comp2 S X m k f).el A u t' := by
  obtain ⟨u, r, e, hu⟩ := h k (ISub.id k)
  rw [isub_id_of_closed (closed_of_isTyK hW hA), isub_id_of_closed (closed_of_ty hW ht),
    isub_id_of_closed (closed_of_ty hW ht'), ISub.hom_id, Hom.comp_id] at *
  exact ⟨u, r, e, hu⟩

/-- The base clause of a head expansion. -/
theorem base_expand {X : V} {f : Hom k m} {A A' B : Tm} (hA : IsTyK S k A) (e : TyEq S k A B)
    (hB : (Comp2 S X m k f).ty B A') :
    IsTyK S k A ∧ IsTyK S k A' ∧ semK S k A = res f X ∧ semK S k A' = res f X ∧ TyEq S k A A' := by
  obtain ⟨-, -, h2, h3, h4, h5⟩ := Comp2_ty_base hB
  exact ⟨hA, h2, (semK_tyEq hW e).trans h3, h4, e.trans hW h5⟩

/-- The element clause of a head expansion: typing, equality and value. -/
theorem el_expand {X : V} {f : Hom k m} {A t t' u : Tm} (ht : HasTy S k .one [] t A)
    (e : EqTm S k .one [] t u A) (hu : (Comp2 S X m k f).el A u t') :
    EB S k A t t' ∧ semK S k t ∈ El (res f X) (Hom.id k) := by
  obtain ⟨hE, hm⟩ := Comp2_el hu
  exact ⟨⟨ht, hE.2.1, e.trans hE.2.2⟩, by rw [semK_eq hW e]; exact hm⟩

end

/-! ### `Π` and `Σ` -/

section pisig
variable {A B : V} (hA : A ≠ ∅)

omit hA in
/-- The fibres of a family of codes along restrictions. -/
theorem cod_res (hW : WfSig S) (hBne : ∀ k (f : Hom k m), ∀ a ∈ El A f, apZ (dat B k f) a ≠ ∅)
    (hBn : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
      res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a))
    {g : Hom k m} {a A1 : Tm} (ha : HasTy S k .one [] a A1) (hmem : semK S k a ∈ El A g) (σ : ISub k' k) :
    Comp2 S (apZ (dat B k g) (semK S k a)) k k' σ.hom =
      Comp2 S (apZ (dat B k' (g.comp σ.hom)) (semK S k' (a.isub σ))) k' k' (Hom.id k') := by
  rw [Comp2_eq_res (hBne _ _ _ hmem), hBn _ _ _ hmem, semK_isubS hW ha]

include hA

theorem piC_at (hW : WfSig S) {g : Hom k m} {U V : Tm} (h : (Comp2 S (piC m A B) m k g).ty U V) :
    ∃ A1 B1 A1' B1', RedT S k U (.pi A1 B1) ∧ RedT S k V (.pi A1' B1') ∧ (Comp2 S A m k g).ty A1 A1' ∧
      ∀ a a', (Comp2 S A m k g).el A1 a a' →
        (Comp2 S (apZ (dat B k g) (semK S k a)) k k (Hom.id k)).ty (B1.inst a) (B1'.inst a') := by
  rw [Comp2_piC A B hA] at h
  obtain ⟨⟨hU, hV, -⟩, hall, -⟩ := h
  have := hall k (ISub.id k)
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_isTyK hW hV), ISub.hom_id,
    Hom.comp_id] at this

theorem piC_coh {g : Hom k m} {U V : Tm} (h : (Comp2 S (piC m A B) m k g).ty U V) :
    cohPi S A B g U ∧ cohPi S A B g V := by
  rw [Comp2_piC A B hA] at h
  exact h.2.2

theorem piC_coh1 (hW : WfSig S) {g : Hom k m} {U V : Tm} (h : (Comp2 S (piC m A B) m k g).ty U V)
    (σ' : ISub k'' k) {A1 B1 A2 B2 : Tm} (h1 : RedT S k U (.pi A1 B1)) (h2 : RedT S k'' (U.isub σ') (.pi A2 B2)) :
    (Comp2 S A m k'' (g.comp σ'.hom)).ty (A1.isub σ') A2 ∧
    ∀ a a', (Comp2 S A m k'' (g.comp σ'.hom)).el (A1.isub σ') a a' →
      (Comp2 S (apZ (dat B k'' (g.comp σ'.hom)) (semK S k'' a)) k'' k'' (Hom.id k'')).ty
        ((B1.isub σ').inst a) (B2.inst a') := by
  have hU := (Comp2_ty_base h).2.1
  have := (piC_coh hA h).1 k (ISub.id k) k'' σ' A1 B1 A2 B2
    (by rwa [isub_id_of_closed (closed_of_isTyK hW hU)]) (by rwa [ISub.id_comp])
  simpa only [ISub.id_comp] using this

theorem piC_el_at (hW : WfSig S) {g : Hom k m} {U u v : Tm} (h : (Comp2 S (piC m A B) m k g).el U u v) :
    ∃ A1 B1, RedT S k U (.pi A1 B1) ∧ ∀ a a', (Comp2 S A m k g).el A1 a a' →
      (Comp2 S (apZ (dat B k g) (semK S k a)) k k (Hom.id k)).el (B1.inst a) (.app u a) (.app v a') := by
  rw [Comp2_piC A B hA] at h
  obtain ⟨hE, -, -, hall⟩ := h
  have := hall k (ISub.id k)
  have hU := isTyK_of_ty hW hE.1
  simp only [ISub.id_comp, ISub.hom_id, Hom.comp_id] at this
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_ty hW hE.1),
    isub_id_of_closed (closed_of_ty hW hE.2.1)] at this

variable (hW : WfSig S) (perA : PER2 S m A) (krX : KR2 S m (piC m A B))
  (perB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a))
include hW perA krX perB

/-- Coherence of a type whose restrictions reduce to related types. -/
theorem cohPi_expand {f : Hom k m} {T T' : Tm}
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (piC m A B) m k' (f.comp σ.hom)).ty U (T'.isub σ)) : cohPi S A B f T := by
  intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
  obtain ⟨U, rU, eU, hU⟩ := hall k1 σ
  obtain ⟨V, rV, eV, hV⟩ := hall k2 (σ.comp σ')
  have h1' := RedT.to_red hW rU eU h1
  have h2' := RedT.to_red hW rV eV h2
  have hUσ := (krX k1 (f.comp σ.hom) k2 σ' U (T'.isub σ) U U).1 hU
  rw [ISub.comp_hom, Tm.isub_isub] at hUσ
  obtain ⟨C1, D1, E1, F1, hC, hE, hCE, hDF⟩ := piC_at hA hW hUσ
  obtain ⟨hc1, hc2⟩ := piC_coh1 hA hW hU σ' h1' hC
  rw [ISub.comp_hom] at hc1 hc2
  obtain ⟨A2', B2', E1', F1', hA2, hE', hAE, hBF⟩ := piC_at hA hW hV
  obtain ⟨rfl, rfl⟩ : A2' = A2 ∧ B2' = B2 := by
    have := RedW.unique hA2.1 h2'.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : E1' = E1 ∧ F1' = F1 := by
    have := RedW.unique hE'.1 hE.1; injection this; constructor <;> assumption
  have P := perA k2 (f.comp (σ.comp σ').hom)
  have h12 := P.transTy hc1 (P.transTy hCE (P.symTy hAE))
  refine ⟨h12, fun a a' ha => ?_⟩
  have haa := P.reflEl h12 ha
  have Q := perB k2 _ _ (fib_mem ha) k2 (Hom.id k2)
  have x1 := hc2 a a haa
  have x2 := hDF a a (P.conv hc1 haa)
  have x3 := hBF a' a (P.symEl hAE (P.conv h12 ha))
  rw [← fib_code hW ha] at x3
  exact Q.transTy x1 (Q.transTy x2 (Q.symTy x3))

/-- Head expansion for `Π` types. -/
theorem heTy_piC {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T')
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (piC m A B) m k' (f.comp σ.hom)).ty U (T'.isub σ)) : (Comp2 S (piC m A B) m k f).ty T T' := by
  obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
  have hc' := (piC_coh hA hU0).2
  rw [Comp2_piC A B hA]
  refine ⟨base_expand hW hT e0 hU0, fun k' σ => ?_, cohPi_expand hA hW perA krX perB hall, hc'⟩
  obtain ⟨U, r, e, hU⟩ := hall k' σ
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := piC_at hA hW hU
  exact ⟨A1, B1, A1', B1', RedT.of_red hW r e h1, h2, h3, h4⟩

omit krX in
/-- Head expansion for elements of `Π` types. -/
theorem heEl_piC (krA : KR2 S m A) (hBne : ∀ k (f : Hom k m), ∀ a ∈ El A f, apZ (dat B k f) a ≠ ∅)
    (hBn : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
      res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a))
    (heB : ∀ k (f : Hom k m), ∀ a ∈ El A f, HE2 S k (apZ (dat B k f) a))
    {f : Hom k m} {T t t' : Tm} (hTT : (Comp2 S (piC m A B) m k f).ty T T)
    (ht : HasTy S k .one [] t T) (ht' : HasTy S k .one [] t' T)
    (hall : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (T.isub σ) ∧
      (Comp2 S (piC m A B) m k' (f.comp σ.hom)).el (T.isub σ) u (t'.isub σ)) :
    (Comp2 S (piC m A B) m k f).el T t t' := by
  obtain ⟨u0, -, e0, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
  have hcT := (piC_coh hA hTT).1
  have hTall := hTT
  rw [Comp2_piC A B hA] at hTall
  replace hTall := hTall.2.1
  rw [Comp2_piC A B hA]
  obtain ⟨hEB, hmem⟩ := el_expand hW ht e0 hu0
  refine ⟨hEB, hmem, hEB, fun k1 σ1 => ?_⟩
  obtain ⟨u1, -, -, hu1⟩ := hall k1 σ1
  obtain ⟨A1, B1, hR1, -⟩ := piC_el_at hA hW hu1
  refine ⟨A1, B1, hR1, fun a a' ha => ?_⟩
  simp only [ISub.id_comp, ISub.hom_id] at ha ⊢
  have hamem := fib_mem ha
  obtain ⟨A1x, B1x, A1y, B1y, hx, hy, -, hB⟩ := hTall k1 σ1
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hx.1 hR1.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
    have := RedW.unique hy.1 hR1.1; injection this; constructor <;> assumption
  have hBB := hB a a' ha
  have Q := perB k1 _ _ hamem k1 (Hom.id k1)
  have haT := (Comp2_el ha).1.1
  have ha'T := (Comp2_el ha).1.2.1
  have hpi : HasTy S k1 .one [] (t.isub σ1) (.pi A1y B1y) := (HasTy.isubS hW ht σ1).tyConv hR1.2
  have hpi' : HasTy S k1 .one [] (t'.isub σ1) (.pi A1y B1y) := (HasTy.isubS hW ht' σ1).tyConv hR1.2
  refine (heB k1 _ _ hamem k1 (Hom.id k1) (B1y.inst a) (B1y.inst a) (.app (t.isub σ1) a)
    (.app (t'.isub σ1) a')).2 (Q.reflTy hBB) (HasTy.app hpi haT)
    ((HasTy.app hpi' ha'T).tyConv (Comp2_ty_base hBB).2.2.2.2.2.symm) fun k3 σ3 => ?_
  obtain ⟨u3, r3, e3, hu3⟩ := hall k3 (σ1.comp σ3)
  refine ⟨.app u3 (a.isub σ3), ?_, ?_, ?_⟩
  · rw [isub_app, Tm.isub_isub]; exact red_app _ r3
  · have hTy : TyEq S k3 (T.isub (σ1.comp σ3)) (.pi (A1y.isub σ3) (B1y.isub σ3)) := by
      have := hR1.2.isub hW σ3
      rwa [Tm.isub_isub, isub_pi] at this
    rw [isub_app, Tm.isub_isub, isub_inst]
    exact EqTm.app (e3.tyConv hTy) (EqTm.refl (HasTy.isubS hW haT σ3))
  · rw [Hom.id_comp, cod_res hW hBne hBn haT hamem σ3, isub_inst, isub_app, Tm.isub_isub, ISub.comp_hom]
    obtain ⟨A3, B3, hR3, happ3⟩ := piC_el_at hA hW hu3
    obtain ⟨hc1, hc2⟩ := hcT k1 σ1 k3 σ3 A1y B1y A3 B3 hR1 hR3
    have haσ := (krA k1 (f.comp σ1.hom) k3 σ3 A1y A1y a a').2 ha
    rw [ISub.comp_hom] at haσ
    have P3 := perA k3 (f.comp (σ1.comp σ3).hom)
    have x := happ3 _ _ (P3.conv hc1 haσ)
    have hBc := hc2 _ _ (P3.reflEl hc1 haσ)
    have Q3 := perB k3 _ _ (fib_mem haσ) k3 (Hom.id k3)
    exact Q3.conv (Q3.symTy hBc) x

end pisig

section sig
variable {A B : V} (hA : A ≠ ∅)

include hA

theorem sigmaC_at (hW : WfSig S) {g : Hom k m} {U V : Tm} (h : (Comp2 S (sigmaC m A B) m k g).ty U V) :
    ∃ A1 B1 A1' B1', RedT S k U (.sigma A1 B1) ∧ RedT S k V (.sigma A1' B1') ∧ (Comp2 S A m k g).ty A1 A1' ∧
      ∀ a a', (Comp2 S A m k g).el A1 a a' →
        (Comp2 S (apZ (dat B k g) (semK S k a)) k k (Hom.id k)).ty (B1.inst a) (B1'.inst a') := by
  rw [Comp2_sigmaC A B hA] at h
  obtain ⟨⟨hU, hV, -⟩, hall, -⟩ := h
  have := hall k (ISub.id k)
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_isTyK hW hV), ISub.hom_id,
    Hom.comp_id] at this

theorem sigmaC_coh {g : Hom k m} {U V : Tm} (h : (Comp2 S (sigmaC m A B) m k g).ty U V) :
    cohSigma S A B g U ∧ cohSigma S A B g V := by
  rw [Comp2_sigmaC A B hA] at h
  exact h.2.2

theorem sigmaC_coh1 (hW : WfSig S) {g : Hom k m} {U V : Tm} (h : (Comp2 S (sigmaC m A B) m k g).ty U V)
    (σ' : ISub k'' k) {A1 B1 A2 B2 : Tm} (h1 : RedT S k U (.sigma A1 B1)) (h2 : RedT S k'' (U.isub σ') (.sigma A2 B2)) :
    (Comp2 S A m k'' (g.comp σ'.hom)).ty (A1.isub σ') A2 ∧
    ∀ a a', (Comp2 S A m k'' (g.comp σ'.hom)).el (A1.isub σ') a a' →
      (Comp2 S (apZ (dat B k'' (g.comp σ'.hom)) (semK S k'' a)) k'' k'' (Hom.id k'')).ty
        ((B1.isub σ').inst a) (B2.inst a') := by
  have hU := (Comp2_ty_base h).2.1
  have := (sigmaC_coh hA h).1 k (ISub.id k) k'' σ' A1 B1 A2 B2
    (by rwa [isub_id_of_closed (closed_of_isTyK hW hU)]) (by rwa [ISub.id_comp])
  simpa only [ISub.id_comp] using this

variable (hW : WfSig S) (perA : PER2 S m A) (krX : KR2 S m (sigmaC m A B))
  (perB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a))
include hW perA krX perB

/-- Coherence of a type whose restrictions reduce to related types. -/
theorem cohSigma_expand {f : Hom k m} {T T' : Tm}
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (sigmaC m A B) m k' (f.comp σ.hom)).ty U (T'.isub σ)) : cohSigma S A B f T := by
  intro k1 σ k2 σ' A1 B1 A2 B2 h1 h2
  obtain ⟨U, rU, eU, hU⟩ := hall k1 σ
  obtain ⟨V, rV, eV, hV⟩ := hall k2 (σ.comp σ')
  have h1' := RedT.to_red hW rU eU h1
  have h2' := RedT.to_red hW rV eV h2
  have hUσ := (krX k1 (f.comp σ.hom) k2 σ' U (T'.isub σ) U U).1 hU
  rw [ISub.comp_hom, Tm.isub_isub] at hUσ
  obtain ⟨C1, D1, E1, F1, hC, hE, hCE, hDF⟩ := sigmaC_at hA hW hUσ
  obtain ⟨hc1, hc2⟩ := sigmaC_coh1 hA hW hU σ' h1' hC
  rw [ISub.comp_hom] at hc1 hc2
  obtain ⟨A2', B2', E1', F1', hA2, hE', hAE, hBF⟩ := sigmaC_at hA hW hV
  obtain ⟨rfl, rfl⟩ : A2' = A2 ∧ B2' = B2 := by
    have := RedW.unique hA2.1 h2'.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : E1' = E1 ∧ F1' = F1 := by
    have := RedW.unique hE'.1 hE.1; injection this; constructor <;> assumption
  have P := perA k2 (f.comp (σ.comp σ').hom)
  have h12 := P.transTy hc1 (P.transTy hCE (P.symTy hAE))
  refine ⟨h12, fun a a' ha => ?_⟩
  have haa := P.reflEl h12 ha
  have Q := perB k2 _ _ (fib_mem ha) k2 (Hom.id k2)
  have x1 := hc2 a a haa
  have x2 := hDF a a (P.conv hc1 haa)
  have x3 := hBF a' a (P.symEl hAE (P.conv h12 ha))
  rw [← fib_code hW ha] at x3
  exact Q.transTy x1 (Q.transTy x2 (Q.symTy x3))

/-- Head expansion for `Σ` types. -/
theorem heTy_sigmaC {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T')
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (sigmaC m A B) m k' (f.comp σ.hom)).ty U (T'.isub σ)) : (Comp2 S (sigmaC m A B) m k f).ty T T' := by
  obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
  have hc' := (sigmaC_coh hA hU0).2
  rw [Comp2_sigmaC A B hA]
  refine ⟨base_expand hW hT e0 hU0, fun k' σ => ?_, cohSigma_expand hA hW perA krX perB hall, hc'⟩
  obtain ⟨U, r, e, hU⟩ := hall k' σ
  obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := sigmaC_at hA hW hU
  exact ⟨A1, B1, A1', B1', RedT.of_red hW r e h1, h2, h3, h4⟩

omit krX perA perB in
theorem sigmaC_el_at {g : Hom k m} {U u v : Tm} (h : (Comp2 S (sigmaC m A B) m k g).el U u v) :
    ∃ A1 B1, RedT S k U (.sigma A1 B1) ∧ (Comp2 S A m k g).el A1 (.fst u) (.fst v) ∧
      (Comp2 S (apZ (dat B k g) (semK S k (.fst u))) k k (Hom.id k)).el (B1.inst (.fst u)) (.snd u) (.snd v) := by
  rw [Comp2_sigmaC A B hA] at h
  obtain ⟨hE, -, -, hall⟩ := h
  have := hall k (ISub.id k)
  have hU := isTyK_of_ty hW hE.1
  simp only [ISub.id_comp, ISub.hom_id, Hom.comp_id] at this
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_ty hW hE.1),
    isub_id_of_closed (closed_of_ty hW hE.2.1)] at this

omit krX in
/-- Head expansion for elements of `Σ` types. -/
theorem heEl_sigmaC (krA : KR2 S m A) (heA : HE2 S m A)
    (hBne : ∀ k (f : Hom k m), ∀ a ∈ El A f, apZ (dat B k f) a ≠ ∅)
    (hBn : ∀ k (f : Hom k m), ∀ a ∈ El A f, ∀ n (h : Hom n k),
      res h (apZ (dat B k f) a) = apZ (dat B n (f.comp h)) (res h a))
    (heB : ∀ k (f : Hom k m), ∀ a ∈ El A f, HE2 S k (apZ (dat B k f) a))
    {f : Hom k m} {T t t' : Tm} (hTT : (Comp2 S (sigmaC m A B) m k f).ty T T)
    (ht : HasTy S k .one [] t T) (ht' : HasTy S k .one [] t' T)
    (hall : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (T.isub σ) ∧
      (Comp2 S (sigmaC m A B) m k' (f.comp σ.hom)).el (T.isub σ) u (t'.isub σ)) :
    (Comp2 S (sigmaC m A B) m k f).el T t t' := by
  obtain ⟨u0, -, e0, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
  have hcT := (sigmaC_coh hA hTT).1
  have hTall := hTT
  rw [Comp2_sigmaC A B hA] at hTall
  replace hTall := hTall.2.1
  rw [Comp2_sigmaC A B hA]
  obtain ⟨hEB, hmem⟩ := el_expand hW ht e0 hu0
  refine ⟨hEB, hmem, hEB, fun k1 σ1 => ?_⟩
  obtain ⟨u1, -, -, hu1⟩ := hall k1 σ1
  obtain ⟨A1, B1, hR1, -, -⟩ := sigmaC_el_at hA hW hu1
  obtain ⟨A1x, B1x, A1y, B1y, hx, hy, hAA, hB⟩ := hTall k1 σ1
  obtain ⟨rfl, rfl⟩ : A1x = A1 ∧ B1x = B1 := by
    have := RedW.unique hx.1 hR1.1; injection this; constructor <;> assumption
  obtain ⟨rfl, rfl⟩ : A1y = A1x ∧ B1y = B1x := by
    have := RedW.unique hy.1 hR1.1; injection this; constructor <;> assumption
  have hsig : HasTy S k1 .one [] (t.isub σ1) (.sigma A1y B1y) := (HasTy.isubS hW ht σ1).tyConv hR1.2
  have hsig' : HasTy S k1 .one [] (t'.isub σ1) (.sigma A1y B1y) := (HasTy.isubS hW ht' σ1).tyConv hR1.2
  have hTy : ∀ k3 (σ3 : ISub k3 k1), TyEq S k3 (T.isub (σ1.comp σ3)) (.sigma (A1y.isub σ3) (B1y.isub σ3)) := by
    intro k3 σ3
    have := hR1.2.isub hW σ3
    rwa [Tm.isub_isub, isub_sigma] at this
  have P1 := perA k1 (f.comp σ1.hom)
  -- the first projections
  have hfst : (Comp2 S A m k1 (f.comp σ1.hom)).el A1y (.fst (t.isub σ1)) (.fst (t'.isub σ1)) := by
    refine (heA k1 _ A1y A1y _ _).2 (P1.reflTy hAA) (HasTy.fst hsig) (HasTy.fst hsig') fun k3 σ3 => ?_
    obtain ⟨u3, r3, e3, hu3⟩ := hall k3 (σ1.comp σ3)
    refine ⟨.fst u3, ?_, ?_, ?_⟩
    · rw [isub_fst, Tm.isub_isub]; exact red_fst r3
    · rw [isub_fst, Tm.isub_isub]; exact EqTm.fst (e3.tyConv (hTy k3 σ3))
    · rw [isub_fst, Tm.isub_isub, ISub.comp_hom]
      obtain ⟨A3, B3, hR3, hf3, -⟩ := sigmaC_el_at hA hW hu3
      obtain ⟨hc1, -⟩ := hcT k1 σ1 k3 σ3 A1y B1y A3 B3 hR1 hR3
      exact (perA k3 _).conv ((perA k3 _).symTy hc1) hf3
  refine ⟨A1y, B1y, hR1, by simpa only [ISub.id_comp] using hfst, ?_⟩
  simp only [ISub.id_comp, ISub.hom_id]
  have hamem := fib_mem hfst
  have hBB := hB _ _ (P1.reflEl hAA hfst)
  have Q := perB k1 _ _ hamem k1 (Hom.id k1)
  refine (heB k1 _ _ hamem k1 (Hom.id k1) (B1y.inst (.fst (t.isub σ1))) (B1y.inst (.fst (t.isub σ1)))
    (.snd (t.isub σ1)) (.snd (t'.isub σ1))).2 hBB (HasTy.snd hsig) ?_ fun k3 σ3 => ?_
  · have hBB' := hB _ _ hfst
    exact (HasTy.snd hsig').tyConv (Comp2_ty_base hBB').2.2.2.2.2.symm
  obtain ⟨u3, r3, e3, hu3⟩ := hall k3 (σ1.comp σ3)
  refine ⟨.snd u3, ?_, ?_, ?_⟩
  · rw [isub_snd, Tm.isub_isub]; exact red_snd r3
  · rw [isub_snd, Tm.isub_isub, isub_inst, isub_fst, Tm.isub_isub]
    exact EqTm.snd (e3.tyConv (hTy k3 σ3))
  · have hfT := (Comp2_el hfst).1.1
    rw [Hom.id_comp, cod_res hW hBne hBn hfT hamem σ3, isub_inst, isub_snd, isub_fst, Tm.isub_isub, Tm.isub_isub,
      ISub.comp_hom]
    obtain ⟨A3, B3, hR3, hf3, hs3⟩ := sigmaC_el_at hA hW hu3
    obtain ⟨hc1, hc2⟩ := hcT k1 σ1 k3 σ3 A1y B1y A3 B3 hR1 hR3
    have P3 := perA k3 (f.comp (σ1.comp σ3).hom)
    have hfσ := (krA k1 (f.comp σ1.hom) k3 σ3 A1y A1y _ _).2 hfst
    rw [ISub.comp_hom, isub_fst, isub_fst, Tm.isub_isub, Tm.isub_isub] at hfσ
    -- `fst (t σ1 σ3)` and `fst u3` are related
    have hfu := P3.transEl hc1 hfσ (P3.symEl hc1 (P3.conv (P3.symTy hc1) hf3))
    have hBc := hc2 _ _ hfu
    have Q3 := perB k3 _ _ (fib_mem hfσ) k3 (Hom.id k3)
    rw [← fib_code hW hfu] at hs3
    exact Q3.conv (Q3.symTy hBc) hs3

end sig


/-! ### Path types and `(i : I) → L` -/

theorem ISub.cons_comp (r : I) (hr : r.Scoped k') (σ : ISub k' k) (σ' : ISub k'' k') :
    (ISub.cons r hr σ).comp σ' = ISub.cons (r.subst σ'.τ) (I.scoped_subst hr σ'.sc) (σ.comp σ') := by
  ext i; rcases i with _ | i <;> rfl

section path
variable {L a0 a1 : V} (hLne : L ≠ ∅) (hW : WfSig S)
include hLne hW

theorem pathC_clause {g : Hom k m} {U V : Tm} (h : (Comp2 S (pathC m L a0 a1) m k g).ty U V) :
    ∃ L1 b0 b1 L1' b0' b1', RedT S k U (.path L1 b0 b1) ∧ RedT S k V (.path L1' b0' b1') ∧
      (Comp2 S L (m + 1) (k + 1) ((Hom.lift g).comp (ISub.id k).up.hom)).ty L1 L1' ∧
      (∀ (r r' : I) (hr : r.Scoped k) (hr' : r'.Scoped k), I.Eq r r' →
        (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons r hr (ISub.id k)).hom)).ty (L1.dinst r) (L1'.dinst r')) ∧
      (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons .zero trivial (ISub.id k)).hom)).el (L1.dinst .zero) b0 b0' ∧
      (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons .one trivial (ISub.id k)).hom)).el (L1.dinst .one) b1 b1' := by
  rw [Comp2_pathC L a0 a1 hLne] at h
  obtain ⟨⟨hU, hV, -⟩, hall, -⟩ := h
  have := hall k (ISub.id k)
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_isTyK hW hV)] at this

omit hW in
theorem pathC_coh {g : Hom k m} {U V : Tm} (h : (Comp2 S (pathC m L a0 a1) m k g).ty U V) :
    cohPath S L g U ∧ cohPath S L g V := by
  rw [Comp2_pathC L a0 a1 hLne] at h
  exact h.2.2

theorem pathC_coh1 {g : Hom k m} {U V : Tm} (h : (Comp2 S (pathC m L a0 a1) m k g).ty U V)
    (σ' : ISub k'' k) {L1 b0 b1 L2 c0 c1 : Tm} (h1 : RedT S k U (.path L1 b0 b1))
    (h2 : RedT S k'' (U.isub σ') (.path L2 c0 c1)) :
    (Comp2 S L (m + 1) (k'' + 1) ((Hom.lift g).comp σ'.up.hom)).ty (L1.isub σ'.up) L2 ∧
    (Comp2 S L (m + 1) k'' ((Hom.lift g).comp (ISub.cons .zero trivial σ').hom)).el
      (L2.dinst .zero) (b0.isub σ') c0 ∧
    (Comp2 S L (m + 1) k'' ((Hom.lift g).comp (ISub.cons .one trivial σ').hom)).el
      (L2.dinst .one) (b1.isub σ') c1 := by
  have hU := (Comp2_ty_base h).2.1
  have := (pathC_coh hLne h).1 k (ISub.id k) k'' σ' L1 b0 b1 L2 c0 c1
    (by rwa [isub_id_of_closed (closed_of_isTyK hW hU)]) (by rwa [ISub.id_comp])
  simpa only [ISub.id_comp] using this

theorem pathC_el_at {g : Hom k m} {U u v : Tm} (h : (Comp2 S (pathC m L a0 a1) m k g).el U u v) :
    ∃ L1 b0 b1, RedT S k U (.path L1 b0 b1) ∧
      (∀ (r r' : I) (hr : r.Scoped k) (hr' : r'.Scoped k), I.Eq r r' →
        (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons r hr (ISub.id k)).hom)).el (L1.dinst r)
          (.papp u r) (.papp v r')) ∧
      (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons .zero trivial (ISub.id k)).hom)).el (L1.dinst .zero)
        (.papp u .zero) b0 ∧
      (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons .one trivial (ISub.id k)).hom)).el (L1.dinst .one)
        (.papp u .one) b1 := by
  rw [Comp2_pathC L a0 a1 hLne] at h
  obtain ⟨hE, -, -, hall⟩ := h
  have := hall k (ISub.id k)
  have hU := isTyK_of_ty hW hE.1
  simp only [ISub.id_comp] at this
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_ty hW hE.1),
    isub_id_of_closed (closed_of_ty hW hE.2.1)] at this

variable (perL : PER2 S (m + 1) L) (krL : KR2 S (m + 1) L) (krX : KR2 S m (pathC m L a0 a1))
include perL krX

omit krL in
theorem cohPath_expand {f : Hom k m} {T T' : Tm}
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (pathC m L a0 a1) m k' (f.comp σ.hom)).ty U (T'.isub σ)) : cohPath S L f T := by
  intro k1 σ k2 σ' L1 b0 b1 L2 c0 c1 h1 h2
  obtain ⟨U, rU, eU, hU⟩ := hall k1 σ
  obtain ⟨V, rV, eV, hV⟩ := hall k2 (σ.comp σ')
  have h1' := RedT.to_red hW rU eU h1
  have h2' := RedT.to_red hW rV eV h2
  have hUσ := (krX k1 (f.comp σ.hom) k2 σ' U (T'.isub σ) U U).1 hU
  rw [ISub.comp_hom, Tm.isub_isub] at hUσ
  obtain ⟨M1, d0, d1, E1, e0', e1', hM, hE, hME, hrrM, hd0, hd1⟩ := pathC_clause hLne hW hUσ
  obtain ⟨hc, hc0, hc1⟩ := pathC_coh1 hLne hW hU σ' h1' hM
  obtain ⟨L2', c0', c1', E1', e0'', e1'', hL2, hE', hLE, hrrL, hl0, hl1⟩ := pathC_clause hLne hW hV
  obtain ⟨rfl, rfl, rfl⟩ : L2 = L2' ∧ c0 = c0' ∧ c1 = c1' := by
    have := RedW.unique h2'.1 hL2.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  obtain ⟨rfl, rfl, rfl⟩ : E1' = E1 ∧ e0'' = e0' ∧ e1'' = e1' := by
    have := RedW.unique hE'.1 hE.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  rw [lift_hom_comp, ISub.comp_id] at hME hLE
  rw [lift_hom_comp] at hc
  rw [lift_cons] at hc0 hc1
  rw [lift_cons, ISub.comp_id] at hd0 hd1 hl0 hl1
  have P := perL (k2 + 1) ((Hom.lift f).comp (σ.comp σ').up.hom)
  have ends : ∀ (e : I) (he : e = .zero ∨ e = .one) {x y z w : Tm},
      (Comp2 S L (m + 1) k2 ((Hom.lift f).comp (ISub.cons e (by rcases he with rfl | rfl <;> trivial)
        (σ.comp σ')).hom)).el (M1.dinst e) x y →
      (Comp2 S L (m + 1) k2 ((Hom.lift f).comp (ISub.cons e (by rcases he with rfl | rfl <;> trivial)
        (σ.comp σ')).hom)).el (M1.dinst e) y z →
      (Comp2 S L (m + 1) k2 ((Hom.lift f).comp (ISub.cons e (by rcases he with rfl | rfl <;> trivial)
        (σ.comp σ')).hom)).el (L2.dinst e) w z →
      (Comp2 S L (m + 1) k2 ((Hom.lift f).comp (ISub.cons e (by rcases he with rfl | rfl <;> trivial)
        (σ.comp σ')).hom)).el (L2.dinst e) x w := by
    intro e he x y z w h1 h2 h3
    have hes : e.Scoped k2 := by rcases he with rfl | rfl <;> trivial
    have tM := hrrM e e hes hes (I_eq_refl _)
    have tL := hrrL e e hes hes (I_eq_refl _)
    rw [lift_cons, ISub.comp_id] at tM tL
    have Q := perL k2 ((Hom.lift f).comp (ISub.cons e hes (σ.comp σ')).hom)
    have x13 := Q.conv (Q.transTy tM (Q.symTy tL)) (Q.transEl tM h1 h2)
    exact Q.transEl tL x13 (Q.symEl tL h3)
  exact ⟨P.transTy hc (P.transTy hME (P.symTy hLE)), ends .zero (.inl rfl) hc0 hd0 hl0,
    ends .one (.inr rfl) hc1 hd1 hl1⟩

omit krL in
/-- Head expansion for path types. -/
theorem heTy_pathC {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T')
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (pathC m L a0 a1) m k' (f.comp σ.hom)).ty U (T'.isub σ)) :
    (Comp2 S (pathC m L a0 a1) m k f).ty T T' := by
  obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
  have hc' := (pathC_coh hLne hU0).2
  rw [Comp2_pathC L a0 a1 hLne]
  refine ⟨base_expand hW hT e0 hU0, fun k' σ => ?_, cohPath_expand hLne hW perL krX hall, hc'⟩
  obtain ⟨U, r, e, hU⟩ := hall k' σ
  obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, h3, hrr, h4, h5⟩ := pathC_clause hLne hW hU
  rw [lift_hom_comp, ISub.comp_id] at h3
  rw [lift_cons, ISub.comp_id] at h4 h5
  refine ⟨L1, b0, b1, L1', b0', b1', RedT.of_red hW r e h1, h2, h3, fun r r' hr hr' he => ?_, h4, h5⟩
  have := hrr r r' hr hr' he
  rwa [lift_cons, ISub.comp_id] at this

omit krX in
include krL in
/-- Head expansion for elements of path types. -/
theorem heEl_pathC (heL : HE2 S (m + 1) L) (perX : PER2 S m (pathC m L a0 a1)) (krX : KR2 S m (pathC m L a0 a1))
    {f : Hom k m} {T t t' : Tm} (hTT : (Comp2 S (pathC m L a0 a1) m k f).ty T T)
    (ht : HasTy S k .one [] t T) (ht' : HasTy S k .one [] t' T)
    (hall : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (T.isub σ) ∧
      (Comp2 S (pathC m L a0 a1) m k' (f.comp σ.hom)).el (T.isub σ) u (t'.isub σ)) :
    (Comp2 S (pathC m L a0 a1) m k f).el T t t' := by
  obtain ⟨u0, -, e0, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
  have hcT := (pathC_coh hLne hTT).1
  have hTall := hTT
  rw [Comp2_pathC L a0 a1 hLne] at hTall
  replace hTall := hTall.2.1
  have hTT' := hTT
  rw [Comp2_pathC L a0 a1 hLne]
  obtain ⟨hEB, hmem⟩ := el_expand hW ht e0 hu0
  refine ⟨hEB, hmem, hEB, fun k1 σ1 => ?_⟩
  obtain ⟨u1, -, -, hu1⟩ := hall k1 σ1
  obtain ⟨L1, b0, b1, hR1, -, he0, he1⟩ := pathC_el_at hLne hW hu1
  obtain ⟨L1x, b0x, b1x, L1y, b0y, b1y, hx, hy, hLL, hrr, -, -⟩ := hTall k1 σ1
  obtain ⟨rfl, rfl, rfl⟩ : L1x = L1 ∧ b0x = b0 ∧ b1x = b1 := by
    have := RedW.unique hx.1 hR1.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  obtain ⟨rfl, rfl, rfl⟩ : L1y = L1x ∧ b0y = b0x ∧ b1y = b1x := by
    have := RedW.unique hy.1 hR1.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
  rw [lift_cons, ISub.comp_id] at he0 he1
  simp only [ISub.id_comp]
  have hp : HasTy S k1 .one [] (t.isub σ1) (.path L1y b0y b1y) := (HasTy.isubS hW ht σ1).tyConv hR1.2
  -- applications at equal interval terms, against any term related to `t'` at all restrictions
  have key : ∀ (w : Tm), HasTy S k1 .one [] w (.path L1y b0y b1y) →
      (∀ k3 (σ3 : ISub k3 k1) u, (Comp2 S (pathC m L a0 a1) m k3 (f.comp (σ1.comp σ3).hom)).el
        (T.isub (σ1.comp σ3)) u (t'.isub (σ1.comp σ3)) →
        (Comp2 S (pathC m L a0 a1) m k3 (f.comp (σ1.comp σ3).hom)).el (T.isub (σ1.comp σ3)) u (w.isub σ3)) →
      ∀ (r r' : I) (hr : r.Scoped k1) (hr' : r'.Scoped k1), I.Eq r r' →
      (Comp2 S L (m + 1) k1 ((Hom.lift f).comp (ISub.cons r hr σ1).hom)).el (L1y.dinst r)
        (.papp (t.isub σ1) r) (.papp w r') := by
    intro w hw hrel r r' hr hr' hE
    have hTr := hrr r r' hr hr' hE
    refine (heL k1 _ (L1y.dinst r) (L1y.dinst r) (.papp (t.isub σ1) r) (.papp w r')).2
      ((perL _ _).reflTy hTr) (HasTy.papp hp hr)
      ((HasTy.papp hw hr').tyConv (Comp2_ty_base hTr).2.2.2.2.2.symm) fun k3 σ3 => ?_
    obtain ⟨u3, r3, e3, hu3⟩ := hall k3 (σ1.comp σ3)
    have hrσ : (r.subst σ3.τ).Scoped k3 := I.scoped_subst hr σ3.sc
    have hrσ' : (r'.subst σ3.τ).Scoped k3 := I.scoped_subst hr' σ3.sc
    refine ⟨.papp u3 (r.subst σ3.τ), ?_, ?_, ?_⟩
    · rw [isub_papp, Tm.isub_isub]; exact red_papp _ r3
    · have hTy : TyEq S k3 (T.isub (σ1.comp σ3)) (.path (L1y.isub σ3.up) (b0y.isub σ3) (b1y.isub σ3)) := by
        have := hR1.2.isub hW σ3
        rwa [Tm.isub_isub, isub_path] at this
      rw [isub_papp, Tm.isub_isub, isub_dinst]
      exact EqTm.papp (e3.tyConv hTy) hrσ hrσ fun _ => rfl
    · rw [isub_papp, isub_dinst, Hom.comp_assoc, ← ISub.hom_comp, ISub.cons_comp]
      obtain ⟨L3, c0, c1, hR3, hp3, -, -⟩ := pathC_el_at hLne hW (hrel k3 σ3 u3 hu3)
      have hc := hcT k1 σ1 k3 σ3 L1y b0y b1y L3 c0 c1 hR1 hR3
      have hl := line_ty hW krL (σ1.comp σ3) hc.1 (r.subst σ3.τ) hrσ
      have x := hp3 (r.subst σ3.τ) (r'.subst σ3.τ) hrσ hrσ' (Meta.I_eq_subst hE _)
      rw [lift_cons, ISub.comp_id] at x
      have P := perL k3 ((Hom.lift f).comp (ISub.cons (r.subst σ3.τ) hrσ (σ1.comp σ3)).hom)
      exact P.conv (P.symTy hl) x
  have hp' : HasTy S k1 .one [] (t'.isub σ1) (.path L1y b0y b1y) := (HasTy.isubS hW ht' σ1).tyConv hR1.2
  have keyT := key (t'.isub σ1) hp' fun k3 σ3 u hu => by rwa [Tm.isub_isub]
  -- `u1` is related to `t'` at all restrictions
  have hu1T : HasTy S k1 .one [] u1 (.path L1y b0y b1y) := (Comp2_el hu1).1.1.tyConv hR1.2
  have keyU := key u1 hu1T fun k3 σ3 u hu => by
    have h1 := (krX k1 (f.comp σ1.hom) k3 σ3 (T.isub σ1) (T.isub σ1) u1 (t'.isub σ1)).2 hu1
    have h2 := (krX k (f) k3 (σ1.comp σ3) T T t t).1 hTT'
    rw [ISub.comp_hom, Tm.isub_isub, Tm.isub_isub] at h1
    have P := perX k3 (f.comp (σ1.comp σ3).hom)
    exact P.transEl h2 hu (P.symEl h2 h1)
  refine ⟨L1y, b0y, b1y, hR1, keyT, ?_, ?_⟩
  · have hT0 := hrr .zero .zero trivial trivial (fun _ => rfl)
    exact (perL _ _).transEl hT0 (keyU .zero .zero trivial trivial (fun _ => rfl)) he0
  · have hT1 := hrr .one .one trivial trivial (fun _ => rfl)
    exact (perL _ _).transEl hT1 (keyU .one .one trivial trivial (fun _ => rfl)) he1

end path

section ipi
variable {L : V} (hLne : L ≠ ∅) (hW : WfSig S)
include hLne hW

theorem ipiC_clause {g : Hom k m} {U V : Tm} (h : (Comp2 S (ipiC m L) m k g).ty U V) :
    ∃ L1 L1', RedT S k U (.ipi L1) ∧ RedT S k V (.ipi L1') ∧
      (Comp2 S L (m + 1) (k + 1) ((Hom.lift g).comp (ISub.id k).up.hom)).ty L1 L1' ∧
      (∀ (r r' : I) (hr : r.Scoped k) (hr' : r'.Scoped k), I.Eq r r' →
        (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons r hr (ISub.id k)).hom)).ty (L1.dinst r) (L1'.dinst r')) := by
  rw [Comp2_ipiC L hLne] at h
  obtain ⟨⟨hU, hV, -⟩, hall, -⟩ := h
  have := hall k (ISub.id k)
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_isTyK hW hV)] at this

omit hW in
theorem ipiC_coh {g : Hom k m} {U V : Tm} (h : (Comp2 S (ipiC m L) m k g).ty U V) :
    cohIPi S L g U ∧ cohIPi S L g V := by
  rw [Comp2_ipiC L hLne] at h
  exact h.2.2

theorem ipiC_coh1 {g : Hom k m} {U V : Tm} (h : (Comp2 S (ipiC m L) m k g).ty U V)
    (σ' : ISub k'' k) {L1 L2 : Tm} (h1 : RedT S k U (.ipi L1)) (h2 : RedT S k'' (U.isub σ') (.ipi L2)) :
    (Comp2 S L (m + 1) (k'' + 1) ((Hom.lift g).comp σ'.up.hom)).ty (L1.isub σ'.up) L2 := by
  have hU := (Comp2_ty_base h).2.1
  have := (ipiC_coh hLne h).1 k (ISub.id k) k'' σ' L1 L2
    (by rwa [isub_id_of_closed (closed_of_isTyK hW hU)]) (by rwa [ISub.id_comp])
  simpa only [ISub.id_comp] using this

theorem ipiC_el_at {g : Hom k m} {U u v : Tm} (h : (Comp2 S (ipiC m L) m k g).el U u v) :
    ∃ L1, RedT S k U (.ipi L1) ∧
      ∀ (r r' : I) (hr : r.Scoped k) (hr' : r'.Scoped k), I.Eq r r' →
        (Comp2 S L (m + 1) k ((Hom.lift g).comp (ISub.cons r hr (ISub.id k)).hom)).el (L1.dinst r)
          (.papp u r) (.papp v r') := by
  rw [Comp2_ipiC L hLne] at h
  obtain ⟨hE, -, -, hall⟩ := h
  have := hall k (ISub.id k)
  have hU := isTyK_of_ty hW hE.1
  simp only [ISub.id_comp] at this
  rwa [isub_id_of_closed (closed_of_isTyK hW hU), isub_id_of_closed (closed_of_ty hW hE.1),
    isub_id_of_closed (closed_of_ty hW hE.2.1)] at this

variable (perL : PER2 S (m + 1) L) (krL : KR2 S (m + 1) L) (krX : KR2 S m (ipiC m L))
include perL krX

omit krL in
theorem cohIPi_expand {f : Hom k m} {T T' : Tm}
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (ipiC m L) m k' (f.comp σ.hom)).ty U (T'.isub σ)) : cohIPi S L f T := by
  intro k1 σ k2 σ' L1 L2 h1 h2
  obtain ⟨U, rU, eU, hU⟩ := hall k1 σ
  obtain ⟨V, rV, eV, hV⟩ := hall k2 (σ.comp σ')
  have h1' := RedT.to_red hW rU eU h1
  have h2' := RedT.to_red hW rV eV h2
  have hUσ := (krX k1 (f.comp σ.hom) k2 σ' U (T'.isub σ) U U).1 hU
  rw [ISub.comp_hom, Tm.isub_isub] at hUσ
  obtain ⟨M1, E1, hM, hE, hME, -⟩ := ipiC_clause hLne hW hUσ
  have hc := ipiC_coh1 hLne hW hU σ' h1' hM
  obtain ⟨L2', E1', hL2, hE', hLE, -⟩ := ipiC_clause hLne hW hV
  obtain rfl : L2' = L2 := by have := RedW.unique hL2.1 h2'.1; injection this
  obtain rfl : E1' = E1 := by have := RedW.unique hE'.1 hE.1; injection this
  rw [lift_hom_comp, ISub.comp_id] at hME hLE
  rw [lift_hom_comp] at hc
  have P := perL (k2 + 1) ((Hom.lift f).comp (σ.comp σ').up.hom)
  exact P.transTy hc (P.transTy hME (P.symTy hLE))

omit krL in
/-- Head expansion for types `(i : I) → L`. -/
theorem heTy_ipiC {f : Hom k m} {T T' : Tm} (hT : IsTyK S k T) (hT' : IsTyK S k T')
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (ipiC m L) m k' (f.comp σ.hom)).ty U (T'.isub σ)) :
    (Comp2 S (ipiC m L) m k f).ty T T' := by
  obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
  have hc' := (ipiC_coh hLne hU0).2
  rw [Comp2_ipiC L hLne]
  refine ⟨base_expand hW hT e0 hU0, fun k' σ => ?_, cohIPi_expand hLne hW perL krX hall, hc'⟩
  obtain ⟨U, r, e, hU⟩ := hall k' σ
  obtain ⟨L1, L1', h1, h2, h3, hrr⟩ := ipiC_clause hLne hW hU
  rw [lift_hom_comp, ISub.comp_id] at h3
  refine ⟨L1, L1', RedT.of_red hW r e h1, h2, h3, fun r r' hr hr' he => ?_⟩
  have := hrr r r' hr hr' he
  rwa [lift_cons, ISub.comp_id] at this

omit krX in
include krL in
/-- Head expansion for elements of types `(i : I) → L`. -/
theorem heEl_ipiC (heL : HE2 S (m + 1) L)
    {f : Hom k m} {T t t' : Tm} (hTT : (Comp2 S (ipiC m L) m k f).ty T T)
    (ht : HasTy S k .one [] t T) (ht' : HasTy S k .one [] t' T)
    (hall : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (T.isub σ) ∧
      (Comp2 S (ipiC m L) m k' (f.comp σ.hom)).el (T.isub σ) u (t'.isub σ)) :
    (Comp2 S (ipiC m L) m k f).el T t t' := by
  obtain ⟨u0, -, e0, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
  have hcT := (ipiC_coh hLne hTT).1
  have hTall := hTT
  rw [Comp2_ipiC L hLne] at hTall
  replace hTall := hTall.2.1
  rw [Comp2_ipiC L hLne]
  obtain ⟨hEB, hmem⟩ := el_expand hW ht e0 hu0
  refine ⟨hEB, hmem, hEB, fun k1 σ1 => ?_⟩
  obtain ⟨u1, -, -, hu1⟩ := hall k1 σ1
  obtain ⟨L1, hR1, -⟩ := ipiC_el_at hLne hW hu1
  obtain ⟨L1x, L1y, hx, hy, hLL, hrr⟩ := hTall k1 σ1
  obtain rfl : L1x = L1 := by have := RedW.unique hx.1 hR1.1; injection this
  obtain rfl : L1y = L1x := by have := RedW.unique hy.1 hR1.1; injection this
  simp only [ISub.id_comp]
  have hp : HasTy S k1 .one [] (t.isub σ1) (.ipi L1y) := (HasTy.isubS hW ht σ1).tyConv hR1.2
  have hp' : HasTy S k1 .one [] (t'.isub σ1) (.ipi L1y) := (HasTy.isubS hW ht' σ1).tyConv hR1.2
  refine ⟨L1y, hR1, fun r r' hr hr' hE => ?_⟩
  have hTr := hrr r r' hr hr' hE
  refine (heL k1 _ (L1y.dinst r) (L1y.dinst r) (.papp (t.isub σ1) r) (.papp (t'.isub σ1) r')).2
    ((perL _ _).reflTy hTr) (HasTy.iapp hp hr)
    ((HasTy.iapp hp' hr').tyConv (Comp2_ty_base hTr).2.2.2.2.2.symm) fun k3 σ3 => ?_
  obtain ⟨u3, r3, e3, hu3⟩ := hall k3 (σ1.comp σ3)
  have hrσ : (r.subst σ3.τ).Scoped k3 := I.scoped_subst hr σ3.sc
  have hrσ' : (r'.subst σ3.τ).Scoped k3 := I.scoped_subst hr' σ3.sc
  refine ⟨.papp u3 (r.subst σ3.τ), ?_, ?_, ?_⟩
  · rw [isub_papp, Tm.isub_isub]; exact red_papp _ r3
  · have hTy : TyEq S k3 (T.isub (σ1.comp σ3)) (.ipi (L1y.isub σ3.up)) := by
      have := hR1.2.isub hW σ3
      rwa [Tm.isub_isub, isub_ipi] at this
    rw [isub_papp, Tm.isub_isub, isub_dinst]
    exact EqTm.iapp (e3.tyConv hTy) hrσ hrσ fun _ => rfl
  · rw [isub_papp, Tm.isub_isub, isub_dinst, Hom.comp_assoc, ← ISub.hom_comp, ISub.cons_comp]
    obtain ⟨L3, hR3, hp3⟩ := ipiC_el_at hLne hW hu3
    have hc := hcT k1 σ1 k3 σ3 L1y L3 hR1 hR3
    have hl := line_ty hW krL (σ1.comp σ3) hc (r.subst σ3.τ) hrσ
    have x := hp3 (r.subst σ3.τ) (r'.subst σ3.τ) hrσ hrσ' (Meta.I_eq_subst hE _)
    rw [lift_cons, ISub.comp_id] at x
    have P := perL k3 ((Hom.lift f).comp (ISub.cons (r.subst σ3.τ) hrσ (σ1.comp σ3)).hom)
    exact P.conv (P.symTy hl) x

end ipi


/-! ### The empty type, universes and inductive types -/

section misc
variable (hW : WfSig S)
include hW

theorem he2_emptyC : HE2 S m (emptyC m) := by
  intro k f T T' t t'
  constructor
  · intro hT hT' hall
    obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
    rw [Comp2_emptyC]
    exact base_expand hW hT e0 hU0
  · intro hTT ht ht' hall
    obtain ⟨u0, -, -, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
    rw [Comp2_emptyC] at hu0
    exact hu0.elim

theorem he2_univC {l : ℕ} (ih : ∀ m' X, WF l m' X → HE2 S m' X) : HE2 S m (univC m l) := by
  intro k f T T' t t'
  constructor
  · intro hT hT' hall
    obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
    rw [Comp2_univC]
    refine ⟨base_expand hW hT e0 hU0, fun k' σ => ?_⟩
    obtain ⟨U, r, e, hU⟩ := hall k' σ
    rw [Comp2_univC] at hU
    obtain ⟨⟨hUt, hVt, -⟩, hc⟩ := hU
    have := hc k' (ISub.id k')
    rw [isub_id_of_closed (closed_of_isTyK hW hUt), isub_id_of_closed (closed_of_isTyK hW hVt)] at this
    exact ⟨RedT.of_red hW r e this.1, this.2⟩
  · intro hTT ht ht' hall
    obtain ⟨u0, -, e0, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
    have hTc := hTT
    rw [Comp2_univC] at hTc
    replace hTc := hTc.2
    obtain ⟨hEB, hmem⟩ := el_expand hW ht e0 hu0
    rw [Comp2_univC] at hu0 ⊢
    obtain ⟨-, -, hm0, -, hK0⟩ := hu0
    have hsem := semK_eq hW e0
    have hWF : WF l k (semK S k t) := by rw [hsem]; exact (ZFSet.mem_sep.1 hm0).2
    have hne : semK S k t ≠ ∅ := IsKV.ne_empty hWF.fib.kv
    refine ⟨hEB, hmem, by rw [hsem]; exact hm0, ?_, by rw [hsem]; exact hK0⟩
    have hU : ∀ k' (σ : ISub k' k), TyEq S k' (T.isub σ) (.univ l) := fun k' σ => (hTc k' σ).1.2
    have htU : ∀ k' (σ : ISub k' k) {x : Tm}, HasTy S k' .one [] x (T.isub σ) → HasTy S k' .one [] x (.univ l) :=
      fun k' σ x hx => hx.tyConv (hU k' σ)
    have hTid : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW (Comp2_ty_base hTT).2.1)
    have ht0 : HasTy S k .one [] t (.univ l) := htU k (ISub.id k) (by rw [hTid]; exact ht)
    have ht0' : HasTy S k .one [] t' (.univ l) := htU k (ISub.id k) (by rw [hTid]; exact ht')
    refine (ih k _ hWF k (Hom.id k) t t' t t).1 (tyk ht0) (tyk ht0') fun k' σ => ?_
    obtain ⟨u, r, e, hu⟩ := hall k' σ
    refine ⟨u, r, .inr ⟨l, e.tyConv (hU k' σ)⟩, ?_⟩
    rw [Comp2_univC] at hu
    obtain ⟨-, -, -, hty, -⟩ := hu
    rw [Hom.id_comp, Comp2_eq_res hne, ← semK_isubS hW ht0, semK_eq hW (e.tyConv (hU k' σ))]
    exact hty

omit hW in
/-- The argument clause of an inductive type, from that of the restricted base. -/
theorem argRel2_unbase {Θ : SData m} {k k'' : ℕ} (f : Hom k m) {k' : ℕ} (σ : ISub k' k) {σ' : ISub k'' k'}
    {ps ps' : Tm} (h : argRel2 S Θ (f.comp σ.hom) k'' σ' ps ps') : argRel2 S Θ f k'' (σ.comp σ') ps ps' := by
  intro k3 σ3 c C args args' hC hl hl' hr hrec hpt
  have := h k3 σ3 c C args args' hC hl hl' hr
    (fun j hj hj' hrj => DR2.rebase f (hrec j hj hj' hrj) σ.hom (σ'.comp σ3).hom
      (by rw [ISub.comp_assoc, ISub.hom_comp]))
    (fun j hj hj' hrj => (dataP2_base f σ.hom (σ'.comp σ3).hom).2
      (by rw [← ISub.hom_comp, ← ISub.comp_assoc]; exact hpt j hj hj' hrj))
  rw [ISub.comp_hom, ← ISub.comp_assoc] at this; exact this

omit hW in
theorem parRel2_unbase {Θ : SData m} {k k'' : ℕ} (f : Hom k m) {k' : ℕ} (σ : ISub k' k) {σ' : ISub k'' k'}
    {ps ps' : Tm} (h : parRel2 S Θ (f.comp σ.hom) k'' σ' ps ps') : parRel2 S Θ f k'' (σ.comp σ') ps ps' := by
  unfold parRel2 at h ⊢
  simp only [parEntry_base f σ σ'] at h
  exact h

/-- A related element of an inductive type at a stage, through a reduct. -/
theorem DR2At.expand {k0 : ℕ} {Θ : SData m} {f : Hom k0 m} {d : ℕ} {D : DataDecl} {g : Hom k k0} {A t u t' : Tm}
    (h : DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A u t') (r : Red S t u) (e : EqTm S k .one [] t u A) :
    DR2At S d D (dataMem S Θ f) (dataP2 S Θ f) k g A t t' := by
  cases h with
  | con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    exact .con (by unfold dataMem at hm ⊢; rwa [semK_eq hW e]) hm' (e.trans heq) hC hA hpl (RedE.of_red r e ht) ht'
      hrs hrs' hreq hsc hsc' hl hl' hrec hpt
  | hcomp hm hm' heq hH hA hpl ht ht' hs hs' h12 h21 ha hu =>
    exact .hcomp (by unfold dataMem at hm ⊢; rwa [semK_eq hW e]) hm' (e.trans heq) hH hA hpl (RedE.of_red r e ht) ht'
      hs hs' h12 h21 ha hu

/-- A related pair of elements of an inductive type is related at its own stage. -/
theorem DR2.at_id {k0 : ℕ} {Θ : SData m} {f : Hom k0 m} {g : Hom k k0} {X x y : Tm}
    (h : DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g X x y) :
    DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k g X x y := by
  cases h with
  | intro he hh _ _ =>
    have hx := HasTy.eqL he
    have hy := HasTy.eqR he
    have := hh k (ISub.id k)
    rwa [isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW hx)), isub_id_of_closed (closed_of_ty hW hx),
      isub_id_of_closed (closed_of_ty hW hy), ISub.hom_id, Hom.comp_id] at this

/-- The coherence of an inductive type's normal forms, for a head expansion: through the reducts at a
restriction and at a further restriction. -/
theorem cohData_expand {Θ : SData m}
    (hP : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V),
      PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)))
    (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X)
    {f : Hom k m} {T T' : Tm}
    (hall : ∀ k' (σ : ISub k' k), ∃ U, Red S (T.isub σ) U ∧ TyEq S k' (T.isub σ) U ∧
      (Comp2 S (dataC Θ) m k' (f.comp σ.hom)).ty U (T'.isub σ)) : cohData S Θ f T := by
  intro k' σ k'' σ' ps1 ps2 h1 h2
  obtain ⟨U, r, e, hU⟩ := hall k' σ
  obtain ⟨U2, r2, e2, hU2⟩ := hall k'' (σ.comp σ')
  have hUb := Comp2_ty_base hU
  have hU2b := Comp2_ty_base hU2
  rw [Comp2_dataC] at hU hU2
  have hU1 : RedT S k' U (.data Θ.idx ps1) := RedT.to_red hW r e h1
  have hU2' : RedT S k'' U2 (.data Θ.idx ps2) := RedT.to_red hW r2 e2 h2
  have hUc := closed_of_isTyK hW hUb.2.1
  have hU2c := closed_of_isTyK hW hU2b.2.1
  -- the reduct at `σ`, at its own stage and at `σ'`
  obtain ⟨p0, -, f0, -, -, -, -, -, a00, -, -⟩ := hU.2.1 k' (ISub.id k')
  rw [isub_id_of_closed hUc] at f0
  obtain rfl : ps1 = p0 := (redT_data_eq (RedT.to_red hW hU1.1.1 hU1.2 f0)).symm
  obtain ⟨q, q', g1, g2, hql, hq'l, a12, a21, a11, a22, p12⟩ := hU.2.1 k'' σ'
  obtain ⟨c1, c2, c3⟩ := hU.2.2.1 k' (ISub.id k') k'' σ' ps1 q (by rw [isub_id_of_closed hUc]; exact hU1)
    (by rw [ISub.id_comp]; exact g1)
  -- the reduct at `σ ∘ σ'`, at its own stage
  obtain ⟨p2, p2', f1, f2, -, -, b12, b21, b11, b22, pb⟩ := hU2.2.1 k'' (ISub.id k'')
  rw [isub_id_of_closed hU2c] at f1
  obtain rfl : ps2 = p2 := (redT_data_eq (RedT.to_red hW hU2'.1.1 hU2'.2 f1)).symm
  have g2' : RedT S k'' (T'.isub (σ.comp σ')) (.data Θ.idx q') := by rw [← Tm.isub_isub]; exact g2
  rw [isub_id_of_closed (closed_of_isTyK hW hU2b.2.2.1)] at f2
  obtain rfl : q' = p2' := by have := RedW.unique g2'.1 f2.1; injection this
  -- everything at the base `f` and the restriction `σ ∘ σ'`
  have ub : ∀ {x y : Tm}, argRel2 S Θ (f.comp σ.hom) k'' σ' x y → argRelH Θ f S k'' (σ.comp σ').hom x y :=
    fun h => (argRel2_iff Θ _).1 (argRel2_unbase f σ h)
  have ub0 : ∀ {x y : Tm}, argRel2 S Θ (f.comp σ.hom) k'' ((ISub.id k').comp σ') x y →
      argRelH Θ f S k'' (σ.comp σ').hom x y := fun h => by rw [ISub.id_comp] at h; exact ub h
  have ub2 : ∀ {x y : Tm}, argRel2 S Θ (f.comp (σ.comp σ').hom) k'' (ISub.id k'') x y →
      argRelH Θ f S k'' (σ.comp σ').hom x y := fun h => by
    have := (argRel2_iff Θ _).1 (argRel2_unbase f (σ.comp σ') h); rwa [ISub.comp_id] at this
  have pb0 : ∀ {x y : Tm}, parRel2 S Θ (f.comp σ.hom) k'' ((ISub.id k').comp σ') x y →
      parRel2 S Θ f k'' (σ.comp σ') x y := fun h => by
    rw [ISub.id_comp] at h; exact parRel2_unbase f σ h
  have pb1 : ∀ {x y : Tm}, parRel2 S Θ (f.comp σ.hom) k'' σ' x y → parRel2 S Θ f k'' (σ.comp σ') x y :=
    fun h => parRel2_unbase f σ h
  have pb2 : ∀ {x y : Tm}, parRel2 S Θ (f.comp (σ.comp σ').hom) k'' (ISub.id k'') x y →
      parRel2 S Θ f k'' (σ.comp σ') x y := fun h => by
    have := parRel2_unbase f (σ.comp σ') h; rwa [ISub.comp_id] at this
  have d1 : argRelH Θ f S k'' (σ.comp σ').hom (ps1.isub σ') (ps1.isub σ') := by
    have := argRelH_isub Θ f ((argRel2_iff Θ _).1 (argRel2_unbase f σ a00)) σ'
    rwa [ISub.comp_id, ← ISub.hom_comp] at this
  -- typing of the parameters
  have tU : IsTyK S k' (.data Θ.idx ps1) := hUb.2.1.of_tyEq hU1.2
  have t1 : IsTyK S k'' (.data Θ.idx (ps1.isub σ')) := tU.isub hW σ'
  have tq : IsTyK S k'' (.data Θ.idx q) := (hUb.2.1.isub hW σ').of_tyEq g1.2
  have tq' : IsTyK S k'' (.data Θ.idx q') := ((hUb.2.2.1.isub hW σ').of_tyEq g2.2)
  have t2 : IsTyK S k'' (.data Θ.idx ps2) := hU2b.2.1.of_tyEq hU2'.2
  have e1q : TyEq S k'' (.data Θ.idx (ps1.isub σ')) (.data Θ.idx q) :=
    (hU1.2.isub hW σ').symm.trans hW g1.2
  have eqq' : TyEq S k'' (.data Θ.idx q) (.data Θ.idx q') :=
    (g1.2.symm.trans hW (hUb.2.2.2.2.2.isub hW σ')).trans hW g2.2
  have eq'2 : TyEq S k'' (.data Θ.idx q') (.data Θ.idx ps2) :=
    (g2'.2.symm.trans hW hU2b.2.2.2.2.2.symm).trans hW hU2'.2
  have e2q' : TyEq S k'' (.data Θ.idx ps2) (.data Θ.idx q) := (eqq'.trans hW eq'2).symm
  have r1q' := argRelH_comp hW f hP (ub0 c1) d1 (ub a11) (ub a12) t1 tq tq' hql e1q
  have r12 := argRelH_comp hW f hP r1q' d1 (ub a22) (ub2 b21) t1 tq' t2 hq'l (e1q.trans hW eqq')
  have r2q := argRelH_comp hW f hP (ub2 b12) (ub2 b11) (ub2 b22) (ub a21) t2 tq' tq hq'l eq'2.symm
  have r21 := argRelH_comp hW f hP r2q (ub2 b11) (ub a11) (ub0 c2) t2 tq t1 hql e2q'
  have hl1 := data_len_of hW t1
  have hlq := data_len_of hW tq
  have hlq' := data_len_of hW tq'
  have pr := parRel2_trans ihp f (σ.comp σ') (by rw [hlq, hl1]) (pb0 c3)
    (parRel2_trans ihp f (σ.comp σ') (by rw [hlq', hlq]) (pb1 p12) (parRel2_symm ihp f (σ.comp σ') (pb2 pb)))
  exact ⟨(argRel2_iff Θ _).2 r12, (argRel2_iff Θ _).2 r21, pr⟩

theorem he2_dataC {Θ : SData m}
    (hP : ∀ {n : ℕ} (h : Hom n m) (c j : ℕ) (pre : List V),
      PERP (Comp2 S (tyLook (shapeV (Θ.restr h)) c j pre) n n (Hom.id n)))
    (ihp : ∀ n (g : Hom n m) j t X, vnth (Θ.pt n g) j = ZFSet.pair t X → PER2 S n X) : HE2 S m (dataC Θ) := by
  intro k f T T' t t'
  constructor
  · intro hT hT' hall
    obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
    have hc0 := cohData_expand hW hP ihp hall
    have hb0 := base_expand hW hT e0 hU0
    rw [Comp2_dataC] at hU0 ⊢
    refine ⟨hb0, fun k' σ => ?_, hc0, hU0.2.2.2⟩
    obtain ⟨U, r, e, hU⟩ := hall k' σ
    rw [Comp2_dataC] at hU
    obtain ⟨⟨hUt, hVt, -⟩, hc, -⟩ := hU
    obtain ⟨ps, ps', h1, h2, hpl, hpl', a1, a2, a3, a4, a5⟩ := hc k' (ISub.id k')
    rw [isub_id_of_closed (closed_of_isTyK hW hUt)] at h1
    rw [isub_id_of_closed (closed_of_isTyK hW hVt)] at h2
    have := fun {x y : Tm} (h : argRel2 S Θ (f.comp σ.hom) k' (ISub.id k') x y) => by
      have := argRel2_unbase f σ h; rwa [ISub.comp_id] at this
    have hp5 := parRel2_unbase f σ a5
    rw [ISub.comp_id] at hp5
    exact ⟨ps, ps', RedT.of_red hW r e h1, h2, hpl, hpl', this a1, this a2, this a3, this a4, hp5⟩
  · intro hTT ht ht' hall
    obtain ⟨u0, -, e0, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
    obtain ⟨hEB, hmem⟩ := el_expand hW ht e0 hu0
    have hTall := hTT
    rw [Comp2_dataC] at hTall
    -- the argument clauses of the type at every restriction
    have hyp : ∀ k' (σ : ISub k' k) ps, RedT S k' (T.isub σ) (.data Θ.idx ps) →
        argRelH Θ f S k' σ.hom ps ps := by
      intro k' σ ps hps
      obtain ⟨ps1, -, h1, -, -, -, -, -, a3, -⟩ := hTall.2.1 k' σ
      obtain rfl := redT_data_eq (RedT.to_red hW h1.1.1 h1.2 hps)
      exact (argRel2_iff Θ σ).1 a3
    -- the reducts at every restriction
    have red : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (T.isub σ) ∧
        DR2 S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k' σ.hom (T.isub σ) u (t'.isub σ) := by
      intro k' σ
      obtain ⟨u, r, e, hu⟩ := hall k' σ
      rw [Comp2_dataC] at hu
      obtain ⟨-, -, -, hdr⟩ := hu
      have := DR2.unbase (h := σ.hom) f hdr
      rw [Hom.comp_id] at this
      exact ⟨u, r, e, this⟩
    have main : ∀ k' (σ : ISub k' k), DR2At S Θ.idx (dataD S Θ.idx) (dataMem S Θ f) (dataP2 S Θ f) k' σ.hom
        (T.isub σ) (t.isub σ) (t'.isub σ) := fun k' σ => by
      obtain ⟨u, r, e, hdr⟩ := red k' σ
      exact (DR2.at_id hW hdr).expand hW r e
    rw [Comp2_dataC]
    refine ⟨hEB, hmem, hEB, .intro hEB.2.2 (fun k' σ => by rw [Hom.id_comp]; exact main k' σ)
      (fun k' σ w hw k'' ρ => ?_) (fun k' σ w hw k'' ρ => ?_)⟩
    · obtain ⟨u, r, e, hdr⟩ := red k' σ
      have hu := (DR2.at_id hW hdr)
      cases hdr with
      | intro he hh hc _ =>
        have hut := HasTy.eqL he
        have a := hc k' (ISub.id k') w (by rw [isub_id_of_closed (closed_of_ty hW hut)]; exact red_redW r hw) k'' ρ
        have b := hh k'' ρ
        simp only [ISub.id_comp, Tm.isub_isub, ← ISub.hom_comp] at a b
        have hy := hyp k'' (σ.comp ρ)
        rw [Hom.id_comp]
        exact DR2At_trans hW f hP (DR2At_trans hW f hP a b hy) (DR2At_symm hW f hP (main k'' (σ.comp ρ)) hy) hy
    · obtain ⟨u, r, e, hdr⟩ := red k' σ
      cases hdr with
      | intro he _ _ hc' =>
        have hut := HasTy.eqR he
        have a := hc' k' (ISub.id k') w (by rw [isub_id_of_closed (closed_of_ty hW hut)]; exact hw) k'' ρ
        simp only [ISub.id_comp, Tm.isub_isub, ← ISub.hom_comp] at a
        rw [Hom.id_comp]
        exact a

end misc


/-! ### Glue types -/

section glue
variable (hW : WfSig S) {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
  (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
  (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
include hW hA hφ hTp hTkv

omit hW hA in
theorem glue_holds {g : Hom k m} (hg : (φ.restr g).holds) (σ : ISub k' k) :
    Comp2 S (glueC m A φ Tp ep) m k' (g.comp σ.hom) = Comp2 S (dat Tp k g) k k' σ.hom := by
  have hgσ : (φ.restr (g.comp σ.hom)).holds := by
    rw [← Cof.restr_restr]; exact (hφ.restr g).holds_restr hg _
  rw [Comp2_glueC_at hφ hTp hTkv, if_pos hgσ, Comp2_eq_res (IsKV.ne_empty (hTkv k g hg)), hTp k g hg]

/-- The type relation of a Glue code at a restriction is its relation at one stage. -/
theorem glueLocT_of_rel {f : Hom k m} {k' : ℕ} (σ : ISub k' k) {Y Z : Tm}
    (h : (Comp2 S (glueC m A φ Tp ep) m k' (f.comp σ.hom)).ty Y Z) : glueLocT S A Tp φ f k' σ Y Z := by
  by_cases hh : (φ.restr (f.comp σ.hom)).holds
  · rw [Comp2_glueC_at hφ hTp hTkv, if_pos hh] at h
    unfold glueLocT; rw [if_pos hh]; exact h
  · rw [Comp2_glueC_f hA hφ hTp hTkv _ hh] at h
    obtain ⟨⟨hY, hZ, -⟩, hall, -⟩ := h
    have := hall k' (ISub.id k')
    rwa [glueLocT_comp, ISub.comp_id, isub_id_of_closed (closed_of_isTyK hW hY),
      isub_id_of_closed (closed_of_isTyK hW hZ)] at this

/-- The element relation of a Glue code at a restriction is its relation at one stage. -/
theorem glueLocE_of_rel {f : Hom k m} {k' : ℕ} (σ : ISub k' k) {X y z : Tm}
    (h : (Comp2 S (glueC m A φ Tp ep) m k' (f.comp σ.hom)).el X y z) : glueLocE S A Tp φ f k' σ X y z := by
  by_cases hh : (φ.restr (f.comp σ.hom)).holds
  · rw [Comp2_glueC_at hφ hTp hTkv, if_pos hh] at h
    unfold glueLocE; rw [if_pos hh]; exact h
  · rw [Comp2_glueC_f hA hφ hTp hTkv _ hh] at h
    obtain ⟨hE, -, -, hall, -⟩ := h
    have := hall k' (ISub.id k')
    rwa [glueLocE_comp, ISub.comp_id, isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW hE.1)),
      isub_id_of_closed (closed_of_ty hW hE.1), isub_id_of_closed (closed_of_ty hW hE.2.1)] at this

/-- The coherence of a related Glue type at a restriction where the face does not hold. -/
theorem cohGT_of_rel {f : Hom k m} {k' : ℕ} (σ : ISub k' k) (hn : ¬ (φ.restr (f.comp σ.hom)).holds) {Y Z : Tm}
    (h : (Comp2 S (glueC m A φ Tp ep) m k' (f.comp σ.hom)).ty Y Z) {W : Tm} (hW' : RedW S Y W)
    {k'' : ℕ} (ρ : ISub k'' k') : glueLocT S A Tp φ f k'' (σ.comp ρ) (W.isub ρ) (Y.isub ρ) := by
  rw [Comp2_glueC_f hA hφ hTp hTkv _ hn] at h
  obtain ⟨⟨hY, -⟩, -, hc, -⟩ := h
  have := hc k' (ISub.id k') (by rwa [ISub.hom_id, Hom.comp_id])
    W (by rwa [isub_id_of_closed (closed_of_isTyK hW hY)]) k'' ρ
  rwa [glueLocT_comp, ISub.id_comp] at this

/-- The coherence of related elements of a Glue type at a restriction where the face does not hold. -/
theorem cohGE_of_rel {f : Hom k m} {k' : ℕ} (σ : ISub k' k) (hn : ¬ (φ.restr (f.comp σ.hom)).holds) {X y z : Tm}
    (h : (Comp2 S (glueC m A φ Tp ep) m k' (f.comp σ.hom)).el X y z) {w : Tm} (hw : RedW S y w)
    {k'' : ℕ} (ρ : ISub k'' k') :
    ((φ.restr (f.comp (σ.comp ρ).hom)).holds → ∀ ψ e0 t0 a0, w = .glueEl ψ e0 t0 a0 →
      (Comp2 S (dat Tp k'' (f.comp (σ.comp ρ).hom)) k'' k'' (Hom.id k'')).el (X.isub ρ) (t0.isub ρ) (y.isub ρ)) ∧
    (¬ (φ.restr (f.comp (σ.comp ρ).hom)).holds →
      glueLocE S A Tp φ f k'' (σ.comp ρ) (X.isub ρ) (w.isub ρ) (y.isub ρ)) := by
  rw [Comp2_glueC_f hA hφ hTp hTkv _ hn] at h
  obtain ⟨hE, -, -, -, hc, -⟩ := h
  have hy := closed_of_ty hW hE.1
  have := hc k' (ISub.id k') (by rwa [ISub.hom_id, Hom.comp_id]) w (by rwa [isub_id_of_closed hy]) k'' ρ
  simp only [ISub.id_comp, glueLocE_comp, ISub.comp_hom] at this ⊢
  exact this

theorem he2_glueC (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → HE2 S k (dat Tp k f))
    (perA : PER2 S m A) (krA : KR2 S m A)
    (perT : ∀ k (f : Hom k m), (φ.restr f).holds → PER2 S k (dat Tp k f))
    (krT : ∀ k (f : Hom k m), (φ.restr f).holds → KR2 S k (dat Tp k f)) (krX : KR2 S m (glueC m A φ Tp ep)) :
    HE2 S m (glueC m A φ Tp ep) := by
  intro k f T T' t t'
  by_cases hf : (φ.restr f).holds
  · have e0 := glue_holds (S := S) (ep := ep) (A := A) hφ hTp hTkv hf (ISub.id k)
    rw [ISub.hom_id, Hom.comp_id] at e0
    have eσ := fun k' (σ : ISub k' k) => glue_holds (S := S) (ep := ep) (A := A) hφ hTp hTkv hf σ
    have ih := ihT k f hf k (Hom.id k) T T' t t'
    simp only [Hom.id_comp] at ih
    simp only [e0, eσ]
    exact ih
  -- the relation of `T`'s code at a restriction where the face holds, from those at further restrictions
  have hT_at : ∀ {k' : ℕ} (σ : ISub k' k), (φ.restr (f.comp σ.hom)).holds → ∀ k'' (σ' : ISub k'' k'),
      Comp2 S (glueC m A φ Tp ep) m k'' (f.comp (σ.comp σ').hom) =
        Comp2 S (dat Tp k' (f.comp σ.hom)) k' k'' ((Hom.id k').comp σ'.hom) := by
    intro k' σ hh k'' σ'
    rw [Hom.id_comp, ← ISub.comp_hom, glue_holds hφ hTp hTkv hh]
  have rel_σ : ∀ {k' : ℕ} (σ : ISub k' k) {k'' : ℕ} (ρ : ISub k'' k'),
      (f.comp σ.hom).comp ρ.hom = f.comp (σ.comp ρ).hom := by
    intro k' σ k'' ρ; exact ISub.comp_hom f σ ρ
  constructor
  · intro hT hT' hall
    obtain ⟨U0, -, e0, hU0⟩ := hypT_id hW hT hT' hall
    have hb := base_expand hW hT e0 hU0
    have hc' : cohGT S A Tp φ f T' := by
      rw [Comp2_glueC_f hA hφ hTp hTkv f hf] at hU0; exact hU0.2.2.2
    have main : ∀ k' (σ : ISub k' k), glueLocT S A Tp φ f k' σ (T.isub σ) (T'.isub σ) := by
      intro k' σ
      by_cases hfσ : (φ.restr (f.comp σ.hom)).holds
      · unfold glueLocT; rw [if_pos hfσ]
        refine (ihT k' _ hfσ k' (Hom.id k') (T.isub σ) (T'.isub σ) T T).1 (hT.isub hW σ) (hT'.isub hW σ)
          fun k'' σ' => ?_
        obtain ⟨U, r, e, hU⟩ := hall k'' (σ.comp σ')
        rw [← hT_at σ hfσ, Tm.isub_isub, Tm.isub_isub]
        exact ⟨U, r, e, hU⟩
      · obtain ⟨U, r, e, hU⟩ := hall k' σ
        have := glueLocT_of_rel hW hA hφ hTp hTkv (f := f) σ hU
        unfold glueLocT at this ⊢
        rw [if_neg hfσ] at this ⊢
        obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', h1, rest⟩ := this
        exact ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', RedT.of_red hW r e h1, rest⟩
    rw [Comp2_glueC_f hA hφ hTp hTkv f hf]
    refine ⟨hb, main, fun k' σ hn W hW' k'' ρ => ?_, hc'⟩
    obtain ⟨U, r, e, hU⟩ := hall k' σ
    have hUt := (Comp2_ty_base hU).2.1
    have a := cohGT_of_rel hW hA hφ hTp hTkv σ hn hU (red_redW r hW') ρ
    have b := (krX k' (f.comp σ.hom) k'' ρ U (T'.isub σ) U U).1 hU
    rw [rel_σ, Tm.isub_isub] at b
    have b' := glueLocT_of_rel hW hA hφ hTp hTkv (σ.comp ρ) b
    have c := main k'' (σ.comp ρ)
    -- the normal form of `T σ` (a Glue type, related to itself) is typed
    have hWt : IsTyK S k' W := by
      have hm := main k' σ
      unfold glueLocT at hm; rw [if_neg hn] at hm
      obtain ⟨A1, φ1, T1, e1, -, -, -, -, h1, -⟩ := hm
      obtain rfl := RedW.unique hW' h1.1
      exact (hT.isub hW σ).of_tyEq h1.2
    have hτ := hT.isub hW (σ.comp ρ)
    have hτ' := hT'.isub hW (σ.comp ρ)
    refine glueLocT_trans hW perA krA perT krT f (σ.comp ρ) (hWt.isub hW ρ) (hUt.isub hW ρ) a
      (glueLocT_trans hW perA krA perT krT f (σ.comp ρ) (hUt.isub hW ρ) hτ' b'
        (glueLocT_symm hW perA krA perT krT f (σ.comp ρ) hτ hτ' c))
  · intro hTT ht ht' hall
    obtain ⟨u0, -, e0, hu0⟩ := hypE_id hW (Comp2_ty_base hTT).2.1 ht ht' hall
    obtain ⟨hEB, hmem⟩ := el_expand hW ht e0 hu0
    have hc' : cohGE S A Tp φ f T t' := by
      rw [Comp2_glueC_f hA hφ hTp hTkv f hf] at hu0; exact hu0.2.2.2.2.2
    have hTT' := hTT
    rw [Comp2_glueC_f hA hφ hTp hTkv f hf] at hTT'
    have main : ∀ k' (σ : ISub k' k), glueLocE S A Tp φ f k' σ (T.isub σ) (t.isub σ) (t'.isub σ) := by
      intro k' σ
      have hTσ := hTT'.2.1 k' σ
      by_cases hfσ : (φ.restr (f.comp σ.hom)).holds
      · unfold glueLocT at hTσ; rw [if_pos hfσ] at hTσ
        unfold glueLocE; rw [if_pos hfσ]
        refine (ihT k' _ hfσ k' (Hom.id k') (T.isub σ) (T.isub σ) (t.isub σ) (t'.isub σ)).2 hTσ
          (HasTy.isubS hW ht σ) (HasTy.isubS hW ht' σ) fun k'' σ' => ?_
        obtain ⟨u, r, e, hu⟩ := hall k'' (σ.comp σ')
        rw [← hT_at σ hfσ, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
        exact ⟨u, r, e, hu⟩
      · obtain ⟨u, r, e, hu⟩ := hall k' σ
        have := glueLocE_of_rel hW hA hφ hTp hTkv (f := f) σ hu
        unfold glueLocE at this ⊢
        rw [if_neg hfσ] at this ⊢
        obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', h1, h2, rest⟩ := this
        exact ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', h1, RedE.of_red r e h2, rest⟩
    rw [Comp2_glueC_f hA hφ hTp hTkv f hf]
    refine ⟨hEB, hmem, hEB, main, fun k' σ hn w hw k'' ρ => ?_, hc'⟩
    obtain ⟨u, r, e, hu⟩ := hall k' σ
    have a := cohGE_of_rel hW hA hφ hTp hTkv σ hn hu (red_redW r hw) ρ
    have b := (krX k' (f.comp σ.hom) k'' ρ (T.isub σ) (T.isub σ) u (t'.isub σ)).2 hu
    rw [rel_σ, Tm.isub_isub, Tm.isub_isub] at b
    rw [Tm.isub_isub] at a
    have c := main k'' (σ.comp ρ)
    have hTτ := hTT'.2.1 k'' (σ.comp ρ)
    refine ⟨fun hh ψ e0 t0 a0 hwe => ?_, fun hh => ?_⟩
    · -- where the face holds: the fiber of the normal form, through `T`'s relation
      have a1 := a.1 hh ψ e0 t0 a0 hwe
      rw [Comp2_glueC_at hφ hTp hTkv, if_pos hh] at b
      unfold glueLocE at c; rw [if_pos hh] at c
      unfold glueLocT at hTτ; rw [if_pos hh] at hTτ
      have P := perT k'' _ hh k'' (Hom.id k'')
      exact P.transEl hTτ a1 (P.transEl hTτ b (P.symEl hTτ c))
    · have b' := glueLocE_of_rel hW hA hφ hTp hTkv (σ.comp ρ) b
      exact glueLocE_trans hW perA krA perT krT f (σ.comp ρ) hTτ (a.2 hh)
        (glueLocE_trans hW perA krA perT krT f (σ.comp ρ) hTτ b'
          (glueLocE_symm hW perA krA perT krT f (σ.comp ρ) hTτ c))

end glue



end

end Model.Whnf
