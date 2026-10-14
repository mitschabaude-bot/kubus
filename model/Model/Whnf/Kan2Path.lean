import Model.Whnf.Kan2IPi
import Model.Canon.KanPath

/-!
# The binary Kan operations at path types
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The structure of a pair of related types whose normal forms are path types. -/
structure PathStr (S : Sig) (k : ℕ) (T T' : Tm) : Prop where
  tyEq : TyEq S k T T'
  whnf : ∀ k' (ρ : ISub k' k), ∃ L1 b0 b1 L1' b0' b1', RedT S k' (T.isub ρ) (.path L1 b0 b1) ∧
    RedT S k' (T'.isub ρ) (.path L1' b0' b1') ∧
    (∀ (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' → RT2 S k' (L1.dinst r) (L1'.dinst r')) ∧
    RE2 S k' (L1.dinst .zero) b0 b0' ∧ RE2 S k' (L1.dinst .one) b1 b1'
  coh : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') L1 b0 b1 L2 c0 c1, RedT S k' (T.isub ρ) (.path L1 b0 b1) →
    RedT S k'' (T.isub (ρ.comp ρ')) (.path L2 c0 c1) → ∀ (s : I), s.Scoped k'' →
    RT2 S k'' ((L1.isub ρ'.up).dinst s) (L2.dinst s)
  tc : ∀ k' (ρ : ISub k' k) L1 b0 b1, RedT S k' (T.isub ρ) (.path L1 b0 b1) → ∀ (s : I), s.Scoped k' →
    TyCode k' (semK S k' (L1.dinst s))
  elim : ∀ k' (ρ : ISub k' k) L1 b0 b1 f f', RedT S k' (T.isub ρ) (.path L1 b0 b1) → RE2 S k' (T.isub ρ) f f' →
    (∀ (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' → RE2 S k' (L1.dinst r) (.papp f r) (.papp f' r')) ∧
    RE2 S k' (L1.dinst .zero) (.papp f .zero) b0 ∧ RE2 S k' (L1.dinst .one) (.papp f .one) b1
  coh' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') L1 b0 b1 L2 c0 c1, RedT S k' (T'.isub ρ) (.path L1 b0 b1) →
    RedT S k'' (T'.isub (ρ.comp ρ')) (.path L2 c0 c1) → ∀ (s : I), s.Scoped k'' →
    RT2 S k'' ((L1.isub ρ'.up).dinst s) (L2.dinst s)
  elim' : ∀ k' (ρ : ISub k' k) L1 b0 b1 f f', RedT S k' (T'.isub ρ) (.path L1 b0 b1) → RE2 S k' (T'.isub ρ) f f' →
    (∀ (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' → RE2 S k' (L1.dinst r) (.papp f r) (.papp f' r')) ∧
    RE2 S k' (L1.dinst .zero) (.papp f .zero) b0 ∧ RE2 S k' (L1.dinst .one) (.papp f .one) b1

variable (hW : WfSig S)
include hW

theorem PathStr_of {T T' L a b : Tm} {l : ℕ} (h : RT2 S k T T') (hR : RedT S k T (.path L a b))
    (hpath : HasTy S k .one [] (.path L a b) (.univ l)) : PathStr S k T T' := by
  have hL0 := HasTy.pathLine hpath
  have hLne := semK_ne hW hL0
  have hLc := tyCode_of_univ hW hL0
  have hX : semK S k T = pathC k (semK S (k + 1) L) (semK S k a) (semK S k b) :=
    (semK_tyEq hW hR.2).trans (semK_pathT hW hpath)
  have hT := h
  unfold RT2 at hT
  rw [hX, Comp2_pathC _ _ _ hLne] at hT
  obtain ⟨hbase, hall, hcoh, hcoh'⟩ := hT
  have hXne : pathC k (semK S (k + 1) L) (semK S k a) (semK S k b) ≠ ∅ := mkKV_ne_empty _
  -- the elimination of related elements of a type with the code of `T`
  have elimGen : ∀ k' (ρ : ISub k' k) (U : Tm), semK S k' U = res ρ.hom (semK S k T) →
      ∀ L1 b0 b1 f f', RedT S k' U (.path L1 b0 b1) →
      (∀ (s : I) (hs : s.Scoped k'), semK S k' (L1.dinst s) =
        res ((Hom.lift (Hom.id k)).comp (ISub.cons s hs ρ).hom) (semK S (k + 1) L)) → RE2 S k' U f f' →
      (∀ (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' → RE2 S k' (L1.dinst r) (.papp f r) (.papp f' r')) ∧
      RE2 S k' (L1.dinst .zero) (.papp f .zero) b0 ∧ RE2 S k' (L1.dinst .one) (.papp f .one) b1 := by
    intro k' ρ U hU L1 b0 b1 f f' h1 hsem hf
    have hf2 : (Comp2 S (pathC k (semK S (k + 1) L) (semK S k a) (semK S k b)) k k' ρ.hom).el U f f' := by
      rw [Comp2_eq_res hXne, ← hX, ← hU]; exact hf
    obtain ⟨L3, c0, c1, h3, happ, h0, h1'⟩ := pathC_el_at hLne hW hf2
    obtain ⟨rfl, rfl, rfl⟩ : L3 = L1 ∧ c0 = b0 ∧ c1 = b1 := by
      have := RedW.unique h3.1 h1.1; injection this; exact ⟨by assumption, by assumption, by assumption⟩
    have e : ∀ (r : I) (hr : r.Scoped k'), (Hom.lift ρ.hom).comp (ISub.cons r hr (ISub.id k')).hom =
        (Hom.lift (Hom.id k)).comp (ISub.cons r hr ρ).hom := by
      intro r hr
      have := lift_cons (Hom.id k) ρ r hr (ISub.id k')
      simpa only [Hom.id_comp, ISub.comp_id] using this
    have conv : ∀ (r : I) (hr : r.Scoped k') {x y : Tm},
        (Comp2 S (semK S (k + 1) L) (k + 1) k' ((Hom.lift ρ.hom).comp (ISub.cons r hr (ISub.id k')).hom)).el
          (L3.dinst r) x y → RE2 S k' (L3.dinst r) x y := by
      intro r hr x y hxy
      rw [e r hr] at hxy
      exact (Comp2_el_iff hLne (hsem r hr)).1 hxy
    exact ⟨fun r r' hr hr' hE => conv r hr (happ r r' hr hr' hE), conv .zero trivial h0, conv .one trivial h1'⟩
  refine ⟨hbase.2.2.2.2, fun k' ρ => ?_, fun k1 ρ k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2 s hs => ?_,
    fun k' ρ L1 b0 b1 h1 s hs => ?_, fun k' ρ L1 b0 b1 f f' h1 hf => ?_,
    fun k1 ρ k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2 s hs => ?_, fun k' ρ L1 b0 b1 f f' h1 hf => ?_⟩
  · obtain ⟨L1, b0, b1, L1', b0', b1', h1, h2, -, h4, h5, h6⟩ := hall k' ρ
    refine ⟨L1, b0, b1, L1', b0', b1', h1, h2, fun r r' hr hr' hE => Comp2_ty_RT2 (h4 r r' hr hr' hE), ?_, ?_⟩
    · exact (Comp2_el_iff hLne (Comp2_ty_base (h4 .zero .zero trivial trivial (I_eq_refl _))).2.2.2.1).1 h5
    · exact (Comp2_el_iff hLne (Comp2_ty_base (h4 .one .one trivial trivial (I_eq_refl _))).2.2.2.1).1 h6
  · have c := hcoh k1 ρ k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2
    exact RT2.dinst hW (Comp2_ty_tyCode c hLc) (Comp2_ty_RT2 c) s hs
  · obtain ⟨L4, b4, b5, L4x, b4x, b5x, h4, -, -, hd, -, -⟩ := hall k' ρ
    obtain rfl : L4 = L1 := by have := RedW.unique h4.1 h1.1; injection this
    exact Comp2_ty_tyCode (hd s s hs hs (I_eq_refl s)) hLc
  · refine elimGen k' ρ _ (semK_isubTy hW hbase.1 ρ) L1 b0 b1 f f' h1 (fun s hs => ?_) hf
    obtain ⟨L4, b4, b5, L4x, b4x, b5x, h4, -, -, hd, -, -⟩ := hall k' ρ
    obtain rfl : L4 = L1 := by have := RedW.unique h4.1 h1.1; injection this
    exact (Comp2_ty_base (hd s s hs hs (I_eq_refl s))).2.2.2.1
  · have c := hcoh' k1 ρ k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2
    exact RT2.dinst hW (Comp2_ty_tyCode c hLc) (Comp2_ty_RT2 c) s hs
  · refine elimGen k' ρ _ ((semK_isubTy hW hbase.2.1 ρ).trans (by rw [RT2.semK_eq hW h])) L1 b0 b1 f f' h1
      (fun s hs => ?_) hf
    obtain ⟨L4, b4, b5, L4x, b4x, b5x, -, h4, -, hd, -, -⟩ := hall k' ρ
    obtain rfl : L4x = L1 := by have := RedW.unique h4.1 h1.1; injection this
    exact (Comp2_ty_base (hd s s hs hs (I_eq_refl s))).2.2.2.2.1

theorem PathStr.isub {T T' : Tm} (hP : PathStr S k T T') (σ : ISub k' k) : PathStr S k' (T.isub σ) (T'.isub σ) where
  tyEq := hP.tyEq.isub hW σ
  whnf k'' ρ := by simpa only [Tm.isub_isub] using hP.whnf k'' (σ.comp ρ)
  coh k1 ρ k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh k1 (σ.comp ρ) k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2
  tc k1 ρ L1 b0 b1 h1 := by
    rw [Tm.isub_isub] at h1
    exact hP.tc k1 (σ.comp ρ) L1 b0 b1 h1
  elim k1 ρ L1 b0 b1 f f' h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    exact hP.elim k1 (σ.comp ρ) L1 b0 b1 f f' h1 h2
  coh' k1 ρ k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh' k1 (σ.comp ρ) k2 ρ' L1 b0 b1 L2 c0 c1 h1 h2
  elim' k1 ρ L1 b0 b1 f f' h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    exact hP.elim' k1 (σ.comp ρ) L1 b0 b1 f f' h1 h2

/-- Related elements of a type whose normal form is a path type, through their points and endpoints. -/
theorem RE2_pathW_intro {T L a b t t' : Tm} {l : ℕ} (hTT : RT2 S k T T) (hR : RedT S k T (.path L a b))
    (hpath : HasTy S k .one [] (.path L a b) (.univ l)) (hE : EB S k T t t')
    (happ : ∀ k' (ρ : ISub k' k) L1 b0 b1, RedT S k' (T.isub ρ) (.path L1 b0 b1) →
      (∀ (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
        RE2 S k' (L1.dinst r) (.papp (t.isub ρ) r) (.papp (t'.isub ρ) r')) ∧
      RE2 S k' (L1.dinst .zero) (.papp (t.isub ρ) .zero) b0 ∧ RE2 S k' (L1.dinst .one) (.papp (t.isub ρ) .one) b1) :
    RE2 S k T t t' := by
  have hL0 := HasTy.pathLine hpath
  have hLne := semK_ne hW hL0
  have hX : semK S k T = pathC k (semK S (k + 1) L) (semK S k a) (semK S k b) :=
    (semK_tyEq hW hR.2).trans (semK_pathT hW hpath)
  have hT := hTT
  unfold RT2 at hT
  rw [hX, Comp2_pathC _ _ _ hLne] at hT
  obtain ⟨-, hall, -, -⟩ := hT
  unfold RE2
  rw [hX, Comp2_pathC _ _ _ hLne]
  refine ⟨hE, ?_, hE, fun k' ρ => ?_⟩
  · rw [← hX, res_id (by rw [hX]; exact isKV_mkKV _)]; exact mem_of_ty hW hE.1
  obtain ⟨L1, b0, b1, L1x, b0x, b1x, h1, -, -, hd, -, -⟩ := hall k' ρ
  obtain ⟨hp, h0, h1'⟩ := happ k' ρ L1 b0 b1 h1
  refine ⟨L1, b0, b1, h1, fun r r' hr hr' hEq => ?_, ?_, ?_⟩ <;> rw [ISub.id_comp]
  · exact (Comp2_el_iff hLne (Comp2_ty_base (hd r r hr hr (I_eq_refl r))).2.2.2.1).2 (hp r r' hr hr' hEq)
  · exact (Comp2_el_iff hLne (Comp2_ty_base (hd .zero .zero trivial trivial (I_eq_refl _))).2.2.2.1).2 h0
  · exact (Comp2_el_iff hLne (Comp2_ty_base (hd .one .one trivial trivial (I_eq_refl _))).2.2.2.1).2 h1'


/-! ### Systems of the form `[φ ↦ p, ¬x ↦ a, x ↦ b]` -/

omit hW in
theorem ent_neg_absurd {x : I} (hx : x.Scoped k) (h1 : I.Entails .one x) (h2 : I.Entails .one (.neg x)) : False := by
  have a := ieq_one_of_holds hx (entails_holds h1 (ρ := idEnv k) (by rw [ival_one]; rfl))
  have b := ieq_zero_of_holds_neg hx (entails_holds h2 (ρ := idEnv k) (by rw [ival_one]; rfl))
  have := I_eq_trans (I_eq_symm a) b (fun _ => .zero)
  simp [I.eval] at this

omit hW in
theorem ieq_neg {x x' : I} (h : I.Eq x x') : I.Eq (.neg x) (.neg x') := fun ρ => by
  simp only [I.eval]; rw [h ρ]

omit hW in
theorem ent_one_ieq {x x' : I} (e : I.Eq x x') (h : I.Entails .one x) : I.Entails .one x' := ent_trans h (eq_ent e)

/-- A term related to a system `[φ ↦ p, ¬x ↦ a, x ↦ b]` on its faces. -/
theorem RE2_sys_r {A q p a b : Tm} {φ x : I} (hφ : φ.Scoped k) (hx : x.Scoped k)
    (hor : I.Entails .one (.or φ (.or (.neg x) x))) (hAA : RT2 S k A A)
    (hsp : HasTy S k .one [] (.split φ p (.or (.neg x) x) (.split (.neg x) a x b)) A) (hq : HasTy S k .one [] q A)
    (hp : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → RE2 S k' (A.isub σ) (q.isub σ) (p.isub σ))
    (ha : ∀ k' (σ : ISub k' k), I.Entails .one ((I.neg x).subst σ.τ) → RE2 S k' (A.isub σ) (q.isub σ) (a.isub σ))
    (hb : ∀ k' (σ : ISub k' k), I.Entails .one (x.subst σ.τ) → RE2 S k' (A.isub σ) (q.isub σ) (b.isub σ)) :
    RE2 S k A q (.split φ p (.or (.neg x) x) (.split (.neg x) a x b)) := by
  have hX := tyCode_of_ty hW hq
  refine RE2_split_r hW hφ ⟨hx, hx⟩ hor hAA hsp hq hp fun k' σ hσ => ?_
  have hxσ : (x.subst σ.τ).Scoped k' := I.scoped_subst hx σ.sc
  have hin : HasTy S k' .one [] (.split ((I.neg x).subst σ.τ) (a.isub σ) (x.subst σ.τ) (b.isub σ)) (A.isub σ) :=
    HasTy.eqR (EqTm.splitR hσ (HasTy.isubS hW hsp σ))
  refine RE2_split_r hW hxσ hxσ hσ (RT2.isub hW hX hAA σ) hin (HasTy.isubS hW hq σ)
    (fun k2 σ2 h => ?_) (fun k2 σ2 h => ?_)
  · have e := ha k2 (σ.comp σ2) (ent_comp_inv (φ := .neg x) h)
    rw [← Tm.isub_isub A, ← Tm.isub_isub q, ← Tm.isub_isub a] at e; exact e
  · have e := hb k2 (σ.comp σ2) (ent_comp_inv h)
    rw [← Tm.isub_isub A, ← Tm.isub_isub q, ← Tm.isub_isub b] at e; exact e

/-- Two systems `[φ ↦ p, ¬x ↦ a, x ↦ b]`, related on the intersections of their faces. -/
theorem RE2_pathSys {A p p' a a' b b' : Tm} {φ φ' x x' : I} (hφ : φ.Scoped k) (hφ' : φ'.Scoped k)
    (hx : x.Scoped k) (hx' : x'.Scoped k) (hxx : I.Eq x x') (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (hor : I.Entails .one (.or φ (.or (.neg x) x))) (hAA : RT2 S k A A)
    (hsp : HasTy S k .one [] (.split φ p (.or (.neg x) x) (.split (.neg x) a x b)) A)
    (hsp' : HasTy S k .one [] (.split φ' p' (.or (.neg x') x') (.split (.neg x') a' x' b')) A)
    (hpp : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → RE2 S k' (A.isub σ) (p.isub σ) (p'.isub σ))
    (hpa : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → I.Entails .one ((I.neg x).subst σ.τ) →
      RE2 S k' (A.isub σ) (p.isub σ) (a'.isub σ))
    (hap : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → I.Entails .one ((I.neg x).subst σ.τ) →
      RE2 S k' (A.isub σ) (a.isub σ) (p'.isub σ))
    (hpb : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → I.Entails .one (x.subst σ.τ) →
      RE2 S k' (A.isub σ) (p.isub σ) (b'.isub σ))
    (hbp : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → I.Entails .one (x.subst σ.τ) →
      RE2 S k' (A.isub σ) (b.isub σ) (p'.isub σ))
    (haa : ∀ k' (σ : ISub k' k), I.Entails .one ((I.neg x).subst σ.τ) → RE2 S k' (A.isub σ) (a.isub σ) (a'.isub σ))
    (hbb : ∀ k' (σ : ISub k' k), I.Entails .one (x.subst σ.τ) → RE2 S k' (A.isub σ) (b.isub σ) (b'.isub σ)) :
    RE2 S k A (.split φ p (.or (.neg x) x) (.split (.neg x) a x b))
      (.split φ' p' (.or (.neg x') x') (.split (.neg x') a' x' b')) := by
  have hX := tyCode_of_ty hW hsp
  have hor' : I.Entails .one (.or φ' (.or (.neg x') x')) :=
    ent_trans hor (ent_or_elim (ent_trans h12 (ent_or_left _ _))
      (ent_trans (ent_or_elim (ent_trans (eq_ent (ieq_neg hxx)) (ent_or_left _ _))
        (ent_trans (eq_ent hxx) (ent_or_right _ _))) (ent_or_right _ _)))
  have hxσ : ∀ k' (σ : ISub k' k), I.Entails .one ((I.neg x').subst σ.τ) → I.Entails .one ((I.neg x).subst σ.τ) :=
    fun k' σ h => ent_one_ieq (I_eq_subst (ieq_neg (I_eq_symm hxx)) σ.τ) h
  have hxσ' : ∀ k' (σ : ISub k' k), I.Entails .one (x'.subst σ.τ) → I.Entails .one (x.subst σ.τ) :=
    fun k' σ h => ent_one_ieq (I_eq_subst (I_eq_symm hxx) σ.τ) h
  -- restricting the hypotheses
  have R : ∀ {k1 k2 : ℕ} (σ : ISub k1 k) (σ2 : ISub k2 k1) {X t t' : Tm},
      RE2 S k2 (X.isub (σ.comp σ2)) (t.isub (σ.comp σ2)) (t'.isub (σ.comp σ2)) →
      RE2 S k2 ((X.isub σ).isub σ2) ((t.isub σ).isub σ2) ((t'.isub σ).isub σ2) := by
    intro k1 k2 σ σ2 X t t' h; rwa [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
  refine RE2_split_l hW hφ ⟨hx, hx⟩ hor hAA hsp hsp' (fun k1 σ hσ => ?_) (fun k1 σ hσ => ?_)
  · -- the first branch
    refine RE2_sys_r hW (I.scoped_subst hφ' σ.sc) (I.scoped_subst hx' σ.sc) (ent_one_subst hor' σ.τ)
      (RT2.isub hW hX hAA σ) (HasTy.isubS hW hsp' σ) (RE2.typed (hpp k1 σ hσ)).1
      (fun k2 σ2 h => R σ σ2 ?_) (fun k2 σ2 h => R σ σ2 ?_) (fun k2 σ2 h => R σ σ2 ?_)
    · exact hpp k2 (σ.comp σ2) (ent_trans (ent_comp_inv h) (ent_subst h21 _))
    · exact hpa k2 (σ.comp σ2) (ent_comp hσ) (hxσ _ _ (ent_comp_inv (φ := .neg x') h))
    · exact hpb k2 (σ.comp σ2) (ent_comp hσ) (hxσ' _ _ (ent_comp_inv h))
  · -- the second branch
    have hsc : (x.subst σ.τ).Scoped k1 := I.scoped_subst hx σ.sc
    have hin : HasTy S k1 .one [] (.split ((I.neg x).subst σ.τ) (a.isub σ) (x.subst σ.τ) (b.isub σ)) (A.isub σ) :=
      HasTy.eqR (EqTm.splitR hσ (HasTy.isubS hW hsp σ))
    -- the right system, at a restriction, against a term
    have hright : ∀ {k2 : ℕ} (τ : ISub k2 k) (q : Tm), HasTy S k2 .one [] q (A.isub τ) →
        (∀ k3 (σ3 : ISub k3 k2), I.Entails .one (φ'.subst (τ.comp σ3).τ) →
          RE2 S k3 (A.isub (τ.comp σ3)) (q.isub σ3) (p'.isub (τ.comp σ3))) →
        (∀ k3 (σ3 : ISub k3 k2), I.Entails .one ((I.neg x').subst (τ.comp σ3).τ) →
          RE2 S k3 (A.isub (τ.comp σ3)) (q.isub σ3) (a'.isub (τ.comp σ3))) →
        (∀ k3 (σ3 : ISub k3 k2), I.Entails .one (x'.subst (τ.comp σ3).τ) →
          RE2 S k3 (A.isub (τ.comp σ3)) (q.isub σ3) (b'.isub (τ.comp σ3))) →
        RE2 S k2 (A.isub τ) q (.split (φ'.subst τ.τ) (p'.isub τ) (.or (.neg (x'.subst τ.τ)) (x'.subst τ.τ))
          (.split (.neg (x'.subst τ.τ)) (a'.isub τ) (x'.subst τ.τ) (b'.isub τ))) := by
      intro k2 τ q hq h1 h2 h3
      refine RE2_sys_r hW (I.scoped_subst hφ' τ.sc) (I.scoped_subst hx' τ.sc) (ent_one_subst hor' τ.τ)
        (RT2.isub hW hX hAA τ) (HasTy.isubS hW hsp' τ) hq (fun k3 σ3 h => ?_) (fun k3 σ3 h => ?_)
        (fun k3 σ3 h => ?_) <;> rw [Tm.isub_isub, Tm.isub_isub]
      · exact h1 k3 σ3 (ent_comp_inv h)
      · exact h2 k3 σ3 (ent_comp_inv (φ := .neg x') h)
      · exact h3 k3 σ3 (ent_comp_inv h)
    refine RE2_split_l hW hsc hsc hσ (RT2.isub hW hX hAA σ) hin (HasTy.isubS hW hsp' σ)
      (fun k2 σ2 h0 => ?_) (fun k2 σ2 h0 => ?_)
    · have h0' := ent_comp_inv (φ := .neg x) h0
      rw [Tm.isub_isub, Tm.isub_isub, show (Tm.subst Tm.var σ.τ a).isub σ2 = a.isub (σ.comp σ2) from Tm.isub_isub a σ σ2]
      refine hright (σ.comp σ2) _ (RE2.typed (haa k2 _ h0')).1 (fun k3 σ3 h => ?_) (fun k3 σ3 h => ?_)
        (fun k3 σ3 h => ?_) <;> rw [Tm.isub_isub]
      · exact hap k3 _ (ent_trans h (ent_subst h21 _)) (ent_comp h0')
      · exact haa k3 _ (hxσ _ _ h)
      · exact (ent_neg_absurd (I.scoped_subst hx (((σ.comp σ2).comp σ3).sc)) (hxσ' _ _ h) (ent_comp h0')).elim
    · have h0' := ent_comp_inv h0
      rw [Tm.isub_isub, Tm.isub_isub, show (Tm.subst Tm.var σ.τ b).isub σ2 = b.isub (σ.comp σ2) from Tm.isub_isub b σ σ2]
      refine hright (σ.comp σ2) _ (RE2.typed (hbb k2 _ h0')).1 (fun k3 σ3 h => ?_) (fun k3 σ3 h => ?_)
        (fun k3 σ3 h => ?_) <;> rw [Tm.isub_isub]
      · exact hbp k3 _ (ent_trans h (ent_subst h21 _)) (ent_comp h0')
      · exact (ent_neg_absurd (I.scoped_subst hx (((σ.comp σ2).comp σ3).sc)) (ent_comp h0') (hxσ _ _ h)).elim
      · exact hbb k3 _ (hxσ' _ _ h)


/-! ### Composition at path types -/

/-- The tube `[φ ↦ u r, ¬r ↦ c0, r ↦ c1]` of a point of `hcompPath`, at stage `k + 1`. -/
def sysP (φ r : I) (u c0 c1 : Tm) : Tm :=
  .split φ.shift (.papp u r.shift) (.or (.neg r.shift) r.shift) (.split (.neg r.shift) c0.dshift r.shift c1.dshift)

omit hW in
theorem sysP_isub_dinst (φ r : I) (u c0 c1 : Tm) (θ : ISub k' k) (x : I) :
    ((sysP φ r u c0 c1).isub θ.up).dinst x = .split (φ.subst θ.τ) (.papp ((u.isub θ.up).dinst x) (r.subst θ.τ))
      (.or (.neg (r.subst θ.τ)) (r.subst θ.τ)) (.split (.neg (r.subst θ.τ)) (c0.isub θ) (r.subst θ.τ) (c1.isub θ)) := by
  have e : ∀ y : I, (y.shift.subst θ.up.τ).subst (I.inst0 x) = y.subst θ.τ := fun y => shift_up_inst0 y θ.τ x
  show Tm.split ((φ.shift.subst θ.up.τ).subst (I.inst0 x)) (.papp ((u.isub θ.up).dinst x)
      ((r.shift.subst θ.up.τ).subst (I.inst0 x)))
    (.or (.neg ((r.shift.subst θ.up.τ).subst (I.inst0 x))) ((r.shift.subst θ.up.τ).subst (I.inst0 x)))
    (.split (.neg ((r.shift.subst θ.up.τ).subst (I.inst0 x))) ((c0.dshift.isub θ.up).dinst x)
      ((r.shift.subst θ.up.τ).subst (I.inst0 x)) ((c1.dshift.isub θ.up).dinst x)) = _
  rw [e, e, dshift_isub_up_dinst, dshift_isub_up_dinst]

omit hW in
theorem hcompPath_body' (A a b u p0 : Tm) (φ r : I) : ∃ t, Tm.hcompPath A a b φ u p0 = .plam t ∧
    t.dinst r = .hcomp (A.dinst r) (.or φ (.or (.neg r) r)) (sysP φ r u a b) (.papp p0 r) :=
  hcompPath_body A a b u p0 φ r

omit hW in
theorem step_hcomp_path {L a b u p : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.hcomp (.path L a b) φ u p) = some (Tm.hcompPath L a b φ u p) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

/-- A point of a composition in a path type whose face does not hold. -/
theorem papp_hcomp_path {T L1 b0 b1 u a0 : Tm} {φ r : I} (hn : ¬ I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : RedT S k T (.path L1 b0 b1)) :
    Red S (.papp (.hcomp T φ u a0) r) (.hcomp (L1.dinst r) (.or φ (.or (.neg r) r)) (sysP φ r u b0 b1) (.papp a0 r)) ∧
    EqTm S k .one [] (.papp (.hcomp T φ u a0) r)
      (.hcomp (L1.dinst r) (.or φ (.or (.neg r) r)) (sysP φ r u b0 b1) (.papp a0 r)) (L1.dinst r) := by
  obtain ⟨t, ht, htr⟩ := hcompPath_body' L1 b0 b1 u a0 φ r
  have e1 := eq_hcomp_ty hW hty hR.2
  have e2 := EqTm.hcompPath (HasTy.eqR e1)
  have e3 := (e1.trans e2).tyConv hR.2
  have e4 := EqTm.papp e3 hr hr (I_eq_refl r)
  rw [ht] at e4
  have e5 := EqTm.pathBeta (HasTy.eqR e4)
  rw [htr] at e5
  refine ⟨(red_papp r ((red_hcomp_ty hn hR.1.1).trans (.step (step_hcomp_path hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rw [ht]; show some (t.dinst r) = _; rw [htr]

/-- A point of a composition in a path type whose face holds. -/
theorem papp_hcomp_face_path {T L1 b0 b1 u a0 : Tm} {φ r : I} (h : I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : TyEq S k T (.path L1 b0 b1)) :
    Red S (.papp (.hcomp T φ u a0) r) (.papp (u.dinst .one) r) ∧
    EqTm S k .one [] (.papp (.hcomp T φ u a0) r) (.papp (u.dinst .one) r) (L1.dinst r) :=
  ⟨red_papp r (.step (step_hcomp_face h) (.refl _)),
    EqTm.papp ((EqTm.hcompFace h hty).tyConv hR) hr hr (I_eq_refl r)⟩

/-- The tube of a composition is typed at points where its face holds. -/
theorem hcomp_tube_typed {X T u a : Tm} {φ : I} (hty : HasTy S k .one [] (.hcomp T φ u a) X) (x : I)
    (hx : x.Scoped k) (hh : (ival (idEnv k) φ).holds) : HasTy S k .one [] (u.dinst x) T := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨lq, ⟨hq, hψ, htube, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
  have hT := HasTy0.isub hS (Ψ' := k) (Φ' := .one) (τ := (ISub.cons x hx (ISub.id k)).τ) htube
    (fun i hi => (ISub.cons x hx (ISub.id k)).sc i hi)
    (ent_cof_cons hW hψ x hx (ISub.id k) (by rwa [I_subst_id hψ]))
    (Wf0.nil trivial)
  have hT' := minimal_to_spec hT
  rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons, isub_id_of_closed (closed_ty hq),
    isub_cons_id_of_closed (closed_ty htube)] at hT'
  exact hT'


omit hW in
theorem papp_dinst_isub (u : Tm) (w : ISub k' k) (x s : I) (σ : ISub k'' k') :
    (Tm.papp ((u.isub w.up).dinst x) s).isub σ = .papp ((u.isub (w.comp σ).up).dinst (x.subst σ.τ)) (s.subst σ.τ) := by
  show Tm.papp (((u.isub w.up).dinst x).isub σ) (s.subst σ.τ) = _
  rw [isub_dinst, Tm.isub_isub, ← ISub.up_comp]

omit hW in
theorem not_ent_zero : ¬ I.Entails .one .zero := by decide

omit hW in
theorem ent_or3 {φ φ' x x' : I} (h : I.Entails φ φ') (e : I.Eq x x') :
    I.Entails (.or φ (.or (.neg x) x)) (.or φ' (.or (.neg x') x')) :=
  ent_or_elim (ent_trans h (ent_or_left _ _))
    (ent_trans (ent_or_elim (ent_trans (eq_ent (ieq_neg e)) (ent_or_left _ _))
      (ent_trans (eq_ent e) (ent_or_right _ _))) (ent_or_right _ _))

/-- Composition in path types, at related points. -/
theorem kanH2_path_core {T T' : Tm} (hP : PathStr S k T T') (hTT : RT2 S k T T')
    (hIH : ∀ k' (ρ : ISub k' k) L1 b0 b1, RedT S k' (T.isub ρ) (.path L1 b0 b1) → ∀ (s : I), s.Scoped k' →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' ((L1.dinst s).isub ρ') X' → KanH2 S k'' ((L1.dinst s).isub ρ') X')
    {φ φ' : I} {u u' a0 a0' : Tm} (hty : HasTy S k .one [] (.hcomp T φ u a0) T)
    (hty' : HasTy S k .one [] (.hcomp T' φ' u' a0') T)
    (heq : EqTm S k .one [] (.hcomp T φ u a0) (.hcomp T' φ' u' a0') T)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k T φ u u') (ha0 : RE2 S k T a0 a0')
    {L1 b0 b1 : Tm} (hR : RedT S k T (.path L1 b0 b1)) {r r' : I} (hr : r.Scoped k) (hr' : r'.Scoped k)
    (hE : I.Eq r r') :
    RE2 S k (L1.dinst r) (.papp (.hcomp T φ u a0) r) (.papp (.hcomp T' φ' u' a0') r') := by
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hTK : IsTyK S k T := isTyK_of_ty hW hty
  have hTc : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTK)
  have hXT : TyCode k (semK S k T) := tyCode_of_ty hW hty
  choose L2 c0 c1 L2' c0' c1' hw using hP.whnf
  have hR0 : RedT S k (T.isub (ISub.id k)) (.path L1 b0 b1) := by rw [hTc]; exact hR
  have hL2id : L2 k (ISub.id k) = L1 := by
    have := RedW.unique (hw k (ISub.id k)).1.1 hR0.1; injection this
  have hrid : r.subst (ISub.id k).τ = r := I_subst_id hr
  have hrid' : r'.subst (ISub.id k).τ = r' := I_subst_id hr'
  have hsc : ∀ k' (ρ : ISub k' k), (r.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr ρ.sc
  have hsc' : ∀ k' (ρ : ISub k' k), (r'.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr' ρ.sc
  have hEρ : ∀ k' (ρ : ISub k' k), I.Eq (r.subst ρ.τ) (r'.subst ρ.τ) := fun k' ρ => I_eq_subst hE ρ.τ
  have hX2 : ∀ k' (ρ : ISub k' k) (s : I), s.Scoped k' → TyCode k' (semK S k' ((L2 k' ρ).dinst s)) :=
    fun k' ρ s hs => hP.tc k' ρ _ _ _ (hw k' ρ).1 s hs
  have hCY : ∀ k' (ρ : ISub k' k), RT2 S k' ((L1.dinst r).isub ρ) ((L2 k' ρ).dinst (r.subst ρ.τ)) := by
    intro k' ρ
    rw [isub_dinst]
    exact hP.coh k (ISub.id k) k' ρ L1 b0 b1 (L2 k' ρ) (c0 k' ρ) (c1 k' ρ) hR0
      (by rw [ISub.id_comp]; exact (hw k' ρ).1) _ (hsc k' ρ)
  have hXY : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' ((L1.dinst r).isub ρ)) := fun k' ρ =>
    RT2.tyCode_l hW (hCY k' ρ) (hX2 k' ρ _ (hsc k' ρ))
  have hLL' : ∀ k' (ρ : ISub k' k) (s s' : I), s.Scoped k' → s'.Scoped k' → I.Eq s s' →
      RT2 S k' ((L2 k' ρ).dinst s) ((L2' k' ρ).dinst s') := fun k' ρ => (hw k' ρ).2.2.1
  have hel : ∀ k' (ρ : ISub k' k) f f', RE2 S k' (T.isub ρ) f f' →
      RE2 S k' ((L1.dinst r).isub ρ) (.papp f (r.subst ρ.τ)) (.papp f' (r'.subst ρ.τ)) := fun k' ρ f f' h =>
    RE2.conv' hW (hCY k' ρ) ((hP.elim k' ρ _ _ _ f f' (hw k' ρ).1 h).1 _ _ (hsc k' ρ) (hsc' k' ρ) (hEρ k' ρ))
      (hXY k' ρ)
  have hX : TyCode k (semK S k (L1.dinst r)) := by
    have := hX2 k (ISub.id k) r hr; rwa [hL2id] at this
  have hYY : RT2 S k (L1.dinst r) (L1.dinst r) := by
    have := hLL' k (ISub.id k) r r hr hr (I_eq_refl r); rw [hL2id] at this; exact RT2.refl hW hX this
  have hYv : ∀ k' (ρ : ISub k' k), RT2 S k' ((L1.dinst r).isub ρ) ((L1.dinst r).isub ρ) := fun k' ρ =>
    RT2.isub hW hX hYY ρ
  have hpT : HasTy S k .one [] (.hcomp T φ u a0) (.path L1 b0 b1) := hty.tyConv hR.2
  have hE0 : EqTm S k .one [] (.papp (.hcomp T φ u a0) r) (.papp (.hcomp T' φ' u' a0') r') (L1.dinst r) :=
    EqTm.papp (heq.tyConv hR.2) hr hr' hE
  have hcoh : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'),
      RT2 S k'' (((L2 k' ρ).dinst (r.subst ρ.τ)).isub ρ') ((L2 k'' (ρ.comp ρ')).dinst (r.subst (ρ.comp ρ').τ)) := by
    intro k' ρ k'' ρ'
    rw [isub_dinst, I_subst_comp]
    exact hP.coh k' ρ k'' ρ' _ _ _ _ _ _ (hw k' ρ).1 (hw k'' (ρ.comp ρ')).1 _ (by rw [← I_subst_comp]; exact hsc k'' _)
  have hXTρ : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' (T.isub ρ)) := fun k' ρ => by
    rw [semK_isubTy hW hTK ρ]; exact hXT.res ρ.hom
  have hTρ : ∀ k' (ρ : ISub k' k), RT2 S k' (T.isub ρ) (T'.isub ρ) := fun k' ρ => RT2.isub hW hXT hTT ρ
  have reflL : ∀ k' (ρ : ISub k' k) {f g : Tm}, RE2 S k' (T.isub ρ) f g → RE2 S k' (T.isub ρ) f f :=
    fun k' ρ f g h => RE2.trans hW (hTρ k' ρ) h (RE2.symm hW (hTρ k' ρ) h)
  have reflR : ∀ k' (ρ : ISub k' k) {f g : Tm}, RE2 S k' (T.isub ρ) g f → RE2 S k' (T.isub ρ) f f :=
    fun k' ρ f g h => RE2.trans hW (hTρ k' ρ) (RE2.symm hW (hTρ k' ρ) h) h
  have hT'T : RT2 S k T' T := RT2.symm hW hXT hTT
  have ha0'' : RE2 S k T' a0' a0' := by
    have h := RE2.conv hW hTT ha0
    exact RE2.trans hW hT'T (RE2.symm hW hT'T h) h
  have hcE0 : ∀ k1 (ρ1 : ISub k1 k) k2 (ρ2 : ISub k2 k1),
      RE2 S k2 ((L2 k2 (ρ1.comp ρ2)).dinst .zero) ((c0 k1 ρ1).isub ρ2) (c0 k2 (ρ1.comp ρ2)) := by
    intro k1 ρ1 k2 ρ2
    have e1 := (hP.elim k1 ρ1 _ _ _ _ _ (hw k1 ρ1).1 (RE2.isub hW ha0 ρ1)).2.1
    have e2 := RE2.isub hW e1 ρ2
    have c := hP.coh k1 ρ1 k2 ρ2 _ _ _ _ _ _ (hw k1 ρ1).1 (hw k2 (ρ1.comp ρ2)).1 .zero trivial
    rw [isub_dinst] at e2
    have e2' := RE2.conv hW c e2
    have ea : (Tm.papp (a0.isub ρ1) .zero).isub ρ2 = .papp (a0.isub (ρ1.comp ρ2)) .zero := by
      show Tm.papp ((a0.isub ρ1).isub ρ2) _ = _; rw [Tm.isub_isub]; rfl
    rw [ea] at e2'
    have e3 := (hP.elim k2 (ρ1.comp ρ2) _ _ _ _ _ (hw k2 (ρ1.comp ρ2)).1 (RE2.isub hW ha0 (ρ1.comp ρ2))).2.1
    have hA := hLL' k2 (ρ1.comp ρ2) .zero .zero trivial trivial (I_eq_refl _)
    exact RE2.trans hW hA (RE2.symm hW hA e2') e3
  have hcE0' : ∀ k1 (ρ1 : ISub k1 k) k2 (ρ2 : ISub k2 k1),
      RE2 S k2 ((L2' k2 (ρ1.comp ρ2)).dinst .zero) ((c0' k1 ρ1).isub ρ2) (c0' k2 (ρ1.comp ρ2)) := by
    intro k1 ρ1 k2 ρ2
    have e1 := (hP.elim' k1 ρ1 _ _ _ _ _ (hw k1 ρ1).2.1 (RE2.isub hW ha0'' ρ1)).2.1
    have e2 := RE2.isub hW e1 ρ2
    have c := hP.coh' k1 ρ1 k2 ρ2 _ _ _ _ _ _ (hw k1 ρ1).2.1 (hw k2 (ρ1.comp ρ2)).2.1 .zero trivial
    rw [isub_dinst] at e2
    have e2' := RE2.conv hW c e2
    have ea : (Tm.papp (a0'.isub ρ1) .zero).isub ρ2 = .papp (a0'.isub (ρ1.comp ρ2)) .zero := by
      show Tm.papp ((a0'.isub ρ1).isub ρ2) _ = _; rw [Tm.isub_isub]; rfl
    rw [ea] at e2'
    have e3 := (hP.elim' k2 (ρ1.comp ρ2) _ _ _ _ _ (hw k2 (ρ1.comp ρ2)).2.1
      (RE2.isub hW ha0'' (ρ1.comp ρ2))).2.1
    have hA := hLL' k2 (ρ1.comp ρ2) .zero .zero trivial trivial (I_eq_refl _)
    have hA' := RT2.symm hW (hX2 k2 (ρ1.comp ρ2) .zero trivial) hA
    exact RE2.trans hW hA' (RE2.symm hW hA' e2') e3
  have hLx0 : ∀ k4 (v : ISub k4 k) (x : I), x.Scoped k4 → I.Eq x .zero →
      RT2 S k4 ((L2 k4 v).dinst x) ((L2 k4 v).dinst .zero) := by
    intro k4 v x hx hx0
    have t1 := hLL' k4 v x .zero hx trivial hx0
    have t2 := hLL' k4 v .zero .zero trivial trivial (I_eq_refl _)
    exact RT2.trans hW (hX2 k4 v x hx) t1 (RT2.symm hW (hX2 k4 v .zero trivial) t2)
  have hpE0 : ∀ k4 (v : ISub k4 k) f (x : I), RE2 S k4 (T.isub v) f f → x.Scoped k4 → I.Eq x .zero →
      RE2 S k4 ((L2 k4 v).dinst .zero) (.papp f x) (c0 k4 v) := by
    intro k4 v f x h hx hx0
    have el := hP.elim k4 v _ _ _ f f (hw k4 v).1 h
    have t2 := hLL' k4 v .zero .zero trivial trivial (I_eq_refl _)
    exact RE2.trans hW t2 (RE2.conv hW (hLx0 k4 v x hx hx0) (el.1 x .zero hx trivial hx0)) el.2.1
  have hY0 : ∀ k4 (v : ISub k4 k), I.Eq (r.subst v.τ) .zero → RT2 S k4 ((L1.dinst r).isub v) ((L2 k4 v).dinst .zero) :=
    fun k4 v e => RT2.trans hW (hXY k4 v) (hCY k4 v) (hLx0 k4 v _ (hsc k4 v) e)
  have hY0' : ∀ k4 (v : ISub k4 k), I.Eq (r.subst v.τ) .zero → RT2 S k4 ((L1.dinst r).isub v) ((L2' k4 v).dinst .zero) :=
    fun k4 v e => RT2.trans hW (hXY k4 v) (hY0 k4 v e) (hLL' k4 v .zero .zero trivial trivial (I_eq_refl _))
  have toY0 : ∀ k4 (v : ISub k4 k) {a b : Tm}, I.Eq (r.subst v.τ) .zero → RE2 S k4 ((L2 k4 v).dinst .zero) a b →
      RE2 S k4 ((L1.dinst r).isub v) a b := fun k4 v a b e h => RE2.conv' hW (hY0 k4 v e) h (hXY k4 v)
  have toY0' : ∀ k4 (v : ISub k4 k) {a b : Tm}, I.Eq (r.subst v.τ) .zero → RE2 S k4 ((L2' k4 v).dinst .zero) a b →
      RE2 S k4 ((L1.dinst r).isub v) a b := fun k4 v a b e h => RE2.conv' hW (hY0' k4 v e) h (hXY k4 v)
  have hcE1 : ∀ k1 (ρ1 : ISub k1 k) k2 (ρ2 : ISub k2 k1),
      RE2 S k2 ((L2 k2 (ρ1.comp ρ2)).dinst .one) ((c1 k1 ρ1).isub ρ2) (c1 k2 (ρ1.comp ρ2)) := by
    intro k1 ρ1 k2 ρ2
    have e1 := (hP.elim k1 ρ1 _ _ _ _ _ (hw k1 ρ1).1 (RE2.isub hW ha0 ρ1)).2.2
    have e2 := RE2.isub hW e1 ρ2
    have c := hP.coh k1 ρ1 k2 ρ2 _ _ _ _ _ _ (hw k1 ρ1).1 (hw k2 (ρ1.comp ρ2)).1 .one trivial
    rw [isub_dinst] at e2
    have e2' := RE2.conv hW c e2
    have ea : (Tm.papp (a0.isub ρ1) .one).isub ρ2 = .papp (a0.isub (ρ1.comp ρ2)) .one := by
      show Tm.papp ((a0.isub ρ1).isub ρ2) _ = _; rw [Tm.isub_isub]; rfl
    rw [ea] at e2'
    have e3 := (hP.elim k2 (ρ1.comp ρ2) _ _ _ _ _ (hw k2 (ρ1.comp ρ2)).1 (RE2.isub hW ha0 (ρ1.comp ρ2))).2.2
    have hA := hLL' k2 (ρ1.comp ρ2) .one .one trivial trivial (I_eq_refl _)
    exact RE2.trans hW hA (RE2.symm hW hA e2') e3
  have hcE1' : ∀ k1 (ρ1 : ISub k1 k) k2 (ρ2 : ISub k2 k1),
      RE2 S k2 ((L2' k2 (ρ1.comp ρ2)).dinst .one) ((c1' k1 ρ1).isub ρ2) (c1' k2 (ρ1.comp ρ2)) := by
    intro k1 ρ1 k2 ρ2
    have e1 := (hP.elim' k1 ρ1 _ _ _ _ _ (hw k1 ρ1).2.1 (RE2.isub hW ha0'' ρ1)).2.2
    have e2 := RE2.isub hW e1 ρ2
    have c := hP.coh' k1 ρ1 k2 ρ2 _ _ _ _ _ _ (hw k1 ρ1).2.1 (hw k2 (ρ1.comp ρ2)).2.1 .one trivial
    rw [isub_dinst] at e2
    have e2' := RE2.conv hW c e2
    have ea : (Tm.papp (a0'.isub ρ1) .one).isub ρ2 = .papp (a0'.isub (ρ1.comp ρ2)) .one := by
      show Tm.papp ((a0'.isub ρ1).isub ρ2) _ = _; rw [Tm.isub_isub]; rfl
    rw [ea] at e2'
    have e3 := (hP.elim' k2 (ρ1.comp ρ2) _ _ _ _ _ (hw k2 (ρ1.comp ρ2)).2.1
      (RE2.isub hW ha0'' (ρ1.comp ρ2))).2.2
    have hA := hLL' k2 (ρ1.comp ρ2) .one .one trivial trivial (I_eq_refl _)
    have hA' := RT2.symm hW (hX2 k2 (ρ1.comp ρ2) .one trivial) hA
    exact RE2.trans hW hA' (RE2.symm hW hA' e2') e3
  have hLx1 : ∀ k4 (v : ISub k4 k) (x : I), x.Scoped k4 → I.Eq x .one →
      RT2 S k4 ((L2 k4 v).dinst x) ((L2 k4 v).dinst .one) := by
    intro k4 v x hx hx0
    have t1 := hLL' k4 v x .one hx trivial hx0
    have t2 := hLL' k4 v .one .one trivial trivial (I_eq_refl _)
    exact RT2.trans hW (hX2 k4 v x hx) t1 (RT2.symm hW (hX2 k4 v .one trivial) t2)
  have hpE1 : ∀ k4 (v : ISub k4 k) f (x : I), RE2 S k4 (T.isub v) f f → x.Scoped k4 → I.Eq x .one →
      RE2 S k4 ((L2 k4 v).dinst .one) (.papp f x) (c1 k4 v) := by
    intro k4 v f x h hx hx0
    have el := hP.elim k4 v _ _ _ f f (hw k4 v).1 h
    have t2 := hLL' k4 v .one .one trivial trivial (I_eq_refl _)
    exact RE2.trans hW t2 (RE2.conv hW (hLx1 k4 v x hx hx0) (el.1 x .one hx trivial hx0)) el.2.2
  have hY1 : ∀ k4 (v : ISub k4 k), I.Eq (r.subst v.τ) .one → RT2 S k4 ((L1.dinst r).isub v) ((L2 k4 v).dinst .one) :=
    fun k4 v e => RT2.trans hW (hXY k4 v) (hCY k4 v) (hLx1 k4 v _ (hsc k4 v) e)
  have hY1' : ∀ k4 (v : ISub k4 k), I.Eq (r.subst v.τ) .one → RT2 S k4 ((L1.dinst r).isub v) ((L2' k4 v).dinst .one) :=
    fun k4 v e => RT2.trans hW (hXY k4 v) (hY1 k4 v e) (hLL' k4 v .one .one trivial trivial (I_eq_refl _))
  have toY1 : ∀ k4 (v : ISub k4 k) {a b : Tm}, I.Eq (r.subst v.τ) .one → RE2 S k4 ((L2 k4 v).dinst .one) a b →
      RE2 S k4 ((L1.dinst r).isub v) a b := fun k4 v a b e h => RE2.conv' hW (hY1 k4 v e) h (hXY k4 v)
  have toY1' : ∀ k4 (v : ISub k4 k) {a b : Tm}, I.Eq (r.subst v.τ) .one → RE2 S k4 ((L2' k4 v).dinst .one) a b →
      RE2 S k4 ((L1.dinst r).isub v) a b := fun k4 v a b e h => RE2.conv' hW (hY1' k4 v e) h (hXY k4 v)
  have eq0 : ∀ {k4 : ℕ} {x : I}, x.Scoped k4 → I.Entails .one (.neg x) → I.Eq x .zero := fun {k4} {x} hx h =>
    ieq_zero_of_holds_neg hx (entails_holds h (ρ := idEnv k4) (by rw [ival_one]; rfl))
  have eq1 : ∀ {k4 : ℕ} {x : I}, x.Scoped k4 → I.Entails .one x → I.Eq x .one := fun {k4} {x} hx h =>
    ieq_one_of_holds hx (entails_holds h (ρ := idEnv k4) (by rw [ival_one]; rfl))
  -- the typings of the tubes of the reducts
  have hsysT : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') (x : I), x.Scoped k'' →
      ¬ I.Entails .one (φ.subst ρ.τ) →
      (ival (idEnv k'') ((I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).subst ρ'.τ)).holds →
      HasTy S k'' .one [] (((sysP (φ.subst ρ.τ) (r.subst ρ.τ) (u.isub ρ.up) (c0 k' ρ) (c1 k' ρ)).isub ρ'.up).dinst x)
        ((L1.dinst r).isub (ρ.comp ρ')) := by
    intro k' ρ k'' ρ' x hx hf hh
    have hρ : HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (T.isub ρ) :=
      HasTy.isubS hW hty ρ
    have h1 := HasTy.isubS hW (HasTy.eqR (papp_hcomp_path hW hf (hsc k' ρ) hρ (hw k' ρ).1).2) ρ'
    have h2 := hcomp_tube_typed hW h1 x hx hh
    have cc := hcoh k' ρ k'' ρ'
    exact h2.tyConv (TyEq.trans hW (Comp2_ty_base cc).2.2.2.2.2
      (TyEq.symm (Comp2_ty_base (hCY k'' (ρ.comp ρ'))).2.2.2.2.2))
  have hsysT' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') (x : I), x.Scoped k'' →
      ¬ I.Entails .one (φ'.subst ρ.τ) →
      (ival (idEnv k'') ((I.or (φ'.subst ρ.τ) (.or (.neg (r'.subst ρ.τ)) (r'.subst ρ.τ))).subst ρ'.τ)).holds →
      HasTy S k'' .one [] (((sysP (φ'.subst ρ.τ) (r'.subst ρ.τ) (u'.isub ρ.up) (c0' k' ρ) (c1' k' ρ)).isub ρ'.up).dinst x)
        ((L1.dinst r).isub (ρ.comp ρ')) := by
    intro k' ρ k'' ρ' x hx hf hh
    have hρ : HasTy S k' .one [] (.hcomp (T'.isub ρ) (φ'.subst ρ.τ) (u'.isub ρ.up) (a0'.isub ρ)) (T'.isub ρ) :=
      (HasTy.isubS hW hty' ρ).tyConv (hP.tyEq.isub hW ρ)
    have h1 := HasTy.isubS hW (HasTy.eqR (papp_hcomp_path hW hf (hsc' k' ρ) hρ (hw k' ρ).2.1).2) ρ'
    have h2 := hcomp_tube_typed hW h1 x hx hh
    have e := TyEq.trans hW (TyEq.symm (Comp2_ty_base (hLL' k' ρ _ _ (hsc k' ρ) (hsc' k' ρ) (hEρ k' ρ))).2.2.2.2.2)
      (TyEq.symm (Comp2_ty_base (hCY k' ρ)).2.2.2.2.2)
    have h3 := h2.tyConv (e.isub hW ρ')
    rwa [Tm.isub_isub] at h3
  -- chains of related endpoints, at the type of the points
  have tr : ∀ {k4 : ℕ} (v : ISub k4 k) {a b c : Tm}, RE2 S k4 ((L1.dinst r).isub v) a b →
      RE2 S k4 ((L1.dinst r).isub v) b c → RE2 S k4 ((L1.dinst r).isub v) a c :=
    fun {k4} v a b c h1 h2 => RE2.trans hW (hYv k4 v) h1 h2
  have sy : ∀ {k4 : ℕ} (v : ISub k4 k) {a b : Tm}, RE2 S k4 ((L1.dinst r).isub v) a b →
      RE2 S k4 ((L1.dinst r).isub v) b a := fun {k4} v a b h => RE2.symm hW (hYv k4 v) h
  have cL0 : ∀ k1 (ρ1 : ISub k1 k) k4 (ρ2 : ISub k4 k1), I.Eq (r.subst (ρ1.comp ρ2).τ) .zero →
      RE2 S k4 ((L1.dinst r).isub (ρ1.comp ρ2)) ((c0 k1 ρ1).isub ρ2) (c0 k4 (ρ1.comp ρ2)) :=
    fun k1 ρ1 k4 ρ2 e => toY0 k4 _ e (hcE0 k1 ρ1 k4 ρ2)
  have cR0 : ∀ k1 (ρ1 : ISub k1 k) k4 (ρ2 : ISub k4 k1), I.Eq (r.subst (ρ1.comp ρ2).τ) .zero →
      RE2 S k4 ((L1.dinst r).isub (ρ1.comp ρ2)) (c0 k4 (ρ1.comp ρ2)) ((c0' k1 ρ1).isub ρ2) := by
    intro k1 ρ1 k4 ρ2 e
    have hA' := RT2.symm hW (hX2 k4 (ρ1.comp ρ2) .zero trivial)
      (hLL' k4 (ρ1.comp ρ2) .zero .zero trivial trivial (I_eq_refl _))
    exact tr _ (toY0 k4 _ e (hw k4 (ρ1.comp ρ2)).2.2.2.1) (toY0' k4 _ e (RE2.symm hW hA' (hcE0' k1 ρ1 k4 ρ2)))
  have pL0 : ∀ k4 (v : ISub k4 k) f g, RE2 S k4 (T.isub v) f g → I.Eq (r.subst v.τ) .zero →
      RE2 S k4 ((L1.dinst r).isub v) (.papp f (r.subst v.τ)) (c0 k4 v) :=
    fun k4 v f g h e => toY0 k4 v e (hpE0 k4 v f _ (reflL k4 v h) (hsc k4 v) e)
  have pR0 : ∀ k4 (v : ISub k4 k) f g, RE2 S k4 (T.isub v) g f → I.Eq (r.subst v.τ) .zero →
      RE2 S k4 ((L1.dinst r).isub v) (.papp f (r'.subst v.τ)) (c0 k4 v) :=
    fun k4 v f g h e => toY0 k4 v e (hpE0 k4 v f _ (reflR k4 v h) (hsc' k4 v) (I_eq_trans (I_eq_symm (hEρ k4 v)) e))
  have cL1 : ∀ k1 (ρ1 : ISub k1 k) k4 (ρ2 : ISub k4 k1), I.Eq (r.subst (ρ1.comp ρ2).τ) .one →
      RE2 S k4 ((L1.dinst r).isub (ρ1.comp ρ2)) ((c1 k1 ρ1).isub ρ2) (c1 k4 (ρ1.comp ρ2)) :=
    fun k1 ρ1 k4 ρ2 e => toY1 k4 _ e (hcE1 k1 ρ1 k4 ρ2)
  have cR1 : ∀ k1 (ρ1 : ISub k1 k) k4 (ρ2 : ISub k4 k1), I.Eq (r.subst (ρ1.comp ρ2).τ) .one →
      RE2 S k4 ((L1.dinst r).isub (ρ1.comp ρ2)) (c1 k4 (ρ1.comp ρ2)) ((c1' k1 ρ1).isub ρ2) := by
    intro k1 ρ1 k4 ρ2 e
    have hA' := RT2.symm hW (hX2 k4 (ρ1.comp ρ2) .one trivial)
      (hLL' k4 (ρ1.comp ρ2) .one .one trivial trivial (I_eq_refl _))
    exact tr _ (toY1 k4 _ e (hw k4 (ρ1.comp ρ2)).2.2.2.2) (toY1' k4 _ e (RE2.symm hW hA' (hcE1' k1 ρ1 k4 ρ2)))
  have pL1 : ∀ k4 (v : ISub k4 k) f g, RE2 S k4 (T.isub v) f g → I.Eq (r.subst v.τ) .one →
      RE2 S k4 ((L1.dinst r).isub v) (.papp f (r.subst v.τ)) (c1 k4 v) :=
    fun k4 v f g h e => toY1 k4 v e (hpE1 k4 v f _ (reflL k4 v h) (hsc k4 v) e)
  have pR1 : ∀ k4 (v : ISub k4 k) f g, RE2 S k4 (T.isub v) g f → I.Eq (r.subst v.τ) .one →
      RE2 S k4 ((L1.dinst r).isub v) (.papp f (r'.subst v.τ)) (c1 k4 v) :=
    fun k4 v f g h e => toY1 k4 v e (hpE1 k4 v f _ (reflR k4 v h) (hsc' k4 v) (I_eq_trans (I_eq_symm (hEρ k4 v)) e))
  have H := kanH2_elim_core hW hφs (fun k' ρ x => .papp x (r.subst ρ.τ)) (fun k' ρ x => .papp x (r'.subst ρ.τ))
    (fun k' ρ => (L2 k' ρ).dinst (r.subst ρ.τ)) (fun k' ρ => (L2' k' ρ).dinst (r'.subst ρ.τ))
    (fun k' ρ => sysP (φ.subst ρ.τ) (r.subst ρ.τ) (u.isub ρ.up) (c0 k' ρ) (c1 k' ρ))
    (fun k' ρ => sysP (φ'.subst ρ.τ) (r'.subst ρ.τ) (u'.isub ρ.up) (c0' k' ρ) (c1' k' ρ))
    (fun k' ρ => .papp (a0.isub ρ) (r.subst ρ.τ)) (fun k' ρ => .papp (a0'.isub ρ) (r'.subst ρ.τ))
    (fun k' ρ => .or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ)))
    (fun k' ρ => .or (φ'.subst ρ.τ) (.or (.neg (r'.subst ρ.τ)) (r'.subst ρ.τ)))
    hX hYY (by simp only [hrid]; exact HasTy.papp hpT hr) (by simp only [hrid']; exact HasTy.eqR hE0)
    (by simp only [hrid, hrid']; exact hE0)
    (fun k' ρ k'' ρ' x => by
      show Tm.papp (x.isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = Tm.papp (x.isub ρ') (r.subst (ρ.comp ρ').τ)
      rw [I_subst_comp])
    (fun k' ρ k'' ρ' x => by
      show Tm.papp (x.isub ρ') ((r'.subst ρ.τ).subst ρ'.τ) = Tm.papp (x.isub ρ') (r'.subst (ρ.comp ρ').τ)
      rw [I_subst_comp])
    (fun k' ρ => ?_) (fun k' ρ => ?_) hel
    (fun k' ρ k'' ρ' hf2 => by
      show I.Entails .one (.or ((φ.subst ρ.τ).subst ρ'.τ) _)
      rw [← I_subst_comp]; exact ent_trans hf2 (ent_or_left _ _))
    (fun k' ρ k'' ρ' _ => by
      show I.Entails (.or ((φ.subst ρ.τ).subst ρ'.τ) (.or (.neg ((r.subst ρ.τ).subst ρ'.τ)) ((r.subst ρ.τ).subst ρ'.τ)))
          (.or (φ'.subst (ρ.comp ρ').τ) (.or (.neg (r'.subst (ρ.comp ρ').τ)) (r'.subst (ρ.comp ρ').τ))) ∧
        I.Entails (.or (φ'.subst (ρ.comp ρ').τ) (.or (.neg (r'.subst (ρ.comp ρ').τ)) (r'.subst (ρ.comp ρ').τ)))
          (.or ((φ.subst ρ.τ).subst ρ'.τ) (.or (.neg ((r.subst ρ.τ).subst ρ'.τ)) ((r.subst ρ.τ).subst ρ'.τ)))
      rw [← I_subst_comp, ← I_subst_comp]
      exact ⟨ent_or3 (ent_subst h12 _) (hEρ _ _), ent_or3 (ent_subst h21 _) (I_eq_symm (hEρ _ _))⟩)
    (fun k' ρ k'' ρ' hf hf2 => ?_)
    (fun k' ρ k'' ρ' hnf => ?_)
    (fun k' ρ k'' ρ' _ => by
      show RE2 S k'' _ ((Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ')
        (Tm.papp (a0'.isub (ρ.comp ρ')) (r'.subst (ρ.comp ρ').τ))
      rw [show (Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ' = Tm.papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ) by
        show Tm.papp ((a0.isub ρ).isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = _; rw [Tm.isub_isub, I_subst_comp]]
      exact hel k'' (ρ.comp ρ') _ _ (RE2.isub hW ha0 _))
    (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' _ => ?_) h12 h21 htube
  · simpa only [hrid, hrid'] using H
  · have hρ : HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (T.isub ρ) :=
      HasTy.isubS hW hty ρ
    have e := TyEq.symm (Comp2_ty_base (hCY k' ρ)).2.2.2.2.2
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a, b⟩ := papp_hcomp_face_path hW hf (hsc k' ρ) hρ (hw k' ρ).1.2
      exact ⟨a, b.tyConv e⟩
    · obtain ⟨a, b⟩ := papp_hcomp_path hW hf (hsc k' ρ) hρ (hw k' ρ).1
      exact ⟨a, b.tyConv e⟩
  · have hρ : HasTy S k' .one [] (.hcomp (T'.isub ρ) (φ'.subst ρ.τ) (u'.isub ρ.up) (a0'.isub ρ)) (T'.isub ρ) :=
      (HasTy.isubS hW hty' ρ).tyConv (hP.tyEq.isub hW ρ)
    have e := TyEq.trans hW (TyEq.symm (Comp2_ty_base (hLL' k' ρ _ _ (hsc k' ρ) (hsc' k' ρ) (hEρ k' ρ))).2.2.2.2.2)
      (TyEq.symm (Comp2_ty_base (hCY k' ρ)).2.2.2.2.2)
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a, b⟩ := papp_hcomp_face_path hW hf (hsc' k' ρ) hρ (hw k' ρ).2.1.2
      exact ⟨a, b.tyConv e⟩
    · obtain ⟨a, b⟩ := papp_hcomp_path hW hf (hsc' k' ρ) hρ (hw k' ρ).2.1
      exact ⟨a, b.tyConv e⟩
  · -- the tube's end, where the face holds only after restriction
    have hsφ : (I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).Scoped k' :=
      ⟨I.scoped_subst hφs ρ.sc, hsc k' ρ, hsc k' ρ⟩
    have hh : (ival (idEnv k'') ((I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).subst ρ'.τ)).holds := by
      refine (holds_iff_entails (I.scoped_subst hsφ ρ'.sc)).2 ?_
      show I.Entails .one (.or ((φ.subst ρ.τ).subst ρ'.τ) _)
      rw [← I_subst_comp]; exact ent_trans hf2 (ent_or_left _ _)
    have hT := hsysT k' ρ k'' ρ' .one trivial hf hh
    show RE2 S k'' _ (((sysP (φ.subst ρ.τ) (r.subst ρ.τ) (u.isub ρ.up) (c0 k' ρ) (c1 k' ρ)).isub ρ'.up).dinst .one)
      (.papp ((u'.isub (ρ.comp ρ').up).dinst .one) (r'.subst (ρ.comp ρ').τ))
    rw [sysP_isub_dinst] at hT ⊢
    simp only [Tm.isub_isub, ← ISub.up_comp, ← I_subst_comp] at hT ⊢
    have hφw : ∀ k3 (σ3 : ISub k3 k''), (ival (idEnv k3) (φ.subst (ρ.comp (ρ'.comp σ3)).τ)).holds := fun k3 σ3 =>
      (holds_iff_entails (I.scoped_subst hφs (ρ.comp (ρ'.comp σ3)).sc)).2 (by rw [← ISub.comp_assoc]; exact ent_comp hf2)
    have hq := hel k'' (ρ.comp ρ') _ _ (htube k'' (ρ.comp ρ') .one .one trivial trivial (I_eq_refl _)
      ((holds_iff_entails (I.scoped_subst hφs (ρ.comp ρ').sc)).2 hf2))
    refine RE2.symm hW (hYv k'' _) (RE2_sys_r hW (I.scoped_subst hφs (ρ.comp ρ').sc) (hsc k'' _)
      (ent_trans hf2 (ent_or_left _ _)) (hYv k'' _) hT (RE2.typed hq).2.1
      (fun k3 σ3 h => ?_) (fun k3 σ3 h => ?_) (fun k3 σ3 h => ?_)) <;>
      simp only [papp_dinst_isub, Tm.isub_isub, ← I_subst_comp, ISub.comp_assoc] at h ⊢
    · exact RE2.symm hW (hYv k3 _) (hel k3 _ _ _ (htube k3 _ _ _ trivial trivial (I_eq_refl _) (hφw k3 σ3)))
    · have h' : I.Entails .one (I.neg (r.subst (ρ.comp (ρ'.comp σ3)).τ)) := by
        have := ent_comp_inv (φ := .neg r) h; rwa [ISub.comp_assoc] at this
      have e0 := eq0 (hsc k3 _) h'
      exact tr _ (pR0 k3 _ _ _ (htube k3 _ .one .one trivial trivial (I_eq_refl _) (hφw k3 σ3)) e0)
        (sy _ (cL0 k' ρ k3 (ρ'.comp σ3) e0))
    · have e1 := eq1 (hsc k3 _) h
      exact tr _ (pR1 k3 _ _ _ (htube k3 _ .one .one trivial trivial (I_eq_refl _) (hφw k3 σ3)) e1)
        (sy _ (cL1 k' ρ k3 (ρ'.comp σ3) e1))
  · -- the tubes, where the face does not hold
    intro k3 σ3 x x' hx hx' hEx hh
    have hf : ¬ I.Entails .one (φ.subst ρ.τ) := fun h => hnf (ent_comp h)
    have hf' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hnf (ent_trans h (ent_subst h21 _))
    have hsφ : (I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).Scoped k' :=
      ⟨I.scoped_subst hφs ρ.sc, hsc k' ρ, hsc k' ρ⟩
    have hh1 : (ival (idEnv k3)
        ((I.or (φ.subst ρ.τ) (.or (.neg (r.subst ρ.τ)) (r.subst ρ.τ))).subst (ρ'.comp σ3).τ)).holds := by
      rw [I_subst_comp]; exact hh
    have hor : I.Entails .one (I.or (φ.subst (ρ.comp (ρ'.comp σ3)).τ)
        (.or (.neg (r.subst (ρ.comp (ρ'.comp σ3)).τ)) (r.subst (ρ.comp (ρ'.comp σ3)).τ))) := by
      have := (holds_iff_entails (I.scoped_subst hsφ (ρ'.comp σ3).sc)).1 hh1
      have e := ent_comp_inv (φ := I.or φ (.or (.neg r) r)) (ρ := ρ) (ρ' := ρ'.comp σ3) this
      exact e
    have hor' : I.Entails .one (I.or (φ'.subst (ρ.comp (ρ'.comp σ3)).τ)
        (.or (.neg (r'.subst (ρ.comp (ρ'.comp σ3)).τ)) (r'.subst (ρ.comp (ρ'.comp σ3)).τ))) :=
      ent_trans hor (ent_or3 (ent_subst h12 _) (hEρ k3 _))
    have hh2 : (ival (idEnv k3) ((I.or (φ'.subst (ρ.comp ρ').τ)
        (.or (.neg (r'.subst (ρ.comp ρ').τ)) (r'.subst (ρ.comp ρ').τ))).subst σ3.τ)).holds := by
      have hs' : (I.or φ' (.or (.neg r') r')).Scoped k := ⟨by
        obtain ⟨l1, ⟨-, h, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl; exact h, hr', hr'⟩
      refine (holds_iff_entails (I.scoped_subst (I.scoped_subst hs' (ρ.comp ρ').sc) σ3.sc)).2 ?_
      have e : I.Entails .one ((I.or φ' (.or (.neg r') r')).subst ((ρ.comp ρ').comp σ3).τ) := by
        rw [ISub.comp_assoc]; exact hor'
      rw [I_subst_comp] at e; exact e
    have hT := hsysT k' ρ k3 (ρ'.comp σ3) x hx hf hh1
    have hT' := hsysT' k'' (ρ.comp ρ') k3 σ3 x' hx' hf' hh2
    show RE2 S k3 (((L1.dinst r).isub (ρ.comp ρ')).isub σ3)
      ((((sysP (φ.subst ρ.τ) (r.subst ρ.τ) (u.isub ρ.up) (c0 k' ρ) (c1 k' ρ)).isub ρ'.up).isub σ3.up).dinst x)
      (((sysP (φ'.subst (ρ.comp ρ').τ) (r'.subst (ρ.comp ρ').τ) (u'.isub (ρ.comp ρ').up) (c0' k'' (ρ.comp ρ'))
        (c1' k'' (ρ.comp ρ'))).isub σ3.up).dinst x')
    rw [Tm.isub_isub (sysP _ _ _ _ _), ← ISub.up_comp, sysP_isub_dinst, sysP_isub_dinst]
    rw [sysP_isub_dinst] at hT hT'
    simp only [Tm.isub_isub, ← ISub.up_comp, ← I_subst_comp, ISub.comp_assoc] at hT hT' ⊢
    have hφs' : φ'.Scoped k := by
      obtain ⟨l1, ⟨-, h, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl; exact h
    -- passing to a further restriction
    have toV : ∀ {k4 : ℕ} (σ4 : ISub k4 k3) {ψ : I}, I.Entails .one ((ψ.subst (ρ.comp (ρ'.comp σ3)).τ).subst σ4.τ) →
        I.Entails .one (ψ.subst (ρ.comp (ρ'.comp (σ3.comp σ4))).τ) := fun σ4 ψ h => by
      have := ent_comp_inv h; simpa only [ISub.comp_assoc] using this
    have tube : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), I.Entails .one ((φ.subst (ρ.comp (ρ'.comp σ3)).τ).subst σ4.τ) →
        RE2 S k4 (T.isub (ρ.comp (ρ'.comp (σ3.comp σ4))))
          ((u.isub (ρ.comp (ρ'.comp (σ3.comp σ4))).up).dinst (x.subst σ4.τ))
          ((u'.isub (ρ.comp (ρ'.comp (σ3.comp σ4))).up).dinst (x'.subst σ4.τ)) := fun σ4 h =>
      htube _ _ _ _ (I.scoped_subst hx σ4.sc) (I.scoped_subst hx' σ4.sc) (I_eq_subst hEx _)
        ((holds_iff_entails (I.scoped_subst hφs (ρ.comp (ρ'.comp (σ3.comp σ4))).sc)).2 (toV σ4 h))
    have assoc : ∀ {k4 : ℕ} (σ4 : ISub k4 k3), (ρ.comp ρ').comp (σ3.comp σ4) = ρ.comp (ρ'.comp (σ3.comp σ4)) :=
      fun σ4 => ISub.comp_assoc _ _ _
    refine RE2_pathSys hW (I.scoped_subst hφs (ρ.comp (ρ'.comp σ3)).sc) (I.scoped_subst hφs' (ρ.comp (ρ'.comp σ3)).sc) (hsc k3 _) (hsc' k3 _) (hEρ k3 _)
      (ent_subst h12 _) (ent_subst h21 _) hor (hYv k3 _) hT hT'
      (fun k4 σ4 h => ?_) (fun k4 σ4 h h' => ?_) (fun k4 σ4 h h' => ?_) (fun k4 σ4 h h' => ?_)
      (fun k4 σ4 h h' => ?_) (fun k4 σ4 h' => ?_) (fun k4 σ4 h' => ?_) <;>
      simp only [papp_dinst_isub, Tm.isub_isub, ← I_subst_comp, ISub.comp_assoc]
    · exact hel k4 _ _ _ (tube σ4 h)
    · have e0 := eq0 (hsc k4 _) (toV σ4 (ψ := .neg r) h')
      have c := cR0 k'' (ρ.comp ρ') k4 (σ3.comp σ4) (by rw [assoc]; exact e0)
      rw [assoc] at c
      exact tr _ (hel k4 _ _ _ (tube σ4 h)) (tr _ (pR0 k4 _ _ _ (tube σ4 h) e0) c)
    · have e0 := eq0 (hsc k4 _) (toV σ4 (ψ := .neg r) h')
      exact tr _ (cL0 k' ρ k4 (ρ'.comp (σ3.comp σ4)) e0) (sy _ (pR0 k4 _ _ _ (tube σ4 h) e0))
    · have e1 := eq1 (hsc k4 _) (toV σ4 h')
      have c := cR1 k'' (ρ.comp ρ') k4 (σ3.comp σ4) (by rw [assoc]; exact e1)
      rw [assoc] at c
      exact tr _ (hel k4 _ _ _ (tube σ4 h)) (tr _ (pR1 k4 _ _ _ (tube σ4 h) e1) c)
    · have e1 := eq1 (hsc k4 _) (toV σ4 h')
      exact tr _ (cL1 k' ρ k4 (ρ'.comp (σ3.comp σ4)) e1) (sy _ (pR1 k4 _ _ _ (tube σ4 h) e1))
    · have e0 := eq0 (hsc k4 _) (toV σ4 (ψ := .neg r) h')
      have c := cR0 k'' (ρ.comp ρ') k4 (σ3.comp σ4) (by rw [assoc]; exact e0)
      rw [assoc] at c
      exact tr _ (cL0 k' ρ k4 (ρ'.comp (σ3.comp σ4)) e0) c
    · have e1 := eq1 (hsc k4 _) (toV σ4 h')
      have c := cR1 k'' (ρ.comp ρ') k4 (σ3.comp σ4) (by rw [assoc]; exact e1)
      rw [assoc] at c
      exact tr _ (cL1 k' ρ k4 (ρ'.comp (σ3.comp σ4)) e1) c
  · have cc := hcoh k' ρ k'' ρ'
    exact RT2.trans hW (RT2.tyCode_l hW cc (hX2 k'' _ _ (hsc k'' _))) cc
      (RT2.symm hW (hXY k'' _) (hCY k'' (ρ.comp ρ')))
  · have cc := hcoh k' ρ k'' ρ'
    exact hIH k' ρ (L2 k' ρ) (c0 k' ρ) (c1 k' ρ) (hw k' ρ).1 _ (hsc k' ρ) k'' ρ' _
      (RT2.trans hW (RT2.tyCode_l hW cc (hX2 k'' _ _ (hsc k'' _))) cc
        (hLL' k'' (ρ.comp ρ') _ _ (hsc k'' _) (hsc' k'' _) (hEρ k'' _)))


omit hW in
theorem sysP_dinst (φ r : I) (u c0 c1 : Tm) (x : I) :
    (sysP φ r u c0 c1).dinst x = .split φ (.papp (u.dinst x) r) (.or (.neg r) r) (.split (.neg r) c0 r c1) := by
  show Tm.split (φ.shift.subst (I.inst0 x)) (.papp (u.dinst x) (r.shift.subst (I.inst0 x)))
    (.or (.neg (r.shift.subst (I.inst0 x))) (r.shift.subst (I.inst0 x)))
    (.split (.neg (r.shift.subst (I.inst0 x))) (c0.dshift.dinst x) (r.shift.subst (I.inst0 x)) (c1.dshift.dinst x)) = _
  rw [I_shift_inst0, I_shift_inst0, dshift_dinst, dshift_dinst]

/-- The endpoints of the normal forms of the restrictions of a path type are coherent (given an element). -/
theorem PathStr.endCoh0 {T T' a a' : Tm} (hP : PathStr S k T T') (ha : RE2 S k T a a') {k1 : ℕ} {ρ1 : ISub k1 k}
    {L c0 c1 : Tm} (h1 : RedT S k1 (T.isub ρ1) (.path L c0 c1)) {k2 : ℕ} {ρ2 : ISub k2 k1} {L' c0' c1' : Tm}
    (h2 : RedT S k2 (T.isub (ρ1.comp ρ2)) (.path L' c0' c1')) :
    RE2 S k2 (L'.dinst .zero) (c0.isub ρ2) c0' := by
  have e1 := (hP.elim k1 ρ1 _ _ _ _ _ h1 (RE2.isub hW ha ρ1)).2.1
  have e2 := RE2.isub hW e1 ρ2
  have c := hP.coh k1 ρ1 k2 ρ2 _ _ _ _ _ _ h1 h2 .zero trivial
  rw [isub_dinst] at e2
  have e2' := RE2.conv hW c e2
  have ea : (Tm.papp (a.isub ρ1) .zero).isub ρ2 = .papp (a.isub (ρ1.comp ρ2)) .zero := by
    show Tm.papp ((a.isub ρ1).isub ρ2) _ = _; rw [Tm.isub_isub]; rfl
  rw [ea] at e2'
  have e3 := (hP.elim k2 (ρ1.comp ρ2) _ _ _ _ _ h2 (RE2.isub hW ha (ρ1.comp ρ2))).2.1
  obtain ⟨L4, d0, d1, L4', d0', d1', h4, -, hLL, -, -⟩ := hP.whnf k2 (ρ1.comp ρ2)
  obtain rfl : L4 = L' := by have := RedW.unique h4.1 h2.1; injection this
  have hA := hLL .zero .zero trivial trivial (I_eq_refl _)
  exact RE2.trans hW hA (RE2.symm hW hA e2') e3

/-- The endpoint of a composition in a path type. -/
theorem hcomp_path_end0 {T T' : Tm} (hP : PathStr S k T T') (hTT : RT2 S k T T') {φ : I} {u u' a0 a0' : Tm}
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (htube : Tube2 S k T φ u u') (ha0 : RE2 S k T a0 a0')
    {L1 b0 b1 : Tm} (hR : RedT S k T (.path L1 b0 b1)) :
    RE2 S k (L1.dinst .zero) (.papp (.hcomp T φ u a0) .zero) b0 := by
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hTK : IsTyK S k T := isTyK_of_ty hW hty
  have hTc : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTK)
  have hXT : TyCode k (semK S k T) := tyCode_of_ty hW hty
  have hR0 : RedT S k (T.isub (ISub.id k)) (.path L1 b0 b1) := by rw [hTc]; exact hR
  have hTρ : ∀ k' (ρ : ISub k' k), RT2 S k' (T.isub ρ) (T'.isub ρ) := fun k' ρ => RT2.isub hW hXT hTT ρ
  have reflL : ∀ k' (ρ : ISub k' k) {f g : Tm}, RE2 S k' (T.isub ρ) f g → RE2 S k' (T.isub ρ) f f :=
    fun k' ρ f g h => RE2.trans hW (hTρ k' ρ) h (RE2.symm hW (hTρ k' ρ) h)
  obtain ⟨L2, c0, c1, L2', c0', c1', h2, -, hLL, hb0, hb1⟩ := hP.whnf k (ISub.id k)
  have e := RedW.unique h2.1 hR0.1
  injection e with eL e0 e1
  subst L2 c0 c1
  have hX0 : TyCode k (semK S k (L1.dinst .zero)) := hP.tc k (ISub.id k) _ _ _ hR0 .zero trivial
  have hAA : RT2 S k (L1.dinst .zero) (L1.dinst .zero) := RT2.refl hW hX0 (hLL .zero .zero trivial trivial (I_eq_refl _))
  have hpT : HasTy S k .one [] (.hcomp T φ u a0) (.path L1 b0 b1) := hty.tyConv hR.2
  have ht : HasTy S k .one [] (.papp (.hcomp T φ u a0) .zero) (L1.dinst .zero) := HasTy.papp hpT trivial
  have ht' : HasTy S k .one [] b0 (L1.dinst .zero) := (RE2.typed hb0).1
  refine RE2.expandH hW hAA ht ht' fun k' ρ => ?_
  obtain ⟨L3, d0, d1, L3', d0', d1', h3, -, hLL3, -, -⟩ := hP.whnf k' ρ
  have h3' : RedT S k' (T.isub ((ISub.id k).comp ρ)) (.path L3 d0 d1) := by rw [ISub.id_comp]; exact h3
  have cohT : RT2 S k' ((L1.dinst .zero).isub ρ) (L3.dinst .zero) := by
    rw [isub_dinst]; exact hP.coh k (ISub.id k) k' ρ _ _ _ _ _ _ hR0 h3' .zero trivial
  have hX3 := hP.tc k' ρ _ _ _ h3 .zero trivial
  have hXY : TyCode k' (semK S k' ((L1.dinst .zero).isub ρ)) := RT2.tyCode_l hW cohT hX3
  have hYY : RT2 S k' ((L1.dinst .zero).isub ρ) ((L1.dinst .zero).isub ρ) := RT2.isub hW hX0 hAA ρ
  have hA3 := hLL3 .zero .zero trivial trivial (I_eq_refl _)
  -- the endpoint of the restriction, against the restricted endpoint
  have eb : RE2 S k' ((L1.dinst .zero).isub ρ) d0 (b0.isub ρ) :=
    RE2.conv' hW cohT (RE2.symm hW hA3 (hP.endCoh0 hW ha0 hR0 h3')) hXY
  have hρ : HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (T.isub ρ) :=
    HasTy.isubS hW hty ρ
  have tyE : TyEq S k' (L3.dinst .zero) ((L1.dinst .zero).isub ρ) := TyEq.symm (Comp2_ty_base cohT).2.2.2.2.2
  -- the point of an element related to something, against the endpoint
  have pE : ∀ k4 (v : ISub k4 k') f g, RE2 S k4 (T.isub (ρ.comp v)) f g →
      RE2 S k4 ((L1.dinst .zero).isub (ρ.comp v)) (.papp f .zero) (b0.isub (ρ.comp v)) := by
    intro k4 v f g h
    obtain ⟨L5, e0, e1, L5', e0', e1', h5, -, hLL5, -, -⟩ := hP.whnf k4 (ρ.comp v)
    have h5' : RedT S k4 (T.isub ((ISub.id k).comp (ρ.comp v))) (.path L5 e0 e1) := by rw [ISub.id_comp]; exact h5
    have coh5 : RT2 S k4 ((L1.dinst .zero).isub (ρ.comp v)) (L5.dinst .zero) := by
      rw [isub_dinst]; exact hP.coh k (ISub.id k) k4 (ρ.comp v) _ _ _ _ _ _ hR0 h5' .zero trivial
    have hA5 := hLL5 .zero .zero trivial trivial (I_eq_refl _)
    have el := (hP.elim k4 (ρ.comp v) _ _ _ _ _ h5 (reflL k4 _ h)).2.1
    have ec := RE2.symm hW hA5 (hP.endCoh0 hW ha0 hR0 h5')
    have hX5 := RT2.tyCode_l hW coh5 (hP.tc k4 _ _ _ _ h5 .zero trivial)
    exact RE2.conv' hW coh5 (RE2.trans hW hA5 el ec) hX5
  by_cases hf : I.Entails .one (φ.subst ρ.τ)
  · obtain ⟨a, b⟩ := papp_hcomp_face_path hW hf (show I.Scoped k' I.zero from trivial) hρ h3.2
    refine ⟨_, a, b.tyConv tyE, ?_⟩
    have ht1 := htube k' ρ .one .one trivial trivial (I_eq_refl _) ((holds_iff_entails (I.scoped_subst hφs ρ.sc)).2 hf)
    rw [← ISub.comp_id ρ] at ht1
    have := pE k' (ISub.id k') _ _ ht1
    rwa [ISub.comp_id] at this
  · obtain ⟨a, b⟩ := papp_hcomp_path hW hf (show I.Scoped k' I.zero from trivial) hρ h3
    refine ⟨_, a, b.tyConv tyE, ?_⟩
    have htyH := (HasTy.eqR b).tyConv tyE
    have hface : I.Entails .one (I.or (φ.subst ρ.τ) (.or (.neg .zero) .zero)) :=
      ent_trans (show I.Entails .one (I.neg .zero) by decide) (ent_trans (ent_or_left _ _) (ent_or_right _ _))
    have hst := stable_hcompFace hW hface htyH
    have htyS := HasTy.eqR (EqTm.hcompFace hface htyH)
    refine RE2.expandL hW hYY htyH (HasTy.isubS hW ht' ρ) hst ?_
    rw [sysP_dinst] at htyS ⊢
    refine RE2.symm hW hYY (RE2_sys_r hW (I.scoped_subst hφs ρ.sc) trivial
      (ent_trans hface (ent_refl _)) hYY htyS (HasTy.isubS hW ht' ρ) (fun k4 v h => ?_) (fun k4 v h => ?_)
      (fun k4 v h => ?_))
    · -- the tube's point, where the face holds
      have hv := ent_comp_inv h
      have := pE k4 v _ _ (htube k4 (ρ.comp v) .one .one trivial trivial (I_eq_refl _)
        ((holds_iff_entails (I.scoped_subst hφs (ρ.comp v).sc)).2 hv))
      rw [Tm.isub_isub, Tm.isub_isub]
      refine RE2.symm hW (RT2.isub hW hX0 hAA (ρ.comp v)) ?_
      show RE2 S k4 _ (Tm.papp (((u.isub ρ.up).dinst .one).isub v) .zero) _
      rw [up_dinst_one_isub]
      exact this
    · -- the endpoint
      rw [Tm.isub_isub, Tm.isub_isub]
      obtain ⟨L5, e0, e1, L5', e0', e1', h5, -, hLL5, -, -⟩ := hP.whnf k4 (ρ.comp v)
      have h5' : RedT S k4 (T.isub ((ISub.id k).comp (ρ.comp v))) (.path L5 e0 e1) := by
        rw [ISub.id_comp]; exact h5
      have coh5 : RT2 S k4 ((L1.dinst .zero).isub (ρ.comp v)) (L5.dinst .zero) := by
        rw [isub_dinst]; exact hP.coh k (ISub.id k) k4 (ρ.comp v) _ _ _ _ _ _ hR0 h5' .zero trivial
      have hA5 := hLL5 .zero .zero trivial trivial (I_eq_refl _)
      have hX5 := RT2.tyCode_l hW coh5 (hP.tc k4 _ _ _ _ h5 .zero trivial)
      have x1 := hP.endCoh0 hW ha0 hR0 h5'
      have x2 := hP.endCoh0 hW ha0 h3 h5
      exact RE2.conv' hW coh5 (RE2.trans hW hA5 x1 (RE2.symm hW hA5 x2)) hX5
    · exact (not_ent_zero h).elim

/-- The endpoints of the normal forms of the restrictions of a path type are coherent (given an element). -/
theorem PathStr.endCoh1 {T T' a a' : Tm} (hP : PathStr S k T T') (ha : RE2 S k T a a') {k1 : ℕ} {ρ1 : ISub k1 k}
    {L c0 c1 : Tm} (h1 : RedT S k1 (T.isub ρ1) (.path L c0 c1)) {k2 : ℕ} {ρ2 : ISub k2 k1} {L' c0' c1' : Tm}
    (h2 : RedT S k2 (T.isub (ρ1.comp ρ2)) (.path L' c0' c1')) :
    RE2 S k2 (L'.dinst .one) (c1.isub ρ2) c1' := by
  have e1 := (hP.elim k1 ρ1 _ _ _ _ _ h1 (RE2.isub hW ha ρ1)).2.2
  have e2 := RE2.isub hW e1 ρ2
  have c := hP.coh k1 ρ1 k2 ρ2 _ _ _ _ _ _ h1 h2 .one trivial
  rw [isub_dinst] at e2
  have e2' := RE2.conv hW c e2
  have ea : (Tm.papp (a.isub ρ1) .one).isub ρ2 = .papp (a.isub (ρ1.comp ρ2)) .one := by
    show Tm.papp ((a.isub ρ1).isub ρ2) _ = _; rw [Tm.isub_isub]; rfl
  rw [ea] at e2'
  have e3 := (hP.elim k2 (ρ1.comp ρ2) _ _ _ _ _ h2 (RE2.isub hW ha (ρ1.comp ρ2))).2.2
  obtain ⟨L4, d0, d1, L4', d0', d1', h4, -, hLL, -, -⟩ := hP.whnf k2 (ρ1.comp ρ2)
  obtain rfl : L4 = L' := by have := RedW.unique h4.1 h2.1; injection this
  have hA := hLL .one .one trivial trivial (I_eq_refl _)
  exact RE2.trans hW hA (RE2.symm hW hA e2') e3

/-- The endpoint of a composition in a path type. -/
theorem hcomp_path_end1 {T T' : Tm} (hP : PathStr S k T T') (hTT : RT2 S k T T') {φ : I} {u u' a0 a0' : Tm}
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (htube : Tube2 S k T φ u u') (ha0 : RE2 S k T a0 a0')
    {L1 b0 b1 : Tm} (hR : RedT S k T (.path L1 b0 b1)) :
    RE2 S k (L1.dinst .one) (.papp (.hcomp T φ u a0) .one) b1 := by
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hTK : IsTyK S k T := isTyK_of_ty hW hty
  have hTc : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTK)
  have hXT : TyCode k (semK S k T) := tyCode_of_ty hW hty
  have hR0 : RedT S k (T.isub (ISub.id k)) (.path L1 b0 b1) := by rw [hTc]; exact hR
  have hTρ : ∀ k' (ρ : ISub k' k), RT2 S k' (T.isub ρ) (T'.isub ρ) := fun k' ρ => RT2.isub hW hXT hTT ρ
  have reflL : ∀ k' (ρ : ISub k' k) {f g : Tm}, RE2 S k' (T.isub ρ) f g → RE2 S k' (T.isub ρ) f f :=
    fun k' ρ f g h => RE2.trans hW (hTρ k' ρ) h (RE2.symm hW (hTρ k' ρ) h)
  obtain ⟨L2, c0, c1, L2', c0', c1', h2, -, hLL, hb0, hb1⟩ := hP.whnf k (ISub.id k)
  have e := RedW.unique h2.1 hR0.1
  injection e with eL e0 e1
  subst L2 c0 c1
  have hX0 : TyCode k (semK S k (L1.dinst .one)) := hP.tc k (ISub.id k) _ _ _ hR0 .one trivial
  have hAA : RT2 S k (L1.dinst .one) (L1.dinst .one) := RT2.refl hW hX0 (hLL .one .one trivial trivial (I_eq_refl _))
  have hpT : HasTy S k .one [] (.hcomp T φ u a0) (.path L1 b0 b1) := hty.tyConv hR.2
  have ht : HasTy S k .one [] (.papp (.hcomp T φ u a0) .one) (L1.dinst .one) := HasTy.papp hpT trivial
  have ht' : HasTy S k .one [] b1 (L1.dinst .one) := (RE2.typed hb1).1
  refine RE2.expandH hW hAA ht ht' fun k' ρ => ?_
  obtain ⟨L3, d0, d1, L3', d0', d1', h3, -, hLL3, -, -⟩ := hP.whnf k' ρ
  have h3' : RedT S k' (T.isub ((ISub.id k).comp ρ)) (.path L3 d0 d1) := by rw [ISub.id_comp]; exact h3
  have cohT : RT2 S k' ((L1.dinst .one).isub ρ) (L3.dinst .one) := by
    rw [isub_dinst]; exact hP.coh k (ISub.id k) k' ρ _ _ _ _ _ _ hR0 h3' .one trivial
  have hX3 := hP.tc k' ρ _ _ _ h3 .one trivial
  have hXY : TyCode k' (semK S k' ((L1.dinst .one).isub ρ)) := RT2.tyCode_l hW cohT hX3
  have hYY : RT2 S k' ((L1.dinst .one).isub ρ) ((L1.dinst .one).isub ρ) := RT2.isub hW hX0 hAA ρ
  have hA3 := hLL3 .one .one trivial trivial (I_eq_refl _)
  -- the endpoint of the restriction, against the restricted endpoint
  have eb : RE2 S k' ((L1.dinst .one).isub ρ) d1 (b1.isub ρ) :=
    RE2.conv' hW cohT (RE2.symm hW hA3 (hP.endCoh1 hW ha0 hR0 h3')) hXY
  have hρ : HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (T.isub ρ) :=
    HasTy.isubS hW hty ρ
  have tyE : TyEq S k' (L3.dinst .one) ((L1.dinst .one).isub ρ) := TyEq.symm (Comp2_ty_base cohT).2.2.2.2.2
  -- the point of an element related to something, against the endpoint
  have pE : ∀ k4 (v : ISub k4 k') f g, RE2 S k4 (T.isub (ρ.comp v)) f g →
      RE2 S k4 ((L1.dinst .one).isub (ρ.comp v)) (.papp f .one) (b1.isub (ρ.comp v)) := by
    intro k4 v f g h
    obtain ⟨L5, e0, e1, L5', e0', e1', h5, -, hLL5, -, -⟩ := hP.whnf k4 (ρ.comp v)
    have h5' : RedT S k4 (T.isub ((ISub.id k).comp (ρ.comp v))) (.path L5 e0 e1) := by rw [ISub.id_comp]; exact h5
    have coh5 : RT2 S k4 ((L1.dinst .one).isub (ρ.comp v)) (L5.dinst .one) := by
      rw [isub_dinst]; exact hP.coh k (ISub.id k) k4 (ρ.comp v) _ _ _ _ _ _ hR0 h5' .one trivial
    have hA5 := hLL5 .one .one trivial trivial (I_eq_refl _)
    have el := (hP.elim k4 (ρ.comp v) _ _ _ _ _ h5 (reflL k4 _ h)).2.2
    have ec := RE2.symm hW hA5 (hP.endCoh1 hW ha0 hR0 h5')
    have hX5 := RT2.tyCode_l hW coh5 (hP.tc k4 _ _ _ _ h5 .one trivial)
    exact RE2.conv' hW coh5 (RE2.trans hW hA5 el ec) hX5
  by_cases hf : I.Entails .one (φ.subst ρ.τ)
  · obtain ⟨a, b⟩ := papp_hcomp_face_path hW hf (show I.Scoped k' I.one from trivial) hρ h3.2
    refine ⟨_, a, b.tyConv tyE, ?_⟩
    have ht1 := htube k' ρ .one .one trivial trivial (I_eq_refl _) ((holds_iff_entails (I.scoped_subst hφs ρ.sc)).2 hf)
    rw [← ISub.comp_id ρ] at ht1
    have := pE k' (ISub.id k') _ _ ht1
    rwa [ISub.comp_id] at this
  · obtain ⟨a, b⟩ := papp_hcomp_path hW hf (show I.Scoped k' I.one from trivial) hρ h3
    refine ⟨_, a, b.tyConv tyE, ?_⟩
    have htyH := (HasTy.eqR b).tyConv tyE
    have hface : I.Entails .one (I.or (φ.subst ρ.τ) (.or (.neg .one) .one)) :=
      ent_trans (show I.Entails .one I.one by decide) (ent_trans (ent_or_right _ _) (ent_or_right _ _))
    have hst := stable_hcompFace hW hface htyH
    have htyS := HasTy.eqR (EqTm.hcompFace hface htyH)
    refine RE2.expandL hW hYY htyH (HasTy.isubS hW ht' ρ) hst ?_
    rw [sysP_dinst] at htyS ⊢
    refine RE2.symm hW hYY (RE2_sys_r hW (I.scoped_subst hφs ρ.sc) trivial
      (ent_trans hface (ent_refl _)) hYY htyS (HasTy.isubS hW ht' ρ) (fun k4 v h => ?_) (fun k4 v h => ?_)
      (fun k4 v h => ?_))
    · -- the tube's point, where the face holds
      have hv := ent_comp_inv h
      have := pE k4 v _ _ (htube k4 (ρ.comp v) .one .one trivial trivial (I_eq_refl _)
        ((holds_iff_entails (I.scoped_subst hφs (ρ.comp v).sc)).2 hv))
      rw [Tm.isub_isub, Tm.isub_isub]
      refine RE2.symm hW (RT2.isub hW hX0 hAA (ρ.comp v)) ?_
      show RE2 S k4 _ (Tm.papp (((u.isub ρ.up).dinst .one).isub v) .one) _
      rw [up_dinst_one_isub]
      exact this
    · exact (not_ent_zero h).elim
    · -- the endpoint
      rw [Tm.isub_isub, Tm.isub_isub]
      obtain ⟨L5, e0, e1, L5', e0', e1', h5, -, hLL5, -, -⟩ := hP.whnf k4 (ρ.comp v)
      have h5' : RedT S k4 (T.isub ((ISub.id k).comp (ρ.comp v))) (.path L5 e0 e1) := by
        rw [ISub.id_comp]; exact h5
      have coh5 : RT2 S k4 ((L1.dinst .one).isub (ρ.comp v)) (L5.dinst .one) := by
        rw [isub_dinst]; exact hP.coh k (ISub.id k) k4 (ρ.comp v) _ _ _ _ _ _ hR0 h5' .one trivial
      have hA5 := hLL5 .one .one trivial trivial (I_eq_refl _)
      have hX5 := RT2.tyCode_l hW coh5 (hP.tc k4 _ _ _ _ h5 .one trivial)
      have x1 := hP.endCoh1 hW ha0 hR0 h5'
      have x2 := hP.endCoh1 hW ha0 h3 h5
      exact RE2.conv' hW coh5 (RE2.trans hW hA5 x1 (RE2.symm hW hA5 x2)) hX5

/-- Composition at a pair of related types whose normal forms are path types. -/
theorem kanH2_path {T T' L a b : Tm} {l : ℕ} (hTT : RT2 S k T T') (hR : RedT S k T (.path L a b))
    (hpath : HasTy S k .one [] (.path L a b) (.univ l))
    (hIH : ∀ k' (ρ : ISub k' k) L1 b0 b1, RedT S k' (T.isub ρ) (.path L1 b0 b1) → ∀ (s : I), s.Scoped k' →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' ((L1.dinst s).isub ρ') X' → KanH2 S k'' ((L1.dinst s).isub ρ') X') :
    KanH2 S k T T' := by
  have hP := PathStr_of hW hTT hR hpath
  intro φ φ' u u' a0 a0' hty hty' heq h12 h21 htube ha0
  have hXT : TyCode k (semK S k T) := tyCode_of_ty hW hty
  refine RE2_pathW_intro hW (RT2.refl hW hXT hTT) hR hpath ⟨hty, hty', heq⟩ fun k' ρ L1 b0 b1 h1 => ?_
  have hPρ := hP.isub hW ρ
  have hTTρ := RT2.isub hW hXT hTT ρ
  have hIHρ : ∀ k1 (ρ1 : ISub k1 k') L3 c0 c1, RedT S k1 ((T.isub ρ).isub ρ1) (.path L3 c0 c1) → ∀ (s : I),
      s.Scoped k1 → ∀ k2 (ρ2 : ISub k2 k1) X', RT2 S k2 ((L3.dinst s).isub ρ2) X' →
      KanH2 S k2 ((L3.dinst s).isub ρ2) X' := by
    intro k1 ρ1 L3 c0 c1 h3 s hs k2 ρ2 X' hX'
    rw [Tm.isub_isub] at h3
    exact hIH k1 (ρ.comp ρ1) L3 c0 c1 h3 s hs k2 ρ2 X' hX'
  exact ⟨fun r r' hr hr' hE => kanH2_path_core hW hPρ hTTρ hIHρ (HasTy.isubS hW hty ρ) (HasTy.isubS hW hty' ρ)
      (EqTm.isubS hW heq ρ) (ent_subst h12 ρ.τ) (ent_subst h21 ρ.τ) (htube.isub ρ) (RE2.isub hW ha0 ρ) h1 hr hr' hE,
    hcomp_path_end0 hW hPρ hTTρ (HasTy.isubS hW hty ρ) (htube.isub ρ) (RE2.isub hW ha0 ρ) h1,
    hcomp_path_end1 hW hPρ hTTρ (HasTy.isubS hW hty ρ) (htube.isub ρ) (RE2.isub hW ha0 ρ) h1⟩

end

end Model.Whnf
