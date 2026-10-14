import Model.Whnf.Data2
import Model.Whnf.Pack2
import Model.Whnf.GlueAux2
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
      RedT S k' (T.isub σ) (.pi A1 B1) ∧ RedT S k' (T'.isub σ) (.pi A1' B1') ∧
      (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1' ∧
        ∀ a a', (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
          (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a) (B1'.inst a')) ↔
      piT (S := S) D C T T' := by
    intro T T'; simp only [piT, D, C, ISub.hom_id]
  refine ⟨fun {T T'} hT => ⟨base_symm hT.1, (eT T' T).2 (pi_symTy D C hD hC hCa ((eT T T').1 hT.2.1)), hT.2.2.2.1, hT.2.2.1, hT.2.2.2.2.2, hT.2.2.2.2.1⟩,
    fun {T T' T''} hT hT' => ⟨base_trans hW hT.1 hT'.1,
      (eT T T'').2 (pi_transTy D C hD hC hCa ((eT T T').1 hT.2.1) ((eT T' T'').1 hT'.2.1)), hT.2.2.1, hT'.2.2.2.1, hT.2.2.2.2.1, hT'.2.2.2.2.2⟩,
    fun {T T' t t'} hT ht => ?_, fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    exact ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, pi_symEl D C hD hC hCa ((eT T T').1 hT.2.1) hpi⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    obtain ⟨he', -, hpi'⟩ := ht'
    exact ⟨he.trans he', hmem, pi_transEl D C hD hC hCa ((eT T T').1 hT.2.1) hpi hpi'⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    exact ⟨he.conv hT.1.2.2.2.2, hmem, pi_conv D C hD hC ((eT T T').1 hT.2.1) hT.1.2.2.2.2 hpi⟩

/-- The PER properties at a `Σ` code. -/
theorem per2_sigmaC {A B : V} (hA : A ≠ ∅) (ihA : PER2 S m A)
    (ihB : ∀ k (f : Hom k m), ∀ a ∈ El A f, PER2 S k (apZ (dat B k f) a)) : PER2 S m (sigmaC m A B) := by
  intro k f
  rw [Comp2_sigmaC A B hA]
  let D : (k' : ℕ) → ISub k' k → Pack2 := fun k' σ => Comp2 S A m k' (f.comp σ.hom)
  let C : (k' : ℕ) → ISub k' k → Tm → (k'' : ℕ) → ISub k'' k' → Pack2 := fun k' σ a k'' σ' =>
    Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k'' σ'.hom
  have hD : ∀ k' (σ : ISub k' k), PERP (D k' σ) := fun k' σ => ihA k' _
  have hC : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → PERP (C k' σ a k' (ISub.id k')) :=
    fun k' σ _ _ _ ha => ihB k' _ _ (fib_mem ha) k' _
  have hCa : ∀ k' (σ : ISub k' k) X a a', (D k' σ).el X a a' → C k' σ a = C k' σ a' := by
    intro k' σ _ a a' ha; simp only [C, fib_code hW ha]
  have eT : ∀ T T', (∀ k' (σ : ISub k' k), ∃ A1 B1 A1' B1',
      RedT S k' (T.isub σ) (.sigma A1 B1) ∧ RedT S k' (T'.isub σ) (.sigma A1' B1') ∧
      (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1' ∧
        ∀ a a', (Comp2 S A m k' (f.comp σ.hom)).el A1 a a' →
          (Comp2 S (apZ (dat B k' (f.comp σ.hom)) (semK S k' a)) k' k' (Hom.id k')).ty (B1.inst a) (B1'.inst a')) ↔
      sigT (S := S) D C T T' := by
    intro T T'; simp only [sigT, D, C, ISub.hom_id]
  refine ⟨fun {T T'} hT => ⟨base_symm hT.1, (eT T' T).2 (sig_symTy D C hD hC hCa ((eT T T').1 hT.2.1)), hT.2.2.2.1, hT.2.2.1, hT.2.2.2.2.2, hT.2.2.2.2.1⟩,
    fun {T T' T''} hT hT' => ⟨base_trans hW hT.1 hT'.1,
      (eT T T'').2 (sig_transTy D C hD hC hCa ((eT T T').1 hT.2.1) ((eT T' T'').1 hT'.2.1)), hT.2.2.1, hT'.2.2.2.1, hT.2.2.2.2.1, hT'.2.2.2.2.2⟩,
    fun {T T' t t'} hT ht => ?_, fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    exact ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, sig_symEl D C hD hC hCa ((eT T T').1 hT.2.1) hpi⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    obtain ⟨he', -, hpi'⟩ := ht'
    exact ⟨he.trans he', hmem, sig_transEl D C hD hC hCa ((eT T T').1 hT.2.1) hpi hpi'⟩
  · obtain ⟨he, hmem, hpi⟩ := ht
    exact ⟨he.conv hT.1.2.2.2.2, hmem, sig_conv D C hD hC ((eT T T').1 hT.2.1) hT.1.2.2.2.2 hpi⟩

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
  let Lp : (k' : ℕ) → ISub k' (k + 1) → Pack2 := fun k' σ => Comp2 S L (m + 1) k' ((Hom.lift f).comp σ.hom)
  have hLp : ∀ k' (σ : ISub k' (k + 1)), PERP (Lp k' σ) := fun k' σ => ihL k' _
  have hLt : ∀ k' (σ : ISub k' k) (r r' : I) (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
      Lp k' (ISub.cons r hr σ) = Lp k' (ISub.cons r' hr' σ) := fun k' σ r r' hr hr' he => by
    simp only [Lp, ISub.hom_cons_eq σ hr hr' he]
  refine ⟨fun {T T'} hT => ⟨base_symm hT.1, path_symTy Lp hLp hLt hT.2.1, hT.2.2.2, hT.2.2.1⟩,
    fun {T T' T''} hT hT' => ⟨base_trans hW hT.1 hT'.1, path_transTy Lp hLp hLt hT.2.1 hT'.2.1, hT.2.2.1, hT'.2.2.2⟩,
    fun {T T' t t'} hT ht => ?_, fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨he, hmem, hp⟩ := ht
    exact ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, path_symEl Lp hLp hLt hT.2.1 hp⟩
  · obtain ⟨he, hmem, hp⟩ := ht
    obtain ⟨he', -, hp'⟩ := ht'
    exact ⟨he.trans he', hmem, path_transEl Lp hLp hLt hT.2.1 hp hp'⟩
  · obtain ⟨he, hmem, hp⟩ := ht
    exact ⟨he.conv hT.1.2.2.2.2, hmem, path_conv Lp hLp hLt hT.2.1 hT.1.2.2.2.2 hp⟩

/-- The PER properties at a code `(i : I) → L`. -/
theorem per2_ipiC {L : V} (hLne : L ≠ ∅) (hL : KR2 S (m + 1) L) (ihL : PER2 S (m + 1) L) :
    PER2 S m (ipiC m L) := by
  intro k f
  rw [Comp2_ipiC L hLne]
  have hLe : ∀ {k'} (σ : ISub k' k) {r r' : I} (hr : r.Scoped k') (hr' : r'.Scoped k'), I.Eq r r' →
      Comp2 S L (m + 1) k' ((Hom.lift f).comp (ISub.cons r hr σ).hom) =
        Comp2 S L (m + 1) k' ((Hom.lift f).comp (ISub.cons r' hr' σ).hom) := fun σ r r' hr hr' he => by
    rw [ISub.hom_cons_eq σ hr hr' he]
  have rf : ∀ r : I, I.Eq r r := fun _ _ => rfl
  have sy : ∀ {r r' : I}, I.Eq r r' → I.Eq r' r := fun he ρ => (he ρ).symm
  refine ⟨fun {T T'} hT => ?_, fun {T T' T''} hT hT' => ?_, fun {T T' t t'} hT ht => ?_,
    fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨hb, hall, hc, hc'⟩ := hT
    refine ⟨base_symm hb, fun k' σ => ?_, hc', hc⟩
    obtain ⟨L1, L1', h1, h2, h3, hrr⟩ := hall k' σ
    refine ⟨L1', L1, h2, h1, (ihL _ _).symTy h3, fun r r' hr hr' he => ?_⟩
    have := hrr r' r hr' hr (sy he)
    rw [hLe σ hr' hr (sy he)] at this
    exact (ihL _ _).symTy this
  · obtain ⟨hb, hall, hc, -⟩ := hT
    obtain ⟨hb', hall', -, hc''⟩ := hT'
    refine ⟨base_trans hW hb hb', fun k' σ => ?_, hc, hc''⟩
    obtain ⟨L1, L1', h1, h2, h3, hrr⟩ := hall k' σ
    obtain ⟨L2, L2', h1', h2', h3', hrr'⟩ := hall' k' σ
    obtain rfl : L1' = L2 := by have := RedW.unique h2.1 h1'.1; injection this
    refine ⟨L1, L2', h1, h2', (ihL _ _).transTy h3 h3', fun r r' hr hr' he => ?_⟩
    have x := hrr r r' hr hr' he
    have y := hrr' r' r' hr' hr' (rf r')
    rw [← hLe σ hr hr' he] at y
    exact (ihL _ _).transTy x y
  · obtain ⟨he, hmem, -, hall⟩ := ht
    refine ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, he.symm, fun k'' σ' => ?_⟩
    obtain ⟨L1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, L1', hrx, -, -, hrr⟩ := hT.2.1 k'' σ'
    obtain rfl : L1x = L1 := by have := RedW.unique hrx.1 hr.1; injection this
    simp only [ISub.id_comp] at hel ⊢
    refine ⟨L1x, hr, fun r r' hr1 hr1' hE => ?_⟩
    have x := hel r' r hr1' hr1 (sy hE)
    have y := (ihL _ _).symEl (hrr r' r' hr1' hr1' (rf r')) x
    have t1 := hrr r' r hr1' hr1 (sy hE)
    have t2 := hrr r r hr1 hr1 (rf r)
    rw [hLe σ' hr1 hr1' hE] at t2 ⊢
    exact (ihL _ _).conv ((ihL _ _).transTy t1 ((ihL _ _).symTy t2)) y
  · obtain ⟨he, hmem, -, hall⟩ := ht
    obtain ⟨he', -, -, hall'⟩ := ht'
    refine ⟨he.trans he', hmem, he.trans he', fun k'' σ' => ?_⟩
    obtain ⟨L1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, hrx, hel'⟩ := hall' k'' σ'
    obtain rfl : L1x = L1 := by have := RedW.unique hrx.1 hr.1; injection this
    obtain ⟨L1y, L1', hry, -, -, hrr⟩ := hT.2.1 k'' σ'
    obtain rfl : L1y = L1x := by have := RedW.unique hry.1 hr.1; injection this
    simp only [ISub.id_comp] at hel hel' ⊢
    refine ⟨L1y, hr, fun r r' hr1 hr1' hE => ?_⟩
    have x := hel r r' hr1 hr1' hE
    have y := hel' r' r' hr1' hr1' (rf r')
    have t1 := hrr r' r' hr1' hr1' (rf r')
    have t2 := hrr r r' hr1 hr1' hE
    rw [← hLe σ' hr1 hr1' hE] at y t1
    have y' := (ihL _ _).conv ((ihL _ _).transTy t1 ((ihL _ _).symTy t2)) y
    exact (ihL _ _).transEl t2 x y'
  · obtain ⟨he, hmem, -, hall⟩ := ht
    have hTT := hT.1.2.2.2.2
    refine ⟨he.conv hTT, hmem, he.conv hTT, fun k'' σ' => ?_⟩
    obtain ⟨L1, hr, hel⟩ := hall k'' σ'
    obtain ⟨L1x, L1', hrx, hr2, -, hrr⟩ := hT.2.1 k'' σ'
    obtain rfl : L1x = L1 := by have := RedW.unique hrx.1 hr.1; injection this
    simp only [ISub.id_comp] at hel ⊢
    exact ⟨L1', hr2, fun r r' hr1 hr1' hE => (ihL _ _).conv (hrr r r hr1 hr1 (rf r)) (hel r r' hr1 hr1' hE)⟩

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
  · obtain ⟨he, hmem, hm, hty, hK⟩ := ht
    have es := semK_eq hW he.2.2
    have P := ih k _ (ZFSet.mem_sep.1 hm).2 k (Hom.id k)
    refine ⟨he.symm, by rw [← es]; exact hmem, by rw [← es]; exact hm, ?_, by rw [← es]; exact hK⟩
    rw [← es]; exact P.symTy hty
  · obtain ⟨he, hmem, hm, hty, hK⟩ := ht
    obtain ⟨he', -, -, hty', -⟩ := ht'
    have es := semK_eq hW he.2.2
    have P := ih k _ (ZFSet.mem_sep.1 hm).2 k (Hom.id k)
    rw [← es] at hty'
    exact ⟨he.trans he', hmem, hm, P.transTy hty hty', hK⟩
  · obtain ⟨he, hmem, hm, hty, hK⟩ := ht
    exact ⟨he.conv hT.1.2.2.2.2, hmem, hm, hty, hK⟩

/-- Related equivalences, applied to related elements of the domain. -/
theorem equivF_app {n : ℕ} {TP AP : (k' : ℕ) → ISub k' n → Pack2} {T A e e' x x' : Tm}
    (hcT : T.closedB 0 n = true) (hcA : A.closedB 0 n = true)
    (h : (equivF S TP AP n (ISub.id n)).el (Tm.equiv T A) e e') (hx : (TP n (ISub.id n)).el T x x') :
    (AP n (ISub.id n)).el A (.app (.fst e) x) (.app (.fst e') x') := by
  obtain ⟨hE, hall⟩ := h
  have hcE := closed_of_isTyK hW (isTyK_of_ty hW hE.1)
  have hce := closed_of_ty hW hE.1
  have hce' := closed_of_ty hW hE.2.1
  obtain ⟨A1, B1, h0, hfst, -⟩ := hall n (ISub.id n)
  rw [isub_id_of_closed hcE] at h0
  have e0 := RedW.unique (redW_self (by simp [Tm.equiv, step])) h0.1
  simp only [Tm.equiv, Tm.sigma.injEq] at e0
  obtain ⟨rfl, rfl⟩ := e0
  simp only [ISub.id_comp] at hfst
  rw [isub_id_of_closed hce, isub_id_of_closed hce'] at hfst
  have := app_rel hfst (ISub.id n) (by rwa [isub_id_of_closed hcT])
  rwa [isub_id_of_closed (show (Tm.fst e).closedB 0 n = true from hce),
    isub_id_of_closed (show (Tm.fst e').closedB 0 n = true from hce'), isub_id_of_closed hcA] at this

section glueLoc
variable {A Tp : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
  (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
  (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
  (ihA : PER2 S m A) (krA : KR2 S m A)
  (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → PER2 S k (dat Tp k f))
  (krT : ∀ k (f : Hom k m), (φ.restr f).holds → KR2 S k (dat Tp k f)) (f : Hom k m)
include ihA krA ihT krT

/-- The relation of the equivalences, between two decompositions. -/
theorem glue_equivTy {k' : ℕ} (σ : ISub k' k) {X X' A1 T1 e1 A1' T1' e1' : Tm} {φ1 φ1' : I}
    (hX : IsTyK S k' X) (hX' : IsTyK S k' X')
    (r1 : RedT S k' X (.glue A1 φ1 T1 e1)) (r1' : RedT S k' X' (.glue A1' φ1' T1' e1'))
    (f1 : (ival (idEnv k') φ1).face = φ.restr (f.comp σ.hom)) (f1' : (ival (idEnv k') φ1').face = φ.restr (f.comp σ.hom))
    (hAA : (Comp2 S A m k' (f.comp σ.hom)).ty A1 A1')
    {k'' : ℕ} (σ' : ISub k'' k') (hh' : (φ.restr (f.comp (σ.comp σ').hom)).holds)
    (hTT : (Comp2 S (dat Tp k'' (f.comp (σ.comp σ').hom)) k'' k'' (Hom.id k'')).ty (T1.isub σ') (T1'.isub σ')) :
    (equivF S (fun k3 σ3 => Comp2 S (dat Tp k'' (f.comp (σ.comp σ').hom)) k'' k3 σ3.hom)
      (fun k3 σ3 => Comp2 S A m k3 (f.comp ((σ.comp σ').comp σ3).hom)) k'' (ISub.id k'')).ty
      (Tm.equiv (T1.isub σ') (A1.isub σ')) (Tm.equiv (T1'.isub σ') (A1'.isub σ')) := by
  have FT := famOK_comp2_id (ihT k'' _ hh') (krT k'' _ hh')
  have FA := famOK_comp2 ihA krA f (σ.comp σ')
  obtain ⟨l1, hA1, s1, hT1, -⟩ := glue_parts hW r1 hX
  obtain ⟨l2, hA1', s1', hT1', -⟩ := glue_parts hW r1' hX'
  have hh1 : (ival (idEnv k'') (φ1.subst σ'.τ)).holds :=
    holds_of_face f1 σ' (by rwa [Cof.restr_restr, ISub.comp_hom])
  have hTT' : (Comp2 S (dat Tp k'' (f.comp (σ.comp σ').hom)) k'' k'' (ISub.id k'').hom).ty (T1.isub σ')
      (T1'.isub σ') := by rw [ISub.hom_id]; exact hTT
  have hAA' := (krA k' (f.comp σ.hom) k'' σ' A1 A1' A1 A1).1 hAA
  have hAA'' : (Comp2 S A m k'' (f.comp ((σ.comp σ').comp (ISub.id k'')).hom)).ty (A1.isub σ') (A1'.isub σ') := by
    rw [ISub.comp_id, ← ISub.comp_hom]; exact hAA'
  have eT := eqTop hW (Comp2_ty_base hTT).2.2.2.2.2 (face_ty hW s1 hT1 σ' hh1)
  have eA := eqTop hW (Comp2_ty_base hAA').2.2.2.2.2 (HasTy.isubS hW hA1 σ')
  exact equivF_ty hW FT FA eT eA hTT' hAA''

theorem glueLocT_symm {k' : ℕ} (σ : ISub k' k) {Y Z : Tm} (hY : IsTyK S k' Y) (hZ : IsTyK S k' Z)
    (h : glueLocT S A Tp φ f k' σ Y Z) : glueLocT S A Tp φ f k' σ Z Y := by
  unfold glueLocT at h ⊢
  split_ifs at h ⊢ with hh
  · exact (ihT k' _ hh k' (Hom.id k')).symTy h
  obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', r1, r1', s1, s1', f1, f1', hAA, hrest⟩ := h
  refine ⟨A1', φ1', T1', e1', A1, φ1, T1, e1, r1', r1, s1', s1, f1', f1, (ihA k' _).symTy hAA,
    fun k'' σ' hh' => ?_⟩
  obtain ⟨hTT, hee⟩ := hrest k'' σ' hh'
  have hEq := glue_equivTy hW ihA krA ihT krT f σ hY hZ r1 r1' f1 f1' hAA σ' hh' hTT
  have P := (equivF_ok hW _ _ (famOK_comp2_id (ihT k'' _ hh') (krT k'' _ hh'))
    (famOK_comp2 ihA krA f (σ.comp σ'))).per k'' (ISub.id k'')
  exact ⟨(ihT k'' _ hh' k'' (Hom.id k'')).symTy hTT, P.conv hEq (P.symEl hEq hee)⟩

theorem glueLocT_trans {k' : ℕ} (σ : ISub k' k) {Y Z W : Tm} (hY : IsTyK S k' Y) (hZ : IsTyK S k' Z)
    (h : glueLocT S A Tp φ f k' σ Y Z) (h' : glueLocT S A Tp φ f k' σ Z W) : glueLocT S A Tp φ f k' σ Y W := by
  unfold glueLocT at h h' ⊢
  split_ifs at h h' ⊢ with hh
  · exact (ihT k' _ hh k' (Hom.id k')).transTy h h'
  obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', r1, r1', s1, s1', f1, f1', hAA, hrest⟩ := h
  obtain ⟨A2, φ2, T2, e2, A2', φ2', T2', e2', r2, r2', s2, s2', f2, f2', hAA', hrest'⟩ := h'
  obtain ⟨rfl, rfl, rfl, rfl⟩ : A1' = A2 ∧ φ1' = φ2 ∧ T1' = T2 ∧ e1' = e2 := by
    have := RedW.unique r1'.1 r2.1; injection this with e1 e2 e3 e4; exact ⟨e1, e2, e3, e4⟩
  refine ⟨A1, φ1, T1, e1, A2', φ2', T2', e2', r1, r2', s1, s2', f1, f2', (ihA k' _).transTy hAA hAA',
    fun k'' σ' hh' => ?_⟩
  obtain ⟨hTT, hee⟩ := hrest k'' σ' hh'
  obtain ⟨hTT', hee'⟩ := hrest' k'' σ' hh'
  have hEq := glue_equivTy hW ihA krA ihT krT f σ hY hZ r1 r1' f1 f1' hAA σ' hh' hTT
  have P := (equivF_ok hW _ _ (famOK_comp2_id (ihT k'' _ hh') (krT k'' _ hh'))
    (famOK_comp2 ihA krA f (σ.comp σ'))).per k'' (ISub.id k'')
  exact ⟨(ihT k'' _ hh' k'' (Hom.id k'')).transTy hTT hTT', P.transEl hEq hee (P.conv (P.symTy hEq) hee')⟩

theorem glueLocE_symm {k' : ℕ} (σ : ISub k' k) {X X' g g' : Tm}
    (hT : glueLocT S A Tp φ f k' σ X X') (h : glueLocE S A Tp φ f k' σ X g g') : glueLocE S A Tp φ f k' σ X g' g := by
  unfold glueLocT at hT
  unfold glueLocE at h ⊢
  split_ifs at h hT ⊢ with hh
  · exact (ihT k' _ hh k' (Hom.id k')).symEl hT h
  obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', h1, h2, h3, h4, he0, he0', ha, hfib⟩ := h
  obtain ⟨A2, φ2, T2, e2, A2', φ2', T2', e2', r2, -, -, -, -, -, hAA, hrest⟩ := hT
  have e := RedW.unique r2.1 r1.1
  simp only [Tm.glue.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact ⟨_, _, _, _, ψ', e0', t0', a0', ψ, e0, t0, a0, r1, rg', rg, h3, h4, h1, h2, he0', he0,
    (ihA k' _).symEl hAA ha, fun k'' σ' hh => ⟨(ihT k'' _ hh k'' (Hom.id k'')).symEl (hrest k'' σ' hh).1
      (hfib k'' σ' hh).1, (hfib k'' σ' hh).2.2, (hfib k'' σ' hh).2.1⟩⟩

theorem glueLocE_trans {k' : ℕ} (σ : ISub k' k) {X X' g g' g'' : Tm}
    (hT : glueLocT S A Tp φ f k' σ X X') (h : glueLocE S A Tp φ f k' σ X g g')
    (h' : glueLocE S A Tp φ f k' σ X g' g'') : glueLocE S A Tp φ f k' σ X g g'' := by
  unfold glueLocT at hT
  unfold glueLocE at h h' ⊢
  split_ifs at h h' hT ⊢ with hh
  · exact (ihT k' _ hh k' (Hom.id k')).transEl hT h h'
  obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', h1, h2, h3, h4, he0, he0', ha, hfib⟩ := h
  obtain ⟨A3, φ3, T3, e3, χ, f0, s0, b0, χ', f0', s0', b0', r3, rh, rh', -, -, h7, h8, -, hf0', hb, hfib'⟩ := h'
  have e := RedW.unique r3.1 r1.1
  simp only [Tm.glue.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  have e' := RedW.unique rh.1 rg'.1
  simp only [Tm.glueEl.injEq] at e'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e'
  obtain ⟨A2, φ2, T2, e2, A2', φ2', T2', e2', r2, -, -, -, -, -, hAA, hrest⟩ := hT
  have e'' := RedW.unique r2.1 r3.1
  simp only [Tm.glue.injEq] at e''
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e''
  exact ⟨_, _, _, _, ψ, e0, t0, a0, χ', f0', s0', b0', r3, rg, rh', h1, h2, h7, h8, he0, hf0',
    (ihA k' _).transEl hAA ha hb, fun k'' σ' hh => ⟨(ihT k'' _ hh k'' (Hom.id k'')).transEl (hrest k'' σ' hh).1
      (hfib k'' σ' hh).1 (hfib' k'' σ' hh).1, (hfib k'' σ' hh).2.1, (hfib' k'' σ' hh).2.2⟩⟩

theorem glueLocE_conv {k' : ℕ} (σ : ISub k' k) {X X' g g' : Tm} (hX : IsTyK S k' X) (hX' : IsTyK S k' X')
    (hTσ : TyEq S k' X X') (hT : glueLocT S A Tp φ f k' σ X X') (h : glueLocE S A Tp φ f k' σ X g g') :
    glueLocE S A Tp φ f k' σ X' g g' := by
  unfold glueLocT at hT
  unfold glueLocE at h ⊢
  split_ifs at h hT ⊢ with hh
  · exact (ihT k' _ hh k' (Hom.id k')).conv hT h
  obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', h1, h2, h3, h4, he0, he0', ha, hfib⟩ := h
  obtain ⟨A2, φ2, T2, e2, A2', φ2', T2', e2', r2, r2', s2, s2', f2, f2', hAA, hrest⟩ := hT
  have e := RedW.unique r2.1 r1.1
  simp only [Tm.glue.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  obtain ⟨l1, hA1, -, hT1, he1⟩ := glue_parts hW r1 hX
  obtain ⟨l2, hA2, -, hT2, he2⟩ := glue_parts hW r2' hX'
  have q12 : I.Entails φ2 φ2' := ent_of_face_eq s2 s2' (f2.trans f2'.symm)
  have q21 : I.Entails φ2' φ2 := ent_of_face_eq s2' s2 (f2'.trans f2.symm)
  have hΦ : (cof .one φ2).Scoped k' := ⟨trivial, s2⟩
  have hΦ' : (cof .one φ2').Scoped k' := ⟨trivial, s2'⟩
  have c12 : I.Entails (cof .one φ2) (cof .one φ2') := ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) q12)
  have c21 : I.Entails (cof .one φ2') (cof .one φ2) := ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) q21)
  have hE1 := equiv_ty_cof hW s2 hA1 hT1
  have hE2 := HasTy.restrict hΦ c12 (equiv_ty_cof hW s2' hA2 hT2)
  -- the two equivalence types agree under the face
  have eqv : EqTm S k' (cof .one φ2) [] (Tm.equiv T2 A2) (Tm.equiv T2' A2') (.univ maxLevel) := by
    refine eq_of_restr hW s2 (.inr rfl) hE1 hE2 fun k'' σ' hh1 => ?_
    have hh' := face_of_holds f2 σ' hh1
    rw [Cof.restr_restr, ISub.comp_hom] at hh'
    obtain ⟨hTT2, -⟩ := hrest k'' σ' hh'
    have hEq := glue_equivTy hW ihA krA ihT krT f σ hX hX' r1 r2' f2 f2' hAA σ' hh' hTT2
    have hty := face_ty hW s2 hE1 σ' hh1
    rw [isub_equiv, isub_univ] at hty
    rw [isub_equiv, isub_equiv, isub_univ]
    exact eqTop hW hEq.1.2.2 hty
  -- the equivalences agree under the face
  have key : EqTm S k' (cof .one φ2) [] e2 e2' (Tm.equiv T2 A2) := by
    have he2' := HasTy.restrict hΦ c12 he2
    refine eq_of_restr hW s2 (.inl hE1) he1 (HasTy.conv he2' (EqTm.symm eqv)) fun k'' σ' hh1 => ?_
    have hh' := face_of_holds f2 σ' hh1
    rw [Cof.restr_restr, ISub.comp_hom] at hh'
    obtain ⟨-, hee⟩ := hrest k'' σ' hh'
    rw [isub_equiv]
    exact hee.1.2.2
  have eT' : EqTm S k' (cof .one φ2') [] (Tm.equiv T2 A2) (Tm.equiv T2' A2') (.univ maxLevel) :=
    EqTm.restrict hΦ' c21 eqv
  refine ⟨A2', φ2', T2', e2', ψ, e0, t0, a0, ψ', e0', t0', a0', r2', ⟨rg.1, rg.2.tyConv hTσ⟩,
    ⟨rg'.1, rg'.2.tyConv hTσ⟩, ent_trans h1 q12, ent_trans q21 h2, ent_trans h3 q12, ent_trans q21 h4,
    ?_, ?_, (ihA k' _).conv hAA ha, fun k'' σ' hh => ?_⟩
  · exact EqTm.conv (EqTm.restrict hΦ' c21 (he0.trans key)) eT'
  · exact EqTm.conv (EqTm.restrict hΦ' c21 (he0'.trans key)) eT'
  · obtain ⟨hTT2, hee⟩ := hrest k'' σ' hh
    obtain ⟨hf1, hb1, hb2⟩ := hfib k'' σ' hh
    have PT := ihT k'' _ hh k'' (Hom.id k'')
    have PA := ihA k'' (f.comp (σ.comp σ').hom)
    have hAAσ := (krA k' (f.comp σ.hom) k'' σ' A2 A2' A2 A2).1 hAA
    rw [ISub.comp_hom] at hAAσ
    -- the bases, converted along the bases and the equivalences of the types
    have cA2 := closed_of_ty hW (HasTy.isubS hW hA1 σ')
    have hT1σ := face_ty hW s2 hT1 σ' (holds_of_face f2 σ' (by rwa [Cof.restr_restr, ISub.comp_hom]))
    have cT2 := closed_of_ty hW hT1σ
    have hrefl : ∀ {x x' : Tm}, (Comp2 S (dat Tp k'' (f.comp (σ.comp σ').hom)) k'' k'' (Hom.id k'')).el
        (T2.isub σ') x x' → (Comp2 S A m k'' (f.comp (σ.comp σ').hom)).el (A2.isub σ')
          (.app (.fst (e2.isub σ')) x) (.app (.fst (e2'.isub σ')) x) := fun {x x'} hx => by
      have hx' := PT.reflEl hTT2 hx
      have := equivF_app hW cT2 cA2 hee (TP := fun k3 σ3 => Comp2 S (dat Tp k'' (f.comp (σ.comp σ').hom)) k'' k3 σ3.hom)
        (AP := fun k3 σ3 => Comp2 S A m k3 (f.comp ((σ.comp σ').comp σ3).hom))
        (by simp only [ISub.hom_id]; exact hx')
      simpa only [ISub.comp_id] using this
    refine ⟨PT.conv hTT2 hf1, PA.conv hAAσ (PA.transEl hAAσ hb1 (hrefl hf1)),
      PA.conv hAAσ (PA.transEl hAAσ hb2 (hrefl (PT.reflEl' hTT2 hf1)))⟩

end glueLoc

theorem per2_glueC {A Tp ep : V} {φ : Cof m} (hA : IsKV m A) (hφ : φ.IsCof)
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
    (ihA : PER2 S m A) (krA : KR2 S m A)
    (ihT : ∀ k (f : Hom k m), (φ.restr f).holds → PER2 S k (dat Tp k f))
    (krT : ∀ k (f : Hom k m), (φ.restr f).holds → KR2 S k (dat Tp k f)) :
    PER2 S m (glueC m A φ Tp ep) := by
  intro k f
  by_cases hf : (φ.restr f).holds
  · rw [Comp2_glueC_at hφ hTp hTkv f, if_pos hf]; exact ihT k f hf k (Hom.id k)
  rw [Comp2_glueC_f hA hφ hTp hTkv f hf]
  refine ⟨fun {T T'} hT => ?_, fun {T T' T''} hT hT' => ?_, fun {T T' t t'} hT ht => ?_,
    fun {T T' t t' t''} hT ht ht' => ?_, fun {T T' t t'} hT ht => ?_⟩
  · obtain ⟨hb, hall, hc, hc'⟩ := hT
    exact ⟨base_symm hb, fun k' σ => glueLocT_symm hW ihA krA ihT krT f σ (hb.1.isub hW σ) (hb.2.1.isub hW σ)
      (hall k' σ), hc', hc⟩
  · obtain ⟨hb, hall, hc, -⟩ := hT
    obtain ⟨hb', hall', -, hc''⟩ := hT'
    exact ⟨base_trans hW hb hb', fun k' σ => glueLocT_trans hW ihA krA ihT krT f σ (hb.1.isub hW σ)
      (hb.2.1.isub hW σ) (hall k' σ) (hall' k' σ), hc, hc''⟩
  · obtain ⟨he, hmem, -, hall, hc, hc'⟩ := ht
    exact ⟨he.symm, by rw [← semK_eq hW he.2.2]; exact hmem, he.symm,
      fun k' σ => glueLocE_symm hW ihA krA ihT krT f σ (hT.2.1 k' σ) (hall k' σ), hc', hc⟩
  · obtain ⟨he, hmem, -, hall, hc, -⟩ := ht
    obtain ⟨he', -, -, hall', -, hc''⟩ := ht'
    exact ⟨he.trans he', hmem, he.trans he',
      fun k' σ => glueLocE_trans hW ihA krA ihT krT f σ (hT.2.1 k' σ) (hall k' σ) (hall' k' σ), hc, hc''⟩
  · obtain ⟨he, hmem, -, hall, hc, hc'⟩ := ht
    have hTT := hT.1.2.2.2.2
    have cv : ∀ k' (σ : ISub k' k) {g g' : Tm}, glueLocE S A Tp φ f k' σ (T.isub σ) g g' →
        glueLocE S A Tp φ f k' σ (T'.isub σ) g g' := fun k' σ g g' h =>
      glueLocE_conv hW ihA krA ihT krT f σ (hT.1.1.isub hW σ) (hT.1.2.1.isub hW σ) (hTT.isub hW σ)
        (hT.2.1 k' σ) h
    have cvh : ∀ k' (σ : ISub k' k) (hh : (φ.restr (f.comp σ.hom)).holds) {g g' : Tm},
        (Comp2 S (dat Tp k' (f.comp σ.hom)) k' k' (Hom.id k')).el (T.isub σ) g g' →
        (Comp2 S (dat Tp k' (f.comp σ.hom)) k' k' (Hom.id k')).el (T'.isub σ) g g' := fun k' σ hh g g' h => by
      have hTσ := hT.2.1 k' σ
      unfold glueLocT at hTσ; rw [if_pos hh] at hTσ
      exact (ihT k' _ hh k' (Hom.id k')).conv hTσ h
    exact ⟨he.conv hTT, hmem, he.conv hTT, fun k' σ => cv k' σ (hall k' σ),
      fun k' σ hn w hw k'' ρ => ⟨fun hh ψ e0 t0 a0 hwe => cvh k'' (σ.comp ρ) hh ((hc k' σ hn w hw k'' ρ).1 hh ψ e0 t0 a0 hwe),
        fun hh => cv k'' (σ.comp ρ) ((hc k' σ hn w hw k'' ρ).2 hh)⟩,
      fun k' σ hn w hw k'' ρ => ⟨fun hh ψ e0 t0 a0 hwe => cvh k'' (σ.comp ρ) hh ((hc' k' σ hn w hw k'' ρ).1 hh ψ e0 t0 a0 hwe),
        fun hh => cv k'' (σ.comp ρ) ((hc' k' σ hn w hw k'' ρ).2 hh)⟩⟩

end

end Model.Whnf
