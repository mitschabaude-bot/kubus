import Model.Whnf.Kan2Elim
import Model.Canon.KanIPi

/-!
# The binary Kan operations at types of the form `(i : I) → A`
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The structure of a pair of related types whose normal forms are `(i : I) → A` types. -/
structure IPiStr (S : Sig) (k : ℕ) (T T' : Tm) : Prop where
  tyEq : TyEq S k T T'
  whnf : ∀ k' (ρ : ISub k' k), ∃ L1 L1', RedT S k' (T.isub ρ) (.ipi L1) ∧ RedT S k' (T'.isub ρ) (.ipi L1') ∧
    RT2 S (k' + 1) L1 L1' ∧ ∀ (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' →
      RT2 S k' (L1.dinst r) (L1'.dinst r')
  coh : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') L1 L2, RedT S k' (T.isub ρ) (.ipi L1) →
    RedT S k'' (T.isub (ρ.comp ρ')) (.ipi L2) → ∀ (s : I), s.Scoped k'' → RT2 S k'' ((L1.isub ρ'.up).dinst s) (L2.dinst s)
  tc : ∀ k' (ρ : ISub k' k) L1, RedT S k' (T.isub ρ) (.ipi L1) → ∀ (s : I), s.Scoped k' →
    TyCode k' (semK S k' (L1.dinst s))
  elim : ∀ k' (ρ : ISub k' k) L1 f f', RedT S k' (T.isub ρ) (.ipi L1) → RE2 S k' (T.isub ρ) f f' →
    ∀ (r r' : I), r.Scoped k' → r'.Scoped k' → I.Eq r r' → RE2 S k' (L1.dinst r) (.papp f r) (.papp f' r')
  coh' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') L1 L2, RedT S k' (T'.isub ρ) (.ipi L1) →
    RedT S k'' (T'.isub (ρ.comp ρ')) (.ipi L2) → ∀ (s : I), s.Scoped k'' →
    RT2 S k'' ((L1.isub ρ'.up).dinst s) (L2.dinst s)

theorem Comp2_ty_tyCode {m : ℕ} {X : V} {g : Hom k m} {A A' : Tm} (h : (Comp2 S X m k g).ty A A')
    (hX : TyCode m X) : TyCode k (semK S k A) := by
  rw [(Comp2_ty_base h).2.2.2.1]; exact hX.res g

variable (hW : WfSig S)
include hW

theorem RT2.dinst {A B : Tm} (hX : TyCode (k + 1) (semK S (k + 1) A)) (h : RT2 S (k + 1) A B) (s : I)
    (hs : s.Scoped k) : RT2 S k (A.dinst s) (B.dinst s) := by
  have hb := Comp2_ty_base h
  have := RT2.isub hW hX h (ISub.cons s hs (ISub.id k))
  rwa [isub_cons_id_of_closed (closed_of_isTyK hW hb.2.1),
    isub_cons_id_of_closed (closed_of_isTyK hW hb.2.2.1)] at this

theorem IPiStr_of {T T' L : Tm} {l : ℕ} (h : RT2 S k T T') (hR : RedT S k T (.ipi L))
    (hipi : HasTy S k .one [] (.ipi L) (.univ l)) : IPiStr S k T T' := by
  have hL0 := ipi_line hW hipi
  have hLne := semK_ne hW hL0
  have hX : semK S k T = ipiC k (semK S (k + 1) L) := (semK_tyEq hW hR.2).trans (semK_ipiT hW hipi)
  have hT := h
  unfold RT2 at hT
  rw [hX, Comp2_ipiC _ hLne] at hT
  obtain ⟨hbase, hall, hcoh, hcoh'⟩ := hT
  have hLc := tyCode_of_univ hW hL0
  refine ⟨hbase.2.2.2.2, fun k' ρ => ?_, fun k1 ρ k2 ρ' L1 L2 h1 h2 s hs => ?_, fun k' ρ L1 h1 s hs => ?_,
    fun k' ρ L1 f f' h1 hf => ?_, fun k1 ρ k2 ρ' L1 L2 h1 h2 s hs => ?_⟩
  rotate_right
  · have c := hcoh' k1 ρ k2 ρ' L1 L2 h1 h2
    exact RT2.dinst hW (Comp2_ty_tyCode c hLc) (Comp2_ty_RT2 c) s hs
  · obtain ⟨L1, L1', h1, h2, h3, h4⟩ := hall k' ρ
    exact ⟨L1, L1', h1, h2, Comp2_ty_RT2 h3, fun r r' hr hr' hE => Comp2_ty_RT2 (h4 r r' hr hr' hE)⟩
  · have c := hcoh k1 ρ k2 ρ' L1 L2 h1 h2
    exact RT2.dinst hW (Comp2_ty_tyCode c hLc) (Comp2_ty_RT2 c) s hs
  · obtain ⟨L4, L4', h4, -, -, hd⟩ := hall k' ρ
    obtain rfl : L4 = L1 := by have := RedW.unique h4.1 h1.1; injection this
    exact Comp2_ty_tyCode (hd s s hs hs (I_eq_refl s)) hLc
  · have hTρ : semK S k' (T.isub ρ) = res ρ.hom (semK S k T) :=
      semK_isubTy hW (Comp2_ty_base (show RT2 S k T T' from h)).2.1 ρ
    have hf2 : (Comp2 S (ipiC k (semK S (k + 1) L)) k k' ρ.hom).el (T.isub ρ) f f' := by
      rw [Comp2_eq_res (show ipiC k (semK S (k + 1) L) ≠ ∅ from mkKV_ne_empty _), ← hX, ← hTρ]
      exact hf
    obtain ⟨L3, h3, happ⟩ := ipiC_el_at hLne hW hf2
    obtain rfl : L3 = L1 := by have := RedW.unique h3.1 h1.1; injection this
    obtain ⟨L4, L4', h4, -, -, hd⟩ := hall k' ρ
    obtain rfl : L4 = L3 := by have := RedW.unique h4.1 h1.1; injection this
    intro r r' hr hr' hE
    have x := happ r r' hr hr' hE
    have hb := Comp2_ty_base (hd r r hr hr (I_eq_refl r))
    have e : (Hom.lift ρ.hom).comp (ISub.cons r hr (ISub.id k')).hom =
        (Hom.lift (Hom.id k)).comp (ISub.cons r hr ρ).hom := by
      have := lift_cons (Hom.id k) ρ r hr (ISub.id k')
      simpa only [Hom.id_comp, ISub.comp_id] using this
    rw [e] at x
    exact (Comp2_el_iff hb.1 hb.2.2.2.1).1 x


omit hW in
theorem step_hcomp_ipi {L u a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.hcomp (.ipi L) φ u a) = some (Tm.hcompIPi L φ u a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

/-- A point of a composition in an interval Π-type whose face does not hold. -/
theorem papp_hcomp_ipi {T L1 u a0 : Tm} {φ r : I} (hn : ¬ I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : RedT S k T (.ipi L1)) :
    Red S (.papp (.hcomp T φ u a0) r) (.hcomp (L1.dinst r) φ (.papp u r.shift) (.papp a0 r)) ∧
    EqTm S k .one [] (.papp (.hcomp T φ u a0) r) (.hcomp (L1.dinst r) φ (.papp u r.shift) (.papp a0 r))
      (L1.dinst r) := by
  obtain ⟨t, ht, htr⟩ := hcompIPi_body L1 u a0 φ r
  have e1 := eq_hcomp_ty hW hty hR.2
  have e2 := EqTm.hcompIPi (HasTy.eqR e1)
  have e3 := (e1.trans e2).tyConv hR.2
  have e4 := EqTm.iapp e3 hr hr (I_eq_refl r)
  rw [ht] at e4
  have e5 := EqTm.pathBeta (HasTy.eqR e4)
  rw [htr] at e5
  refine ⟨(red_papp r ((red_hcomp_ty hn hR.1.1).trans (.step (step_hcomp_ipi hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans e5⟩
  rw [ht]; show some (t.dinst r) = _; rw [htr]

/-- A point of a composition whose face holds. -/
theorem papp_hcomp_face {T L1 u a0 : Tm} {φ r : I} (h : I.Entails .one φ) (hr : r.Scoped k)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : TyEq S k T (.ipi L1)) :
    Red S (.papp (.hcomp T φ u a0) r) (.papp (u.dinst .one) r) ∧
    EqTm S k .one [] (.papp (.hcomp T φ u a0) r) (.papp (u.dinst .one) r) (L1.dinst r) :=
  ⟨red_papp r (.step (step_hcomp_face h) (.refl _)),
    EqTm.iapp ((EqTm.hcompFace h hty).tyConv hR) hr hr (I_eq_refl r)⟩

omit hW in
theorem papp_up_dinst (u : Tm) (r : I) (ρ : ISub k' k) (τ : ISub k'' k') (x : I) :
    ((Tm.papp (u.isub ρ.up) (r.subst ρ.τ).shift).isub τ.up).dinst x =
      .papp ((u.isub (ρ.comp τ).up).dinst x) (r.subst (ρ.comp τ).τ) := by
  show Tm.papp (((u.isub ρ.up).isub τ.up).dinst x) ((((r.subst ρ.τ).shift).subst τ.up.τ).subst (I.inst0 x)) = _
  rw [show (((r.subst ρ.τ).shift).subst τ.up.τ).subst (I.inst0 x) = (r.subst ρ.τ).subst τ.τ from
    shift_up_inst0 _ τ.τ x, Tm.isub_isub, ← ISub.up_comp, I_subst_comp]


theorem IPiStr.isub {T T' : Tm} (hP : IPiStr S k T T') (σ : ISub k' k) : IPiStr S k' (T.isub σ) (T'.isub σ) where
  tyEq := hP.tyEq.isub hW σ
  whnf k'' ρ := by simpa only [Tm.isub_isub] using hP.whnf k'' (σ.comp ρ)
  coh k1 ρ k2 ρ' L1 L2 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh k1 (σ.comp ρ) k2 ρ' L1 L2 h1 h2
  tc k1 ρ L1 h1 := by
    rw [Tm.isub_isub] at h1
    exact hP.tc k1 (σ.comp ρ) L1 h1
  elim k1 ρ L1 f f' h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    exact hP.elim k1 (σ.comp ρ) L1 f f' h1 h2
  coh' k1 ρ k2 ρ' L1 L2 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh' k1 (σ.comp ρ) k2 ρ' L1 L2 h1 h2

/-- Composition in interval Π-types, at related points. -/
theorem kanH2_ipi_core {T T' : Tm} (hP : IPiStr S k T T')
    (hIH : ∀ k' (ρ : ISub k' k) L1, RedT S k' (T.isub ρ) (.ipi L1) → ∀ (s : I), s.Scoped k' →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' ((L1.dinst s).isub ρ') X' → KanH2 S k'' ((L1.dinst s).isub ρ') X')
    {φ φ' : I} {u u' a0 a0' : Tm} (hty : HasTy S k .one [] (.hcomp T φ u a0) T)
    (hty' : HasTy S k .one [] (.hcomp T' φ' u' a0') T)
    (heq : EqTm S k .one [] (.hcomp T φ u a0) (.hcomp T' φ' u' a0') T)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k T φ u u') (ha0 : RE2 S k T a0 a0')
    {L1 : Tm} (hR : RedT S k T (.ipi L1)) {r r' : I} (hr : r.Scoped k) (hr' : r'.Scoped k) (hE : I.Eq r r') :
    RE2 S k (L1.dinst r) (.papp (.hcomp T φ u a0) r) (.papp (.hcomp T' φ' u' a0') r') := by
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hTK : IsTyK S k T := isTyK_of_ty hW hty
  have hTc : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTK)
  choose L2 L2' hw using hP.whnf
  have hR0 : RedT S k (T.isub (ISub.id k)) (.ipi L1) := by rw [hTc]; exact hR
  have hL2id : L2 k (ISub.id k) = L1 := by have := RedW.unique (hw k (ISub.id k)).1.1 hR0.1; injection this
  have hrid : r.subst (ISub.id k).τ = r := I_subst_id hr
  have hrid' : r'.subst (ISub.id k).τ = r' := I_subst_id hr'
  have hsc : ∀ k' (ρ : ISub k' k), (r.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr ρ.sc
  have hsc' : ∀ k' (ρ : ISub k' k), (r'.subst ρ.τ).Scoped k' := fun k' ρ => I.scoped_subst hr' ρ.sc
  have hEρ : ∀ k' (ρ : ISub k' k), I.Eq (r.subst ρ.τ) (r'.subst ρ.τ) := fun k' ρ => I_eq_subst hE ρ.τ
  have hX2 : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' ((L2 k' ρ).dinst (r.subst ρ.τ))) := fun k' ρ =>
    hP.tc k' ρ _ (hw k' ρ).1 _ (hsc k' ρ)
  have hCY : ∀ k' (ρ : ISub k' k), RT2 S k' ((L1.dinst r).isub ρ) ((L2 k' ρ).dinst (r.subst ρ.τ)) := by
    intro k' ρ
    rw [isub_dinst]
    exact hP.coh k (ISub.id k) k' ρ L1 (L2 k' ρ) hR0 (by rw [ISub.id_comp]; exact (hw k' ρ).1) _ (hsc k' ρ)
  have hXY : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' ((L1.dinst r).isub ρ)) := fun k' ρ =>
    RT2.tyCode_l hW (hCY k' ρ) (hX2 k' ρ)
  have hCC' : ∀ k' (ρ : ISub k' k), RT2 S k' ((L2 k' ρ).dinst (r.subst ρ.τ)) ((L2' k' ρ).dinst (r'.subst ρ.τ)) :=
    fun k' ρ => (hw k' ρ).2.2.2 _ _ (hsc k' ρ) (hsc' k' ρ) (hEρ k' ρ)
  have hel : ∀ k' (ρ : ISub k' k) f f', RE2 S k' (T.isub ρ) f f' →
      RE2 S k' ((L1.dinst r).isub ρ) (.papp f (r.subst ρ.τ)) (.papp f' (r'.subst ρ.τ)) := fun k' ρ f f' h =>
    RE2.conv' hW (hCY k' ρ) (hP.elim k' ρ _ f f' (hw k' ρ).1 h _ _ (hsc k' ρ) (hsc' k' ρ) (hEρ k' ρ)) (hXY k' ρ)
  have hX : TyCode k (semK S k (L1.dinst r)) := by
    have := hP.tc k (ISub.id k) L1 hR0 r hr; exact this
  have hYY : RT2 S k (L1.dinst r) (L1.dinst r) := by
    have := hCC' k (ISub.id k); rw [hL2id, hrid] at this; exact RT2.refl hW hX this
  have hpT : HasTy S k .one [] (.hcomp T φ u a0) (.ipi L1) := hty.tyConv hR.2
  have hE0 : EqTm S k .one [] (.papp (.hcomp T φ u a0) r) (.papp (.hcomp T' φ' u' a0') r') (L1.dinst r) :=
    EqTm.iapp (heq.tyConv hR.2) hr hr' hE
  -- the (combined) coherence of the eliminated types at a restriction of a restriction
  have hcoh : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k'),
      RT2 S k'' (((L2 k' ρ).dinst (r.subst ρ.τ)).isub ρ') ((L2 k'' (ρ.comp ρ')).dinst (r.subst (ρ.comp ρ').τ)) := by
    intro k' ρ k'' ρ'
    rw [isub_dinst, I_subst_comp]
    exact hP.coh k' ρ k'' ρ' _ _ (hw k' ρ).1 (hw k'' (ρ.comp ρ')).1 _ (by rw [← I_subst_comp]; exact hsc k'' _)
  have H := kanH2_elim_core hW hφs (fun k' ρ x => .papp x (r.subst ρ.τ)) (fun k' ρ x => .papp x (r'.subst ρ.τ))
    (fun k' ρ => (L2 k' ρ).dinst (r.subst ρ.τ)) (fun k' ρ => (L2' k' ρ).dinst (r'.subst ρ.τ))
    (fun k' ρ => .papp (u.isub ρ.up) (r.subst ρ.τ).shift) (fun k' ρ => .papp (u'.isub ρ.up) (r'.subst ρ.τ).shift)
    (fun k' ρ => .papp (a0.isub ρ) (r.subst ρ.τ)) (fun k' ρ => .papp (a0'.isub ρ) (r'.subst ρ.τ))
    (fun k' ρ => φ.subst ρ.τ) (fun k' ρ => φ'.subst ρ.τ)
    hX hYY (by simp only [hrid]; exact HasTy.iapp hpT hr) (by simp only [hrid']; exact HasTy.eqR hE0)
    (by simp only [hrid, hrid']; exact hE0)
    (fun k' ρ k'' ρ' x => by
      show Tm.papp (x.isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = Tm.papp (x.isub ρ') (r.subst (ρ.comp ρ').τ)
      rw [I_subst_comp])
    (fun k' ρ k'' ρ' x => by
      show Tm.papp (x.isub ρ') ((r'.subst ρ.τ).subst ρ'.τ) = Tm.papp (x.isub ρ') (r'.subst (ρ.comp ρ').τ)
      rw [I_subst_comp])
    (fun k' ρ => ?_) (fun k' ρ => ?_) hel
    (fun k' ρ k'' ρ' hf2 => by
      show I.Entails .one ((φ.subst ρ.τ).subst ρ'.τ); rw [← I_subst_comp]; exact hf2)
    (fun k' ρ k'' ρ' _ => by
      show I.Entails ((φ.subst ρ.τ).subst ρ'.τ) (φ'.subst (ρ.comp ρ').τ) ∧
        I.Entails (φ'.subst (ρ.comp ρ').τ) ((φ.subst ρ.τ).subst ρ'.τ)
      rw [← I_subst_comp]; exact ⟨ent_subst h12 _, ent_subst h21 _⟩)
    (fun k' ρ k'' ρ' _ hf2 => by
      show RE2 S k'' _ (((Tm.papp (u.isub ρ.up) (r.subst ρ.τ).shift).isub ρ'.up).dinst .one) _
      rw [papp_up_dinst]
      exact hel k'' (ρ.comp ρ') _ _ (htube k'' (ρ.comp ρ') .one .one trivial trivial (I_eq_refl _)
        ((holds_iff_entails (I.scoped_subst hφs (ρ.comp ρ').sc)).2 hf2)))
    (fun k' ρ k'' ρ' _ k3 σ3 x x' hx hx' hEx hh => by
      show RE2 S k3 _ ((((Tm.papp (u.isub ρ.up) (r.subst ρ.τ).shift).isub ρ'.up).isub σ3.up).dinst x)
        (((Tm.papp (u'.isub (ρ.comp ρ').up) (r'.subst (ρ.comp ρ').τ).shift).isub σ3.up).dinst x')
      have e1 : (((Tm.papp (u.isub ρ.up) (r.subst ρ.τ).shift).isub ρ'.up).isub σ3.up).dinst x =
          Tm.papp ((u.isub (ρ.comp (ρ'.comp σ3)).up).dinst x) (r.subst (ρ.comp (ρ'.comp σ3)).τ) := by
        rw [Tm.isub_isub, ← ISub.up_comp, papp_up_dinst]
      rw [e1, papp_up_dinst, Tm.isub_isub, ISub.comp_assoc]
      refine hel k3 _ _ _ (htube k3 _ x x' hx hx' hEx ?_)
      rw [I_subst_comp, I_subst_comp]; exact hh)
    (fun k' ρ k'' ρ' _ => by
      show RE2 S k'' _ ((Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ') (Tm.papp (a0'.isub (ρ.comp ρ')) (r'.subst (ρ.comp ρ').τ))
      rw [show (Tm.papp (a0.isub ρ) (r.subst ρ.τ)).isub ρ' = Tm.papp (a0.isub (ρ.comp ρ')) (r.subst (ρ.comp ρ').τ) by
        show Tm.papp ((a0.isub ρ).isub ρ') ((r.subst ρ.τ).subst ρ'.τ) = _; rw [Tm.isub_isub, I_subst_comp]]
      exact hel k'' (ρ.comp ρ') _ _ (RE2.isub hW ha0 _))
    (fun k' ρ k'' ρ' _ => ?_) (fun k' ρ k'' ρ' _ => ?_) h12 h21 htube
  · simpa only [hrid, hrid'] using H
  · have hρ : HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (T.isub ρ) :=
      HasTy.isubS hW hty ρ
    have e := TyEq.symm (Comp2_ty_base (hCY k' ρ)).2.2.2.2.2
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a, b⟩ := papp_hcomp_face hW hf (hsc k' ρ) hρ (hw k' ρ).1.2
      exact ⟨a, b.tyConv e⟩
    · obtain ⟨a, b⟩ := papp_hcomp_ipi hW hf (hsc k' ρ) hρ (hw k' ρ).1
      exact ⟨a, b.tyConv e⟩
  · have hρ : HasTy S k' .one [] (.hcomp (T'.isub ρ) (φ'.subst ρ.τ) (u'.isub ρ.up) (a0'.isub ρ)) (T'.isub ρ) :=
      (HasTy.isubS hW hty' ρ).tyConv (hP.tyEq.isub hW ρ)
    have e := TyEq.trans hW (TyEq.symm (Comp2_ty_base (hCC' k' ρ)).2.2.2.2.2)
      (TyEq.symm (Comp2_ty_base (hCY k' ρ)).2.2.2.2.2)
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a, b⟩ := papp_hcomp_face hW hf (hsc' k' ρ) hρ (hw k' ρ).2.1.2
      exact ⟨a, b.tyConv e⟩
    · obtain ⟨a, b⟩ := papp_hcomp_ipi hW hf (hsc' k' ρ) hρ (hw k' ρ).2.1
      exact ⟨a, b.tyConv e⟩
  · have c1 := hcoh k' ρ k'' ρ'
    exact RT2.trans hW (RT2.tyCode_l hW c1 (hX2 k'' _)) c1 (RT2.symm hW (hXY k'' _) (hCY k'' (ρ.comp ρ')))
  · have c1 := hcoh k' ρ k'' ρ'
    exact hIH k' ρ (L2 k' ρ) (hw k' ρ).1 _ (hsc k' ρ) k'' ρ' _
      (RT2.trans hW (RT2.tyCode_l hW c1 (hX2 k'' _)) c1 (hCC' k'' (ρ.comp ρ')))


/-- Related elements of a type whose normal form is an interval Π-type, through their points. -/
theorem RE2_ipiW_intro {T L t t' : Tm} {l : ℕ} (hTT : RT2 S k T T) (hR : RedT S k T (.ipi L))
    (hipi : HasTy S k .one [] (.ipi L) (.univ l)) (hE : EB S k T t t')
    (happ : ∀ k' (ρ : ISub k' k) L1, RedT S k' (T.isub ρ) (.ipi L1) → ∀ (r r' : I), r.Scoped k' → r'.Scoped k' →
      I.Eq r r' → RE2 S k' (L1.dinst r) (.papp (t.isub ρ) r) (.papp (t'.isub ρ) r')) :
    RE2 S k T t t' := by
  have hL0 := ipi_line hW hipi
  have hLne := semK_ne hW hL0
  have hX : semK S k T = ipiC k (semK S (k + 1) L) := (semK_tyEq hW hR.2).trans (semK_ipiT hW hipi)
  have hT := hTT
  unfold RT2 at hT
  rw [hX, Comp2_ipiC _ hLne] at hT
  obtain ⟨-, hall, -, -⟩ := hT
  unfold RE2
  rw [hX, Comp2_ipiC _ hLne]
  refine ⟨hE, ?_, hE, fun k' ρ => ?_⟩
  · rw [← hX, res_id (by rw [hX]; exact isKV_mkKV _)]; exact mem_of_ty hW hE.1
  obtain ⟨L1, L1', h1, -, -, hd⟩ := hall k' ρ
  refine ⟨L1, h1, fun r r' hr hr' hEq => ?_⟩
  rw [ISub.id_comp]
  have hb := (Comp2_ty_base (hd r r hr hr (I_eq_refl r))).2.2.2.1
  exact (Comp2_el_iff hLne hb).2 (happ k' ρ L1 h1 r r' hr hr' hEq)

/-- Composition at a pair of related types whose normal forms are interval Π-types. -/
theorem kanH2_ipi {T T' L : Tm} {l : ℕ} (hTT : RT2 S k T T') (hR : RedT S k T (.ipi L))
    (hipi : HasTy S k .one [] (.ipi L) (.univ l))
    (hIH : ∀ k' (ρ : ISub k' k) L1, RedT S k' (T.isub ρ) (.ipi L1) → ∀ (s : I), s.Scoped k' →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' ((L1.dinst s).isub ρ') X' → KanH2 S k'' ((L1.dinst s).isub ρ') X') :
    KanH2 S k T T' := by
  have hP := IPiStr_of hW hTT hR hipi
  intro φ φ' u u' a0 a0' hty hty' heq h12 h21 htube ha0
  have hXT : TyCode k (semK S k T) := tyCode_of_ty hW hty
  refine RE2_ipiW_intro hW (RT2.refl hW hXT hTT) hR hipi ⟨hty, hty', heq⟩ fun k' ρ L1 h1 r r' hr hr' hE => ?_
  refine kanH2_ipi_core hW (hP.isub hW ρ) (fun k1 ρ1 L3 h3 s hs k2 ρ2 X' hX' => ?_) (HasTy.isubS hW hty ρ)
    (HasTy.isubS hW hty' ρ) (EqTm.isubS hW heq ρ) (ent_subst h12 ρ.τ) (ent_subst h21 ρ.τ) (htube.isub ρ)
    (RE2.isub hW ha0 ρ) h1 hr hr' hE
  rw [Tm.isub_isub] at h3
  exact hIH k1 (ρ.comp ρ1) L3 h3 s hs k2 ρ2 X' hX'

end

end Model.Whnf
