import Model.Whnf.Kan2Basic
import Model.Canon.KanPi

/-!
# The binary Kan operations at Π-types
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- A composition at an equal type. -/
theorem eq_hcomp_ty {T W u a : Tm} {φ : I} (hty : HasTy S k .one [] (.hcomp T φ u a) T) (e : TyEq S k T W) :
    EqTm S k .one [] (.hcomp T φ u a) (.hcomp W φ u a) T := by
  rcases e with rfl | ⟨l, e⟩
  · exact EqTm.refl hty
  obtain ⟨l1, ⟨hq, hψ, hu, ha1, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have H := HasTy0.hcomp hq hψ hu ha1 hside
  have e0 := spec_to_minimal_eq hW e
  exact minimal_to_spec_eq (EqTm0.hcomp H (hcomp_retype0 hW hψ hu ha1 hside e0) e0 (ent_refl _) (ent_refl _)
    (EqTm0.refl hu) (EqTm0.refl ha1))

omit hW in
theorem step_hcomp_pi {A B u a : Tm} {φ : I} (hn : ¬ I.Entails .one φ) :
    step S (.hcomp (.pi A B) φ u a) = some (Tm.hcompPi A B φ u a) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn']

/-- An application of a composition in a Π-type whose face does not hold. -/
theorem app_hcomp_pi {T A1 B1 u a0 b : Tm} {φ : I} (hn : ¬ I.Entails .one φ)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : RedT S k T (.pi A1 B1)) (hb : HasTy S k .one [] b A1) :
    Red S (.app (.hcomp T φ u a0) b) (.hcomp (B1.inst b) φ (.app u b.dshift) (.app a0 b)) ∧
    EqTm S k .one [] (.app (.hcomp T φ u a0) b) (.hcomp (B1.inst b) φ (.app u b.dshift) (.app a0 b))
      (B1.inst b) := by
  have e1 := eq_hcomp_ty hW hty hR.2
  have e2 := EqTm.hcompPi (HasTy.eqR e1)
  have e3 := (e1.trans e2).tyConv hR.2
  have e4 := EqTm.app e3 (EqTm.refl hb)
  have e5 := EqTm.piBeta (HasTy.eqR e4)
  simp only [Tm.hcompPi] at e5
  rw [hcompPi_body_inst] at e5
  refine ⟨(red_app b ((red_hcomp_ty hn hR.1.1).trans (.step (step_hcomp_pi hn) (.refl _)))).trans
    (.step ?_ (.refl _)), e4.trans ?_⟩
  · show step S (.app (Tm.lam A1 _) b) = _
    simp only [step]; rw [hcompPi_body_inst]
  · simpa only [Tm.hcompPi] using e5

/-- An application of a composition whose face holds. -/
theorem app_hcomp_face {T A1 B1 u a0 b : Tm} {φ : I} (h : I.Entails .one φ)
    (hty : HasTy S k .one [] (.hcomp T φ u a0) T) (hR : TyEq S k T (.pi A1 B1)) (hb : HasTy S k .one [] b A1) :
    Red S (.app (.hcomp T φ u a0) b) (.app (u.dinst .one) b) ∧
    EqTm S k .one [] (.app (.hcomp T φ u a0) b) (.app (u.dinst .one) b) (B1.inst b) :=
  ⟨red_app b (.step (step_hcomp_face h) (.refl _)), EqTm.app ((EqTm.hcompFace h hty).tyConv hR) (EqTm.refl hb)⟩


omit hW in
theorem isub_hcomp (T u a : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.hcomp T φ u a).isub σ = .hcomp (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (a.isub σ) := rfl

/-- Converting a related pair to a related type, given a related element at the target. -/
theorem RE2.conv' {A A' t t' : Tm} (hA : RT2 S k A' A) (h : RE2 S k A t t') (hX : TyCode k (semK S k A')) :
    RE2 S k A' t t' :=
  RE2.conv hW (RT2.symm hW hX hA) h

theorem RT2.tyCode_r {A A' : Tm} (h : RT2 S k A A') (hX : TyCode k (semK S k A)) : TyCode k (semK S k A') := by
  rw [RT2.semK_eq hW h]; exact hX

theorem RT2.tyCode_l {A A' : Tm} (h : RT2 S k A A') (hX : TyCode k (semK S k A')) : TyCode k (semK S k A) := by
  rw [← RT2.semK_eq hW h]; exact hX

/-- The structure of a pair of related types whose normal forms are Π-types. -/
structure PiStr (S : Sig) (k : ℕ) (T T' : Tm) : Prop where
  tyEq : TyEq S k T T'
  whnf : ∀ k' (ρ : ISub k' k), ∃ A1 B1 A1' B1', RedT S k' (T.isub ρ) (.pi A1 B1) ∧
    RedT S k' (T'.isub ρ) (.pi A1' B1') ∧ RT2 S k' A1 A1' ∧ ∀ a a', RE2 S k' A1 a a' → RT2 S k' (B1.inst a) (B1'.inst a')
  coh : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') A1 B1 A2 B2, RedT S k' (T.isub ρ) (.pi A1 B1) →
    RedT S k'' (T.isub (ρ.comp ρ')) (.pi A2 B2) →
    RT2 S k'' (A1.isub ρ') A2 ∧ ∀ a a', RE2 S k'' (A1.isub ρ') a a' → RT2 S k'' ((B1.isub ρ').inst a) (B2.inst a')
  elim : ∀ k' (ρ : ISub k' k) A1 B1 f f', RedT S k' (T.isub ρ) (.pi A1 B1) → RE2 S k' (T.isub ρ) f f' →
    ∀ a a', RE2 S k' A1 a a' → RE2 S k' (B1.inst a) (.app f a) (.app f' a')
  coh' : ∀ k' (ρ : ISub k' k) k'' (ρ' : ISub k'' k') A1 B1 A2 B2, RedT S k' (T'.isub ρ) (.pi A1 B1) →
    RedT S k'' (T'.isub (ρ.comp ρ')) (.pi A2 B2) →
    RT2 S k'' (A1.isub ρ') A2 ∧ ∀ a a', RE2 S k'' (A1.isub ρ') a a' → RT2 S k'' ((B1.isub ρ').inst a) (B2.inst a')


omit hW in
theorem app_up_dinst (u a : Tm) (ρ : ISub k' k) (τ : ISub k'' k') (r : I) :
    ((Tm.app (u.isub ρ.up) (a.isub ρ).dshift).isub τ.up).dinst r =
      .app ((u.isub (ρ.comp τ).up).dinst r) (a.isub (ρ.comp τ)) := by
  rw [isub_app, Tm.isub_isub, ← ISub.up_comp]
  show Tm.app (((u.isub (ρ.comp τ).up)).dinst r) ((((a.isub ρ).dshift).isub τ.up).dinst r) = _
  rw [dshift_isub_up_dinst, Tm.isub_isub]

omit hW in
theorem up_dinst_one_isub (u : Tm) (ρ : ISub k' k) (τ : ISub k'' k') :
    ((u.isub ρ.up).dinst .one).isub τ = (u.isub (ρ.comp τ).up).dinst .one := by
  rw [isub_dinst, Tm.isub_isub, ← ISub.up_comp]; rfl

/-- Applying judgmentally equal tubes to judgmentally equal arguments. -/
theorem eqCof_app {ψ : I} (hψ : ψ.Scoped k) {f f' X A B a a' : Tm} {l : ℕ}
    (hf : EqTm S (k + 1) (cof .one ψ).shift [] f f' X.dshift) (hX : TyEq S k X (.pi A B))
    (hpi : HasTy S k .one [] (.pi A B) (.univ l)) (ha : EqTm S k .one [] a a' A) :
    EqTm S (k + 1) (cof .one ψ).shift [] (.app f a.dshift) (.app f' a'.dshift) ((B.inst a).isub (ISub.wk k)) := by
  have e1 := EqTm.cofConv hψ hf hX
  rw [← dshift_eq_isub_closed (closed_of_ty hW hpi), isub_pi] at e1
  have ea := EqTm.toCof hψ (EqTm.isubS hW ha (ISub.wk k))
  rw [dshift_eq_isub_closed (closed_of_ty hW (HasTy.eqL ha)), dshift_eq_isub_closed (closed_of_ty hW (HasTy.eqR ha))] at ea
  have e2 := EqTm.app e1 ea
  rw [isub_inst, dshift_eq_isub_closed (closed_of_ty hW (HasTy.eqL ha))]
  exact e2

/-- Composition in Π-types, applied to related arguments. -/
theorem kanH2_pi_core {T T' : Tm} (hP : PiStr S k T T')
    (hIH : ∀ k' (ρ : ISub k' k) A1 B1, RedT S k' (T.isub ρ) (.pi A1 B1) → ∀ b, RE2 S k' A1 b b →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' ((B1.inst b).isub ρ') X' → KanH2 S k'' ((B1.inst b).isub ρ') X')
    {φ φ' : I} {u u' a0 a0' : Tm} (hty : HasTy S k .one [] (.hcomp T φ u a0) T)
    (hty' : HasTy S k .one [] (.hcomp T' φ' u' a0') T)
    (heq : EqTm S k .one [] (.hcomp T φ u a0) (.hcomp T' φ' u' a0') T)
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' T.dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k T φ u u') (ha0 : RE2 S k T a0 a0')
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) ((u.isub σ.up).dinst .zero) (a0'.isub σ))
    (hbd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (a0.isub σ) ((u'.isub σ.up).dinst .zero))
    {A1 B1 : Tm} (hR : RedT S k T (.pi A1 B1)) {a a' : Tm} (ha : RE2 S k A1 a a') :
    RE2 S k (B1.inst a) (.app (.hcomp T φ u a0) a) (.app (.hcomp T' φ' u' a0') a') := by
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hTK : IsTyK S k T := isTyK_of_ty hW hty
  have hTc : T.isub (ISub.id k) = T := isub_id_of_closed (closed_of_isTyK hW hTK)
  choose A2 B2 A2' B2' hw using hP.whnf
  have hR0 : RedT S k (T.isub (ISub.id k)) (.pi A1 B1) := by rw [hTc]; exact hR
  -- the coherence from the stage itself to a restriction
  have hC : ∀ k' (ρ : ISub k' k), RT2 S k' (A1.isub ρ) (A2 k' ρ) ∧
      ∀ b b', RE2 S k' (A1.isub ρ) b b' → RT2 S k' ((B1.isub ρ).inst b) ((B2 k' ρ).inst b') := by
    intro k' ρ
    exact hP.coh k (ISub.id k) k' ρ A1 B1 (A2 k' ρ) (B2 k' ρ) hR0 (by rw [ISub.id_comp]; exact (hw k' ρ).1)
  have haρ : ∀ k' (ρ : ISub k' k), RE2 S k' (A1.isub ρ) (a.isub ρ) (a'.isub ρ) := fun k' ρ => RE2.isub hW ha ρ
  have hX1 : ∀ k' (ρ : ISub k' k), TyCode k' (semK S k' (A1.isub ρ)) := fun k' ρ => RE2.tyCode hW (haρ k' ρ)
  have haaρ : ∀ k' (ρ : ISub k' k), RE2 S k' (A1.isub ρ) (a.isub ρ) (a.isub ρ) := fun k' ρ =>
    (perK hW (hX1 k' ρ)).reflEl (hC k' ρ).1 (haρ k' ρ)
  -- applications of related elements of a restriction of `T` to the arguments
  have H1 : ∀ k' (ρ : ISub k' k) f f', RE2 S k' (T.isub ρ) f f' →
      RE2 S k' ((B1.inst a).isub ρ) (.app f (a.isub ρ)) (.app f' (a'.isub ρ)) := by
    intro k' ρ f f' h
    have hel := hP.elim k' ρ (A2 k' ρ) (B2 k' ρ) f f' (hw k' ρ).1 h _ _ (RE2.conv hW (hC k' ρ).1 (haρ k' ρ))
    have hcod := (hC k' ρ).2 _ _ (haaρ k' ρ)
    have hX : TyCode k' (semK S k' ((B1.isub ρ).inst (a.isub ρ))) := by
      rw [← RT2.semK_eq hW hcod]; exact RE2.tyCode hW hel
    rw [isub_inst]
    exact RE2.conv' hW hcod hel hX
  -- the type of the applications
  have hpiK : IsTyK S k (.pi A1 B1) := hTK.of_tyEq hR.2
  have hpic := closed_of_isTyK hW hpiK
  simp only [Tm.closedB, Bool.and_eq_true] at hpic
  have hB1c : B1.isub (ISub.id k) = B1 := isub_id_of_closed hpic.2
  have hA1c : A1.isub (ISub.id k) = A1 := isub_id_of_closed hpic.1
  obtain ⟨hA2id, hB2id⟩ : A2 k (ISub.id k) = A1 ∧ B2 k (ISub.id k) = B1 := by
    have := RedW.unique (hw k (ISub.id k)).1.1 hR0.1; injection this; constructor <;> assumption
  have haa : RE2 S k A1 a a := by have := haaρ k (ISub.id k); rwa [hA1c, isub_id_of_closed
    (closed_of_ty hW (RE2.typed ha).1)] at this
  have hcodY : ∀ b b', RE2 S k A1 b b' → RT2 S k (B1.inst b) (B1.inst b') := by
    intro b b' hb
    have := (hC k (ISub.id k)).2 b b' (by rwa [hA1c])
    rwa [hB1c, hB2id] at this
  have hYY : RT2 S k (B1.inst a) (B1.inst a) := hcodY a a haa
  have hpiT : HasTy S k .one [] (.hcomp T φ u a0) (.pi A1 B1) := hty.tyConv hR.2
  have ht : HasTy S k .one [] (.app (.hcomp T φ u a0) a) (B1.inst a) := HasTy.app hpiT (RE2.typed ha).1
  have ht' : HasTy S k .one [] (.app (.hcomp T' φ' u' a0') a') (B1.inst a) :=
    (HasTy.app (hty'.tyConv hR.2) (RE2.typed ha).2.1).tyConv (TyEq.symm (Comp2_ty_base (hcodY a a' ha)).2.2.2.2.2)
  have hX : TyCode k (semK S k (B1.inst a)) := tyCode_of_ty hW ht
  -- the reducts at a restriction
  let L : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    if I.Entails .one (φ.subst ρ.τ) then .app ((u.isub ρ.up).dinst .one) (a.isub ρ)
    else .hcomp ((B2 k' ρ).inst (a.isub ρ)) (φ.subst ρ.τ) (.app (u.isub ρ.up) (a.isub ρ).dshift)
      (.app (a0.isub ρ) (a.isub ρ))
  let R : ∀ k' (_ : ISub k' k), Tm := fun k' ρ =>
    if I.Entails .one (φ'.subst ρ.τ) then .app ((u'.isub ρ.up).dinst .one) (a'.isub ρ)
    else .hcomp ((B2' k' ρ).inst (a'.isub ρ)) (φ'.subst ρ.τ) (.app (u'.isub ρ.up) (a'.isub ρ).dshift)
      (.app (a0'.isub ρ) (a'.isub ρ))
  have hYρ : ∀ k' (ρ : ISub k' k), TyEq S k' ((B2 k' ρ).inst (a.isub ρ)) ((B1.inst a).isub ρ) := by
    intro k' ρ
    rw [isub_inst]
    exact TyEq.symm (Comp2_ty_base ((hC k' ρ).2 _ _ (haaρ k' ρ))).2.2.2.2.2
  have hb : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (a.isub ρ) (A2 k' ρ) := fun k' ρ =>
    (RE2.typed (RE2.conv hW (hC k' ρ).1 (haρ k' ρ))).1
  have hrel2 : ∀ k' (ρ : ISub k' k), RE2 S k' (A2 k' ρ) (a.isub ρ) (a'.isub ρ) := fun k' ρ =>
    RE2.conv hW (hC k' ρ).1 (haρ k' ρ)
  have hb' : ∀ k' (ρ : ISub k' k), HasTy S k' .one [] (a'.isub ρ) (A2' k' ρ) := fun k' ρ =>
    (RE2.typed (RE2.conv hW (hw k' ρ).2.2.1 (hrel2 k' ρ))).2.1
  have hYρ' : ∀ k' (ρ : ISub k' k), TyEq S k' ((B2' k' ρ).inst (a'.isub ρ)) ((B1.inst a).isub ρ) := by
    intro k' ρ
    have e1 := (Comp2_ty_base ((hw k' ρ).2.2.2 _ _ (hrel2 k' ρ))).2.2.2.2.2
    exact TyEq.trans hW (TyEq.symm e1) (hYρ k' ρ)
  have hu : ∀ k' (ρ : ISub k' k), Red S ((Tm.app (.hcomp T φ u a0) a).isub ρ) (L k' ρ) ∧
      EqTm S k' .one [] ((Tm.app (.hcomp T φ u a0) a).isub ρ) (L k' ρ) ((B1.inst a).isub ρ) := by
    intro k' ρ
    have hρ : HasTy S k' .one [] (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (T.isub ρ) :=
      HasTy.isubS hW hty ρ
    show Red S (.app (.hcomp (T.isub ρ) (φ.subst ρ.τ) (u.isub ρ.up) (a0.isub ρ)) (a.isub ρ)) _ ∧ _
    by_cases hf : I.Entails .one (φ.subst ρ.τ)
    · simp only [L, if_pos hf]
      obtain ⟨r, e⟩ := app_hcomp_face hW hf hρ (hw k' ρ).1.2 (hb k' ρ)
      exact ⟨r, e.tyConv (hYρ k' ρ)⟩
    · simp only [L, if_neg hf]
      obtain ⟨r, e⟩ := app_hcomp_pi hW hf hρ (hw k' ρ).1 (hb k' ρ)
      exact ⟨r, e.tyConv (hYρ k' ρ)⟩
  have hu' : ∀ k' (ρ : ISub k' k), Red S ((Tm.app (.hcomp T' φ' u' a0') a').isub ρ) (R k' ρ) ∧
      EqTm S k' .one [] ((Tm.app (.hcomp T' φ' u' a0') a').isub ρ) (R k' ρ) ((B1.inst a).isub ρ) := by
    intro k' ρ
    have hρ : HasTy S k' .one [] (.hcomp (T'.isub ρ) (φ'.subst ρ.τ) (u'.isub ρ.up) (a0'.isub ρ)) (T'.isub ρ) :=
      (HasTy.isubS hW hty' ρ).tyConv (hP.tyEq.isub hW ρ)
    show Red S (.app (.hcomp (T'.isub ρ) (φ'.subst ρ.τ) (u'.isub ρ.up) (a0'.isub ρ)) (a'.isub ρ)) _ ∧ _
    by_cases hf : I.Entails .one (φ'.subst ρ.τ)
    · simp only [R, if_pos hf]
      obtain ⟨r, e⟩ := app_hcomp_face hW hf hρ (hw k' ρ).2.1.2 (hb' k' ρ)
      exact ⟨r, e.tyConv (hYρ' k' ρ)⟩
    · simp only [R, if_neg hf]
      obtain ⟨r, e⟩ := app_hcomp_pi hW hf hρ (hw k' ρ).2.1 (hb' k' ρ)
      exact ⟨r, e.tyConv (hYρ' k' ρ)⟩
  refine RE2.expandBoth hW hX hYY ht ht' L R hu hu' fun k' ρ k'' ρ' => ?_
  -- the cross relation of the reducts
  have hφτ : ∀ {ψ : I}, I.Entails .one (ψ.subst (ρ.comp ρ').τ) ↔ I.Entails .one ((ψ.subst ρ.τ).subst ρ'.τ) := by
    intro ψ; rw [I_subst_subst]; rfl
  have hholds : ∀ {k3 : ℕ} (τ : ISub k3 k), I.Entails .one (φ.subst τ.τ) → (ival (idEnv k3) (φ.subst τ.τ)).holds :=
    fun τ h => (holds_iff_entails (I.scoped_subst hφs τ.sc)).2 h
  have hfin : I.Entails .one (φ.subst (ρ.comp ρ').τ) →
      RE2 S k'' ((B1.inst a).isub (ρ.comp ρ')) (.app ((u.isub (ρ.comp ρ').up).dinst .one) (a.isub (ρ.comp ρ')))
        (R k'' (ρ.comp ρ')) := by
    intro hf2
    have hf2' : I.Entails .one (φ'.subst (ρ.comp ρ').τ) := ent_trans hf2 (ent_subst h12 _)
    simp only [R, if_pos hf2']
    exact H1 k'' (ρ.comp ρ') _ _ (htube k'' (ρ.comp ρ') .one .one trivial trivial (I_eq_refl _) (hholds _ hf2))
  have htyL : HasTy S k'' .one [] ((L k' ρ).isub ρ') ((B1.inst a).isub (ρ.comp ρ')) := by
    have := HasTy.isubS hW (HasTy.eqR (hu k' ρ).2) ρ'
    rwa [Tm.isub_isub] at this
  have htyR : HasTy S k'' .one [] (R k'' (ρ.comp ρ')) ((B1.inst a).isub (ρ.comp ρ')) := HasTy.eqR (hu' k'' (ρ.comp ρ')).2
  have hYτ : RT2 S k'' ((B1.inst a).isub (ρ.comp ρ')) ((B1.inst a).isub (ρ.comp ρ')) := RT2.isub hW hX hYY _
  by_cases hf : I.Entails .one (φ.subst ρ.τ)
  · -- the face holds at the first restriction
    have hL : (L k' ρ).isub ρ' = .app ((u.isub (ρ.comp ρ').up).dinst .one) (a.isub (ρ.comp ρ')) := by
      simp only [L, if_pos hf]
      rw [isub_app, up_dinst_one_isub, Tm.isub_isub]
    rw [hL]
    exact hfin (ent_comp hf)
  by_cases hf2 : I.Entails .one (φ.subst (ρ.comp ρ').τ)
  · -- the face holds only at the second restriction
    have hL : (L k' ρ).isub ρ' = .hcomp (((B2 k' ρ).inst (a.isub ρ)).isub ρ') ((φ.subst ρ.τ).subst ρ'.τ)
        ((Tm.app (u.isub ρ.up) (a.isub ρ).dshift).isub ρ'.up) ((Tm.app (a0.isub ρ) (a.isub ρ)).isub ρ') := by
      simp only [L, if_neg hf]; rfl
    have hst := stable_hcompFace hW (hφτ.1 hf2) (hL ▸ htyL)
    rw [app_up_dinst] at hst
    rw [hL] at htyL ⊢
    exact RE2.expandL hW hYτ htyL htyR hst (hfin hf2)
  · -- the face holds at neither: compose in the codomains
    have hf2' : ¬ I.Entails .one (φ'.subst (ρ.comp ρ').τ) := fun h => hf2 (ent_trans h (ent_subst h21 _))
    have hL : (L k' ρ).isub ρ' = .hcomp (((B2 k' ρ).inst (a.isub ρ)).isub ρ') ((φ.subst ρ.τ).subst ρ'.τ)
        ((Tm.app (u.isub ρ.up) (a.isub ρ).dshift).isub ρ'.up) ((Tm.app (a0.isub ρ) (a.isub ρ)).isub ρ') := by
      simp only [L, if_neg hf]; rfl
    have hR' : R k'' (ρ.comp ρ') = .hcomp ((B2' k'' (ρ.comp ρ')).inst (a'.isub (ρ.comp ρ'))) (φ'.subst (ρ.comp ρ').τ)
        (.app (u'.isub (ρ.comp ρ').up) (a'.isub (ρ.comp ρ')).dshift)
        (.app (a0'.isub (ρ.comp ρ')) (a'.isub (ρ.comp ρ'))) := by
      simp only [R, if_neg hf2']
    -- the types of the two compositions
    have c1 := hP.coh k' ρ k'' ρ' (A2 k' ρ) (B2 k' ρ) (A2 k'' (ρ.comp ρ')) (B2 k'' (ρ.comp ρ')) (hw k' ρ).1
      (hw k'' (ρ.comp ρ')).1
    have haa2 : RE2 S k' (A2 k' ρ) (a.isub ρ) (a.isub ρ) := RE2.conv hW (hC k' ρ).1 (haaρ k' ρ)
    have haa2σ : RE2 S k'' ((A2 k' ρ).isub ρ') (a.isub (ρ.comp ρ')) (a.isub (ρ.comp ρ')) := by
      have := RE2.isub hW haa2 ρ'; rwa [Tm.isub_isub] at this
    have hX1 : RT2 S k'' (((B2 k' ρ).inst (a.isub ρ)).isub ρ') ((B2 k'' (ρ.comp ρ')).inst (a.isub (ρ.comp ρ'))) := by
      rw [isub_inst, Tm.isub_isub]; exact c1.2 _ _ haa2σ
    have hX2 := (hC k'' (ρ.comp ρ')).2 _ _ (haaρ k'' (ρ.comp ρ'))
    have hXc : TyCode k'' (semK S k'' ((B1.inst a).isub (ρ.comp ρ'))) := tyCode_of_ty hW htyR
    -- `X` related to the restricted type of the applications
    have hXc' : TyCode k'' (semK S k'' ((B1.isub (ρ.comp ρ')).inst (a.isub (ρ.comp ρ')))) := by
      rw [← isub_inst]; exact hXc
    have hYc2 : TyCode k'' (semK S k'' ((B2 k'' (ρ.comp ρ')).inst (a.isub (ρ.comp ρ')))) :=
      RT2.tyCode_r hW hX2 hXc'
    have hXcode : TyCode k'' (semK S k'' (((B2 k' ρ).inst (a.isub ρ)).isub ρ')) := RT2.tyCode_l hW hX1 hYc2
    have hXY : RT2 S k'' (((B2 k' ρ).inst (a.isub ρ)).isub ρ') ((B1.inst a).isub (ρ.comp ρ')) := by
      refine RT2.trans hW hXcode hX1 ?_
      rw [isub_inst]
      exact RT2.symm hW hXc' hX2
    have hXX' : RT2 S k'' (((B2 k' ρ).inst (a.isub ρ)).isub ρ') ((B2' k'' (ρ.comp ρ')).inst (a'.isub (ρ.comp ρ'))) :=
      RT2.trans hW hXcode hX1 ((hw k'' (ρ.comp ρ')).2.2.2 _ _ (hrel2 k'' (ρ.comp ρ')))
    have hK := hIH k' ρ (A2 k' ρ) (B2 k' ρ) (hw k' ρ).1 (a.isub ρ) haa2 k'' ρ' _ hXX'
    have hTyXY := (Comp2_ty_base hXY).2.2.2.2.2
    -- the equality of the two compositions
    have E0 : EqTm S k .one [] (.app (.hcomp T φ u a0) a) (.app (.hcomp T' φ' u' a0') a') (B1.inst a) :=
      EqTm.app (heq.tyConv hR.2) (RE2.typed ha).2.2
    have EL := EqTm.isubS hW (hu k' ρ).2 ρ'
    rw [Tm.isub_isub, Tm.isub_isub] at EL
    have Eall := (EL.symm.trans (EqTm.isubS hW E0 (ρ.comp ρ'))).trans (hu' k'' (ρ.comp ρ')).2
    rw [hL, hR'] at Eall
    rw [hL] at htyL
    rw [hR'] at htyR
    rw [hL, hR']
    -- the tubes, applied, are judgmentally equal
    have htub : EqTm S (k'' + 1) (cof .one ((φ.subst ρ.τ).subst ρ'.τ)).shift []
        ((Tm.app (u.isub ρ.up) (a.isub ρ).dshift).isub ρ'.up) (.app (u'.isub (ρ.comp ρ').up) (a'.isub (ρ.comp ρ')).dshift)
        ((((B2 k' ρ).inst (a.isub ρ)).isub ρ').dshift) := by
      have hfσ := EqTm.cofIsub hW hφs hteq (ρ.comp ρ')
      rw [isub_dshift] at hfσ
      obtain ⟨lσ, hpiσ⟩ := ty_of_tyEq hW (isTyK_of_ty hW (HasTy.isubS hW hty (ρ.comp ρ'))) (hw k'' (ρ.comp ρ')).1.2
        (fun l h => by cases h)
      have e := eqCof_app hW (I.scoped_subst hφs (ρ.comp ρ').sc) hfσ (hw k'' (ρ.comp ρ')).1.2 hpiσ (RE2.typed (hrel2 k'' _)).2.2
      have hcl := closed_of_isTyK hW (Comp2_ty_base hX1).2.2.1
      rw [dshift_eq_isub_closed hcl] at e
      have e' := EqTm.cofConv (I.scoped_subst hφs (ρ.comp ρ').sc) e (TyEq.symm (Comp2_ty_base hX1).2.2.2.2.2)
      rw [isub_app, Tm.isub_isub, ← ISub.up_comp, isub_dshift, Tm.isub_isub, ← I_subst_comp]
      exact e'
    refine RE2.conv hW hXY (hK _ _ _ _ _ _ (htyL.tyConv (TyEq.symm hTyXY)) (htyR.tyConv (TyEq.symm hTyXY))
      (Eall.tyConv (TyEq.symm hTyXY)) htub ?_ ?_ (fun k3 σ3 r r' hr hr' hE hh => ?_) ?_ (fun k3 σ3 hh => ?_)
      (fun k3 σ3 hh => ?_))
    · rw [I_subst_subst]; exact ent_subst h12 (ρ.comp ρ').τ
    · rw [I_subst_subst]; exact ent_subst h21 (ρ.comp ρ').τ
    · -- the tubes, applied
      simp only [Tm.isub_isub, ← ISub.up_comp]
      rw [app_up_dinst, app_up_dinst]
      have hh' : (ival (idEnv k3) (φ.subst ((ρ.comp ρ').comp σ3).τ)).holds := by
        have e : φ.subst ((ρ.comp ρ').comp σ3).τ = ((φ.subst ρ.τ).subst ρ'.τ).subst σ3.τ := by
          rw [I_subst_comp, I_subst_comp]
        rw [e]; exact hh
      have h1 := H1 k3 ((ρ.comp ρ').comp σ3) _ _ (htube k3 _ r r' hr hr' hE hh')
      have hXY3 := RT2.isub hW hXcode hXY σ3
      simp only [Tm.isub_isub] at hXY3
      rw [ISub.comp_assoc] at h1 hXY3 ⊢
      exact RE2.conv' hW hXY3 h1 (RT2.tyCode_l hW hXY3 (RE2.tyCode hW h1))
    · -- the bases, applied
      have h1 := H1 k'' (ρ.comp ρ') _ _ (RE2.isub hW ha0 (ρ.comp ρ'))
      rw [isub_app, Tm.isub_isub, Tm.isub_isub]
      exact RE2.conv' hW hXY h1 hXcode
    · -- the boundaries, applied
      have hh' : (ival (idEnv k3) (φ.subst ((ρ.comp ρ').comp σ3).τ)).holds := by
        have e : φ.subst ((ρ.comp ρ').comp σ3).τ = ((φ.subst ρ.τ).subst ρ'.τ).subst σ3.τ := by
          rw [I_subst_comp, I_subst_comp]
        rw [e]; exact hh
      simp only [Tm.isub_isub, ← ISub.up_comp]
      rw [app_up_dinst]
      have h1 := H1 k3 ((ρ.comp ρ').comp σ3) _ _ (hbd k3 _ hh')
      have hXY3 := RT2.isub hW hXcode hXY σ3
      simp only [Tm.isub_isub] at hXY3
      rw [isub_app, Tm.isub_isub, Tm.isub_isub]
      rw [ISub.comp_assoc] at h1 hXY3 ⊢
      exact RE2.conv' hW hXY3 h1 (RT2.tyCode_l hW hXY3 (RE2.tyCode hW h1))
    · have hh' : (ival (idEnv k3) (φ.subst ((ρ.comp ρ').comp σ3).τ)).holds := by
        have e : φ.subst ((ρ.comp ρ').comp σ3).τ = ((φ.subst ρ.τ).subst ρ'.τ).subst σ3.τ := by
          rw [I_subst_comp, I_subst_comp]
        rw [e]; exact hh
      simp only [Tm.isub_isub, ← ISub.up_comp]
      rw [app_up_dinst]
      have h1 := H1 k3 ((ρ.comp ρ').comp σ3) _ _ (hbd' k3 _ hh')
      have hXY3 := RT2.isub hW hXcode hXY σ3
      simp only [Tm.isub_isub] at hXY3
      rw [isub_app, Tm.isub_isub, Tm.isub_isub]
      rw [ISub.comp_assoc] at h1 hXY3 ⊢
      exact RE2.conv' hW hXY3 h1 (RT2.tyCode_l hW hXY3 (RE2.tyCode hW h1))


theorem PiStr.isub {T T' : Tm} (hP : PiStr S k T T') (σ : ISub k' k) : PiStr S k' (T.isub σ) (T'.isub σ) where
  tyEq := hP.tyEq.isub hW σ
  whnf k'' ρ := by simpa only [Tm.isub_isub] using hP.whnf k'' (σ.comp ρ)
  coh k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh k1 (σ.comp ρ) k2 ρ' A1 B1 A2 B2 h1 h2
  elim k1 ρ A1 B1 f f' h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    exact hP.elim k1 (σ.comp ρ) A1 B1 f f' h1 h2
  coh' k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 := by
    rw [Tm.isub_isub] at h1 h2
    rw [← ISub.comp_assoc] at h2
    exact hP.coh' k1 (σ.comp ρ) k2 ρ' A1 B1 A2 B2 h1 h2

omit hW in
theorem Tube2.isub {T u u' : Tm} {φ : I} (h : Tube2 S k T φ u u') (σ : ISub k' k) :
    Tube2 S k' (T.isub σ) (φ.subst σ.τ) (u.isub σ.up) (u'.isub σ.up) := by
  intro k'' ρ r r' hr hr' hE hh
  have := h k'' (σ.comp ρ) r r' hr hr' hE (by rwa [I_subst_comp])
  rwa [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]

omit hW in
theorem bdry_isub {T u a' : Tm} {φ : I} (h : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ)) (ρ : ISub k' k) :
    ∀ k'' (σ : ISub k'' k'), (ival (idEnv k'') ((φ.subst ρ.τ).subst σ.τ)).holds →
      RE2 S k'' ((T.isub ρ).isub σ) (((u.isub ρ.up).isub σ.up).dinst .zero) ((a'.isub ρ).isub σ) := by
  intro k'' σ hh
  have := h k'' (ρ.comp σ) (by rwa [I_subst_comp])
  rwa [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]

omit hW in
theorem bdry_isub' {T u' a : Tm} {φ : I} (h : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) (ρ : ISub k' k) :
    ∀ k'' (σ : ISub k'' k'), (ival (idEnv k'') ((φ.subst ρ.τ).subst σ.τ)).holds →
      RE2 S k'' ((T.isub ρ).isub σ) ((a.isub ρ).isub σ) (((u'.isub ρ.up).isub σ.up).dinst .zero) := by
  intro k'' σ hh
  have := h k'' (ρ.comp σ) (by rwa [I_subst_comp])
  rwa [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, ← ISub.up_comp]

/-- Composition at a pair of related types whose normal forms are Π-types. -/
theorem kanH2_pi {T T' : Tm} (hP : PiStr S k T T')
    (hIH : ∀ k' (ρ : ISub k' k) A1 B1, RedT S k' (T.isub ρ) (.pi A1 B1) → ∀ b, RE2 S k' A1 b b →
      ∀ k'' (ρ' : ISub k'' k') X', RT2 S k'' ((B1.inst b).isub ρ') X' → KanH2 S k'' ((B1.inst b).isub ρ') X')
    (hintro : ∀ t t', EB S k T t t' → (∀ k' (ρ : ISub k' k) A1 B1, RedT S k' (T.isub ρ) (.pi A1 B1) →
      ∀ a a', RE2 S k' A1 a a' → RE2 S k' (B1.inst a) (.app (t.isub ρ) a) (.app (t'.isub ρ) a')) →
      RE2 S k T t t') : KanH2 S k T T' := by
  intro φ φ' u u' a0 a0' hty hty' heq hteq h12 h21 htube ha0 hbd hbd'
  obtain ⟨l0, ⟨-, hφs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  refine hintro _ _ ⟨hty, hty', heq⟩ fun k' ρ A1 B1 hR a a' ha => ?_
  have hteqρ := EqTm.cofIsub hW hφs hteq ρ
  rw [isub_dshift] at hteqρ
  refine kanH2_pi_core hW (hP.isub hW ρ) (fun k1 ρ1 A3 B3 h3 b hb k2 ρ2 X' hX' => ?_) (HasTy.isubS hW hty ρ)
    (HasTy.isubS hW hty' ρ) (EqTm.isubS hW heq ρ) hteqρ (ent_subst h12 ρ.τ) (ent_subst h21 ρ.τ) (htube.isub ρ)
    (RE2.isub hW ha0 ρ) (bdry_isub hbd ρ) (bdry_isub' hbd' ρ) hR ha
  rw [Tm.isub_isub] at h3
  exact hIH k1 (ρ.comp ρ1) A3 B3 h3 b hb k2 ρ2 X' hX'


omit hW in
theorem Comp2_ty_iff {m : ℕ} {X : V} {g : Hom k' m} {A A' : Tm} (hne : X ≠ ∅) (hb : semK S k' A = res g X) :
    (Comp2 S X m k' g).ty A A' ↔ RT2 S k' A A' := by
  unfold RT2; rw [hb, Comp2_eq_res hne]

omit hW in
theorem Comp2_el_iff {m : ℕ} {X : V} {g : Hom k' m} {A t t' : Tm} (hne : X ≠ ∅) (hb : semK S k' A = res g X) :
    (Comp2 S X m k' g).el A t t' ↔ RE2 S k' A t t' := by
  unfold RE2; rw [hb, Comp2_eq_res hne]

omit hW in
theorem Comp2_ty_RT2 {m : ℕ} {X : V} {g : Hom k' m} {A A' : Tm} (h : (Comp2 S X m k' g).ty A A') : RT2 S k' A A' :=
  (Comp2_ty_iff (Comp2_ty_base h).1 (Comp2_ty_base h).2.2.2.1).1 h

/-- Related types whose normal form is a Π-type have the structure `PiStr`. -/
theorem PiStr_of {T T' A B : Tm} {l : ℕ} (h : RT2 S k T T') (hR : RedT S k T (.pi A B))
    (hpiK : HasTy S k .one [] (.pi A B) (.univ l)) : PiStr S k T T' := by
  have hAne := semK_ne hW (HasTy.piDom hpiK)
  have hX : semK S k T = piC k (semK S k A)
      (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) :=
    (semK_tyEq hW hR.2).trans (semK_piT hW hpiK)
  have hT := h
  unfold RT2 at hT
  rw [hX, Comp2_piC _ _ hAne] at hT
  obtain ⟨hbase, hall, hcoh, hcoh'⟩ := hT
  -- the domain relation at a restriction, and its base
  refine ⟨hbase.2.2.2.2, fun k' ρ => ?_, fun k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 => ?_, fun k' ρ A1 B1 f f' h1 hf => ?_,
    fun k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2 => ?_⟩
  rotate_right
  · obtain ⟨c1, c2⟩ := hcoh' k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2
    refine ⟨Comp2_ty_RT2 c1, fun a a' ha => Comp2_ty_RT2 (c2 a a' ?_)⟩
    exact (Comp2_el_iff hAne (Comp2_ty_base c1).2.2.2.1).2 ha
  · obtain ⟨A1, B1, A1', B1', h1, h2, h3, h4⟩ := hall k' ρ
    refine ⟨A1, B1, A1', B1', h1, h2, Comp2_ty_RT2 h3, fun a a' ha => Comp2_ty_RT2 (h4 a a' ?_)⟩
    exact (Comp2_el_iff hAne (Comp2_ty_base h3).2.2.2.1).2 ha
  · obtain ⟨c1, c2⟩ := hcoh k1 ρ k2 ρ' A1 B1 A2 B2 h1 h2
    refine ⟨Comp2_ty_RT2 c1, fun a a' ha => Comp2_ty_RT2 (c2 a a' ?_)⟩
    exact (Comp2_el_iff hAne (Comp2_ty_base c1).2.2.2.1).2 ha
  · -- the elimination of related elements
    have hTρ : semK S k' (T.isub ρ) = res ρ.hom (semK S k T) :=
      semK_isubTy hW (Comp2_ty_base (show RT2 S k T T' from h)).2.1 ρ
    have hf2 : (Comp2 S (piC k (semK S k A) (famV k (semK S k A) fun k' g a =>
        sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a))) k k' ρ.hom).el (T.isub ρ) f f' := by
      rw [Comp2_eq_res (show piC k (semK S k A) (famV k (semK S k A) fun k' g a =>
        sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) ≠ ∅ from mkKV_ne_empty _), ← hX, ← hTρ]
      exact hf
    obtain ⟨A3, B3, h3, happ⟩ := piC_el_at hAne hW hf2
    obtain ⟨rfl, rfl⟩ : A3 = A1 ∧ B3 = B1 := by
      have := RedW.unique h3.1 h1.1; injection this; constructor <;> assumption
    obtain ⟨A4, B4, A4', B4', h4, -, hd, hc⟩ := hall k' ρ
    obtain ⟨rfl, rfl⟩ : A4 = A3 ∧ B4 = B3 := by
      have := RedW.unique h4.1 h1.1; injection this; constructor <;> assumption
    intro a a' ha
    have ha' : (Comp2 S (semK S k A) k k' ((Hom.id k).comp ρ.hom)).el A4 a a' :=
      (Comp2_el_iff hAne (Comp2_ty_base hd).2.2.2.1).2 ha
    have x := happ a a' (by rwa [Hom.id_comp] at ha')
    have haa : (Comp2 S (semK S k A) k k' ((Hom.id k).comp ρ.hom)).el A4 a a :=
      (per2_tyCode hW (tyCode_of_univ hW (HasTy.piDom hpiK)) k' _ |>.reflEl) hd ha'
    have hcb := Comp2_ty_base (hc a a haa)
    rw [Hom.id_comp] at hcb
    exact (Comp2_el_iff hcb.1 hcb.2.2.2.1).1 x


/-- Related elements of a type whose normal form is a Π-type, through their applications. -/
theorem RE2_piW_intro {T A B t t' : Tm} {l : ℕ} (hTT : RT2 S k T T) (hR : RedT S k T (.pi A B))
    (hpiK : HasTy S k .one [] (.pi A B) (.univ l)) (hE : EB S k T t t')
    (happ : ∀ k' (ρ : ISub k' k) A1 B1, RedT S k' (T.isub ρ) (.pi A1 B1) →
      ∀ a a', RE2 S k' A1 a a' → RE2 S k' (B1.inst a) (.app (t.isub ρ) a) (.app (t'.isub ρ) a')) :
    RE2 S k T t t' := by
  have hAne := semK_ne hW (HasTy.piDom hpiK)
  have hX : semK S k T = piC k (semK S k A)
      (famV k (semK S k A) fun k' g a => sem S B k' ((idEnv k).restr g) (TEnv.cons (TEnv.restr (γ0 k) g) a)) :=
    (semK_tyEq hW hR.2).trans (semK_piT hW hpiK)
  have hT := hTT
  unfold RT2 at hT
  rw [hX, Comp2_piC _ _ hAne] at hT
  obtain ⟨-, hall, -, -⟩ := hT
  unfold RE2
  rw [hX, Comp2_piC _ _ hAne]
  refine ⟨hE, ?_, hE, fun k' ρ => ?_⟩
  · rw [← hX, res_id (by rw [hX]; exact isKV_mkKV _)]; exact mem_of_ty hW hE.1
  obtain ⟨A1, B1, A1', B1', h1, -, hd, hc⟩ := hall k' ρ
  refine ⟨A1, B1, h1, fun a a' ha => ?_⟩
  simp only [ISub.id_comp, Hom.id_comp] at ha hd hc ⊢
  have hb := (Comp2_ty_base hd).2.2.2.1
  have haR : RE2 S k' A1 a a' := (Comp2_el_iff hAne hb).1 ha
  have x := happ k' ρ A1 B1 h1 a a' haR
  have haa := (per2_tyCode hW (tyCode_of_univ hW (HasTy.piDom hpiK)) k' ρ.hom).reflEl hd ha
  have hcb := Comp2_ty_base (hc a a haa)
  rw [ISub.hom_id]
  exact (Comp2_el_iff hcb.1 hcb.2.2.2.1).2 x

end

end Model.Whnf
