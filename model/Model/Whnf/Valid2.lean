import Model.Whnf.CSub2

/-!
# Semantic validity of judgments

`Valid2 S Ψ Φ Γ t u A`: at every related closing substitution, the instances of `A` are related types
and the left instance of `t` is related to the right instance of `u`. The fundamental lemma shows
that every derivable equation is valid; this file has the validity of the structural rules and of the
rules of the type formers without Kan operations.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-- Semantic validity of an equation. -/
def Valid2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t u A : Tm) : Prop :=
  ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L A) (c.R A) ∧ RE2 S k (c.L A) (c.L t) (c.R u)

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem Valid2.tyCode {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) (c : CSub2 S Ψ Φ Γ k) :
    TyCode k (semK S k (c.L A)) :=
  RE2.tyCode hW (h k c).2

/-- The right instances, related at the left type. -/
theorem Valid2.right {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) (c : CSub2 S Ψ Φ Γ k) :
    RE2 S k (c.L A) (c.R t) (c.R u) :=
  RE2.conv hW (RT2.symm hW (h.tyCode hW c) (h k c).1) (h k (c.diagR hW)).2

theorem valid_symm {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) : Valid2 S Ψ Φ Γ u t A := by
  intro k c
  obtain ⟨hT, h1⟩ := h k c
  have hX := h.tyCode hW c
  have hTL := RT2.refl hW hX hT
  have h2 := (h k (c.diagL hW)).2
  have h3 := h.right hW c
  refine ⟨hT, ?_⟩
  exact RE2.trans hW hTL (RE2.symm hW hTL h2) (RE2.trans hW hTL h1 (RE2.symm hW hTL h3))

theorem valid_trans {t u v A : Tm} (h1 : Valid2 S Ψ Φ Γ t u A) (h2 : Valid2 S Ψ Φ Γ u v A) :
    Valid2 S Ψ Φ Γ t v A := by
  intro k c
  obtain ⟨hT, a⟩ := h1 k c
  have hTL := RT2.refl hW (h1.tyCode hW c) hT
  exact ⟨hT, RE2.trans hW hTL a (h2.right hW c)⟩

/-- A valid type, at the universe. -/
theorem Valid2.ty {A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ A B (.univ l)) (c : CSub2 S Ψ Φ Γ k) :
    RT2 S k (c.L A) (c.R B) :=
  RE2_univ_ty hW (h k c).2

theorem valid_conv {t u A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ t u A) (hAB : Valid2 S Ψ Φ Γ A B (.univ l)) :
    Valid2 S Ψ Φ Γ t u B := by
  intro k c
  obtain ⟨hT, a⟩ := h k c
  have hX := h.tyCode hW c
  have hLR := hAB.ty hW c
  have hLL := hAB.ty hW (c.diagL hW)
  refine ⟨RT2.trans hW (RT2.semK_eq hW hLL ▸ hX) (RT2.symm hW hX hLL) hLR, RE2.conv hW hLL a⟩

theorem valid_restrict {Φ' : I} {t u A : Tm} (he : I.Entails Φ' Φ) (h : Valid2 S Ψ Φ Γ t u A) :
    Valid2 S Ψ Φ' Γ t u A := fun k c => h k (c.restrictTo he)

theorem valid_var {x : ℕ} {A : Tm} (h : Γ.lookup x = some A) : Valid2 S Ψ Φ Γ (.var x) (.var x) A :=
  fun k c => ⟨c.lookT x A h, c.look x A h⟩

theorem valid_univ {l : ℕ} (hl : l + 1 ≤ maxLevel) : Valid2 S Ψ Φ Γ (.univ l) (.univ l) (.univ (l + 1)) := by
  intro k c
  have hty : HasTy S k .one [] (.univ l) (.univ (l + 1)) := HasTy.univ hl (Wf.nil trivial)
  exact ⟨RT2_univ hW, RE2_univ_of hW ⟨hty, hty, EqTm.refl hty⟩ (RT2_univ hW)⟩

theorem valid_cumul {A B : Tm} {l : ℕ} (hl : l + 1 ≤ maxLevel) (h : Valid2 S Ψ Φ Γ A B (.univ l)) :
    Valid2 S Ψ Φ Γ A B (.univ (l + 1)) := by
  intro k c
  obtain ⟨he, hm, hrt⟩ := (RE2_univ_iff hW).1 (h k c).2
  refine ⟨RT2_univ hW, (RE2_univ_iff hW).2 ⟨⟨HasTy.cumul hl he.1, HasTy.cumul hl he.2.1, EqTm.cumul hl he.2.2⟩,
    ?_, hrt⟩⟩
  have hm' := ZFSet.mem_sep.1 hm
  exact ZFSet.mem_sep.2 ⟨Vt_subset_succ l (by unfold maxLevel at hl; omega) hm'.1, hm'.2.cumul⟩


/-- A valid type equation relates the two instances of its left side. -/
theorem Valid2.tySelf {A A' : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ A A' (.univ l)) (c : CSub2 S Ψ Φ Γ k) :
    RT2 S k (c.L A) (c.R A) := by
  have h1 := h.ty hW c
  have h2 := h.ty hW (c.diagR hW)
  have hX : TyCode k (semK S k (c.L A)) := tyCode_of_univ hW (RE2.typed (h k c).2).1
  have hX' : TyCode k (semK S k (c.R A)) := tyCode_of_univ hW (RE2.typed (h k (c.diagR hW)).2).1
  exact RT2.trans hW hX h1 (RT2.symm hW hX' h2)

/-- A valid type equation, at a restriction. -/
theorem Valid2.tyRestr {A A' : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ A A' (.univ l)) (c : CSub2 S Ψ Φ Γ k)
    (σ : ISub k' k) : RT2 S k' ((c.L A).isub σ) ((c.R A').isub σ) := by
  have := h.ty hW (c.restr hW σ)
  rwa [CSub2.restr_L, CSub2.restr_R] at this

/-! ### `Π` -/

theorem valid_pi {A A' B B' : Tm} {l : ℕ} (hA : Valid2 S Ψ Φ Γ A A' (.univ l))
    (hB : Valid2 S Ψ Φ (A :: Γ) B B' (.univ l)) (hty : HasTy0 S Ψ Φ Γ (.pi A B) (.univ l))
    (hty' : HasTy0 S Ψ Φ Γ (.pi A' B') (.univ l)) (heq : EqTm0 S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l)) :
    Valid2 S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l) := by
  intro k c
  refine ⟨RT2_univ hW, RE2_univ_of hW ⟨c.ty hW hty, c.tyR hW hty', c.eq hW heq⟩
    (RT2_pi_intro hW (c.ty hW hty) (c.tyR hW hty') (c.eq hW heq) (fun k' σ => hA.tyRestr hW c σ)
      (fun k' σ a a' ha => ?_))⟩
  rw [← CSub2.restr_L hW c σ] at ha
  have hAA := hA.tySelf hW (c.restr hW σ)
  have := hB.ty hW ((c.restr hW σ).ext A a a' ha hAA)
  rw [subst_up_isub_inst, subst_up_isub_inst]
  exact this


/-- The instances of a valid type, related at its own code (left and left). -/
theorem Valid2.tyLL {t u A : Tm} (h : Valid2 S Ψ Φ Γ t u A) (c : CSub2 S Ψ Φ Γ k) : RT2 S k (c.L A) (c.L A) :=
  RT2.refl hW (h.tyCode hW c) (h k c).1

omit hW in
theorem isub_lam (A1 b : Tm) (σ : ISub k' k) : (Tm.lam A1 b).isub σ = .lam (A1.isub σ) (b.isub σ) := by
  simp only [Tm.isub, Tm.subst, up_var]

/-- β-reduction of a closed application, at every restriction. -/
theorem stable_beta {X A1 b a : Tm} (hty : HasTy S k .one [] (.app (.lam A1 b) a) X) :
    StableE S k X (.app (.lam A1 b) a) (b.inst a) := by
  intro k' σ
  have hσ := HasTy.isubS hW hty σ
  rw [isub_app, isub_lam] at hσ ⊢
  rw [isub_inst]
  exact ⟨.step (by simp [step]) (.refl _), EqTm.piBeta hσ⟩


/-- Expansion on both sides, at the level of `RE2`. -/
theorem RE2.expand2 {A t t' u u' : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A) (hs : StableE S k A t u) (hs' : StableE S k A t' u') (h : RE2 S k A u u') :
    RE2 S k A t t' :=
  el_expandS2 hW (RE2.tyCode hW h) hAA ht ht' (RE2.typed h).1 hs hs' h

/-- Reduction on the right, at the level of `RE2`. -/
theorem RE2.reduceR {A t t' u' : Tm} (hAA : RT2 S k A A) (h : RE2 S k A t t') (hs : StableE S k A t' u')
    (hu : HasTy S k .one [] u' A) : RE2 S k A t u' :=
  el_reduceSR hW (RE2.tyCode hW h) hAA h hs hu

/-- Reduction on the left, at the level of `RE2`. -/
theorem RE2.reduceL {A t t' u : Tm} (hAA : RT2 S k A A) (h : RE2 S k A t t') (hs : StableE S k A t u)
    (hu : HasTy S k .one [] u A) : RE2 S k A u t' :=
  el_reduceSL hW (RE2.tyCode hW h) hAA h hs hu

theorem valid_lam {A B t t' : Tm} {l : ℕ} (hpi : Valid2 S Ψ Φ Γ (.pi A B) (.pi A B) (.univ l))
    (ht : Valid2 S Ψ Φ (A :: Γ) t t' B) (hty : HasTy0 S Ψ Φ Γ (.lam A t) (.pi A B))
    (hty' : HasTy0 S Ψ Φ Γ (.lam A t') (.pi A B)) (heq : EqTm0 S Ψ Φ Γ (.lam A t) (.lam A t') (.pi A B)) :
    Valid2 S Ψ Φ Γ (.lam A t) (.lam A t') (.pi A B) := by
  intro k c
  have hpiTy : HasTy S k .one [] (c.L (.pi A B)) (.univ l) := (RE2.typed (hpi k c).2).1
  refine ⟨hpi.ty hW c, RE2_pi_intro hW hpiTy ⟨c.ty hW hty, c.tyR' hW hty', c.eq hW heq⟩ fun k' σ a a' ha => ?_⟩
  have hP : RT2 S k' ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ)
      ((Tm.pi (c.R A) (B.subst (Tm.up c.γ') c.σ'.τ)).isub σ) := hpi.tyRestr hW c σ
  have hPL : RT2 S k' ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := hpi.tyRestr hW (c.diagL hW) σ
  simp only [isub_pi] at hP hPL
  have hI := RT2_pi_inv hW hP
  have hIL := RT2_pi_inv hW hPL
  have haa := RE2.trans hW hIL.1 ha (RE2.symm hW hIL.1 ha)
  have hXX := hIL.2 a a haa
  have hTyE := (Comp2_ty_base (hIL.2 a a' ha)).2.2.2.2.2
  have hlamL : HasTy S k' .one [] ((Tm.lam (c.L A) (t.subst (Tm.up c.γ) c.σ.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := HasTy.isubS hW (c.ty hW hty) σ
  have hlamR : HasTy S k' .one [] ((Tm.lam (c.R A) (t'.subst (Tm.up c.γ') c.σ'.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := HasTy.isubS hW (c.tyR' hW hty') σ
  rw [isub_pi, isub_lam] at hlamL hlamR
  have happL := HasTy.app hlamL (RE2.typed ha).1
  have happR := (HasTy.app hlamR (RE2.typed ha).2.1).tyConv (TyEq.symm hTyE)
  have hA1 := hI.1
  have ha1 := ha
  rw [← CSub2.restr_L hW c σ] at ha1 hA1
  rw [← CSub2.restr_R hW c σ] at hA1
  have hmain := (ht k' ((c.restr hW σ).ext A a a' ha1 hA1)).2
  have hm : RE2 S k' (((B.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a) (((t.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a)
      (((t'.subst (Tm.up c.γ') c.σ'.τ).isub σ).inst a') := by
    rw [subst_up_isub_inst, subst_up_isub_inst, subst_up_isub_inst]; exact hmain
  show RE2 S k' _ (.app ((Tm.lam (c.L A) (t.subst (Tm.up c.γ) c.σ.τ)).isub σ) a)
    (.app ((Tm.lam (c.R A) (t'.subst (Tm.up c.γ') c.σ'.τ)).isub σ) a')
  rw [isub_lam, isub_lam]
  exact RE2.expand2 hW hXX happL happR (stable_beta hW happL) (stable_beta hW happR) hm


theorem valid_app {A B f f' a a' : Tm} (hf : Valid2 S Ψ Φ Γ f f' (.pi A B)) (ha : Valid2 S Ψ Φ Γ a a' A) :
    Valid2 S Ψ Φ Γ (.app f a) (.app f' a') (B.inst a) := by
  intro k c
  have hP : RT2 S k (.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) (.pi (c.R A) (B.subst (Tm.up c.γ') c.σ'.τ)) :=
    (hf k c).1
  have hI := RT2_pi_inv hW hP
  have hAA := RT2.refl hW (ha.tyCode hW c) hI.1
  have haR : RE2 S k (c.L A) (c.L a) (c.R a) := RE2.trans hW hAA (ha k c).2 (RE2.symm hW hAA (ha.right hW c))
  simp only [CSub2.L, CSub2.R, inst_subst]
  exact ⟨hI.2 _ _ haR, RE2_pi_elim hW (hf k c).2 (ha k c).2⟩

/-- A computation rule: the right instances of `t` reduce stably to those of `u`. -/
theorem valid_redR {t u T : Tm} (h : Valid2 S Ψ Φ Γ t t T) (hu : HasTy0 S Ψ Φ Γ u T)
    (hs : ∀ k (c : CSub2 S Ψ Φ Γ k), StableE S k (c.L T) (c.R t) (c.R u)) : Valid2 S Ψ Φ Γ t u T :=
  fun k c => ⟨(h k c).1, RE2.reduceR hW (h.tyLL hW c) (h k c).2 (hs k c) (c.tyR' hW hu)⟩

theorem valid_piBeta {A b a T : Tm} (h : Valid2 S Ψ Φ Γ (.app (.lam A b) a) (.app (.lam A b) a) T)
    (hty : HasTy0 S Ψ Φ Γ (.app (.lam A b) a) T) (hu : HasTy0 S Ψ Φ Γ (b.inst a) T) :
    Valid2 S Ψ Φ Γ (.app (.lam A b) a) (b.inst a) T := by
  refine valid_redR hW h hu fun k c => ?_
  have := stable_beta hW (c.tyR' hW hty)
  simp only [CSub2.R, inst_subst]
  exact this


omit hW in
theorem eta_body (f a : Tm) (γ : ℕ → Tm) (τ : ℕ → I) (σ : ISub k' k) :
    (((Tm.app f.shift (.var 0)).subst (Tm.up γ) τ).isub σ).inst a = .app ((f.subst γ τ).isub σ) a := by
  rw [subst_up_isub_inst, subst_isub2]
  simp only [Tm.subst, shift_consT]
  rfl

/-- Expansion on the right, at the level of `RE2`. -/
theorem RE2.expandR {A t t' u' : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A) (hs : StableE S k A t' u') (h : RE2 S k A t u') : RE2 S k A t t' :=
  el_expandSR hW (RE2.tyCode hW h) hAA ht ht' hs h

theorem valid_piEta {A B f : Tm} (hf : Valid2 S Ψ Φ Γ f f (.pi A B)) (hty : HasTy0 S Ψ Φ Γ f (.pi A B))
    (hu : HasTy0 S Ψ Φ Γ (.lam A (.app f.shift (.var 0))) (.pi A B))
    (heq : EqTm0 S Ψ Φ Γ f (.lam A (.app f.shift (.var 0))) (.pi A B)) :
    Valid2 S Ψ Φ Γ f (.lam A (.app f.shift (.var 0))) (.pi A B) := by
  intro k c
  have hft := c.ty hW hty
  obtain ⟨l, hpiTy⟩ := ty_of_tyEq hW (isTyK_of_ty hW hft) (TyEq.refl _) (fun l h => by cases h)
  refine ⟨(hf k c).1, RE2_pi_intro hW hpiTy ⟨hft, c.tyR' hW hu, c.eq hW heq⟩ fun k' σ a a' ha => ?_⟩
  have hfσ : RE2 S k' ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) ((c.L f).isub σ) ((c.R f).isub σ) :=
    RE2.isub hW (hf k c).2 σ
  have hPL : RT2 S k' ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := RT2.isub hW (hf.tyCode hW c) (hf.tyLL hW c) σ
  simp only [isub_pi] at hfσ hPL
  have hIL := RT2_pi_inv hW hPL
  have haa := RE2.trans hW hIL.1 ha (RE2.symm hW hIL.1 ha)
  have hXX := hIL.2 a a haa
  have hTyE := (Comp2_ty_base (hIL.2 a a' ha)).2.2.2.2.2
  have hel := RE2_pi_elim hW hfσ ha
  have hlamR : HasTy S k' .one [] ((Tm.lam (c.R A) ((Tm.app f.shift (.var 0)).subst (Tm.up c.γ') c.σ'.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := HasTy.isubS hW (c.tyR' hW hu) σ
  rw [isub_pi, isub_lam] at hlamR
  have happR := (HasTy.app hlamR (RE2.typed ha).2.1).tyConv (TyEq.symm hTyE)
  have hs := stable_beta hW happR
  rw [eta_body] at hs
  show RE2 S k' _ _ (.app ((Tm.lam (c.R A) ((Tm.app f.shift (.var 0)).subst (Tm.up c.γ') c.σ'.τ)).isub σ) a')
  rw [isub_lam]
  exact RE2.expandR hW hXX (RE2.typed hel).1 happR hs hel


/-- A type equation is valid once its instances are related types. -/
theorem valid_univ_of {X X' : Tm} {l : ℕ} (hty : HasTy0 S Ψ Φ Γ X (.univ l)) (hty' : HasTy0 S Ψ Φ Γ X' (.univ l))
    (heq : EqTm0 S Ψ Φ Γ X X' (.univ l)) (h : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L X) (c.R X')) :
    Valid2 S Ψ Φ Γ X X' (.univ l) :=
  fun k c => ⟨RT2_univ hW, RE2_univ_of hW ⟨c.ty hW hty, c.tyR hW hty', c.eq hW heq⟩ (h k c)⟩

theorem valid_piInjDom {A A' B B' : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l))
    (hty : HasTy0 S Ψ Φ Γ A (.univ l)) (hty' : HasTy0 S Ψ Φ Γ A' (.univ l))
    (heq : EqTm0 S Ψ Φ Γ A A' (.univ l)) : Valid2 S Ψ Φ Γ A A' (.univ l) :=
  valid_univ_of hW hty hty' heq fun k c => (RT2_pi_inv hW (h.ty hW c)).1

theorem valid_piInjCod {A A' B B' a : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l))
    (ha : Valid2 S Ψ Φ Γ a a A) (hty : HasTy0 S Ψ Φ Γ (B.inst a) (.univ l))
    (hty' : HasTy0 S Ψ Φ Γ (B'.inst a) (.univ l)) (heq : EqTm0 S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l)) :
    Valid2 S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l) := by
  refine valid_univ_of hW hty hty' heq fun k c => ?_
  simp only [CSub2.L, CSub2.R, inst_subst]
  exact (RT2_pi_inv hW (h.ty hW c)).2 _ _ (ha k c).2

theorem valid_sigmaInjDom {A A' B B' : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l))
    (hty : HasTy0 S Ψ Φ Γ A (.univ l)) (hty' : HasTy0 S Ψ Φ Γ A' (.univ l))
    (heq : EqTm0 S Ψ Φ Γ A A' (.univ l)) : Valid2 S Ψ Φ Γ A A' (.univ l) :=
  valid_univ_of hW hty hty' heq fun k c => (RT2_sigma_inv hW (h.ty hW c)).1

theorem valid_sigmaInjCod {A A' B B' a : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l))
    (ha : Valid2 S Ψ Φ Γ a a A) (hty : HasTy0 S Ψ Φ Γ (B.inst a) (.univ l))
    (hty' : HasTy0 S Ψ Φ Γ (B'.inst a) (.univ l)) (heq : EqTm0 S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l)) :
    Valid2 S Ψ Φ Γ (B.inst a) (B'.inst a) (.univ l) := by
  refine valid_univ_of hW hty hty' heq fun k c => ?_
  simp only [CSub2.L, CSub2.R, inst_subst]
  exact (RT2_sigma_inv hW (h.ty hW c)).2 _ _ (ha k c).2


/-! ### `Σ` -/

theorem valid_sigma {A A' B B' : Tm} {l : ℕ} (hA : Valid2 S Ψ Φ Γ A A' (.univ l))
    (hB : Valid2 S Ψ Φ (A :: Γ) B B' (.univ l)) (hty : HasTy0 S Ψ Φ Γ (.sigma A B) (.univ l))
    (hty' : HasTy0 S Ψ Φ Γ (.sigma A' B') (.univ l)) (heq : EqTm0 S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l)) :
    Valid2 S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l) := by
  refine valid_univ_of hW hty hty' heq fun k c => RT2_sigma_intro hW (c.ty hW hty) (c.tyR hW hty') (c.eq hW heq)
    (fun k' σ => hA.tyRestr hW c σ) (fun k' σ a a' ha => ?_)
  rw [← CSub2.restr_L hW c σ] at ha
  have := hB.ty hW ((c.restr hW σ).ext A a a' ha (hA.tySelf hW (c.restr hW σ)))
  rw [subst_up_isub_inst, subst_up_isub_inst]
  exact this

theorem stable_fstBeta {X a b : Tm} (hty : HasTy S k .one [] (.fst (.pair a b)) X) :
    StableE S k X (.fst (.pair a b)) a := fun k' σ => by
  have hσ : HasTy S k' .one [] (.fst (.pair (a.isub σ) (b.isub σ))) (X.isub σ) := HasTy.isubS hW hty σ
  show Red S (.fst (.pair (a.isub σ) (b.isub σ))) _ ∧ _
  exact ⟨.step (by simp [step]) (.refl _), EqTm.fstBeta hσ⟩

theorem stable_sndBeta {X a b : Tm} (hty : HasTy S k .one [] (.snd (.pair a b)) X) :
    StableE S k X (.snd (.pair a b)) b := fun k' σ => by
  have hσ : HasTy S k' .one [] (.snd (.pair (a.isub σ) (b.isub σ))) (X.isub σ) := HasTy.isubS hW hty σ
  show Red S (.snd (.pair (a.isub σ) (b.isub σ))) _ ∧ _
  exact ⟨.step (by simp [step]) (.refl _), EqTm.sndBeta hσ⟩

theorem valid_fst {A B p p' : Tm} (hp : Valid2 S Ψ Φ Γ p p' (.sigma A B)) :
    Valid2 S Ψ Φ Γ (.fst p) (.fst p') A := fun k c =>
  ⟨(RT2_sigma_inv hW (show RT2 S k (.sigma _ _) (.sigma _ _) from (hp k c).1)).1,
    (RE2_sigma_elim hW (show RE2 S k (.sigma _ _) _ _ from (hp k c).2)).1⟩

theorem valid_snd {A B p p' : Tm} (hp : Valid2 S Ψ Φ Γ p p' (.sigma A B)) :
    Valid2 S Ψ Φ Γ (.snd p) (.snd p') (B.inst (.fst p)) := by
  intro k c
  have hP : RT2 S k (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) (.sigma (c.R A) (B.subst (Tm.up c.γ') c.σ'.τ)) :=
    (hp k c).1
  have hPP := RT2.refl hW (hp.tyCode hW c) hP
  have hpR : RE2 S k (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) (c.L p) (c.R p) :=
    RE2.trans hW hPP (hp k c).2 (RE2.symm hW hPP (hp.right hW c))
  simp only [CSub2.L, CSub2.R, inst_subst]
  exact ⟨(RT2_sigma_inv hW hP).2 _ _ (RE2_sigma_elim hW hpR).1, (RE2_sigma_elim hW (hp k c).2).2⟩

theorem valid_fstBeta {a b T : Tm} (h : Valid2 S Ψ Φ Γ (.fst (.pair a b)) (.fst (.pair a b)) T)
    (hty : HasTy0 S Ψ Φ Γ (.fst (.pair a b)) T) (hu : HasTy0 S Ψ Φ Γ a T) :
    Valid2 S Ψ Φ Γ (.fst (.pair a b)) a T :=
  valid_redR hW h hu fun k c => stable_fstBeta hW (c.tyR' hW hty)

theorem valid_sndBeta {a b T : Tm} (h : Valid2 S Ψ Φ Γ (.snd (.pair a b)) (.snd (.pair a b)) T)
    (hty : HasTy0 S Ψ Φ Γ (.snd (.pair a b)) T) (hu : HasTy0 S Ψ Φ Γ b T) :
    Valid2 S Ψ Φ Γ (.snd (.pair a b)) b T :=
  valid_redR hW h hu fun k c => stable_sndBeta hW (c.tyR' hW hty)


theorem valid_pair {A B a a' b b' : Tm} {l : ℕ} (hsig : Valid2 S Ψ Φ Γ (.sigma A B) (.sigma A B) (.univ l))
    (ha : Valid2 S Ψ Φ Γ a a' A) (hb : Valid2 S Ψ Φ Γ b b' (B.inst a))
    (hty : HasTy0 S Ψ Φ Γ (.pair a b) (.sigma A B)) (hty' : HasTy0 S Ψ Φ Γ (.pair a' b') (.sigma A B))
    (heq : EqTm0 S Ψ Φ Γ (.pair a b) (.pair a' b') (.sigma A B)) :
    Valid2 S Ψ Φ Γ (.pair a b) (.pair a' b') (.sigma A B) := by
  intro k c
  have hsigTy : HasTy S k .one [] (c.L (.sigma A B)) (.univ l) := (RE2.typed (hsig k c).2).1
  have hpL : HasTy S k .one [] (.pair (c.L a) (c.L b)) (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) := c.ty hW hty
  have hpR : HasTy S k .one [] (.pair (c.R a') (c.R b')) (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) :=
    c.tyR' hW hty'
  have hLL : RT2 S k (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) :=
    hsig.ty hW (c.diagL hW)
  have hI := RT2_sigma_inv hW hLL
  have hAA := ha.tyLL hW c
  have hfL := HasTy.fst hpL
  have hfR := HasTy.fst hpR
  have h1 : RE2 S k (c.L A) (.fst (.pair (c.L a) (c.L b))) (.fst (.pair (c.R a') (c.R b'))) :=
    RE2.expand2 hW hAA hfL hfR (stable_fstBeta hW hfL) (stable_fstBeta hW hfR) (ha k c).2
  have haf : RE2 S k (c.L A) (c.L a) (.fst (.pair (c.L a) (c.L b))) :=
    RE2.expandR hW hAA (RE2.typed (ha k c).2).1 hfL (stable_fstBeta hW hfL)
      (RE2.trans hW hAA (ha k c).2 (RE2.symm hW hAA (ha k c).2))
  have hT := hI.2 _ _ haf
  have hbk := (hb k c).2
  have hbk1 := (hb k c).1
  simp only [CSub2.L, CSub2.R, inst_subst] at hbk hbk1
  have hb' := RE2.conv hW hT hbk
  have hXX := RT2.refl' hW (RE2.tyCode hW hbk) hT
  have hsL := HasTy.snd hpL
  have hsR := (HasTy.snd hpR).tyConv (TyEq.symm (Comp2_ty_base (hI.2 _ _ h1)).2.2.2.2.2)
  have h2 := RE2.expand2 hW hXX hsL hsR (stable_sndBeta hW hsL) (stable_sndBeta hW hsR) hb'
  exact ⟨hsig.ty hW c, RE2_sigma_intro hW hsigTy ⟨hpL, hpR, c.eq hW heq⟩ h1 h2⟩

theorem valid_sigmaEta {A B p : Tm} (hp : Valid2 S Ψ Φ Γ p p (.sigma A B)) (hty : HasTy0 S Ψ Φ Γ p (.sigma A B))
    (hu : HasTy0 S Ψ Φ Γ (.pair (.fst p) (.snd p)) (.sigma A B))
    (heq : EqTm0 S Ψ Φ Γ p (.pair (.fst p) (.snd p)) (.sigma A B)) :
    Valid2 S Ψ Φ Γ p (.pair (.fst p) (.snd p)) (.sigma A B) := by
  intro k c
  have hpt := c.ty hW hty
  obtain ⟨l, hsigTy⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpt) (TyEq.refl _) (fun l h => by cases h)
  have hLL : RT2 S k (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) :=
    hp.tyLL hW c
  have hI := RT2_sigma_inv hW hLL
  have hpR : HasTy S k .one [] (.pair (.fst (c.R p)) (.snd (c.R p))) (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) :=
    c.tyR' hW hu
  have hel := RE2_sigma_elim hW (show RE2 S k (.sigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)) _ _ from (hp k c).2)
  have hfR := HasTy.fst hpR
  have h1 := RE2.expandR hW hI.1 (RE2.typed hel.1).1 hfR (stable_fstBeta hW hfR) hel.1
  have hfLL := RE2.trans hW hI.1 hel.1 (RE2.symm hW hI.1 hel.1)
  have hXX := hI.2 _ _ hfLL
  have hsR := (HasTy.snd hpR).tyConv (TyEq.symm (Comp2_ty_base (hI.2 _ _ h1)).2.2.2.2.2)
  have h2 := RE2.expandR hW hXX (RE2.typed hel.2).1 hsR (stable_sndBeta hW hsR) hel.2
  exact ⟨(hp k c).1, RE2_sigma_intro hW hsigTy ⟨hpt, hpR, c.eq hW heq⟩ h1 h2⟩


/-! ### Path types -/

omit hW in
theorem isub_plam (t : Tm) (σ : ISub k' k) : (Tm.plam t).isub σ = .plam (t.isub σ.up) := rfl

theorem stable_pathBeta {X t : Tm} {r : I} (hty : HasTy S k .one [] (.papp (.plam t) r) X) :
    StableE S k X (.papp (.plam t) r) (t.dinst r) := by
  intro k' σ
  have hσ := HasTy.isubS hW hty σ
  rw [isub_papp, isub_plam] at hσ ⊢
  rw [isub_dinst]
  exact ⟨.step (by simp [step]) (.refl _), EqTm.pathBeta hσ⟩

theorem valid_path {L L' a a' b b' : Tm} {l : ℕ} (hL : Valid2 S (Ψ + 1) Φ.shift Γ.dshift L L' (.univ l))
    (ha : Valid2 S Ψ Φ Γ a a' (L.dinst .zero)) (hb : Valid2 S Ψ Φ Γ b b' (L.dinst .one))
    (hty : HasTy0 S Ψ Φ Γ (.path L a b) (.univ l)) (hty' : HasTy0 S Ψ Φ Γ (.path L' a' b') (.univ l))
    (heq : EqTm0 S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l)) :
    Valid2 S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l) := by
  refine valid_univ_of hW hty hty' heq fun k c => RT2_path_intro hW (c.ty hW hty) (c.tyR hW hty') (c.eq hW heq)
    (fun k' σ => ?_) (fun k' σ r r' hr hr' hE => ?_) ?_ ?_
  · have := hL.ty hW ((c.restr hW σ).up hW)
    rw [CSub2.up_restr_L, CSub2.up_restr_R] at this; exact this
  · have := hL.ty hW ((c.restr hW σ).cons r r' hr hr' hE)
    rw [CSub2.cons_restr_L, CSub2.cons_restr_R] at this; exact this
  · have := (ha k c).2; simp only [CSub2.L, CSub2.R, dinst_subst] at this; exact this
  · have := (hb k c).2; simp only [CSub2.L, CSub2.R, dinst_subst] at this; exact this

/-- Validity of a path abstraction, given its endpoints. -/
theorem valid_plam_core {L a b t t' : Tm} {l : ℕ} (hpath : Valid2 S Ψ Φ Γ (.path L a b) (.path L a b) (.univ l))
    (ht : Valid2 S (Ψ + 1) Φ.shift Γ.dshift t t' L) (hty : HasTy0 S Ψ Φ Γ (.plam t) (.path L a b))
    (hty' : HasTy0 S Ψ Φ Γ (.plam t') (.path L a b)) (heq : EqTm0 S Ψ Φ Γ (.plam t) (.plam t') (.path L a b))
    (h0 : ∀ k (c : CSub2 S Ψ Φ Γ k), RE2 S k ((L.subst (dupS c.γ) (I.up c.σ.τ)).dinst .zero)
      (.papp (c.L (.plam t)) .zero) (c.L a))
    (h1 : ∀ k (c : CSub2 S Ψ Φ Γ k), RE2 S k ((L.subst (dupS c.γ) (I.up c.σ.τ)).dinst .one)
      (.papp (c.L (.plam t)) .one) (c.L b)) :
    Valid2 S Ψ Φ Γ (.plam t) (.plam t') (.path L a b) := by
  intro k c
  have hpathTy : HasTy S k .one [] (c.L (.path L a b)) (.univ l) := (RE2.typed (hpath k c).2).1
  refine ⟨hpath.ty hW c, RE2_path_intro hW hpathTy ⟨c.ty hW hty, c.tyR' hW hty', c.eq hW heq⟩
    (fun k' σ r r' hr hr' hE => ?_) (h0 k c) (h1 k c)⟩
  have hPL : RT2 S k' ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ)
      ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ) := hpath.tyRestr hW (c.diagL hW) σ
  rw [isub_path] at hPL
  have hI := RT2_path_inv hW hPL
  have hTyE := (Comp2_ty_base (hI.2.1 r r' hr hr' hE)).2.2.2.2.2
  have hpL : HasTy S k' .one [] ((Tm.plam (t.subst (dupS c.γ) (I.up c.σ.τ))).isub σ)
      ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ) := HasTy.isubS hW (c.ty hW hty) σ
  have hpR : HasTy S k' .one [] ((Tm.plam (t'.subst (dupS c.γ') (I.up c.σ'.τ))).isub σ)
      ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ) := HasTy.isubS hW (c.tyR' hW hty') σ
  rw [isub_path, isub_plam] at hpL hpR
  have happL := HasTy.papp hpL hr
  have happR := (HasTy.papp hpR hr').tyConv (TyEq.symm hTyE)
  have ih := (ht k' ((c.restr hW σ).cons r r' hr hr' hE)).2
  have hXX := ht.tyLL hW ((c.restr hW σ).cons r r' hr hr' hE)
  rw [CSub2.cons_restr_L, CSub2.cons_restr_L, CSub2.cons_restr_R] at ih
  rw [CSub2.cons_restr_L] at hXX
  show RE2 S k' _ (.papp ((Tm.plam (t.subst (dupS c.γ) (I.up c.σ.τ))).isub σ) r)
    (.papp ((Tm.plam (t'.subst (dupS c.γ') (I.up c.σ'.τ))).isub σ) r')
  rw [isub_plam, isub_plam]
  exact RE2.expand2 hW hXX happL happR (stable_pathBeta hW happL) (stable_pathBeta hW happR) ih


/-- Expansion on the left, at the level of `RE2`. -/
theorem RE2.expandL {A t t' u : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A)
    (ht' : HasTy S k .one [] t' A) (hs : StableE S k A t u) (h : RE2 S k A u t') : RE2 S k A t t' :=
  el_expandS hW (RE2.tyCode hW h) hAA ht ht' hs h

theorem valid_plam {L a b t : Tm} {l : ℕ} (hpath : Valid2 S Ψ Φ Γ (.path L a b) (.path L a b) (.univ l))
    (ht : Valid2 S (Ψ + 1) Φ.shift Γ.dshift t t L) (h0 : Valid2 S Ψ Φ Γ (t.dinst .zero) a (L.dinst .zero))
    (h1 : Valid2 S Ψ Φ Γ (t.dinst .one) b (L.dinst .one)) (hty : HasTy0 S Ψ Φ Γ (.plam t) (.path L a b)) :
    Valid2 S Ψ Φ Γ (.plam t) (.plam t) (.path L a b) := by
  have hend : ∀ (x : Tm) (d : I), (d = .zero ∨ d = .one) → Valid2 S Ψ Φ Γ (t.dinst d) x (L.dinst d) →
      ∀ k (c : CSub2 S Ψ Φ Γ k), RE2 S k ((L.subst (dupS c.γ) (I.up c.σ.τ)).dinst d)
        (.papp (c.L (.plam t)) d) (c.L x) := by
    intro x d hd hv k c
    have hp : HasTy S k .one [] (.plam (t.subst (dupS c.γ) (I.up c.σ.τ)))
        (.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)) := c.ty hW hty
    have hdS : d.Scoped k := by rcases hd with rfl | rfl <;> trivial
    have hdτ : d.subst c.σ.τ = d := by rcases hd with rfl | rfl <;> rfl
    have happ := HasTy.papp hp hdS
    have hv1 := (hv k (c.diagL hW)).2
    have hAA := hv.tyLL hW c
    simp only [CSub2.L, CSub2.R, CSub2.diagL, dinst_subst, hdτ] at hv1 hAA
    exact RE2.expandL hW hAA happ (RE2.typed hv1).2.1 (stable_pathBeta hW happ) hv1
  exact valid_plam_core hW hpath ht hty hty (EqTm0.refl hty) (hend a .zero (.inl rfl) h0)
    (hend b .one (.inr rfl) h1)

theorem valid_plam_eq {L a b t t' : Tm} {l : ℕ} (hpath : Valid2 S Ψ Φ Γ (.path L a b) (.path L a b) (.univ l))
    (hp : Valid2 S Ψ Φ Γ (.plam t) (.plam t) (.path L a b)) (ht : Valid2 S (Ψ + 1) Φ.shift Γ.dshift t t' L)
    (hty : HasTy0 S Ψ Φ Γ (.plam t) (.path L a b)) (hty' : HasTy0 S Ψ Φ Γ (.plam t') (.path L a b))
    (heq : EqTm0 S Ψ Φ Γ (.plam t) (.plam t') (.path L a b)) :
    Valid2 S Ψ Φ Γ (.plam t) (.plam t') (.path L a b) :=
  valid_plam_core hW hpath ht hty hty' heq (fun k c => (RE2_path_elim hW (hp k c).2).2.1)
    (fun k c => (RE2_path_elim hW (hp k c).2).2.2)

omit hW in
theorem CSub2.ieq_subst (c : CSub2 S Ψ Φ Γ k) {r r' : I} (hE : I.Eq r r') :
    I.Eq (r.subst c.σ.τ) (r'.subst c.σ'.τ) :=
  I_eq_trans (I_eq_subst_congr c.hσ r) (I_eq_subst hE c.σ'.τ)

theorem valid_papp {L a b p p' : Tm} {r r' : I} (hp : Valid2 S Ψ Φ Γ p p' (.path L a b)) (hr : r.Scoped Ψ)
    (hr' : r'.Scoped Ψ) (hE : I.Eq r r') : Valid2 S Ψ Φ Γ (.papp p r) (.papp p' r') (L.dinst r) := by
  intro k c
  have hI := RT2_path_inv hW (hp k c).1
  have hel := RE2_path_elim hW (hp k c).2
  simp only [CSub2.L, CSub2.R, dinst_subst]
  exact ⟨hI.2.1 _ _ (I.scoped_subst hr c.σ.sc) (I.scoped_subst hr c.σ'.sc) (c.ieq_subst (I_eq_refl r)),
    hel.1 _ _ (I.scoped_subst hr c.σ.sc) (I.scoped_subst hr' c.σ'.sc) (c.ieq_subst hE)⟩

theorem valid_pathBeta {t T : Tm} {r : I} (h : Valid2 S Ψ Φ Γ (.papp (.plam t) r) (.papp (.plam t) r) T)
    (hty : HasTy0 S Ψ Φ Γ (.papp (.plam t) r) T) (hu : HasTy0 S Ψ Φ Γ (t.dinst r) T) :
    Valid2 S Ψ Φ Γ (.papp (.plam t) r) (t.dinst r) T := by
  refine valid_redR hW h hu fun k c => ?_
  have := stable_pathBeta hW (c.tyR' hW hty)
  simp only [CSub2.R, dinst_subst]
  exact this

theorem valid_pathZero {L a b p : Tm} (hp : Valid2 S Ψ Φ Γ p p (.path L a b)) :
    Valid2 S Ψ Φ Γ (.papp p .zero) a (L.dinst .zero) := by
  intro k c
  have hI := RT2_path_inv hW (hp k c).1
  have hel := RE2_path_elim hW (hp k c).2
  simp only [CSub2.L, CSub2.R, dinst_subst]
  have hT := hI.2.1 .zero .zero trivial trivial (I_eq_refl _)
  exact ⟨hT, RE2.trans hW hT hel.2.1 hI.2.2.1⟩

theorem valid_pathOne {L a b p : Tm} (hp : Valid2 S Ψ Φ Γ p p (.path L a b)) :
    Valid2 S Ψ Φ Γ (.papp p .one) b (L.dinst .one) := by
  intro k c
  have hI := RT2_path_inv hW (hp k c).1
  have hel := RE2_path_elim hW (hp k c).2
  simp only [CSub2.L, CSub2.R, dinst_subst]
  have hT := hI.2.1 .one .one trivial trivial (I_eq_refl _)
  exact ⟨hT, RE2.trans hW hT hel.2.2 hI.2.2.2⟩


omit hW in
theorem peta_body (p : Tm) (γ : ℕ → Tm) (τ : ℕ → I) (σ : ISub k' k) (r : I) :
    (((Tm.papp p.dshift (.var 0)).subst (dupS γ) (I.up τ)).isub σ.up).dinst r =
      .papp ((p.subst γ τ).isub σ) r := by
  have e : ((Tm.papp p.dshift (.var 0)).subst (dupS γ) (I.up τ)).isub σ.up =
      (Tm.papp p.dshift (.var 0)).subst (dupS fun x => (γ x).isub σ) (I.up fun i => (τ i).subst σ.τ) := by
    simp only [Tm.isub, subst_subst, ISub.up]
    apply subst_congr
    · intro x; exact isub_dshift (γ x) σ
    · intro i; exact I_up_comp _ _ i
  rw [e, dup_dinst, subst_isub2]
  simp only [Tm.subst, dshift_consI]
  rfl

theorem valid_pathEta {L a b p : Tm} (hp : Valid2 S Ψ Φ Γ p p (.path L a b)) (hty : HasTy0 S Ψ Φ Γ p (.path L a b))
    (hu : HasTy0 S Ψ Φ Γ (.plam (.papp p.dshift (.var 0))) (.path L a b))
    (heq : EqTm0 S Ψ Φ Γ p (.plam (.papp p.dshift (.var 0))) (.path L a b)) :
    Valid2 S Ψ Φ Γ p (.plam (.papp p.dshift (.var 0))) (.path L a b) := by
  intro k c
  have hpt := c.ty hW hty
  obtain ⟨l, hpathTy⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpt) (TyEq.refl _) (fun l h => by cases h)
  have hel := RE2_path_elim hW (show RE2 S k (.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)) _ _ from
    (hp k c).2)
  refine ⟨(hp k c).1, RE2_path_intro hW hpathTy ⟨hpt, c.tyR' hW hu, c.eq hW heq⟩
    (fun k' σ r r' hr hr' hE => ?_) hel.2.1 hel.2.2⟩
  have hpσ : RE2 S k' ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ)
      ((c.L p).isub σ) ((c.R p).isub σ) := RE2.isub hW (hp k c).2 σ
  have hPL : RT2 S k' ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ)
      ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ) :=
    RT2.isub hW (hp.tyCode hW c) (hp.tyLL hW c) σ
  rw [isub_path] at hpσ hPL
  have hI := RT2_path_inv hW hPL
  have hXX := hI.2.1 r r hr hr (I_eq_refl r)
  have hTyE := (Comp2_ty_base (hI.2.1 r r' hr hr' hE)).2.2.2.2.2
  have h := (RE2_path_elim hW hpσ).1 r r' hr hr' hE
  have hR : HasTy S k' .one [] ((Tm.plam ((Tm.papp p.dshift (.var 0)).subst (dupS c.γ') (I.up c.σ'.τ))).isub σ)
      ((Tm.path (L.subst (dupS c.γ) (I.up c.σ.τ)) (c.L a) (c.L b)).isub σ) := HasTy.isubS hW (c.tyR' hW hu) σ
  rw [isub_path, isub_plam] at hR
  have happR := (HasTy.papp hR hr').tyConv (TyEq.symm hTyE)
  have hs := stable_pathBeta hW happR
  rw [peta_body] at hs
  show RE2 S k' _ _ (.papp ((Tm.plam ((Tm.papp p.dshift (.var 0)).subst (dupS c.γ') (I.up c.σ'.τ))).isub σ) r')
  rw [isub_plam]
  exact RE2.expandR hW hXX (RE2.typed h).1 happR hs h

theorem valid_pathInjLine {L L' a a' b b' : Tm} {r : I} {l : ℕ}
    (h : Valid2 S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l)) (hr : r.Scoped Ψ)
    (hty : HasTy0 S Ψ Φ Γ (L.dinst r) (.univ l)) (hty' : HasTy0 S Ψ Φ Γ (L'.dinst r) (.univ l))
    (heq : EqTm0 S Ψ Φ Γ (L.dinst r) (L'.dinst r) (.univ l)) : Valid2 S Ψ Φ Γ (L.dinst r) (L'.dinst r) (.univ l) := by
  refine valid_univ_of hW hty hty' heq fun k c => ?_
  simp only [CSub2.L, CSub2.R, dinst_subst]
  exact (RT2_path_inv hW (h.ty hW c)).2.1 _ _ (I.scoped_subst hr c.σ.sc) (I.scoped_subst hr c.σ'.sc)
    (c.ieq_subst (I_eq_refl r))

theorem valid_pathInjLeft {L L' a a' b b' : Tm} {l : ℕ}
    (h : Valid2 S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l)) : Valid2 S Ψ Φ Γ a a' (L.dinst .zero) := by
  intro k c
  have h1 := RT2_path_inv hW (h.ty hW c)
  have h2 := RT2_path_inv hW (h.ty hW (c.diagR hW))
  have hX := tyCode_of_ty hW (RE2.typed h1.2.2.1).1
  have hX' := tyCode_of_ty hW (RE2.typed h2.2.2.1).1
  simp only [CSub2.L, CSub2.R, dinst_subst]
  exact ⟨RT2.trans hW hX (h1.2.1 .zero .zero trivial trivial (I_eq_refl _))
    (RT2.symm hW hX' (h2.2.1 .zero .zero trivial trivial (I_eq_refl _))), h1.2.2.1⟩

theorem valid_pathInjRight {L L' a a' b b' : Tm} {l : ℕ}
    (h : Valid2 S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l)) : Valid2 S Ψ Φ Γ b b' (L.dinst .one) := by
  intro k c
  have h1 := RT2_path_inv hW (h.ty hW c)
  have h2 := RT2_path_inv hW (h.ty hW (c.diagR hW))
  have hX := tyCode_of_ty hW (RE2.typed h1.2.2.2).1
  have hX' := tyCode_of_ty hW (RE2.typed h2.2.2.2).1
  simp only [CSub2.L, CSub2.R, dinst_subst]
  exact ⟨RT2.trans hW hX (h1.2.1 .one .one trivial trivial (I_eq_refl _))
    (RT2.symm hW hX' (h2.2.1 .one .one trivial trivial (I_eq_refl _))), h1.2.2.2⟩


/-! ### `(i : I) → L` -/

theorem valid_ipi {L L' : Tm} {l : ℕ} (hL : Valid2 S (Ψ + 1) Φ.shift Γ.dshift L L' (.univ l))
    (hty : HasTy0 S Ψ Φ Γ (.ipi L) (.univ l)) (hty' : HasTy0 S Ψ Φ Γ (.ipi L') (.univ l))
    (heq : EqTm0 S Ψ Φ Γ (.ipi L) (.ipi L') (.univ l)) : Valid2 S Ψ Φ Γ (.ipi L) (.ipi L') (.univ l) := by
  refine valid_univ_of hW hty hty' heq fun k c => RT2_ipi_intro hW (c.ty hW hty) (c.tyR hW hty') (c.eq hW heq)
    (fun k' σ => ?_) (fun k' σ r r' hr hr' hE => ?_)
  · have := hL.ty hW ((c.restr hW σ).up hW)
    rw [CSub2.up_restr_L, CSub2.up_restr_R] at this; exact this
  · have := hL.ty hW ((c.restr hW σ).cons r r' hr hr' hE)
    rw [CSub2.cons_restr_L, CSub2.cons_restr_R] at this; exact this

theorem valid_ilam {L t t' : Tm} {l : ℕ} (hipi : Valid2 S Ψ Φ Γ (.ipi L) (.ipi L) (.univ l))
    (ht : Valid2 S (Ψ + 1) Φ.shift Γ.dshift t t' L) (hty : HasTy0 S Ψ Φ Γ (.plam t) (.ipi L))
    (hty' : HasTy0 S Ψ Φ Γ (.plam t') (.ipi L)) (heq : EqTm0 S Ψ Φ Γ (.plam t) (.plam t') (.ipi L)) :
    Valid2 S Ψ Φ Γ (.plam t) (.plam t') (.ipi L) := by
  intro k c
  have hipiTy : HasTy S k .one [] (c.L (.ipi L)) (.univ l) := (RE2.typed (hipi k c).2).1
  refine ⟨hipi.ty hW c, RE2_ipi_intro hW hipiTy ⟨c.ty hW hty, c.tyR' hW hty', c.eq hW heq⟩
    (fun k' σ r r' hr hr' hE => ?_)⟩
  have hPL : RT2 S k' ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ)
      ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ) := hipi.tyRestr hW (c.diagL hW) σ
  rw [isub_ipi] at hPL
  have hI := RT2_ipi_inv hW hPL
  have hTyE := (Comp2_ty_base (hI.2 r r' hr hr' hE)).2.2.2.2.2
  have hpL : HasTy S k' .one [] ((Tm.plam (t.subst (dupS c.γ) (I.up c.σ.τ))).isub σ)
      ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ) := HasTy.isubS hW (c.ty hW hty) σ
  have hpR : HasTy S k' .one [] ((Tm.plam (t'.subst (dupS c.γ') (I.up c.σ'.τ))).isub σ)
      ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ) := HasTy.isubS hW (c.tyR' hW hty') σ
  rw [isub_ipi, isub_plam] at hpL hpR
  have happL := HasTy.iapp hpL hr
  have happR := (HasTy.iapp hpR hr').tyConv (TyEq.symm hTyE)
  have ih := (ht k' ((c.restr hW σ).cons r r' hr hr' hE)).2
  have hXX := ht.tyLL hW ((c.restr hW σ).cons r r' hr hr' hE)
  rw [CSub2.cons_restr_L, CSub2.cons_restr_L, CSub2.cons_restr_R] at ih
  rw [CSub2.cons_restr_L] at hXX
  show RE2 S k' _ (.papp ((Tm.plam (t.subst (dupS c.γ) (I.up c.σ.τ))).isub σ) r)
    (.papp ((Tm.plam (t'.subst (dupS c.γ') (I.up c.σ'.τ))).isub σ) r')
  rw [isub_plam, isub_plam]
  exact RE2.expand2 hW hXX happL happR (stable_pathBeta hW happL) (stable_pathBeta hW happR) ih

theorem valid_iapp {L p p' : Tm} {r r' : I} (hp : Valid2 S Ψ Φ Γ p p' (.ipi L)) (hr : r.Scoped Ψ)
    (hr' : r'.Scoped Ψ) (hE : I.Eq r r') : Valid2 S Ψ Φ Γ (.papp p r) (.papp p' r') (L.dinst r) := by
  intro k c
  have hI := RT2_ipi_inv hW (hp k c).1
  have hel := RE2_ipi_elim hW (hp k c).2
  simp only [CSub2.L, CSub2.R, dinst_subst]
  exact ⟨hI.2 _ _ (I.scoped_subst hr c.σ.sc) (I.scoped_subst hr c.σ'.sc) (c.ieq_subst (I_eq_refl r)),
    hel _ _ (I.scoped_subst hr c.σ.sc) (I.scoped_subst hr' c.σ'.sc) (c.ieq_subst hE)⟩

theorem valid_ipiEta {L p : Tm} (hp : Valid2 S Ψ Φ Γ p p (.ipi L)) (hty : HasTy0 S Ψ Φ Γ p (.ipi L))
    (hu : HasTy0 S Ψ Φ Γ (.plam (.papp p.dshift (.var 0))) (.ipi L))
    (heq : EqTm0 S Ψ Φ Γ p (.plam (.papp p.dshift (.var 0))) (.ipi L)) :
    Valid2 S Ψ Φ Γ p (.plam (.papp p.dshift (.var 0))) (.ipi L) := by
  intro k c
  have hpt := c.ty hW hty
  obtain ⟨l, hipiTy⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpt) (TyEq.refl _) (fun l h => by cases h)
  refine ⟨(hp k c).1, RE2_ipi_intro hW hipiTy ⟨hpt, c.tyR' hW hu, c.eq hW heq⟩
    (fun k' σ r r' hr hr' hE => ?_)⟩
  have hpσ : RE2 S k' ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ)
      ((c.L p).isub σ) ((c.R p).isub σ) := RE2.isub hW (hp k c).2 σ
  have hPL : RT2 S k' ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ)
      ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ) :=
    RT2.isub hW (hp.tyCode hW c) (hp.tyLL hW c) σ
  rw [isub_ipi] at hpσ hPL
  have hI := RT2_ipi_inv hW hPL
  have hXX := hI.2 r r hr hr (I_eq_refl r)
  have hTyE := (Comp2_ty_base (hI.2 r r' hr hr' hE)).2.2.2.2.2
  have h := RE2_ipi_elim hW hpσ r r' hr hr' hE
  have hR : HasTy S k' .one [] ((Tm.plam ((Tm.papp p.dshift (.var 0)).subst (dupS c.γ') (I.up c.σ'.τ))).isub σ)
      ((Tm.ipi (L.subst (dupS c.γ) (I.up c.σ.τ))).isub σ) := HasTy.isubS hW (c.tyR' hW hu) σ
  rw [isub_ipi, isub_plam] at hR
  have happR := (HasTy.iapp hR hr').tyConv (TyEq.symm hTyE)
  have hs := stable_pathBeta hW happR
  rw [peta_body] at hs
  show RE2 S k' _ _ (.papp ((Tm.plam ((Tm.papp p.dshift (.var 0)).subst (dupS c.γ') (I.up c.σ'.τ))).isub σ) r')
  rw [isub_plam]
  exact RE2.expandR hW hXX (RE2.typed h).1 happR hs h

theorem valid_ipiInj {L L' : Tm} {r : I} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.ipi L) (.ipi L') (.univ l))
    (hr : r.Scoped Ψ) (hty : HasTy0 S Ψ Φ Γ (L.dinst r) (.univ l)) (hty' : HasTy0 S Ψ Φ Γ (L'.dinst r) (.univ l))
    (heq : EqTm0 S Ψ Φ Γ (L.dinst r) (L'.dinst r) (.univ l)) : Valid2 S Ψ Φ Γ (L.dinst r) (L'.dinst r) (.univ l) := by
  refine valid_univ_of hW hty hty' heq fun k c => ?_
  simp only [CSub2.L, CSub2.R, dinst_subst]
  exact (RT2_ipi_inv hW (h.ty hW c)).2 _ _ (I.scoped_subst hr c.σ.sc) (I.scoped_subst hr c.σ'.sc)
    (c.ieq_subst (I_eq_refl r))


/-! ### Systems -/

/-- Head expansion with a reduct chosen at each restriction. -/
theorem RE2.expandH {A t t' : Tm} (hAA : RT2 S k A A) (ht : HasTy S k .one [] t A) (ht' : HasTy S k .one [] t' A)
    (h : ∀ k' (σ : ISub k' k), ∃ u, Red S (t.isub σ) u ∧ EqTm S k' .one [] (t.isub σ) u (A.isub σ) ∧
      RE2 S k' (A.isub σ) u (t'.isub σ)) : RE2 S k A t t' := by
  have hb := Comp2_ty_base hAA
  refine (he2_tyCode hW (tyCode_of_ty hW ht) k (Hom.id k) A A t t').2 hAA ht ht' fun k' σ => ?_
  obtain ⟨u, h1, h2, h3⟩ := h k' σ
  refine ⟨u, h1, h2, ?_⟩
  rw [Hom.id_comp, Comp2_eq_res hb.1, ← semK_isubTy hW hb.2.1 σ]
  exact h3

omit hW in
/-- The disjunction property of faces at the generic point of a stage. -/
theorem ent_or_cases {φ ψ : I} (hφ : φ.Scoped k) (hψ : ψ.Scoped k) (h : I.Entails .one (.or φ ψ)) :
    I.Entails .one φ ∨ I.Entails .one ψ := by
  have hh := entails_holds h (ρ := idEnv k) (by rw [ival_one]; rfl)
  rcases holds_or hh with h1 | h1
  · exact .inl (entails_of_holds hφ h1)
  · exact .inr (entails_of_holds hψ h1)

omit hW in
theorem ent_one_subst {φ : I} (h : I.Entails .one φ) (τ : ℕ → I) : I.Entails .one (φ.subst τ) :=
  ent_subst h τ

theorem stable_splitL {X t u : Tm} {φ ψ : I} (hφ : I.Entails .one φ)
    (hsp : HasTy S k .one [] (.split φ t ψ u) X) : StableE S k X (.split φ t ψ u) t := by
  intro k' σ
  have hσ : HasTy S k' .one [] (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) (X.isub σ) :=
    HasTy.isubS hW hsp σ
  have hφσ := ent_one_subst hφ σ.τ
  refine ⟨.step ?_ (.refl _), EqTm.splitL hφσ hσ⟩
  show step S (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) = some (t.isub σ)
  simp only [step, show I.entails .one (φ.subst σ.τ) = true from hφσ, if_true]

/-- A system is related to `x` if each branch is, wherever its face holds. -/
theorem RE2_split_l {A x t u : Tm} {φ ψ : I} (hφ : φ.Scoped k) (hψ : ψ.Scoped k)
    (hor : I.Entails .one (.or φ ψ)) (hAA : RT2 S k A A) (hsp : HasTy S k .one [] (.split φ t ψ u) A)
    (hx : HasTy S k .one [] x A)
    (ht : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → RE2 S k' (A.isub σ) (t.isub σ) (x.isub σ))
    (hu : ∀ k' (σ : ISub k' k), I.Entails .one (ψ.subst σ.τ) → RE2 S k' (A.isub σ) (u.isub σ) (x.isub σ)) :
    RE2 S k A (.split φ t ψ u) x := by
  refine RE2.expandH hW hAA hsp hx fun k' σ => ?_
  have hσ : HasTy S k' .one [] (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) (A.isub σ) :=
    HasTy.isubS hW hsp σ
  show ∃ u', Red S (.split (φ.subst σ.τ) (t.isub σ) (ψ.subst σ.τ) (u.isub σ)) u' ∧ _
  by_cases hφσ : I.Entails .one (φ.subst σ.τ)
  · refine ⟨t.isub σ, .step ?_ (.refl _), EqTm.splitL hφσ hσ, ht k' σ hφσ⟩
    simp only [step, show I.entails .one (φ.subst σ.τ) = true from hφσ, if_true]
  · have hψσ : I.Entails .one (ψ.subst σ.τ) := by
      rcases ent_or_cases (I.scoped_subst hφ σ.sc) (I.scoped_subst hψ σ.sc) (ent_one_subst hor σ.τ) with h | h
      · exact absurd h hφσ
      · exact h
    refine ⟨u.isub σ, .step ?_ (.refl _), EqTm.splitR hψσ hσ, hu k' σ hψσ⟩
    have hf : I.entails .one (φ.subst σ.τ) = false := by
      cases e : I.entails .one (φ.subst σ.τ)
      · rfl
      · exact absurd e hφσ
    simp only [step, hf, show I.entails .one (ψ.subst σ.τ) = true from hψσ, if_true, Bool.false_eq_true, if_false]

theorem RE2_split_r {A x t u : Tm} {φ ψ : I} (hφ : φ.Scoped k) (hψ : ψ.Scoped k)
    (hor : I.Entails .one (.or φ ψ)) (hAA : RT2 S k A A) (hsp : HasTy S k .one [] (.split φ t ψ u) A)
    (hx : HasTy S k .one [] x A)
    (ht : ∀ k' (σ : ISub k' k), I.Entails .one (φ.subst σ.τ) → RE2 S k' (A.isub σ) (x.isub σ) (t.isub σ))
    (hu : ∀ k' (σ : ISub k' k), I.Entails .one (ψ.subst σ.τ) → RE2 S k' (A.isub σ) (x.isub σ) (u.isub σ)) :
    RE2 S k A x (.split φ t ψ u) := by
  have hX := tyCode_of_ty hW hx
  refine RE2.symm hW hAA (RE2_split_l hW hφ hψ hor hAA hsp hx (fun k' σ h => ?_) (fun k' σ h => ?_))
  · exact RE2.symm hW (RT2.isub hW hX hAA σ) (ht k' σ h)
  · exact RE2.symm hW (RT2.isub hW hX hAA σ) (hu k' σ h)


omit hW in
theorem CSub2.restr_face (c : CSub2 S Ψ Φ Γ k) {φ : I} {ρ : ISub k' k}
    (h : I.Entails .one ((φ.subst c.σ.τ).subst ρ.τ)) : I.Entails .one (φ.subst (c.σ.comp ρ).τ) := by
  rw [I_subst_subst] at h; exact h

omit hW in
theorem CSub2.face_RL (c : CSub2 S Ψ Φ Γ k) {φ : I} {ρ : ISub k' k}
    (h : I.Entails .one ((φ.subst c.σ'.τ).subst ρ.τ)) : I.Entails .one ((φ.subst c.σ.τ).subst ρ.τ) :=
  ent_trans h (eq_ent (I_eq_subst (I_eq_symm (c.ieq_subst (I_eq_refl φ))) ρ.τ))

omit hW in
theorem ent_comp {k'' : ℕ} {φ : I} {ρ : ISub k' k} {ρ' : ISub k'' k'} (h : I.Entails .one (φ.subst ρ.τ)) :
    I.Entails .one (φ.subst (ρ.comp ρ').τ) := by
  have := ent_one_subst h ρ'.τ
  rw [I_subst_subst] at this; exact this

omit hW in
theorem ent_comp_inv {k'' : ℕ} {φ : I} {ρ : ISub k' k} {ρ' : ISub k'' k'} (h : I.Entails .one ((φ.subst ρ.τ).subst ρ'.τ)) :
    I.Entails .one (φ.subst (ρ.comp ρ').τ) := by
  rw [I_subst_subst] at h; exact h

theorem valid_split {A t t' u u' : Tm} {φ ψ : I} (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ)
    (hor : I.Entails Φ (.or φ ψ)) (htt : Valid2 S Ψ (cof Φ φ) Γ t t' A) (huu : Valid2 S Ψ (cof Φ ψ) Γ u u' A)
    (htu' : Valid2 S Ψ (cof (cof Φ φ) ψ) Γ t' u' A) (hsp : HasTy0 S Ψ Φ Γ (.split φ t ψ u) A)
    (hsp' : HasTy0 S Ψ Φ Γ (.split φ t' ψ u') A) :
    Valid2 S Ψ Φ Γ (.split φ t ψ u) (.split φ t' ψ u') A := by
  intro k c
  -- the branches, at restrictions where their faces hold
  have T : ∀ k' (ρ : ISub k' k), I.Entails .one (φ.subst (c.σ.comp ρ).τ) →
      RE2 S k' ((c.L A).isub ρ) ((c.L t).isub ρ) ((c.R t').isub ρ) := by
    intro k' ρ h
    have e : RE2 S k' ((c.restr hW ρ).L A) ((c.restr hW ρ).L t) ((c.restr hW ρ).R t') :=
      (htt k' ((c.restr hW ρ).cof h)).2
    rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at e
  have U : ∀ k' (ρ : ISub k' k), I.Entails .one (ψ.subst (c.σ.comp ρ).τ) →
      RE2 S k' ((c.L A).isub ρ) ((c.L u).isub ρ) ((c.R u').isub ρ) := by
    intro k' ρ h
    have e : RE2 S k' ((c.restr hW ρ).L A) ((c.restr hW ρ).L u) ((c.restr hW ρ).R u') :=
      (huu k' ((c.restr hW ρ).cof h)).2
    rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at e
  have TU : ∀ k' (ρ : ISub k' k) (h1 : I.Entails .one (φ.subst (c.σ.comp ρ).τ)),
      I.Entails .one (ψ.subst (c.σ.comp ρ).τ) →
      RE2 S k' ((c.L A).isub ρ) ((c.R t').isub ρ) ((c.R u').isub ρ) := by
    intro k' ρ h1 h2
    have e : RE2 S k' ((c.restr hW ρ).L A) ((c.restr hW ρ).R t') ((c.restr hW ρ).R u') :=
      htu'.right hW (((c.restr hW ρ).cof h1).cof h2)
    rwa [CSub2.restr_L, CSub2.restr_R, CSub2.restr_R] at e
  -- the type
  have hφL := I.scoped_subst hφ c.σ.sc
  have hψL := I.scoped_subst hψ c.σ.sc
  have hφR := I.scoped_subst hφ c.σ'.sc
  have hψR := I.scoped_subst hψ c.σ'.sc
  have horL : I.Entails .one (.or (φ.subst c.σ.τ) (ψ.subst c.σ.τ)) := ent_trans c.face (ent_subst hor c.σ.τ)
  have horR : I.Entails .one (.or (φ.subst c.σ'.τ) (ψ.subst c.σ'.τ)) := ent_trans c.face' (ent_subst hor c.σ'.τ)
  have hTy : RT2 S k (c.L A) (c.R A) ∧ RT2 S k (c.L A) (c.L A) := by
    rcases ent_or_cases hφL hψL horL with h | h
    · exact ⟨(htt k (c.cof h)).1, htt.tyLL hW (c.cof h)⟩
    · exact ⟨(huu k (c.cof h)).1, huu.tyLL hW (c.cof h)⟩
  refine ⟨hTy.1, ?_⟩
  have hAA := hTy.2
  have hsL : HasTy S k .one [] (.split (φ.subst c.σ.τ) (c.L t) (ψ.subst c.σ.τ) (c.L u)) (c.L A) := c.ty hW hsp
  have hsR : HasTy S k .one [] (.split (φ.subst c.σ'.τ) (c.R t') (ψ.subst c.σ'.τ) (c.R u')) (c.L A) :=
    c.tyR' hW hsp'
  have hX := tyCode_of_ty hW hsL
  refine RE2_split_l hW hφL hψL horL hAA hsL hsR (fun k' ρ hρ => ?_) (fun k' ρ hρ => ?_)
  · -- the left system is at its first branch
    have hAρ := RT2.isub hW hX hAA ρ
    have hsRρ : HasTy S k' .one [] (.split ((φ.subst c.σ'.τ).subst ρ.τ) ((c.R t').isub ρ)
        ((ψ.subst c.σ'.τ).subst ρ.τ) ((c.R u').isub ρ)) ((c.L A).isub ρ) := HasTy.isubS hW hsR ρ
    show RE2 S k' _ _ (.split ((φ.subst c.σ'.τ).subst ρ.τ) ((c.R t').isub ρ) ((ψ.subst c.σ'.τ).subst ρ.τ)
      ((c.R u').isub ρ))
    have hx := (RE2.typed (T k' ρ (c.restr_face hρ))).1
    refine RE2_split_r hW (I.scoped_subst hφR ρ.sc) (I.scoped_subst hψR ρ.sc) (ent_one_subst horR ρ.τ) hAρ
      hsRρ hx (fun k'' ρ' h => ?_) (fun k'' ρ' h => ?_)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact T k'' (ρ.comp ρ') (c.restr_face (c.face_RL (ent_comp_inv h)))
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      have h1 : I.Entails .one (φ.subst (c.σ.comp (ρ.comp ρ')).τ) := c.restr_face (ent_comp (ρ' := ρ') hρ)
      have h2 : I.Entails .one (ψ.subst (c.σ.comp (ρ.comp ρ')).τ) := c.restr_face (c.face_RL (ent_comp_inv h))
      have hA2 := RT2.isub hW hX hAA (ρ.comp ρ')
      exact RE2.trans hW hA2 (T k'' _ h1) (TU k'' _ h1 h2)
  · -- the left system is at its second branch
    have hAρ := RT2.isub hW hX hAA ρ
    have hsRρ : HasTy S k' .one [] (.split ((φ.subst c.σ'.τ).subst ρ.τ) ((c.R t').isub ρ)
        ((ψ.subst c.σ'.τ).subst ρ.τ) ((c.R u').isub ρ)) ((c.L A).isub ρ) := HasTy.isubS hW hsR ρ
    show RE2 S k' _ _ (.split ((φ.subst c.σ'.τ).subst ρ.τ) ((c.R t').isub ρ) ((ψ.subst c.σ'.τ).subst ρ.τ)
      ((c.R u').isub ρ))
    have hx := (RE2.typed (U k' ρ (c.restr_face hρ))).1
    refine RE2_split_r hW (I.scoped_subst hφR ρ.sc) (I.scoped_subst hψR ρ.sc) (ent_one_subst horR ρ.τ) hAρ
      hsRρ hx (fun k'' ρ' h => ?_) (fun k'' ρ' h => ?_)
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      have h1 : I.Entails .one (φ.subst (c.σ.comp (ρ.comp ρ')).τ) := c.restr_face (c.face_RL (ent_comp_inv h))
      have h2 : I.Entails .one (ψ.subst (c.σ.comp (ρ.comp ρ')).τ) := c.restr_face (ent_comp (ρ' := ρ') hρ)
      have hA2 := RT2.isub hW hX hAA (ρ.comp ρ')
      exact RE2.trans hW hA2 (U k'' _ h2) (RE2.symm hW hA2 (TU k'' _ h1 h2))
    · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
      exact U k'' (ρ.comp ρ') (c.restr_face (c.face_RL (ent_comp_inv h)))


theorem valid_splitL {A t u : Tm} {φ ψ : I} (hφ0 : I.Entails Φ φ)
    (h : Valid2 S Ψ Φ Γ (.split φ t ψ u) (.split φ t ψ u) A) (hsp : HasTy0 S Ψ Φ Γ (.split φ t ψ u) A)
    (ht : HasTy0 S Ψ Φ Γ t A) : Valid2 S Ψ Φ Γ (.split φ t ψ u) t A :=
  valid_redR hW h ht fun k c => stable_splitL hW (ent_trans c.face' (ent_subst hφ0 c.σ'.τ)) (c.tyR' hW hsp)

theorem valid_splitR {A t u : Tm} {φ ψ : I} (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ) (hψ0 : I.Entails Φ ψ)
    (huu : Valid2 S Ψ (cof Φ ψ) Γ u u A) (htu : Valid2 S Ψ (cof (cof Φ φ) ψ) Γ t u A)
    (hsp : HasTy0 S Ψ Φ Γ (.split φ t ψ u) A) (hu : HasTy0 S Ψ Φ Γ u A) :
    Valid2 S Ψ Φ Γ (.split φ t ψ u) u A := by
  intro k c
  have hψc : I.Entails .one (ψ.subst c.σ.τ) := ent_trans c.face (ent_subst hψ0 c.σ.τ)
  have hTy := huu k (c.cof hψc)
  refine ⟨hTy.1, ?_⟩
  have hAA := huu.tyLL hW (c.cof hψc)
  have hsL : HasTy S k .one [] (.split (φ.subst c.σ.τ) (c.L t) (ψ.subst c.σ.τ) (c.L u)) (c.L A) := c.ty hW hsp
  refine RE2_split_l hW (I.scoped_subst hφ c.σ.sc) (I.scoped_subst hψ c.σ.sc)
    (ent_trans hψc (ent_or_right _ _)) hAA hsL (c.tyR' hW hu) (fun k' ρ hρ => ?_) (fun k' ρ hρ => ?_)
  · have h2 : I.Entails .one (ψ.subst (c.σ.comp ρ).τ) := c.restr_face (ent_one_subst hψc ρ.τ)
    have e : RE2 S k' ((c.restr hW ρ).L A) ((c.restr hW ρ).L t) ((c.restr hW ρ).R u) :=
      (htu k' (((c.restr hW ρ).cof (c.restr_face hρ)).cof h2)).2
    rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at e
  · have e : RE2 S k' ((c.restr hW ρ).L A) ((c.restr hW ρ).L u) ((c.restr hW ρ).R u) :=
      (huu k' ((c.restr hW ρ).cof (c.restr_face hρ))).2
    rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at e

omit hW in
theorem valid_local {t u A : Tm} {φ ψ : I} (hφ : φ.Scoped Ψ) (hψ : ψ.Scoped Ψ) (hor : I.Entails Φ (.or φ ψ))
    (h1 : Valid2 S Ψ (cof Φ φ) Γ t u A) (h2 : Valid2 S Ψ (cof Φ ψ) Γ t u A) : Valid2 S Ψ Φ Γ t u A := by
  intro k c
  rcases ent_or_cases (I.scoped_subst hφ c.σ.sc) (I.scoped_subst hψ c.σ.sc)
    (ent_trans c.face (ent_subst hor c.σ.τ)) with h | h
  · exact h1 k (c.cof h)
  · exact h2 k (c.cof h)

omit hW in
theorem valid_absurd {t u A : Tm} (hz : I.Entails Φ .zero) : Valid2 S Ψ Φ Γ t u A := by
  intro k c
  exact absurd (entails_holds (ent_trans c.face (ent_subst hz c.σ.τ)) (ρ := idEnv k) (by rw [ival_one]; rfl))
    not_holds_zero

end

end Model.Whnf
