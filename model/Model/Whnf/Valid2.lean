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

end

end Model.Whnf
