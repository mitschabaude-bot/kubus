import Model.Whnf.Fund2Aux
import Model.Whnf.Kan2Glue

/-!
# Validity of `glueBeta`

`unglue φ e (glueEl φ e t a) ≡ a : G`, with the coherence premise `a ≡ e.1 t : G` under `φ` (spec
change C4). Where the face does not hold, the redex steps to `a`; where it holds, it steps to
`e.1 (glueEl φ e t a)`, which is related to `e.1 t` (the Glue introduction is its fibre component
there) and hence, by the coherence premise, to `a`. The annotations of the `glueEl` may differ from
those of the `unglue`; the Glue introduction's fibre component is transferred along the relation of
the two Glue types (`ElTr2`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

theorem TyChainC.transportEq {Ψ : ℕ} {Φ : I} {Γ : Ctx} {X Y : Tm} :
    TyChainC S Ψ Φ Γ X Y → ∀ {t u}, EqTm0 S Ψ Φ Γ t u X → EqTm0 S Ψ Φ Γ t u Y
  | .refl _, _, _, h => h
  | .step e ch, _, _, h => ch.transportEq (EqTm0.conv h e)
  | .up hl ch, _, _, h => ch.transportEq (EqTm0.cumul hl h)

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- The domain of a related equivalence type. -/
theorem RT2_equiv_dom {T A T' A' : Tm} (h : RT2 S k (Tm.equiv T A) (Tm.equiv T' A')) : RT2 S k T T' := by
  unfold Tm.equiv at h
  have h1 := (RT2_sigma_inv hW h).1
  unfold Tm.arrow at h1
  exact (RT2_pi_inv hW h1).1

theorem valid_glueBeta2 {A T e t a G A2 T2 : Tm} {φ : I} {l l2 : ℕ} (hφ : φ.Scoped Ψ)
    (hty : HasTy0 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) G) (haG : Valid2 S Ψ Φ Γ a a G)
    (hcoh : EqTm0 S Ψ (cof Φ φ) Γ a (.app (.fst e) t) G)
    (hcohV : Valid2 S Ψ (cof Φ φ) Γ a (.app (.fst e) t) G)
    -- the `unglue`
    (hA0 : HasTy0 S Ψ Φ Γ A (.univ l)) (he0 : HasTy0 S Ψ (cof Φ φ) Γ e (Tm.equiv T A))
    (he : Valid2 S Ψ (cof Φ φ) Γ e e (Tm.equiv T A)) (htr : ElTr2 S Ψ Φ Γ A G)
    (hgA : HasTy0 S Ψ Φ Γ (.glueEl φ e t a) (.glue A φ T e)) (hch : TyChainC S Ψ Φ Γ A G)
    -- the `glueEl`
    (hG2 : HasTy0 S Ψ Φ Γ (.glue A2 φ T2 e) (.univ l2)) (htv : Valid2 S Ψ (cof Φ φ) Γ t t T2)
    (htr2 : ElTr2 S Ψ Φ Γ (.glue A2 φ T2 e) (.glue A φ T e)) :
    Valid2 S Ψ Φ Γ (.unglue φ e (.glueEl φ e t a)) a G := by
  have hS := sigClosed_of_wfSig hW
  have hΦs : Φ.Scoped Ψ := scoped_of_ty hA0
  have hX : (cof Φ φ).Scoped Ψ := ⟨hΦs, hφ⟩
  intro k c0
  refine ⟨(haG k c0).1, RE2.expandH hW (haG.tyLL hW c0) (c0.ty hW hty) (RE2.typed (haG k c0).2).2.1 fun k' σ => ?_⟩
  have hL := CSub2.restr_L hW c0 σ
  have hR := CSub2.restr_R hW c0 σ
  rw [← hL, ← hL, ← hR]
  generalize c0.restr hW σ = c
  have hu := c.ty hW hty
  have hgL : HasTy S k' .one [] (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a))
      (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := c.ty hW hgA
  have haa := (haG k' c).2
  have hGG : RT2 S k' (c.L G) (c.L G) := haG.tyLL hW c
  by_cases hφe : I.Entails .one (φ.subst c.σ.τ)
  · -- the face holds: the redex steps to `e.1 (glueEl φ e t a)`
    have hred : Red S (.unglue (φ.subst c.σ.τ) (c.L e) (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a)))
        (.app (.fst (c.L e)) (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a))) :=
      .step (by simp [step, show I.entails .one (φ.subst c.σ.τ) = true from hφe]) (.refl _)
    -- the judgmental equality at `G`, under the face, then instantiated
    have e0 : EqTm0 S Ψ (cof Φ φ) Γ (.unglue φ e (.glueEl φ e t a)) (.app (.fst e) (.glueEl φ e t a)) G :=
      (hch.restrict hX (ent_and_left _ _)).transportEq
        (EqTm0.unglueFace (ent_and_right _ _) (HasTy0.restrict hX (ent_and_left _ _) hgA)
          (HasTy0.restrict hX (ent_and_left _ _) hA0) he0)
    have hφσ := I.scoped_subst hφ c.σ.sc
    have e1 := minimal_to_spec_eq ((sub_eq hS e0).2 (c.tySubLCof hW hφσ))
    have e2 := EqTm.restrict (Φ' := .one) trivial (ent_cof_one hW hφe) e1
    refine ⟨_, hred, e2, ?_⟩
    -- the fibre component
    let cd := (c.cof hφe).diagL hW
    have hGK : IsTyK S k' (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) := isTyK_of_ty hW hgL
    have hface := glue_face_tyEq hW hGK hφe
    have hee : RE2 S k' (Tm.equiv (c.L T) (c.L A)) (c.L e) (c.L e) := by
      have := (he k' cd).2
      rwa [show cd.L (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) from equiv_subst (σ := c.γ) (τ := c.σ.τ) T A] at this
    have hTT : RT2 S k' (c.L T) (c.L T) := RT2_equiv_dom hW (RT2.refl hW (RE2.tyCode hW hee) (by
      have := (he k' cd).1
      rwa [show cd.L (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) from equiv_subst (σ := c.γ) (τ := c.σ.τ) T A,
        show cd.R (Tm.equiv T A) = Tm.equiv (c.L T) (c.L A) from equiv_subst (σ := c.γ) (τ := c.σ.τ) T A] at this))
    have htt2 := (htv k' cd).2
    have hT2T2 : RT2 S k' (c.L T2) (c.L T2) := htv.tyLL hW cd
    have hG2c : HasTy S k' .one [] (.glue (c.L A2) (φ.subst c.σ.τ) (c.L T2) (c.L e)) (.univ l2) := c.ty hW hG2
    have tG2 := RE2_glue_of_fiber hW hG2c hφe hT2T2 htt2
    have tG := htr2 k' c _ _ tG2
    obtain ⟨lG, hG0, -, -⟩ := glue_ty_of_el hW hgA
    have hGc : HasTy S k' .one [] (.glue (c.L A) (φ.subst c.σ.τ) (c.L T) (c.L e)) (.univ lG) := c.ty hW hG0
    have tT := RE2_glue_fib hW hGc hφe hTT tG
    have hgT : RE2 S k' (c.L T) (.glueEl (φ.subst c.σ.τ) (c.L e) (c.L t) (c.L a)) (c.L t) :=
      RE2.expandL hW hTT (hgL.tyConv hface) (RE2.typed tT).1 (stable_glueEl hW (hgL.tyConv hface) hφe) tT
    have happ := RE2_equiv_app hW hee hgT
    have happG := htr k' c _ _ happ
    have hcd := (hcohV k' cd).2
    exact RE2.trans hW hGG happG (RE2.trans hW hGG (RE2.symm hW hGG hcd) haa)
  · -- the face does not hold: the redex steps to `a`
    refine ⟨c.L a, red_unglue_base hφe (redE_glueEl_self (S := S) hφe hgL).1,
      EqTm.glueBeta hu (RE2.typed haa).1 (minimal_to_spec_eq ((sub_eq hS hcoh).2
        (c.tySubLCof hW (I.scoped_subst hφ c.σ.sc)))), haa⟩

end

end Model.Whnf
