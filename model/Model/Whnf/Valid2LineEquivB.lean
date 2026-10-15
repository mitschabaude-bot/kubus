import Model.Whnf.Valid2LineEquiv

/-!
# Validity of `lineEquiv` between related lines

The binary version of `VTy.lineEquiv'` (`Valid2LineEquiv.lean`): for lines `B`, `B'` of types of
level `l` that are judgmentally equal and valid together, `lineEquiv B` and `lineEquiv B'` are valid
together (`VEq.lineEquiv₂`). The related lines carry their transport operations. This relates the
equivalences of the `hcompU` contracta of related compositions in the universe.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- `λ` with judgmentally equal domains. -/
theorem valid_lamD {A A' B t t' : Tm} {l : ℕ} (hpi : Valid2 S Ψ Φ Γ (.pi A B) (.pi A B) (.univ l))
    (ht : Valid2 S Ψ Φ (A :: Γ) t t' B) (hty : HasTy0 S Ψ Φ Γ (.lam A t) (.pi A B))
    (hty' : HasTy0 S Ψ Φ Γ (.lam A' t') (.pi A B)) (heq : EqTm0 S Ψ Φ Γ (.lam A t) (.lam A' t') (.pi A B)) :
    Valid2 S Ψ Φ Γ (.lam A t) (.lam A' t') (.pi A B) := by
  intro k c
  have hpiTy : HasTy S k .one [] (c.L (.pi A B)) (.univ l) := (RE2.typed (hpi k c).2).1
  refine ⟨hpi.ty hW c, RE2_pi_intro hW hpiTy ⟨c.ty hW hty, c.tyR' hW hty', c.eq hW heq⟩ fun k' σ a a' ha => ?_⟩
  have hPL : RT2 S k' ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := hpi.tyRestr hW (c.diagL hW) σ
  simp only [isub_pi] at hPL
  have hIL := RT2_pi_inv hW hPL
  have haa := RE2.trans hW hIL.1 ha (RE2.symm hW hIL.1 ha)
  have hXX := hIL.2 a a haa
  have hTyE := (Comp2_ty_base (hIL.2 a a' ha)).2.2.2.2.2
  have hlamL : HasTy S k' .one [] ((Tm.lam (c.L A) (t.subst (Tm.up c.γ) c.σ.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := HasTy.isubS hW (c.ty hW hty) σ
  have hlamR : HasTy S k' .one [] ((Tm.lam (c.R A') (t'.subst (Tm.up c.γ') c.σ'.τ)).isub σ)
      ((Tm.pi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ)).isub σ) := HasTy.isubS hW (c.tyR' hW hty') σ
  rw [isub_pi, isub_lam] at hlamL hlamR
  have happL := HasTy.app hlamL (RE2.typed ha).1
  have happR := (HasTy.app hlamR (RE2.typed ha).2.1).tyConv (TyEq.symm hTyE)
  have ha1 := ha
  rw [← CSub2.restr_L hW c σ] at ha1
  have hA1 := CSub2.tyRob_of hW (fun k c => (RT2_pi_inv hW (show RT2 S k (.pi _ _) (.pi _ _) from hpi.ty hW c)).1)
    (c.restr hW σ)
  have hmain := (ht k' ((c.restr hW σ).ext hW A a a' ha1 hA1)).2
  have hm : RE2 S k' (((B.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a) (((t.subst (Tm.up c.γ) c.σ.τ).isub σ).inst a)
      (((t'.subst (Tm.up c.γ') c.σ'.τ).isub σ).inst a') := by
    rw [subst_up_isub_inst, subst_up_isub_inst, subst_up_isub_inst]; exact hmain
  show RE2 S k' _ (.app ((Tm.lam (c.L A) (t.subst (Tm.up c.γ) c.σ.τ)).isub σ) a)
    (.app ((Tm.lam (c.R A') (t'.subst (Tm.up c.γ') c.σ'.τ)).isub σ) a')
  rw [isub_lam, isub_lam]
  exact RE2.expand2 hW hXX happL happR (stable_beta hW happL) (stable_beta hW happR) hm

/-! ### Paired formers, between different terms -/

theorem VEq.pi₂ {A A' B B' : Tm} {l : ℕ} (hA : VEq S Ψ Φ Γ A A' (.univ l)) (hB : VEq S Ψ Φ (A :: Γ) B B' (.univ l)) :
    VEq S Ψ Φ Γ (.pi A B) (.pi A' B') (.univ l) := by
  have e := EqTm0.pi hA.eq hB.eq
  exact ⟨e, valid_pi hW hA.v hB.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.sigma₂ {A A' B B' : Tm} {l : ℕ} (hA : VEq S Ψ Φ Γ A A' (.univ l)) (hB : VEq S Ψ Φ (A :: Γ) B B' (.univ l)) :
    VEq S Ψ Φ Γ (.sigma A B) (.sigma A' B') (.univ l) := by
  have e := EqTm0.sigma hA.eq hB.eq
  exact ⟨e, valid_sigma hW hA.v hB.v (presup hW e).1 (presup hW e).2 e⟩

theorem VEq.path₂ {L L' a a' b b' : Tm} {l : ℕ} (hL : VEq S (Ψ + 1) Φ.shift Γ.dshift L L' (.univ l))
    (ha : VEq S Ψ Φ Γ a a' (L.dinst .zero)) (hb : VEq S Ψ Φ Γ b b' (L.dinst .one)) :
    VEq S Ψ Φ Γ (.path L a b) (.path L' a' b') (.univ l) := by
  have e := EqTm0.path hL.eq ha.eq hb.eq
  exact ⟨e, valid_path hW hL.v ha.v hb.v (presup hW e).1 (presup hW e).2 e⟩

/-- `λ` with judgmentally equal domains. -/
theorem VEq.lamD₂ {A A' B t t' : Tm} {l : ℕ} (hpi : VTy S Ψ Φ Γ (.pi A B) (.univ l))
    (hA : VEq S Ψ Φ Γ A A' (.univ l)) (ht : VEq S Ψ Φ (A :: Γ) t t' B) :
    VEq S Ψ Φ Γ (.lam A t) (.lam A' t') (.pi A B) := by
  have hS := sigClosed_of_wfSig hW
  have hA0 := HasTy0.piDom hS hpi.ty
  have hty := HasTy0.lam hpi.ty (presup hW ht.eq).1
  have ht' := HasTy0.ctxConv hS (presup hW ht.eq).2 (presup hW hA.eq).2 (EqTm0.symm hA.eq)
  have ePi : EqTm0 S Ψ Φ Γ (.pi A B) (.pi A' B) (.univ l) := EqTm0.pi hA.eq (EqTm0.refl (HasTy0.piCod hS hpi.ty))
  have hty' := HasTy0.conv (HasTy0.lam (presup hW ePi).2 ht') (EqTm0.symm ePi)
  have e := lam_congr' hS hA0 hpi.ty hty' ht.eq
  exact ⟨e, valid_lamD hW hpi.v ht.v hty hty' e⟩


theorem VEq.pathC₂ {A A' a a' b b' : Tm} {l : ℕ} (hA : VEq S Ψ Φ Γ A A' (.univ l)) (ha : VEq S Ψ Φ Γ a a' A)
    (hb : VEq S Ψ Φ Γ b b' A) : VEq S Ψ Φ Γ (Tm.pathC A a b) (Tm.pathC A' a' b') (.univ l) := by
  have hAd := VEq.dwk' hW hA
  exact VEq.path₂ hW hAd (by rw [dshift_dinst]; exact ha) (by rw [dshift_dinst]; exact hb)

theorem VEq.isContr₂ {X X' : Tm} {l : ℕ} (hX : VEq S Ψ Φ Γ X X' (.univ l)) :
    VEq S Ψ Φ Γ (Tm.isContr X) (Tm.isContr X') (.univ l) := by
  have hXL := VEq.lty' hW hX
  have hX1 := VEq.wk' hW hXL.ty hX
  have hX1L := VEq.lty' hW hX1
  have hX2 := VEq.wk' hW hX1L.ty hX1
  have hv1 : VTy S Ψ Φ (X.shift :: X :: Γ) (.var 1) X.shift.shift := VTy.var' hW (Wf0.cons hX1L.ty) rfl
  have hv0 : VTy S Ψ Φ (X.shift :: X :: Γ) (.var 0) X.shift.shift := VTy.var' hW (Wf0.cons hX1L.ty) rfl
  exact VEq.sigma₂ hW hX (VEq.pi₂ hW hX1 (VEq.pathC₂ hW hX2 (VEq.refl' hv1) (VEq.refl' hv0)))

theorem VEq.fiber₂ {T T' A A' f f' y y' : Tm} {l : ℕ} (hT : VEq S Ψ Φ Γ T T' (.univ l))
    (hA : VEq S Ψ Φ Γ A A' (.univ l)) (hf : VEq S Ψ Φ Γ f f' (Tm.arrow T A)) (hy : VEq S Ψ Φ Γ y y' A) :
    VEq S Ψ Φ Γ (Tm.fiber T A f y) (Tm.fiber T' A' f' y') (.univ l) := by
  have hTL := VEq.lty' hW hT
  have hA1 := VEq.wk' hW hTL.ty hA
  have hf1 := VEq.wk' hW hTL.ty hf
  rw [arrow_shift] at hf1
  have happ := VEq.app' hW hf1 (VEq.refl' (VTy.var0' hW hTL))
  rw [shift_inst] at happ
  exact VEq.sigma₂ hW hT (VEq.pathC₂ hW hA1 happ (VEq.wk' hW hTL.ty hy))

theorem VEq.isEquiv₂ {T T' A A' f f' : Tm} {l : ℕ} (hT : VEq S Ψ Φ Γ T T' (.univ l))
    (hA : VEq S Ψ Φ Γ A A' (.univ l)) (hf : VEq S Ψ Φ Γ f f' (Tm.arrow T A)) :
    VEq S Ψ Φ Γ (Tm.isEquiv T A f) (Tm.isEquiv T' A' f') (.univ l) := by
  have hAL := VEq.lty' hW hA
  have hT1 := VEq.wk' hW hAL.ty hT
  have hA1 := VEq.wk' hW hAL.ty hA
  have hf1 := VEq.wk' hW hAL.ty hf
  rw [arrow_shift] at hf1
  exact VEq.pi₂ hW hA (VEq.isContr₂ hW (VEq.fiber₂ hW hT1 hA1 hf1 (VEq.refl' (VTy.var0' hW hAL))))

theorem VEq.arrow₂ {T T' A A' : Tm} {l : ℕ} (hT : VEq S Ψ Φ Γ T T' (.univ l)) (hA : VEq S Ψ Φ Γ A A' (.univ l)) :
    VEq S Ψ Φ Γ (Tm.arrow T A) (Tm.arrow T' A') (.univ l) :=
  VEq.pi₂ hW hT (VEq.wk' hW (VEq.lty' hW hT).ty hA)

theorem VEq.equiv₂ {T T' A A' : Tm} {l : ℕ} (hT : VEq S Ψ Φ Γ T T' (.univ l)) (hA : VEq S Ψ Φ Γ A A' (.univ l)) :
    VEq S Ψ Φ Γ (Tm.equiv T A) (Tm.equiv T' A') (.univ l) := by
  have hTA := VEq.arrow₂ hW hT hA
  have hTAL := VEq.lty' hW hTA
  have hv := VTy.var0' hW hTAL
  rw [arrow_shift] at hv
  exact VEq.sigma₂ hW hTA (VEq.isEquiv₂ hW (VEq.wk' hW hTAL.ty hT) (VEq.wk' hW hTAL.ty hA) (VEq.refl' hv))


/-- Transport along related lines of types of level `l`, with the left line constant on the face. -/
theorem VEq.transpL₂ {A A' a a' : Tm} {φ : I} {l : ℕ}
    (hA : VEq S (Ψ + 1) Φ.shift Γ.dshift A A' (.univ l)) (hφ : φ.Scoped Ψ)
    (hc : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (hty' : HasTy0 S Ψ Φ Γ (.transp A' φ a') (A.dinst .one))
    (ha : VEq S Ψ Φ Γ a a' (A.dinst .zero)) : VEq S Ψ Φ Γ (.transp A φ a) (.transp A' φ a') (A.dinst .one) := by
  have hAL := VEq.lty' hW hA
  have hty := (VTy.transp' hW hAL hφ hc (VEq.lty' hW ha)).ty
  exact VEq.transp' hW  hφ (ent_refl _)
    (ent_refl _) hty hty' hA hc.v ha

/-- The transport filler with a constant cofibration, between related lines and starts. -/
theorem VEq.tfill₂ {C C' a a' : Tm} {l : ℕ} (hC : VEq S (Ψ + 1) Φ.shift Γ.dshift C C' (.univ l))
    (ha : VEq S Ψ Φ Γ a a' (C.dinst .zero)) :
    VEq S (Ψ + 1) Φ.shift Γ.dshift (KubusCore.Meta.tfill C a) (KubusCore.Meta.tfill C' a') C := by
  have hS := sigClosed_of_wfSig hW
  have hCL := VEq.lty' hW hC
  have hCR := VEq.rty' hW hC
  have haR : VTy S Ψ Φ Γ a' (C'.dinst .zero) :=
    VTy.conv' hW (VEq.rty' hW ha) (VEq.dsubst' hW .zero trivial hC)
  have tR := (VTy.tfill' hW hCR haR).1
  have hw0 := wf_unshift hS (wf_of_ty hCL.ty)
  have hs := scoped_of_wf hw0
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hv0' : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hL := VTy.bind2' hW (X := Φ.shift.shift) (r := .and (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hs (ent_refl _)
    (hw0.dwk2 hS) hCL
  rw [univ_dsubst] at hL
  have hL₂ := VEq.bind2' hW (X := Φ.shift.shift) (r := .and (.var 1) (.var 0)) ⟨hv1, hv0'⟩ hs (ent_refl _)
    (hw0.dwk2 hS) hC
  rw [univ_dsubst] at hL₂
  let Y : I := (cof Φ.shift (.neg (.var 0))).shift
  have hYs : Y.Scoped (Ψ + 1 + 1) := KubusCore.I.scoped_shift ⟨KubusCore.I.scoped_shift hs, hv0⟩
  have hYΦ : I.Entails Y Φ.shift.shift := ent_shift (ent_and_left _ _)
  have hY1 : I.Entails Y (I.lit 1 false) := ent_shift (ent_and_right _ (.neg (.var 0)))
  have hYΦ2 : I.Entails Y (Φ.subst (fun n => .var (n + 2))) := by rw [I_add2]; exact hYΦ
  have hwY : Wf0 S (Ψ + 2) Y (Ctx.dren 2 Γ) := by
    rw [Ctx.dren_two]; exact (hw0.dwk2 hS).restrict hYs hYΦ
  have hconst : VEq S (Ψ + 1 + 1) Y Γ.dshift.dshift
      (C.dsubst (Tm.bind2 (.and (.var 1) (.var 0))))
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero).dshift (.univ l) := by
    have hLY := VTy.restrict' hW hYs hYΦ hL
    have e1 := VEq.faceU' hW (i := 1) (d := false) hv1 hY1 hLY
    rw [tf_L1] at e1
    have e2 := VTy.lineIeq hW hCL (k := 2) (r := .and .zero (.var 0)) (r' := .zero) hYΦ2
      ⟨trivial, hv0'⟩ trivial (I_eq_and_zero _) hwY
    rw [Ctx.dren_two] at e2
    have hL0 := VTy.restrict' hW hYs hYΦ
      (VTy.dwk' hW (VTy.dsubst' hW (Φ := Φ.shift) (Γ := Γ.dshift) .zero trivial hL))
    rw [tf_L0s] at hL0
    have e3 := VEq.faceU' hW (i := 1) (d := false) hv1 hY1 hL0
    rw [tf_L0s1] at e3
    have e4 := VTy.lineIeq hW hCL (k := 2) (r := .and .zero .zero) (r' := .zero) hYΦ2
      ⟨trivial, trivial⟩ trivial (I_eq_and_zero _) hwY
    rw [Ctx.dren_two] at e4
    rw [tf_L0s]
    exact VEq.trans' hW e1 (VEq.trans' hW e2 (VEq.symm' hW (VEq.trans' hW e3 e4)))
  have hwX : Wf0 S (Ψ + 1) Φ.shift (Ctx.dren 1 Γ) := wf_of_ty hCL.ty
  have ha' : VEq S (Ψ + 1) Φ.shift Γ.dshift a.dshift a'.dshift
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .zero) := by
    rw [tf_L0]
    have e := VTy.lineIeq hW hCL (k := 1) (r := .zero) (r' := .and (.var 0) .zero) (ent_refl _) trivial
      ⟨hv0, trivial⟩ (I_eq_symm (I_eq_and_zero_r _)) hwX
    rw [sk_zero1] at e
    exact VEq.conv' hW (VEq.dwk' hW ha) e
  have eC : VEq S (Ψ + 1) Φ.shift Γ.dshift ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) C (.univ l) := by
    have e := VTy.lineIeq hW hCL (k := 1) (r := .and (.var 0) .one) (r' := .var 0) (ent_refl _)
      ⟨hv0, trivial⟩ hv0 (I_eq_and_one_r _) hwX
    rw [sk_var1] at e
    rw [tf_L1']; exact e
  have hty' : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (KubusCore.Meta.tfill C' a')
      ((C.dsubst (Tm.bind2 (.and (.var 1) (.var 0)))).dinst .one) :=
    HasTy0.conv tR.ty (EqTm0.trans (EqTm0.symm hC.eq) (EqTm0.symm eC.eq))
  have ht0 := VEq.transpL₂ hW hL₂ (show (I.neg (.var 0)).Scoped (Ψ + 1) from hv0) hconst hty' ha'
  exact VEq.conv' hW ht0 eC


/-- Transport along related lines, as functions. -/
theorem VEq.lineFun₂ {B B' : Tm} {l : ℕ} (hB : VEq S (Ψ + 1) Φ.shift Γ.dshift B B' (.univ l)) :
    VEq S (Ψ + 1) Φ.shift Γ.dshift (Tm.lineFun B) (Tm.lineFun B') (Tm.arrow (B.dinst .zero).dshift B) := by
  have hB0 := VEq.dsubst' hW .zero trivial hB
  have hB0d := VEq.dwk' hW hB0
  have hB0dL := VEq.lty' hW hB0d
  have hBL := VEq.lty' hW hB
  have hC : VEq S (Ψ + 1) Φ.shift (Ctx.dshift (B.dinst .zero :: Γ)) B.shift B'.shift (.univ l) :=
    VEq.wk' hW hB0dL.ty hB
  have ha : VEq S Ψ Φ (B.dinst .zero :: Γ) (.var 0) (.var 0) (B.shift.dinst .zero) := by
    rw [shift_dinst_comm]; exact VEq.refl' (VTy.var0' hW (VEq.lty' hW hB0))
  have ht := VEq.tfill₂ hW hC ha
  have hpi : VTy S (Ψ + 1) Φ.shift Γ.dshift (.pi (B.dinst .zero).dshift B.shift) (.univ l) :=
    VTy.pi' hW hB0dL (VTy.wk' hW hB0dL.ty hBL)
  exact VEq.lamD₂ hW hpi hB0d ht


/-! ### The identity is an equivalence, between related identities -/

theorem VEq.idIsEquiv₂ {T T' f f' : Tm} {l : ℕ} (h : VIsId S Ψ Φ Γ T f l) (h' : VIsId S Ψ Φ Γ T' f' l)
    (hT : VEq S Ψ Φ Γ T T' (.univ l)) (hf : VEq S Ψ Φ Γ f f' (Tm.arrow T T)) :
    VEq S Ψ Φ Γ (Tm.idIsEquiv T f) (Tm.idIsEquiv T' f') (Tm.isEquiv T T f) := by
  have hE := VTy.isEquiv' hW h.ty h.ty h.fn
  rw [isEquiv_eq] at hE ⊢
  rw [idIsEquiv_eq, idIsEquiv_eq]
  refine VEq.lamD₂ hW hE hT ?_
  have h1 := h.wk hW h.ty.ty
  have hy : VTy S Ψ Φ (T :: Γ) (.var 0) T.shift := VTy.var0' hW h.ty
  have hF := VTy.fiber' hW h1.ty h1.ty h1.fn hy
  have hc := VTy.center' hW h1 hy
  have hpi : VTy S Ψ Φ (T :: Γ) (.pi (Tm.fiber T.shift T.shift f.shift (.var 0))
      (Tm.pathC (Tm.fiber T.shift T.shift f.shift (.var 0)).shift (KubusCore.Meta.center (.var 0)).shift (.var 0)))
      (.univ l) :=
    VTy.pi' hW hF (VTy.pathC' hW (VTy.wk' hW hF.ty hF) (VTy.wk' hW hF.ty hc) (VTy.var0' hW hF))
  have hC := VTy.isContr' hW hF
  rw [isContr_eq] at hC ⊢
  have hT1 := VEq.wk' hW h.ty.ty hT
  have hf1 := VEq.wk' hW h.ty.ty hf
  rw [arrow_shift] at hf1
  have hFF := VEq.fiber₂ hW hT1 hT1 hf1 (VEq.refl' hy)
  refine VEq.pair' hW hC (VEq.refl' hc) ?_
  rw [K_inst]
  exact VEq.lamD₂ hW hpi hFF (VEq.refl' (VTy.contr' hW h1 hy))

/-- Transport along related lines of types of level `l` gives related equivalences between their endpoints. -/
theorem VEq.lineEquiv₂ {B B' : Tm} {l : ℕ} (hB : VEq S (Ψ + 1) Φ.shift Γ.dshift B B' (.univ l)) :
    VEq S Ψ Φ Γ (Tm.lineEquiv B) (Tm.lineEquiv B') (Tm.equiv (B.dinst .zero) (B.dinst .one)) := by
  have hS := sigClosed_of_wfSig hW
  have hBL := VEq.lty' hW hB
  have hBR := VEq.rty' hW hB
  have hw0 := wf_unshift hS (wf_of_ty hBL.ty)
  have hs := scoped_of_wf hw0
  have hB0 := VTy.dsubst' hW .zero trivial hBL
  have hB1 := VTy.dsubst' hW .one trivial hBL
  have hB0d := VTy.dwk' hW hB0
  have hB0' := VTy.dsubst' hW .zero trivial hBR
  have hB0d' := VTy.dwk' hW hB0'
  have eB0 := VEq.dsubst' hW .zero trivial hB
  have eB0d := VEq.dwk' hW eB0
  obtain ⟨hlf, hid⟩ := VTy.lineFun' hW hBL
  obtain ⟨hlf', hid'⟩ := VTy.lineFun' hW hBR
  have elf := VEq.lineFun₂ hW hB
  have hf : ∀ r : I, r.Scoped Ψ → VTy S Ψ Φ Γ ((Tm.lineFun B).dinst r) (Tm.arrow (B.dinst .zero) (B.dinst r)) := by
    intro r hr
    have := VTy.dsubst' hW r hr hlf; rwa [arrow_dinst, dshift_dinst] at this
  have hf' : ∀ r : I, r.Scoped Ψ → VTy S Ψ Φ Γ ((Tm.lineFun B').dinst r) (Tm.arrow (B'.dinst .zero) (B'.dinst r)) := by
    intro r hr
    have := VTy.dsubst' hW r hr hlf'; rwa [arrow_dinst, dshift_dinst] at this
  have ef : ∀ r : I, r.Scoped Ψ → VEq S Ψ Φ Γ ((Tm.lineFun B).dinst r) ((Tm.lineFun B').dinst r)
      (Tm.arrow (B.dinst .zero) (B.dinst r)) := by
    intro r hr
    have := VEq.dsubst' hW r hr elf; rwa [arrow_dinst, dshift_dinst] at this
  -- the line of `isEquiv`s
  have hE := VTy.isEquiv' hW hB0d hBL hlf
  have hE' := VTy.isEquiv' hW hB0d' hBR hlf'
  have eE := VEq.isEquiv₂ hW eB0d hB elf
  have hab : I.Entails (cof Φ .zero).shift .zero := ent_shift (ent_and_right Φ .zero)
  have hZs : (cof Φ .zero).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, trivial⟩
  have hcE := VEq.absurd' hW hab (VTy.restrict' hW hZs (ent_shift (ent_and_left _ _)) hE).ty
    (VTy.restrict' hW hZs (ent_shift (ent_and_left _ _)) (VTy.dwk' hW (VTy.dsubst' hW .zero trivial hE))).ty
  have hcE' := VEq.absurd' hW hab (VTy.restrict' hW hZs (ent_shift (ent_and_left _ _)) hE').ty
    (VTy.restrict' hW hZs (ent_shift (ent_and_left _ _)) (VTy.dwk' hW (VTy.dsubst' hW .zero trivial hE'))).ty
  -- the starts
  have hbase := VTy.idIsEquiv' hW (Ψ := Ψ) (Φ := Φ) (Γ := Γ) ⟨hB0, hf .zero trivial, hid⟩
  have hbase' := VTy.idIsEquiv' hW (Ψ := Ψ) (Φ := Φ) (Γ := Γ) ⟨hB0', hf' .zero trivial, hid'⟩
  have ebase := VEq.idIsEquiv₂ hW ⟨hB0, hf .zero trivial, hid⟩
    ⟨hB0', hf' .zero trivial, hid'⟩ eB0 (ef .zero trivial)
  have ht' := VTy.transp' hW hE' (φ := .zero) trivial hcE' (by rw [isEquiv_dinst, dshift_dinst]; exact hbase')
  have eE1 := VEq.dsubst' hW .one trivial eE
  have ht'L : HasTy0 S Ψ Φ Γ (.transp (Tm.isEquiv (B'.dinst .zero).dshift B' (Tm.lineFun B')) .zero
      (Tm.idIsEquiv (B'.dinst .zero) ((Tm.lineFun B').dinst .zero)))
      ((Tm.isEquiv (B.dinst .zero).dshift B (Tm.lineFun B)).dinst .one) :=
    HasTy0.conv ht'.ty (EqTm0.symm eE1.eq)
  have et := VEq.transpL₂ hW eE (φ := .zero) trivial hcE ht'L
    (by rw [isEquiv_dinst, dshift_dinst]; exact ebase)
  rw [isEquiv_dinst, dshift_dinst] at et
  have hEq := VTy.equiv' hW hB0 hB1
  rw [equiv_eq] at hEq ⊢
  rw [lineEquiv_eq, lineEquiv_eq]
  exact VEq.pair' hW hEq (ef .one trivial) (by rw [isEquiv_inst]; exact et)

end

end Model.Whnf
