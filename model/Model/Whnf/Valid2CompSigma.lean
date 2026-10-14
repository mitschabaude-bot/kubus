import Model.Whnf.Valid2Pair

/-!
# Validity of the computation rules in `Σ`

`transpSigma` and `hcompSigma`, by the typing derivations of their contracta (`KanTransp.lean`,
`KanSigma.lean`) with validity, from the Kan property of the components.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

theorem valid_transpSigma_rule (hKT : KTAll S) {A B u0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.transp (.sigma A B) φ u0) T)
    (hv : Valid2 S Ψ Φ Γ (.transp (.sigma A B) φ u0) (.transp (.sigma A B) φ u0) T)
    (hinv : TranspInv S Ψ Φ Γ (.sigma A B) φ u0 T) :
    Valid2 S Ψ Φ Γ (.transp (.sigma A B) φ u0) (Tm.transpSigma A B φ u0) T := by
  obtain ⟨l, hφ, hLV, hCV, hu0V, htr, hL, hc, hu0⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hu0
  have hLp : VTy S (Ψ + 1) Φ.shift Γ.dshift (.sigma A B) (.univ l) := ⟨hL, hLV⟩
  have hcp : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (.sigma A B) ((Tm.sigma A B).dinst .zero).dshift (.univ l) :=
    ⟨hc, hCV⟩
  have hu0p : VTy S Ψ Φ Γ u0 ((Tm.sigma A B).dinst .zero) := ⟨hu0, hu0V⟩
  have hA : VTy S (Ψ + 1) Φ.shift Γ.dshift A (.univ l) :=
    ⟨HasTy0.sigmaDom hS hL, valid_sigmaDom hW hLV (HasTy0.sigmaDom hS hL)⟩
  have hB : VTy S (Ψ + 1) Φ.shift (A :: Γ.dshift) B (.univ l) :=
    ⟨HasTy0.sigmaCod hS hL, valid_sigmaCod hW hLV (HasTy0.sigmaCod hS hL)⟩
  have hcD := VEq.sigmaInjDom' hW (A' := (A.dinst .zero).dshift) hcp
  have hf0 := VTy.fst' hW (A := A.dinst .zero) (B := B.subst (Tm.up Tm.var) (I.inst0 .zero)) hu0p
  have hs0 := VTy.snd' hW (A := A.dinst .zero) (B := B.subst (Tm.up Tm.var) (I.inst0 .zero)) hu0p
  obtain ⟨htf, e0, e1, eX⟩ := VTy.transpFill' hW hKT hA hφ hcD hf0
  have hBa := VTy.subst' hW hA hB htf
  -- constancy of the second line
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift ⟨hs, hφ⟩
  have hXΦ : I.Entails (cof Φ φ).shift Φ.shift := ent_shift (ent_and_left _ _)
  have haX := VTy.restrict' hW hXs hXΦ htf
  have ec := VEq.sigmaInjCod' hW (A := A) (B := B) (A' := (A.dinst .zero).dshift)
    (B' := (B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen id) Nat.succ) hcp haX
  have hRz : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift ((Tm.sigma A B).dinst .zero).dshift (.univ l) :=
    VTy.restrict' hW hXs hXΦ (VTy.dwk' hW (VTy.dsubst' hW .zero trivial hLp))
  have hAz : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift (A.dinst .zero).dshift (.univ l) :=
    ⟨HasTy0.sigmaDom hS hRz.ty, valid_sigmaDom hW hRz.v (HasTy0.sigmaDom hS hRz.ty)⟩
  have hBz : VTy S (Ψ + 1) (cof Φ φ).shift ((A.dinst .zero).dshift :: Γ.dshift)
      ((B.subst (Tm.up Tm.var) (I.inst0 .zero)).ren (Tm.upRen id) Nat.succ) (.univ l) :=
    ⟨HasTy0.sigmaCod hS hRz.ty, valid_sigmaCod hW hRz.v (HasTy0.sigmaCod hS hRz.ty)⟩
  have had := VTy.restrict' hW hXs hXΦ (VTy.dwk' hW (VTy.dsubst' hW .zero trivial htf))
  have he := VEq.trans' hW (VEq.conv' hW eX hcD) (VEq.symm' hW (VEq.restrict' hW hXs hXΦ (VEq.dwk' hW e0)))
  have e2 := VTy.inst_congr' hW hAz hBz he
  have hBC : VEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift (B.inst (Tm.transpFill A φ (.fst u0)))
      ((B.inst (Tm.transpFill A φ (.fst u0))).dinst .zero).dshift (.univ l) := by
    rw [tsg_inst_dinst_dshift]; exact VEq.trans' hW ec e2
  -- the base
  have hL0 := VTy.dsubst' hW .zero trivial hLp
  have hA0 : VTy S Ψ Φ Γ (A.dinst .zero) (.univ l) :=
    ⟨HasTy0.sigmaDom hS hL0.ty, valid_sigmaDom hW hL0.v (HasTy0.sigmaDom hS hL0.ty)⟩
  have hB0 : VTy S Ψ Φ (A.dinst .zero :: Γ) (B.subst (Tm.up Tm.var) (I.inst0 .zero)) (.univ l) :=
    ⟨HasTy0.sigmaCod hS hL0.ty, valid_sigmaCod hW hL0.v (HasTy0.sigmaCod hS hL0.ty)⟩
  have hbase : VTy S Ψ Φ Γ (.snd u0) ((B.inst (Tm.transpFill A φ (.fst u0))).dinst .zero) := by
    rw [tsg_inst_dinst]
    exact VTy.conv' hW hs0 (VTy.inst_congr' hW hA0 hB0 (VEq.symm' hW e0))
  have ht := VTy.transpG hW hKT hBa hφ hBC hbase
  rw [tsg_inst_dinst] at ht
  have hL1 := VTy.dsubst' hW .one trivial hLp
  have hA1 : VTy S Ψ Φ Γ (A.dinst .one) (.univ l) :=
    ⟨HasTy0.sigmaDom hS hL1.ty, valid_sigmaDom hW hL1.v (HasTy0.sigmaDom hS hL1.ty)⟩
  have hB1 : VTy S Ψ Φ (A.dinst .one :: Γ) (B.subst (Tm.up Tm.var) (I.inst0 .one)) (.univ l) :=
    ⟨HasTy0.sigmaCod hS hL1.ty, valid_sigmaCod hW hL1.v (HasTy0.sigmaCod hS hL1.ty)⟩
  have htr' := VTy.transpG hW hKT hA hφ hcD hf0
  have ht' := VTy.conv' hW ht (VTy.inst_congr' hW hA1 hB1 e1)
  have hy : VTy S Ψ Φ Γ (Tm.transpSigma A B φ u0) ((Tm.sigma A B).dinst .one) :=
    VTy.pair' hW (A := A.dinst .one) (B := B.subst (Tm.up Tm.var) (I.inst0 .one)) hL1 htr' ht'
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hy.v htr hT
  -- where the face holds: `u0`, by η and the faces of the components
  have hX0s : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hX0Φ : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have hφ0 : I.Entails (cof Φ φ) φ := ent_and_right _ _
  have hη := VEq.sigmaEta' hW (A := A.dinst .zero) (B := B.subst (Tm.up Tm.var) (I.inst0 .zero))
    (VTy.restrict' hW hX0s hX0Φ hu0p)
  have hk1 := VEq.dsubst' hW .one trivial hcp
  rw [dshift_dinst] at hk1
  have hη1 := VEq.conv' hW hη (VEq.symm' hW hk1)
  have ha1 := VEq.symm' hW (VEq.transpFace' hW hφ0 (VTy.restrict' hW hX0s hX0Φ htr'))
  have hb1 := VEq.transpFace' hW hφ0 (VTy.restrict' hW hX0s hX0Φ ht)
  have hfa := VEq.trans' hW (VEq.restrict' hW hX0s hX0Φ e1) (VEq.symm' hW ha1)
  have hBfa := VTy.inst_congr' hW (VTy.restrict' hW hX0s hX0Φ hA1) (VTy.restrict' hW hX0s hX0Φ hB1) hfa
  have hb2 := VEq.conv' hW (VEq.symm' hW hb1) hBfa
  have hpair := VEq.pair' hW (A := A.dinst .one) (B := B.subst (Tm.up Tm.var) (I.inst0 .one))
    (VTy.restrict' hW hX0s hX0Φ hL1) ha1 hb2
  have hb := valid_conv_tr (VEq.trans' hW hη1 hpair).v (htr.restrict (ent_and_left _ _))
    fun k c => hT k (c.restrictTo (ent_and_left _ _))
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e3 : c.L (Tm.transpSigma A B φ u0) = Tm.transpSigma (A.subst (dupS c.γ) (I.up c.σ.τ))
        (B.subst (Tm.up (dupS c.γ)) (I.up c.σ.τ)) (φ.subst c.σ.τ) (c.L u0) := transpSigma_subst _ _ A B φ u0
    rw [e3]
    exact ⟨.step (step_transp_sigma hn) (.refl _), EqTm.transpSigma (c.ty hW h)⟩
  · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (c.ty hW h)⟩

end

end Model.Whnf
