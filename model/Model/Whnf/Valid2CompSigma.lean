import Model.Whnf.Valid2Fill

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

theorem valid_transpSigma_rule {A B u0 T : Tm} {φ : I}
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
  obtain ⟨htf, e0, e1, eX⟩ := VTy.transpFill' hW hA hφ hcD hf0
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
  have ht := VTy.transp' hW hBa hφ hBC hbase
  rw [tsg_inst_dinst] at ht
  have hL1 := VTy.dsubst' hW .one trivial hLp
  have hA1 : VTy S Ψ Φ Γ (A.dinst .one) (.univ l) :=
    ⟨HasTy0.sigmaDom hS hL1.ty, valid_sigmaDom hW hL1.v (HasTy0.sigmaDom hS hL1.ty)⟩
  have hB1 : VTy S Ψ Φ (A.dinst .one :: Γ) (B.subst (Tm.up Tm.var) (I.inst0 .one)) (.univ l) :=
    ⟨HasTy0.sigmaCod hS hL1.ty, valid_sigmaCod hW hL1.v (HasTy0.sigmaCod hS hL1.ty)⟩
  have htr' := VTy.transp' hW hA hφ hcD hf0
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

theorem valid_hcompSigma_rule {A B u u0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.hcomp (.sigma A B) φ u u0) T)
    (hv : Valid2 S Ψ Φ Γ (.hcomp (.sigma A B) φ u u0) (.hcomp (.sigma A B) φ u u0) T)
    (hinv : HcompInv S Ψ Φ Γ (.sigma A B) φ u u0 T) :
    Valid2 S Ψ Φ Γ (.hcomp (.sigma A B) φ u u0) (Tm.hcompSigma A B φ u u0) T := by
  obtain ⟨l, hφ, hSigV, huV, hu0V, hsV, htr, hSig, hu, hu0, hside⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hSig
  have hX : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hXs : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hX
  have hSigp : VTy S Ψ Φ Γ (.sigma A B) (.univ l) := ⟨hSig, hSigV⟩
  have hup : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (Tm.sigma A B).dshift := ⟨hu, huV⟩
  have hu0p : VTy S Ψ Φ Γ u0 (.sigma A B) := ⟨hu0, hu0V⟩
  have hsidep : VEq S Ψ (cof Φ φ) Γ (u.dinst .zero) u0 (.sigma A B) := ⟨hside, hsV⟩
  have hA : VTy S Ψ Φ Γ A (.univ l) := ⟨HasTy0.sigmaDom hS hSig, valid_sigmaDom hW hSigV (HasTy0.sigmaDom hS hSig)⟩
  have hB : VTy S Ψ Φ (A :: Γ) B (.univ l) :=
    ⟨HasTy0.sigmaCod hS hSig, valid_sigmaCod hW hSigV (HasTy0.sigmaCod hS hSig)⟩
  rw [sigma_dshift] at hup
  have hfu := VTy.fst' hW hup
  have hsu := VTy.snd' hW hup
  have hfu0 := VTy.fst' hW hu0p
  have hsu0 := VTy.snd' hW hu0p
  have hsf : VEq S Ψ (cof Φ φ) Γ ((Tm.fst u).dinst .zero) (.fst u0) A := VEq.fst' hW hsidep
  have hss := VEq.snd' hW hsidep
  obtain ⟨hf, hf0, hf1, hfφ⟩ := VTy.hfill' hW hA hφ hfu hfu0 hsf
  have ha := VTy.hcomp' hW hA hφ hfu hfu0 hsf
  -- the line of the second component
  have hAd := VTy.dwk' hW hA
  have hBd := VTy.dwk' hW hB
  have hC : VTy S (Ψ + 1) Φ.shift Γ.dshift (B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))) (.univ l) :=
    VTy.subst' hW hAd hBd hf
  -- the tube
  have hAdX := VTy.restrict' hW (Φ' := (cof Φ φ).shift) hXs (ent_shift (ent_and_left Φ φ)) hAd
  have hBdX := VTy.restrict' hW (Φ' := (cof Φ φ).shift) hXs (ent_shift (ent_and_left Φ φ)) hBd
  have hu' : VTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift (.snd u) (B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))) :=
    VTy.conv' hW hsu (VTy.inst_congr' hW hAdX hBdX (VEq.symm' hW hfφ))
  -- the base
  have hf0t : VTy S Ψ Φ Γ ((Tm.hfill A φ (.fst u) (.fst u0)).dinst .zero) (A.dshift.dinst .zero) :=
    VTy.dsubst' hW .zero trivial hf
  rw [dshift_dinst] at hf0t
  have hu0' : VTy S Ψ Φ Γ (.snd u0) ((B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))).dinst .zero) := by
    rw [inst_dshift_dinst]
    exact VTy.conv' hW hsu0 (VTy.inst_congr' hW hA hB (VEq.symm' hW hf0))
  -- the side condition
  have hAX := VTy.restrict' hW hX (ent_and_left Φ φ) hA
  have hBX := VTy.restrict' hW hX (ent_and_left Φ φ) hB
  have hside' : VEq S Ψ (cof Φ φ) Γ ((Tm.snd u).dinst .zero) (.snd u0)
      ((B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))).dinst .zero) := by
    rw [inst_dshift_dinst]
    exact VEq.conv' hW hss (VTy.inst_congr' hW hAX hBX
      (VEq.trans' hW hsf (VEq.symm' hW (VEq.restrict' hW hX (ent_and_left Φ φ) hf0))))
  have hcomp' := VTy.comp' hW hC hφ hu' hu0' hside'
  rw [inst_dshift_dinst] at hcomp'
  have hb := VTy.conv' hW hcomp' (VTy.inst_congr' hW hA hB hf1)
  have hy : VTy S Ψ Φ Γ (Tm.hcompSigma A B φ u u0) (.sigma A B) := by
    rw [hcompSigma_eq]; exact VTy.pair' hW hSigp ha hb
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hy.v htr hT
  -- where the face holds: the tube's end, by η and the faces of the components
  have hX0Φ : I.Entails (cof Φ φ) Φ := ent_and_left _ _
  have hφ0 : I.Entails (cof Φ φ) φ := ent_and_right _ _
  have hu1 : VTy S Ψ (cof Φ φ) Γ (u.dinst .one) (.sigma A B) := by
    refine ⟨?_, valid_tube_end hW hφ .one trivial huV hu hSig⟩
    have := HasTy0.dsubst hS (Φ := cof Φ φ) hu (r := .one) trivial
    rwa [dshift_dinst] at this
  have hη := VEq.sigmaEta' hW hu1
  have haX := VTy.restrict' hW hX hX0Φ ha
  have e1 := VEq.hcompFace' hW hφ0 haX
  have hfa : VEq S Ψ (cof Φ φ) Γ (.fst (u.dinst .one)) (.hcomp A φ (.fst u) (.fst u0)) A := VEq.symm' hW e1
  have hcX := VTy.restrict' hW hX hX0Φ hcomp'
  have e2 := VEq.hcompFace' hW hφ0 hcX
  have hrhs : VTy S Ψ (cof Φ φ) Γ _ _ := ⟨(presup hW e2.eq).2, valid_trans hW (valid_symm hW e2.v) e2.v⟩
  have e3 := VEq.transpFace' hW (ent_one _) hrhs
  have e23 := VEq.trans' hW e2 e3
  have hBe : VEq S Ψ (cof Φ φ) Γ (B.inst ((Tm.hfill A φ (.fst u) (.fst u0)).dinst .one)) (B.inst (.fst (u.dinst .one)))
      (.univ l) :=
    VTy.inst_congr' hW hAX hBX (VEq.trans' hW (VEq.restrict' hW hX hX0Φ hf1) e1)
  have hb2 : VEq S Ψ (cof Φ φ) Γ (.snd (u.dinst .one))
      (Tm.comp (B.dshift.inst (Tm.hfill A φ (.fst u) (.fst u0))) φ (.snd u) (.snd u0)) (B.inst (.fst (u.dinst .one))) :=
    VEq.symm' hW (VEq.conv' hW e23 hBe)
  have hpair := VEq.pair' hW (VTy.restrict' hW hX hX0Φ hSigp) hfa hb2
  rw [← hcompSigma_eq] at hpair
  have hb := valid_conv_tr (VEq.trans' hW hη hpair).v (htr.restrict hX0Φ)
    fun k c => hT k (c.restrictTo hX0Φ)
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e4 : c.L (Tm.hcompSigma A B φ u u0) = Tm.hcompSigma (c.L A) (B.subst (Tm.up c.γ) c.σ.τ) (φ.subst c.σ.τ)
        (u.subst (dupS c.γ) (I.up c.σ.τ)) (c.L u0) := hcompSigma_subst _ _ A B φ u u0
    rw [e4]
    exact ⟨.step (step_hcomp_sigma hn) (.refl _), EqTm.hcompSigma (c.ty hW h)⟩
  · rw [CSub2.L_dinst hW]
    exact ⟨.step (step_hcomp_face hf) (.refl _), EqTm.hcompFace hf (c.ty hW h)⟩

end

end Model.Whnf
