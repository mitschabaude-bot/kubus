import Model.Whnf.Valid2HcompCon
import Model.Whnf.Kan2DataHITStep
import Model.Whnf.Kan2DataHITRel

/-!
# Transport of formal compositions

The binary validity of `transpHcomp` (higher inductive types with parameters): the transport of a formal
composition is related to the composition of the transports of its tube and base. Formal compositions
are related by `hcomp_relD` from tubes related pointwise; the transports are related by the Kan property of the
instances of the line (a hypothesis).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ}

/-- The tube of the `transpHcomp` contractum under a substitution. -/
theorem transp_skip_subst (A : Tm) (φ : I) (u : Tm) (γ : ℕ → Tm) (τ : ℕ → I) :
    (Tm.transp (A.dsubst skip1I) φ.shift u).subst (dupS γ) (I.up τ) =
      .transp ((A.subst (dupS γ) (I.up τ)).dsubst skip1I) (φ.subst τ).shift (u.subst (dupS γ) (I.up τ)) := by
  show Tm.transp ((A.dsubst skip1I).subst (dupS (dupS γ)) (I.up (I.up τ))) ((φ.shift).subst (I.up τ)) _ = _
  rw [I_shift_subst_up]
  congr 1
  simp only [Tm.dsubst, subst_subst]
  refine subst_congr (fun n => ?_) (fun i => ?_) A
  · show (Tm.var n).subst (dupS (dupS γ)) (I.up (I.up τ)) = (dupS γ n).subst Tm.var skip1I
    simp only [Tm.subst, dupS]
    rw [dshift_skip1I]
  · rcases i with _ | i
    · rfl
    · show (I.var (i + 2)).subst (I.up (I.up τ)) = ((τ i).shift).subst skip1I
      rw [I_shift_skip1I]; rfl

/-- The tube of the `transpHcomp` contractum at `1`. -/
theorem transp_skip_dinst1 (A : Tm) (φ : I) (u : Tm) :
    (Tm.transp (A.dsubst skip1I) φ.shift u).dinst .one = .transp A φ (u.dinst .one) := by
  show Tm.transp ((A.subst Tm.var skip1I).subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 .one)))
    (φ.shift.subst (I.inst0 .one)) (u.dinst .one) = _
  congr 1
  · rw [subst_subst]
    apply subst_id_of
    · intro n; rfl
    · intro i; cases i with
      | zero => rfl
      | succ i => rfl
  · simp only [I.shift, I.ren, I_subst_subst]; exact I_subst_var φ

section
variable (hW : WfSig S)
include hW
variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- Transport along a valid line, at a related substitution, of related elements of the start. -/
theorem transp_rel_at {A : Tm}
    {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ)
    (hLV : Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A (.univ l))
    (hCV : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (.univ l))
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (c : CSub2 S Ψ Φ Γ k) {b b' : Tm} (hb : RE2 S k (c.L (A.dinst .zero)) b b') :
    RE2 S k (c.L (A.dinst .one)) (.transp ((c.up hW).L A) (φ.subst c.σ.τ) b)
      (.transp ((c.up hW).R A) (φ.subst c.σ'.τ) b') := by
  have hφL := I.scoped_subst hφ c.σ.sc
  have hφR := I.scoped_subst hφ c.σ'.sc
  have e0 : c.L (A.dinst .zero) = ((c.up hW).L A).dinst .zero := CSub2.L_dinst hW c A .zero
  have e1 : c.L (A.dinst .one) = ((c.up hW).L A).dinst .one := CSub2.L_dinst hW c A .one
  rw [e0] at hb
  rw [e1]
  have hLt : HasTy S (k + 1) .one [] ((c.up hW).L A) (.univ l) := (c.up hW).ty hW hL
  have hLt' : HasTy S (k + 1) .one [] ((c.up hW).R A) (.univ l) := (c.up hW).tyR hW hL
  have eLR : EqTm S (k + 1) .one [] ((c.up hW).L A) ((c.up hW).R A) (.univ l) := (c.up hW).eqLR hW hL
  have hcL : EqTm S (k + 1) (cof .one (φ.subst c.σ.τ)).shift [] ((c.up hW).L A) (((c.up hW).L A).dinst .zero).dshift
      (.univ l) := by
    have h := (c.diagL hW).eqCofUp hW hφL hc
    have e : ((c.diagL hW).up hW).R (A.dinst .zero).dshift = (((c.up hW).L A).dinst .zero).dshift := by
      show (A.dinst .zero).dshift.subst (dupS c.γ) (I.up c.σ.τ) = _
      rw [dshift_dup_subst]; exact congrArg Tm.dshift e0
    rw [e] at h; exact h
  have hcR : EqTm S (k + 1) (cof .one (φ.subst c.σ'.τ)).shift [] ((c.up hW).R A) (((c.up hW).R A).dinst .zero).dshift
      (.univ l) := by
    have h := (c.diagR hW).eqCofUp hW hφR hc
    have e : ((c.diagR hW).up hW).R (A.dinst .zero).dshift = (((c.up hW).R A).dinst .zero).dshift := by
      show (A.dinst .zero).dshift.subst (dupS c.γ') (I.up c.σ'.τ) = _
      rw [dshift_dup_subst]; exact congrArg Tm.dshift (CSub2.R_dinst hW c A .zero)
    rw [e] at h; exact h
  -- the ends of the lines
  have hT0 := hLV.tySelf hW (c.cons .zero .zero trivial trivial (I_eq_refl _))
  rw [CSub2.L_cons hW, CSub2.R_cons hW] at hT0
  have hT1 := hLV.tySelf hW (c.cons .one .one trivial trivial (I_eq_refl _))
  rw [CSub2.L_cons hW, CSub2.R_cons hW] at hT1
  have tyB : ∀ {X Z : Tm}, RT2 S k X Z → TyEq S k X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  have hb0 := (RE2.typed hb).1
  have hb0' := (RE2.typed hb).2.1.tyConv (tyB hT0)
  have hty : HasTy S k .one [] (.transp ((c.up hW).L A) (φ.subst c.σ.τ) b) (((c.up hW).L A).dinst .one) :=
    HasTy.transp hLt hφL hcL hb0
  have hty' : HasTy S k .one [] (.transp ((c.up hW).R A) (φ.subst c.σ'.τ) b') (((c.up hW).L A).dinst .one) :=
    (HasTy.transp hLt' hφR hcR hb0').tyConv (TyEq.symm (tyB hT1))
  have heq := EqTm.transp hty hty' eLR (c.ent_LR (ent_refl φ)) (c.ent_RL (ent_refl φ)) (RE2.typed hb).2.2
  exact hLV.kanT hW c (lineRob_of_valid hW hLV c) _ _ b b' (lineConst_of_valid hW hφ hCV c)
    hty hty' heq (c.ent_LR (ent_refl φ)) (c.ent_RL (ent_refl φ)) hb

/-- The tube of the `transpHcomp` contractum at a related substitution, related at each point where its
face holds. -/
theorem tube_rel {A u : Tm}
    {φ ψ : I} {l : ℕ} (hφ : φ.Scoped Ψ) (hψs : ψ.Scoped Ψ)
    (hLV : Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A (.univ l))
    (hCV : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (.univ l))
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (.univ l))
    (huV : Valid2 S (Ψ + 1) (cof Φ ψ).shift Γ.dshift u u (A.dinst .zero).dshift)
    (c : CSub2 S Ψ Φ Γ k) :
    TubeD S k (c.L (A.dinst .one)) (ψ.subst c.σ.τ) ((c.up hW).L (.transp (A.dsubst skip1I) φ.shift u))
      ((c.up hW).R (.transp (A.dsubst skip1I) φ.shift u)) := by
  intro k' σ r hr hh
  have eL : (c.up hW).L (.transp (A.dsubst skip1I) φ.shift u) =
      .transp (((c.up hW).L A).dsubst skip1I) (φ.subst c.σ.τ).shift ((c.up hW).L u) :=
    transp_skip_subst A φ u c.γ c.σ.τ
  have eR : (c.up hW).R (.transp (A.dsubst skip1I) φ.shift u) =
      .transp (((c.up hW).R A).dsubst skip1I) (φ.subst c.σ'.τ).shift ((c.up hW).R u) :=
    transp_skip_subst A φ u c.γ' c.σ'.τ
  rw [eL, eR, show skip1I = skipI from rfl, tHc_tube_pt _ _ _ σ r hr, tHc_tube_pt _ _ _ σ r hr,
    ← CSub2.up_restr_L, ← CSub2.up_restr_L, ← CSub2.up_restr_R, ← CSub2.up_restr_R, ← CSub2.restr_L hW c σ,
    ← I_subst_comp, ← I_subst_comp]
  have hψ' : I.Entails .one (ψ.subst (c.restr hW σ).σ.τ) := by
    change I.Entails .one (ψ.subst (c.σ.comp σ).τ)
    rw [I_subst_comp]
    exact (holds_iff_entails (I.scoped_subst (I.scoped_subst hψs c.σ.sc) σ.sc)).1 hh
  have b := (huV k' (((c.restr hW σ).cof hψ').cons r r hr hr (I_eq_refl _))).2
  rw [CSub2.L_cons hW, CSub2.L_cons hW, CSub2.R_cons hW] at b
  change RE2 S k' ((((c.restr hW σ).up hW).L (A.dinst .zero).dshift).dinst r) ((((c.restr hW σ).up hW).L u).dinst r)
    ((((c.restr hW σ).up hW).R u).dinst r) at b
  rw [show (((c.restr hW σ).up hW).L (A.dinst .zero).dshift).dinst r = (c.restr hW σ).L (A.dinst .zero) by
    show ((A.dinst .zero).dshift.subst (dupS (c.restr hW σ).γ) (I.up (c.restr hW σ).σ.τ)).dinst r = _
    rw [dshift_dup_subst, dshift_dinst]] at b
  exact transp_rel_at hW hφ hLV hCV hL hc (c.restr hW σ) b

variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ []) (hH : D.isHIT = true)
include hD hp hH

/-- **Transport of a formal composition** in a higher inductive type with parameters. -/
theorem valid_transpHcomp {ps qs u a T : Tm} {φ ψ : I}
    (h3 : HasTy0 S Ψ Φ Γ (.hcomp (.data d (ps.dinst .zero)) ψ u a) (.data d (ps.dinst .zero)))
    (h4 : HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) T)
    (hyT : HasTy0 S Ψ Φ Γ (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
      (.transp (.data d ps) φ a)) T)
    (hv : Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a))
      (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) T)
    (hti : TranspInv S Ψ Φ Γ (.data d ps) φ (.hcomp (.data d qs) ψ u a) T)
    (hhi : HcompInv S Ψ Φ Γ (.data d (ps.dinst .zero)) ψ u a (.data d (ps.dinst .zero))) :
    Valid2 S Ψ Φ Γ (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a))
      (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
        (.transp (.data d ps) φ a)) T := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hφ, hLV, hCV, hbV, htr, hL, hc, hb⟩ := hti
  obtain ⟨l', hψ, -, huV, haV, hsV, -, hA0, hu, ha, hside⟩ := hhi
  -- the contractum, typed at the end of the line
  have hy1 : HasTy0 S Ψ Φ Γ (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
      (.transp (.data d ps) φ a)) ((Tm.data d ps).dinst .one) := by
    have hs := scoped_of_wf (wf_of_ty ha)
    have hXs : (cof Φ ψ).Scoped Ψ := ⟨hs, hψ⟩
    have hent : I.Entails (cof Φ ψ) Φ := ent_and_left Φ ψ
    have htu := transp_skip hS hL hφ hc hu
    have hA1 := HasTy0.dsubst hS hL (r := .one) trivial
    have hta := HasTy0.transp hL hφ hc ha
    have hu0 : HasTy0 S Ψ (cof Φ ψ) Γ (u.dinst .zero) ((Tm.data d ps).dinst .zero) := by
      have := HasTy0.dsubst hS hu (r := .zero) trivial
      rwa [dshift_dinst] at this
    have hLc := HasTy0.restrict (KubusCore.I.scoped_shift hXs) (ent_shift hent) hL
    have hcc := EqTm0.restrict (KubusCore.I.scoped_shift (show (cof (cof Φ ψ) φ).Scoped Ψ from ⟨hXs, hφ⟩))
      (ent_shift (ent_and_mono hent (ent_refl _))) hc
    have h1 := HasTy0.transp hLc hφ hcc hu0
    have h2 := HasTy0.restrict hXs hent hta
    have side := EqTm0.transp h1 h2 (EqTm0.refl hLc) (ent_refl _) (ent_refl _) hside
    rw [← transp_skip_dinst0] at side
    exact HasTy0.hcomp hA1 hψ htu hta side
  -- the inductive type at the end of the line, at its level
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele hL rfl
  rw [hD] at hD2; cases hD2
  have hLD : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (.data d ps) (.univ D.level) := HasTy0.data hD (hW.2 d D hD).1 hpt
  have hD1 : HasTy0 S Ψ Φ Γ ((Tm.data d ps).dinst .one) (.univ D.level) := HasTy0.dsubst hS hLD (r := .one) trivial
  -- the contracta at a related substitution
  have hyRel : ∀ k (c : CSub2 S Ψ Φ Γ k), RE2 S k (c.L ((Tm.data d ps).dinst .one))
      (c.L (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
        (.transp (.data d ps) φ a)))
      (c.R (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
        (.transp (.data d ps) φ a))) := by
    intro k c
    have hPk : HasTy S k .one [] (.data d (c.L (ps.dinst .one))) (.univ D.level) := c.ty hW hD1
    have hPPk : RT2 S k (.data d (c.L (ps.dinst .one))) (.data d (c.L (ps.dinst .one))) := by
      have h := hLV.tySelf hW ((c.diagL hW).cons .one .one trivial trivial (I_eq_refl _))
      rw [CSub2.L_cons hW, CSub2.R_cons hW] at h
      have e : c.L ((Tm.data d ps).dinst .one) = ((c.up hW).L (Tm.data d ps)).dinst .one := CSub2.L_dinst hW c _ .one
      change RT2 S k (((c.up hW).L (Tm.data d ps)).dinst .one) (((c.up hW).L (Tm.data d ps)).dinst .one) at h
      rw [← e] at h; exact h
    have hPc : (c.L (ps.dinst .one)).closedB 0 k = true := data_closed hW hD hPk
    have e0 : (c.L (ps.dinst .one)).isub (ISub.id k) = c.L (ps.dinst .one) := isub_id_of_closed hPc
    have htube := tube_rel hW hφ hψ hLV hCV hL hc huV c
    have hpre : ∀ {k' : ℕ} (σ : ISub k' k), RT2 S k' ((c.L ((Tm.data d ps).dinst .one)).isub σ)
        ((c.L ((Tm.data d ps).dinst .one)).isub σ) := fun σ => RT2.isub hW (tyCode_of_univ hW hPk) hPPk σ
    have tS := tube_rel hW hφ hψ hLV hCV hL hc huV (c.diagL hW)
    have hψL := I.scoped_subst hψ c.σ.sc
    have hψR := I.scoped_subst hψ c.σ'.sc
    have tS' : TubeD S k (c.L ((Tm.data d ps).dinst .one)) (ψ.subst c.σ'.τ)
        ((c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u))
        ((c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)) := fun k' σ r hr hh => by
      have hh' : (ival (idEnv k') ((ψ.subst c.σ.τ).subst σ.τ)).holds := by
        rw [holds_iff_entails (I.scoped_subst hψL σ.sc)]
        exact ent_trans ((holds_iff_entails (I.scoped_subst hψR σ.sc)).1 hh) (ent_subst (c.ent_RL (ent_refl ψ)) σ.τ)
      exact RE2.trans hW (hpre σ) (RE2.symm hW (hpre σ) (htube k' σ r hr hh')) (htube k' σ r hr hh')
    have haa := transp_rel_at hW hφ hLV hCV hL hc c (haV k c).2
    have R := hcomp_relD hW hD hH hPk hPPk (ISub.id k) (Q1 := c.L (ps.dinst .one)) (Q2 := c.R (ps.dinst .one))
      (φ := ψ.subst c.σ.τ) (φ' := ψ.subst c.σ'.τ)
      (u := (c.up hW).L (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u))
      (u' := (c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u))
      (a := .transp ((c.up hW).L (.data d ps)) (φ.subst c.σ.τ) (c.L a))
      (a' := .transp ((c.up hW).R (.data d ps)) (φ.subst c.σ'.τ) (c.R a))
      (by rw [e0]; exact c.ty hW hy1) (by rw [e0]; exact c.tyR' hW hy1) (by rw [e0]; exact c.eqLR hW hy1)
      (c.ent_LR (ent_refl ψ)) (c.ent_RL (ent_refl ψ)) (by rw [e0]; exact htube) (by rw [e0]; exact tS)
      (by rw [e0]; exact tS') (by rw [e0]; exact haa)
    rw [e0] at R
    exact R
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyA : Valid2 S Ψ Φ Γ (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
      (.transp (.data d ps) φ a)) (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
      (.transp (.data d ps) φ a)) ((Tm.data d ps).dinst .one) := fun k c => by
    have hT1 := hLV.tySelf hW (c.cons .one .one trivial trivial (I_eq_refl _))
    rw [CSub2.L_cons hW, CSub2.R_cons hW] at hT1
    exact ⟨by rw [CSub2.L_dinst hW, CSub2.R_dinst hW]; exact hT1, hyRel k c⟩
  have hy := valid_conv_tr hyA htr hT
  have heqT := EqTm0.transpHcomp hD hp hH h3 h4
  have ht1 : HasTy0 S Ψ Φ Γ (.transp (.data d ps) φ (.hcomp (.data d qs) ψ u a)) ((Tm.data d ps).dinst .one) :=
    HasTy0.transp hL hφ hc hb
  have heq1 := EqTm0.transpHcomp hD hp hH h3 ht1
  refine valid_red_rule hW hv hy fun k c => ?_
  have eTube : ∀ (γ : ℕ → Tm) (τ : ℕ → I),
      (Tm.transp ((Tm.data d ps).dsubst skip1I) φ.shift u).subst (dupS γ) (I.up τ) =
        .transp (((Tm.data d ps).subst (dupS γ) (I.up τ)).dsubst skip1I) (φ.subst τ).shift (u.subst (dupS γ) (I.up τ)) :=
    fun γ τ => transp_skip_subst _ φ u γ τ
  by_cases hf : I.Entails .one (φ.subst c.σ.τ)
  · -- the face of the transport holds: the base, against the right contractum
    refine ⟨c.L (.hcomp (.data d qs) ψ u a), .step (step_transp_face hf) (.refl _), EqTm.transpFace hf (c.ty hW h4), ?_⟩
    have hφL := I.scoped_subst hφ c.σ.sc
    have hψL := I.scoped_subst hψ c.σ.sc
    have hψR := I.scoped_subst hψ c.σ'.sc
    have hPk : HasTy S k .one [] (.data d (c.L (ps.dinst .one))) (.univ D.level) := c.ty hW hD1
    have hPPk : RT2 S k (.data d (c.L (ps.dinst .one))) (.data d (c.L (ps.dinst .one))) := by
      have h := hLV.tySelf hW ((c.diagL hW).cons .one .one trivial trivial (I_eq_refl _))
      rw [CSub2.L_cons hW, CSub2.R_cons hW] at h
      have e : c.L ((Tm.data d ps).dinst .one) = ((c.up hW).L (Tm.data d ps)).dinst .one := CSub2.L_dinst hW c _ .one
      change RT2 S k (((c.up hW).L (Tm.data d ps)).dinst .one) (((c.up hW).L (Tm.data d ps)).dinst .one) at h
      rw [← e] at h; exact h
    have hPc : (c.L (ps.dinst .one)).closedB 0 k = true := data_closed hW hD hPk
    have e0 : (c.L (ps.dinst .one)).isub (ISub.id k) = c.L (ps.dinst .one) := isub_id_of_closed hPc
    have hpre : ∀ {k' : ℕ} (σ : ISub k' k), RT2 S k' ((c.L ((Tm.data d ps).dinst .one)).isub σ)
        ((c.L ((Tm.data d ps).dinst .one)).isub σ) := fun σ => RT2.isub hW (tyCode_of_univ hW hPk) hPPk σ
    -- the start and the end of the line agree where the face holds
    have eA1 : ∀ {k' : ℕ} (σ : ISub k' k),
        ((c.up hW).L (.data d ps)).isub (ISub.cons .one trivial σ) = (c.L ((Tm.data d ps).dinst .one)).isub σ := by
      intro k' σ
      rw [← isub_up_dinst _ σ .one trivial, CSub2.L_dinst hW, isub_dinst]; rfl
    have eA0 : ∀ {k' : ℕ} (σ : ISub k' k),
        ((c.up hW).L (.data d ps)).isub (ISub.cons .zero trivial σ) = (c.L ((Tm.data d ps).dinst .zero)).isub σ := by
      intro k' σ
      rw [← isub_up_dinst _ σ .zero trivial, CSub2.L_dinst hW, isub_dinst]; rfl
    have hfσ : ∀ {k' : ℕ} (σ : ISub k' k), (ival (idEnv k') ((φ.subst c.σ.τ).subst σ.τ)).holds := fun σ => by
      rw [holds_iff_entails (I.scoped_subst hφL σ.sc)]
      have := ent_subst hf σ.τ; simpa [I.subst] using this
    have r10 : ∀ {k' : ℕ} (σ : ISub k' k), RT2 S k' ((c.L ((Tm.data d ps).dinst .one)).isub σ)
        ((c.L ((Tm.data d ps).dinst .zero)).isub σ) := fun σ => by
      have h := lineConst_of_valid hW hφ hCV c _ σ .one trivial (hfσ σ)
      rw [eA1 σ, eA0 σ] at h
      exact h
    have hX1 : ∀ {k' : ℕ} (σ : ISub k' k), TyCode k' (semK S k' ((c.L ((Tm.data d ps).dinst .one)).isub σ)) :=
      fun σ => tyCode_of_univ hW (HasTy.isubS hW hPk σ)
    have to1 : ∀ {k' : ℕ} (σ : ISub k' k) {x y : Tm}, RE2 S k' ((c.L ((Tm.data d ps).dinst .zero)).isub σ) x y →
        RE2 S k' ((c.L ((Tm.data d ps).dinst .one)).isub σ) x y := by
      intro k' σ x y h
      exact RE2.conv hW (RT2.symm hW (hX1 σ) (r10 σ)) h
    have htubeY := tube_rel hW hφ hψ hLV hCV hL hc huV c
    -- the tubes
    have htube : TubeD S k (c.L ((Tm.data d ps).dinst .one)) (ψ.subst c.σ.τ) ((c.up hW).L u)
        ((c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)) := by
      intro k' σ r hr hh
      have hty' := (RE2.typed (htubeY k' σ r hr hh)).2.1
      rw [show (c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u) = _ from eTube c.γ' c.σ'.τ,
        show skip1I = skipI from rfl, tHc_tube_pt _ _ _ σ r hr] at hty' ⊢
      have hψ' : I.Entails .one (ψ.subst (c.restr hW σ).σ.τ) := by
        change I.Entails .one (ψ.subst (c.σ.comp σ).τ)
        rw [I_subst_comp]; exact (holds_iff_entails (I.scoped_subst hψL σ.sc)).1 hh
      have b := (huV k' (((c.restr hW σ).cof hψ').cons r r hr hr (I_eq_refl _))).2
      rw [CSub2.L_cons hW, CSub2.L_cons hW, CSub2.R_cons hW] at b
      change RE2 S k' ((((c.restr hW σ).up hW).L ((Tm.data d ps).dinst .zero).dshift).dinst r)
        ((((c.restr hW σ).up hW).L u).dinst r) ((((c.restr hW σ).up hW).R u).dinst r) at b
      rw [show ((((c.restr hW σ).up hW).L ((Tm.data d ps).dinst .zero).dshift).dinst r) =
          (c.restr hW σ).L ((Tm.data d ps).dinst .zero) by
        show (((Tm.data d ps).dinst .zero).dshift.subst (dupS (c.restr hW σ).γ) (I.up (c.restr hW σ).σ.τ)).dinst r = _
        rw [dshift_dup_subst, dshift_dinst], CSub2.restr_L, CSub2.up_restr_L, CSub2.up_restr_R] at b
      have b1 := to1 σ b
      have hfR : I.Entails .one ((φ.subst c.σ'.τ).subst σ.τ) :=
        ent_trans ((holds_iff_entails (I.scoped_subst hφL σ.sc)).1 (hfσ σ)) (ent_subst (c.ent_LR (ent_refl φ)) σ.τ)
      exact RE2.expandR hW (hpre σ) (RE2.typed b1).1 hty' (stable_transpFace hW hfR hty') b1
    have hψRL : ∀ {k' : ℕ} (σ : ISub k' k), (ival (idEnv k') ((ψ.subst c.σ'.τ).subst σ.τ)).holds →
        (ival (idEnv k') ((ψ.subst c.σ.τ).subst σ.τ)).holds := fun σ hh => by
      rw [holds_iff_entails (I.scoped_subst hψL σ.sc)]
      exact ent_trans ((holds_iff_entails (I.scoped_subst hψR σ.sc)).1 hh) (ent_subst (c.ent_RL (ent_refl ψ)) σ.τ)
    have tS : TubeD S k (c.L ((Tm.data d ps).dinst .one)) (ψ.subst c.σ.τ) ((c.up hW).L u) ((c.up hW).L u) :=
      fun k' σ r hr hh => RE2.trans hW (hpre σ) (htube k' σ r hr hh) (RE2.symm hW (hpre σ) (htube k' σ r hr hh))
    have tS' : TubeD S k (c.L ((Tm.data d ps).dinst .one)) (ψ.subst c.σ'.τ)
        ((c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u))
        ((c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)) := fun k' σ r hr hh =>
      RE2.trans hW (hpre σ) (RE2.symm hW (hpre σ) (htube k' σ r hr (hψRL σ hh))) (htube k' σ r hr (hψRL σ hh))
    -- the bases
    have haR := transp_rel_at hW hφ hLV hCV hL hc c (haV k c).2
    have hD0 : HasTy0 S Ψ Φ Γ ((Tm.data d ps).dinst .zero) (.univ D.level) := HasTy0.dsubst hS hLD (r := .zero) trivial
    have c1 : (c.L ((Tm.data d ps).dinst .one)).closedB 0 k = true := closed_of_ty hW (c.ty hW hD1)
    have c0 : (c.L ((Tm.data d ps).dinst .zero)).closedB 0 k = true := closed_of_ty hW (c.ty hW hD0)
    have r10k := r10 (ISub.id k)
    rw [isub_id_of_closed c1, isub_id_of_closed c0] at r10k
    have hfR : I.Entails .one (φ.subst c.σ'.τ) := ent_trans hf (c.ent_LR (ent_refl φ))
    have haa : RE2 S k (c.L ((Tm.data d ps).dinst .one)) (c.L a)
        (.transp ((c.up hW).R (.data d ps)) (φ.subst c.σ'.τ) (c.R a)) := by
      have h0 := RE2.conv hW (RT2.symm hW (tyCode_of_univ hW (c.ty hW hD1)) r10k) (haV k c).2
      have hty' := (RE2.typed haR).2.1
      exact RE2.expandR hW hPPk (RE2.typed h0).1 hty' (stable_transpFace hW hfR hty') h0
    -- the base and the contractum
    have hb1 : HasTy S k .one [] (c.L (.hcomp (.data d qs) ψ u a)) (c.L ((Tm.data d ps).dinst .one)) :=
      (c.ty hW hb).tyConv (Comp2_ty_base (RT2.symm hW (tyCode_of_univ hW (c.ty hW hD1)) r10k)).2.2.2.2.2
    have heqb : EqTm S k .one [] (c.L (.hcomp (.data d qs) ψ u a))
        (c.R (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
          (.transp (.data d ps) φ a))) (c.L ((Tm.data d ps).dinst .one)) :=
      (EqTm.transpFace hf (c.ty hW ht1)).symm.trans (c.eq hW heq1)
    have R := hcomp_relD hW hD hH hPk hPPk (ISub.id k) (Q1 := c.L qs) (Q2 := c.R (ps.dinst .one))
      (φ := ψ.subst c.σ.τ) (φ' := ψ.subst c.σ'.τ) (u := (c.up hW).L u)
      (u' := (c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)) (a := c.L a)
      (a' := .transp ((c.up hW).R (.data d ps)) (φ.subst c.σ'.τ) (c.R a))
      (by rw [e0]; exact hb1) (by rw [e0]; exact c.tyR' hW hy1) (by rw [e0]; exact heqb)
      (c.ent_LR (ent_refl ψ)) (c.ent_RL (ent_refl ψ)) (by rw [e0]; exact htube) (by rw [e0]; exact tS)
      (by rw [e0]; exact tS') (by rw [e0]; exact haa)
    rw [e0] at R
    exact htr k c _ _ R
  by_cases hg : I.Entails .one (ψ.subst c.σ.τ)
  · -- the face of the composition holds: the transport of the tube's end
    have hn' : I.entails .one (φ.subst c.σ.τ) = false := by simpa [I.Entails] using hf
    have hg' : I.entails .one (ψ.subst c.σ.τ) = true := hg
    have eyL : ((c.up hW).L (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)).dinst .one =
        .transp ((c.up hW).L (.data d ps)) (φ.subst c.σ.τ) (((c.up hW).L u).dinst .one) := by
      rw [show (c.up hW).L (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u) = _ from eTube c.γ c.σ.τ,
        transp_skip_dinst1]; rfl
    refine ⟨.transp ((c.up hW).L (.data d ps)) (φ.subst c.σ.τ) (((c.up hW).L u).dinst .one), .step ?_ (.refl _), ?_, ?_⟩
    · show step S (.transp (.data d ((c.up hW).L ps)) (φ.subst c.σ.τ)
        (.hcomp (.data d (c.L qs)) (ψ.subst c.σ.τ) ((c.up hW).L u) (c.L a))) = _
      simp [step, hn', hg', hD, hp]
      rfl
    · have e1 := (c.diagL hW).eq hW heqT
      have e2 : EqTm S k .one [] (c.L (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
          (.transp (.data d ps) φ a)))
          (((c.up hW).L (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)).dinst .one) (c.L T) :=
        EqTm.hcompFace hg (c.ty hW hyT)
      rw [eyL] at e2
      exact e1.trans e2
    · -- the right contractum computes to the transport of its tube's end
      have hgR : I.Entails .one (ψ.subst c.σ'.τ) := ent_trans hg (c.ent_LR (ent_refl ψ))
      have eyR : ((c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)).dinst .one =
          .transp ((c.up hW).R (.data d ps)) (φ.subst c.σ'.τ) (((c.up hW).R u).dinst .one) := by
        rw [show (c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u) = _ from eTube c.γ' c.σ'.τ,
          transp_skip_dinst1]; rfl
      have hyR := c.tyR' hW hyT
      have hs : StableE S k (c.L T) (c.R (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
          (.transp (.data d ps) φ a)))
          (((c.up hW).R (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)).dinst .one) :=
        stable_hcompFace hW hgR hyR
      rw [eyR] at hs
      -- the tube's ends are related
      have b := (huV k ((c.cof hg).cons .one .one trivial trivial (I_eq_refl _))).2
      rw [CSub2.L_cons hW, CSub2.L_cons hW, CSub2.R_cons hW] at b
      change RE2 S k (((c.up hW).L ((Tm.data d ps).dinst .zero).dshift).dinst .one) (((c.up hW).L u).dinst .one)
        (((c.up hW).R u).dinst .one) at b
      rw [show (((c.up hW).L ((Tm.data d ps).dinst .zero).dshift).dinst .one) = c.L ((Tm.data d ps).dinst .zero) by
        show (((Tm.data d ps).dinst .zero).dshift.subst (dupS c.γ) (I.up c.σ.τ)).dinst .one = _
        rw [dshift_dup_subst, dshift_dinst]] at b
      have r := htr k c _ _ (transp_rel_at hW hφ hLV hCV hL hc c b)
      have e1 := (c.diagL hW).eq hW heqT
      have e2 : EqTm S k .one [] (c.L (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
          (.transp (.data d ps) φ a)))
          (((c.up hW).L (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)).dinst .one) (c.L T) :=
        EqTm.hcompFace hg (c.ty hW hyT)
      rw [eyL] at e2
      exact RE2.expandR hW (hv.tyLL hW c) (HasTy.eqR (e1.trans e2)) hyR hs r
  · -- neither face holds: the step
    refine ⟨c.L (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
      (.transp (.data d ps) φ a)), .step ?_ (.refl _), (c.diagL hW).eq hW heqT, (hy k c).2⟩
    have eY : c.L (.hcomp (.data d (ps.dinst .one)) ψ (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)
        (.transp (.data d ps) φ a)) = tHc d ((c.up hW).L ps) (φ.subst c.σ.τ) (ψ.subst c.σ.τ) ((c.up hW).L u) (c.L a) := by
      show Tm.hcomp (.data d (c.L (ps.dinst .one))) (ψ.subst c.σ.τ)
        ((c.up hW).L (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u)) (c.L (.transp (.data d ps) φ a)) = _
      rw [show (c.up hW).L (.transp ((Tm.data d ps).dsubst skip1I) φ.shift u) = _ from eTube c.γ c.σ.τ,
        CSub2.L_dinst hW c ps .one]
      rfl
    rw [eY]
    exact step_transp_hcompH hD hp hH hf hg

end

end

end Model.Whnf
