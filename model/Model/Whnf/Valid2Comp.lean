import Model.Whnf.Valid2Sub

/-!
# Semantic validity of the computation rules of the Kan operations

A computation rule `redex ≡ contractum` is valid once the contractum is valid (as an open term, from
the validity of the redex's components) and, where the face holds, related to the face reduct: at each
restriction the redex reduces either to the contractum or, where the face holds, to the face reduct
(`valid_comp_rule`). The contracta are built from Kan operations at the components' types, so their
validity takes the Kan property of those (`KanOracle2.hcomp`, `KanOracle2.transp`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

variable (hW : WfSig S)
include hW

variable {Ψ : ℕ} {Φ : I} {Γ : Ctx}

/-- A computation rule with a face: the redex reduces to the contractum where the face does not hold,
and to `b` where it holds. -/
theorem valid_comp_rule {t y b T : Tm} {φ : I}
    (ht : Valid2 S Ψ Φ Γ t t T) (hy : Valid2 S Ψ Φ Γ y y T) (hb : Valid2 S Ψ (cof Φ φ) Γ b y T)
    (hred : ∀ k (c : CSub2 S Ψ Φ Γ k),
      (¬ I.Entails .one (φ.subst c.σ.τ) → Red S (c.L t) (c.L y) ∧ EqTm S k .one [] (c.L t) (c.L y) (c.L T)) ∧
      (I.Entails .one (φ.subst c.σ.τ) → Red S (c.L t) (c.L b) ∧ EqTm S k .one [] (c.L t) (c.L b) (c.L T))) :
    Valid2 S Ψ Φ Γ t y T := by
  intro k c
  refine ⟨(ht k c).1, RE2.expandH hW (ht.tyLL hW c) (RE2.typed (ht k c).2).1 (RE2.typed (hy k c).2).2.1
    fun k' σ => ?_⟩
  have hr := hred k' (c.restr hW σ)
  simp only [CSub2.restr_L] at hr
  by_cases hf : I.Entails .one (φ.subst (c.restr hW σ).σ.τ)
  · obtain ⟨r1, r2⟩ := hr.2 hf
    refine ⟨_, r1, r2, ?_⟩
    have := (hb k' ((c.restr hW σ).cof hf)).2
    change RE2 S k' ((c.restr hW σ).L T) ((c.restr hW σ).L b) ((c.restr hW σ).R y) at this
    rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at this
  · obtain ⟨r1, r2⟩ := hr.1 hf
    refine ⟨_, r1, r2, ?_⟩
    have := (hy k' (c.restr hW σ)).2
    rwa [CSub2.restr_L, CSub2.restr_L, CSub2.restr_R] at this

/-! ### Components of `Π` -/

omit hW in
theorem consT_succ_eq (γ : ℕ → Tm) : consT (γ 0) (fun x => γ (x + 1)) = γ := by
  funext x; cases x <;> rfl

omit hW in
theorem subst_up_inst_eq (B a : Tm) (γ : ℕ → Tm) (τ : ℕ → I) :
    (B.subst (Tm.up γ) τ).inst a = B.subst (consT a γ) τ := by
  simp only [Tm.inst, subst_subst]
  apply subst_congr
  · intro n; cases n with
    | zero => rfl
    | succ n => simp only [Tm.up, consT, shift_subst]; exact subst_var _
  · intro i; exact I_subst_var _

omit hW in
/-- A related substitution for `A :: Γ`, as one for `Γ` and the head. -/
theorem CSub2.head_rel {A : Tm} (c : CSub2 S Ψ Φ (A :: Γ) k) :
    RE2 S k ((c.ren (· + 1) lookup_shift_ren).L A) (c.γ 0) (c.γ' 0) := by
  have := c.look 0 A.shift rfl
  simp only [CSub2.L, CSub2.ren, shift_subst] at this ⊢
  exact this

theorem valid_piDom {A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.pi A B) (.pi A B) (.univ l))
    (hA : HasTy0 S Ψ Φ Γ A (.univ l)) : Valid2 S Ψ Φ Γ A A (.univ l) :=
  valid_univ_of hW hA hA (EqTm0.refl hA) fun k c => (RT2_pi_inv hW (h.ty hW c)).1

theorem valid_piCod {A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.pi A B) (.pi A B) (.univ l))
    (hB : HasTy0 S Ψ Φ (A :: Γ) B (.univ l)) : Valid2 S Ψ Φ (A :: Γ) B B (.univ l) := by
  refine valid_univ_of hW hB hB (EqTm0.refl hB) fun k c => ?_
  have hh := (RT2_pi_inv hW (h.ty hW (c.ren (· + 1) lookup_shift_ren))).2 _ _ c.head_rel
  simp only [CSub2.ren, subst_up_inst_eq, consT_succ_eq] at hh
  exact hh

theorem valid_sigmaDom {A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.sigma A B) (.sigma A B) (.univ l))
    (hA : HasTy0 S Ψ Φ Γ A (.univ l)) : Valid2 S Ψ Φ Γ A A (.univ l) :=
  valid_univ_of hW hA hA (EqTm0.refl hA) fun k c => (RT2_sigma_inv hW (h.ty hW c)).1

theorem valid_sigmaCod {A B : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.sigma A B) (.sigma A B) (.univ l))
    (hB : HasTy0 S Ψ Φ (A :: Γ) B (.univ l)) : Valid2 S Ψ Φ (A :: Γ) B B (.univ l) := by
  refine valid_univ_of hW hB hB (EqTm0.refl hB) fun k c => ?_
  have hh := (RT2_sigma_inv hW (h.ty hW (c.ren (· + 1) lookup_shift_ren))).2 _ _ c.head_rel
  simp only [CSub2.ren, subst_up_inst_eq, consT_succ_eq] at hh
  exact hh

/-! ### The endpoint of a tube -/

/-- The end of a valid tube. -/
theorem valid_tube_end {u A : Tm} {φ : I} {l : ℕ} (hφ : φ.Scoped Ψ) (r : I) (hr : r.Scoped Ψ)
    (hu : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u u A.dshift)
    (hut : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift) (hA : HasTy0 S Ψ Φ Γ A (.univ l)) :
    Valid2 S Ψ (cof Φ φ) Γ (u.dinst r) (u.dinst r) A := by
  have hS := sigClosed_of_wfSig hW
  have hs : (cof Φ φ).Scoped Ψ := ⟨scoped_of_ty hA, hφ⟩
  have hc := closed_ty hut
  have hcA := closed_ty (HasTy0.dwk hS hA)
  simp only [Ctx.dshift, List.length_map] at hc hcA
  have := valid_dinst' (Φ := cof Φ φ) r hr hc hc hcA hs hu
  rwa [show A.dshift.dinst r = A from dshift_dinst A r] at this

/-! ### `hcomp` in `Π` -/

theorem valid_hcompPi_rule {A B u u0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.hcomp (.pi A B) φ u u0) T)
    (hv : Valid2 S Ψ Φ Γ (.hcomp (.pi A B) φ u u0) (.hcomp (.pi A B) φ u u0) T)
    (hinv : HcompInv S Ψ Φ Γ (.pi A B) φ u u0 T) :
    Valid2 S Ψ Φ Γ (.hcomp (.pi A B) φ u u0) (Tm.hcompPi A B φ u u0) T := by
  obtain ⟨l, hφ, hPiV, huV, hu0V, hsV, htr, hPi, hu, hu0, hside⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hPi
  have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hA := HasTy0.piDom hS hPi
  have hB := HasTy0.piCod hS hPi
  have hBV := valid_piCod hW hPiV hB
  -- the tube, applied to the bound variable
  have hAd : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift A.dshift (.univ l) :=
    HasTy0.dwk hS (HasTy0.restrict hs' (ent_and_left _ _) hA)
  have huw := HasTy0.wk hS hAd hu
  have huwV := valid_wk A.dshift huV
  rw [pi_dshift] at huw huwV
  simp only [Tm.shift, Tm.ren] at huw huwV
  have hvar : HasTy0 S (Ψ + 1) (cof Φ φ).shift (A.dshift :: Γ.dshift) (.var 0) A.dshift.shift :=
    HasTy0.var (Wf0.cons hAd) rfl
  have hU := HasTy0.app huw hvar
  have hUV := valid_app hW huwV (valid_var hW (Γ := A.dshift :: Γ.dshift) (x := 0) rfl)
  rw [upShift_dshift_inst0] at hU hUV
  -- the base, applied to the bound variable
  have hu0w := HasTy0.wk hS hA hu0
  have hu0wV := valid_wk A hu0V
  simp only [Tm.shift, Tm.ren] at hu0w hu0wV
  have hv0 : HasTy0 S Ψ Φ (A :: Γ) (.var 0) A.shift := HasTy0.var (Wf0.cons hA) rfl
  have hU0 := HasTy0.app hu0w hv0
  have hU0V := valid_app hW hu0wV (valid_var hW (Γ := A :: Γ) (x := 0) rfl)
  rw [upShift_inst0] at hU0 hU0V
  -- the side condition
  have hAc := HasTy0.restrict hs' (ent_and_left _ _) hA
  have hsw := EqTm0.wk hS hAc hside
  have hswV := valid_wk A hsV
  simp only [Tm.shift, Tm.ren] at hsw hswV
  have hv0c : HasTy0 S Ψ (cof Φ φ) (A :: Γ) (.var 0) A.shift := HasTy0.var (Wf0.cons hAc) rfl
  have hsd := EqTm0.app hsw (EqTm0.refl hv0c)
  have hsdV := valid_app hW hswV (valid_var hW (Γ := A :: Γ) (Φ := cof Φ φ) (x := 0) rfl)
  rw [upShift_inst0] at hsd hsdV
  have e : (Tm.app u.shift (.var 0)).dinst .zero = .app (u.dinst .zero).shift (.var 0) := by
    show Tm.app (u.shift.dinst .zero) ((Tm.var 0).dinst .zero) = _
    rw [shift_dinst_comm]; rfl
  have hsd' : EqTm0 S Ψ (cof Φ φ) (A :: Γ) ((Tm.app u.shift (.var 0)).dinst .zero) (.app u0.shift (.var 0)) B := by
    rw [e]; exact hsd
  have hsdV' : Valid2 S Ψ (cof Φ φ) (A :: Γ) ((Tm.app u.shift (.var 0)).dinst .zero) (.app u0.shift (.var 0)) B := by
    rw [e]; exact hsdV
  -- the body and the contractum
  have hbody : HasTy0 S Ψ Φ (A :: Γ) (.hcomp B φ (.app u.shift (.var 0)) (.app u0.shift (.var 0))) B :=
    HasTy0.hcomp hB hφ hU hU0 hsd'
  have hbodyV := valid_hcomp hW hφ (ent_refl _) (ent_refl _) hBV hUV hU0V hsdV' hsdV' hbody hbody (.refl hbody)
    (.refl hU)
  have hlam : HasTy0 S Ψ Φ Γ (Tm.hcompPi A B φ u u0) (.pi A B) := HasTy0.lam hPi hbody
  have hyV : Valid2 S Ψ Φ Γ (Tm.hcompPi A B φ u u0) (Tm.hcompPi A B φ u u0) (.pi A B) :=
    valid_lam hW hPiV hbodyV hlam hlam (.refl hlam)
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hyV htr hT
  -- where the face holds: the tube's end, by η and the face of the body
  have hu1V := valid_tube_end hW hφ .one trivial huV hu hPi
  have hu1 : HasTy0 S Ψ (cof Φ φ) Γ (u.dinst .one) (.pi A B) := by
    have := HasTy0.dsubst hS (Φ := cof Φ φ) hu (r := .one) trivial
    rwa [dshift_dinst] at this
  have hηe := EqTm0.piEta hu1
  have hη := valid_piEta hW hu1V hu1 (presup hW hηe).2 hηe
  have hPiC := HasTy0.restrict hs' (ent_and_left _ _) hPi
  have hbodyC := HasTy0.restrict hs' (ent_and_left _ _) hbody
  have hU1 : HasTy0 S Ψ (cof Φ φ) (A :: Γ) ((Tm.app u.shift (.var 0)).dinst .one) B := by
    have := HasTy0.dsubst hS (Φ := cof Φ φ) (Γ := A :: Γ) hU (r := .one) trivial
    rwa [dshift_dinst] at this
  have hfe := EqTm0.hcompFace (ent_and_right _ _) hbodyC
  have hfV := valid_hcompFace hW (ent_and_right _ _) (valid_restrict hW (ent_and_left _ _) hbodyV) hbodyC hU1
  have e1 : (Tm.app (Tm.ren Nat.succ id u) (.var 0)).dinst .one = .app (u.dinst .one).shift (.var 0) := by
    show Tm.app (u.shift.dinst .one) ((Tm.var 0).dinst .one) = _
    rw [shift_dinst_comm]; rfl
  simp only [Tm.shift] at hfe hfV
  rw [e1] at hfe hfV
  have hlamE := EqTm0.lam hPiC (EqTm0.symm hfe)
  have hlamV := valid_lam hW (valid_restrict hW (ent_and_left _ _) hPiV) (valid_symm hW hfV) (presup hW hlamE).1
    (presup hW hlamE).2 hlamE
  have hb := valid_conv_tr (valid_trans hW hη hlamV) (htr.restrict (ent_and_left _ _))
    fun k c => hT k (c.restrictTo (ent_and_left _ _))
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e2 : c.L (Tm.hcompPi A B φ u u0) = Tm.hcompPi (c.L A) (B.subst (Tm.up c.γ) c.σ.τ) (φ.subst c.σ.τ)
        (u.subst (dupS c.γ) (I.up c.σ.τ)) (c.L u0) := hcompPi_subst _ _ A B φ u u0
    rw [e2]
    exact ⟨.step (step_hcomp_pi hn) (.refl _), EqTm.hcompPi (c.ty hW h)⟩
  · rw [CSub2.L_dinst hW]
    exact ⟨.step (step_hcomp_face hf) (.refl _), EqTm.hcompFace hf (c.ty hW h)⟩

/-! ### Dropping the innermost interval variable of a related substitution -/

omit hW in
/-- A related substitution for an interval-extended context, restricted to the context. -/
def CSub2.dtail (c : CSub2 S (Ψ + 1) Φ.shift Γ.dshift k) : CSub2 S Ψ Φ Γ k where
  σ := c.σ.tail
  σ' := c.σ'.tail
  hσ := INear.tail c.hσ
  γ := c.γ
  γ' := c.γ'
  hγ := c.hγ
  hγ' := c.hγ'
  face := by have := c.face; rwa [I_shift_subst] at this
  look x A h := by
    have := c.look x A.dshift (by rw [lookup_dshift, h]; rfl)
    rwa [dshift_subst] at this
  lookT x A h k' ρ τ1 τ2 h1 h2 b1 b2 := by
    have hsc : ((c.σ.τ 0).subst ρ.τ).Scoped k' := I.scoped_subst (c.σ.sc 0 (by omega)) ρ.sc
    have hn : ∀ τ1 : ISub k' Ψ, INear (c.σ.tail.comp ρ) τ1 → INear (c.σ.comp ρ) (ISub.cons _ hsc τ1) := by
      intro τ1 hτ i; cases i with
      | zero => exact I_eq_refl _
      | succ i => exact hτ i
    have := c.lookT x A.dshift (by rw [lookup_dshift, h]; rfl) k' ρ _ _ (hn τ1 h1) (hn τ2 h2) b1 b2
    rwa [dshift_subst, dshift_subst] at this

omit hW in
theorem consI_tail (σ : ISub k (Ψ + 1)) : consI (σ.τ 0) σ.tail.τ = σ.τ := by
  funext i; cases i <;> rfl

theorem valid_ipiLine {A : Tm} {l : ℕ} (h : Valid2 S Ψ Φ Γ (.ipi A) (.ipi A) (.univ l))
    (hA : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift A (.univ l)) : Valid2 S (Ψ + 1) Φ.shift Γ.dshift A A (.univ l) := by
  refine valid_univ_of hW hA hA (EqTm0.refl hA) fun k c => ?_
  have hh := (RT2_ipi_inv hW (h.ty hW c.dtail)).2 _ _ (c.σ.sc 0 (by omega)) (c.σ'.sc 0 (by omega)) (c.hσ 0)
  simp only [CSub2.L, CSub2.R, CSub2.dtail] at hh ⊢
  rw [dup_dinst, dup_dinst] at hh
  have e1 : consI (c.σ.τ 0) c.σ.tail.τ = c.σ.τ := consI_tail c.σ
  have e2 : consI (c.σ'.τ 0) c.σ'.tail.τ = c.σ'.τ := consI_tail c.σ'
  rwa [e1, e2] at hh

/-! ### `hcomp` in `(i : I) → A` -/

omit hW in
theorem ipi_bind2_dinst1 (A : Tm) :
    ((A.ren id (Tm.upRen Nat.succ)).subst Tm.var (I.up (Tm.bind2 (.var 0)))).dinst (.var 1) = A.dshift := by
  simp only [Tm.dinst, Tm.dsubst, ren_eq_subst, dshift_eq, subst_subst]
  refine subst_congr (fun n => rfl) (fun i => ?_) A
  rcases i with _ | _ | i <;> rfl

omit hW in
theorem bind2_dinst0 (u : Tm) : (u.dsubst (Tm.bind2 (.var 0))).dinst .zero = (u.dinst .zero).dshift := by
  simp only [Tm.dinst, Tm.dsubst, dshift_eq, subst_subst]
  apply subst_congr
  · intro n; rfl
  · intro i; rcases i with _ | i <;> rfl

omit hW in
theorem bind2_dinst1 (u : Tm) : (u.dsubst (Tm.bind2 (.var 0))).dinst .one = (u.dinst .one).dshift := by
  simp only [Tm.dinst, Tm.dsubst, dshift_eq, subst_subst]
  apply subst_congr
  · intro n; rfl
  · intro i; rcases i with _ | i <;> rfl

theorem valid_hcompIPi_rule {A u u0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.hcomp (.ipi A) φ u u0) T)
    (hv : Valid2 S Ψ Φ Γ (.hcomp (.ipi A) φ u u0) (.hcomp (.ipi A) φ u u0) T)
    (hinv : HcompInv S Ψ Φ Γ (.ipi A) φ u u0 T) :
    Valid2 S Ψ Φ Γ (.hcomp (.ipi A) φ u u0) (Tm.hcompIPi A φ u u0) T := by
  obtain ⟨l, hφ, hIV, huV, hu0V, hsV, htr, hI, hu, hu0, hside⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hI
  have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hA := HasTy0.ipiLine hS hI
  have hAV := valid_ipiLine hW hIV hA
  have hφ1 : φ.shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hφ
  -- closedness
  have hcu := closed_ty hu
  have hcu0 := closed_ty hu0
  have hcI := closed_ty hI
  have hcId := closed_ty (HasTy0.dwk hS hI)
  have hcIdc := closed_ty (HasTy0.dwk hS (HasTy0.restrict hs' (ent_and_left _ _) hI))
  simp only [Ctx.dshift, List.length_map] at hcu hcId hcIdc
  -- the tube, past the new interval variable
  have hw2 : Wf0 S (Ψ + 1 + 1) (cof Φ φ).shift.shift Γ.dshift.dshift := Wf0.dwk2 hS (wf_of_eq hside)
  have hb2 : ∀ i < Ψ + 1, (Tm.bind2 (.var 0) i).Scoped (Ψ + 1 + 1) := fun i hi => by
    rcases i with _ | i
    · show 0 < Ψ + 1 + 1; omega
    · show i + 2 < Ψ + 1 + 1; omega
  have hu2 : HasTy0 S (Ψ + 1 + 1) (cof Φ φ).shift.shift Γ.dshift.dshift (u.dsubst (Tm.bind2 (.var 0)))
      ((Tm.ipi A).dshift.dsubst (Tm.bind2 (.var 0))) := by
    have := HasTy0.isub hS (τ := Tm.bind2 (.var 0)) hu hb2 (ent_bind2_shift _ (ent_refl _))
      (by rw [ctxI_bind2]; exact hw2)
    rwa [ctxI_bind2] at this
  have hu2V := valid_dsub12 (Γ := Γ) (Φs := (cof Φ φ).shift) (Φ' := (cof Φ φ).shift.shift) (Tm.bind2 (.var 0))
    (show 0 < Ψ + 2 by omega) (fun i => rfl) (KubusCore.I.scoped_shift hs') (ent_bind2_shift _ (ent_refl _))
    hcu hcu hcIdc huV
  have hv1 : (I.var 1).Scoped (Ψ + 1 + 1) := show 1 < Ψ + 1 + 1 by omega
  have hU := HasTy0.iapp (A := (A.ren id (Tm.upRen Nat.succ)).subst Tm.var (I.up (Tm.bind2 (.var 0)))) hu2 hv1
  have hUV := valid_iapp hW (L := (A.ren id (Tm.upRen Nat.succ)).subst Tm.var (I.up (Tm.bind2 (.var 0))))
    hu2V hv1 hv1 (I_eq_refl _)
  rw [ipi_bind2_dinst1] at hU hUV
  -- the base, at the new interval variable
  have hu0d := HasTy0.dwk hS hu0
  have hu0dV := valid_dwk' hcu0 hcu0 hcI hs hu0V
  have hv0 : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hU0 := HasTy0.iapp (A := A.ren id (Tm.upRen Nat.succ)) hu0d hv0
  have hU0V := valid_iapp hW (L := A.ren id (Tm.upRen Nat.succ)) hu0dV hv0 hv0 (I_eq_refl _)
  rw [upDShift_dinst0] at hU0 hU0V
  -- the side condition
  have hcs0 := closed_ty (presup hW hside).1
  have hsd := EqTm0.dwk hS hside
  have hsdV := valid_dwk' hcs0 hcu0 hcI hs' hsV
  have hsd' := EqTm0.iapp (A := A.ren id (Tm.upRen Nat.succ)) hsd hv0 hv0 (I_eq_refl _)
  have hsdV' := valid_iapp hW (L := A.ren id (Tm.upRen Nat.succ)) hsdV hv0 hv0 (I_eq_refl _)
  rw [upDShift_dinst0] at hsd' hsdV'
  have e0 : (Tm.papp (u.dsubst (Tm.bind2 (.var 0))) (.var 1)).dinst .zero = .papp (u.dinst .zero).dshift (.var 0) := by
    show Tm.papp ((u.dsubst (Tm.bind2 (.var 0))).dinst .zero) ((I.var 1).subst (I.inst0 .zero)) = _
    rw [bind2_dinst0]; rfl
  have hsd2 : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift
      ((Tm.papp (u.dsubst (Tm.bind2 (.var 0))) (.var 1)).dinst .zero) (.papp u0.dshift (.var 0)) A := by
    rw [e0]; exact hsd'
  have hsdV2 : Valid2 S (Ψ + 1) (cof Φ φ).shift Γ.dshift
      ((Tm.papp (u.dsubst (Tm.bind2 (.var 0))) (.var 1)).dinst .zero) (.papp u0.dshift (.var 0)) A := by
    rw [e0]; exact hsdV'
  -- the body and the contractum
  have hbody : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift
      (.hcomp A φ.shift (.papp (u.dsubst (Tm.bind2 (.var 0))) (.var 1)) (.papp u0.dshift (.var 0))) A :=
    HasTy0.hcomp hA hφ1 hU hU0 hsd2
  have hbodyV := valid_hcomp hW hφ1 (ent_refl _) (ent_refl _) hAV hUV hU0V hsdV2 hsdV2 hbody hbody (.refl hbody)
    (.refl hU)
  have hpl : HasTy0 S Ψ Φ Γ (Tm.hcompIPi A φ u u0) (.ipi A) := HasTy0.ilam hI hbody
  have hyV : Valid2 S Ψ Φ Γ (Tm.hcompIPi A φ u u0) (Tm.hcompIPi A φ u u0) (.ipi A) :=
    valid_ilam hW hIV hbodyV hpl hpl (.refl hpl)
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hyV htr hT
  -- where the face holds: the tube's end, by η and the face of the body
  have hu1V := valid_tube_end hW hφ .one trivial huV hu hI
  have hu1 : HasTy0 S Ψ (cof Φ φ) Γ (u.dinst .one) (.ipi A) := by
    have := HasTy0.dsubst hS (Φ := cof Φ φ) hu (r := .one) trivial
    rwa [dshift_dinst] at this
  have hηe := EqTm0.ipiEta hu1
  have hη := valid_ipiEta hW hu1V hu1 (presup hW hηe).2 hηe
  have hIC := HasTy0.restrict hs' (ent_and_left _ _) hI
  have hsc1 : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hs'
  have hbodyC := HasTy0.restrict hsc1 (ent_shift (ent_and_left _ _)) hbody
  have hU1 : HasTy0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift
      ((Tm.papp (u.dsubst (Tm.bind2 (.var 0))) (.var 1)).dinst .one) A := by
    have := HasTy0.dsubst hS (Φ := (cof Φ φ).shift) (Γ := Γ.dshift) hU (r := .one) trivial
    rwa [dshift_dinst] at this
  have hφC : I.Entails (cof Φ φ).shift φ.shift := ent_shift (ent_and_right _ _)
  have hfe := EqTm0.hcompFace hφC hbodyC
  have hfV := valid_hcompFace hW hφC (valid_restrict hW (ent_shift (ent_and_left _ _)) hbodyV) hbodyC hU1
  have e1 : (Tm.papp (u.dsubst (Tm.bind2 (.var 0))) (.var 1)).dinst .one = .papp (u.dinst .one).dshift (.var 0) := by
    show Tm.papp ((u.dsubst (Tm.bind2 (.var 0))).dinst .one) ((I.var 1).subst (I.inst0 .one)) = _
    rw [bind2_dinst1]; rfl
  rw [e1] at hfe hfV
  have hlamE := EqTm0.ilam hIC (EqTm0.symm hfe)
  have hlamV := valid_ilam hW (valid_restrict hW (ent_and_left _ _) hIV) (valid_symm hW hfV) (presup hW hlamE).1
    (presup hW hlamE).2 hlamE
  have hb := valid_conv_tr (valid_trans hW hη hlamV) (htr.restrict (ent_and_left _ _))
    fun k c => hT k (c.restrictTo (ent_and_left _ _))
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e2 : c.L (Tm.hcompIPi A φ u u0) = Tm.hcompIPi (A.subst (dupS c.γ) (I.up c.σ.τ)) (φ.subst c.σ.τ)
        (u.subst (dupS c.γ) (I.up c.σ.τ)) (c.L u0) := hcompIPi_subst _ _ A φ u u0
    rw [e2]
    exact ⟨.step (step_hcomp_ipi hn) (.refl _), EqTm.hcompIPi (c.ty hW h)⟩
  · rw [CSub2.L_dinst hW]
    exact ⟨.step (step_hcomp_face hf) (.refl _), EqTm.hcompFace hf (c.ty hW h)⟩

/-! ### `transp` in `(i : I) → A` -/

theorem valid_transpIPi_rule {A u0 T : Tm} {φ : I}
    (h : HasTy0 S Ψ Φ Γ (.transp (.ipi A) φ u0) T)
    (hv : Valid2 S Ψ Φ Γ (.transp (.ipi A) φ u0) (.transp (.ipi A) φ u0) T)
    (hinv : TranspInv S Ψ Φ Γ (.ipi A) φ u0 T) :
    Valid2 S Ψ Φ Γ (.transp (.ipi A) φ u0) (Tm.transpIPi A φ u0) T := by
  obtain ⟨l, hφ, hLV, hCV, hu0V, htr, hL, hc, hu0⟩ := hinv
  have hS := sigClosed_of_wfSig hW
  have hs := scoped_of_ty hu0
  have hs' : (cof Φ φ).Scoped Ψ := ⟨hs, hφ⟩
  have hφ1 : φ.shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hφ
  have hA := HasTy0.ipiLine hS hL
  have hAV := valid_ipiLine hW hLV hA
  -- the swapped line
  have hsw : ∀ i < 2, (swapI i).Scoped (Ψ + 2) := fun i hi => by
    rcases i with _ | _ | i
    · show 1 < Ψ + 2; omega
    · show 0 < Ψ + 2; omega
    · omega
  have hcA := closed_ty hA
  simp only [Ctx.dshift, List.length_map] at hcA
  have hA' := HasTy0.swap hS hA
  have hA'V := valid_dsub22 (Φs := Φ.shift.shift) swapI hsw (fun i => rfl)
    (KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hs)) (by rw [I_shift2_swap]; exact ent_refl _)
    hcA hcA rfl hAV
  rw [univ_dsubst] at hA'
  -- constancy of the swapped line
  have hcd := EqTm0.dwk hS hc
  have hcl := closed_ty (presup hW hc).1
  have hcr := closed_ty (presup hW hc).2
  simp only [Ctx.dshift, List.length_map] at hcl hcr
  have hcdV := valid_dwk' hcl hcr rfl (KubusCore.I.scoped_shift hs') hCV
  have hv0 : (I.var 0).Scoped (Ψ + 1 + 1) := show 0 < Ψ + 1 + 1 by omega
  have hci := EqTm0.ipiInj (A := A.ren id (Tm.upRen Nat.succ))
    (A' := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ)).ren id (Tm.upRen Nat.succ))
    (r := .var 0) hcd hv0
  have hciV := valid_ipiInj hW (L := A.ren id (Tm.upRen Nat.succ))
    (L' := ((A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ)).ren id (Tm.upRen Nat.succ))
    (r := .var 0) hcdV hv0 (presup hW hci).1 (presup hW hci).2 hci
  rw [ipi_c1, ipi_c2] at hci hciV
  have hcs := EqTm0.swap hS (Φ := cof Φ φ) hci
  have hcil := closed_ty (presup hW hci).1
  have hcir := closed_ty (presup hW hci).2
  simp only [Ctx.dshift, List.length_map] at hcil hcir
  have hcsV := valid_dsub22 (Φs := (cof Φ φ).shift.shift) swapI hsw (fun i => rfl)
    (KubusCore.I.scoped_shift (KubusCore.I.scoped_shift hs')) (by rw [I_shift2_swap]; exact ent_refl _)
    hcil hcir rfl hciV
  rw [ipi_c3, univ_dsubst] at hcs hcsV
  -- the base
  have hu0d := HasTy0.dwk hS hu0
  have hcu0 := closed_ty hu0
  have hcT0 := closed_ty (HasTy0.dsubst hS hL (r := .zero) trivial)
  have hu0dV := valid_dwk' hcu0 hcu0 hcT0 hs hu0V
  have hv0' : (I.var 0).Scoped (Ψ + 1) := show 0 < Ψ + 1 by omega
  have hb := HasTy0.iapp (A := (A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ)) (r := .var 0)
    hu0d hv0'
  have hbV := valid_iapp hW (L := (A.subst Tm.var (I.up (I.inst0 .zero))).ren id (Tm.upRen Nat.succ))
    hu0dV hv0' hv0' (I_eq_refl _)
  rw [ipi_c4] at hb hbV
  -- the transport and the contractum
  have ht := HasTy0.transp hA' hφ1 hcs hb
  have htV := valid_transp hW hφ1 (ent_refl _) (ent_refl _) hA'V hcsV hbV ht ht (.refl ht)
  rw [ipi_c5] at ht htV
  have hL1 := HasTy0.dsubst hS hL (r := .one) trivial
  have hL1V := valid_dinst' (r := .one) trivial (closed_ty hL) (closed_ty hL) rfl hs hLV
  have hpl : HasTy0 S Ψ Φ Γ (Tm.transpIPi A φ u0) ((Tm.ipi A).dinst .one) := HasTy0.ilam hL1 ht
  have hyV : Valid2 S Ψ Φ Γ (Tm.transpIPi A φ u0) (Tm.transpIPi A φ u0) ((Tm.ipi A).dinst .one) :=
    valid_ilam hW hL1V htV hpl hpl (.refl hpl)
  have hT : ∀ k (c : CSub2 S Ψ Φ Γ k), RT2 S k (c.L T) (c.R T) := fun k c => (hv k c).1
  have hyT := valid_conv_tr hyV htr hT
  -- where the face holds: the base, by η and the face of the transport
  have hu0C := HasTy0.restrict hs' (ent_and_left _ _) hu0
  have hu0CV := valid_restrict hW (Φ' := cof Φ φ) (ent_and_left _ _) hu0V
  have hηe := EqTm0.ipiEta (A := A.subst Tm.var (I.up (I.inst0 .zero))) hu0C
  have hη := valid_ipiEta hW (L := A.subst Tm.var (I.up (I.inst0 .zero))) hu0CV hu0C (presup hW hηe).2 hηe
  have hk1 := valid_dinst' (Φ := cof Φ φ) (r := .one) trivial (closed_ty (presup hW hc).1)
    (closed_ty (presup hW hc).2) rfl hs' hCV
  rw [dshift_dinst] at hk1
  have hη1 := valid_conv hW hη (valid_symm hW hk1)
  have hsc1 : (cof Φ φ).shift.Scoped (Ψ + 1) := KubusCore.I.scoped_shift hs'
  have hφC : I.Entails (cof Φ φ).shift φ.shift := ent_shift (ent_and_right _ _)
  have htC := HasTy0.restrict hsc1 (ent_shift (ent_and_left _ _)) ht
  have hfe := EqTm0.transpFace hφC htC
  have hfV := valid_transpFace hW hφC (valid_restrict hW (ent_shift (ent_and_left _ _)) htV) htC (presup hW hfe).2
  have hL1C := HasTy0.restrict hs' (ent_and_left _ _) hL1
  have hlamE := EqTm0.ilam hL1C (EqTm0.symm hfe)
  have hlamV := valid_ilam hW (valid_restrict hW (ent_and_left _ _) hL1V) (valid_symm hW hfV) (presup hW hlamE).1
    (presup hW hlamE).2 hlamE
  have hb := valid_conv_tr (valid_trans hW hη1 hlamV) (htr.restrict (ent_and_left _ _))
    fun k c => hT k (c.restrictTo (ent_and_left _ _))
  refine valid_comp_rule hW hv hyT hb fun k c => ⟨fun hn => ?_, fun hf => ?_⟩
  · have e2 : c.L (Tm.transpIPi A φ u0) = Tm.transpIPi (A.subst (dupS (dupS c.γ)) (I.up (I.up c.σ.τ)))
        (φ.subst c.σ.τ) (c.L u0) := transpIPi_subst _ _ A φ u0
    rw [e2]
    exact ⟨.step (step_transp_ipi hn) (.refl _), EqTm.transpIPi (c.ty hW h)⟩
  · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (c.ty hW h)⟩

end

end Model.Whnf
