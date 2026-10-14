import Model.Whnf.Kan2GlueT
import Model.Whnf.Kan2DataTFill

/-!
# Binary transport in Glue types: the pieces

The parts of `transpGlueWith` (`tgA0`, `tgTube`, `tgA1'`, `tgT1`, `tgOmega`, `tgC`, `tgExt`, `tgA1`) at a pair
of related Glue lines are related, as in the unary `KanGlueT`. Near points (from faces equivalent up to
entailment) are handled by near invariance (`RE2_near`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' : ℕ}

theorem I_subst_cons_id {φ : I} (hφ : φ.Scoped (k + 1)) (r : I) (hr : r.Scoped k) :
    φ.subst (ISub.cons r hr (ISub.id k)).τ = φ.subst (I.inst0 r) :=
  I_subst_congr_scoped (fun i hi => by
    rcases i with _ | i
    · rfl
    · show (ISub.id k).τ i = .var i; simp [ISub.id, show i < k by omega]) hφ

theorem I_end_isub (φ : I) {d : I} (hd : d = .zero ∨ d = .one) (σ : ISub k' k) :
    (φ.subst (I.inst0 d)).subst σ.τ = (φ.subst σ.up.τ).subst (I.inst0 d) := by
  rw [I_subst_subst, I_subst_subst]; congr 1; funext i; rcases i with _ | i
  · rcases hd with rfl | rfl <;> rfl
  · show σ.τ i = ((σ.τ i).shift).subst _; rw [I_shift_inst0]

theorem tgTube_cons (φ : I) (e u0 : Tm) (σ : ISub k' k) (r : I) (hr : r.Scoped k') :
    (tgTube φ e u0).isub (ISub.cons r hr σ) =
      .unglue (φ.subst (ISub.cons r hr σ).τ) (e.isub (ISub.cons r hr σ)) (u0.isub σ) := by
  show Tm.unglue _ _ (u0.dshift.isub _) = _; rw [dshift_isub_cons]; rfl

theorem tgTube_zero (φ : I) (e u0 : Tm) (σ : ISub k' k) :
    ((tgTube φ e u0).isub σ.up).dinst .zero = (tgA0 φ e u0).isub σ := by
  show Tm.unglue (((φ.subst σ.up.τ)).subst (I.inst0 .zero)) ((e.isub σ.up).dinst .zero)
      ((u0.dshift.isub σ.up).dinst .zero) = Tm.unglue ((φ.subst (I.inst0 .zero)).subst σ.τ) ((e.dinst .zero).isub σ)
      (u0.isub σ)
  rw [I_end_isub φ (.inl rfl), dinst_isub_end _ (.inl rfl), dshift_isub_up_dinst]

theorem sk2_cons (X : Tm) {k4 : ℕ} (τ : ISub k4 (k + 1)) (z : I) (hz : z.Scoped k4) :
    (X.dsubst (sk (.var 0) 2)).isub (ISub.cons z hz τ) = X.isub (ISub.cons z hz τ.tail) := by
  conv_lhs => rw [← ISub.cons_tail τ]
  rw [sk2_isub]

theorem sk2_closed {X : Tm} (hX : X.closedB 0 (k + 1) = true) :
    X.dsubst (sk (.var 0) 2) = X.isub (ISub.cons (.var 0) (show 0 < k + 1 + 1 by omega) (ISub.wk (k + 1)).tail) := by
  simp only [Tm.dsubst, Tm.isub]
  refine closed_subst_eq X 0 (k + 1) _ _ _ _ hX (fun _ h => absurd h (Nat.not_lt_zero _)) fun i hi => ?_
  rcases i with _ | i
  · rfl
  · show I.var (i + 2) = (ISub.wk (k + 1)).τ (i + 1); simp [ISub.wk, show i < k by omega]

theorem dshift_isub_tail (t : Tm) {k4 : ℕ} (τ : ISub k4 (k + 1)) : t.dshift.isub τ = t.isub τ.tail := by
  conv_lhs => rw [← ISub.cons_tail τ]
  rw [dshift_isub_cons]

variable (hW : WfSig S)
include hW

/-- A term typed under a face in a line, at a point of a restriction where the face holds. -/
theorem ty_line_at {t X : Tm} {ψ : I} (hψ : ψ.Scoped k) (h : HasTy S (k + 1) (cof .one ψ).shift [] t X)
    (τ : ISub k' k) (r : I) (hr : r.Scoped k') (hh : (ival (idEnv k') (ψ.subst τ.τ)).holds) :
    HasTy S k' .one [] (t.isub (ISub.cons r hr τ)) (X.isub (ISub.cons r hr τ)) := by
  have h1 := HasTy.isubF hW (KubusCore.I.scoped_shift ⟨trivial, hψ⟩ : (cof .one ψ).shift.Scoped (k + 1)) h
    (ISub.cons r hr τ)
  rw [I_shift_cons] at h1
  exact HasTy.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds (I.scoped_subst hψ τ.sc) hh)) h1

/-- The systems of the bodies of `ω` are typed at their points where their face holds. -/
theorem tgSys_ty {A T e u0 : Tm} {φ ψ δ : I} {l : ℕ} (H : TG S k .one [] A φ T e ψ u0 δ l) (hδ : I.Entails .one δ)
    {k3 : ℕ} (σ0 : ISub k3 k) {y : I} (hy : y.Scoped k3) (hχ : I.Entails .one (I.or (ψ.subst σ0.τ) (.or (.neg y) y)))
    {x : I} (hx : x.Scoped k3) :
    HasTy S k3 .one [] ((tgSys A φ T e ψ u0).isub (ISub.cons x hx (ISub.cons y hy σ0))) (A.isub (ISub.cons x hx σ0)) := by
  have hRs : (cof (cof .one δ).shift (tgChi ψ)).shift.Scoped (k + 1 + 1) :=
    KubusCore.I.scoped_shift ⟨KubusCore.I.scoped_shift ⟨trivial, H.hδ⟩, KubusCore.I.scoped_shift H.hψ,
      show 0 < k + 1 by omega, show 0 < k + 1 by omega⟩
  have h1 := HasTy.isubF hW hRs (minimal_to_spec H.hsys) (ISub.cons x hx (ISub.cons y hy σ0))
  rw [sk2_isub] at h1
  refine HasTy.restrict (Φ' := .one) trivial ?_ h1
  rw [I_shift_cons]
  show I.Entails .one (I.and (((cof .one δ).shift).subst _) ((tgChi ψ).subst _))
  rw [I_shift_cons]
  exact ent_and_intro (ent_subst (show I.Entails .one (cof .one δ) from ent_cof_one hW hδ) σ0.τ)
    (by simpa only [tgChi, I.subst, I_shift_cons] using hχ)

section
variable {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
  (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ')
include D

theorem TGD2.closedL : A.closedB 0 (k + 1) = true ∧ T.closedB 0 (k + 1) = true ∧ e.closedB 0 (k + 1) = true ∧
    φ.Scoped (k + 1) := by
  obtain ⟨l, hG⟩ := D.hG
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1, hc.1.2, hc.2, (glue_data hW hG).1⟩

theorem TGD2.closedR : A'.closedB 0 (k + 1) = true ∧ T'.closedB 0 (k + 1) = true ∧ e'.closedB 0 (k + 1) = true ∧
    φ'.Scoped (k + 1) := by
  obtain ⟨l, hG⟩ := D.hG'
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1, hc.1.2, hc.2, (glue_data hW hG).1⟩

/-- The bases of the starts. -/
theorem TGD2.a0 : RE2 S k (A.dinst .zero) (tgA0 φ e u0) (tgA0 φ' e' u0') := by
  obtain ⟨hA, -, he, hφ⟩ := D.closedL hW
  obtain ⟨-, -, he', hφ'⟩ := D.closedR hW
  obtain ⟨l, hG⟩ := D.hG
  have hGc := closed_of_ty hW hG
  have h0 : RE2 S k ((Tm.glue A φ T e).isub (ISub.cons .zero trivial (ISub.id k))) u0 u0' := by
    rw [isub_cons_id_of_closed hGc]; exact D.ha0
  have := D.ugAt hW (ISub.cons .zero trivial (ISub.id k)) h0
  rwa [isub_cons_id_of_closed hA, isub_cons_id_of_closed he, isub_cons_id_of_closed he', I_subst_cons_id hφ,
    I_subst_cons_id hφ'] at this

/-- The tubes of the compositions in the bases, at near points where `ψ` holds. -/
theorem TGD2.tube (τ : ISub k' k) {r r' : I} (hr : r.Scoped k') (hr' : r'.Scoped k') (he : I.Eq r r')
    (hh : (ival (idEnv k') (ψ.subst τ.τ)).holds) :
    RE2 S k' (A.isub (ISub.cons r hr τ)) (((tgTube φ e u0).isub τ.up).dinst r)
      (((tgTube φ' e' u0').isub τ.up).dinst r') := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨-, -, -, hφ'⟩ := D.closedR hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  rw [isub_up_dinst _ _ _ hr, isub_up_dinst _ _ _ hr']
  -- the starts, at the Glue line at `r`
  have h0 := RE2.isub hW D.ha0 τ
  rw [dinst_isub_end _ (.inl rfl), isub_up_dinst _ _ .zero trivial] at h0
  have hGr := HasTy.isubS hW hG (ISub.cons r hr τ)
  have hc := D.cG k' τ r hr hh
  have hg : RE2 S k' ((Tm.glue A φ T e).isub (ISub.cons r hr τ)) (u0.isub τ) (u0'.isub τ) :=
    RE2.conv hW (RT2.symm hW (tyCode_of_univ hW hGr) hc) h0
  have x := D.ugAt hW (ISub.cons r hr τ) hg
  -- the right side at the near point
  have hψ' : (ival (idEnv k') (ψ'.subst τ.τ)).holds := by
    rw [holds_iff_entails (I.scoped_subst H'.hψ τ.sc)]
    exact ent_trans (entails_of_holds (I.scoped_subst H.hψ τ.sc) hh) (ent_subst D.p12 τ.τ)
  have ht' := ty_line_at hW H'.hψ (minimal_to_spec H'.htube) τ r' hr' hψ'
  have hAA' := (Comp2_ty_base (D.rA k' τ r r' hr hr' he)).2.2.2.2.2
  have n : TmNear (Tm.unglue (φ'.subst (ISub.cons r hr τ).τ) (e'.isub (ISub.cons r hr τ)) (u0'.isub τ))
      ((tgTube φ' e' u0').isub (ISub.cons r' hr' τ)) := by
    show TmNear _ (Tm.unglue (φ'.subst (ISub.cons r' hr' τ).τ) (e'.isub (ISub.cons r' hr' τ))
      (u0'.dshift.isub (ISub.cons r' hr' τ)))
    rw [dshift_isub_cons]
    refine .unglue (FEq.of_eq (I_eq_subst_congr (fun i => ?_) φ')) (near_cons e' hr hr' he) (TmNear.refl _)
    rcases i with _ | i
    · exact he
    · exact I_eq_refl _
  have y := RE2_near hW (D.rAA k' τ r r hr hr (I_eq_refl _)) x n (ht'.tyConv hAA'.symm)
  show RE2 S k' _ (Tm.unglue (φ.subst (ISub.cons r hr τ).τ) (e.isub (ISub.cons r hr τ))
    (u0.dshift.isub (ISub.cons r hr τ))) _
  rw [dshift_isub_cons]
  exact y

/-- The compositions in the bases. -/
theorem TGD2.a1' : RE2 S k (A.dinst .one) (tgA1' A φ e ψ u0) (tgA1' A' φ' e' ψ' u0') := by
  obtain ⟨hA, -, -, -⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hAA' := (Comp2_ty_base (D.rA k (ISub.id k) .one .one trivial trivial (I_eq_refl _))).2.2.2.2.2
  rw [isub_cons_id_of_closed hA, isub_cons_id_of_closed (D.closedR hW).1] at hAA'
  refine comp2r hW D.rA D.rAA (fun k3 Θ X' h => D.kAT k3 Θ X' h) (fun X' h => ?_) (minimal_to_spec H.ha1')
    ((minimal_to_spec H'.ha1').tyConv hAA'.symm) D.p12 D.p21 (fun k3 σ r r' hr hr' he hh => D.tube hW σ hr hr' he hh)
    (D.a0 hW) (fun k3 σ hh => ?_) (fun k3 σ hh => ?_)
  · rw [← isub_cons_id_of_closed hA .one trivial] at h ⊢
    exact D.kAH k (ISub.cons .one trivial (ISub.id k)) X' h
  · have x := D.tube hW σ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) hh
    rwa [tgTube_zero φ' e' u0'] at x
  · have x := D.tube hW σ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) hh
    rwa [tgTube_zero φ e u0] at x


/-- On `δ`, the face of the left line holds everywhere along it. -/
theorem TGD2.faceL (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (σ : ISub k' (k + 1)) :
    (ival (idEnv k') (φ.subst σ.τ)).holds := by
  obtain ⟨-, -, -, hφ⟩ := D.closedL hW
  have h1 : I.Entails .one φ := ent_trans (ent_shift (entails_of_holds D.hδs hδ)) (ent_forall_shift D.hδ1)
  rw [holds_iff_entails (I.scoped_subst hφ σ.sc)]
  exact ent_subst h1 σ.τ

omit hW in
theorem TGD2.hδ' (hδ : (ival (idEnv k) δ).holds) : (ival (idEnv k) δ').holds := by
  rw [holds_iff_entails D.hδs']
  exact ent_trans (ent_trans (ent_trans (entails_of_holds D.hδs hδ) D.hδ1) (FEq.forall0 ⟨D.f12, D.f21⟩).1) D.hδ2'

/-- Where the face holds, the left Glue line and its fiber are related. -/
theorem TGD2.fibG {k' : ℕ} (σ : ISub k' (k + 1)) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) :
    RT2 S k' (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨-, -, -, hφ⟩ := D.closedL hW
  have hGσ := HasTy.isubS hW hG σ
  rw [isub_glue] at hGσ ⊢
  exact RT2_glue_fib0 hW hGσ (entails_of_holds (I.scoped_subst hφ σ.sc) hh) (D.rTT k' σ hh)

/-- On `δ`, the fiber line is constant on `ψ`. -/
theorem TGD2.cT (hδ : (ival (idEnv k) δ).holds) : LineConst S k T ψ := by
  intro k' σ r hr hh
  obtain ⟨l, hG⟩ := D.hG
  have h1 := D.fibG hW (ISub.cons r hr σ) (D.faceL hW hδ _)
  have h0 := D.fibG hW (ISub.cons .zero trivial σ) (D.faceL hW hδ _)
  have hX := tyCode_of_univ hW (glue_fiber_ty hW hG _ (D.faceL hW hδ (ISub.cons r hr σ))).choose_spec.1
  have hX0 := tyCode_of_univ hW (glue_fiber_ty hW hG _ (D.faceL hW hδ (ISub.cons .zero trivial σ))).choose_spec.1
  exact RT2.trans hW hX (RT2.trans hW hX h1 (D.cG k' σ r hr hh))
    (RT2.symm hW hX0 h0)

/-- On `δ`, the fiber lines are related at near points. -/
theorem TGD2.rTL (hδ : (ival (idEnv k) δ).holds) : LineRob S k T T' := fun k' τ r r' hr hr' he =>
  D.rTN hW τ hr hr' he (D.faceL hW hδ _)

/-- On `δ`, the transports in the fibers. -/
theorem TGD2.t1' (hδ : (ival (idEnv k) δ).holds) : RE2 S k (T.dinst .one) (tgT1 T ψ u0) (tgT1 T' ψ' u0') := by
  obtain ⟨hA, hT, -, -⟩ := D.closedL hW
  obtain ⟨-, hT', -, -⟩ := D.closedR hW
  obtain ⟨l, hG⟩ := D.hG
  have hGc := closed_of_ty hW hG
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hδe := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hδe' := ent_cof_one hW (entails_of_holds D.hδs' (D.hδ' hδ))
  have ht := HasTy.restrict (Φ' := .one) trivial hδe (minimal_to_spec H.ht1)
  have ht' := HasTy.restrict (Φ' := .one) trivial hδe' (minimal_to_spec H'.ht1)
  have hTT1 := D.rTN hW (ISub.id k) (r := .one) (r' := .one) trivial trivial (I_eq_refl _) (D.faceL hW hδ _)
  rw [isub_cons_id_of_closed hT, isub_cons_id_of_closed hT'] at hTT1
  have ht'' := ht'.tyConv (Comp2_ty_base hTT1).2.2.2.2.2.symm
  have hTT := D.rT (k + 1) (ISub.id (k + 1)) (D.faceL hW hδ _)
  rw [isub_id_of_closed hT, isub_id_of_closed hT'] at hTT
  have hK := D.kTT k (ISub.id (k + 1)) (D.faceL hW hδ _) T' (by rw [isub_id_of_closed hT]; exact hTT)
  rw [isub_id_of_closed hT] at hK
  -- the starts, at the fiber
  have h0 : RE2 S k (T.dinst .zero) u0 u0' := by
    have g := D.fibG hW (ISub.cons .zero trivial (ISub.id k)) (D.faceL hW hδ _)
    rw [isub_cons_id_of_closed hT, isub_cons_id_of_closed hGc] at g
    have hX := tyCode_of_univ hW (glue_fiber_ty hW hG _ (D.faceL hW hδ (ISub.cons .zero trivial (ISub.id k)))).choose_spec.1
    rw [isub_cons_id_of_closed hT] at hX
    exact RE2.conv hW (RT2.symm hW hX g) D.ha0
  exact hK (D.rTL hW hδ) ψ ψ' u0 u0' (D.cT hW hδ) ht ht''
    (eqTm_transp_of hW ht ht'' (Comp2_ty_base hTT).2.2.2.2.2 D.p12 D.p21 (RE2.typed h0).2.2) D.p12 D.p21 h0


/-- On `δ`, the starts in the fibers, where `ψ` holds or at the start of the line. -/
theorem TGD2.u0At (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) (r : I) (hr : r.Scoped k')
    (hψ : (ival (idEnv k') (ψ.subst τ.τ)).holds ∨ r = .zero) :
    RE2 S k' (T.isub (ISub.cons r hr τ)) (u0.isub τ) (u0'.isub τ) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨-, -, -, hφ⟩ := D.closedL hW
  have h0 := RE2.isub hW D.ha0 τ
  rw [dinst_isub_end _ (.inl rfl), isub_up_dinst _ _ .zero trivial] at h0
  have hGr := HasTy.isubS hW hG (ISub.cons r hr τ)
  have hg : RE2 S k' ((Tm.glue A φ T e).isub (ISub.cons r hr τ)) (u0.isub τ) (u0'.isub τ) := by
    rcases hψ with hh | rfl
    · exact RE2.conv hW (RT2.symm hW (tyCode_of_univ hW hGr) (D.cG k' τ r hr hh)) h0
    · exact h0
  rw [isub_glue] at hg hGr
  exact RE2_glue_fib hW hGr (entails_of_holds (I.scoped_subst hφ (ISub.cons r hr τ).sc) (D.faceL hW hδ _)) (D.rTT k' _ (D.faceL hW hδ _)) hg

/-- On `δ`, the fiber line is typed. -/
theorem TGD2.hTδ (hδ : (ival (idEnv k) δ).holds) : ∃ l, HasTy S (k + 1) .one [] T (.univ l) := by
  obtain ⟨l, H⟩ := D.tgL hW
  exact ⟨l, HasTy.restrict (Φ' := .one) trivial (ent_shift (ent_cof_one hW (entails_of_holds D.hδs hδ)))
    (minimal_to_spec H.hTZ)⟩

/-- On `δ`, the fiber line is related to itself at near points. -/
theorem TGD2.rTLL (hδ : (ival (idEnv k) δ).holds) : LineRob S k T T := fun k' τ y y' hy hy' he => by
  obtain ⟨l, hT⟩ := D.hTδ hW hδ
  exact RT2_near hW (tyCode_of_univ hW (HasTy.isubS hW hT _)) (D.rTT k' _ (D.faceL hW hδ _)) (near_cons T hy hy' he)
    ⟨l, .inl (HasTy.isubS hW hT _)⟩

/-- On `δ`, the transport fillers in the fibers. -/
theorem TGD2.tfAt (hδ : (ival (idEnv k) δ).holds) {k3 : ℕ} (σ σ' : ISub k3 (k + 1)) (et : σ.tail = σ'.tail)
    (e0 : I.Eq (σ.τ 0) (σ'.τ 0)) :
    RE2 S k3 (T.isub σ) ((Tm.transpFill T ψ u0).isub σ) ((Tm.transpFill T' ψ' u0').isub σ') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨-, hTc, -, -⟩ := D.closedL hW
  obtain ⟨l, hT⟩ := D.hTδ hW hδ
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hδe := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hδe' := ent_cof_one hW (entails_of_holds D.hδs' (D.hδ' hδ))
  have hF := HasTy.restrict (Φ' := .one) trivial (ent_shift hδe)
    (minimal_to_spec (transpFill_typed hS H.hTZ H.hψ H.hconstT H.hu0T).1)
  have hF' := HasTy.restrict (Φ' := .one) trivial (ent_shift hδe')
    (minimal_to_spec (transpFill_typed hS H'.hTZ H'.hψ H'.hconstT H'.hu0T).1)
  have ha := D.u0At hW hδ (ISub.id k) .zero trivial (.inr rfl)
  rw [isub_cons_id_of_closed hTc, isub_id_of_closed (closed_ty H.hu0), isub_id_of_closed (closed_ty H'.hu0)] at ha
  refine tfill_rel hW hT H.hψ D.p12 D.p21 (D.rTL hW hδ) (D.rTLL hW hδ) (D.cT hW hδ)
    (fun k4 τ y y' hy hy' he _ => ?_) hF hF' ha k3 σ σ' et e0
  exact KanT2.at (D.kTT k4 (ISub.cons y hy τ.up.tail) (D.faceL hW hδ _) _ (D.rTL hW hδ (k4 + 1) τ.up.tail y y' hy hy' he)) _ _

/-- The first components of the equivalences, applied at near points. -/
theorem TGD2.eApp {k' : ℕ} (τ : ISub k' k) {r r' : I} (hr : r.Scoped k') (hr' : r'.Scoped k') (he : I.Eq r r')
    (hh : (ival (idEnv k') (φ.subst (ISub.cons r hr τ).τ)).holds) {x x' : Tm}
    (hx : RE2 S k' (T.isub (ISub.cons r hr τ)) x x') :
    RE2 S k' (A.isub (ISub.cons r hr τ)) (.app (.fst (e.isub (ISub.cons r hr τ))) x)
      (.app (.fst (e'.isub (ISub.cons r' hr' τ))) x') :=
  RE2_equiv_app hW (D.rEN hW τ hr hr' he hh) hx


/-- The base lines are judgmentally equal. -/
theorem TGD2.eqA : EqTm S (k + 1) .one [] A A' (.univ maxLevel) := by
  obtain ⟨hA, -, -, -⟩ := D.closedL hW
  obtain ⟨hA', -, -, -⟩ := D.closedR hW
  obtain ⟨l1, H⟩ := D.tgL hW
  have h := D.rA.at (ISub.id (k + 1))
  rw [isub_id_of_closed hA, isub_id_of_closed hA'] at h
  exact tyEq_top hW (minimal_to_spec H.hA) (Comp2_ty_base h).2.2.2.2.2

/-- The tubes of the compositions in the bases are judgmentally equal. -/
theorem TGD2.eqTube : EqTm S (k + 1) (cof .one ψ).shift [] (tgTube φ e u0) (tgTube φ' e' u0') A := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hc : (cof .one ψ).shift.Scoped (k + 1) := KubusCore.I.scoped_shift ⟨trivial, H.hψ⟩
  have hu' : HasTy S (k + 1) (cof .one ψ).shift [] (tgTube φ' e' u0') A :=
    (HasTy.restrict hc (ent_shift (ent_and_mono (ent_refl _) D.p12)) (minimal_to_spec H'.htube)).conv
      (EqTm.restrict hc (ent_trans (ent_shift (ent_and_left _ _)) (ent_refl _)) (D.eqA hW)).symm
  exact eqTube_of_rel hW H.hψ (HasTy.restrict hc (ent_trans (ent_shift (ent_and_left _ _)) (ent_refl _))
    ((minimal_to_spec H.hA).cumulTo (lvl_of_ty hW (minimal_to_spec H.hA)) le_rfl))
    (minimal_to_spec H.htube) hu' fun k3 σ r hr hh => D.tube hW σ hr hr (I_eq_refl _) hh

/-- The fillers of the compositions in the bases, at near restrictions. -/
theorem TGD2.fillAt {k3 : ℕ} (σ σ' : ISub k3 (k + 1)) (et : σ.tail = σ'.tail) (e0 : I.Eq (σ.τ 0) (σ'.τ 0)) :
    RE2 S k3 (A.isub σ) ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).isub σ)
      ((Tm.fill A' ψ' (tgTube φ' e' u0') (tgA0 φ' e' u0')).isub σ') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hF := minimal_to_spec (fill_typed hS H.hA H.hψ H.htube H.ha0 H.htube_side).1
  have hF' := (minimal_to_spec (fill_typed hS H'.hA H'.hψ H'.htube H'.ha0 H'.htube_side).1).conv
    (D.eqA hW).symm
  have hteq := D.eqTube hW
  have heqF := minimal_to_spec_eq (fill_cong hW (spec_to_minimal hW hF) (spec_to_minimal hW hF')
    ⟨_, spec_to_minimal_eq hW (D.eqA hW)⟩ (spec_to_minimal_eq hW hteq)
    (spec_to_minimal_eq hW (RE2.typed (D.a0 hW)).2.2) D.p12 D.p21)
  refine fill_rel hW H.hψ D.rA D.rAA (fun k4 Θ X' h => D.kAT k4 Θ X' h) (fun k4 Θ X' h => D.kAH k4 Θ X' h) hF hF'
    heqF hteq D.p12 D.p21 (fun k4 σ r r' hr hr' he hh => D.tube hW σ hr hr' he hh) (D.a0 hW)
    (fun k4 σ hh => ?_) (fun k4 σ hh => ?_) σ σ' et e0
  · have x := D.tube hW σ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) hh
    rwa [tgTube_zero φ' e' u0'] at x
  · have x := D.tube hW σ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) hh
    rwa [tgTube_zero φ e u0] at x


/-- On `δ`, the equivalences applied to the starts, where `ψ` holds or at the start of the line. -/
theorem TGD2.eu0 (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) {r r' : I} (hr : r.Scoped k')
    (hr' : r'.Scoped k') (he : I.Eq r r') (hψ : (ival (idEnv k') (ψ.subst τ.τ)).holds ∨ r = .zero) :
    RE2 S k' (A.isub (ISub.cons r hr τ)) (.app (.fst (e.isub (ISub.cons r hr τ))) (u0.isub τ))
      (.app (.fst (e'.isub (ISub.cons r' hr' τ))) (u0'.isub τ)) :=
  D.eApp hW τ hr hr' he (D.faceL hW hδ _) (D.u0At hW hδ τ r hr hψ)

omit D in
/-- A related element is related to itself. -/
theorem RE2.reflL {X t t' : Tm} (hXX : RT2 S k X X) (h : RE2 S k X t t') : RE2 S k X t t :=
  RE2.trans hW hXX h (RE2.symm hW hXX h)

/-- On `δ`, where `ψ` holds, the tube of the bases is the equivalence applied to the start. -/
theorem TGD2.tubeE (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) {r : I} (hr : r.Scoped k')
    (hh : (ival (idEnv k') (ψ.subst τ.τ)).holds) :
    RE2 S k' (A.isub (ISub.cons r hr τ)) (((tgTube φ e u0).isub τ.up).dinst r)
      (.app (.fst (e.isub (ISub.cons r hr τ))) (u0.isub τ)) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨hA, -, -, hφ⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨-, lA, hAt, -⟩ := glue_data hW hG
  have hAA := D.rAA k' τ r r hr hr (I_eq_refl _)
  have x := RE2.reflL hW hAA (D.eu0 hW hδ τ hr hr (I_eq_refl _) (.inl hh))
  have hu := ty_line_at hW H.hψ (minimal_to_spec H.htube) τ r hr hh
  rw [isub_up_dinst _ _ _ hr, tgTube_cons] at *
  have hg : HasTy S k' .one [] (u0.isub τ) ((Tm.glue A φ T e).isub (ISub.cons r hr τ)) := by
    have h0 := RE2.isub hW D.ha0 τ
    rw [dinst_isub_end _ (.inl rfl), isub_up_dinst _ _ .zero trivial] at h0
    exact (RE2.typed h0).1.tyConv (Comp2_ty_base (D.cG k' τ r hr hh)).2.2.2.2.2.symm
  obtain ⟨-, -, heσ⟩ := glue_fiber_ty hW hG (ISub.cons r hr τ) (D.faceL hW hδ _)
  rw [isub_glue] at hg
  have hst := stable_unglueFace hW (entails_of_holds (I.scoped_subst hφ (ISub.cons r hr τ).sc) (D.faceL hW hδ _))
    hu hg (HasTy.isubS hW hAt _) heσ (TyEq.refl _)
  exact RE2.expandL hW hAA hu (RE2.typed x).1 hst x


/-- The left tube, related to itself at near points. -/
theorem TGD2.tubeL (τ : ISub k' k) {r r' : I} (hr : r.Scoped k') (hr' : r'.Scoped k') (he : I.Eq r r')
    (hh : (ival (idEnv k') (ψ.subst τ.τ)).holds) :
    RE2 S k' (A.isub (ISub.cons r hr τ)) (((tgTube φ e u0).isub τ.up).dinst r) (((tgTube φ e u0).isub τ.up).dinst r') := by
  have hAA := D.rAA k' τ r r hr hr (I_eq_refl _)
  have x := D.tube hW τ hr hr' he hh
  have y := RE2.conv hW (D.rAA k' τ r' r hr' hr (I_eq_symm he)) (D.tube hW τ hr' hr' (I_eq_refl _) hh)
  exact RE2.trans hW hAA x (RE2.symm hW hAA y)

theorem TGD2.hF : HasTy S (k + 1) .one [] (Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)) A := by
  obtain ⟨l1, H⟩ := D.tgL hW
  exact minimal_to_spec (fill_typed (sigClosed_of_wfSig hW) H.hA H.hψ H.htube H.ha0 H.htube_side).1

/-- On `δ`, where `ψ` holds, the filler of the bases is the equivalence applied to the start. -/
theorem TGD2.fillE (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) {r : I} (hr : r.Scoped k')
    (hh : (ival (idEnv k') (ψ.subst τ.τ)).holds) :
    RE2 S k' (A.isub (ISub.cons r hr τ)) ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).isub (ISub.cons r hr τ))
      (.app (.fst (e.isub (ISub.cons r hr τ))) (u0.isub τ)) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hAA := D.rAA k' τ r r hr hr (I_eq_refl _)
  have a := fill_face_pt hW H.hψ D.rAA (D.hF hW) (fun k4 σ r r' hr hr' he hh => D.tubeL hW σ hr hr' he hh) τ r hr hh
  exact RE2.trans hW hAA a (D.tubeE hW hδ τ hr hh)

/-- On `δ`, where `ψ` holds, the transport filler in the fiber is the start. -/
theorem TGD2.tfE (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) {r : I} (hr : r.Scoped k')
    (hh : (ival (idEnv k') (ψ.subst τ.τ)).holds ∨ r = .zero) :
    RE2 S k' (T.isub (ISub.cons r hr τ)) ((Tm.transpFill T ψ u0).isub (ISub.cons r hr τ)) (u0.isub τ) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨-, hTc, -, -⟩ := D.closedL hW
  obtain ⟨l, hT⟩ := D.hTδ hW hδ
  obtain ⟨l1, H⟩ := D.tgL hW
  have hδe := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hF := HasTy.restrict (Φ' := .one) trivial (ent_shift hδe)
    (minimal_to_spec (transpFill_typed hS H.hTZ H.hψ H.hconstT H.hu0T).1)
  have ha := D.u0At hW hδ (ISub.id k) .zero trivial (.inr rfl)
  rw [isub_cons_id_of_closed hTc, isub_id_of_closed (closed_ty H.hu0), isub_id_of_closed
    (closed_ty (D.tgR hW).choose_spec.hu0)] at ha
  have hTT0 : RT2 S k (T.dinst .zero) (T.dinst .zero) := by
    have := D.rTT k (ISub.cons .zero trivial (ISub.id k)) (D.faceL hW hδ _)
    rwa [isub_cons_id_of_closed hTc] at this
  have hor : I.Entails .one (I.or (ψ.subst τ.τ) (.neg r)) := by
    rcases hh with hh | rfl
    · exact ent_trans (entails_of_holds (I.scoped_subst H.hψ τ.sc) hh) (ent_or_left _ _)
    · exact ent_trans (show I.Entails .one (I.neg .zero) by decide) (ent_or_right _ _)
  exact tfill_face hW hT (D.rTLL hW hδ) (D.cT hW hδ) hF (RE2.reflL hW hTT0 ha) τ r hr hor hh


/-- On `δ`, the systems of the bodies of `ω`, at a point of the body and a near point of the line. -/
theorem TGD2.sysAt (hδ : (ival (idEnv k) δ).holds) {k3 : ℕ} (σ0 : ISub k3 k) {y : I} (hy : y.Scoped k3)
    {x x' : I} (hx : x.Scoped k3) (hx' : x'.Scoped k3) (he : I.Eq x x')
    (hh : (ival (idEnv k3) ((tgChi ψ).subst (ISub.cons y hy σ0).τ)).holds) :
    RE2 S k3 (A.isub (ISub.cons x hx σ0)) ((tgSys A φ T e ψ u0).isub (ISub.cons x hx (ISub.cons y hy σ0)))
      ((tgSys A' φ' T' e' ψ' u0').isub (ISub.cons x' hx' (ISub.cons y hy σ0))) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hAA := D.rAA k3 σ0 x x hx hx (I_eq_refl _)
  have hδe := entails_of_holds D.hδs hδ
  have hδe' := entails_of_holds D.hδs' (D.hδ' hδ)
  have hψσ := I.scoped_subst H.hψ σ0.sc
  have hψσ' := I.scoped_subst H'.hψ σ0.sc
  have hχ : I.Entails .one (I.or (ψ.subst σ0.τ) (.or (.neg y) y)) := by
    have := entails_of_holds (I.scoped_subst (show (tgChi ψ).Scoped (k + 1) from
      ⟨KubusCore.I.scoped_shift H.hψ, show 0 < k + 1 by omega, show 0 < k + 1 by omega⟩) (ISub.cons y hy σ0).sc) hh
    simpa only [tgChi, I.subst, I_shift_cons] using this
  have hsp := tgSys_ty hW H hδe σ0 hy hχ hx
  have hsp' := (tgSys_ty hW H' hδe' σ0 hy (ent_trans hχ (ent_or_elim (ent_trans (ent_subst D.p12 _) (ent_or_left _ _))
    (ent_or_right _ _))) hx').tyConv (Comp2_ty_base (D.rA k3 σ0 x x' hx hx' he)).2.2.2.2.2.symm
  unfold tgSys at hsp hsp' ⊢
  rw [tgSys'_isub] at hsp hsp'
  rw [tgSys'_isub, tgSys'_isub]
  -- the restrictions of the components
  have rs : ∀ {k4 : ℕ} (σ2 : ISub k4 k3) (X : Tm) (z : I) (hz : z.Scoped k3),
      (X.isub (ISub.cons z hz σ0)).isub σ2 = X.isub (ISub.cons (z.subst σ2.τ) (I.scoped_subst hz σ2.sc) (σ0.comp σ2)) :=
    fun σ2 X z hz => by rw [Tm.isub_isub, ISub.cons_comp]
  have ψc : ∀ {k4 : ℕ} (σ2 : ISub k4 k3), I.Entails .one ((ψ.subst σ0.τ).subst σ2.τ) →
      (ival (idEnv k4) (ψ.subst (σ0.comp σ2).τ)).holds := fun σ2 h => by
    rw [holds_iff_entails (I.scoped_subst H.hψ (σ0.comp σ2).sc), I_subst_comp]; exact h
  have hxσ : ∀ {k4 : ℕ} (σ2 : ISub k4 k3), I.Eq (x.subst σ2.τ) (x'.subst σ2.τ) := fun σ2 => I_eq_subst he _
  refine RE2_pathSys hW hψσ hψσ' hy hy (I_eq_refl _) (ent_subst D.p12 _) (ent_subst D.p21 _) hχ hAA hsp hsp'
    (fun k4 σ2 h => ?_) (fun k4 σ2 h _ => ?_) (fun k4 σ2 h _ => ?_) (fun k4 σ2 h _ => ?_) (fun k4 σ2 h _ => ?_)
    (fun k4 σ2 _ => ?_) (fun k4 σ2 _ => ?_) <;>
    simp only [isub_app, isub_fst, rs, Tm.isub_isub] <;>
    have hAA2 := D.rAA k4 (σ0.comp σ2) _ _ (I.scoped_subst hx σ2.sc) (I.scoped_subst hx σ2.sc) (I_eq_refl _)
  · exact D.eu0 hW hδ (σ0.comp σ2) _ _ (hxσ σ2) (.inl (ψc σ2 h))
  · -- `e.1 u0` against `e'.1 tf'`
    have t1 := D.tfE hW hδ (σ0.comp σ2) (I.scoped_subst hx σ2.sc) (.inl (ψc σ2 h))
    have hTT := D.rTT k4 _ (D.faceL hW hδ (ISub.cons _ (I.scoped_subst hx σ2.sc) (σ0.comp σ2)))
    have t2 := D.tfAt hW hδ (ISub.cons _ (I.scoped_subst hx σ2.sc) (σ0.comp σ2))
      (ISub.cons _ (I.scoped_subst hx' σ2.sc) (σ0.comp σ2)) rfl (hxσ σ2)
    exact D.eApp hW (σ0.comp σ2) _ _ (hxσ σ2) (D.faceL hW hδ _) (RE2.trans hW hTT (RE2.symm hW hTT t1) t2)
  · -- `e.1 tf` against `e'.1 u0'`
    have t1 := D.tfE hW hδ (σ0.comp σ2) (I.scoped_subst hx σ2.sc) (.inl (ψc σ2 h))
    have hTT := D.rTT k4 _ (D.faceL hW hδ (ISub.cons _ (I.scoped_subst hx σ2.sc) (σ0.comp σ2)))
    have t2 := D.u0At hW hδ (σ0.comp σ2) _ (I.scoped_subst hx σ2.sc) (.inl (ψc σ2 h))
    exact D.eApp hW (σ0.comp σ2) _ _ (hxσ σ2) (D.faceL hW hδ _) (RE2.trans hW hTT t1 t2)
  · -- `e.1 u0` against the filler
    have f1 := D.fillE hW hδ (σ0.comp σ2) (I.scoped_subst hx σ2.sc) (ψc σ2 h)
    have f2 := D.fillAt hW (ISub.cons _ (I.scoped_subst hx σ2.sc) (σ0.comp σ2))
      (ISub.cons _ (I.scoped_subst hx' σ2.sc) (σ0.comp σ2)) rfl (hxσ σ2)
    exact RE2.trans hW hAA2 (RE2.symm hW hAA2 f1) f2
  · -- the filler against `e'.1 u0'`
    have f1 := D.fillE hW hδ (σ0.comp σ2) (I.scoped_subst hx σ2.sc) (ψc σ2 h)
    exact RE2.trans hW hAA2 f1 (D.eu0 hW hδ (σ0.comp σ2) _ _ (hxσ σ2) (.inl (ψc σ2 h)))
  · exact D.eApp hW (σ0.comp σ2) _ _ (hxσ σ2) (D.faceL hW hδ _)
      (D.tfAt hW hδ (ISub.cons _ (I.scoped_subst hx σ2.sc) (σ0.comp σ2))
        (ISub.cons _ (I.scoped_subst hx' σ2.sc) (σ0.comp σ2)) rfl (hxσ σ2))
  · exact D.fillAt hW (ISub.cons _ (I.scoped_subst hx σ2.sc) (σ0.comp σ2))
      (ISub.cons _ (I.scoped_subst hx' σ2.sc) (σ0.comp σ2)) rfl (hxσ σ2)


/-- On `δ`, the base of the start is the equivalence applied to the start. -/
theorem TGD2.a0E (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) :
    RE2 S k' (A.isub (ISub.cons .zero trivial τ)) ((tgA0 φ e u0).isub τ)
      (.app (.fst (e.isub (ISub.cons .zero trivial τ))) (u0.isub τ)) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨hA, -, -, hφ⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨-, lA, hAt, -⟩ := glue_data hW hG
  have hAA := D.rAA k' τ .zero .zero trivial trivial (I_eq_refl _)
  have x := RE2.reflL hW hAA (D.eu0 hW hδ τ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (.inr rfl))
  have hu := HasTy.isubS hW (minimal_to_spec H.ha0) τ
  rw [← tgTube_zero, isub_up_dinst _ _ .zero trivial, tgTube_cons] at hu ⊢
  rw [dinst_isub_end _ (.inl rfl), isub_up_dinst _ _ .zero trivial] at hu
  have h0 := RE2.isub hW D.ha0 τ
  rw [dinst_isub_end _ (.inl rfl), isub_up_dinst _ _ .zero trivial] at h0
  have hg := (RE2.typed h0).1
  obtain ⟨-, -, heσ⟩ := glue_fiber_ty hW hG (ISub.cons .zero trivial τ) (D.faceL hW hδ _)
  rw [isub_glue] at hg
  have hst := stable_unglueFace hW (entails_of_holds (I.scoped_subst hφ (ISub.cons .zero trivial τ).sc)
    (D.faceL hW hδ _)) hu hg (HasTy.isubS hW hAt _) heσ (TyEq.refl _)
  exact RE2.expandL hW hAA hu (RE2.typed x).1 hst x

/-- On `δ`, the system of the body of `ω` at the start of its line, against the base of the right body. -/
theorem TGD2.sysZ (hδ : (ival (idEnv k) δ).holds) {k3 : ℕ} (σ0 : ISub k3 k) {y : I} (hy : y.Scoped k3)
    (hχ : I.Entails .one (I.or (ψ.subst σ0.τ) (.or (.neg y) y))) :
    RE2 S k3 (A.isub (ISub.cons .zero trivial σ0)) ((tgSys A φ T e ψ u0).isub (ISub.cons .zero trivial (ISub.cons y hy σ0)))
      (.app (.fst (e'.isub (ISub.cons .zero trivial σ0))) (u0'.isub σ0)) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hAA := D.rAA k3 σ0 .zero .zero trivial trivial (I_eq_refl _)
  have hδe := entails_of_holds D.hδs hδ
  have hψσ := I.scoped_subst H.hψ σ0.sc
  have hsp := tgSys_ty hW H hδe σ0 hy hχ (x := .zero) trivial
  have base := D.eu0 hW hδ σ0 (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (.inr rfl)
  unfold tgSys at hsp ⊢
  rw [tgSys'_isub] at hsp ⊢
  have rs : ∀ {k4 : ℕ} (σ2 : ISub k4 k3) (X : Tm),
      (X.isub (ISub.cons .zero trivial σ0)).isub σ2 = X.isub (ISub.cons .zero trivial (σ0.comp σ2)) :=
    fun σ2 X => by rw [Tm.isub_isub, ISub.cons_comp]; rfl
  have comp0 : ∀ {k4 : ℕ} (σ2 : ISub k4 k3),
      RE2 S k4 (A.isub (ISub.cons .zero trivial (σ0.comp σ2)))
        (.app (.fst (e.isub (ISub.cons .zero trivial (σ0.comp σ2)))) ((Tm.transpFill T ψ u0).isub
          (ISub.cons .zero trivial (σ0.comp σ2))))
        (.app (.fst (e'.isub (ISub.cons .zero trivial (σ0.comp σ2)))) (u0'.isub (σ0.comp σ2))) := by
    intro k4 σ2
    have t1 := D.tfE hW hδ (σ0.comp σ2) (r := .zero) trivial (.inr rfl)
    have hTT := D.rTT k4 _ (D.faceL hW hδ (ISub.cons .zero trivial (σ0.comp σ2)))
    have t2 := D.u0At hW hδ (σ0.comp σ2) .zero trivial (.inr rfl)
    exact D.eApp hW (σ0.comp σ2) (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (D.faceL hW hδ _)
      (RE2.trans hW hTT t1 t2)
  have fill0 : ∀ {k4 : ℕ} (σ2 : ISub k4 k3),
      RE2 S k4 (A.isub (ISub.cons .zero trivial (σ0.comp σ2)))
        ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).isub (ISub.cons .zero trivial (σ0.comp σ2)))
        (.app (.fst (e'.isub (ISub.cons .zero trivial (σ0.comp σ2)))) (u0'.isub (σ0.comp σ2))) := by
    intro k4 σ2
    have hAA2 := D.rAA k4 (σ0.comp σ2) .zero .zero trivial trivial (I_eq_refl _)
    have hA0 := D.rAA k (ISub.id k) .zero .zero trivial trivial (I_eq_refl _)
    rw [isub_cons_id_of_closed (D.closedL hW).1] at hA0
    have f := fill_zero_pt hW H.hψ D.rAA (D.hF hW) (fun k5 σ r r' hr hr' he hh => D.tubeL hW σ hr hr' he hh)
      (RE2.reflL hW hA0 (D.a0 hW))
      (fun k5 σ hh => by
        have x := D.tubeL hW σ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) hh
        rw [tgTube_zero φ e u0]; rwa [tgTube_zero φ e u0] at x) (σ0.comp σ2)
    exact RE2.trans hW hAA2 (RE2.trans hW hAA2 f (D.a0E hW hδ _))
      (D.eu0 hW hδ (σ0.comp σ2) (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (.inr rfl))
  refine RE2_split_l hW hψσ ⟨hy, hy⟩ hχ hAA hsp (RE2.typed base).2.1 (fun k4 σ2 h => ?_) (fun k4 σ2 h => ?_)
  · simp only [isub_app, isub_fst, rs, Tm.isub_isub]
    exact D.eu0 hW hδ (σ0.comp σ2) (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (.inr rfl)
  · have hσ := HasTy.isubS hW hsp σ2
    have hin := HasTy.eqR (EqTm.splitR h hσ)
    have hAA2 := D.rAA k4 (σ0.comp σ2) .zero .zero trivial trivial (I_eq_refl _)
    simp only [isub_app, isub_fst, rs, Tm.isub_isub] at hin ⊢
    refine RE2_split_l hW (I.scoped_subst hy σ2.sc) (I.scoped_subst hy σ2.sc) (by simpa only [I.subst] using h) hAA2 hin
      (RE2.typed (D.eu0 hW hδ (σ0.comp σ2) (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (.inr rfl))).2.1
      (fun k5 σ3 _ => ?_) (fun k5 σ3 _ => ?_)
    · simp only [← isub_eq_subst, isub_app, isub_fst, Tm.isub_isub, ISub.cons_comp, I.subst]
      have := comp0 (σ2.comp σ3)
      simp only [← ISub.comp_assoc] at this ⊢
      exact this
    · simp only [← isub_eq_subst, isub_app, isub_fst, Tm.isub_isub, ISub.cons_comp, I.subst]
      have := fill0 (σ2.comp σ3)
      simp only [← ISub.comp_assoc] at this ⊢
      exact this


/-- On `δ`, the bodies of `ω`. -/
theorem TGD2.body (hδ : (ival (idEnv k) δ).holds) :
    RE2 S (k + 1) (A.dinst .one).dshift (tgBody A φ T e ψ u0) (tgBody A' φ' T' e' ψ' u0') := by
  obtain ⟨hAc, -, hec, -⟩ := D.closedL hW
  obtain ⟨hAc', -, hec', -⟩ := D.closedR hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hδe := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hδe' := ent_cof_one hW (entails_of_holds D.hδs' (D.hδ' hδ))
  have hb := HasTy.restrict (Φ' := .one) trivial (ent_shift hδe) (minimal_to_spec H.hbody)
  have hb' := HasTy.restrict (Φ' := .one) trivial (ent_shift hδe') (minimal_to_spec H'.hbody)
  have hA1 := D.rA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
  rw [isub_cons_id_of_closed hAc, isub_cons_id_of_closed hAc'] at hA1
  have hX1 : TyCode k (semK S k (A.dinst .one)) := tyCode_of_univ hW (minimal_to_spec (H.hAr (r := .one) trivial))
  have eT := (Comp2_ty_base (RT2.dshift hW hX1 hA1)).2.2.2.2.2
  have hb'' := hb'.tyConv eT.symm
  rw [← L_C1] at hb hb'' ⊢
  unfold tgBody at hb hb'' ⊢
  have hχs : (tgChi ψ).Scoped (k + 1) :=
    ⟨KubusCore.I.scoped_shift H.hψ, show 0 < k + 1 by omega, show 0 < k + 1 by omega⟩
  have hθ : ∀ {k4 : ℕ} (σ0 : ISub k4 k) (y : I) (hy : y.Scoped k4),
      (ival (idEnv k4) ((tgChi ψ).subst (ISub.cons y hy σ0).τ)).holds →
      I.Entails .one (I.or (ψ.subst σ0.τ) (.or (.neg y) y)) := fun σ0 y hy hh => by
    have := entails_of_holds (I.scoped_subst hχs (ISub.cons y hy σ0).sc) hh
    simpa only [tgChi, I.subst, I_shift_cons] using this
  refine comp2r hW (fun k4 τ z z' hz hz' he => ?_) (fun k4 τ z z' hz hz' he => ?_) (fun k3 Θ X' h => ?_)
    (fun X' h => ?_) hb hb'' ?_ ?_ (fun k3 σ r r' hr hr' he hh => ?_) ?_ (fun k3 σ hh => ?_) (fun k3 σ hh => ?_)
  · rw [sk2_cons, sk2_cons]; exact D.rA k4 τ.tail z z' hz hz' he
  · rw [sk2_cons, sk2_cons]; exact D.rAA k4 τ.tail z z' hz hz' he
  · rw [sk2_closed hAc, Tm.isub_isub] at h ⊢; exact D.kAT k3 _ X' h
  · have e1 : (A.dinst .one).dshift = A.isub (ISub.cons .one trivial (ISub.wk k)) := by
      rw [← dshift_eq_isub_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))),
        dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial]
    rw [L_C1, e1] at h ⊢; exact D.kAH (k + 1) _ X' h
  · exact ent_or_elim (ent_trans (ent_shift D.p12) (ent_or_left _ _)) (ent_or_right _ _)
  · exact ent_or_elim (ent_trans (ent_shift D.p21) (ent_or_left _ _)) (ent_or_right _ _)
  · obtain ⟨y, hy, σ0, rfl⟩ : ∃ y hy σ0, σ = ISub.cons y hy σ0 := ⟨_, _, _, (ISub.cons_tail σ).symm⟩
    rw [sk2_cons, isub_up_dinst _ _ _ hr, isub_up_dinst _ _ _ hr', ISub.tail_cons]
    exact D.sysAt hW hδ σ0 hy hr hr' he hh
  · rw [L_C0]
    have x := RE2.dshift hW (D.eu0 hW hδ (ISub.id k) (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (.inr rfl))
    rw [isub_cons_id_of_closed hAc, isub_cons_id_of_closed hec, isub_cons_id_of_closed hec',
      isub_id_of_closed (closed_ty H.hu0), isub_id_of_closed (closed_ty H'.hu0)] at x
    exact x
  · obtain ⟨y, hy, σ0, rfl⟩ : ∃ y hy σ0, σ = ISub.cons y hy σ0 := ⟨_, _, _, (ISub.cons_tail σ).symm⟩
    rw [sk2_cons, isub_up_dinst _ _ .zero trivial, isub_app, isub_fst, dshift_isub_tail, dshift_isub_tail,
      dinst_isub_end _ (.inl rfl), isub_up_dinst _ _ .zero trivial, ISub.tail_cons]
    exact D.sysZ hW hδ σ0 hy (hθ σ0 y hy hh)
  · obtain ⟨y, hy, σ0, rfl⟩ : ∃ y hy σ0, σ = ISub.cons y hy σ0 := ⟨_, _, _, (ISub.cons_tail σ).symm⟩
    rw [sk2_cons, isub_up_dinst _ _ .zero trivial, isub_app, isub_fst, dshift_isub_tail, dshift_isub_tail,
      dinst_isub_end _ (.inl rfl), isub_up_dinst _ _ .zero trivial, ISub.tail_cons]
    have hAA := D.rAA k3 σ0 .zero .zero trivial trivial (I_eq_refl _)
    have z := D.sysZ hW hδ σ0 hy (hθ σ0 y hy hh)
    have b := D.eu0 hW hδ σ0 (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) (.inr rfl)
    have a := D.sysAt hW hδ σ0 hy (x := .zero) (x' := .zero) trivial trivial (I_eq_refl _) hh
    have zb := RE2.trans hW hAA z (RE2.symm hW hAA b)
    exact RE2.trans hW hAA (RE2.symm hW hAA zb) a
end

end

end Model.Whnf
