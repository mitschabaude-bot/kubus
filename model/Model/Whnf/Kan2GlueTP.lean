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

theorem subst_up_inst0_dinst {X : Tm} {n : ℕ} (hX : X.closedB n (k + 2) = true) {r s : I} (hr : r.Scoped k)
    (hs : s.Scoped k) :
    (X.subst Tm.var (I.up (I.inst0 r))).dinst s = X.isub (ISub.cons s hs (ISub.cons r hr (ISub.id k))) := by
  simp only [Tm.dinst, Tm.dsubst, Tm.isub, subst_subst]
  refine closed_subst_eq X n (k + 2) _ _ _ _ hX (fun x _ => rfl) fun i hi => ?_
  rcases i with _ | _ | i
  · rfl
  · show ((I.inst0 r 0).shift).subst (I.inst0 s) = r
    rw [I_shift_inst0]; rfl
  · show (((I.inst0 r (i + 1)).shift).subst (I.inst0 s)) = (ISub.id k).τ i
    rw [I_shift_inst0]; simp [ISub.id, I.inst0, show i < k by omega]

variable (hW : WfSig S)
include hW

/-- A heterogeneous composition whose face holds is stably its tube's end. -/
theorem stable_compFace {C u u0 X : Tm} {ψ : I} (h : I.Entails .one ψ) (hty : HasTy S k .one [] (Tm.comp C ψ u u0) X) :
    StableE S k X (Tm.comp C ψ u u0) (u.dinst .one) := by
  intro k' σ
  have hσ := HasTy.isubS hW hty σ
  rw [comp_isub] at hσ ⊢
  rw [dinst_isub_end _ (.inr rfl)]
  exact ⟨red_comp_face (ent_subst h σ.τ), minimal_to_spec_eq (comp_face (sigClosed_of_wfSig hW)
    (spec_to_minimal hW hσ) (ent_subst h σ.τ))⟩

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

/-- On `δ`, the transport in the fiber, typed at a restriction. -/
theorem TGD2.t1Ty (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) :
    HasTy S k' .one [] ((tgT1 T ψ u0).isub τ) (T.isub (ISub.cons .one trivial τ)) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have h := HasTy.isubS hW (HasTy.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds D.hδs hδ))
    (minimal_to_spec H.ht1)) τ
  rwa [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial] at h

/-- On `δ`, where `ψ` holds, the transport in the fiber is the start. -/
theorem TGD2.t1E (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) (hh : (ival (idEnv k') (ψ.subst τ.τ)).holds) :
    RE2 S k' (T.isub (ISub.cons .one trivial τ)) (u0.isub τ) ((tgT1 T ψ u0).isub τ) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hTT := D.rTT k' _ (D.faceL hW hδ (ISub.cons .one trivial τ))
  have x := RE2.reflL hW hTT (D.u0At hW hδ τ .one trivial (.inl hh))
  have hty := D.t1Ty hW hδ τ
  refine RE2.expandR hW hTT (RE2.typed x).1 hty ?_ x
  unfold tgT1 at hty ⊢
  rw [transp_isub] at hty ⊢
  exact stable_transpFace hW (entails_of_holds (I.scoped_subst H.hψ τ.sc) hh) hty

/-- On `δ`, the transport filler in the fiber at the end of its line is near the transport. -/
theorem TGD2.tf1 (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (τ : ISub k' k) :
    RE2 S k' (T.isub (ISub.cons .one trivial τ)) ((Tm.transpFill T ψ u0).isub (ISub.cons .one trivial τ))
      ((tgT1 T ψ u0).isub τ) := by
  obtain ⟨-, hTc, -, -⟩ := D.closedL hW
  have hTT := D.rTT k' _ (D.faceL hW hδ (ISub.cons .one trivial τ))
  have x := RE2.reflL hW hTT (D.tfAt hW hδ (ISub.cons .one trivial τ) (ISub.cons .one trivial τ) rfl (I_eq_refl _))
  refine RE2_near hW hTT x ?_ (D.t1Ty hW hδ τ)
  rw [transpFill_isub_cons]
  unfold tgT1
  rw [transp_isub, ← ISub.cons_var0_up_tail τ]
  exact .transp (near_cons T _ _ (I_eq_and_one_l (.var 0))) (FEq.of_eq (ieq_or_negone _)) (TmNear.refl _)


/-- On `δ`, the body of `ω` at the start of the path is the equivalence applied to the transport. -/
theorem TGD2.w0 (hδ : (ival (idEnv k) δ).holds) :
    RE2 S k (A.dinst .one) ((tgBody A φ T e ψ u0).dinst .zero) (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) := by
  obtain ⟨hAc, hTc, hec, -⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l, hG⟩ := D.hG
  have hδe := entails_of_holds D.hδs hδ
  have hAA := D.rAA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
  -- typings
  have hb := HasTy.isubS hW (HasTy.restrict (Φ' := .one) trivial (ent_shift (ent_cof_one hW hδe))
    (minimal_to_spec H.hbody)) (ISub.cons .zero trivial (ISub.id k))
  rw [dshift_isub_cons, isub_id_of_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))),
    isub_cons_id_of_closed (closed_ty H.hbody)] at hb
  obtain ⟨-, -, he1⟩ := glue_fiber_ty hW hG (ISub.cons .one trivial (ISub.id k)) (D.faceL hW hδ _)
  have ht1 := D.t1Ty hW hδ (ISub.id k)
  rw [isub_id_of_closed (closed_ty (H.ht1))] at ht1
  have hx := minimal_to_spec (app_fst_equiv (spec_to_minimal hW he1) (spec_to_minimal hW ht1))
  rw [isub_cons_id_of_closed hec, isub_cons_id_of_closed hAc] at hx
  rw [isub_cons_id_of_closed hAc] at hAA
  -- the composition reduces to the end of its tube
  rw [tgBody_dinst] at hb ⊢
  have hface : I.Entails .one (I.or ψ (.or (.neg .zero) .zero)) :=
    ent_trans (show I.Entails .one (I.neg .zero) by decide) (ent_trans (ent_or_left _ _) (ent_or_right _ _))
  refine RE2.expandL hW hAA hb hx (stable_compFace hW hface hb) ?_
  rw [subst_up_inst0_dinst (closed_ty H.hsys) (r := .zero) (s := .one) trivial trivial]
  have hχ : I.Entails .one (I.or (ψ.subst (ISub.id k).τ) (.or (.neg .zero) .zero)) := by
    rw [I_subst_id H.hψ]; exact hface
  have hsp := tgSys_ty hW H hδe (ISub.id k) (y := .zero) trivial hχ (x := .one) trivial
  rw [isub_cons_id_of_closed hAc] at hsp
  unfold tgSys at hsp ⊢
  rw [tgSys'_isub] at hsp ⊢
  rw [← isub_cons_id_of_closed hAc .one trivial, ← isub_cons_id_of_closed hec .one trivial,
    ← isub_id_of_closed (closed_ty H.ht1)] at hx ⊢
  rw [← isub_cons_id_of_closed hAc .one trivial] at hAA hsp
  have rs : ∀ {k4 : ℕ} (σ2 : ISub k4 k) (X : Tm),
      (X.isub (ISub.cons .one trivial (ISub.id k))).isub σ2 = X.isub (ISub.cons .one trivial σ2) :=
    fun σ2 X => by rw [Tm.isub_isub, ISub.cons_comp, ISub.id_comp]; rfl
  refine RE2_split_l hW (I.scoped_subst H.hψ (ISub.id k).sc) ⟨trivial, trivial⟩ hχ hAA hsp hx (fun k4 σ2 h => ?_)
    (fun k4 σ2 h => ?_)
  · simp only [isub_app, isub_fst, rs, Tm.isub_isub, ISub.id_comp]
    have hh : (ival (idEnv k4) (ψ.subst σ2.τ)).holds := by
      rw [holds_iff_entails (I.scoped_subst H.hψ σ2.sc)]
      rw [I_subst_id H.hψ] at h; exact h
    exact RE2_equiv_app hW (D.rEL k4 _ (D.faceL hW hδ _)) (D.t1E hW hδ σ2 hh)
  · have hσ := HasTy.isubS hW hsp σ2
    have hin := HasTy.eqR (EqTm.splitR h hσ)
    have hAA2 := D.rAA k4 σ2 .one .one trivial trivial (I_eq_refl _)
    simp only [← isub_eq_subst, isub_app, isub_fst, rs, Tm.isub_isub, ISub.id_comp, I.subst] at hin ⊢
    refine RE2_split_l hW trivial trivial (by simpa only [I.subst] using h) hAA2 hin
      (by simpa only [isub_app, isub_fst, rs, Tm.isub_isub, ISub.id_comp] using HasTy.isubS hW hx σ2)
      (fun k5 σ3 _ => ?_) (fun k5 σ3 h3 => ?_)
    · simp only [← isub_eq_subst, isub_app, isub_fst, Tm.isub_isub, ISub.cons_comp, I.subst, ISub.id_comp]
      exact RE2_equiv_app hW (D.rEL k5 _ (D.faceL hW hδ _)) (D.tf1 hW hδ (σ2.comp σ3))
    · exact absurd h3 (by simp only [I.subst]; decide)


/-- The filler of the bases at the end of its line is the composition. -/
theorem TGD2.fill1 {k' : ℕ} (τ : ISub k' k) :
    RE2 S k' (A.isub (ISub.cons .one trivial τ)) ((Tm.fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).isub (ISub.cons .one trivial τ))
      ((tgA1' A φ e ψ u0).isub τ) := by
  obtain ⟨hAc, -, -, -⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  have hA0 := D.rAA k (ISub.id k) .zero .zero trivial trivial (I_eq_refl _)
  rw [isub_cons_id_of_closed hAc] at hA0
  exact fill_one_pt hW H.hψ D.rAA (fun k3 Θ X' h => D.kAT k3 Θ X' h) (fun k3 Θ X' h => D.kAH k3 Θ X' h)
    (minimal_to_spec H.ha1') (D.hF hW) (fun k5 σ r r' hr hr' he hh => D.tubeL hW σ hr hr' he hh)
    (RE2.reflL hW hA0 (D.a0 hW))
    (fun k5 σ hh => by
      have x := D.tubeL hW σ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _) hh
      rw [tgTube_zero φ e u0]; rwa [tgTube_zero φ e u0] at x) τ

/-- On `δ`, the body of `ω` at the end of the path is the composition in the bases. -/
theorem TGD2.w1 (hδ : (ival (idEnv k) δ).holds) :
    RE2 S k (A.dinst .one) ((tgBody A φ T e ψ u0).dinst .one) (tgA1' A φ e ψ u0) := by
  obtain ⟨hAc, hTc, hec, -⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  have hδe := entails_of_holds D.hδs hδ
  have hAA := D.rAA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
  have hb := HasTy.isubS hW (HasTy.restrict (Φ' := .one) trivial (ent_shift (ent_cof_one hW hδe))
    (minimal_to_spec H.hbody)) (ISub.cons .one trivial (ISub.id k))
  rw [dshift_isub_cons, isub_id_of_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))),
    isub_cons_id_of_closed (closed_ty H.hbody)] at hb
  have hx := minimal_to_spec H.ha1'
  rw [isub_cons_id_of_closed hAc] at hAA
  rw [tgBody_dinst] at hb ⊢
  have hface : I.Entails .one (I.or ψ (.or (.neg .one) .one)) :=
    ent_trans (ent_refl _) (ent_trans (ent_or_right _ _) (ent_or_right _ _))
  refine RE2.expandL hW hAA hb hx (stable_compFace hW hface hb) ?_
  rw [subst_up_inst0_dinst (closed_ty H.hsys) (r := .one) (s := .one) trivial trivial]
  have hχ : I.Entails .one (I.or (ψ.subst (ISub.id k).τ) (.or (.neg .one) .one)) := by
    rw [I_subst_id H.hψ]; exact hface
  have hsp := tgSys_ty hW H hδe (ISub.id k) (y := .one) trivial hχ (x := .one) trivial
  unfold tgSys at hsp ⊢
  rw [tgSys'_isub] at hsp ⊢
  rw [← isub_id_of_closed (closed_ty H.ha1')] at hx ⊢
  rw [← isub_cons_id_of_closed hAc .one trivial] at hAA hx ⊢
  have rs : ∀ {k4 : ℕ} (σ2 : ISub k4 k) (X : Tm),
      (X.isub (ISub.cons .one trivial (ISub.id k))).isub σ2 = X.isub (ISub.cons .one trivial σ2) :=
    fun σ2 X => by rw [Tm.isub_isub, ISub.cons_comp, ISub.id_comp]; rfl
  refine RE2_split_l hW (I.scoped_subst H.hψ (ISub.id k).sc) ⟨trivial, trivial⟩ hχ hAA hsp
    hx
    (fun k4 σ2 h => ?_) (fun k4 σ2 h => ?_)
  · simp only [isub_app, isub_fst, rs, Tm.isub_isub, ISub.id_comp]
    have hh : (ival (idEnv k4) (ψ.subst σ2.τ)).holds := by
      rw [holds_iff_entails (I.scoped_subst H.hψ σ2.sc)]
      rw [I_subst_id H.hψ] at h; exact h
    have hAA2 := D.rAA k4 σ2 .one .one trivial trivial (I_eq_refl _)
    have t := D.tubeE hW hδ σ2 (r := .one) trivial hh
    rw [isub_up_dinst _ _ .one trivial] at t
    have hc := HasTy.isubS hW (minimal_to_spec H.ha1') σ2
    rw [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial] at hc
    have st := stable_compFace hW (entails_of_holds (I.scoped_subst H.hψ σ2.sc) hh)
      (by unfold tgA1' at hc; rw [comp_isub] at hc; exact hc)
    unfold tgA1'
    rw [comp_isub]
    rw [isub_up_dinst _ _ .one trivial] at st
    exact RE2.expandR hW hAA2 (RE2.typed t).2.1 (by unfold tgA1' at hc; rwa [comp_isub] at hc) st
      (RE2.symm hW hAA2 t)
  · have hσ := HasTy.isubS hW hsp σ2
    have hin := HasTy.eqR (EqTm.splitR h hσ)
    have hAA2 := D.rAA k4 σ2 .one .one trivial trivial (I_eq_refl _)
    simp only [← isub_eq_subst, isub_app, isub_fst, rs, Tm.isub_isub, ISub.id_comp] at hin ⊢
    refine RE2_split_l hW trivial trivial (by simpa only [I.subst] using h) hAA2 hin
      (by have := HasTy.isubS hW (minimal_to_spec H.ha1') σ2
          rwa [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial] at this)
      (fun k5 σ3 h3 => ?_) (fun k5 σ3 _ => ?_)
    · exact absurd h3 (by simp only [I.subst]; decide)
    · simp only [← isub_eq_subst, isub_app, isub_fst, Tm.isub_isub, ISub.cons_comp, I.subst, ISub.id_comp]
      exact D.fill1 hW (σ2.comp σ3)


/-- On `δ`, the bodies of `ω` at near points of restrictions. -/
theorem TGD2.bodyAt (hδ : (ival (idEnv k) δ).holds) {k' : ℕ} (σ : ISub k' k) {r r' : I} (hr : r.Scoped k')
    (hr' : r'.Scoped k') (he : I.Eq r r') :
    RE2 S k' ((A.dinst .one).isub σ) (((tgBody A φ T e ψ u0).isub σ.up).dinst r)
      (((tgBody A' φ' T' e' ψ' u0').isub σ.up).dinst r') := by
  have hb := D.body hW hδ
  have x := RE2.isub hW hb (ISub.cons r hr σ)
  have hR := HasTy.isubS hW (RE2.typed hb).2.1 (ISub.cons r' hr' σ)
  rw [dshift_isub_cons] at x hR
  have hAA : RT2 S k' ((A.dinst .one).isub σ) ((A.dinst .one).isub σ) := by
    rw [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial]
    exact D.rAA k' σ .one .one trivial trivial (I_eq_refl _)
  rw [isub_up_dinst _ _ _ hr, isub_up_dinst _ _ _ hr']
  exact RE2_near hW hAA x (near_cons _ hr hr' he) hR

/-- On `δ`, the paths `ω`. -/
theorem TGD2.omega (hδ : (ival (idEnv k) δ).holds) :
    RE2 S k (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0))
      (tgOmega A φ T e ψ u0) (tgOmega A' φ' T' e' ψ' u0') := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hentδ : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hω := HasTy.restrict (Φ' := .one) trivial hentδ (minimal_to_spec H.hω)
  obtain ⟨lp, hpT⟩ := ty_of_tyEq hW (isTyK_of_ty hW hω) (TyEq.refl _) (fun l h => by cases h)
  have hb := D.body hW hδ
  have hbc := closed_ty H.hbody
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hbc' := closed_ty H'.hbody
  have hAc : (A.dinst .one).closedB 0 k = true := closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))
  have hpt : ∀ (d : I) (hd : d.Scoped k), RE2 S k (A.dinst .one) ((tgBody A φ T e ψ u0).dinst d)
      ((tgBody A' φ' T' e' ψ' u0').dinst d) := fun d hd => by
    have x := D.bodyAt hW hδ (ISub.id k) hd hd (I_eq_refl _)
    rwa [isub_id_of_closed hAc, isub_up_id_of_closed hbc, isub_up_id_of_closed hbc'] at x
  have hw0 := D.w0 hW hδ
  have hw1 := D.w1 hW hδ
  unfold Tm.pathC at hω hpT ⊢
  have hωR : HasTy S k .one [] (tgOmega A' φ' T' e' ψ' u0') (.path (A.dinst .one).dshift
      (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0)) := by
    refine HasTy.plam hpT (RE2.typed hb).2.1 ?_ ?_ <;> rw [dshift_dinst]
    · exact (RE2.typed (hpt .zero trivial)).2.2.symm.trans (RE2.typed hw0).2.2
    · exact (RE2.typed (hpt .one trivial)).2.2.symm.trans (RE2.typed hw1).2.2
  have hpb : ∀ {k' : ℕ} (σ : ISub k' k) {r : I} (hr : r.Scoped k') {X : Tm} (hX : HasTy S k .one [] X
      (.path (A.dinst .one).dshift (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0))),
      HasTy S k' .one [] (.papp (X.isub σ) r) ((A.dinst .one).isub σ) := fun σ r hr X hX => by
    have h1 := HasTy.isubS hW hX σ
    rw [isub_path] at h1
    have := HasTy.papp h1 hr
    rwa [isub_up_dinst _ _ _ hr, dshift_isub_cons] at this
  refine RE2_path_intro hW hpT ⟨hω, hωR, EqTm.plam hpT hω hωR (RE2.typed hb).2.2⟩
    (fun k' σ r r' hr hr' he => ?_) ?_ ?_
  · rw [isub_up_dinst _ _ _ hr, dshift_isub_cons]
    have hAA : RT2 S k' ((A.dinst .one).isub σ) ((A.dinst .one).isub σ) := by
      rw [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial]
      exact D.rAA k' σ .one .one trivial trivial (I_eq_refl _)
    have hL := hpb σ hr hω
    have hR := hpb σ hr' hωR
    unfold tgOmega at hL hR ⊢
    rw [isub_plam] at hL hR ⊢
    refine RE2.expandL hW hAA hL hR (stable_pathBeta hW hL) ?_
    exact RE2.expandR hW hAA (RE2.typed (D.bodyAt hW hδ σ hr hr' he)).1 hR (stable_pathBeta hW hR)
      (D.bodyAt hW hδ σ hr hr' he)
  · have hL := hpb (ISub.id k) (r := .zero) trivial hω
    rw [isub_id_of_closed hAc, isub_id_of_closed (closed_of_ty hW hω)] at hL
    rw [dshift_dinst]
    have hAA := (D.rAA k (ISub.id k) .one .one trivial trivial (I_eq_refl _))
    rw [isub_cons_id_of_closed (closed_ty H.hA)] at hAA
    unfold tgOmega at hL ⊢
    exact RE2.expandL hW hAA hL (RE2.typed hw0).2.1 (stable_pathBeta hW hL) hw0
  · have hL := hpb (ISub.id k) (r := .one) trivial hω
    rw [isub_id_of_closed hAc, isub_id_of_closed (closed_of_ty hW hω)] at hL
    rw [dshift_dinst]
    have hAA := (D.rAA k (ISub.id k) .one .one trivial trivial (I_eq_refl _))
    rw [isub_cons_id_of_closed (closed_ty H.hA)] at hAA
    unfold tgOmega at hL ⊢
    exact RE2.expandL hW hAA hL (RE2.typed hw1).2.1 (stable_pathBeta hW hL) hw1

end

end

end Model.Whnf
