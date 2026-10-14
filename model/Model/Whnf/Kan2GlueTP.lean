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

theorem tgTube_zero (φ : I) (e u0 : Tm) (σ : ISub k' k) :
    ((tgTube φ e u0).isub σ.up).dinst .zero = (tgA0 φ e u0).isub σ := by
  show Tm.unglue (((φ.subst σ.up.τ)).subst (I.inst0 .zero)) ((e.isub σ.up).dinst .zero)
      ((u0.dshift.isub σ.up).dinst .zero) = Tm.unglue ((φ.subst (I.inst0 .zero)).subst σ.τ) ((e.dinst .zero).isub σ)
      (u0.isub σ)
  rw [I_end_isub φ (.inl rfl), dinst_isub_end _ (.inl rfl), dshift_isub_up_dinst]

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

end

end

end Model.Whnf
