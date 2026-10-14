import Model.Whnf.Kan2GlueTP

/-!
# Binary transport in Glue types: the fibres of the equivalence at the end of the line

Where `φ(1)` holds, the fibres `tgFib` of `e(1)` over the compositions `a1'` are related, contractible
(`TGD2.c`) and have compositions (`TGD2.fibK`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' : ℕ}

theorem dinst1_isub (X : Tm) (σ : ISub k' k) : (X.dinst .one).isub σ = X.isub (ISub.cons .one trivial σ) := by
  rw [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial]

theorem I_inst1_isub (φ : I) (σ : ISub k' k) :
    (φ.subst (I.inst0 .one)).subst σ.τ = φ.subst (ISub.cons .one trivial σ).τ := by
  rw [I_subst_subst]; congr 1; funext i; rcases i with _ | i <;> rfl

theorem fibB_isub_inst (X f y a : Tm) (σ : ISub k' k) :
    ((Tm.pathC X.shift (.app f.shift (.var 0)) y.shift).isub σ).inst a =
      Tm.pathC (X.isub σ) (.app (f.isub σ) a) (y.isub σ) := by
  rw [pathC_isub, isub_shift, isub_shift]
  have eapp : (Tm.app f.shift (.var 0)).isub σ = .app (f.isub σ).shift (.var 0) := by
    show Tm.app (f.shift.isub σ) (Tm.var 0) = _; rw [isub_shift]
  rw [eapp, P_inst]

theorem isub_cons_var0_wk {X : Tm} {n : ℕ} (h : X.closedB n (k + 1) = true) :
    X.isub (ISub.cons (.var 0) (show (0 : ℕ) < k + 1 by omega) (ISub.wk k)) = X :=
  closed_subst_id h (fun x _ => rfl) (fun i hi => by
    rcases i with _ | i
    · rfl
    · simp [ISub.cons, ISub.wk, show i < k by omega])

theorem tgBody_isub (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (σ : ISub k' k) :
    (tgBody A φ T e ψ u0).isub σ.up =
      tgBody (A.isub σ.up) (φ.subst σ.up.τ) (T.isub σ.up) (e.isub σ.up) (ψ.subst σ.τ) (u0.isub σ) := by
  have h := (tg_subst_low A φ T e ψ u0 Tm.var σ.τ).2.1
  rw [dupS_var] at h
  exact h

variable (hW : WfSig S)
include hW

theorem pathC_elim2 {F c p X Y : Tm} (h : RE2 S k (Tm.pathC F c p) X Y) {s s' : I} (hs : s.Scoped k)
    (hs' : s'.Scoped k) (he : I.Eq s s') : RE2 S k F (.papp X s) (.papp Y s') := by
  unfold Tm.pathC at h
  have := (RE2_path_elim hW h).1 s s' hs hs' he
  rwa [dshift_dinst] at this

theorem pathC_elim0 {F c p X Y : Tm} (h : RE2 S k (Tm.pathC F c p) X Y) : RE2 S k F (.papp X .zero) c := by
  unfold Tm.pathC at h
  have := (RE2_path_elim hW h).2.1
  rwa [dshift_dinst] at this

theorem HasTy.top {X : Tm} {l : ℕ} (h : HasTy S k .one [] X (.univ l)) : HasTy S k .one [] X (.univ maxLevel) :=
  h.cumulTo (lvl_of_ty hW h) le_rfl

/-- The contraction of a contractible type to a point. -/
theorem RE2_contr {X c c' p p' : Tm} (hc : RE2 S k (Tm.isContr X) c c') (hp : RE2 S k X p p') :
    RE2 S k (Tm.pathC X (.fst c) p) (.app (.snd c) p) (.app (.snd c') p') := by
  unfold Tm.isContr at hc
  have h := (RE2_sigma_elim hW hc).2
  rw [K_inst] at h
  have h2 := RE2_pi_elim hW h hp
  rwa [pathC_var0_inst] at h2

/-- Pairs of related components. -/
theorem RE2_pair_intro {A B a a' b b' : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A B) (.univ l))
    (hp : HasTy S k .one [] (.pair a b) (.sigma A B)) (hp' : HasTy S k .one [] (.pair a' b') (.sigma A B))
    (hLL : RT2 S k (.sigma A B) (.sigma A B)) (ha : RE2 S k A a a') (hb : RE2 S k (B.inst a) b b') :
    RE2 S k (.sigma A B) (.pair a b) (.pair a' b') := by
  have hI := RT2_sigma_inv hW hLL
  have hAA := hI.1
  have hfL := HasTy.fst hp
  have hfR := HasTy.fst hp'
  have h1 : RE2 S k A (.fst (.pair a b)) (.fst (.pair a' b')) :=
    RE2.expand2 hW hAA hfL hfR (stable_fstBeta hW hfL) (stable_fstBeta hW hfR) ha
  have haf : RE2 S k A a (.fst (.pair a b)) :=
    RE2.expandR hW hAA (RE2.typed ha).1 hfL (stable_fstBeta hW hfL) (RE2.reflL hW hAA ha)
  have hT := hI.2 _ _ haf
  have hb' := RE2.conv hW hT hb
  have hXX := RT2.refl' hW (RE2.tyCode hW hb) hT
  have hsL := HasTy.snd hp
  have hsR := (HasTy.snd hp').tyConv (TyEq.symm (Comp2_ty_base (hI.2 _ _ h1)).2.2.2.2.2)
  have h2 := RE2.expand2 hW hXX hsL hsR (stable_sndBeta hW hsL) (stable_sndBeta hW hsR) hb'
  exact RE2_sigma_intro hW hsig ⟨hp, hp', EqTm.pair hsig (RE2.typed ha).2.2 (RE2.typed hb).2.2⟩ h1 h2

/-- The systems of the compositions in the fibres, typed at points of restrictions where their face holds. -/
theorem psysTy {A T e u0 : Tm} {φ ψ δ : I} {l : ℕ} (H : TG S k .one [] A φ T e ψ u0 δ l)
    (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds) {k' : ℕ}
    (σ : ISub k' k) (hh : (ival (idEnv k') ((I.or δ ψ).subst σ.τ)).holds) {r : I} (hr : r.Scoped k') :
    HasTy S k' .one [] (.split (δ.subst σ.τ) (.papp ((tgPd A φ T e ψ u0).isub σ) r) (ψ.subst σ.τ)
      (.papp ((tgPpsi A φ e ψ u0).isub σ) r)) ((tgFib A φ T e ψ u0).isub σ) := by
  have hφ1s : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) := ent_cof_one hW (entails_of_holds hφ1s hφ1)
  have hsp := HasTy.isubF hW (show ((cof (cof .one (φ.subst (I.inst0 .one))) (.or δ ψ)).shift).Scoped (k + 1) from
    KubusCore.I.scoped_shift ⟨⟨trivial, hφ1s⟩, H.hδ, H.hψ⟩) (minimal_to_spec H.hpsys) (ISub.cons r hr σ)
  rw [I_shift_cons, dshift_isub_cons, ← isub_up_dinst _ _ _ hr, psys_isub] at hsp
  exact HasTy.restrict (Φ' := .one) trivial (ent_and_intro (ent_subst hent1 σ.τ)
    (entails_of_holds (I.scoped_subst (show (I.or δ ψ).Scoped k from ⟨H.hδ, H.hψ⟩) σ.sc) hh)) hsp

section
variable {A T e A' T' e' u0 u0' : Tm} {φ φ' ψ ψ' δ δ' : I}
  (D : TGD2 S k A φ T e A' φ' T' e' ψ ψ' u0 u0' δ δ')
  (hφ1 : (ival (idEnv k) (φ.subst (I.inst0 .one))).holds)
include D hφ1

/-- Where `φ(1)` holds, the face holds at the end of the line, under every restriction. -/
theorem TGD2.φ1At (σ : ISub k' k) : (ival (idEnv k') (φ.subst (ISub.cons .one trivial σ).τ)).holds := by
  obtain ⟨-, -, -, hφs⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  have hs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have := holds_isub hW hs hφ1 σ
  rwa [I_inst1_isub] at this

theorem TGD2.φ1R : (ival (idEnv k) (φ'.subst (I.inst0 .one))).holds := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  rw [holds_iff_entails (H'.hφr (r := .one) trivial)]
  exact ent_trans (entails_of_holds (H.hφr (r := .one) trivial) hφ1) (ent_subst D.f12 _)

/-- The fibres at the end of the line. -/
theorem TGD2.rT1 (σ : ISub k' k) : RT2 S k' ((T.dinst .one).isub σ) ((T'.dinst .one).isub σ) := by
  rw [dinst1_isub, dinst1_isub]; exact D.rT k' _ (D.φ1At hW hφ1 σ)

/-- The equivalences at the end of the line. -/
theorem TGD2.e1 (σ : ISub k' k) :
    RE2 S k' (Tm.equiv ((T.dinst .one).isub σ) ((A.dinst .one).isub σ)) ((e.dinst .one).isub σ)
      ((e'.dinst .one).isub σ) := by
  rw [dinst1_isub, dinst1_isub, dinst1_isub, dinst1_isub]; exact D.rE k' _ (D.φ1At hW hφ1 σ)

theorem TGD2.hT1 : ∃ l, HasTy S k .one [] (T.dinst .one) (.univ l) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  exact ⟨l1, minimal_to_spec (H.hTr (r := .one) trivial (X := .one) trivial (ent_refl _)
    (entails_of_holds hφs hφ1))⟩

/-- The fibres of the equivalences over the compositions in the bases are related types. -/
theorem TGD2.rFib : RT2 S k (tgFib A φ T e ψ u0) (tgFib A' φ' T' e' ψ' u0') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφs' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) := ent_cof_one hW (entails_of_holds hφs hφ1)
  have hent1' : I.Entails .one (cof .one (φ'.subst (I.inst0 .one))) :=
    ent_cof_one hW (entails_of_holds hφs' (D.φ1R hW hφ1))
  have hfib := HasTy.top hW (HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hfib))
  have hfib' := HasTy.top hW (HasTy.restrict (Φ' := .one) trivial hent1' (minimal_to_spec H'.hfib))
  obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
  have hA1 := minimal_to_spec (H.hAr (r := .one) trivial)
  have rT := D.rT1 hW hφ1 (ISub.id k)
  have he1 := D.e1 hW hφ1 (ISub.id k)
  have hAc := closed_of_ty hW hA1
  have hTc := closed_of_ty hW hT1
  have hec := closed_ty (H.her (r := .one) trivial (X := cof .one (φ.subst (I.inst0 .one))) ⟨trivial, hφs⟩
    (ent_and_left _ _) (ent_and_right _ _))
  have hec' := closed_ty (H'.her (r := .one) trivial (X := cof .one (φ'.subst (I.inst0 .one))) ⟨trivial, hφs'⟩
    (ent_and_left _ _) (ent_and_right _ _))
  have hTc' := closed_ty (H'.hTr (r := .one) trivial (X := .one) trivial (ent_refl _)
    (entails_of_holds hφs' (D.φ1R hW hφ1)))
  rw [isub_id_of_closed hTc, isub_id_of_closed hTc'] at rT
  rw [isub_id_of_closed hTc, isub_id_of_closed hAc, isub_id_of_closed hec, isub_id_of_closed hec'] at he1
  have rA : RT2 S k (A.dinst .one) (A'.dinst .one) := by
    have := D.rA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed (D.closedL hW).1, isub_cons_id_of_closed (D.closedR hW).1] at this
  have eT := tyEq_top hW hT1 (Comp2_ty_base rT).2.2.2.2.2
  have eA := tyEq_top hW hA1 (Comp2_ty_base rA).2.2.2.2.2
  have ee := (RE2.typed he1).2.2
  unfold Tm.equiv at ee
  have he := fiber_congrS hW eT eA (EqTm.fst ee) (RE2.typed (D.a1' hW)).2.2
  rw [tgFib_eq] at hfib hfib' ⊢
  rw [tgFib_eq]
  refine RT2_sigma_intro hW hfib hfib' he (fun k' σ => D.rT1 hW hφ1 σ) fun k' σ a a' ha => ?_
  rw [fibB_isub_inst, fibB_isub_inst]
  have eσ := D.e1 hW hφ1 σ
  have rAσ : ∀ {k3} (τ : ISub k3 k), RT2 S k3 ((A.dinst .one).isub τ) ((A'.dinst .one).isub τ) := fun τ => by
    rw [dinst1_isub, dinst1_isub]; exact D.rA _ τ .one .one trivial trivial (I_eq_refl _)
  have happ : RE2 S k' ((A.dinst .one).isub σ) (.app (.fst ((e.dinst .one).isub σ)) a)
      (.app (.fst ((e'.dinst .one).isub σ)) a') := by
    rw [dinst1_isub, dinst1_isub, dinst1_isub]
    rw [dinst1_isub] at ha
    exact D.eApp hW σ (r := .one) (r' := .one) trivial trivial (I_eq_refl _) (D.φ1At hW hφ1 σ) ha
  have ha1 := RE2.isub hW (D.a1' hW) σ
  have hAσ := HasTy.isubS hW hA1 σ
  have hAσ' := HasTy.isubS hW (minimal_to_spec (H'.hAr (r := .one) trivial)) σ
  have hp := HasTy.top hW (minimal_to_spec (pathC_typed hS (spec_to_minimal hW hAσ)
    (spec_to_minimal hW (RE2.typed happ).1) (spec_to_minimal hW (RE2.typed ha1).1)))
  have eAσ := tyEq_top hW hAσ (Comp2_ty_base (rAσ σ)).2.2.2.2.2
  have hp' := HasTy.top hW (minimal_to_spec (pathC_typed hS (spec_to_minimal hW hAσ')
    (spec_to_minimal hW ((RE2.typed happ).2.1.conv eAσ)) (spec_to_minimal hW ((RE2.typed ha1).2.1.conv eAσ))))
  have hpe := pathC_congrS hW eAσ (RE2.typed happ).2.2 (RE2.typed ha1).2.2
  unfold Tm.pathC at hp hp' hpe ⊢
  refine RT2_path_intro hW hp hp' hpe (fun k3 σ3 => ?_) (fun k3 σ3 r r' hr hr' he => ?_) ?_ ?_
  · rw [isub_dshift, isub_dshift, Tm.isub_isub, Tm.isub_isub]
    have x := RT2.isub hW (tyCode_of_univ hW (HasTy.isubS hW hA1 _)) (rAσ (σ.comp σ3)) (ISub.wk k3)
    rwa [isub_wk_of_closed (closed_of_ty hW (HasTy.isubS hW hA1 (σ.comp σ3))),
      isub_wk_of_closed (closed_of_ty hW (HasTy.isubS hW (minimal_to_spec (H'.hAr (r := .one) trivial)) (σ.comp σ3)))]
      at x
  · rw [isub_dshift, isub_dshift, dshift_dinst, dshift_dinst, Tm.isub_isub, Tm.isub_isub]
    exact rAσ (σ.comp σ3)
  · rw [dshift_dinst]; exact happ
  · rw [dshift_dinst]; exact ha1


/-- The equivalences at the end of the line, unrestricted. -/
theorem TGD2.e1id : RE2 S k (Tm.equiv (T.dinst .one) (A.dinst .one)) (e.dinst .one) (e'.dinst .one) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφs' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have hec := closed_ty (H.her (r := .one) trivial (X := cof .one (φ.subst (I.inst0 .one))) ⟨trivial, hφs⟩
    (ent_and_left _ _) (ent_and_right _ _))
  have hec' := closed_ty (H'.her (r := .one) trivial (X := cof .one (φ'.subst (I.inst0 .one))) ⟨trivial, hφs'⟩
    (ent_and_left _ _) (ent_and_right _ _))
  obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
  have he1 := D.e1 hW hφ1 (ISub.id k)
  rwa [isub_id_of_closed (closed_of_ty hW hT1),
    isub_id_of_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))), isub_id_of_closed hec,
    isub_id_of_closed hec'] at he1

/-- The fibres are contractible. -/
theorem TGD2.c : RE2 S k (Tm.isContr (tgFib A φ T e ψ u0)) (tgC A φ e ψ u0) (tgC A' φ' e' ψ' u0') := by
  have he1 := D.e1id hW hφ1
  unfold Tm.equiv at he1
  have h2 := (RE2_sigma_elim hW he1).2
  rw [isEquiv_inst, isEquiv_eq] at h2
  have h3 := RE2_pi_elim hW h2 (D.a1' hW)
  rwa [isContr_fiber_inst] at h3

/-- The paths in the fibres, typed. -/
theorem TGD2.fibPath (ρ : ISub k' k) {b : Tm} (hb : RE2 S k' ((T.dinst .one).isub ρ) b b) :
    ∃ l, HasTy S k' .one [] (Tm.pathC ((A.dinst .one).isub ρ) (.app (.fst ((e.dinst .one).isub ρ)) b)
      ((tgA1' A φ e ψ u0).isub ρ)) (.univ l) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have happ : RE2 S k' ((A.dinst .one).isub ρ) (.app (.fst ((e.dinst .one).isub ρ)) b)
      (.app (.fst ((e'.dinst .one).isub ρ)) b) := by
    rw [dinst1_isub, dinst1_isub, dinst1_isub]
    rw [dinst1_isub] at hb
    exact D.eApp hW ρ (r := .one) (r' := .one) trivial trivial (I_eq_refl _) (D.φ1At hW hφ1 ρ) hb
  exact ⟨l1, minimal_to_spec (pathC_typed (sigClosed_of_wfSig hW)
    (spec_to_minimal hW (HasTy.isubS hW (minimal_to_spec (H.hAr (r := .one) trivial)) ρ))
    (spec_to_minimal hW (RE2.typed happ).1) (spec_to_minimal hW (RE2.typed (RE2.isub hW (D.a1' hW) ρ)).1))⟩

/-- The fibres have compositions. -/
theorem TGD2.fibK : KanH2 S k (tgFib A φ T e ψ u0) (tgFib A' φ' T' e' ψ' u0') := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hent1 : I.Entails .one (cof .one (φ.subst (I.inst0 .one))) := ent_cof_one hW (entails_of_holds hφs hφ1)
  have hfib := HasTy.restrict (Φ' := .one) trivial hent1 (minimal_to_spec H.hfib)
  have rF := D.rFib hW hφ1
  have KH : ∀ {k1} (ρ : ISub k1 k), KHRel S k1 ((A.dinst .one).isub ρ) := fun ρ k3 σ X X' h h' =>
    D.kAR k3 (ISub.cons .one trivial (ρ.comp σ)) X X' (by rwa [Tm.isub_isub, dinst1_isub] at h) h'
  have KT : ∀ {k1} (ρ : ISub k1 k), KTRel S k1 ((A.dinst .one).isub ρ) := fun ρ k3 Θ X X' h h' =>
    D.kATR k3 (ISub.cons .one trivial (ρ.comp Θ)) X X' (by rwa [Tm.isub_isub, dinst1_isub] at h) h'
  rw [tgFib_eq] at hfib rF ⊢
  refine kanH2_sigma hW rF ⟨redW_self rfl, TyEq.refl _⟩ hfib (fun k1 ρ1 A1 B1 h1 k2 ρ2 X X' hX hXX' => ?_)
    (fun k1 ρ1 A1 B1 h1 b hb k2 ρ2 X X' hX hXX' => ?_) (fun k1 ρ1 A1 B1 h1 b hb k2 ρ2 X X' hX hXX' => ?_) <;>
  · rw [isub_sigma] at h1
    obtain ⟨rfl, rfl⟩ : _ = A1 ∧ _ = B1 := by
      have := RedW.unique (redW_self rfl) h1.1; injection this; constructor <;> assumption
    first
    | (rw [Tm.isub_isub, dinst1_isub] at hX
       exact D.kTR k2 _ (D.φ1At hW hφ1 _) X X' hX hXX')
    | (rw [fibB_isub_inst] at hX
       obtain ⟨lp, hp⟩ := D.fibPath hW hφ1 ρ1 hb
       first
       | exact khRel_pathC hW hp (KH ρ1) k2 ρ2 X X' hX hXX'
       | exact ktRel_pathC hW hp (KH ρ1) (KT ρ1) k2 ρ2 X X' hX hXX')


/-- The fibres, typed. -/
theorem TGD2.hfib : HasTy S k .one [] (tgFib A φ T e ψ u0) (.univ maxLevel) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  exact HasTy.top hW (HasTy.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds hφs hφ1))
    (minimal_to_spec H.hfib))

/-- A term of the right fibre is one of the left fibre. -/
theorem TGD2.fibConv {p : Tm} (h : HasTy S k .one [] p (tgFib A' φ' T' e' ψ' u0')) :
    HasTy S k .one [] p (tgFib A φ T e ψ u0) :=
  h.tyConv (TyEq.symm (Comp2_ty_base (D.rFib hW hφ1)).2.2.2.2.2)

/-- On `δ`, the pairs `(t1', ω)` in the fibres. -/
theorem TGD2.pairD (hδ : (ival (idEnv k) δ).holds) :
    RE2 S k (tgFib A φ T e ψ u0) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))
      (.pair (tgT1 T' ψ' u0') (tgOmega A' φ' T' e' ψ' u0')) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφs' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have hent : I.Entails .one (cof (cof .one (φ.subst (I.inst0 .one))) δ) :=
    ent_and_intro (ent_cof_one hW (entails_of_holds hφs hφ1)) (entails_of_holds D.hδs hδ)
  have hent' : I.Entails .one (cof (cof .one (φ'.subst (I.inst0 .one))) δ') :=
    ent_and_intro (ent_cof_one hW (entails_of_holds hφs' (D.φ1R hW hφ1))) (entails_of_holds D.hδs' (D.hδ' hδ))
  have hp := HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.hpd)
  have hp' := D.fibConv hW hφ1 (HasTy.restrict (Φ' := .one) trivial hent' (minimal_to_spec H'.hpd))
  have hfib := D.hfib hW hφ1
  have hLL := RT2.refl hW (tyCode_of_univ hW hfib) (D.rFib hW hφ1)
  rw [tgFib_eq] at hfib hp hp' hLL ⊢
  exact RE2_pair_intro hW hfib hp hp' hLL (D.t1' hW hδ) (by rw [P_inst]; exact D.omega hW hδ)

/-- On `δ`, the contractions to `(t1', ω)`. -/
theorem TGD2.Pd (hδ : (ival (idEnv k) δ).holds) :
    RE2 S k (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)))
      (tgPd A φ T e ψ u0) (tgPd A' φ' T' e' ψ' u0') :=
  RE2_contr hW (D.c hW hφ1) (D.pairD hW hφ1 hδ)


section
variable (hψk : (ival (idEnv k) ψ).holds)
include hψk

/-- On `ψ`, the starts lie in the fibres at the end of the line. -/
theorem TGD2.u0T1 : RE2 S k (T.dinst .one) u0 u0' := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have := D.u0F hW (ISub.id k) .one trivial (.inl (by rw [I_subst_id H.hψ]; exact hψk)) (D.φ1At hW hφ1 (ISub.id k))
  rwa [isub_cons_id_of_closed (D.closedL hW).2.1, isub_id_of_closed (closed_ty H.hu0),
    isub_id_of_closed (closed_ty H'.hu0)] at this

/-- On `ψ`, the composition in the bases is the equivalence applied to the start. -/
theorem TGD2.a1'E : RE2 S k (A.dinst .one) (tgA1' A φ e ψ u0) (.app (.fst (e.dinst .one)) u0) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have x := D.tubeEF hW (ISub.id k) (r := .one) trivial (by rw [I_subst_id H.hψ]; exact hψk) (D.φ1At hW hφ1 (ISub.id k))
  have hAc := (D.closedL hW).1
  rw [isub_cons_id_of_closed hAc, isub_cons_id_of_closed (D.closedL hW).2.2.1, isub_up_id_of_closed (closed_ty H.htube),
    isub_id_of_closed (closed_ty H.hu0)] at x
  have hAA := D.rAA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
  rw [isub_cons_id_of_closed hAc] at hAA
  have hty := minimal_to_spec H.ha1'
  exact RE2.expandL hW hAA hty (RE2.typed x).2.1 (stable_compFace hW (entails_of_holds H.hψ hψk) hty) x

/-- On `ψ`, the constant paths at the compositions in the bases. -/
theorem TGD2.plamP : RE2 S k (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) u0) (tgA1' A φ e ψ u0))
    (.plam (tgA1' A φ e ψ u0).dshift) (.plam (tgA1' A' φ' e' ψ' u0').dshift) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφs' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have hent : I.Entails .one (cof (cof .one (φ.subst (I.inst0 .one))) ψ) :=
    ent_and_intro (ent_cof_one hW (entails_of_holds hφs hφ1)) (entails_of_holds H.hψ hψk)
  have hent' : I.Entails .one (cof (cof .one (φ'.subst (I.inst0 .one))) ψ') :=
    ent_and_intro (ent_cof_one hW (entails_of_holds hφs' (D.φ1R hW hφ1)))
      (ent_trans (entails_of_holds H.hψ hψk) D.p12)
  have hpl := HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.hpl)
  obtain ⟨lp, hpT⟩ := ty_of_tyEq hW (isTyK_of_ty hW hpl) (TyEq.refl _) (fun l h => by cases h)
  have rA : RT2 S k (A.dinst .one) (A'.dinst .one) := by
    have := D.rA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed (D.closedL hW).1, isub_cons_id_of_closed (D.closedR hW).1] at this
  have hA1 := minimal_to_spec (H.hAr (r := .one) trivial)
  have hAA := RT2.refl hW (tyCode_of_univ hW hA1) rA
  have happ := RE2_equiv_app hW (D.e1id hW hφ1) (D.u0T1 hW hφ1 hψk)
  have ha1 := D.a1' hW
  have eP := pathC_congrS hW (tyEq_top hW hA1 (Comp2_ty_base rA).2.2.2.2.2) (RE2.typed happ).2.2 (RE2.typed ha1).2.2
  have hpl' := (HasTy.restrict (Φ' := .one) trivial hent' (minimal_to_spec H'.hpl)).tyConv
    (TyEq.symm (.inr ⟨_, eP⟩))
  have hpb : ∀ {k' : ℕ} (σ : ISub k' k) {r : I} (hr : r.Scoped k') {X : Tm} (hX : HasTy S k .one [] X
      (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) u0) (tgA1' A φ e ψ u0))),
      HasTy S k' .one [] (.papp (X.isub σ) r) ((A.dinst .one).isub σ) := fun σ r hr X hX => by
    unfold Tm.pathC at hX
    have h1 := HasTy.isubS hW hX σ
    rw [isub_path] at h1
    have := HasTy.papp h1 hr
    rwa [isub_up_dinst _ _ _ hr, dshift_isub_cons] at this
  have hL0 := hpb (ISub.id k) (r := .zero) trivial hpl
  have hL1 := hpb (ISub.id k) (r := .one) trivial hpl
  rw [isub_id_of_closed (closed_of_ty hW hA1), isub_id_of_closed (closed_of_ty hW hpl)] at hL0 hL1
  unfold Tm.pathC at hpl hpl' hpT ⊢
  refine RE2_path_intro hW hpT ⟨hpl, hpl', EqTm.plam hpT hpl hpl' (EqTm.dwk (RE2.typed ha1).2.2)⟩
    (fun k' σ r r' hr hr' he => ?_) ?_ ?_
  · rw [isub_up_dinst _ _ _ hr, dshift_isub_cons]
    have hAAσ : RT2 S k' ((A.dinst .one).isub σ) ((A.dinst .one).isub σ) := RT2.isub hW (tyCode_of_univ hW hA1) hAA σ
    have hL := hpb σ hr hpl
    have hR := hpb σ hr' hpl'
    have x := RE2.isub hW ha1 σ
    rw [isub_plam] at hL hR
    rw [isub_plam, isub_plam]
    refine RE2.expand2 hW hAAσ hL hR (stable_pathBeta hW hL) (stable_pathBeta hW hR) ?_
    rwa [isub_up_dinst _ _ _ hr, isub_up_dinst _ _ _ hr', dshift_isub_cons, dshift_isub_cons]
  · rw [dshift_dinst]
    refine RE2.expandL hW hAA hL0 (RE2.typed happ).1 (stable_pathBeta hW hL0) ?_
    rw [dshift_dinst]; exact D.a1'E hW hφ1 hψk
  · rw [dshift_dinst]
    refine RE2.expandL hW hAA hL1 (RE2.typed ha1).1 (stable_pathBeta hW hL1) ?_
    rw [dshift_dinst]; exact RE2.reflL hW hAA ha1

/-- On `ψ`, the pairs `(u0, ⟨_⟩ a1')` in the fibres. -/
theorem TGD2.pairP : RE2 S k (tgFib A φ T e ψ u0) (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift))
    (.pair u0' (.plam (tgA1' A' φ' e' ψ' u0').dshift)) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφs' : (φ'.subst (I.inst0 .one)).Scoped k := H'.hφr (r := .one) trivial
  have hent : I.Entails .one (cof (cof .one (φ.subst (I.inst0 .one))) ψ) :=
    ent_and_intro (ent_cof_one hW (entails_of_holds hφs hφ1)) (entails_of_holds H.hψ hψk)
  have hent' : I.Entails .one (cof (cof .one (φ'.subst (I.inst0 .one))) ψ') :=
    ent_and_intro (ent_cof_one hW (entails_of_holds hφs' (D.φ1R hW hφ1)))
      (ent_trans (entails_of_holds H.hψ hψk) D.p12)
  have hp := HasTy.restrict (Φ' := .one) trivial hent (minimal_to_spec H.hpψ)
  have hp' := D.fibConv hW hφ1 (HasTy.restrict (Φ' := .one) trivial hent' (minimal_to_spec H'.hpψ))
  have hfib := D.hfib hW hφ1
  have hLL := RT2.refl hW (tyCode_of_univ hW hfib) (D.rFib hW hφ1)
  rw [tgFib_eq] at hfib hp hp' hLL ⊢
  exact RE2_pair_intro hW hfib hp hp' hLL (D.u0T1 hW hφ1 hψk) (by rw [P_inst]; exact D.plamP hW hφ1 hψk)

/-- On `ψ`, the contractions to `(u0, ⟨_⟩ a1')`. -/
theorem TGD2.Ppsi :
    RE2 S k (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift)))
      (tgPpsi A φ e ψ u0) (tgPpsi A' φ' e' ψ' u0') :=
  RE2_contr hW (D.c hW hφ1) (D.pairP hW hφ1 hψk)

end


/-- On `δ` and `ψ`, the bodies of `ω` are the composition in the bases. -/
theorem TGD2.wψ (hδ : (ival (idEnv k) δ).holds) (hψk : (ival (idEnv k) ψ).holds) {r : I} (hr : r.Scoped k) :
    RE2 S k (A.dinst .one) ((tgBody A φ T e ψ u0).dinst r) (tgA1' A φ e ψ u0) := by
  obtain ⟨hAc, hTc, hec, -⟩ := D.closedL hW
  obtain ⟨l1, H⟩ := D.tgL hW
  have hδe := entails_of_holds D.hδs hδ
  have hψe := entails_of_holds H.hψ hψk
  have hAA := D.rAA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
  have hb := HasTy.isubS hW (HasTy.restrict (Φ' := .one) trivial (ent_shift (ent_cof_one hW hδe))
    (minimal_to_spec H.hbody)) (ISub.cons r hr (ISub.id k))
  rw [dshift_isub_cons, isub_id_of_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))),
    isub_cons_id_of_closed (closed_ty H.hbody)] at hb
  have hx := minimal_to_spec H.ha1'
  rw [isub_cons_id_of_closed hAc] at hAA
  rw [tgBody_dinst] at hb ⊢
  have hface : I.Entails .one (I.or ψ (.or (.neg r) r)) := ent_trans hψe (ent_or_left _ _)
  refine RE2.expandL hW hAA hb hx (stable_compFace hW hface hb) ?_
  rw [subst_up_inst0_dinst (closed_ty H.hsys) (r := r) (s := .one) hr trivial]
  have hχ : I.Entails .one (I.or (ψ.subst (ISub.id k).τ) (.or (.neg r) r)) := by
    rw [I_subst_id H.hψ]; exact hface
  have hsp := tgSys_ty hW H hδe (ISub.id k) (y := r) hr hχ (x := .one) trivial
  unfold tgSys at hsp ⊢
  rw [tgSys'_isub] at hsp ⊢
  rw [← isub_id_of_closed (closed_ty H.ha1')] at hx ⊢
  rw [← isub_cons_id_of_closed hAc .one trivial] at hAA hx ⊢
  have rs : ∀ {k4 : ℕ} (σ2 : ISub k4 k) (X : Tm),
      (X.isub (ISub.cons .one trivial (ISub.id k))).isub σ2 = X.isub (ISub.cons .one trivial σ2) :=
    fun σ2 X => by rw [Tm.isub_isub, ISub.cons_comp, ISub.id_comp]; rfl
  refine RE2_split_l hW (I.scoped_subst H.hψ (ISub.id k).sc) (show (I.or (.neg r) r).Scoped k from ⟨hr, hr⟩) hχ hAA hsp
    hx
    (fun k4 σ2 h => ?_) (fun k4 σ2 h => ?_)
  · simp only [isub_app, isub_fst, rs, Tm.isub_isub, ISub.id_comp]
    have hh : (ival (idEnv k4) (ψ.subst σ2.τ)).holds := by
      rw [holds_iff_entails (I.scoped_subst H.hψ σ2.sc)]
      rw [I_subst_id H.hψ] at h; exact h
    exact D.eu0a1 hW hδ σ2 hh
  · have hσ := HasTy.isubS hW hsp σ2
    have hin := HasTy.eqR (EqTm.splitR h hσ)
    have hAA2 := D.rAA k4 σ2 .one .one trivial trivial (I_eq_refl _)
    simp only [← isub_eq_subst, isub_app, isub_fst, rs, Tm.isub_isub, ISub.id_comp] at hin ⊢
    refine RE2_split_l hW (I.scoped_subst (show (I.neg r).Scoped k from hr) σ2.sc) (I.scoped_subst hr σ2.sc) (by simpa only [I.subst] using h) hAA2 hin
      (by have := HasTy.isubS hW (minimal_to_spec H.ha1') σ2
          rwa [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial] at this)
      (fun k5 σ3 h3 => ?_) (fun k5 σ3 _ => ?_)
    · simp only [← isub_eq_subst, isub_app, isub_fst, Tm.isub_isub, ISub.cons_comp, I.subst, ISub.id_comp]
      have hψτ := holds_isub hW H.hψ hψk (σ2.comp σ3)
      have hf := D.faceL hW hδ (ISub.cons .one trivial (σ2.comp σ3))
      have hTT := D.rTT k5 _ hf
      have hAA3 := D.rAA k5 (σ2.comp σ3) .one .one trivial trivial (I_eq_refl _)
      have x := RE2.trans hW hTT (D.tf1 hW hδ (σ2.comp σ3)) (RE2.symm hW hTT (D.t1E hW hδ (σ2.comp σ3) hψτ))
      exact RE2.trans hW hAA3 (RE2_equiv_app hW (D.rEL k5 _ hf) x) (D.eu0a1 hW hδ (σ2.comp σ3) hψτ)
    · simp only [← isub_eq_subst, isub_app, isub_fst, Tm.isub_isub, ISub.cons_comp, I.subst, ISub.id_comp]
      exact D.fill1 hW (σ2.comp σ3)


/-- On `δ` and `ψ`, the bodies of `ω` along the path are the composition in the bases. -/
theorem TGD2.bodyψ (hδ : (ival (idEnv k) δ).holds) (hψk : (ival (idEnv k) ψ).holds) :
    RE2 S (k + 1) (A.dinst .one).dshift (tgBody A φ T e ψ u0) (tgA1' A φ e ψ u0).dshift := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hφ1' : (ival (idEnv (k + 1)) ((φ.subst (ISub.wk k).up.τ).subst (I.inst0 .one))).holds := by
    have := holds_isub hW hφs hφ1 (ISub.wk k)
    rwa [I_end_isub _ (.inr rfl)] at this
  have x := (D.isub hW (ISub.wk k)).wψ hW hφ1' (holds_isub hW D.hδs hδ (ISub.wk k))
    (holds_isub hW H.hψ hψk (ISub.wk k)) (r := .var 0) (show (0 : ℕ) < k + 1 by omega)
  rw [← dinst_isub_end _ (.inr rfl), isub_wk_of_closed (closed_of_ty hW (minimal_to_spec (H.hAr (r := .one) trivial))),
    ← tgA1'_isub, isub_wk_of_closed (closed_ty H.ha1'), ← tgBody_isub, isub_up_dinst _ _ (.var 0) (show (I.var 0).Scoped (k + 1) from show (0 : ℕ) < k + 1 by omega),
    isub_cons_var0_wk (closed_ty H.hbody)] at x
  exact x


/-- On `δ` and `ψ`, `ω` is the constant path at the composition in the bases. -/
theorem TGD2.omegaQ (hδ : (ival (idEnv k) δ).holds) (hψk : (ival (idEnv k) ψ).holds) :
    RE2 S k (Tm.pathC (A.dinst .one) (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0))
      (tgOmega A φ T e ψ u0) (.plam (tgA1' A φ e ψ u0).dshift) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hentδ : I.Entails .one (cof .one δ) := ent_cof_one hW (entails_of_holds D.hδs hδ)
  have hω := HasTy.restrict (Φ' := .one) trivial hentδ (minimal_to_spec H.hω)
  obtain ⟨lp, hpT⟩ := ty_of_tyEq hW (isTyK_of_ty hW hω) (TyEq.refl _) (fun l h => by cases h)
  have hb := D.bodyψ hW hφ1 hδ hψk
  have hw0 := D.w0 hW hδ
  have hw1 := D.w1 hW hδ
  have hb0 := D.wψ hW hφ1 hδ hψk (r := .zero) trivial
  have hA1 := minimal_to_spec (H.hAr (r := .one) trivial)
  have hAc : (A.dinst .one).closedB 0 k = true := closed_of_ty hW hA1
  have hAA := D.rAA k (ISub.id k) .one .one trivial trivial (I_eq_refl _)
  rw [isub_cons_id_of_closed (closed_ty H.hA)] at hAA
  unfold Tm.pathC at hω hpT ⊢
  have hpl : HasTy S k .one [] (.plam (tgA1' A φ e ψ u0).dshift) (.path (A.dinst .one).dshift
      (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0)) := by
    refine HasTy.plam hpT (RE2.typed hb).2.1 ?_ ?_ <;> rw [dshift_dinst, dshift_dinst]
    · exact (RE2.typed hb0).2.2.symm.trans (RE2.typed hw0).2.2
    · exact EqTm.refl (RE2.typed hw1).2.1
  have hpb : ∀ {k' : ℕ} (σ : ISub k' k) {r : I} (hr : r.Scoped k') {X : Tm} (hX : HasTy S k .one [] X
      (.path (A.dinst .one).dshift (.app (.fst (e.dinst .one)) (tgT1 T ψ u0)) (tgA1' A φ e ψ u0))),
      HasTy S k' .one [] (.papp (X.isub σ) r) ((A.dinst .one).isub σ) := fun σ r hr X hX => by
    have h1 := HasTy.isubS hW hX σ
    rw [isub_path] at h1
    have := HasTy.papp h1 hr
    rwa [isub_up_dinst _ _ _ hr, dshift_isub_cons] at this
  refine RE2_path_intro hW hpT ⟨hω, hpl, EqTm.plam hpT hω hpl (RE2.typed hb).2.2⟩
    (fun k' σ r r' hr hr' he => ?_) ?_ ?_
  · rw [isub_up_dinst _ _ _ hr, dshift_isub_cons]
    have hAAσ : RT2 S k' ((A.dinst .one).isub σ) ((A.dinst .one).isub σ) := by
      rw [dinst_isub_end _ (.inr rfl), isub_up_dinst _ _ .one trivial]
      exact D.rAA k' σ .one .one trivial trivial (I_eq_refl _)
    have hL := hpb σ hr hω
    have hR := hpb σ hr' hpl
    have x := RE2.isub hW hb (ISub.cons r hr σ)
    rw [dshift_isub_cons, dshift_isub_cons] at x
    unfold tgOmega at hL ⊢
    rw [isub_plam] at hL hR
    rw [isub_plam, isub_plam]
    refine RE2.expand2 hW hAAσ hL hR (stable_pathBeta hW hL) (stable_pathBeta hW hR) ?_
    rwa [isub_up_dinst _ _ _ hr, isub_up_dinst _ _ _ hr', dshift_isub_cons]
  · have hL := hpb (ISub.id k) (r := .zero) trivial hω
    rw [isub_id_of_closed hAc, isub_id_of_closed (closed_of_ty hW hω)] at hL
    rw [dshift_dinst]
    unfold tgOmega at hL ⊢
    exact RE2.expandL hW hAA hL (RE2.typed hw0).2.1 (stable_pathBeta hW hL) hw0
  · have hL := hpb (ISub.id k) (r := .one) trivial hω
    rw [isub_id_of_closed hAc, isub_id_of_closed (closed_of_ty hW hω)] at hL
    rw [dshift_dinst]
    unfold tgOmega at hL ⊢
    exact RE2.expandL hW hAA hL (RE2.typed hw1).2.1 (stable_pathBeta hW hL) hw1

/-- On `δ` and `ψ`, the two pairs in the left fibre. -/
theorem TGD2.pairPQ (hδ : (ival (idEnv k) δ).holds) (hψk : (ival (idEnv k) ψ).holds) :
    RE2 S k (tgFib A φ T e ψ u0) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))
      (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift)) := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have hφs : (φ.subst (I.inst0 .one)).Scoped k := H.hφr (r := .one) trivial
  have hent1 := ent_cof_one hW (entails_of_holds hφs hφ1)
  have hp := HasTy.restrict (Φ' := .one) trivial (ent_and_intro hent1 (entails_of_holds D.hδs hδ))
    (minimal_to_spec H.hpd)
  have hq := HasTy.restrict (Φ' := .one) trivial (ent_and_intro hent1 (entails_of_holds H.hψ hψk))
    (minimal_to_spec H.hpψ)
  have hfib := D.hfib hW hφ1
  have hLL := RT2.refl hW (tyCode_of_univ hW hfib) (D.rFib hW hφ1)
  obtain ⟨lT, hT1⟩ := D.hT1 hW hφ1
  have hTT := RT2.refl hW (tyCode_of_univ hW hT1) (by
    have := D.rT1 hW hφ1 (ISub.id k)
    rwa [isub_id_of_closed (closed_of_ty hW hT1)] at this)
  have te := D.t1E hW hδ (ISub.id k) (by rw [I_subst_id H.hψ]; exact hψk)
  rw [isub_cons_id_of_closed (D.closedL hW).2.1, isub_id_of_closed (closed_ty H.hu0),
    isub_id_of_closed (closed_ty H.ht1)] at te
  rw [tgFib_eq] at hfib hp hq hLL ⊢
  exact RE2_pair_intro hW hfib hp hq hLL (RE2.symm hW hTT te) (by rw [P_inst]; exact D.omegaQ hW hφ1 hδ hψk)

/-- On `δ` and `ψ`, the contraction to `(t1', ω)` against the right contraction to `(u0, ⟨_⟩ a1')`. -/
theorem TGD2.PdX (hδ : (ival (idEnv k) δ).holds) (hψk : (ival (idEnv k) ψ).holds) :
    RE2 S k (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0)))
      (tgPd A φ T e ψ u0) (tgPpsi A' φ' e' ψ' u0') := by
  have hLL := RT2.refl hW (tyCode_of_univ hW (D.hfib hW hφ1)) (D.rFib hW hφ1)
  exact RE2_contr hW (D.c hW hφ1) (RE2.trans hW hLL (D.pairPQ hW hφ1 hδ hψk) (D.pairP hW hφ1 hψk))

/-- On `δ` and `ψ`, the contraction to `(u0, ⟨_⟩ a1')` against the right contraction to `(t1', ω)`. -/
theorem TGD2.PpsiX (hδ : (ival (idEnv k) δ).holds) (hψk : (ival (idEnv k) ψ).holds) :
    RE2 S k (Tm.pathC (tgFib A φ T e ψ u0) (.fst (tgC A φ e ψ u0)) (.pair u0 (.plam (tgA1' A φ e ψ u0).dshift)))
      (tgPpsi A φ e ψ u0) (tgPd A' φ' T' e' ψ' u0') := by
  have hLL := RT2.refl hW (tyCode_of_univ hW (D.hfib hW hφ1)) (D.rFib hW hφ1)
  exact RE2_contr hW (D.c hW hφ1)
    (RE2.trans hW hLL (RE2.symm hW hLL (D.pairPQ hW hφ1 hδ hψk)) (D.pairD hW hφ1 hδ))


omit hφ1 in
theorem TGD2.δδ : I.Entails δ δ' ∧ I.Entails δ' δ :=
  ⟨ent_trans (ent_trans D.hδ1 (FEq.forall0 ⟨D.f12, D.f21⟩).1) D.hδ2',
    ent_trans (ent_trans D.hδ1' (FEq.forall0 ⟨D.f12, D.f21⟩).2) D.hδ2⟩

/-- `φ(1)` under restrictions, in the form of the restricted data. -/
theorem TGD2.φ1isub (σ : ISub k' k) : (ival (idEnv k') ((φ.subst σ.up.τ).subst (I.inst0 .one))).holds := by
  obtain ⟨l1, H⟩ := D.tgL hW
  have := holds_isub hW (H.hφr (r := .one) trivial) hφ1 σ
  rwa [I_phi1_isub] at this

theorem TGD2.PdPt (τ : ISub k' k) (hδτ : (ival (idEnv k') (δ.subst τ.τ)).holds) {s s' : I} (hs : s.Scoped k')
    (hs' : s'.Scoped k') (he : I.Eq s s') :
    RE2 S k' ((tgFib A φ T e ψ u0).isub τ) (.papp ((tgPd A φ T e ψ u0).isub τ) s)
      (.papp ((tgPd A' φ' T' e' ψ' u0').isub τ) s') := by
  have y := pathC_elim2 hW ((D.isub hW τ).Pd hW (D.φ1isub hW hφ1 τ) hδτ) hs hs' he
  obtain ⟨hF, -, hP, -, -, -⟩ := tg_isub A φ T e ψ u0 δ τ
  obtain ⟨-, -, hP', -, -, -⟩ := tg_isub A' φ' T' e' ψ' u0' δ' τ
  rw [hF, hP, hP']; exact y

theorem TGD2.PpsiPt (τ : ISub k' k) (hψτ : (ival (idEnv k') (ψ.subst τ.τ)).holds) {s s' : I} (hs : s.Scoped k')
    (hs' : s'.Scoped k') (he : I.Eq s s') :
    RE2 S k' ((tgFib A φ T e ψ u0).isub τ) (.papp ((tgPpsi A φ e ψ u0).isub τ) s)
      (.papp ((tgPpsi A' φ' e' ψ' u0').isub τ) s') := by
  have y := pathC_elim2 hW ((D.isub hW τ).Ppsi hW (D.φ1isub hW hφ1 τ) hψτ) hs hs' he
  obtain ⟨hF, -, -, hP, -, -⟩ := tg_isub A φ T e ψ u0 δ τ
  obtain ⟨-, -, -, hP', -, -⟩ := tg_isub A' φ' T' e' ψ' u0' δ' τ
  rw [hF, hP, hP']; exact y

theorem TGD2.PdXPt (τ : ISub k' k) (hδτ : (ival (idEnv k') (δ.subst τ.τ)).holds)
    (hψτ : (ival (idEnv k') (ψ.subst τ.τ)).holds) {s s' : I} (hs : s.Scoped k')
    (hs' : s'.Scoped k') (he : I.Eq s s') :
    RE2 S k' ((tgFib A φ T e ψ u0).isub τ) (.papp ((tgPd A φ T e ψ u0).isub τ) s)
      (.papp ((tgPpsi A' φ' e' ψ' u0').isub τ) s') := by
  have y := pathC_elim2 hW ((D.isub hW τ).PdX hW (D.φ1isub hW hφ1 τ) hδτ hψτ) hs hs' he
  obtain ⟨hF, -, hP, -, -, -⟩ := tg_isub A φ T e ψ u0 δ τ
  obtain ⟨-, -, -, hP', -, -⟩ := tg_isub A' φ' T' e' ψ' u0' δ' τ
  rw [hF, hP, hP']; exact y

theorem TGD2.PpsiXPt (τ : ISub k' k) (hδτ : (ival (idEnv k') (δ.subst τ.τ)).holds)
    (hψτ : (ival (idEnv k') (ψ.subst τ.τ)).holds) {s s' : I} (hs : s.Scoped k')
    (hs' : s'.Scoped k') (he : I.Eq s s') :
    RE2 S k' ((tgFib A φ T e ψ u0).isub τ) (.papp ((tgPpsi A φ e ψ u0).isub τ) s)
      (.papp ((tgPd A' φ' T' e' ψ' u0').isub τ) s') := by
  have y := pathC_elim2 hW ((D.isub hW τ).PpsiX hW (D.φ1isub hW hφ1 τ) hδτ hψτ) hs hs' he
  obtain ⟨hF, -, -, hP, -, -⟩ := tg_isub A φ T e ψ u0 δ τ
  obtain ⟨-, -, hP', -, -, -⟩ := tg_isub A' φ' T' e' ψ' u0' δ' τ
  rw [hF, hP, hP']; exact y

theorem TGD2.Pd0Pt (τ : ISub k' k) (hδτ : (ival (idEnv k') (δ.subst τ.τ)).holds) :
    RE2 S k' ((tgFib A φ T e ψ u0).isub τ) (.papp ((tgPd A φ T e ψ u0).isub τ) .zero)
      ((Tm.fst (tgC A φ e ψ u0)).isub τ) := by
  have y := pathC_elim0 hW ((D.isub hW τ).Pd hW (D.φ1isub hW hφ1 τ) hδτ)
  obtain ⟨hF, hC, hP, -, -, -⟩ := tg_isub A φ T e ψ u0 δ τ
  rw [hF, hP, isub_fst, hC]; exact y

theorem TGD2.Ppsi0Pt (τ : ISub k' k) (hψτ : (ival (idEnv k') (ψ.subst τ.τ)).holds) :
    RE2 S k' ((tgFib A φ T e ψ u0).isub τ) (.papp ((tgPpsi A φ e ψ u0).isub τ) .zero)
      ((Tm.fst (tgC A φ e ψ u0)).isub τ) := by
  have y := pathC_elim0 hW ((D.isub hW τ).Ppsi hW (D.φ1isub hW hφ1 τ) hψτ)
  obtain ⟨hF, hC, -, hP, -, -⟩ := tg_isub A φ T e ψ u0 δ τ
  rw [hF, hP, isub_fst, hC]; exact y


/-- The systems of the compositions in the fibres at near points. -/
theorem TGD2.sysAt2 (σ : ISub k' k) (hh : (ival (idEnv k') ((I.or δ ψ).subst σ.τ)).holds) {r r' : I}
    (hr : r.Scoped k') (hr' : r'.Scoped k') (he : I.Eq r r') :
    RE2 S k' ((tgFib A φ T e ψ u0).isub σ)
      (((Tm.split δ.shift (.papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift
        (.papp (tgPpsi A φ e ψ u0).dshift (.var 0))).isub σ.up).dinst r)
      (((Tm.split δ'.shift (.papp (tgPd A' φ' T' e' ψ' u0').dshift (.var 0)) ψ'.shift
        (.papp (tgPpsi A' φ' e' ψ' u0').dshift (.var 0))).isub σ.up).dinst r') := by
  obtain ⟨l1, H⟩ := D.tgL hW
  obtain ⟨l2, H'⟩ := D.tgR hW
  rw [psys_isub, psys_isub]
  have hδδ := D.δδ hW
  have hh' : (ival (idEnv k') ((I.or δ' ψ').subst σ.τ)).holds := by
    rw [holds_iff_entails (I.scoped_subst (show (I.or δ' ψ').Scoped k from ⟨D.hδs', H'.hψ⟩) σ.sc)]
    exact ent_trans (entails_of_holds (I.scoped_subst (show (I.or δ ψ).Scoped k from ⟨D.hδs, H.hψ⟩) σ.sc) hh)
      (ent_subst (ent_or_elim (ent_trans hδδ.1 (ent_or_left _ _)) (ent_trans D.p12 (ent_or_right _ _))) σ.τ)
  have hfib := D.hfib hW hφ1
  have hX := tyCode_of_univ hW hfib
  have rFσ := RT2.isub hW hX (D.rFib hW hφ1) σ
  have hAA := RT2.isub hW hX (RT2.refl hW hX (D.rFib hW hφ1)) σ
  have hsp := psysTy hW H hφ1 σ hh hr
  have hsp' := (psysTy hW H' (D.φ1R hW hφ1) σ hh' hr').tyConv (Comp2_ty_base rFσ).2.2.2.2.2.symm
  have hd : ∀ {k2} (σ2 : ISub k2 k'), I.Entails .one ((δ.subst σ.τ).subst σ2.τ) →
      (ival (idEnv k2) (δ.subst (σ.comp σ2).τ)).holds := fun σ2 h =>
    (holds_iff_entails (I.scoped_subst D.hδs (σ.comp σ2).sc)).2 (by rw [I_subst_comp]; exact h)
  have hp : ∀ {k2} (σ2 : ISub k2 k'), I.Entails .one ((ψ.subst σ.τ).subst σ2.τ) →
      (ival (idEnv k2) (ψ.subst (σ.comp σ2).τ)).holds := fun σ2 h =>
    (holds_iff_entails (I.scoped_subst H.hψ (σ.comp σ2).sc)).2 (by rw [I_subst_comp]; exact h)
  refine RE2_sys2 hW (I.scoped_subst D.hδs σ.sc) (I.scoped_subst D.hδs' σ.sc) (I.scoped_subst H.hψ σ.sc)
    (I.scoped_subst H'.hψ σ.sc) (ent_subst hδδ.1 _) (ent_subst hδδ.2 _) (ent_subst D.p12 _) (ent_subst D.p21 _)
    (entails_of_holds (I.scoped_subst (show (I.or δ ψ).Scoped k from ⟨D.hδs, H.hψ⟩) σ.sc) hh) hAA hsp hsp'
    (fun k2 σ2 h => ?_) (fun k2 σ2 h h' => ?_) (fun k2 σ2 h h' => ?_) (fun k2 σ2 h => ?_) <;>
  simp only [isub_papp, Tm.isub_isub]
  · exact D.PdPt hW hφ1 (σ.comp σ2) (hd σ2 h) (I.scoped_subst hr σ2.sc) (I.scoped_subst hr' σ2.sc)
      (I_eq_subst he σ2.τ)
  · exact D.PdXPt hW hφ1 (σ.comp σ2) (hd σ2 h) (hp σ2 h') (I.scoped_subst hr σ2.sc) (I.scoped_subst hr' σ2.sc)
      (I_eq_subst he σ2.τ)
  · exact D.PpsiXPt hW hφ1 (σ.comp σ2) (hd σ2 h) (hp σ2 h') (I.scoped_subst hr σ2.sc) (I.scoped_subst hr' σ2.sc)
      (I_eq_subst he σ2.τ)
  · exact D.PpsiPt hW hφ1 (σ.comp σ2) (hp σ2 h) (I.scoped_subst hr σ2.sc) (I.scoped_subst hr' σ2.sc)
      (I_eq_subst he σ2.τ)

end

end

end Model.Whnf
