import Model.Canon.ProjFace
import Model.Canon.KanDerived

/-!
# Canonicity: composition of a constructor in an inductive type without path constructors

The tube of a composition in such a type is, on each face of its cofibration, a constructor
(computability); the projections glue the arguments uniformly, so that `hcompCon` applies.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig}

theorem nonHIT_ctor {D : DataDecl} (hH : D.isHIT = false) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) :
    C.dims = 0 ∧ C.bnd = [] := by
  unfold DataDecl.isHIT at hH
  have h := (List.any_eq_false.1 hH) C (List.mem_of_getElem? hC)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff, not_or,
    Decidable.not_not] at h
  exact ⟨h.1, by simpa using h.2⟩

theorem closedB_toList {t : Tm} {n m : ℕ} (h : t.closedB n m = true) : ∀ x ∈ t.toList, x.closedB n m = true := by
  induction t with
  | tcons a as _ ih =>
    simp only [Tm.closedB, Bool.and_eq_true] at h
    intro x hx
    simp only [Tm.toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx
  | _ => intro x hx; simp [Tm.toList] at hx

theorem PD.of (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
    {Ψ : ℕ} {Φ : I} {ps : Tm} (hd : HasTy0 S Ψ Φ [] (.data d ps) (.univ D.level)) : PD S Ψ Φ d D ps := by
  obtain ⟨D', hD', hpt⟩ := gen_data_tele hd rfl
  rw [hD] at hD'; cases hD'
  have hc : ps.closedB 0 Ψ = true := by simpa [Tm.closedB] using closed_ty hd
  exact ⟨hD, tele_isList hpt, closedB_toList hc, by simpa using tele_length hpt, hpt, hd, wf_of_ty hd,
    fun c C hC => (nonHIT_ctor hH hC).1, fun c C hC => (nonHIT_ctor hH hC).2⟩

/-- Canonical forms of a tube at its faces. -/
def TubeCanon (S : Sig) (k d : ℕ) (D : DataDecl) (ps : Tm) (φ : I) (u : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
    ∃ c' C' X', D.ctors[c']? = some C' ∧
      HasTele0 S k' .one [] (Tm.ofList X') (C'.argTys d D.params.length) (ps.isub σ).toList.reverse ∧
      EqTm S k' .one [] ((u.isub σ.up).dinst r) (.con d c' (ps.isub σ) (Tm.ofList X') []) (.data d (ps.isub σ))

theorem holds_sub {k k'' : ℕ} {φ : I} (hφ : φ.Scoped k) (hh : (ival (idEnv k) φ).holds) (σ : ISub k'' k) :
    (ival (idEnv k'') (φ.subst σ.τ)).holds := by
  rw [holds_iff_entails (I.scoped_subst hφ σ.sc)]
  exact ent_subst (entails_of_holds hφ hh) σ.τ

/-- An interval substitution, weakened by one interval variable. -/
def ISub.sh {k' k : ℕ} (σ : ISub k' k) : ISub (k' + 1) k :=
  ISub.ofFun k (fun i => (σ.τ i).shift) fun i hi => I.scoped_shift (σ.sc i hi)

theorem isub_sh_up_var {k' k : ℕ} {u : Tm} (hu : u.closedB 0 (k + 1) = true) (σ : ISub k' k) :
    (u.isub σ.sh.up).dinst (.var 0) = u.isub σ.up := by
  simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  apply closed_subst_eq u 0 (k + 1) _ _ _ _ hu (fun x hx => absurd hx (Nat.not_lt_zero _))
  intro i hi
  rcases i with _ | i
  · rfl
  · show (((ISub.ofFun k (fun i => (σ.τ i).shift) _).τ i).shift).subst _ = (σ.τ i).shift
    simp only [ISub.ofFun, if_pos (show i < k by omega)]
    rw [I_shift_inst0]

theorem isub_sh {k' k : ℕ} {t : Tm} (ht : t.closedB 0 k = true) (σ : ISub k' k) :
    t.isub σ.sh = (t.isub σ).dshift := by
  unfold ISub.sh
  rw [isub_ofFun ht, dshift_eq]
  simp only [Tm.isub, subst_subst]
  rfl

theorem dinst_isub_end' {k' k : ℕ} (X : Tm) {r : I} (hr : r = .zero ∨ r = .one) (σ : ISub k' k) :
    (X.dinst r).isub σ = (X.isub σ.up).dinst r := by
  simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  congr 1; funext i; rcases i with _ | i
  · rcases hr with rfl | rfl <;> rfl
  · show σ.τ i = ((σ.τ i).shift).subst _; rw [I_shift_inst0]

/-- All canonical forms of a tube have the base's constructor. -/
theorem tube_tag (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
    {k : ℕ} {ps u : Tm} {φ : I} {c : ℕ} {C : Ctor} {X : List Tm} (hC : D.ctors[c]? = some C)
    (hd : HasTy S k .one [] (.data d ps) (.univ D.level)) (hφs : φ.Scoped k) (hut : u.closedB 0 (k + 1) = true)
    (hside : EqTm S k (cof .one φ) [] (u.dinst .zero) (.con d c ps (Tm.ofList X) []) (.data d ps))
    (hcan : TubeCanon S k d D ps φ u) {k' : ℕ} (σ : ISub k' k) {r : I} (hr : r.Scoped k')
    (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) {c' : ℕ} {C' : Ctor} {X' : List Tm} (hC' : D.ctors[c']? = some C')
    (he : EqTm S k' .one [] ((u.isub σ.up).dinst r) (.con d c' (ps.isub σ) (Tm.ofList X') []) (.data d (ps.isub σ))) :
    c' = c := by
  have hS := sigClosed_of_wfSig hW
  have hpsc : ps.closedB 0 k = true := by simpa [Tm.closedB] using closed_of_ty hW hd
  have hdσ := HasTy.isubS hW hd σ
  -- the canonical form of the whole restricted line
  have hh1 : (ival (idEnv (k' + 1)) (φ.subst σ.sh.τ)).holds := by
    rw [holds_iff_entails (I.scoped_subst hφs σ.sh.sc)]
    rw [I_subst_congr_scoped (τ := fun i => (σ.τ i).shift) (fun i hi => by simp [ISub.sh, ISub.ofFun, hi]) hφs]
    rw [show (fun i => (σ.τ i).shift) = (fun i => (σ.τ i).subst fun j => .var (j + 1)) from rfl, ← I_subst_subst]
    exact ent_subst (entails_of_holds (I.scoped_subst hφs σ.sc) hh) _
  obtain ⟨c1, C1, X1, hC1, -, e1⟩ := hcan (k' + 1) σ.sh (.var 0) (show 0 < k' + 1 by omega) hh1
  rw [isub_sh_up_var hut, isub_sh hpsc] at e1
  -- its instances
  have inst : ∀ s : I, s.Scoped k' → EqTm S k' .one [] ((u.isub σ.up).dinst s)
      (.con d c1 (ps.isub σ) ((Tm.ofList X1).dinst s) []) (.data d (ps.isub σ)) := by
    intro s hs
    have := minimal_to_spec_eq (EqTm0.dsubst hS (Ψ := k') (Φ := .one) (Γ := []) (spec_to_minimal_eq hW e1) (r := s) hs)
    rw [show (Tm.con d c1 (ps.isub σ).dshift (Tm.ofList X1) []).dinst s =
        Tm.con d c1 ((ps.isub σ).dshift.dinst s) ((Tm.ofList X1).dinst s) [] from rfl,
      show (Tm.data d (ps.isub σ).dshift).dinst s = Tm.data d ((ps.isub σ).dshift.dinst s) from rfl,
      Meta.dshift_dinst] at this
    exact this
  have hd1 := HasTy.eqR he
  have tagr := con_tag hW hD hC1 hC' (nonHIT_ctor hH hC1).2 (nonHIT_ctor hH hC').2 hdσ hdσ
    (HasTy.eqR (inst r hr)) hd1 ((inst r hr).symm.trans he)
  -- at the start of the tube
  have hent : I.Entails .one (cof .one (φ.subst σ.τ)) := ent_cof_one hW (entails_of_holds (I.scoped_subst hφs σ.sc) hh)
  have hs0 := EqTm.restrict (Φ' := .one) trivial hent (EqTm.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩) hside σ)
  rw [dinst_isub_end' _ (.inl rfl)] at hs0
  have e0 := (inst .zero trivial).symm.trans hs0
  have tag0 := con_tag hW hD hC1 hC (nonHIT_ctor hH hC1).2 (nonHIT_ctor hH hC).2 hdσ hdσ
    (HasTy.eqR (inst .zero trivial)) (HasTy.eqR hs0) e0
  rw [← tagr, tag0]

theorem ISub.cons_tail {k k'' : ℕ} (ρ : ISub k'' (k + 1)) : ISub.cons (ρ.τ 0) (ρ.sc 0 (by omega)) ρ.tail = ρ := by
  ext i; rcases i with _ | i <;> rfl

/-- A face holds at its own endpoints. -/
theorem ent_ofFace_faceSub {α : I.Face} (hc : I.Face.consistent α = true) :
    I.Entails .one ((I.ofFace α).subst (faceSub α)) := by
  rw [entails_iff]
  intro ρ _ _
  rw [eval_subst]
  exact (KubusCore.Meta.eval_ofFace _ α).2 fun l hl => by
    show (faceSub α l.1).eval ρ = _
    rw [faceSub_mem hc hl, eval_ofDir]

theorem inst_dsubst (t a : Tm) (τ : ℕ → I) :
    (t.inst a).subst Tm.var τ = (t.subst Tm.var τ).inst (a.subst Tm.var τ) := by
  simp only [Tm.inst, subst_subst]
  congr 1
  · funext x; cases x with
    | zero => rfl
    | succ x => rfl
  · funext i; exact (I_subst_var _).symm

section
variable {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor} {j : ℕ}

/-- `proj_j` respects judgmental equality of its argument. -/
theorem proj_congr (hS : SigClosed S) (hW : WfSig S) {Ψ : ℕ} {Φ : I} {ps : Tm} (H : PD S Ψ Φ d D ps)
    (hcC : D.ctors[c]? = some C) (hj : j < C.args.length) {t t' : Tm} (e : EqTm0 S Ψ Φ [] t t' (.data d ps)) :
    EqTm0 S Ψ Φ [] (proj d D ps c C j t) (proj d D ps c C j t') ((projQ d D ps c C j).inst t) := by
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  obtain ⟨ht, ht', -⟩ := pre_eq hS hT hCt e
  have h1 := proj_typed hS hW H hcC hj H.hw ht
  have h2 := proj_typed hS hW H hcC hj H.hw ht'
  have eQ := HasTy0.inst_congr hS (projQ_typed hS hW H hcC hj) ht ht' e
  refine EqTm0.elim H.hD h1 (HasTy0.conv h2 (EqTm0.symm eQ)) (EqTele0.refl H.hpt)
    (EqTm0.refl (projQ_typed hS hW H hcC hj)) (branchesOf_isList _ _ _ _ _) (branchesOf_isList _ _ _ _ _) rfl
    (fun c' C' b b' hc' hb hb' => ?_) e
  rw [hb] at hb'; cases hb'
  rw [branchesOf_get hc', Option.some.injEq] at hb; subst hb
  exact EqTm0.refl (proj_branch_typed hS hW H hcC hj hc')

end


section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C)
include hW hD hH hC

/-- On a face of the cofibration of a composition, the tube is the base's constructor, at
arguments which are the projections of the tube there. -/
theorem face_data {k : ℕ} {ps u : Tm} {φ : I} {X : List Tm}
    (hd : HasTy S k .one [] (.data d ps) (.univ D.level)) (hφs : φ.Scoped k)
    (hut : HasTy0 S (k + 1) (cof .one φ).shift [] u (Tm.data d ps).dshift)
    (hside : EqTm S k (cof .one φ) [] (u.dinst .zero) (.con d c ps (Tm.ofList X) []) (.data d ps))
    (hcan : TubeCanon S k d D ps φ u) {α : I.Face} (hα : α ∈ ((cof .one φ).shift).faces) :
    ∃ X' : List Tm,
      HasTele0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] (Tm.ofList X') (C.argTys d D.params.length)
        (ps.dshift.subst Tm.var (faceSub α)).toList.reverse ∧
      EqTm0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] u
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList X') []) (.data d ps.dshift) ∧
      EqTm0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] (.data d ps.dshift)
        (.data d (ps.dshift.subst Tm.var (faceSub α))) (.univ D.level) ∧
      HasTy0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] (.data d (ps.dshift.subst Tm.var (faceSub α)))
        (.univ D.level) := by
  have hS := sigClosed_of_wfSig hW
  have hΦs : ((cof .one φ).shift).Scoped (k + 1) := I.scoped_shift ⟨trivial, hφs⟩
  have hcα := faces_consistent hα
  have hsc := faces_scoped hΦs α hα
  have hsα : (I.ofFace α).Scoped (k + 1) := scoped_ofFace hsc
  have hΞs : (cof (cof .one φ).shift (I.ofFace α)).Scoped (k + 1) := ⟨hΦs, hsα⟩
  have hτ : ∀ i < k + 1, (faceSub α i).Scoped (k + 1) := fun i hi => by
    rcases faceSub_cases α i with ⟨e, _, h⟩ | ⟨_, h⟩
    · rw [h]; cases e <;> trivial
    · rw [h]; exact hi
  set ρ := ISub.ofFun (k + 1) (faceSub α) hτ with hρ
  have hpsc : ps.closedB 0 k = true := by simpa [Tm.closedB] using closed_of_ty hW hd
  have hpsd : ps.dshift.closedB 0 (k + 1) = true := by
    have := closed_of_ty hW (HasTy.isubS hW hd (ISub.wk k))
    rw [isub_wk_of_closed (closed_of_ty hW hd)] at this
    simpa [Tm.closedB] using this
  have hPα : ps.dshift.subst Tm.var (faceSub α) = ps.isub ρ.tail := by
    rw [← dshift_isub_tail, hρ, isub_ofFun hpsd]
  have huc : u.closedB 0 (k + 1) = true := closed_ty hut
  have huα : u.subst Tm.var (faceSub α) = (u.isub ρ.tail.up).dinst (ρ.τ 0) := by
    rw [isub_up_dinst _ _ _ (ρ.sc 0 (by omega)), ISub.cons_tail, hρ, isub_ofFun huc]
  -- the face holds at its endpoints
  have hface : (ival (idEnv (k + 1)) (φ.subst ρ.tail.τ)).holds := by
    rw [holds_iff_entails (I.scoped_subst hφs ρ.tail.sc)]
    have h1 : I.Entails (I.ofFace α) φ.shift :=
      ent_trans (ofFace_ent hα) (ent_and_right _ _)
    have h2 := ent_trans (ent_ofFace_faceSub hcα) (ent_subst h1 (faceSub α))
    have e3 : φ.shift.subst (faceSub α) = φ.subst ρ.tail.τ := by
      rw [← I_shift_tail]
      exact I_subst_congr_scoped (fun i hi => by
        show faceSub α i = (if i < k + 1 then faceSub α i else .zero); rw [if_pos hi]) (I.scoped_shift hφs)
    rwa [e3] at h2
  obtain ⟨c', C', X', hC', hX', e'⟩ := hcan (k + 1) ρ.tail (ρ.τ 0) (ρ.sc 0 (by omega)) hface
  have htag := tube_tag hW hD hH hC hd hφs huc hside hcan ρ.tail (ρ.sc 0 (by omega)) hface hC' e'
  subst htag; rw [hC] at hC'; cases hC'
  rw [← huα, ← hPα] at e'
  rw [← hPα] at hX'
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  have hent : I.Entails (cof (cof .one φ).shift (I.ofFace α)) .one := ent_one _
  have hX'Ξ := HasTele0.restrict hΞs hent hX'
  have e'Ξ := EqTm0.restrict hΞs hent (spec_to_minimal_eq hW e')
  have hd1 : HasTy0 S (k + 1) (I.one.shift) (Ctx.dshift []) (Tm.data d ps).dshift (Tm.univ D.level).dshift :=
    HasTy0.dwk hS (spec_to_minimal hW hd)
  have hdΞ : HasTy0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] (Tm.data d ps.dshift) (.univ D.level) :=
    HasTy0.restrict hΞs hent hd1
  have e_u := face_all hW (.inl hdΞ) (HasTy0.restrict hΞs (ent_and_left _ _) hut) α hsc (ent_and_right _ _)
  have e_T := face_all hW (l := D.level) (.inr rfl) hdΞ α hsc (ent_and_right _ _)
  have hdα := (pre_eq hS hT hCt e_T).2.1
  exact ⟨X', hX'Ξ, e_u.trans (EqTm0.conv e'Ξ (EqTm0.symm e_T)), e_T, hdα⟩

end

end

end Model.Canon
