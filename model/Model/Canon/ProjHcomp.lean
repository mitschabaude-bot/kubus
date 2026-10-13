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
variable {d : ℕ} {D : DataDecl} {c : ℕ} {C : Ctor}

/-- The projections of a term equal to a constructor are its arguments. -/
theorem proj_canon (hS : SigClosed S) (hW : WfSig S) {Ψ : ℕ} {Φ : I} {ps : Tm} (H : PD S Ψ Φ d D ps)
    (hcC : D.ctors[c]? = some C) {t : Tm} {X : List Tm}
    (hX : HasTele0 S Ψ Φ [] (Tm.ofList X) (C.argTys d D.params.length) ps.toList.reverse)
    (e : EqTm0 S Ψ Φ [] t (.con d c ps (Tm.ofList X) []) (.data d ps)) {i : ℕ} (hi : i < C.args.length) :
    EqTm0 S Ψ Φ [] (proj d D ps c C i t) (X.getD i .abort)
      ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ ps.toList.reverse)) := by
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  obtain ⟨ht, hcon, -⟩ := pre_eq hS hT hCt e
  have eQ := (HasTy0.inst_congr hS (projQ_typed hS hW H hcC hi) ht hcon e).trans
    (by have := projQ_con hS hW H hcC hi H.hw hcC hX; rwa [if_pos rfl] at this)
  exact (EqTm0.conv (proj_congr hS hW H hcC hi e) eQ).trans (proj_con hS hW H hcC hi H.hw hX)

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

/-- The premises of `hcompCon` for the tube's projections. -/
theorem hcompCon_premises {k : ℕ} {ps u : Tm} {φ : I} {X : List Tm}
    (hd : HasTy S k .one [] (.data d ps) (.univ D.level)) (hφs : φ.Scoped k)
    (hut : HasTy0 S (k + 1) (cof .one φ).shift [] u (Tm.data d ps).dshift)
    (hside : EqTm S k (cof .one φ) [] (u.dinst .zero) (.con d c ps (Tm.ofList X) []) (.data d ps))
    (hX : HasTele0 S k .one [] (Tm.ofList X) (C.argTys d D.params.length) ps.toList.reverse)
    (hcan : TubeCanon S k d D ps φ u) :
    HasTele0 S (k + 1) (cof .one φ).shift [] (Tm.ofList ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u))
      (C.argTys d D.params.length) ps.dshift.toList.reverse ∧
    EqTm0 S (k + 1) (cof .one φ).shift [] u
      (.con d c ps.dshift (Tm.ofList ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u)) [])
      (.data d ps.dshift) ∧
    EqTele0 S k (cof .one φ) [] ((Tm.ofList ((List.range C.args.length).map fun j => proj d D ps.dshift c C j u)).dinst .zero)
      (Tm.ofList X) (C.argTys d D.params.length) ps.toList.reverse := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  have hΦs : ((cof .one φ).shift).Scoped (k + 1) := I.scoped_shift ⟨trivial, hφs⟩
  have hd1 : HasTy0 S (k + 1) (cof .one φ).shift [] (.data d ps.dshift) (.univ D.level) :=
    HasTy0.restrict hΦs (ent_one _) (HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal hW hd))
  have H' := PD.of hW hD hH hd1
  set uargs := (List.range C.args.length).map fun j => proj d D ps.dshift c C j u with huargs
  have hul : uargs.length = C.args.length := by simp [uargs]
  have huget : ∀ i (hi : i < uargs.length), uargs[i] = proj d D ps.dshift c C i u := by intro i hi; simp [uargs]
  -- facewise data
  have FD : ∀ α ∈ ((cof .one φ).shift).faces, ∃ X' : List Tm,
      HasTele0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] (Tm.ofList X') (C.argTys d D.params.length)
        (ps.dshift.subst Tm.var (faceSub α)).toList.reverse ∧
      EqTm0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] u
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList X') []) (.data d ps.dshift) ∧
      EqTm0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] (.data d ps.dshift)
        (.data d (ps.dshift.subst Tm.var (faceSub α))) (.univ D.level) ∧
      HasTy0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) [] (.data d (ps.dshift.subst Tm.var (faceSub α)))
        (.univ D.level) := fun α hα => face_data hW hD hH hC hd hφs hut hside hcan hα
  -- the projections of the tube are a telescope
  have claim : ∀ j, j ≤ C.args.length → ∀ i (hi : i < j) (hi' : i < uargs.length),
      HasTy0 S (k + 1) (cof .one φ).shift [] uargs[i]
        ((C.argTy d D.params.length i).substList ((uargs.take i).reverse ++ ps.dshift.toList.reverse)) := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi hi'
      by_cases hij : i < j
      · exact ih (by omega) i hij hi'
      obtain rfl : i = j := by omega
      have hjC : i < C.args.length := by omega
      have hat : ∀ k' (hk : k' < (uargs.take i).length), k' < C.args.length →
          HasTy0 S (k + 1) (cof .one φ).shift [] (uargs.take i)[k']
            ((C.argTy d D.params.length k').substList (((uargs.take i).take k').reverse ++ ps.dshift.toList.reverse)) := by
        intro k' hk _
        have hk' : k' < i := by simp at hk; omega
        rw [List.getElem_take, List.take_take, Nat.min_eq_left hk'.le]
        exact ih (by omega) k' hk' (by omega)
      have hR := argTy_inst_typed hS hW hD hC H'.hpsL H'.hpl H'.hpt H'.hdata H'.hw hat (j := i) (by simp; omega) hjC
      rw [List.take_take, Nat.min_self] at hR
      have hL : HasTy0 S (k + 1) (cof .one φ).shift [] ((projQ d D ps.dshift c C i).inst u) (.univ D.level) :=
        HasTy0.subst hS (projQ_typedΓ hS hW H' hC hjC H'.hw) hut
      have e : EqTm0 S (k + 1) (cof .one φ).shift [] ((projQ d D ps.dshift c C i).inst u)
          ((C.argTy d D.params.length i).substList ((uargs.take i).reverse ++ ps.dshift.toList.reverse)) (.univ D.level) := by
        refine eq_local_faces hL hR fun α hα => ?_
        obtain ⟨X', hX', e_u, e_T, hdα⟩ := FD α hα
        have hsc := faces_scoped hΦs α hα
        have hsα : (I.ofFace α).Scoped (k + 1) := scoped_ofFace hsc
        have hΞs : (cof (cof .one φ).shift (I.ofFace α)).Scoped (k + 1) := ⟨hΦs, hsα⟩
        have hent : I.Entails (cof (cof .one φ).shift (I.ofFace α)) (I.ofFace α) := ent_and_right _ _
        have hΞe : I.Entails (cof (cof .one φ).shift (I.ofFace α)) (cof .one φ).shift := ent_and_left _ _
        have Hα := PD.of hW hD hH hdα
        have huΞ := HasTy0.restrict hΞs hΞe hut
        have hd1Ξ := HasTy0.restrict hΞs hΞe hd1
        have e_uu := face_all hW (.inl hd1Ξ) huΞ α hsc hent
        have e_uαc := EqTm0.conv (e_uu.symm.trans e_u) e_T
        have hX'l : X'.length = C.args.length := by
          have := tele_length hX'; rwa [toList_ofList, argTys_length] at this
        set Y := (List.range C.args.length).map fun i' =>
          proj d D (ps.dshift.subst Tm.var (faceSub α)) c C i' (u.subst Tm.var (faceSub α)) with hY
        have hYl : Y.length = X'.length := by simp [Y, hX'l]
        have hYX : ∀ i' (h1 : i' < X'.length) (h2 : i' < Y.length), EqTm0 S (k + 1)
            (cof (cof .one φ).shift (I.ofFace α)) [] Y[i'] X'[i']
            ((C.argTy d D.params.length i').substList ((X'.take i').reverse ++
              (ps.dshift.subst Tm.var (faceSub α)).toList.reverse)) := by
          intro i' h1 h2
          have := proj_canon hS hW Hα hC hX' e_uαc (i := i') (by omega)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
          simpa [Y] using this
        have tc := tele_conv hW hD hC Hα.hpsL Hα.hpt Hα.hdata hX' hYl hYX
        have a1 := face_all hW (l := D.level) (.inr rfl) (HasTy0.restrict hΞs hΞe hL) α hsc hent
        rw [inst_dsubst, projQ_dsubst hS hD hC hjC H'.hpsL H'.hpl] at a1
        obtain ⟨hua, hca, -⟩ := pre_eq hS hT hCt e_uαc
        have a2 := HasTy0.inst_congr hS (projQ_typed hS hW Hα hC hjC) hua hca e_uαc
        have a3 := projQ_con hS hW Hα hC hjC Hα.hw hC hX'
        rw [if_pos rfl] at a3
        have a4 := (tc.2.2 i (by omega)).symm
        have a5 : (C.argTy d D.params.length i).substList ((Y.take i).reverse ++
            (ps.dshift.subst Tm.var (faceSub α)).toList.reverse) =
            ((C.argTy d D.params.length i).substList ((uargs.take i).reverse ++ ps.dshift.toList.reverse)).subst
              Tm.var (faceSub α) := by
          have hcl := argTy_closed hS hD hC i
          rw [substList_subst (by simpa [H'.hpl, hul, Nat.min_eq_left hjC.le, Nat.add_comm] using hcl),
            List.map_append, toList_subst H'.hpsL, List.map_reverse, List.map_reverse]
          congr 3
          apply List.ext_getElem (by simp [Y, uargs])
          intro i' h1 h2
          simp only [Y, uargs, List.getElem_take, List.getElem_map, List.getElem_range]
          rw [proj_dsubst hS hD hC (by simp at h1; omega) H'.hpsL H'.hpl]
        have a6 := (face_all hW (l := D.level) (.inr rfl) (HasTy0.restrict hΞs hΞe hR) α hsc hent).symm
        rw [← a5] at a6
        exact a1.trans (a2.trans (a3.trans (a4.trans a6)))
      rw [huget i hi']
      exact HasTy0.conv (proj_typed hS hW H' hC hjC H'.hw hut) e
  have hdims := (nonHIT_ctor hH hC).1
  have G1 : HasTele0 S (k + 1) (cof .one φ).shift [] (Tm.ofList uargs) (C.argTys d D.params.length)
      ps.dshift.toList.reverse := by
    refine HasTele0.ofList_of H'.hw uargs _ _ (by simp [hul, argTys_length]) (fun i a A ha hA => ?_)
    have hi := (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    rw [argTys_get (by omega), Option.some.injEq] at hA; subst hA
    exact claim C.args.length (Nat.le_refl _) i (by omega) hi
  have hcon : HasTy0 S (k + 1) (cof .one φ).shift [] (.con d c ps.dshift (Tm.ofList uargs) []) (.data d ps.dshift) :=
    HasTy0.con hD hC H'.hpsL H'.hdata H'.hpt G1 (by simp [hdims]) (by simp)
  refine ⟨G1, eq_local_faces hut hcon fun α hα => ?_, ?_⟩
  · obtain ⟨X', hX', e_u, e_T, hdα⟩ := FD α hα
    have hsc := faces_scoped hΦs α hα
    have hsα : (I.ofFace α).Scoped (k + 1) := scoped_ofFace hsc
    have hΞs : (cof (cof .one φ).shift (I.ofFace α)).Scoped (k + 1) := ⟨hΦs, hsα⟩
    have hent : I.Entails (cof (cof .one φ).shift (I.ofFace α)) (I.ofFace α) := ent_and_right _ _
    have hΞe : I.Entails (cof (cof .one φ).shift (I.ofFace α)) (cof .one φ).shift := ent_and_left _ _
    have Hα := PD.of hW hD hH hdα
    have huΞ := HasTy0.restrict hΞs hΞe hut
    have hd1Ξ := HasTy0.restrict hΞs hΞe hd1
    have e_uu := face_all hW (.inl hd1Ξ) huΞ α hsc hent
    have e_uαc := EqTm0.conv (e_uu.symm.trans e_u) e_T
    have hX'l : X'.length = C.args.length := by
      have := tele_length hX'; rwa [toList_ofList, argTys_length] at this
    set Y := (List.range C.args.length).map fun i' =>
      proj d D (ps.dshift.subst Tm.var (faceSub α)) c C i' (u.subst Tm.var (faceSub α)) with hY
    have hYl : Y.length = X'.length := by simp [Y, hX'l]
    have hYX : ∀ i' (h1 : i' < X'.length) (h2 : i' < Y.length), EqTm0 S (k + 1)
        (cof (cof .one φ).shift (I.ofFace α)) [] Y[i'] X'[i']
        ((C.argTy d D.params.length i').substList ((X'.take i').reverse ++
          (ps.dshift.subst Tm.var (faceSub α)).toList.reverse)) := by
      intro i' h1 h2
      have := proj_canon hS hW Hα hC hX' e_uαc (i := i') (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
      simpa [Y] using this
    have tc := tele_conv hW hD hC Hα.hpsL Hα.hpt Hα.hdata hX' hYl hYX
    have b1 : EqTm0 S (k + 1) (cof (cof .one φ).shift (I.ofFace α)) []
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList X') [])
        (.con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList Y) [])
        (.data d (ps.dshift.subst Tm.var (faceSub α))) :=
      EqTm0.con hD hC (HasTy0.con hD hC Hα.hpsL Hα.hdata Hα.hpt hX' (by simp [hdims]) (by simp))
        (HasTy0.con hD hC Hα.hpsL Hα.hdata Hα.hpt tc.1 (by simp [hdims]) (by simp)) (EqTele0.refl Hα.hpt)
        (EqTele0.ofList_of' Hα.hw X' Y _ _ (by simp [argTys_length, hX'l]) (by simp [argTys_length, Y])
          (fun i a a' A ha ha' hA => by
            have hi := (List.getElem?_eq_some_iff.1 ha).1
            obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha
            obtain ⟨-, rfl⟩ := List.getElem?_eq_some_iff.1 ha'
            rw [argTys_get (by omega), Option.some.injEq] at hA; subst hA
            exact EqTm0.symm (hYX i hi (by omega))))
        rfl (fun _ _ _ h => by simp at h)
    have b2 : (Tm.con d c ps.dshift (Tm.ofList uargs) []).subst Tm.var (faceSub α) =
        .con d c (ps.dshift.subst Tm.var (faceSub α)) (Tm.ofList Y) [] := by
      show Tm.con d c _ ((Tm.ofList uargs).subst Tm.var (faceSub α)) [] = _
      rw [ofList_subst]
      congr 2
      apply List.ext_getElem (by simp [Y, uargs])
      intro i' h1 h2
      simp only [Y, uargs, List.getElem_map, List.getElem_range]
      rw [proj_dsubst hS hD hC (by simp [Y] at h2; omega) H'.hpsL H'.hpl]
    have b3 := face_all hW (.inl hd1Ξ) (HasTy0.restrict hΞs hΞe hcon) α hsc hent
    rw [b2] at b3
    exact e_u.trans ((EqTm0.conv b1 (EqTm0.symm e_T)).trans b3.symm)
  · have hd0 : HasTy0 S k (cof .one φ) [] (.data d ps) (.univ D.level) :=
      HasTy0.restrict (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩) (ent_and_left _ _) (spec_to_minimal hW hd)
    have H0 := PD.of hW hD hH hd0
    have hX0 := HasTele0.restrict (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩) (ent_and_left _ _) hX
    have hside0 := spec_to_minimal_eq hW hside
    have hXl : X.length = C.args.length := by
      have := tele_length hX; rwa [toList_ofList, argTys_length] at this
    set Y0 := (List.range C.args.length).map fun i => proj d D ps c C i (u.dinst .zero) with hY0
    have e0 : (Tm.ofList uargs).dinst .zero = Tm.ofList Y0 := by
      rw [Tm.dinst, Tm.dsubst, ofList_subst]
      congr 1
      apply List.ext_getElem (by simp [Y0, uargs])
      intro i' h1 h2
      simp only [Y0, uargs, List.getElem_map, List.getElem_range]
      rw [proj_dsubst hS hD hC (by simp [Y0] at h2; omega) H'.hpsL H'.hpl]
      congr 1
      exact Meta.dshift_dinst ps .zero
    have hY0X : ∀ i (h1 : i < X.length) (h2 : i < Y0.length), EqTm0 S k (cof .one φ) [] Y0[i] X[i]
        ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ ps.toList.reverse)) := by
      intro i h1 h2
      have := proj_canon hS hW H0 hC hX0 hside0 (i := i) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
      simpa [Y0] using this
    rw [e0]
    exact (tele_conv hW hD hC H0.hpsL H0.hpt H0.hdata hX0 (by simp [Y0, hXl]) hY0X).2.1

end

end

end Model.Canon
