import Model.Canon.KanDerived
import Model.Canon.KanSigma

/-!
# Canonicity: the Kan operations at path types
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem dshift_dinst' (t : Tm) (r : I) : t.dshift.subst .var (I.inst0 r) = t := dshift_dinst t r

theorem hcompPath_body (A a b u p0 : Tm) (φ r : I) : ∃ t, Tm.hcompPath A a b φ u p0 = .plam t ∧
    t.dinst r = .hcomp (A.dinst r) (.or φ (.or (.neg r) r))
      (.split φ.shift (.papp u r.shift) (.or (.neg r.shift) r.shift) (.split (.neg r.shift) a.dshift r.shift b.dshift))
      (.papp p0 r) := by
  refine ⟨_, rfl, ?_⟩
  simp only [Tm.dinst, Tm.dsubst, Tm.subst, I.subst, I_shift_inst0]
  have hφ : φ.shift.shift.subst (I.up (I.inst0 r)) = φ.shift := by
    rw [I_shift_subst_up, I_shift_inst0]
  have hd : ∀ x : Tm, x.dshift.dshift.subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 r)) = x.dshift := by
    intro x; simp only [dshift_eq, subst_subst]
    exact subst_congr (fun _ => rfl) (fun i => rfl) x
  rw [hφ, hd a, hd b, dshift_dinst']
  congr 3
  simp only [subst_subst]
  exact subst_id_of (fun _ => rfl) (fun i => by rcases i with _ | i <;> rfl) u

theorem isub_hcompPath (A a b u p0 : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.hcompPath A a b φ u p0).isub σ =
      Tm.hcompPath (A.isub σ.up) (a.isub σ) (b.isub σ) (φ.subst σ.τ) (u.isub σ.up) (p0.isub σ) := by
  show (Tm.hcompPath A a b φ u p0).subst .var σ.τ = _
  rw [hcompPath_subst, show dupS Tm.var = Tm.var from funext fun n => rfl]; rfl

theorem isub_isub_up_cons (X : Tm) (σ : ISub k' k) {k'' : ℕ} (r : I) (hr : r.Scoped k'') (σ' : ISub k'' k') :
    (X.isub σ.up).isub (ISub.cons r hr σ') = (X.isub (σ.comp σ').up).dinst r := by
  rw [← isub_up_dinst _ _ r hr, Tm.isub_isub]
  exact congrArg (fun s => (X.isub s).dinst r) (ISub.up_comp σ σ').symm


theorem transpPath_body (A a b p0 : Tm) (φ r : I) : ∃ t, Tm.transpPath A a b φ p0 = .plam t ∧
    t.dinst r = Tm.comp (A.subst .var (consI r.shift (consI (.var 0) fun n => .var (n + 1)))) (.or φ (.or (.neg r) r))
      (.split φ.shift (.papp p0.dshift r.shift) (.or (.neg r.shift) r.shift) (.split (.neg r.shift) a r.shift b))
      (.papp p0 r) := by
  refine ⟨_, transpPath_eq A a b φ p0, ?_⟩
  simp only [Tm.comp, Tm.dinst, Tm.dsubst, Tm.subst, I.subst, I_shift_inst0]
  have hφ2 : φ.shift.shift.subst (I.up (I.inst0 r)) = φ.shift := by rw [I_shift_subst_up, I_shift_inst0]
  have hd : ∀ x : Tm, x.dshift.dshift.subst (fun n => (Tm.var n).dshift) (I.up (I.inst0 r)) = x.dshift := by
    intro x; simp only [dshift_eq, subst_subst]
    exact subst_congr (fun _ => rfl) (fun i => rfl) x
  rw [hφ2, hd p0, dshift_dinst']
  congr 1
  · simp only [subst_subst]
    exact subst_congr (fun _ => rfl) (fun x => by
      rcases x with _ | _ | x <;> simp [swapI, consI, I.inst0, I.up, I.subst, I_shift_inst0] <;> rfl) A
  · congr 1
    · simp only [subst_subst]
      exact subst_congr (fun _ => rfl) (fun x => by
        rcases x with _ | _ | x <;> simp [swapI, consI, I.inst0, I.up, Tm.bind2, I.subst]
        · rw [I_shift_subst]; exact (I_add2 r).symm
        · rfl
        · rfl) A
    · congr 2
      · simp only [subst_subst]
        exact subst_id_of (fun _ => rfl) (fun i => by rcases i with _ | i <;> rfl) a
      · simp only [subst_subst]
        exact subst_id_of (fun _ => rfl) (fun i => by rcases i with _ | i <;> rfl) b
  · congr 1
    simp only [subst_subst]
    exact subst_congr (fun _ => rfl) (fun x => by
      rcases x with _ | _ | x <;> simp [swapI, consI, I.inst0, I.up, I.subst, I_shift_inst0] <;> rfl) A

theorem isub_transpPath (A a b p0 : Tm) (φ : I) (σ : ISub k' k) :
    (Tm.transpPath A a b φ p0).isub σ =
      Tm.transpPath (A.isub σ.up.up) (a.isub σ.up) (b.isub σ.up) (φ.subst σ.τ) (p0.isub σ) := by
  show (Tm.transpPath A a b φ p0).subst .var σ.τ = _
  rw [transpPath_subst, show dupS (dupS Tm.var) = Tm.var from funext fun n => rfl,
    show dupS Tm.var = Tm.var from funext fun n => rfl]; rfl



theorem I_add2' (x : I) : x.subst (fun n => Tm.bind2 (.or (.var 1) (.var 0)) (n + 1)) = x.shift.shift := I_add2 x

theorem dupvar_subst (τ : ℕ → I) (X : Tm) : Tm.subst (fun n => (Tm.var n).dshift) τ X = X.subst .var τ :=
  subst_congr (fun _ => rfl) (fun _ => rfl) X

/-- A path line (in `j` = 0, over `i` = 1) at `j := x`, `i := y` and the rest restricted along `ρ`. -/
def nfA (A : Tm) (x y : I) (ρ : ISub k' k) : Tm := A.subst .var (consI x (consI y ρ.τ))

theorem nfA_cons (A : Tm) (x y : I) (hy : y.Scoped k') (ρ : ISub k' k) :
    (A.isub (ISub.cons y hy ρ).up).dinst x = nfA A x y ρ := by
  simp only [nfA, Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · rfl
  · exact I_shift_inst0 y x
  · exact I_shift_inst0 _ x

theorem nfA_end (A : Tm) (x : I) (e : I) (he : e = .zero ∨ e = .one) (ρ : ISub k' k) :
    ((A.subst .var (I.up (I.inst0 e))).isub ρ.up).dinst x = nfA A x e ρ := by
  simp only [nfA, Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · rfl
  · rcases he with rfl | rfl <;> rfl
  · show (((Tm.var i : Tm) |> fun _ => (I.var i).shift).subst (I.up ρ.τ)).subst (I.inst0 x) = ρ.τ i
    rw [I_shift_subst_up, I_shift_inst0]; rfl


theorem nfA_line_isub (A : Tm) (r : I) (σ : ISub k' k) {k'' : ℕ} (y : I) (hy : y.Scoped k'') (σ' : ISub k'' k') :
    (A.subst .var (consI r.shift (consI (.var 0) fun n => (σ.τ n).shift))).isub (ISub.cons y hy σ') =
      nfA A (r.subst σ'.τ) y (σ.comp σ') := by
  simp only [nfA, Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · exact I_shift_cons r y hy σ'
  · rfl
  · exact I_shift_cons _ y hy σ'

theorem nfA_line_dinst (A : Tm) (r : I) (σ : ISub k' k) (y : I) :
    (A.subst .var (consI r.shift (consI (.var 0) fun n => (σ.τ n).shift))).dinst y = nfA A r y σ := by
  simp only [nfA, Tm.dinst, Tm.dsubst, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · exact I_shift_inst0 r y
  · rfl
  · exact I_shift_inst0 _ y

theorem nfA_line_eq (A : Tm) (r : I) (σ : ISub k' k) :
    (A.isub σ.up.up).subst .var (consI r.shift (consI (.var 0) fun n => .var (n + 1))) =
      A.subst .var (consI r.shift (consI (.var 0) fun n => (σ.τ n).shift)) := by
  simp only [Tm.isub, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · rfl
  · rfl
  · show ((σ.τ i).shift.shift).subst _ = _
    rw [I_shift_subst, I_shift_subst]; exact (I_add1 _).symm ▸ rfl

theorem nfA_sys_type (A : Tm) (r : I) (σ : ISub k' k) {k'' : ℕ} (y : I) (hy : y.Scoped k'') (σ' : ISub k'' k') :
    (((A.subst .var (consI r.shift (consI (.var 0) fun n => (σ.τ n).shift))).dsubst
      (Tm.bind2 (.or (.var 1) (.var 0)))).dinst .zero).isub (ISub.cons y hy σ') =
      nfA A (r.subst σ'.τ) (.or y .zero) (σ.comp σ') := by
  simp only [nfA, Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]
  refine subst_congr (fun _ => rfl) (fun i => ?_) A
  rcases i with _ | _ | i
  · show ((r.shift.subst (Tm.bind2 _)).subst (I.inst0 .zero)).subst _ = _
    rw [I_shift_subst, I_add2', I_shift_inst0, I_shift_cons]; rfl
  · rfl
  · show ((((σ.τ i).shift).subst (Tm.bind2 _)).subst (I.inst0 .zero)).subst _ = _
    rw [I_shift_subst, I_add2', I_shift_inst0, I_shift_cons]; rfl


variable (hW : WfSig S)
include hW

theorem tyEq_dinst_ieq {A : Tm} {l : ℕ} (hA : HasTy0 S (k + 1) .one [] A (.univ l)) (ρ : ISub k' k) {x1 x2 : I}
    (h1 : x1.Scoped k') (h2 : x2.Scoped k') (he : I.Eq x1 x2) :
    TyEq S k' ((A.isub ρ.up).dinst x1) ((A.isub ρ.up).dinst x2) :=
  tyEq_ieq hW hA (τ1 := fun i => (ρ.up.τ i).subst (I.inst0 x1)) (τ2 := fun i => (ρ.up.τ i).subst (I.inst0 x2))
    (fun i hi => I.scoped_subst (ρ.up.sc i hi) (fun j hj => by rcases j with _ | j <;> simp [I.inst0, I.Scoped] <;> omega))
    (fun i hi => I.scoped_subst (ρ.up.sc i hi) (fun j hj => by rcases j with _ | j <;> simp [I.inst0, I.Scoped] <;> omega))
    (fun i hi => by
      rcases i with _ | i
      · exact he
      · show I.Eq (((ρ.τ i).shift).subst (I.inst0 x1)) (((ρ.τ i).shift).subst (I.inst0 x2))
        rw [I_shift_inst0, I_shift_inst0]; exact I_eq_refl _)
    (isub_dinst_eq _ _ _) (isub_dinst_eq _ _ _)

theorem kanH_path {A a b : Tm} {l : ℕ} (hpath : HasTy S k .one [] (.path A a b) (.univ l))
    (hA : ∀ k' (ρ : ISub k' (k + 1)), KanH S k' (A.isub ρ))
    (ha : RE S k (A.dinst .zero) a) (hb : RE S k (A.dinst .one) b) : KanH S k (.path A a b) := by
  have hS := sigClosed_of_wfSig hW
  have hAt := HasTy0.pathLine hS (spec_to_minimal hW hpath)
  intro φ u p0 hty hu hp0
  obtain ⟨-, ⟨-, hφ, -, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hty) rfl
  have e := EqTm.hcompPath hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  refine RE_path_intro hW hpath (HasTy.eqR e) fun k' σ r hr => ?_
  obtain ⟨t, ht, htr⟩ := hcompPath_body (A.isub σ.up) (a.isub σ) (b.isub σ) (u.isub σ.up) (p0.isub σ) (φ.subst σ.τ) r
  have hf := HasTy.isubS hW (HasTy.eqR e) σ
  rw [isub_hcompPath, ht, isub_path] at hf
  rw [isub_hcompPath, ht]
  have hβ := EqTm.pathBeta (HasTy.papp hf hr)
  rw [htr] at hβ
  have KH := hA k' (ISub.cons r hr σ)
  rw [← isub_up_dinst _ σ r hr] at KH
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm hβ)
  refine KH _ _ _ (HasTy.eqR hβ) (fun k'' σ' r' hr' hh => ?_) ?_
  · rw [isub_up_dinst _ σ' r' hr']
    have h0 := spec_to_minimal hW (HasTy.eqR hβ)
    obtain ⟨-, ⟨-, hψ, htube, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) h0 rfl
    have hT := HasTy0.isub hS (Ψ' := k'') (Φ' := .one) (τ := (ISub.cons r' hr' σ').τ) htube
      (fun i hi => (ISub.cons r' hr' σ').sc i hi)
      (ent_cof_cons hW hψ r' hr' σ' hh)
      (Wf0.nil trivial)
    have hT' := minimal_to_spec hT
    rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons] at hT'
    have hrs : (r.subst σ'.τ).Scoped k'' := I.scoped_subst hr σ'.sc
    have hTy : ((A.isub σ.up).dinst r).isub σ' = (A.isub (σ.comp σ').up).dinst (r.subst σ'.τ) := by
      rw [isub_dinst, Tm.isub_isub, ISub.up_comp]
    rw [hTy] at hT' ⊢
    rcases holds_or hh with h1 | h23
    · have e := EqTm.splitL (by
        show I.Entails .one ((φ.subst σ.τ).shift.subst (ISub.cons r' hr' σ').τ)
        rw [I_shift_cons]
        exact entails_of_holds (I.scoped_subst (I.scoped_subst hφ σ.sc) σ'.sc) h1) hT'
      have h2 := hu k'' (σ.comp σ') r' hr' (by rw [I_subst_comp]; exact h1)
      rw [isub_path] at h2
      have h3 := RE_path_elim hW h2 (r.subst σ'.τ) hrs
      refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
      show RE S k'' _ (Tm.papp ((u.isub σ.up).isub (ISub.cons r' hr' σ')) (r.shift.subst (ISub.cons r' hr' σ').τ))
      rw [isub_isub_up_cons, I_shift_cons]
      exact h3
    · have hor : I.Entails .one ((I.or (.neg r.shift) r.shift).subst (ISub.cons r' hr' σ').τ) := by
        show I.Entails .one (I.or (.neg (r.shift.subst (ISub.cons r' hr' σ').τ)) (r.shift.subst (ISub.cons r' hr' σ').τ))
        rw [I_shift_cons]
        exact entails_of_holds (show (I.or (.neg (r.subst σ'.τ)) (r.subst σ'.τ)).Scoped k'' from ⟨hrs, hrs⟩) h23
      have e1 := EqTm.splitR hor hT'
      rcases holds_or h23 with h2 | h3
      · have e2 := EqTm.splitL (by
          show I.Entails .one (.neg (r.shift.subst (ISub.cons r' hr' σ').τ))
          rw [I_shift_cons]; exact entails_of_holds (show (I.neg (r.subst σ'.τ)).Scoped k'' from hrs) h2)
          (HasTy.eqR e1)
        have h4 := ha.isub hW (σ.comp σ')
        rw [isub_dinst] at h4
        have h5 := h4.conv_ty hW (tyEq_dinst_ieq hW hAt (σ.comp σ') trivial hrs
          (I_eq_symm (ieq_zero_of_holds_neg hrs h2)))
        refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm (EqTm.trans e1 e2))
        show RE S k'' _ ((a.isub σ).dshift.isub (ISub.cons r' hr' σ'))
        rw [dshift_isub_cons, Tm.isub_isub]; exact h5
      · have e2 := EqTm.splitR (by
          show I.Entails .one (r.shift.subst (ISub.cons r' hr' σ').τ)
          rw [I_shift_cons]; exact entails_of_holds hrs h3)
          (HasTy.eqR e1)
        have h4 := hb.isub hW (σ.comp σ')
        rw [isub_dinst] at h4
        have h5 := h4.conv_ty hW (tyEq_dinst_ieq hW hAt (σ.comp σ') trivial hrs
          (I_eq_symm (ieq_one_of_holds hrs h3)))
        refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm (EqTm.trans e1 e2))
        show RE S k'' _ ((b.isub σ).dshift.isub (ISub.cons r' hr' σ'))
        rw [dshift_isub_cons, Tm.isub_isub]; exact h5
  · have h1 := hp0.isub hW σ
    rw [isub_path] at h1
    exact RE_path_elim hW h1 r hr

theorem tyEq_nfA {A : Tm} {l : ℕ} (hA : HasTy0 S (k + 2) .one [] A (.univ l)) (ρ : ISub k' k) {x x' y y' : I}
    (hx : x.Scoped k') (hx' : x'.Scoped k') (hy : y.Scoped k') (hy' : y'.Scoped k') (ex : I.Eq x x') (ey : I.Eq y y') :
    TyEq S k' (nfA A x y ρ) (nfA A x' y' ρ) :=
  tyEq_ieq hW hA (τ1 := consI x (consI y ρ.τ)) (τ2 := consI x' (consI y' ρ.τ))
    (fun i hi => by rcases i with _ | _ | i
                    · exact hx
                    · exact hy
                    · exact ρ.sc i (by omega))
    (fun i hi => by rcases i with _ | _ | i
                    · exact hx'
                    · exact hy'
                    · exact ρ.sc i (by omega))
    (fun i hi => by rcases i with _ | _ | i
                    · exact ex
                    · exact ey
                    · exact I_eq_refl _) rfl rfl

omit hW in
theorem kanAll_isub {n n' : ℕ} {A : Tm} (h : KanAll S n A) (ρ : ISub n' n) : KanAll S n' (A.isub ρ) :=
  ⟨fun k' ρ' => by rw [Tm.isub_isub]; exact h.1 k' (ρ.comp ρ'), fun k' ρ' => by rw [Tm.isub_isub]; exact h.2 k' (ρ.comp ρ')⟩

theorem kanT_path {A a b : Tm} {l : ℕ} (hpath : HasTy S (k + 1) .one [] (.path A a b) (.univ l))
    (hA : KanAll S (k + 2) A)
    (ha : ∀ k' (σ : ISub k' (k + 1)), RE S k' ((A.isub σ.up).dinst .zero) (a.isub σ))
    (hb : ∀ k' (σ : ISub k' (k + 1)), RE S k' ((A.isub σ.up).dinst .one) (b.isub σ)) :
    KanT S k (.path A a b) := by
  have hS := sigClosed_of_wfSig hW
  intro φ p0 hty hp0
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hL, hφ, hc, -⟩, -⟩ := gen_transpF (Φ := .one) (Γ := []) h0 rfl
  have hAt : HasTy0 S (k + 2) .one [] A (.univ l0) := HasTy0.pathLine hS hL
  have hAc : A.closedB 0 (k + 2) = true := closed_ty hAt
  have e := EqTm.transpPath hty
  refine RE.conv hW ?_ (TyEq.refl _) (EqTm.symm e)
  have hpath1 := minimal_to_spec (HasTy0.dsubst hS (Φ := .one) (Γ := []) hL (r := .one) trivial)
  refine RE_path_intro hW hpath1 (HasTy.eqR e) fun k' σ r hr => ?_
  obtain ⟨t, ht, htr⟩ := transpPath_body (A.isub σ.up.up) (a.isub σ.up) (b.isub σ.up) (p0.isub σ) (φ.subst σ.τ) r
  have hf := HasTy.isubS hW (HasTy.eqR e) σ
  rw [isub_transpPath, ht] at hf
  rw [isub_transpPath, ht]
  have hβ := EqTm.pathBeta (HasTy.papp hf hr)
  rw [htr, nfA_line_eq] at hβ
  simp only [dupvar_subst] at hβ ⊢
  rw [show Tm.subst Tm.var (I.up σ.τ) (Tm.subst Tm.var (I.up (I.inst0 .one)) A) =
    (A.subst .var (I.up (I.inst0 .one))).isub σ.up from rfl] at hβ
  rw [nfA_end A r .one (.inr rfl) σ] at hβ ⊢
  -- the line of the composition
  let τC : ℕ → I := consI r.shift (consI (.var 0) fun n => (σ.τ n).shift)
  have hsc : ∀ x < k + 2, (τC x).Scoped (k' + 1) := fun x hx => by
    rcases x with _ | _ | x
    · exact I.scoped_shift hr
    · show 0 < k' + 1; omega
    · exact I.scoped_shift (σ.sc x (by omega))
  have KAC := kanAll_isub hA (ISub.ofFun (k + 2) τC hsc)
  rw [isub_ofFun hAc] at KAC
  have hβT := HasTy.eqR hβ
  rw [← nfA_line_dinst A r σ .one] at hβT
  refine (RE_comp hW KAC hβT (fun k'' σ'' r'' hr'' hh => ?_) ?_).conv hW
    (by rw [nfA_line_dinst]; exact TyEq.refl _) (EqTm.symm hβ)
  · rw [isub_up_dinst _ σ'' r'' hr'', isub_up_dinst _ σ'' r'' hr'', nfA_line_isub]
    have hρ := σ.comp σ''
    have hrs : (r.subst σ''.τ).Scoped k'' := I.scoped_subst hr σ''.sc
    -- the typing of the system
    obtain ⟨-, ⟨-, hψ, htube, -, -⟩, -⟩ := gen_hcomp (Φ := .one) (Γ := []) (spec_to_minimal hW hβT) rfl
    obtain ⟨-, ⟨-, -, -, hsys⟩, -⟩ := gen_transpF htube rfl
    have hT := minimal_to_spec (HasTy0.isub hS (Ψ' := k'') (Φ' := .one) (τ := (ISub.cons r'' hr'' σ'').τ) hsys
      (fun i hi => (ISub.cons r'' hr'' σ'').sc i hi) (ent_cof_cons hW hψ r'' hr'' σ'' hh) (Wf0.nil trivial))
    rw [← isub_eq_subst, ← isub_eq_subst, nfA_sys_type] at hT
    have hT' := HasTy.tyConv hT (tyEq_nfA hW hAt (σ.comp σ'') hrs hrs ⟨hr'', trivial⟩ hr'' (I_eq_refl _)
      (I_eq_or_zero_r r''))
    have hφρ : φ.subst (σ.comp σ'').τ = (φ.subst σ.τ).subst σ''.τ := I_subst_comp φ σ σ''
    rcases holds_or hh with h1 | h23
    · have e := EqTm.splitL (by
        show I.Entails .one ((φ.subst σ.τ).shift.subst (ISub.cons r'' hr'' σ'').τ)
        rw [I_shift_cons]; exact entails_of_holds (I.scoped_subst (I.scoped_subst hφ σ.sc) σ''.sc) h1) hT'
      have ec := EqTm0.isub hS (Ψ' := k'') (Φ' := .one) (τ := (ISub.cons r'' hr'' (σ.comp σ'')).τ) hc
        (fun i hi => (ISub.cons r'' hr'' (σ.comp σ'')).sc i hi)
        (ent_cof_cons hW hφ r'' hr'' (σ.comp σ'') (by rw [hφρ]; exact h1)) (Wf0.nil trivial)
      rw [← isub_eq_subst, ← isub_eq_subst, dshift_isub_cons] at ec
      have ej := minimal_to_spec_eq (EqTm0.pathInjLine ec hrs)
      simp only [dupvar_subst] at ej
      rw [show Tm.subst Tm.var (I.up (ISub.cons r'' hr'' (σ.comp σ'')).τ) A = A.isub (ISub.cons r'' hr'' (σ.comp σ'')).up
          from rfl, nfA_cons,
        show Tm.subst Tm.var (I.up (σ.comp σ'').τ) (A.subst .var (I.up (I.inst0 .zero))) =
          (A.subst .var (I.up (I.inst0 .zero))).isub (σ.comp σ'').up from rfl,
        nfA_end A _ .zero (.inl rfl)] at ej
      have h2 := RE_path_elim hW (L := (A.subst .var (I.up (I.inst0 .zero))).isub (σ.comp σ'').up)
        (hp0.isub hW (σ.comp σ'')) (r.subst σ''.τ) hrs
      rw [nfA_end A _ .zero (.inl rfl)] at h2
      have eq : Tm.subst Tm.var (ISub.cons r'' hr'' σ'').τ ((p0.isub σ).dshift.papp r.shift) =
          Tm.papp (p0.isub (σ.comp σ'')) (r.subst σ''.τ) := by
        show Tm.papp ((p0.isub σ).dshift.isub (ISub.cons r'' hr'' σ'')) (r.shift.subst (ISub.cons r'' hr'' σ'').τ) = _
        rw [dshift_isub_cons, Tm.isub_isub, I_shift_cons]
      rw [← eq] at h2
      exact h2.conv hW (.inr ⟨l0, EqTm.symm ej⟩) (EqTm.symm e)
    · have hor : I.Entails .one ((I.or (.neg r.shift) r.shift).subst (ISub.cons r'' hr'' σ'').τ) := by
        show I.Entails .one (I.or (.neg (r.shift.subst (ISub.cons r'' hr'' σ'').τ)) (r.shift.subst (ISub.cons r'' hr'' σ'').τ))
        rw [I_shift_cons]
        exact entails_of_holds (show (I.or (.neg (r.subst σ''.τ)) (r.subst σ''.τ)).Scoped k'' from ⟨hrs, hrs⟩) h23
      have e1 := EqTm.splitR hor hT'
      have eqe : ∀ x : Tm, (x.isub σ.up).isub (ISub.cons r'' hr'' σ'') = x.isub (ISub.cons r'' hr'' (σ.comp σ'')) := by
        intro x; rw [isub_isub_up_cons, isub_up_dinst]
      rcases holds_or h23 with h2 | h3
      · have e2 := EqTm.splitL (by
          show I.Entails .one (.neg (r.shift.subst (ISub.cons r'' hr'' σ'').τ))
          rw [I_shift_cons]; exact entails_of_holds (show (I.neg (r.subst σ''.τ)).Scoped k'' from hrs) h2)
          (HasTy.eqR e1)
        have h4 := ha k'' (ISub.cons r'' hr'' (σ.comp σ''))
        rw [nfA_cons, ← eqe] at h4
        have h5 := h4.conv_ty hW (tyEq_nfA hW hAt (σ.comp σ'') trivial hrs hr'' hr''
          (I_eq_symm (ieq_zero_of_holds_neg hrs h2)) (I_eq_refl _))
        exact h5.conv hW (TyEq.refl _) (EqTm.symm (EqTm.trans e1 e2))
      · have e2 := EqTm.splitR (by
          show I.Entails .one (r.shift.subst (ISub.cons r'' hr'' σ'').τ)
          rw [I_shift_cons]; exact entails_of_holds hrs h3)
          (HasTy.eqR e1)
        have h4 := hb k'' (ISub.cons r'' hr'' (σ.comp σ''))
        rw [nfA_cons, ← eqe] at h4
        have h5 := h4.conv_ty hW (tyEq_nfA hW hAt (σ.comp σ'') trivial hrs hr'' hr''
          (I_eq_symm (ieq_one_of_holds hrs h3)) (I_eq_refl _))
        exact h5.conv hW (TyEq.refl _) (EqTm.symm (EqTm.trans e1 e2))
  · have h1 := hp0.isub hW σ
    have h2 := RE_path_elim hW (L := (A.subst .var (I.up (I.inst0 .zero))).isub σ.up) h1 r hr
    rw [nfA_end A r .zero (.inl rfl) σ] at h2
    rw [nfA_line_dinst]; exact h2

end

end Model.Canon
