import Model.Whnf.Kan2DataHITBT

/-!
# Transport along lines of higher inductive types: the motives and the stage cases

As for inductive types without path constructors (`Kan2DataTInd.lean`), elements related at the start of a
literal line of a higher inductive type are transported along related lines by induction on their
relation. The motives: `TM1H` (for the relation, at all restrictions: the transports are related, `TM1`, also for the left
element with itself, and the transport of the left element is related to the contractum of the transport of its normal form, `TR`),
and `TM2H` (for one stage: the contracta `tRedF` of related normal forms are related, `TMc`, and the motive
holds for the immediate subterms, `TMch`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The transport of the left element is related to the contractum of the transport of its normal form. -/
def TR (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A x : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d ((P.dinst .zero).isub ρ) →
  ∀ k3 (σ : ISub k3 k1) (y : I) (hy : y.Scoped (k3 + 1)),
    I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero →
  ∀ (ψ : I), ψ.Scoped k3 → ¬ I.Entails .one ψ →
    LineConst S k3 ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ →
    HasTy S k3 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ))
      (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one) →
  ∀ w, RedW S (x.isub σ) w →
    RE2 S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one)
      (.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ))
      (tRedF d D (P.isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ w)

/-- The transports of the left element along the lines at `I.Eq`-equal points are related. -/
def TM1s (S : Sig) (d K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A x : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d ((P.dinst .zero).isub ρ) →
  ∀ k3 (σ : ISub k3 k1) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
    I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero →
    KanT2At S k3 ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail))
      ((Tm.data d P).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) (x.isub σ) (x.isub σ)

/-- The motive at the relation of the start of a line. -/
def TM1H (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A x x' : Tm) : Prop :=
  TM1 S d K P k1 g A x x' ∧ TM1s S d K P k1 g A x ∧ TR S d D K P k1 g A x

/-- The contracta of the transports of related normal forms are related. -/
def TMc (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A v v' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d ((P.dinst .zero).isub ρ) → ∀ Q, Rob S d K P Q →
  ∀ (y y' : I) (hy : y.Scoped (k1 + 1)) (hy' : y'.Scoped (k1 + 1)), I.Eq y y' →
    I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k1)).τ) .zero →
  ∀ (ψ ψ' : I), ψ.Scoped k1 → I.Entails ψ ψ' → I.Entails ψ' ψ →
    LineConst S k1 ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ →
    HasTy S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ v)
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) →
    HasTy S k1 .one [] (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' v')
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) →
    EqTm S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ v)
      (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' v')
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) →
  ∀ w w', RedE S k1 A v w → RedE S k1 A v' w' →
    RE2 S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one)
      (tRedF d D (P.isub (ISub.cons y hy ρ.up.tail)) ψ w) (tRedF d D (Q.isub (ISub.cons y' hy' ρ.up.tail)) ψ' w')

/-- The motive at the immediate subterms of related normal forms. -/
def TMch (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A v v' : Tm) : Prop :=
  ∀ ps, RedT S k1 A (.data d ps) →
  (∀ (c : ℕ) (C : Ctor) (q : Tm) (X : List Tm) (rs : List I) (q' : Tm) (X' : List Tm) (rs' : List I),
    D.ctors[c]? = some C → RedE S k1 A v (.con d c q (Tm.ofList X) rs) →
    RedE S k1 A v' (.con d c q' (Tm.ofList X') rs') →
    ∀ j (hj : j < X.length) (hj' : j < X'.length), C.isRec j = true → TM1H S d D K P k1 g (.data d ps) X[j] X'[j]) ∧
  (∀ (qs : Tm) (χ : I) (u a qs' : Tm) (χ' : I) (u' a' : Tm),
    RedE S k1 A v (.hcomp (.data d qs) χ u a) → RedE S k1 A v' (.hcomp (.data d qs') χ' u' a') →
    TM1H S d D K P k1 g (.data d ps) a a' ∧
    (∀ k' (σ : ISub k' k1) (r : I), r.Scoped k' → (ival (idEnv k') (χ.subst σ.τ)).holds →
      TM1H S d D K P k' (g.comp σ.hom) ((Tm.data d ps).isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r)) ∧
    (∀ k' (σ : ISub k' k1), (ival (idEnv k') (χ.subst σ.τ)).holds →
      TM1H S d D K P k' (g.comp σ.hom) ((Tm.data d ps).isub σ) ((u.isub σ.up).dinst .zero) (a.isub σ)) ∧
    (∀ k' (σ : ISub k' k1), (ival (idEnv k') (χ'.subst σ.τ)).holds →
      TM1H S d D K P k' (g.comp σ.hom) ((Tm.data d ps).isub σ) ((u'.isub σ.up).dinst .zero) (a'.isub σ)))

/-- The motive at one stage. -/
def TM2H (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A v v' : Tm) : Prop :=
  TMc S d D K P k1 g A v v' ∧ TMch S d D K P k1 g A v v'

/-- A composition at an inductive type, retyped at equal parameters. -/
theorem hcomp_data_retype (hW : WfSig S) {d : ℕ} {qs p u a : Tm} {χ : I} {l : ℕ}
    (h : HasTy S k .one [] (.hcomp (.data d qs) χ u a) (.data d p)) (hp : HasTy S k .one [] (.data d p) (.univ l)) :
    HasTy S k .one [] (.hcomp (.data d p) χ u a) (.data d p) ∧
    EqTm S k .one [] (.hcomp (.data d qs) χ u a) (.hcomp (.data d p) χ u a) (.data d p) := by
  obtain ⟨l1, ⟨hX0, -, -, -, -⟩, ch⟩ := gen_hcomp (spec_to_minimal hW h) rfl
  obtain ⟨m, e⟩ := chain_eq hW ch hX0 rfl (spec_to_minimal hW hp) (fun k h => by cases h)
  have e' : TyEq S k (.data d qs) (.data d p) := .inr ⟨m, minimal_to_spec_eq e⟩
  obtain ⟨h1, h2⟩ := hcomp_retype hW h e'
  exact ⟨h1.tyConv e', h2.tyConv e'⟩

section ind
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hyp : HITHyp2 S (d + 1)) (hp : D.params ≠ []) {K : ℕ} {P : Tm} (hP : HasTy S (K + 1) .one [] (.data d P) (.univ D.level))

  (hRL : Rob S d K P P)
include hW hD hH hyp hp hP  hRL

/-- The constructor case: the `transpCon` contracta of related constructors are related. -/
theorem tm2_conH {k1 : ℕ} {g : Hom k1 K} {A t t' ps qs qs' : Tm} {c : ℕ} {C : Ctor} {args args' : List Tm}
    {rs rs' : List I}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K (P.dinst .zero)) (Hom.id K))
      (dataP2 S (ΘK S D d K (P.dinst .zero)) (Hom.id K)) k1 g A t t')
    (hC : (dataD S d).ctors[c]? = some C) (hA : RedT S k1 A (.data d ps))
    (ht : RedE S k1 A t (.con d c qs (Tm.ofList args) rs)) (ht' : RedE S k1 A t' (.con d c qs' (Tm.ofList args') rs'))
    (hrs : rs.length = C.dims) (hrs' : rs'.length = C.dims)
    (hreq : ∀ (i : ℕ) (r r' : I), rs[i]? = some r → rs'[i]? = some r' → I.Eq r r')
    (hl : args.length = C.args.length) (hl' : args'.length = C.args.length)
    (ihrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      TM1H S d D K P k1 g (.data d ps) args[j] args'[j]) :
    TM2H S d D K P k1 g A t t' := by
  have hdD := dataD_eq hW hD
  have hC' : D.ctors[c]? = some C := hdD ▸ hC
  refine ⟨?_, fun ps2 hA2 => ⟨?_, ?_⟩⟩
  rotate_left
  · intro c2 C2 q2 X2 rs2 q2' X2' rs2' hC2 hr hr' j hj hj' hrj
    have e1 := RedW.unique hr.1 ht.1
    have e2 := RedW.unique hr'.1 ht'.1
    simp only [Tm.con.injEq] at e1 e2
    obtain ⟨-, rfl, -, eX, -⟩ := e1
    obtain ⟨-, -, -, eX', -⟩ := e2
    have eX1 := congrArg Tm.toList eX
    have eX1' := congrArg Tm.toList eX'
    simp only [toList_ofList] at eX1 eX1'
    subst X2 X2'
    rw [hC'] at hC2; cases hC2
    have ep := RedW.unique hA2.1 hA.1
    simp only [Tm.data.injEq] at ep
    obtain ⟨-, rfl⟩ := ep
    exact ihrec j hj hj' hrj
  · intro qs2 χ u a qs2' χ' u' a' hr _
    have := RedW.unique hr.1 ht.1
    cases this
  intro ρ hg hAe Q hQ y y' hy hy' hE h0 ψ ψ' hψs h12 h21 LC hty hty' heq w w' hr hr'
  subst hg hAe
  obtain rfl := RedW.unique hr.1 ht.1
  obtain rfl := RedW.unique hr'.1 ht'.1
  rw [tRedF_con d D _ ψ hC', tRedF_con d D _ ψ' hC']
  have hP0 := P0_ty hW hD hp hP  hRL
  have hP0P0 := P0_rt2 hW hD hp hP  hRL
  obtain rfl : ps = (P.dinst .zero).isub ρ := redT_data_eq (Θ := ΘK S D d K (P.dinst .zero)) hA
  -- the arguments, related at the start of the line
  have hZ : ∀ i (hi : i < C.args.length), RE2 S k1 ((C.argTy d D.params.length i).substList
      ((args.take i).reverse ++ ((P.dinst .zero).isub ρ).toList.reverse)) (args.getD i .abort) (args'.getD i .abort) := by
    rcases DR2At_cases hW hD hP0 hP0P0 ρ hat with
      ⟨c3, C3, q3, Z, rs3, q3', Z', rs3', hC3, hZl, hZ'l, hr3, hr3', -, -, -, -, -, hZ⟩ |
      ⟨_, _, _, _, _, _, _, _, -, hr3, -⟩
    · have f1 := RedW.unique hr3.1 hr.1
      have f2 := RedW.unique hr3'.1 hr'.1
      simp only [Tm.con.injEq] at f1 f2
      obtain ⟨-, rfl, -, eZ, -⟩ := f1
      obtain ⟨-, -, -, eZ', -⟩ := f2
      have eZ1 := congrArg Tm.toList eZ
      have eZ1' := congrArg Tm.toList eZ'
      simp only [toList_ofList] at eZ1 eZ1'
      subst Z Z'
      rw [hC'] at hC3; cases hC3
      exact hZ
    · have := RedW.unique hr3.1 hr.1
      cases this
  have hself := args_self hW hD hP0 hP0P0 ρ hC' hl hl' hZ
  have hrsF : List.Forall₂ I.Eq rs rs' := forall2_ieq (hrs.trans hrs'.symm) hreq
  -- the line and its start
  have hPc := data_closed hW hD hP
  have hXP0 : TyCode K (semK S K (.data d (P.dinst .zero))) := tyCode_of_univ hW hP0
  have hP0ρ : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((P.dinst .zero).isub ρ)) := RT2.isub hW hXP0 hP0P0 ρ
  have hPL0 := line_dinst hW hD hp hP  hRL ρ y hy .zero trivial
  have rel0 : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero)) := by
    rw [P0_isub hW hD hp hP  hRL, hPL0]
    exact hRL k1 ρ .zero _ trivial _ (I_eq_symm h0)
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the arguments, related at the start of the line
  have hargs0 : ∀ i (hi : i < C.args.length), RE2 S k1 ((C.argTy d D.params.length i).substList
      ((args.take i).reverse ++ ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero).toList.reverse))
      (args.getD i .abort) (args'.getD i .abort) := by
    intro i hi
    have T := argTy_rt2' hW hD (HasTy.isubS hW hP0 ρ) hP0ρ rel0 hC' hi (A := args.take i) (B := args.take i)
      (by simp; omega) (by simp; omega) (fun l hl0 => by
        rw [List.take_take, Nat.min_eq_left hl0.le, getD_take_lt hl0]
        exact (hself l (by omega)).2.1)
    exact RE2.conv hW T (hZ i hi)
  -- the transports of the normal forms
  have hQL0 : (Q.isub (ISub.cons y' hy' ρ.up.tail)).dinst .zero = Q.isub (ISub.cons
      (y'.subst (ISub.cons .zero trivial (ISub.id k1)).τ) (I.scoped_subst hy' (ISub.cons .zero trivial (ISub.id k1)).sc) ρ) := by
    have hc : (Q.isub (ISub.cons y' hy' ρ.up.tail)).closedB 0 (k1 + 1) = true := by
      obtain ⟨l', ⟨hLt', -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
      have := closed_ty hLt'; simpa [Tm.closedB] using this
    rw [← isub_cons_id_of_closed hc .zero trivial, Tm.isub_isub, line_comp, ISub.comp_id]
  have hy'0 : I.Eq (y'.subst (ISub.cons .zero trivial (ISub.id k1)).τ) .zero :=
    I_eq_trans (I_eq_subst (I_eq_symm hE) _) h0
  have rel0' : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((Q.isub (ISub.cons y' hy' ρ.up.tail)).dinst .zero)) := by
    rw [P0_isub hW hD hp hP  hRL, hQL0]
    exact hQ k1 ρ .zero _ trivial _ (I_eq_symm hy'0)
  have eb := hr.2.tyConv (tyB rel0)
  have eb' := hr'.2.tyConv (tyB rel0')
  have rb := transp_rebase hW hty eb
  have rb' := transp_rebase hW hty' eb'
  have e1' : TyEq S k1 (((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)).dinst .one)
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) := by
    have hc : (Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).closedB 0 (k1 + 1) = true := by
      obtain ⟨l', ⟨hLt', -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
      exact closed_ty hLt'
    have hcP : (Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).closedB 0 (k1 + 1) = true :=
      closed_of_ty hW (HasTy.isubS hW hP _)
    show TyEq S k1 ((Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).dinst .one)
      ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dinst .one)
    rw [← isub_cons_id_of_closed hc .one trivial, ← isub_cons_id_of_closed hcP .one trivial]
    show TyEq S k1 (Tm.data d ((Q.isub _).isub _)) (Tm.data d ((P.isub _).isub _))
    rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp, ISub.comp_id]
    exact TyEq.symm (tyB (hQ k1 ρ _ _ _ _ (I_eq_subst hE _)))
  -- the end of the line
  have hPθc : (P.isub (ISub.cons y hy ρ.up.tail)).closedB 0 (k1 + 1) = true :=
    data_closed hW hD (HasTy.isubS hW hP (ISub.cons y hy ρ.up.tail))
  have s1 : RT2 S k1 (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .one))
      (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .one)) := by
    have := Rob.line hRL ρ y y hy hy (I_eq_refl _) k1 (ISub.id k1) .one .one trivial trivial (I_eq_refl _)
    rwa [isub_cons_id_of_closed hPθc] at this
  have hd1 : HasTy S k1 .one [] (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .one)) (.univ D.level) :=
    data_whnf_ty hW hD (Comp2_ty_base s1).2.1 ⟨redW_self (step_data d _), TyEq.refl _⟩
  have H : TC S k1 d D (P.isub (ISub.cons y hy ρ.up.tail)) (Q.isub (ISub.cons y' hy' ρ.up.tail)) ψ ψ' _ C _ _
      args args' rs rs' :=
    { hW := hW, hD := hD, hp := hp, hC := hC', hPL := HasTy.isubS hW hP _,
      conR := conR_hit hW hD hH hyp hC' (HasTy.isubS hW hP _) (Rob.line hRL ρ y y hy hy (I_eq_refl _)) hrsF,
      hR := Rob.line hQ ρ y y' hy hy' hE, hRL := Rob.line hRL ρ y y hy hy (I_eq_refl _),
      hφs := hψs, h12 := h12, h21 := h21, hLC := LC, hty := rb.1,
      hty' := rb'.1.tyConv e1', heq := rb.2.symm.trans (heq.trans (rb'.2.tyConv e1')), hargs0 := hargs0,
      hrecT := fun i hi hri k3 τ z z' hz hz' hEz hz0 => by
        have h := (ihrec i (by omega) (by omega) hri).1 ρ rfl rfl Q hQ k3 τ _ _
          (I.scoped_subst hy (ISub.cons z hz τ.up.tail).sc) (I.scoped_subst hy' (ISub.cons z' hz' τ.up.tail).sc)
          (ieq_subst_cons hE hEz hz hz' τ.up.tail) (ieq_zero_comp hy h0 hz hz0 τ)
        rw [getD_eq_get' (show i < args.length by omega),
          getD_eq_get' (show i < args'.length by omega)]
        show KanT2At S k3 (Tm.data d ((P.isub _).isub _)) (Tm.data d ((Q.isub _).isub _)) _ _
        rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp, ISub.comp_up_tail]
        exact h }
  exact H.rel

omit hyp in
/-- The transport induction hypothesis applied to a related pair at one point. -/
theorem tm1h_transp_point {k1 : ℕ} (ρ : ISub k1 K) {Q : Tm} (hQ : Rob S d K P Q)
    (y y' : I) (hy : y.Scoped (k1 + 1)) (hy' : y'.Scoped (k1 + 1)) (hE : I.Eq y y')
    (h0 : I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k1)).τ) .zero)
    (ψ ψ' : I) (h12 : I.Entails ψ ψ') (h21 : I.Entails ψ' ψ)
    (LC : LineConst S k1 ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ)
    {b b' : Tm} (hb : RE2 S k1 (.data d ((P.dinst .zero).isub ρ)) b b')
    (ihb : TM1H S d D K P k1 ρ.hom (.data d ((P.dinst .zero).isub ρ)) b b')
    (ht : HasTy S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ b)
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one))
    (ht' : HasTy S k1 .one [] (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' b')
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one)) :
    RE2 S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one)
      (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ b)
      (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' b') := by
  have K0 := ihb.1 ρ rfl rfl Q hQ k1 (ISub.id k1) y y' hy hy' hE h0
  rw [ISub.comp_id, isub_id_of_closed (closed_of_ty hW (RE2.typed hb).1),
    isub_id_of_closed (closed_of_ty hW (RE2.typed hb).2.1)] at K0
  have rel0 : RT2 S k1 (.data d ((P.dinst .zero).isub ρ))
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .zero) := by
    rw [lineP_dinst hW hD hp hP hRL _ _ _ .zero trivial, P0_isub hW hD hp hP hRL]
    exact hRL k1 ρ .zero _ trivial _ (I_eq_symm h0)
  have eLL : TyEq S (k1 + 1) ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail))
      ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) := by
    have h := Rob.line hQ ρ y y' hy hy' hE (k1 + 1) (ISub.id k1).up.tail (.var 0) (.var 0)
      (show 0 < k1 + 1 by omega) (show 0 < k1 + 1 by omega) (I_eq_refl _)
    have hcP : (P.isub (ISub.cons y hy ρ.up.tail)).closedB 0 (k1 + 1) = true :=
      data_closed hW hD (HasTy.isubS hW hP _)
    have hcQ : (Q.isub (ISub.cons y' hy' ρ.up.tail)).closedB 0 (k1 + 1) = true := by
      have := closed_ty (gen_transpF (spec_to_minimal hW ht') rfl).choose_spec.1.1
      simpa only [Tm.closedB] using this
    rw [ISub.cons_var0_up_tail, isub_up_id_of_closed hcP, isub_up_id_of_closed hcQ] at h
    exact (Comp2_ty_base h).2.2.2.2.2
  exact K0 (Rob.line hQ ρ y y' hy hy' hE) ψ ψ' LC ht ht'
    (eqTm_transp_of hW ht ht' eLL h12 h21 ((RE2.typed hb).2.2.tyConv (Comp2_ty_base rel0).2.2.2.2.2))
    h12 h21 (RE2.conv hW rel0 hb)

omit hyp in
/-- The composition case: the `transpHcomp` contracta of related formal compositions are related. -/
theorem tm2_hcompH {k1 : ℕ} {g : Hom k1 K} {A t t' ps qs qs' u u' a a' : Tm} {χ χ' : I}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K (P.dinst .zero)) (Hom.id K))
      (dataP2 S (ΘK S D d K (P.dinst .zero)) (Hom.id K)) k1 g A t t')
    (hA : RedT S k1 A (.data d ps))
    (ht : RedE S k1 A t (.hcomp (.data d qs) χ u a)) (ht' : RedE S k1 A t' (.hcomp (.data d qs') χ' u' a'))
    (iha : TM1H S d D K P k1 g (.data d ps) a a')
    (ihu : ∀ k' (σ : ISub k' k1) (r : I), r.Scoped k' → (ival (idEnv k') (χ.subst σ.τ)).holds →
      TM1H S d D K P k' (g.comp σ.hom) ((Tm.data d ps).isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r))
    (ihb : ∀ k' (σ : ISub k' k1), (ival (idEnv k') (χ.subst σ.τ)).holds →
      TM1H S d D K P k' (g.comp σ.hom) ((Tm.data d ps).isub σ) ((u.isub σ.up).dinst .zero) (a.isub σ))
    (ihb' : ∀ k' (σ : ISub k' k1), (ival (idEnv k') (χ'.subst σ.τ)).holds →
      TM1H S d D K P k' (g.comp σ.hom) ((Tm.data d ps).isub σ) ((u'.isub σ.up).dinst .zero) (a'.isub σ)) :
    TM2H S d D K P k1 g A t t' := by
  refine ⟨?_, fun ps2 hA2 => ⟨?_, ?_⟩⟩
  rotate_left
  · intro c2 C2 q2 X2 rs2 q2' X2' rs2' hC2 hr
    have := RedW.unique hr.1 ht.1; cases this
  · intro qs2 χ2 u2 a2 qs2' χ2' u2' a2' hr hr'
    have e1 := RedW.unique hr.1 ht.1
    have e2 := RedW.unique hr'.1 ht'.1
    simp only [Tm.hcomp.injEq] at e1 e2
    obtain ⟨-, rfl, rfl, rfl⟩ := e1
    obtain ⟨-, rfl, rfl, rfl⟩ := e2
    have ep := RedW.unique hA2.1 hA.1
    simp only [Tm.data.injEq] at ep
    obtain ⟨-, rfl⟩ := ep
    exact ⟨iha, ihu, ihb, ihb'⟩
  intro ρ hg hAe Q hQ y y' hy hy' hE h0 ψ ψ' hψs h12 h21 LC hty hty' heq w w' hr hr'
  subst hg hAe
  obtain rfl := RedW.unique hr.1 ht.1
  obtain rfl := RedW.unique hr'.1 ht'.1
  rw [tRedF_hcomp, tRedF_hcomp]
  have hdD := dataD_eq hW hD
  have hP0 := P0_ty hW hD hp hP  hRL
  have hP0P0 := P0_rt2 hW hD hp hP  hRL
  have hPP1 := PP1 hW hD hp hP  hRL
  have hPc := data_closed hW hD hP
  obtain rfl : ps = (P.dinst .zero).isub ρ := redT_data_eq (Θ := ΘK S D d K (P.dinst .zero)) hA
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  -- the relations of the bases and the tubes
  obtain ⟨haa3, hu3, hb3, hb3'⟩ : RE2 S k1 (.data d ((P.dinst .zero).isub ρ)) a a' ∧
      (∀ k4 (σ : ISub k4 k1) (r : I), r.Scoped k4 → (ival (idEnv k4) (χ.subst σ.τ)).holds →
        RE2 S k4 (.data d ((P.dinst .zero).isub (ρ.comp σ))) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r)) ∧
      HcompBnd2 S k1 (.data d ((P.dinst .zero).isub ρ)) χ u a ∧
      HcompBnd2 S k1 (.data d ((P.dinst .zero).isub ρ)) χ' u' a' := by
    rcases DR2At_cases hW hD hP0 hP0P0 ρ hat with
      ⟨_, _, _, _, _, _, _, _, -, -, -, hr3, -⟩ |
      ⟨qs3, χ3, u3, a3, qs3', χ3', u3', a3', -, hr3, hr3', -, -, -, -, haa3, hu3, hb3, hb3'⟩
    · have := RedW.unique hr3.1 ht.1; cases this
    · have e1 := RedW.unique hr3.1 ht.1
      have e2 := RedW.unique hr3'.1 ht'.1
      simp only [Tm.hcomp.injEq] at e1 e2
      obtain ⟨-, rfl, rfl, rfl⟩ := e1
      obtain ⟨-, rfl, rfl, rfl⟩ := e2
      exact ⟨haa3, hu3, hb3, hb3'⟩
  have h123 : I.Entails χ χ' ∧ I.Entails χ' χ := by
    rcases DR2At_cases hW hD hP0 hP0P0 ρ hat with
      ⟨_, _, _, _, _, _, _, _, -, -, -, hr3, -⟩ |
      ⟨qs3, χ3, u3, a3, qs3', χ3', u3', a3', -, hr3, hr3', -, -, h1, h2, -, -⟩
    · have := RedW.unique hr3.1 ht.1; cases this
    · have e1 := RedW.unique hr3.1 ht.1
      have e2 := RedW.unique hr3'.1 ht'.1
      simp only [Tm.hcomp.injEq] at e1 e2
      obtain ⟨-, rfl, -, -⟩ := e1
      obtain ⟨-, rfl, -, -⟩ := e2
      exact ⟨h1, h2⟩
  -- the starts and ends of the lines
  have hXP0 : TyCode K (semK S K (.data d (P.dinst .zero))) := tyCode_of_univ hW hP0
  have hPL0 := line_dinst hW hD hp hP  hRL ρ y hy .zero trivial
  have rel0 : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero)) := by
    rw [P0_isub hW hD hp hP  hRL, hPL0]
    exact hRL k1 ρ .zero _ trivial _ (I_eq_symm h0)
  have hQc : (Q.isub (ISub.cons y' hy' ρ.up.tail)).closedB 0 (k1 + 1) = true := by
    obtain ⟨l', ⟨hLt', -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
    have := closed_ty hLt'; simpa [Tm.closedB] using this
  have hQL0 : (Q.isub (ISub.cons y' hy' ρ.up.tail)).dinst .zero = Q.isub (ISub.cons
      (y'.subst (ISub.cons .zero trivial (ISub.id k1)).τ) (I.scoped_subst hy' (ISub.cons .zero trivial (ISub.id k1)).sc) ρ) := by
    rw [← isub_cons_id_of_closed hQc .zero trivial, Tm.isub_isub, line_comp, ISub.comp_id]
  have hy'0 : I.Eq (y'.subst (ISub.cons .zero trivial (ISub.id k1)).τ) .zero :=
    I_eq_trans (I_eq_subst (I_eq_symm hE) _) h0
  have rel0' : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((Q.isub (ISub.cons y' hy' ρ.up.tail)).dinst .zero)) := by
    rw [P0_isub hW hD hp hP  hRL, hQL0]
    exact hQ k1 ρ .zero _ trivial _ (I_eq_symm hy'0)
  have hPθc : (P.isub (ISub.cons y hy ρ.up.tail)).closedB 0 (k1 + 1) = true :=
    data_closed hW hD (HasTy.isubS hW hP (ISub.cons y hy ρ.up.tail))
  have e1' : TyEq S k1 (((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)).dinst .one)
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) := by
    show TyEq S k1 ((Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).dinst .one)
      ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dinst .one)
    rw [← isub_cons_id_of_closed (show (Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).closedB 0 (k1 + 1) = true
        by simpa [Tm.closedB] using hQc) .one trivial,
      ← isub_cons_id_of_closed (show (Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).closedB 0 (k1 + 1) = true
        by simpa [Tm.closedB] using hPθc) .one trivial]
    show TyEq S k1 (Tm.data d ((Q.isub _).isub _)) (Tm.data d ((P.isub _).isub _))
    rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp, ISub.comp_id]
    exact TyEq.symm (tyB (hQ k1 ρ _ _ _ _ (I_eq_subst hE _)))
  have eLL : TyEq S (k1 + 1) (.data d (P.isub (ISub.cons y hy ρ.up.tail))) (.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))) := by
    have h := Rob.line hQ ρ y y' hy hy' hE (k1 + 1) (ISub.id k1).up.tail (.var 0) (.var 0) (show 0 < k1 + 1 by omega)
      (show 0 < k1 + 1 by omega) (I_eq_refl _)
    rw [ISub.cons_var0_up_tail, isub_up_id_of_closed hPθc, isub_up_id_of_closed hQc] at h
    exact tyB h
  -- the compositions, retyped at the starts of the lines, and their transports
  have hd0 : HasTy S k1 .one [] (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero)) (.univ D.level) := by
    rw [hPL0]; exact HasTy.isubS hW hP _
  have hd0' : HasTy S k1 .one [] (.data d ((Q.isub (ISub.cons y' hy' ρ.up.tail)).dinst .zero)) (.univ D.level) :=
    data_whnf_ty hW hD (Comp2_ty_base rel0').2.2.1 ⟨redW_self (step_data d _), TyEq.refl _⟩
  have eb := ht.2.tyConv (tyB rel0)
  have eb' := ht'.2.tyConv (tyB rel0')
  have rb := transp_rebase hW hty eb
  have rb' := transp_rebase hW hty' eb'
  have hb0 := (hcomp_data_retype hW (HasTy.eqR eb) hd0).1
  have hb0' := (hcomp_data_retype hW (HasTy.eqR eb') hd0').1
  have eH := transpHcomp_eq (D := D) hD hp hH hb0 rb.1
  have eH' := transpHcomp_eq (D := D) hD hp hH hb0' rb'.1
  have htH := HasTy.eqR eH
  have htH' := (HasTy.eqR eH').tyConv e1'
  have heqH := eH.symm.trans (rb.2.symm.trans (heq.trans ((rb'.2.tyConv e1').trans (eH'.tyConv e1'))))
  -- the end of the line, as a restriction of the line of types
  have eE : (Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dinst .one = Tm.data d (P.isub (ISub.cons
      (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) (I.scoped_subst hy (ISub.cons .one trivial (ISub.id k1)).sc) ρ)) :=
    lineP_dinst hW hD hp hP  hRL ρ y hy .one trivial
  have hy1 := I.scoped_subst hy (ISub.cons .one trivial (ISub.id k1)).sc
  have hTσ : ∀ {k4 : ℕ} (σ : ISub k4 k1), RT2 S k4
      ((Tm.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))).isub σ)
      ((Tm.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))).isub σ) := by
    intro k4 σ
    have := RT2.isub hW (tyCode_of_univ hW hP) hPP1 ((ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ).comp σ)
    show RT2 S k4 (Tm.data d ((P.isub _).isub σ)) (Tm.data d ((P.isub _).isub σ))
    rwa [Tm.isub_isub]
  -- the tubes
  have hχs : χ.Scoped k1 := (gen_hcomp (spec_to_minimal hW (HasTy.eqR ht.2)) rfl).choose_spec.1.2.1
  have hχs' : χ'.Scoped k1 := (gen_hcomp (spec_to_minimal hW (HasTy.eqR ht'.2)) rfl).choose_spec.1.2.1
  have htube : TubeD S k1 (.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))) χ
      (.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u)
      (.transp ((Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).dsubst skipI) ψ'.shift u') := by
    intro k' σ r hr0 hh
    rw [tHc_tube_pt _ _ _ σ r hr0, tHc_tube_pt _ _ _ σ r hr0]
    have hyσ := I.scoped_subst hy σ.up.sc
    have hy'σ := I.scoped_subst hy' σ.up.sc
    have eLσ : (Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).isub σ.up =
        (Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail) :=
      line_isub_up (Tm.data d P) y hy ρ σ
    have eL'σ : (Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).isub σ.up =
        (Tm.data d Q).isub (ISub.cons (y'.subst σ.up.τ) hy'σ (ρ.comp σ).up.tail) :=
      line_isub_up (Tm.data d Q) y' hy' ρ σ
    have hu := hu3 k' σ r hr0 hh
    have huc := closed_of_ty hW (RE2.typed hu).1
    have huc' := closed_of_ty hW (RE2.typed hu).2.1
    have K1 := (ihu k' σ r hr0 hh).1 (ρ.comp σ) (by rw [ISub.hom_comp])
      (by show Tm.data d (((P.dinst .zero).isub ρ).isub σ) = _; rw [Tm.isub_isub]) Q hQ k' (ISub.id k')
      (y.subst σ.up.τ) (y'.subst σ.up.τ) hyσ hy'σ (I_eq_subst hE _) (ieq_zero_up h0 σ)
    rw [ISub.comp_id, isub_id_of_closed huc, isub_id_of_closed huc'] at K1
    -- the start of the restricted line
    have rel0σ : RT2 S k' (.data d ((P.dinst .zero).isub (ρ.comp σ)))
        (((Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail)).dinst .zero) := by
      rw [lineP_dinst hW hD hp hP  hRL _ _ _ .zero trivial, P0_isub hW hD hp hP  hRL]
      exact hRL k' _ .zero _ trivial _ (I_eq_symm (ieq_zero_up h0 σ))
    -- the typings of the transported tube points
    have hhσ' : (ival (idEnv k') (χ'.subst σ.τ)).holds :=
      (holds_iff_entails (I.scoped_subst hχs' σ.sc)).2
        (ent_trans ((holds_iff_entails (I.scoped_subst hχs σ.sc)).1 hh) (ent_subst h123.1 _))
    have tp : HasTy S k' .one [] (.transp ((Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail))
        (ψ.subst σ.τ) ((u.isub σ.up).dinst r))
        (((Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail)).dinst .one) := by
      have hσ := HasTy.isubS hW htH σ
      have h1 := hcomp_tube_typed' hW (T := (Tm.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .one)).isub σ)
        (u := (Tm.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u).isub σ.up)
        (a := (Tm.transp (Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))) ψ a).isub σ) (φ := χ.subst σ.τ) hσ r hr0 hh
      rw [tHc_tube_pt _ _ _ σ r hr0, eLσ, isub_dinst, line_isub_up] at h1
      exact h1
    have tp' : HasTy S k' .one [] (.transp ((Tm.data d Q).isub (ISub.cons (y'.subst σ.up.τ) hy'σ (ρ.comp σ).up.tail))
        (ψ'.subst σ.τ) ((u'.isub σ.up).dinst r))
        (((Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail)).dinst .one) := by
      have hσ := HasTy.isubS hW htH' σ
      have h1 := hcomp_tube_typed' hW (T := (Tm.data d ((Q.isub (ISub.cons y' hy' ρ.up.tail)).dinst .one)).isub σ)
        (u := (Tm.transp ((Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).dsubst skipI) ψ'.shift u').isub σ.up)
        (a := (Tm.transp (Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))) ψ' a').isub σ) (φ := χ'.subst σ.τ) hσ r hr0 hhσ'
      rw [tHc_tube_pt _ _ _ σ r hr0, eL'σ, isub_dinst, line_isub_up] at h1
      exact h1
    have eLσL : TyEq S (k' + 1) ((Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail))
        ((Tm.data d Q).isub (ISub.cons (y'.subst σ.up.τ) hy'σ (ρ.comp σ).up.tail)) := by
      have := TyEq.isub hW σ.up eLL
      rwa [eLσ, eL'σ] at this
    have LCσ : LineConst S k' ((Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail)) (ψ.subst σ.τ) := by
      have := LineConst.isub LC σ; rwa [line_isub_up] at this
    have R1 := K1 (fun k4 τ z z' hz hz' hEz => Rob.line hQ (ρ.comp σ) _ _ hyσ hy'σ (I_eq_subst hE _) k4 τ z z' hz hz' hEz)
      (ψ.subst σ.τ) (ψ'.subst σ.τ) LCσ tp tp'
      (eqTm_transp_of hW tp tp' eLσL (ent_subst h12 _) (ent_subst h21 _) ((RE2.typed hu).2.2.tyConv (tyB rel0σ)))
      (ent_subst h12 _) (ent_subst h21 _) (RE2.conv hW rel0σ hu)
    rw [lineP_dinst hW hD hp hP  hRL _ _ _ .one trivial] at R1
    have eY : (y.subst σ.up.τ).subst (ISub.cons .one trivial (ISub.id k')).τ =
        (y.subst (ISub.cons .one trivial (ISub.id k1)).τ).subst σ.τ := by
      rw [← I_subst_comp, ← I_subst_comp, ISub.up_comp_cons_id, ISub.cons_comp, ISub.id_comp]; rfl
    rw [eLσ, eL'σ]
    show RE2 S k' (Tm.data d ((P.isub _).isub σ)) _ _
    rw [Tm.isub_isub, ISub.cons_comp]
    exact RE2.conv hW (hRL k' (ρ.comp σ) _ _ _ _ (by rw [eY]; exact I_eq_refl _)) R1
  have tS : TubeD S k1 (.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))) χ
      (.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u)
      (.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u) := by
    intro k' σ r hr0 hh
    have h := htube k' σ r hr0 hh
    exact RE2.trans hW (hTσ σ) h (RE2.symm hW (hTσ σ) h)
  have tS' : TubeD S k1 (.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))) χ'
      (.transp ((Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).dsubst skipI) ψ'.shift u')
      (.transp ((Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).dsubst skipI) ψ'.shift u') := by
    intro k' σ r hr0 hh
    have hh' : (ival (idEnv k') (χ.subst σ.τ)).holds :=
      (holds_iff_entails (I.scoped_subst hχs σ.sc)).2
        (ent_trans ((holds_iff_entails (I.scoped_subst hχs' σ.sc)).1 hh) (ent_subst h123.2 _))
    have h := htube k' σ r hr0 hh'
    exact RE2.trans hW (hTσ σ) (RE2.symm hW (hTσ σ) h) h
  -- the bases
  have hac := closed_of_ty hW (RE2.typed haa3).1
  have hac' := closed_of_ty hW (RE2.typed haa3).2.1
  have K0 := iha.1 ρ rfl rfl Q hQ k1 (ISub.id k1) y y' hy hy' hE h0
  rw [ISub.comp_id, isub_id_of_closed hac, isub_id_of_closed hac'] at K0
  obtain ⟨-, ⟨-, -, -, hta, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW
    (htH : HasTy S k1 .one [] (.hcomp _ _ _ (.transp (Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))) ψ a)) _)) rfl
  obtain ⟨-, ⟨-, -, -, hta', -⟩, -⟩ := gen_hcomp (spec_to_minimal hW
    (HasTy.eqR eH' : HasTy S k1 .one [] (.hcomp _ _ _ (.transp (Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))) ψ' a')) _)) rfl
  have hta1 : HasTy S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ a)
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) := minimal_to_spec hta
  have hta1' : HasTy S k1 .one [] (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' a')
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) := (minimal_to_spec hta').tyConv e1'
  have haa := K0 (Rob.line hQ ρ y y' hy hy' hE) ψ ψ' LC hta1 hta1'
    (eqTm_transp_of hW hta1 hta1' eLL h12 h21 ((RE2.typed haa3).2.2.tyConv (tyB rel0))) h12 h21
    (RE2.conv hW rel0 haa3)
  have eE' : ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one = Tm.data d (P.isub (ISub.cons
      (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ)) := eE
  rw [eE'] at haa htH htH' heqH ⊢
  have hbl : HcompBnd2 S k1 (.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))) χ
      (.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u)
      (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ a) := by
    intro k' σ hh
    rw [tHc_tube_pt _ _ _ σ .zero trivial, isub_transp]
    change RE2 S k' ((Tm.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))).isub σ)
      (.transp (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).isub σ.up) (ψ.subst σ.τ) ((u.isub σ.up).dinst .zero))
      (.transp (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).isub σ.up) (ψ.subst σ.τ) (a.isub σ))
    have hyσ := I.scoped_subst hy σ.up.sc
    rw [line_isub_up]
    have hb0 := hb3 k' σ hh
    have IH := ihb k' σ hh
    rw [← ISub.hom_comp] at IH
    change RE2 S k' (.data d (((P.dinst .zero).isub ρ).isub σ)) _ _ at hb0
    change TM1H S d D K P k' (ρ.comp σ).hom (.data d (((P.dinst .zero).isub ρ).isub σ)) _ _ at IH
    rw [Tm.isub_isub] at hb0 IH
    have tp := hcomp_tube_typed' hW
      (u := (Tm.transp ((Tm.data d (P.isub (ISub.cons y hy ρ.up.tail))).dsubst skipI) ψ.shift u).isub σ.up)
      (HasTy.isubS hW htH σ) .zero trivial hh
    rw [tHc_tube_pt _ _ _ σ .zero trivial] at tp
    change HasTy S k' .one []
      (.transp (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).isub σ.up) (ψ.subst σ.τ) ((u.isub σ.up).dinst .zero))
      ((Tm.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))).isub σ) at tp
    rw [line_isub_up] at tp
    have tb := HasTy.isubS hW hta1 σ
    rw [isub_transp, line_isub_up] at tb
    have ee : (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one).isub σ =
        ((Tm.data d P).isub (ISub.cons (y.subst σ.up.τ) hyσ (ρ.comp σ).up.tail)).dinst .one := by
      rw [isub_dinst, line_isub_up]; rfl
    have eEnd := (congrArg (fun Z : Tm => Z.isub σ) eE').symm.trans ee
    rw [eEnd] at tp
    rw [ee] at tb
    have R := tm1h_transp_point hW hD hH hp hP hRL (ρ.comp σ) hRL
      (y.subst σ.up.τ) (y.subst σ.up.τ) hyσ hyσ (I_eq_refl _) (ieq_zero_up h0 σ)
      (ψ.subst σ.τ) (ψ.subst σ.τ) (ent_refl _) (ent_refl _) (by
        have := LineConst.isub LC σ; rwa [line_isub_up] at this)
      hb0 IH tp tb
    rw [← eEnd] at R
    exact R
  have hbr : HcompBnd2 S k1 (.data d (P.isub (ISub.cons (y.subst (ISub.cons .one trivial (ISub.id k1)).τ) hy1 ρ))) χ'
      (.transp ((Tm.data d (Q.isub (ISub.cons y' hy' ρ.up.tail))).dsubst skipI) ψ'.shift u')
      (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' a') := by
    intro k' σ hh'
    have hh : (ival (idEnv k') (χ.subst σ.τ)).holds :=
      (holds_iff_entails (I.scoped_subst hχs σ.sc)).2
        (ent_trans ((holds_iff_entails (I.scoped_subst hχs' σ.sc)).1 hh') (ent_subst h123.2 _))
    exact RE2.trans hW (hTσ σ) (RE2.symm hW (hTσ σ) (htube k' σ .zero trivial hh))
      (RE2.trans hW (hTσ σ) (hbl k' σ hh) (RE2.isub hW haa σ))
  exact hcomp_relD hW hD hH hP hPP1 _ htH htH' heqH h123.1 h123.2 htube tS tS' haa hbl hbr

end ind

end

end Model.Whnf
