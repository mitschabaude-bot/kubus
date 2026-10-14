import Model.Whnf.Kan2DataHITBT

/-!
# Transport along lines of higher inductive types: the motives and the stage cases

As for inductive types without path constructors (`Kan2DataTInd.lean`), elements related at the start of a
literal line of a higher inductive type are transported along related lines by induction on their
relation. The motives: `TM1H` (for the relation, at all restrictions: the transports are related, `TM1`, and
the transport of the left element is related to the contractum of the transport of its normal form, `TR`),
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

/-- The motive at the relation of the start of a line. -/
def TM1H (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A x x' : Tm) : Prop :=
  TM1 S d K P k1 g A x x' ∧ TR S d D K P k1 g A x

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
    ∀ k' (σ : ISub k' k1) (r : I), r.Scoped k' → (ival (idEnv k') (χ.subst σ.τ)).holds →
      TM1H S d D K P k' (g.comp σ.hom) ((Tm.data d ps).isub σ) ((u.isub σ.up).dinst r) ((u'.isub σ.up).dinst r))

/-- The motive at one stage. -/
def TM2H (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A v v' : Tm) : Prop :=
  TMc S d D K P k1 g A v v' ∧ TMch S d D K P k1 g A v v'

section ind
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = true)
  (hyp : HITHyp2 S) (hp : D.params ≠ []) {K : ℕ} {P : Tm} (hP : HasTy S (K + 1) .one [] (.data d P) (.univ D.level))
  (hArgK : KanShape S (K + 1) (ΘK S D d (K + 1) P))
  (hRL : Rob S d K P P)
include hW hD hH hyp hp hP hArgK hRL

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
  have hP0 := P0_ty hW hD hp hP hArgK hRL
  have hP0P0 := P0_rt2 hW hD hp hP hArgK hRL
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
  have hPL0 := line_dinst hW hD hp hP hArgK hRL ρ y hy .zero trivial
  have rel0 : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero)) := by
    rw [P0_isub hW hD hp hP hArgK hRL, hPL0]
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
    rw [P0_isub hW hD hp hP hArgK hRL, hQL0]
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
      hArgK := argK_restr hArgK _, hφs := hψs, h12 := h12, h21 := h21, hLC := LC, hty := rb.1,
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

end ind

end

end Model.Whnf
