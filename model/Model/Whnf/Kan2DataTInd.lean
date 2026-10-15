import Model.Whnf.Kan2DataTCon

/-!
# Transport along lines of inductive types without path constructors: the induction

Elements related at the start `data d (P(0))` of a literal line `data d P` (at stage `K + 1`) are
transported along all lines `P(y, ρ)` (the restrictions of `P` sending the line variable to `y` and the
other variables to `ρ`), against related lines `Q(y', ρ)`, by induction on their relation: the motives
`TM1` (for the relation, at all restrictions) and `TM2` (for one stage: the `transpCon` contracta are
related).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- Robust relation of two literal lines of inductive types: related at `I.Eq`-equal points. -/
def Rob (S : Sig) (d K : ℕ) (P Q : Tm) : Prop :=
  ∀ k3 (τ : ISub k3 K) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
    RT2 S k3 (.data d (P.isub (ISub.cons y hy τ))) (.data d (Q.isub (ISub.cons y' hy' τ)))

theorem ieq_subst_cons {k3 k4 : ℕ} {y y' z z' : I} (hE : I.Eq y y') (hEz : I.Eq z z') (hz : z.Scoped k4)
    (hz' : z'.Scoped k4) (τ : ISub k4 k3) :
    I.Eq (y.subst (ISub.cons z hz τ).τ) (y'.subst (ISub.cons z' hz' τ).τ) :=
  I_eq_trans (I_eq_subst hE _) (I_eq_subst_congr (fun i => by
    rcases i with _ | i
    · exact hEz
    · exact I_eq_refl _) y')

/-- A line restricted further. -/
theorem line_comp {K k3 k4 : ℕ} (y : I) (hy : y.Scoped (k3 + 1)) (ρ : ISub k3 K) (z : I) (hz : z.Scoped k4)
    (τ : ISub k4 k3) :
    (ISub.cons y hy ρ.up.tail).comp (ISub.cons z hz τ) =
      ISub.cons (y.subst (ISub.cons z hz τ).τ) (I.scoped_subst hy (ISub.cons z hz τ).sc) (ρ.comp τ) := by
  rw [ISub.cons_comp, ISub.up_tail_comp_cons]

theorem Rob.line {d K : ℕ} {P Q : Tm} (h : Rob S d K P Q) {k3 : ℕ} (ρ : ISub k3 K) (y y' : I)
    (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)) (hE : I.Eq y y') :
    Rob S d k3 (P.isub (ISub.cons y hy ρ.up.tail)) (Q.isub (ISub.cons y' hy' ρ.up.tail)) := by
  intro k4 τ z z' hz hz' hEz
  rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp]
  exact h k4 (ρ.comp τ) _ _ _ _ (ieq_subst_cons hE hEz hz hz' τ)

/-- The start of a line, at a restriction. -/
theorem ieq_zero_comp {k3 k4 : ℕ} {y z : I} (hy : y.Scoped (k3 + 1)) (h0 : I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero)
    (hz : z.Scoped (k4 + 1)) (hz0 : I.Eq (z.subst (ISub.cons .zero trivial (ISub.id k4)).τ) .zero) (τ : ISub k4 k3) :
    I.Eq ((y.subst (ISub.cons z hz τ.up.tail).τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ) .zero := by
  have e1 : (ISub.cons z hz τ.up.tail).comp (ISub.cons .zero trivial (ISub.id k4)) =
      ISub.cons (z.subst (ISub.cons .zero trivial (ISub.id k4)).τ)
        (I.scoped_subst hz (ISub.cons .zero trivial (ISub.id k4)).sc) τ := by
    rw [ISub.cons_comp, ISub.up_tail_comp_cons, ISub.comp_id]
  have e2 : (ISub.cons .zero trivial (ISub.id k3)).comp τ = ISub.cons .zero trivial τ := by
    rw [ISub.cons_comp, ISub.id_comp]; rfl
  rw [← I_subst_comp, e1]
  refine I_eq_trans (ieq_subst_cons (I_eq_refl y) hz0 _ (show (I.zero).Scoped k4 from trivial) τ) ?_
  rw [← e2, I_subst_comp]
  exact I_eq_subst h0 _

section lit
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
include hW hD hH hP hPP

/-- The arguments of related elements at one stage of a literal inductive type. -/
theorem DR2At_args {k3 : ℕ} (ρ' : ISub k3 K) {x x' : Tm}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k3 ρ'.hom
      (.data d (P.isub ρ')) x x') :
    ∃ c C qs Z qs' Z', D.ctors[c]? = some C ∧ Z.length = C.args.length ∧ Z'.length = C.args.length ∧
      RedE S k3 (.data d (P.isub ρ')) x (.con d c qs (Tm.ofList Z) []) ∧
      RedE S k3 (.data d (P.isub ρ')) x' (.con d c qs' (Tm.ofList Z') []) ∧
      ∀ i (hi : i < C.args.length), RE2 S k3 ((C.argTy d D.params.length i).substList
        ((Z.take i).reverse ++ (P.isub ρ').toList.reverse)) (Z.getD i .abort) (Z'.getD i .abort) := by
  have hdD := dataD_eq hW hD
  have hTP : IsTyK S k3 (.data d (P.isub ρ')) := ⟨_, .inl (HasTy.isubS hW hP ρ')⟩
  have hPl := (dataLit_rel hW hD hP hPP ρ').2.2.2.2.2.1
  have hplen : (P.isub ρ').toList.length = D.params.length := by
    have := data_len_of hW hTP; rwa [hdD] at this
  cases hat with
  | @con _ _ _ _ _ ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt =>
    have hC' := hdD ▸ hC
    obtain rfl := redT_data_eq (Θ := ΘK S D d K P) hA
    have hrs0 := List.eq_nil_of_length_eq_zero (hrs.trans (nonHIT_ctor hH hC').1)
    have hrs0' := List.eq_nil_of_length_eq_zero (hrs'.trans (nonHIT_ctor hH hC').1)
    subst hrs0 hrs0'
    refine ⟨_, _, _, _, _, _, hC', hl, hl', ht, ht', fun i hi => ?_⟩
    rw [getD_eq_get' (by omega), getD_eq_get' (by omega)]
    cases hri : C.isRec i
    · have := dataP2_RE2 hW hD hP hPP ρ' hC' (by omega) (by omega) hrec hpt (show i < _ by omega)
        (show i < _ by omega) hri
      rwa [hdD] at this
    · rw [argTy_rec_inst hri hPl hplen (by simp; omega)]
      have h := hrec i (by omega) (by omega) hri
      obtain ⟨he⟩ : Nonempty (EqTm S k3 .one [] _ _ (.data d (P.isub ρ'))) := by cases h with | intro he => exact ⟨he⟩
      exact (RE2_dataLit_iff hW hD hP ρ').2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, h⟩
  | hcomp _ _ _ hH' =>
    have : D.isHIT = true := hdD ▸ hH'
    rw [hH] at this; cases this

end lit

/-- The motive at the relation of the start of a line, at all restrictions: transport along the lines. -/
def TM1 (S : Sig) (d : ℕ) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A x x' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d ((P.dinst .zero).isub ρ) → ∀ Q, Rob S d K P Q →
  ∀ k3 (σ : ISub k3 k1) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
    I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero →
    KanT2At S k3 ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail))
      ((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) (x.isub σ) (x'.isub σ)

/-- The motive at the relation of the start of a line at one stage: the `transpCon` contracta are
related. -/
def TM2 (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P : Tm) (k1 : ℕ) (g : Hom k1 K) (A v v' : Tm) : Prop :=
  ∀ (ρ : ISub k1 K), g = ρ.hom → A = .data d ((P.dinst .zero).isub ρ) → ∀ Q, Rob S d K P Q →
  ∀ (y y' : I) (hy : y.Scoped (k1 + 1)) (hy' : y'.Scoped (k1 + 1)), I.Eq y y' →
    I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k1)).τ) .zero →
  ∀ (c : ℕ) (C : Ctor) (qs : Tm) (X : List Tm) (qs' : Tm) (X' : List Tm), D.ctors[c]? = some C →
    RedE S k1 A v (.con d c qs (Tm.ofList X) []) → RedE S k1 A v' (.con d c qs' (Tm.ofList X') []) →
  ∀ (ψ ψ' : I), ψ.Scoped k1 → I.Entails ψ ψ' → I.Entails ψ' ψ →
    LineConst S k1 ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ →
    HasTy S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ v)
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) →
    HasTy S k1 .one [] (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' v')
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) →
    EqTm S k1 .one [] (.transp ((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)) ψ v)
      (.transp ((Tm.data d Q).isub (ISub.cons y' hy' ρ.up.tail)) ψ' v')
      (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one) →
    RE2 S k1 (((Tm.data d P).isub (ISub.cons y hy ρ.up.tail)).dinst .one)
      (tCon d D c C (P.isub (ISub.cons y hy ρ.up.tail)) ψ X) (tCon d D c C (Q.isub (ISub.cons y' hy' ρ.up.tail)) ψ' X')

/-- A transport with an equal base. -/
theorem transp_rebase (hW : WfSig S) {L a a' T : Tm} {ψ : I} (hty : HasTy S k .one [] (.transp L ψ a) T)
    (e : EqTm S k .one [] a a' (L.dinst .zero)) :
    HasTy S k .one [] (.transp L ψ a') (L.dinst .one) ∧
    EqTm S k .one [] (.transp L ψ a) (.transp L ψ a') (L.dinst .one) := by
  obtain ⟨l0, ⟨hL, hψ, hc, ha⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have h1 := HasTy.transp (minimal_to_spec hL) hψ (minimal_to_spec_eq hc) (HasTy.eqR e)
  have h0 := HasTy.transp (minimal_to_spec hL) hψ (minimal_to_spec_eq hc) (minimal_to_spec ha)
  exact ⟨h1, EqTm.transp h0 h1 (EqTm.refl (minimal_to_spec hL)) (ent_refl _) (ent_refl _) e⟩

/-- A restriction of a line, as a line. -/
theorem line_isub_up {K k3 k4 : ℕ} (L : Tm) (y : I) (hy : y.Scoped (k3 + 1)) (τ0 : ISub k3 K) (κ : ISub k4 k3) :
    (L.isub (ISub.cons y hy τ0.up.tail)).isub κ.up =
      L.isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) (τ0.comp κ).up.tail) := by
  rw [Tm.isub_isub, ISub.cons_comp, ISub.up_tail_comp_up]

/-- The start of a restricted line. -/
theorem ieq_zero_up {k3 k4 : ℕ} {y : I} (h0 : I.Eq (y.subst (ISub.cons .zero trivial (ISub.id k3)).τ) .zero)
    (κ : ISub k4 k3) : I.Eq ((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ) .zero := by
  rw [← I_subst_comp, ISub.up_comp_cons_id]
  have e : ISub.cons .zero trivial κ = (ISub.cons .zero trivial (ISub.id k3)).comp κ := by
    rw [ISub.cons_comp, ISub.id_comp]; rfl
  rw [e, I_subst_comp]
  exact I_eq_subst h0 _

section ind
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  (hp : D.params ≠ []) {K : ℕ} {P : Tm} (hP : HasTy S (K + 1) .one [] (.data d P) (.univ D.level))
  (hArgK : KanShape S (K + 1) (ΘK S D d (K + 1) P))
  (hRL : Rob S d K P P)
include hW hD hH hp hP hArgK hRL

omit hH in
theorem P0_ty : HasTy S K .one [] (.data d (P.dinst .zero)) (.univ D.level) := by
  have hPc := data_closed hW hD hP
  have := HasTy.isubS hW hP (ISub.cons .zero trivial (ISub.id K))
  rwa [show (Tm.data d P).isub (ISub.cons .zero trivial (ISub.id K)) = .data d (P.isub (ISub.cons .zero trivial (ISub.id K)))
    from rfl, isub_cons_id_of_closed hPc] at this

omit hH in
theorem P0_rt2 : RT2 S K (.data d (P.dinst .zero)) (.data d (P.dinst .zero)) := by
  have hPc := data_closed hW hD hP
  have := hRL K (ISub.id K) .zero .zero trivial trivial (I_eq_refl _)
  rwa [isub_cons_id_of_closed hPc] at this

omit hH in
theorem P0_isub {k1 : ℕ} (ρ : ISub k1 K) : (P.dinst .zero).isub ρ = P.isub (ISub.cons .zero trivial ρ) := by
  rw [isub_dinst]; exact isub_up_dinst P ρ .zero trivial

omit hH in
theorem line_dinst {k1 : ℕ} (ρ : ISub k1 K) (y : I) (hy : y.Scoped (k1 + 1)) (r : I) (hr : r.Scoped k1) :
    (P.isub (ISub.cons y hy ρ.up.tail)).dinst r =
      P.isub (ISub.cons (y.subst (ISub.cons r hr (ISub.id k1)).τ) (I.scoped_subst hy (ISub.cons r hr (ISub.id k1)).sc) ρ) := by
  have hPc := data_closed hW hD hP
  have hc : (P.isub (ISub.cons y hy ρ.up.tail)).closedB 0 (k1 + 1) = true :=
    data_closed hW hD (HasTy.isubS hW hP (ISub.cons y hy ρ.up.tail))
  rw [← isub_cons_id_of_closed hc r hr, Tm.isub_isub, line_comp, ISub.comp_id]

/-- The constructor case: transport of related constructors along the lines. -/
theorem tm2_con {k1 : ℕ} {g : Hom k1 K} {A t t' ps qs qs' : Tm} {c : ℕ} {C : Ctor} {args args' : List Tm}
    {rs rs' : List I}
    (hat : DR2At S d (dataD S d) (dataMem S (ΘK S D d K (P.dinst .zero)) (Hom.id K))
      (dataP2 S (ΘK S D d K (P.dinst .zero)) (Hom.id K)) k1 g A t t')
    (hC : (dataD S d).ctors[c]? = some C) (hA : RedT S k1 A (.data d ps))
    (ht : RedE S k1 A t (.con d c qs (Tm.ofList args) rs)) (ht' : RedE S k1 A t' (.con d c qs' (Tm.ofList args') rs'))
    (hl : args.length = C.args.length) (hl' : args'.length = C.args.length)
    (ihrec : ∀ j (hj : j < args.length) (hj' : j < args'.length), C.isRec j = true →
      TM1 S d K P k1 g (.data d ps) args[j] args'[j]) :
    TM2 S d D K P k1 g A t t' := by
  intro ρ hg hAe Q hQ y y' hy hy' hE h0 c2 C2 qs2 X2 qs2' X2' hC2 hr hr' ψ ψ' hψs h12 h21 LC hty hty' heq
  subst hg hAe
  have hdD := dataD_eq hW hD
  have hC' : D.ctors[c]? = some C := hdD ▸ hC
  have hP0 := P0_ty hW hD hp hP hArgK hRL
  have hP0P0 := P0_rt2 hW hD hp hP hArgK hRL
  obtain rfl : ps = (P.dinst .zero).isub ρ := redT_data_eq (Θ := ΘK S D d K (P.dinst .zero)) hA
  -- the normal forms
  have e1 := RedW.unique hr.1 ht.1
  have e2 := RedW.unique hr'.1 ht'.1
  simp only [Tm.con.injEq] at e1 e2
  obtain ⟨-, rfl, rfl, eX, rfl⟩ := e1
  obtain ⟨-, -, rfl, eX', rfl⟩ := e2
  have eX1 := congrArg Tm.toList eX
  have eX1' := congrArg Tm.toList eX'
  simp only [toList_ofList] at eX1 eX1'
  subst X2 X2'
  rw [hC'] at hC2; cases hC2
  -- the arguments, related at the start of the line
  obtain ⟨c3, C3, q3, Z, q3', Z', hC3, hZl, hZ'l, hr3, hr3', hZ⟩ := DR2At_args hW hD hH hP0 hP0P0 ρ hat
  have f1 := RedW.unique hr3.1 hr.1
  have f2 := RedW.unique hr3'.1 hr'.1
  simp only [Tm.con.injEq] at f1 f2
  obtain ⟨-, rfl, -, eZ, -⟩ := f1
  obtain ⟨-, -, -, eZ', -⟩ := f2
  have eZ1 := congrArg Tm.toList eZ
  have eZ1' := congrArg Tm.toList eZ'
  simp only [toList_ofList] at eZ1 eZ1'
  subst Z Z'
  rw [hC'] at hC3; cases hC3
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
    have hself : ∀ l (hl0 : l < i), RE2 S k1 ((C.argTy d D.params.length l).substList
        (((args.take i).take l).reverse ++ ((P.dinst .zero).isub ρ).toList.reverse))
        ((args.take i).getD l .abort) ((args.take i).getD l .abort) := by
      intro l hl0
      rw [List.take_take, Nat.min_eq_left hl0.le, getD_take_lt hl0]
      have r := hZ l (by omega)
      have T := argTy_rt2_args hW hD hH hP0 hP0P0 ρ hC' hl hl' hZ (show l < C.args.length by omega)
      exact RE2.trans hW T r (RE2.symm hW T r)
    have T := argTy_rt2' hW hD (HasTy.isubS hW hP0 ρ) hP0ρ rel0 hC' hi (A := args.take i) (B := args.take i)
      (by simp; omega) (by simp; omega) hself
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
      args args' [] [] :=
    { hW := hW, hD := hD, hp := hp, hC := hC', hPL := HasTy.isubS hW hP _,
      conR := fun Y Y' hYl hY'l hcT he hargs => RE2_con_args_id hW hD hH hd1 s1 hC' Y Y' hYl hY'l hcT he hargs,
      hR := Rob.line hQ ρ y y' hy hy' hE, hRL := Rob.line hRL ρ y y hy hy (I_eq_refl _),
      hArgK := argK_restr hArgK _, hφs := hψs, h12 := h12, h21 := h21, hLC := LC, hty := rb.1,
      hty' := rb'.1.tyConv e1', heq := rb.2.symm.trans (heq.trans (rb'.2.tyConv e1')), hargs0 := hargs0,
      hrecT := fun i hi hri k3 τ z z' hz hz' hEz hz0 => by
        have h := ihrec i (by omega) (by omega) hri ρ rfl rfl Q hQ k3 τ _ _
          (I.scoped_subst hy (ISub.cons z hz τ.up.tail).sc) (I.scoped_subst hy' (ISub.cons z' hz' τ.up.tail).sc)
          (ieq_subst_cons hE hEz hz hz' τ.up.tail) (ieq_zero_comp hy h0 hz hz0 τ)
        rw [getD_eq_get' (show i < args.length by omega),
          getD_eq_get' (show i < args'.length by omega)]
        show KanT2At S k3 (Tm.data d ((P.isub _).isub _)) (Tm.data d ((Q.isub _).isub _)) _ _
        rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp, ISub.comp_up_tail]
        exact h }
  exact H.rel

omit hH in
/-- The relation of the start of a line, the end of a restricted line. -/
theorem lineP_dinst {k3 : ℕ} (τ0 : ISub k3 K) (y : I) (hy : y.Scoped (k3 + 1)) (r : I) (hr : r.Scoped k3) :
    ((Tm.data d P).isub (ISub.cons y hy τ0.up.tail)).dinst r =
      .data d (P.isub (ISub.cons (y.subst (ISub.cons r hr (ISub.id k3)).τ)
        (I.scoped_subst hy (ISub.cons r hr (ISub.id k3)).sc) τ0)) := by
  show Tm.data d ((P.isub _).dinst r) = _
  rw [line_dinst hW hD hp hP hArgK hRL τ0 y hy r hr]

omit hH in
theorem PP1 : RT2 S (K + 1) (.data d P) (.data d P) := by
  have hPc := data_closed hW hD hP
  have := hRL (K + 1) (ISub.id K).up.tail (.var 0) (.var 0) (show 0 < K + 1 by omega) (show 0 < K + 1 by omega)
    (I_eq_refl _)
  rwa [ISub.cons_var0_up_tail, isub_up_id_of_closed hPc] at this

/-- The intro case: transport of related elements, from the contracta of their normal forms at all
restrictions. -/
theorem tm1_intro {k1 : ℕ} {g : Hom k1 K} {A x x' : Tm}
    (ih : ∀ k' (σ : ISub k' k1), TM2 S d D K P k' (g.comp σ.hom) (A.isub σ) (x.isub σ) (x'.isub σ))
    (ihc : ∀ k' (σ : ISub k' k1) w, RedW S (x.isub σ) w → ∀ k'' (ρ' : ISub k'' k'),
      TM2 S d D K P k'' (g.comp (σ.comp ρ').hom) (A.isub (σ.comp ρ')) (w.isub ρ') (x.isub (σ.comp ρ'))) :
    TM1 S d K P k1 g A x x' := by
  intro ρ hg hAe Q hQ k3 σ y y' hy hy' hE h0 LR ψ ψ' LC hty hty' heq h12 h21 hbase
  subst hg hAe
  have hdD := dataD_eq hW hD
  have hPc := data_closed hW hD hP
  have hPP1 := PP1 hW hD hp hP hArgK hRL
  have tyB : ∀ {k4 : ℕ} {X Z : Tm}, RT2 S k4 X Z → TyEq S k4 X Z := fun h => (Comp2_ty_base h).2.2.2.2.2
  obtain ⟨-, ⟨-, hψs, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  have hψs' : ψ'.Scoped k3 := (gen_transpF (spec_to_minimal hW hty') rfl).choose_spec.1.2.1
  -- the line, its restrictions and their ends
  -- the restrictions of the line
  have eL : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I),
      (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst r).isub κ =
        ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst
          (r.subst κ.τ) := by
    intro k4 κ r; rw [isub_dinst, line_isub_up]
  have eL' : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I),
      (((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)).dinst r).isub κ =
        ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst
          (r.subst κ.τ) := by
    intro k4 κ r; rw [isub_dinst, line_isub_up]
  -- the bases at a restriction, at the start of the restricted line
  have hb : ∀ {k4 : ℕ} (κ : ISub k4 k3), RE2 S k4 (.data d (P.isub (ISub.cons
      ((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ)
      (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) ((ρ.comp σ).comp κ))))
      (x.isub (σ.comp κ)) (x'.isub (σ.comp κ)) := by
    intro k4 κ
    have h := RE2.isub hW hbase κ
    rw [eL, Tm.isub_isub, Tm.isub_isub, show I.subst κ.τ I.zero = I.zero from rfl,
      lineP_dinst hW hD hp hP hArgK hRL _ _ _ .zero trivial] at h
    exact h
  -- the normal forms of the bases
  have hw := fun k4 (κ : ISub k4 k3) => dataLit_args hW hD hH hP hPP1 _ (hb κ)
  choose c C qs Z qs' Z' hC hZl hZ'l hr hr' hrecZ hptZ using hw
  -- the ends of the restricted lines
  have hPend : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I) (hr0 : r.Scoped k4),
      ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r =
        .data d (P.isub (ISub.cons ((y.subst κ.up.τ).subst (ISub.cons r hr0 (ISub.id k4)).τ)
          (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons r hr0 (ISub.id k4)).sc) ((ρ.comp σ).comp κ))) :=
    fun κ r hr0 => lineP_dinst hW hD hp hP hArgK hRL _ _ _ r hr0
  have hQc : ∀ {k4 : ℕ} (θ : ISub k4 (K + 1)), (Tm.data d (Q.isub θ)).closedB 0 k4 = true := by
    intro k4 θ
    have := closed_of_isTyK hW (Comp2_ty_base (hQ k4 θ.tail (θ.τ 0) (θ.τ 0) (θ.sc 0 (by omega)) (θ.sc 0 (by omega))
      (I_eq_refl _))).2.2.1
    rwa [ISub.cons_tail] at this
  have hQend : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I) (hr0 : r.Scoped k4),
      ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r =
        .data d (Q.isub (ISub.cons ((y'.subst κ.up.τ).subst (ISub.cons r hr0 (ISub.id k4)).τ)
          (I.scoped_subst (I.scoped_subst hy' κ.up.sc) (ISub.cons r hr0 (ISub.id k4)).sc) ((ρ.comp σ).comp κ))) := by
    intro k4 κ r hr0
    show (Tm.data d (Q.isub _)).dinst r = _
    rw [← isub_cons_id_of_closed (hQc _) r hr0]
    show Tm.data d ((Q.isub _).isub _) = _
    rw [Tm.isub_isub, line_comp, ISub.comp_id]
  -- the ends of the right line are those of the left line
  have hLR : ∀ {k4 : ℕ} (κ : ISub k4 k3) (r : I) (hr0 : r.Scoped k4),
      RT2 S k4 (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r)
        (((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst r) := by
    intro k4 κ r hr0
    rw [hPend κ r hr0, hQend κ r hr0]
    exact hQ k4 _ _ _ _ _ (I_eq_subst (I_eq_subst hE _) _)
  -- the typings at a restriction
  have htyκ : ∀ {k4 : ℕ} (κ : ISub k4 k3), HasTy S k4 .one []
      (.transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ.subst κ.τ) (x.isub (σ.comp κ)))
      (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .one) := by
    intro k4 κ
    have h := HasTy.isubS hW hty κ
    have e : (Tm.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ)).isub κ =
        .transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ.subst κ.τ) (x.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d P).isub _).isub κ.up) _ ((x.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one] at h
    exact h
  have htyκ' : ∀ {k4 : ℕ} (κ : ISub k4 k3), HasTy S k4 .one []
      (.transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ'.subst κ.τ) (x'.isub (σ.comp κ)))
      (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .one) := by
    intro k4 κ
    have h := HasTy.isubS hW hty' κ
    have e : (Tm.transp ((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) ψ' (x'.isub σ)).isub κ =
        .transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ'.subst κ.τ) (x'.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d Q).isub _).isub κ.up) _ ((x'.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one] at h
    exact h
  have heqκ : ∀ {k4 : ℕ} (κ : ISub k4 k3), EqTm S k4 .one []
      (.transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ.subst κ.τ) (x.isub (σ.comp κ)))
      (.transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ'.subst κ.τ) (x'.isub (σ.comp κ)))
      (((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).dinst .one) := by
    intro k4 κ
    have h := EqTm.isubS hW heq κ
    have e : (Tm.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ)).isub κ =
        .transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ.subst κ.τ) (x.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d P).isub _).isub κ.up) _ ((x.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    have e' : (Tm.transp ((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) ψ' (x'.isub σ)).isub κ =
        .transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ'.subst κ.τ) (x'.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d Q).isub _).isub κ.up) _ ((x'.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, e', eL κ .one] at h
    exact h
  -- the end of the line is related to itself
  have hcL : ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).closedB 0 (k3 + 1) = true :=
    closed_of_ty hW (HasTy.isubS hW hP _)
  have hX : TyCode k3 (semK S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one)) :=
    tyCode_of_ty hW hty
  have hAA : RT2 S k3 (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one)
      (((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).dinst .one) := by
    have h := LR k3 (ISub.id k3) .one .one trivial trivial (I_eq_refl _)
    rw [isub_cons_id_of_closed hcL] at h
    exact RT2.refl hW hX h
  -- the reducts at the restrictions
  refine RE2.expandBoth hW hX hAA hty hty'
    (fun k4 κ => if I.Entails .one (ψ.subst κ.τ) then x.isub (σ.comp κ) else
      tCon d D (c k4 κ) (C k4 κ) (P.isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ.subst κ.τ) (Z k4 κ))
    (fun k4 κ => if I.Entails .one (ψ'.subst κ.τ) then x'.isub (σ.comp κ) else
      tCon d D (c k4 κ) (C k4 κ) (Q.isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
        (ψ'.subst κ.τ) (Z' k4 κ))
    (fun k4 κ => ?_) (fun k4 κ => ?_) (fun k4 κ k5 κ' => ?_)
  · -- the left reducts
    have e : (Tm.transp ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)) ψ (x.isub σ)).isub κ =
        .transp ((Tm.data d P).isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ.subst κ.τ) (x.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d P).isub _).isub κ.up) _ ((x.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one]
    dsimp only
    split_ifs with hf
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (htyκ κ)⟩
    · have eb := (hr k4 κ).2
      rw [← hPend κ .zero trivial] at eb
      have rb := transp_rebase hW (htyκ κ) eb
      have eT := (transpCon_eq hW hD hp hH (hC k4 κ) rb.1).1
      exact ⟨(red_transp_base hD hp hf (hr k4 κ).1.1).trans (.step (step_transp_con hD hp hH (hC k4 κ) hf (hZl k4 κ))
        (.refl _)), rb.2.trans eT⟩
  · -- the right reducts
    have e : (Tm.transp ((Tm.data d Q).isub (ISub.cons y' hy' (ρ.comp σ).up.tail)) ψ' (x'.isub σ)).isub κ =
        .transp ((Tm.data d Q).isub (ISub.cons (y'.subst κ.up.τ) (I.scoped_subst hy' κ.up.sc) ((ρ.comp σ).comp κ).up.tail))
          (ψ'.subst κ.τ) (x'.isub (σ.comp κ)) := by
      show Tm.transp (((Tm.data d Q).isub _).isub κ.up) _ ((x'.isub σ).isub κ) = _
      rw [line_isub_up, Tm.isub_isub]
    rw [e, eL κ .one]
    dsimp only
    split_ifs with hf
    · exact ⟨.step (step_transp_face hf) (.refl _), EqTm.transpFace hf (htyκ' κ)⟩
    · have r0 := hLR κ .zero trivial
      have r1 := hLR κ .one trivial
      have eb := (hr' k4 κ).2
      rw [← hPend κ .zero trivial] at eb
      have eb' := eb.tyConv (tyB r0)
      have hty1 := (htyκ' κ).tyConv (tyB r1)
      have rb := transp_rebase hW hty1 eb'
      have eT := (transpCon_eq hW hD hp hH (hC k4 κ) rb.1).1
      exact ⟨(red_transp_base hD hp hf (hr' k4 κ).1.1).trans (.step (step_transp_con hD hp hH (hC k4 κ) hf (hZ'l k4 κ))
        (.refl _)), (rb.2.trans eT).tyConv (TyEq.symm (tyB r1))⟩
  · -- the reducts across restrictions
    have hPl : IsList P := tele_isList (gen_data_tele (spec_to_minimal hW hP) rfl).choose_spec.2
    have hPlen : P.toList.length = D.params.length := by
      have := data_len_of hW (⟨_, .inl hP⟩ : IsTyK S (K + 1) (.data d P)); rwa [hdD] at this
    have eY : (y.subst κ.up.τ).subst κ'.up.τ = y.subst (κ.comp κ').up.τ := by rw [← I_subst_comp, ISub.up_comp]
    have eψ : (ψ.subst κ.τ).subst κ'.τ = ψ.subst (κ.comp κ').τ := (I_subst_comp ψ κ κ').symm
    have eT : ((ρ.comp σ).comp κ).comp κ' = (ρ.comp σ).comp (κ.comp κ') := ISub.comp_assoc _ _ _
    have ex : (x.isub (σ.comp κ)).isub κ' = x.isub (σ.comp (κ.comp κ')) := by rw [Tm.isub_isub, ISub.comp_assoc]
    have eLine : (P.isub (ISub.cons (y.subst κ.up.τ) (I.scoped_subst hy κ.up.sc) ((ρ.comp σ).comp κ).up.tail)).isub κ'.up =
        P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
          ((ρ.comp σ).comp (κ.comp κ')).up.tail) := by
      rw [line_isub_up]; congr 2 <;> simp only [eY, eT]
    -- the line at the points of a restriction
    have hLpt : ∀ {k6 : ℕ} (κ3 : ISub k6 k3) (r : I) (hr0 : r.Scoped k6),
        ((Tm.data d P).isub (ISub.cons y hy (ρ.comp σ).up.tail)).isub (ISub.cons r hr0 κ3) =
          ((Tm.data d P).isub (ISub.cons (y.subst κ3.up.τ) (I.scoped_subst hy κ3.up.sc) ((ρ.comp σ).comp κ3).up.tail)).dinst r := by
      intro k6 κ3 r hr0
      rw [← isub_up_dinst _ κ3 r hr0, line_isub_up]
    have hXL : ∀ {k6 : ℕ} (θ : ISub k6 (K + 1)), TyCode k6 (semK S k6 (.data d (P.isub θ))) := fun θ =>
      tyCode_of_univ hW (HasTy.isubS hW hP θ)
    -- the start and the end of the line where the face holds
    have hconst : ∀ {k6 : ℕ} (κ3 : ISub k6 k3), I.Entails .one (ψ.subst κ3.τ) →
        RT2 S k6 (((Tm.data d P).isub (ISub.cons (y.subst κ3.up.τ) (I.scoped_subst hy κ3.up.sc) ((ρ.comp σ).comp κ3).up.tail)).dinst .zero)
          (((Tm.data d P).isub (ISub.cons (y.subst κ3.up.τ) (I.scoped_subst hy κ3.up.sc) ((ρ.comp σ).comp κ3).up.tail)).dinst .one) := by
      intro k6 κ3 hf3
      have c1 := LC k6 κ3 .one trivial ((holds_iff_entails (I.scoped_subst hψs κ3.sc)).2 hf3)
      rw [hLpt, hLpt, hPend κ3 .one trivial, hPend κ3 .zero trivial] at c1
      rw [hPend κ3 .zero trivial, hPend κ3 .one trivial]
      exact RT2.symm hW (hXL _) c1
    rw [eL (κ.comp κ') .one]
    dsimp only
    by_cases hf : I.Entails .one (ψ.subst κ.τ)
    · -- the face holds: the bases
      have hf2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := by rw [← eψ]; exact ent_one_subst hf _
      have hf2' : I.Entails .one (ψ'.subst (κ.comp κ').τ) := ent_trans hf2 (ent_subst h12 _)
      rw [if_pos hf, if_pos hf2', ex]
      have h := hb (κ.comp κ')
      rw [← hPend (κ.comp κ') .zero trivial] at h
      exact RE2.conv hW (hconst _ hf2) h
    -- the face does not hold: the left reduct, restricted
    have hPLl : ∀ {k6 : ℕ} (θ : ISub k6 (K + 1)), IsList (P.isub θ) := fun θ => isList_subst hPl _ _
    have hPLlen : ∀ {k6 : ℕ} (θ : ISub k6 (K + 1)), (P.isub θ).toList.length = D.params.length := fun θ => by
      show (P.subst Tm.var θ.τ).toList.length = _
      rw [toList_subst hPl]; simp [hPlen]
    rw [if_neg hf, tCon_isub hW hD (hC k4 κ) (hPLl _) (hPLlen _) (hZl k4 κ) κ', eLine, eψ]
    have hPθ2 := HasTy.isubS hW hP (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
      ((ρ.comp σ).comp (κ.comp κ')).up.tail)
    -- the restricted normal form of the left base, against the left base at the restriction
    have R0 : RE2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero)
        (.con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) []) (x.isub (σ.comp (κ.comp κ'))) := by
      have r0 := RE2.isub hW (RE2_whnf_con hW hD hH hP hPP1 _ (hb κ) (hC k4 κ) (hr k4 κ)) κ'
      rw [show (Tm.con d (c k4 κ) (qs k4 κ) (Tm.ofList (Z k4 κ)) []).isub κ' =
          .con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) [] by
        show Tm.con d _ ((qs k4 κ).isub κ') ((Tm.ofList (Z k4 κ)).isub κ') [] = _; rw [ofList_isub], ex] at r0
      rw [show (Tm.data d (P.isub (ISub.cons ((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ)
          (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) ((ρ.comp σ).comp κ)))).isub κ' =
          .data d (P.isub (ISub.cons (((y.subst κ.up.τ).subst (ISub.cons .zero trivial (ISub.id k4)).τ).subst κ'.τ)
            (I.scoped_subst (I.scoped_subst (I.scoped_subst hy κ.up.sc) (ISub.cons .zero trivial (ISub.id k4)).sc) κ'.sc)
            ((ρ.comp σ).comp (κ.comp κ')))) by
        show Tm.data d ((P.isub _).isub _) = _; rw [Tm.isub_isub, ISub.cons_comp, eT]] at r0
      rw [hPend (κ.comp κ') .zero trivial]
      refine RE2.conv hW (hRL k5 _ _ _ _ _ ?_) r0
      exact I_eq_trans (I_eq_subst (ieq_zero_up h0 κ) κ'.τ) (I_eq_symm (ieq_zero_up h0 (κ.comp κ')))
    have hA0 : RT2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero)
        (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero) := by
      rw [hPend (κ.comp κ') .zero trivial]; exact hRL k5 _ _ _ _ _ (I_eq_refl _)
    have LC2 : LineConst S k5 (.data d (P.isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail))) (ψ.subst (κ.comp κ').τ) := by
      have := LineConst.isub LC (κ.comp κ'); rwa [line_isub_up] at this
    have e0 := (RE2.typed R0).2.2.symm
    have rb := transp_rebase hW (htyκ (κ.comp κ')) e0
    by_cases hf2' : I.Entails .one (ψ'.subst (κ.comp κ').τ)
    · -- the face holds at the further restriction: the contractum, against the base
      have hf2 : I.Entails .one (ψ.subst (κ.comp κ').τ) := ent_trans hf2' (ent_subst h21 _)
      rw [if_pos hf2']
      have R00 := RE2.trans hW hA0 R0 (RE2.symm hW hA0 R0)
      have TF := tcon_face hW hD hp hH (hC k4 κ) hPθ2 (Rob.line hRL _ _ _ _ _ (I_eq_refl _)) LC2
        (I.scoped_subst hψs (κ.comp κ').sc) hf2 rb.1 R00
      have hc := hconst (κ.comp κ') hf2
      have R0' := RE2.conv hW hc R0
      have hb2 := hb (κ.comp κ')
      rw [← hPend (κ.comp κ') .zero trivial] at hb2
      have hb2' := RE2.conv hW hc hb2
      have hA1 := RT2.refl' hW (RE2.tyCode hW R0) hc
      exact RE2.trans hW hA1 TF (RE2.trans hW hA1 R0' hb2')
    -- the face does not hold at the further restriction: the contracta
    rw [if_neg hf2']
    have hf2n : ¬ I.Entails .one (ψ.subst (κ.comp κ').τ) := fun h => hf2' (ent_trans h (ent_subst h12 _))
    have eA : ∀ (σ2 : ISub k5 k1), (Tm.data d ((P.dinst .zero).isub ρ)).isub σ2 = Tm.data d ((P.dinst .zero).isub (ρ.comp σ2)) :=
      fun σ2 => by show Tm.data d (((P.dinst .zero).isub ρ).isub σ2) = _; rw [Tm.isub_isub]
    have eT3 : (ρ.comp σ).comp (κ.comp κ') = ρ.comp (σ.comp (κ.comp κ')) := ISub.comp_assoc _ _ _
    -- the start of the line, against the type of the bases
    have hAeq : TyEq S k5 (.data d (P.isub (ISub.cons ((y.subst (κ.comp κ').up.τ).subst (ISub.cons .zero trivial (ISub.id k5)).τ)
        (I.scoped_subst (I.scoped_subst hy (κ.comp κ').up.sc) (ISub.cons .zero trivial (ISub.id k5)).sc)
        ((ρ.comp σ).comp (κ.comp κ')))))
        ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp (κ.comp κ'))) := by
      rw [eA, P0_isub hW hD hp hP hArgK hRL, ← eT3]
      exact tyB (hRL k5 _ _ _ _ _ (ieq_zero_up h0 (κ.comp κ')))
    -- the constructors agree
    have R0P := R0
    rw [hPend (κ.comp κ') .zero trivial] at R0P
    obtain ⟨c3, C3, q3, W, q3', W', hC3, -, -, hr3, hr3', -, -⟩ := dataLit_args hW hD hH hP hPP1 _ R0P
    have g1 := RedW.unique hr3.1 (redW_self (step_con_nonHIT hD hH (hC k4 κ) _ _ _))
    have g2 := RedW.unique hr3'.1 (hr k5 (κ.comp κ')).1
    simp only [Tm.con.injEq] at g1 g2
    obtain ⟨-, rfl, -, -, -⟩ := g1
    obtain ⟨-, hcc, -, -, -⟩ := g2
    have hcc' : c k5 (κ.comp κ') = c k4 κ := by rw [← hcc]
    have hCC : C k5 (κ.comp κ') = C k4 κ := by
      have h1 := hC k5 (κ.comp κ'); rw [hcc', hC k4 κ] at h1; exact (Option.some.inj h1).symm
    have hAeq2 : TyEq S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .zero)
        ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp (κ.comp κ'))) := by
      rw [hPend (κ.comp κ') .zero trivial]; exact hAeq
    -- (R1) the restricted normal form of the left base, against the left base, along the left line
    have T1 := ihc k4 (σ.comp κ) _ (hr k4 κ).1 k5 κ'
    rw [ISub.comp_assoc σ κ κ', show (Tm.con d (c k4 κ) (qs k4 κ) (Tm.ofList (Z k4 κ)) []).isub κ' =
      Tm.con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) [] by
        show Tm.con d _ ((qs k4 κ).isub κ') ((Tm.ofList (Z k4 κ)).isub κ') [] = _; rw [ofList_isub]] at T1
    have hcon := (RE2.typed R0).1.tyConv hAeq2
    have RE1 : RedE S k5 ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp (κ.comp κ')))
        (Tm.con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) [])
        (Tm.con d (c k4 κ) ((qs k4 κ).isub κ') (Tm.ofList ((Z k4 κ).map (·.isub κ'))) []) :=
      ⟨redW_self (step_con_nonHIT hD hH (hC k4 κ) _ _ _), EqTm.refl hcon⟩
    have RE2' : RedE S k5 ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp (κ.comp κ'))) (x.isub (σ.comp (κ.comp κ')))
        (Tm.con d (c k4 κ) (qs k5 (κ.comp κ')) (Tm.ofList (Z k5 (κ.comp κ'))) []) := by
      have h := hr k5 (κ.comp κ'); rw [hcc'] at h; exact ⟨h.1, h.2.tyConv hAeq⟩
    have RE3 : RedE S k5 ((Tm.data d ((P.dinst .zero).isub ρ)).isub (σ.comp (κ.comp κ'))) (x'.isub (σ.comp (κ.comp κ')))
        (Tm.con d (c k4 κ) (qs' k5 (κ.comp κ')) (Tm.ofList (Z' k5 (κ.comp κ'))) []) := by
      have h := hr' k5 (κ.comp κ'); rw [hcc'] at h; exact ⟨h.1, h.2.tyConv hAeq⟩
    have LCm := LC2
    have htyA := rb.1
    have htyB := htyκ (κ.comp κ')
    have htyB' := htyκ' (κ.comp κ')
    have heqAB := rb.2.symm
    have heqm := heqκ (κ.comp κ')
    rw [eT3] at LCm htyA htyB htyB' heqAB heqm
    have R1 := T1 (ρ.comp (σ.comp (κ.comp κ'))) (by simp only [ISub.hom_comp]) (eA _) P hRL _ _
      (I.scoped_subst hy (κ.comp κ').up.sc) (I.scoped_subst hy (κ.comp κ').up.sc) (I_eq_refl _) (ieq_zero_up h0 (κ.comp κ'))
      (c k4 κ) (C k4 κ) _ _ _ _ (hC k4 κ) RE1 RE2' (ψ.subst (κ.comp κ').τ) (ψ.subst (κ.comp κ').τ)
      (I.scoped_subst hψs (κ.comp κ').sc) (ent_refl _) (ent_refl _) LCm htyA htyB heqAB
    -- (R2) the bases at the further restriction
    have T2 := ih k5 (σ.comp (κ.comp κ'))
    have R2 := T2 (ρ.comp (σ.comp (κ.comp κ'))) (by simp only [ISub.hom_comp]) (eA _) Q hQ _ _
      (I.scoped_subst hy (κ.comp κ').up.sc) (I.scoped_subst hy' (κ.comp κ').up.sc) (I_eq_subst hE _)
      (ieq_zero_up h0 (κ.comp κ')) (c k4 κ) (C k4 κ) _ _ _ _ (hC k4 κ) RE2' RE3 (ψ.subst (κ.comp κ').τ)
      (ψ'.subst (κ.comp κ').τ) (I.scoped_subst hψs (κ.comp κ').sc) (ent_subst h12 _) (ent_subst h21 _) LCm htyB htyB' heqm
    rw [← eT3] at R1 R2
    rw [hcc', hCC]
    have hA1 : RT2 S k5 (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .one)
        (((Tm.data d P).isub (ISub.cons (y.subst (κ.comp κ').up.τ) (I.scoped_subst hy (κ.comp κ').up.sc)
        ((ρ.comp σ).comp (κ.comp κ')).up.tail)).dinst .one) := by
      rw [hPend (κ.comp κ') .one trivial]; exact hRL k5 _ _ _ _ _ (I_eq_refl _)
    exact RE2.trans hW hA1 R1 R2

/-- Transport of related elements of the start of the line, by induction on their relation. -/
theorem transp_DR2 : ∀ {k1 : ℕ} {g : Hom k1 K} {A x x' : Tm},
    DR2 S d (dataD S d) (dataMem S (ΘK S D d K (P.dinst .zero)) (Hom.id K))
      (dataP2 S (ΘK S D d K (P.dinst .zero)) (Hom.id K)) k1 g A x x' →
    TM1 S d K P k1 g A x x' := by
  have hdD := dataD_eq hW hD
  intro k1 g A x x' h
  refine DR2.rec (motive_1 := fun k1 g A x x' _ => TM1 S d K P k1 g A x x')
    (motive_2 := fun k1 g A y y' _ => TM2 S d D K P k1 g A y y') ?_ ?_ ?_ h
  · intro k1 g A x x' he _ _ _ ih ihc _
    exact tm1_intro hW hD hH hp hP hArgK hRL ih ihc
  · intro k1 g A t t' ps qs qs' c C args args' rs rs' hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl'
      hrec hpt ihrec
    exact tm2_con hW hD hH hp hP hArgK hRL (DR2At.con hm hm' heq hC hA hpl ht ht' hrs hrs' hreq hsc hsc' hl hl' hrec hpt)
      hC hA ht ht' hl hl' ihrec
  · intro k1 g A t t' ps qs qs' u u' a a' φ φ' hm hm' heq hH' _
    have : D.isHIT = true := hdD ▸ hH'
    rw [hH] at this; cases this

/-- Transport along a literal line of an inductive type without path constructors, against a robustly
related literal line. -/
theorem kanT2_lit {Q : Tm} (hQ : Rob S d K P Q) : KanT2 S K (.data d P) (.data d Q) := by
  intro hLR φ φ' a a' hLC hty hty' heq h12 h21 ha
  have hPc := data_closed hW hD hP
  have hP0 := P0_ty hW hD hp hP hArgK hRL
  have hP0c : (P.dinst .zero).closedB 0 K = true := data_closed hW hD hP0
  have hac := closed_of_ty hW (RE2.typed ha).1
  have hac' := closed_of_ty hW (RE2.typed ha).2.1
  have ha' : RE2 S K (.data d ((P.dinst .zero).isub (ISub.id K))) a a' := by
    rw [isub_id_of_closed hP0c]; exact ha
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP0 (ISub.id K)).1 ha'
  have T := transp_DR2 hW hD hH hp hP hArgK hRL hdr (ISub.id K) rfl rfl Q hQ K (ISub.id K) (.var 0) (.var 0)
    (show 0 < K + 1 by omega) (show 0 < K + 1 by omega) (I_eq_refl _) (I_eq_refl _)
  have hQc : (Tm.data d Q).closedB 0 (K + 1) = true := by
    obtain ⟨l', ⟨hLt', -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty') rfl
    exact closed_ty hLt'
  rw [ISub.comp_id, ISub.cons_var0_up_tail, isub_up_id_of_closed (show (Tm.data d P).closedB 0 (K + 1) = true from
    closed_of_ty hW hP), isub_up_id_of_closed hQc, isub_id_of_closed hac, isub_id_of_closed hac'] at T
  exact T hLR φ φ' hLC hty hty' heq h12 h21 ha

end ind

end

end Model.Whnf
