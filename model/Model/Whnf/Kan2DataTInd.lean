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
    rw [getD_eq_get' hW hD hH hP hPP (by omega), getD_eq_get' hW hD hH hP hPP (by omega)]
    cases hri : C.isRec i
    · have := dataP2_RE2 hW hD hH hP hPP ρ' hC' (by omega) (by omega) hrec hpt (show i < _ by omega)
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

section ind
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  (hp : D.params ≠ []) {K : ℕ} {P : Tm} (hP : HasTy S (K + 1) .one [] (.data d P) (.univ D.level))
  (hArgK : ∀ c j n (g : Hom n (K + 1)) pre, (ΘK S D d (K + 1) P).PtValid c n g pre →
    KanP2 S n ((ΘK S D d (K + 1) P).ty c j n g pre))
  (hRL : Rob S d K P P)
include hW hD hH hp hP hArgK hRL

theorem P0_ty : HasTy S K .one [] (.data d (P.dinst .zero)) (.univ D.level) := by
  have hPc := data_closed hW hD hH hP
  have := HasTy.isubS hW hP (ISub.cons .zero trivial (ISub.id K))
  rwa [show (Tm.data d P).isub (ISub.cons .zero trivial (ISub.id K)) = .data d (P.isub (ISub.cons .zero trivial (ISub.id K)))
    from rfl, isub_cons_id_of_closed hPc] at this

theorem P0_rt2 : RT2 S K (.data d (P.dinst .zero)) (.data d (P.dinst .zero)) := by
  have hPc := data_closed hW hD hH hP
  have := hRL K (ISub.id K) .zero .zero trivial trivial (I_eq_refl _)
  rwa [isub_cons_id_of_closed hPc] at this

theorem P0_isub {k1 : ℕ} (ρ : ISub k1 K) : (P.dinst .zero).isub ρ = P.isub (ISub.cons .zero trivial ρ) := by
  rw [isub_dinst]; exact isub_up_dinst P ρ .zero trivial

theorem line_dinst {k1 : ℕ} (ρ : ISub k1 K) (y : I) (hy : y.Scoped (k1 + 1)) (r : I) (hr : r.Scoped k1) :
    (P.isub (ISub.cons y hy ρ.up.tail)).dinst r =
      P.isub (ISub.cons (y.subst (ISub.cons r hr (ISub.id k1)).τ) (I.scoped_subst hy (ISub.cons r hr (ISub.id k1)).sc) ρ) := by
  have hPc := data_closed hW hD hH hP
  have hc : (P.isub (ISub.cons y hy ρ.up.tail)).closedB 0 (k1 + 1) = true :=
    data_closed hW hD hH (HasTy.isubS hW hP (ISub.cons y hy ρ.up.tail))
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
  have hP0 := P0_ty hW hD hH hp hP hArgK hRL
  have hP0P0 := P0_rt2 hW hD hH hp hP hArgK hRL
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
  have hPc := data_closed hW hD hH hP
  have hXP0 : TyCode K (semK S K (.data d (P.dinst .zero))) := tyCode_of_univ hW hP0
  have hP0ρ : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((P.dinst .zero).isub ρ)) := RT2.isub hW hXP0 hP0P0 ρ
  have hPL0 := line_dinst hW hD hH hp hP hArgK hRL ρ y hy .zero trivial
  have rel0 : RT2 S k1 (.data d ((P.dinst .zero).isub ρ)) (.data d ((P.isub (ISub.cons y hy ρ.up.tail)).dinst .zero)) := by
    rw [P0_isub hW hD hH hp hP hArgK hRL, hPL0]
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
    have T := argTy_rt2' hW hD hH (HasTy.isubS hW hP0 ρ) hP0ρ rel0 hC' hi (A := args.take i) (B := args.take i)
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
    rw [P0_isub hW hD hH hp hP hArgK hRL, hQL0]
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
  have H : TC S k1 d D (P.isub (ISub.cons y hy ρ.up.tail)) (Q.isub (ISub.cons y' hy' ρ.up.tail)) ψ ψ' _ C _ _
      args args' :=
    { hW := hW, hD := hD, hH := hH, hp := hp, hC := hC', hPL := HasTy.isubS hW hP _,
      hR := Rob.line hQ ρ y y' hy hy' hE, hRL := Rob.line hRL ρ y y hy hy (I_eq_refl _),
      hArgK := argK_restr hArgK _, hφs := hψs, h12 := h12, h21 := h21, hLC := LC, hty := rb.1,
      hty' := rb'.1.tyConv e1', heq := rb.2.symm.trans (heq.trans (rb'.2.tyConv e1')), hargs0 := hargs0,
      hrecT := fun i hi hri k3 τ z z' hz hz' hEz hz0 => by
        have h := ihrec i (by omega) (by omega) hri ρ rfl rfl Q hQ k3 τ _ _
          (I.scoped_subst hy (ISub.cons z hz τ.up.tail).sc) (I.scoped_subst hy' (ISub.cons z' hz' τ.up.tail).sc)
          (ieq_subst_cons hE hEz hz hz' τ.up.tail) (ieq_zero_comp hy h0 hz hz0 τ)
        rw [getD_eq_get' hW hD hH hP0 hP0P0 (show i < args.length by omega),
          getD_eq_get' hW hD hH hP0 hP0P0 (show i < args'.length by omega)]
        show KanT2At S k3 (Tm.data d ((P.isub _).isub _)) (Tm.data d ((Q.isub _).isub _)) _ _
        rw [Tm.isub_isub, Tm.isub_isub, line_comp, line_comp, ISub.comp_up_tail]
        exact h }
  exact H.rel

end ind

end

end Model.Whnf
