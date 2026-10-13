import Model.Canon.Fund

/-!
# Canonicity: composition in the universe

`hcomp U [φ ↦ u] u0` computes to a Glue type whose equivalence is `lineEquiv` of the reversed
tube. Its computability uses the fundamental lemma on Kan-free terms, with the Kan operations at
lines of types of the universe (covered by the induction hypothesis over codes of level `l`).
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem I.up_scoped_all {τ : ℕ → I} {k : ℕ} (hτ : ∀ i, (τ i).Scoped k) : ∀ i, (I.up τ i).Scoped (k + 1)
  | 0 => show (0 : ℕ) < k + 1 by omega
  | i + 1 => I.scoped_shift (hτ i)

/-- A term-closed instance of a closed type is one of its restrictions. -/
theorem subst_isub_ofFun {X : Tm} {n k' : ℕ} (hc : X.closedB 0 n = true) (γ : ℕ → Tm) (τ : ℕ → I)
    (hτ : ∀ i < n, (τ i).Scoped k') : X.subst γ τ = X.isub (ISub.ofFun n τ hτ) := by
  rw [isub_ofFun hc]
  exact closed_subst_eq X 0 n γ .var τ τ hc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun _ _ => rfl)

/-- The identity computable substitution at stage `k` (closed terms at stage `k`). -/
def CSub.idS (S : Sig) (k : ℕ) : CSub S k .one [] k where
  σ := ISub.id k
  γ := lsub [] 0
  face := ent_refl _
  nat _ := fun _ _ => rfl
  look x A h := by simp [Ctx.lookup] at h

theorem hyp_zero : Hyp S 0 := ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ hd => absurd hd (Nat.not_lt_zero _)⟩

variable (hW : WfSig S) (hGC : GlueCompat S)
include hW

omit hW in
theorem CSub.idS_subst {t : Tm} (hc : t.closedB 0 k = true) : t.subst (CSub.idS S k).γ (CSub.idS S k).σ.τ = t :=
  closed_subst_id hc (fun x hx => absurd hx (Nat.not_lt_zero _)) (fun i hi => by simp [CSub.idS, ISub.id, hi])

include hGC in
/-- The fundamental lemma for a closed Kan-free term at stage `k`. -/
theorem fund_closed {t A : Tm} (ht : HasTy0 S k .one [] t A) (hK : KOK S 0 False t) : RE S k A t := by
  have h := fund_ty hW (O := False) False.elim hyp_zero hGC ht hK k (CSub.idS S k)
  have hs := minimal_to_spec ht
  rwa [CSub.idS_subst (closed_of_ty hW hs), CSub.idS_subst (closed_of_isTyK hW (isTyK_of_ty hW hs))] at h

variable {l : ℕ} (ih : ∀ m' X, WF l m' X → KR S m' X ∧ KanP S m' X)
include ih

theorem kanH_of_ty {X : Tm} (hX : HasTy S k .one [] X (.univ l)) (hR : RT S k X) : KanH S k X := by
  have hm := ((RE_univ_iff hW).1 (RE_univ_of hW hX hR)).2.1
  exact (ih k _ (ZFSet.mem_sep.1 hm).2).2.1 k (Hom.id k) X hR

theorem kanT_of_ty {X : Tm} (hX : HasTy S (k + 1) .one [] X (.univ l)) (hR : RT S (k + 1) X) : KanT S k X := by
  have hm := ((RE_univ_iff hW).1 (RE_univ_of hW hX hR)).2.1
  exact (ih (k + 1) _ (ZFSet.mem_sep.1 hm).2).2.2 k (Hom.id (k + 1)) X hR

/-- Transport along any instance of a computable line of types of level `l`. -/
theorem nkt_inst {n : ℕ} {B : Tm} (hB : HasTy S n .one [] B (.univ l)) (hR : ∀ k' (ρ : ISub k' n), RT S k' (B.isub ρ))
    (γ0 : ℕ → Tm) (τ0 : ℕ → I) : NKT S (B.subst γ0 τ0) := by
  intro k γ τ l' hτ _
  have hc := closed_of_ty hW hB
  have hsc : ∀ i < n, ((τ0 i).subst (I.up τ)).Scoped (k + 1) := fun i _ =>
    I.scoped_subst_all (I.up_scoped_all hτ) _
  rw [subst_subst, subst_isub_ofFun hc _ _ hsc]
  exact ⟨hR _ _, kanT_of_ty hW ih (HasTy.isubS hW hB _) (hR _ _)⟩

/-- Composition in any instance of a computable type of level `l`. -/
theorem nkh_inst {n : ℕ} {B : Tm} (hB : HasTy S n .one [] B (.univ l)) (hR : ∀ k' (ρ : ISub k' n), RT S k' (B.isub ρ))
    (γ0 : ℕ → Tm) (τ0 : ℕ → I) : NKH S (B.subst γ0 τ0) := by
  intro k γ τ l' hτ _
  have hc := closed_of_ty hW hB
  have hsc : ∀ i < n, ((τ0 i).subst τ).Scoped k := fun i _ => I.scoped_subst_all hτ _
  rw [subst_subst, subst_isub_ofFun hc _ _ hsc]
  exact ⟨hR _ _, kanH_of_ty hW ih (HasTy.isubS hW hB _) (hR _ _)⟩

omit hW ih in
theorem isEquiv_subst' (T A f : Tm) (σ : ℕ → Tm) (τ : ℕ → I) :
    (Tm.isEquiv T A f).subst σ τ = Tm.isEquiv (T.subst σ τ) (A.subst σ τ) (f.subst σ τ) := by
  simp only [Tm.isEquiv, Tm.isContr, Tm.fiber, Tm.pathC]; scalc
omit hW ih in
theorem arrow_subst' (T A : Tm) (σ : ℕ → Tm) (τ : ℕ → I) :
    (Tm.arrow T A).subst σ τ = Tm.arrow (T.subst σ τ) (A.subst σ τ) := by
  simp only [Tm.arrow]; scalc

omit ih in
include hGC in
/-- `isEquiv T A f` is computable for computable `T`, `A`, `f`: the fundamental lemma on a generic,
Kan-free term. -/
theorem RT_isEquiv (hl : l + 1 ≤ maxLevel) {T A f : Tm}
    (hT : RE S k (.univ l) T) (hA : RE S k (.univ l) A) (hf : RE S k (Tm.arrow T A) f) :
    RT S k (Tm.isEquiv T A f) := by
  have hS := sigClosed_of_wfSig hW
  have w0 : Wf0 S k .one [] := Wf0.nil trivial
  have hU0 : HasTy0 S k .one [] (.univ l) (.univ (l + 1)) := HasTy0.univ hl w0
  have w1 : Wf0 S k .one [.univ l] := Wf0.cons hU0
  have hU1 : HasTy0 S k .one [.univ l] (.univ l) (.univ (l + 1)) := HasTy0.univ hl w1
  have w2 : Wf0 S k .one [.univ l, .univ l] := Wf0.cons hU1
  have harr : HasTy0 S k .one [.univ l, .univ l] (Tm.arrow (.var 1) (.var 0)) (.univ l) :=
    arrow_typed hS (HasTy0.var w2 rfl) (HasTy0.var w2 rfl)
  have w3 : Wf0 S k .one [Tm.arrow (.var 1) (.var 0), .univ l, .univ l] := Wf0.cons harr
  have hG : HasTy0 S k .one [Tm.arrow (.var 1) (.var 0), .univ l, .univ l]
      (Tm.isEquiv (.var 2) (.var 1) (.var 0)) (.univ l) :=
    isEquiv_typed hS (HasTy0.var w3 rfl) (HasTy0.var w3 rfl) (HasTy0.var w3 rfl)
  have hf' : RE S k ((Tm.arrow (.var 1) (.var 0)).subst
      (((CSub.idS S k).ext hW (.univ l) T hT).ext hW (.univ l) A hA).γ
      (((CSub.idS S k).ext hW (.univ l) T hT).ext hW (.univ l) A hA).σ.τ) f := by
    rw [arrow_subst']; exact hf
  have h := fund_ty hW (O := False) False.elim hyp_zero hGC hG (by simp [Tm.isEquiv, Tm.isContr, Tm.fiber, Tm.pathC, Tm.shift, Tm.dshift, Tm.ren, KOK]) k
    ((((CSub.idS S k).ext hW (.univ l) T hT).ext hW (.univ l) A hA).ext hW _ f hf')
  rw [isEquiv_subst'] at h
  exact ((RE_univ_iff hW).1 h).2.2

omit ih in
/-- Instances of a type computable at all restrictions are computable. -/
theorem re_univ_inst {n : ℕ} {B : Tm} (hB : HasTy S n .one [] B (.univ l)) (hR : ∀ k' (ρ : ISub k' n), RT S k' (B.isub ρ))
    (γ0 : ℕ → Tm) (τ0 : ℕ → I) (hτ : ∀ i, (τ0 i).Scoped k') : RE S k' (.univ l) (B.subst γ0 τ0) := by
  rw [subst_isub_ofFun (closed_of_ty hW hB) _ _ (fun i _ => hτ i)]
  exact RE_univ_of hW (HasTy.isubS hW hB _) (hR _ _)

theorem kok_lineFun {B : Tm} (hB : HasTy S (k + 1) .one [] B (.univ l))
    (hR : ∀ k' (ρ : ISub k' (k + 1)), RT S k' (B.isub ρ)) : KOK S 0 False (Tm.lineFun B) := by
  refine ⟨trivial, .inr ?_, trivial⟩
  show NKT S ((B.shift).dsubst _)
  rw [Tm.dsubst, Tm.shift, subst_ren]
  exact nkt_inst hW ih hB hR _ _

include hGC in
theorem RE_lineFun {B : Tm} (hB : HasTy S (k + 1) .one [] B (.univ l))
    (hR : ∀ k' (ρ : ISub k' (k + 1)), RT S k' (B.isub ρ)) :
    RE S (k + 1) (Tm.arrow (B.dinst .zero).dshift B) (Tm.lineFun B) :=
  fund_closed hW hGC (lineFun_typed (sigClosed_of_wfSig hW) (Ψ := k) (Φ := .one) (Γ := []) (spec_to_minimal hW hB)).1
    (kok_lineFun hW ih hB hR)


include hGC in
/-- Transport along a computable line of types is a computable equivalence. -/
theorem RE_lineEquiv (hl : l + 1 ≤ maxLevel) {B : Tm} (hB : HasTy S (k + 1) .one [] B (.univ l))
    (hR : ∀ k' (ρ : ISub k' (k + 1)), RT S k' (B.isub ρ)) :
    RE S k (Tm.equiv (B.dinst .zero) (B.dinst .one)) (Tm.lineEquiv B) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hB
  have hB0 : HasTy0 S k .one [] (B.dinst .zero) (.univ l) := HasTy0.dsubst hS (Ψ := k) (Φ := .one) (Γ := []) h0 (r := .zero) trivial
  have hB0d := HasTy0.dwk hS hB0
  have hlf := (lineFun_typed hS (Ψ := k) (Φ := .one) (Γ := []) h0).1
  have hL : HasTy S (k + 1) .one [] (Tm.isEquiv (B.dinst .zero).dshift B (Tm.lineFun B)) (.univ l) :=
    minimal_to_spec (isEquiv_typed hS hB0d h0 hlf)
  have hkf := kok_lineFun hW ih hB hR
  refine fund_closed hW hGC (lineEquiv_typed hS (Ψ := k) (Φ := .one) (Γ := []) h0)
    ⟨KOK.subst _ hkf (fun _ => trivial), .inr ?_, by simp [Tm.idIsEquiv, KOK]⟩
  intro k' γ τ l' hτ _
  rw [subst_isub_ofFun (closed_of_ty hW hL) γ (I.up τ) (fun i _ => I.up_scoped_all hτ i)]
  generalize ISub.ofFun (k + 1) (I.up τ) _ = ρ
  have hRT : RT S (k' + 1) ((Tm.isEquiv (B.dinst .zero).dshift B (Tm.lineFun B)).isub ρ) := by
    rw [Tm.isub, isEquiv_subst']
    refine RT_isEquiv hW hGC hl ?_ (re_univ_inst hW hB hR _ _ ρ.scAll) ?_
    · rw [Tm.dshift, ren_eq_subst, Tm.dinst, Tm.dsubst, subst_subst, subst_subst]
      exact re_univ_inst hW hB hR _ _ (fun i => I.scoped_subst_all (fun j => I.scoped_subst_all ρ.scAll _) _)
    · have := (RE_lineFun hW hGC ih hB hR).isub hW ρ
      rwa [Tm.isub, Tm.isub, arrow_subst'] at this
  exact ⟨hRT, kanT_of_ty hW ih (HasTy.isubS hW hL ρ) hRT⟩

end

section

variable {S : Sig} {k k' m : ℕ}

theorem lineEquiv_subst' (B : Tm) (σ : ℕ → Tm) (τ : ℕ → I) :
    (Tm.lineEquiv B).subst σ τ = Tm.lineEquiv (B.subst (dupS σ) (I.up τ)) := by
  simp only [Tm.lineEquiv, Tm.lineFun, Tm.idIsEquiv, Tm.isEquiv, Tm.isContr, Tm.fiber, Tm.pathC]; scalc

/-- A face that holds stays true under further substitution. -/
theorem holds_comp {φ : I} (hφ : φ.Scoped k) (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds)
    {k'' : ℕ} (σ2 : ISub k'' k) (τ3 : ℕ → I) (e : ∀ i < k, σ2.τ i = (σ.τ i).subst τ3) :
    (ival (idEnv k'') (φ.subst σ2.τ)).holds := by
  rw [holds_iff_entails (I.scoped_subst hφ σ2.sc), I_subst_congr_scoped e hφ, ← I_subst_subst]
  exact ent_subst ((holds_iff_entails (I.scoped_subst hφ σ.sc)).1 hh) τ3

theorem ISub.cons_tail {k'' : ℕ} (ρ : ISub k'' (k + 1)) : ISub.cons (ρ.τ 0) (ρ.sc 0 (by omega)) ρ.tail = ρ := by
  ext i; rcases i with _ | i <;> rfl

/-- A computable tube, at an arbitrary restriction of its line. -/
theorem tube_all {A u : Tm} {φ : I} (hu : TubeC S k A φ u) {k'' : ℕ} (ρ : ISub k'' (k + 1))
    (hh : (ival (idEnv k'') (φ.subst ρ.tail.τ)).holds) : RE S k'' (A.isub ρ.tail) (u.isub ρ) := by
  have := hu k'' ρ.tail (ρ.τ 0) (ρ.sc 0 (by omega)) hh
  rwa [isub_up_dinst _ _ _ (ρ.sc 0 (by omega)), ISub.cons_tail] at this

/-- Composition in the universe. -/
theorem kanH_univ (hW : WfSig S) (hGC : GlueCompat S) {l : ℕ} (ih : ∀ m' X, WF l m' X → KR S m' X ∧ KanP S m' X) :
    KanH S k (.univ l) := by
  intro φ u a hty hu ha
  by_cases hφ : (ival (idEnv k) φ).holds
  · exact RE_hcomp_face hW hty hu hφ
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l0, ⟨hU, hφs, hu0, -, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hl := gen_univ hU rfl
  have e := EqTm.hcompU hty
  rw [hcompU_eq] at e
  have hG := HasTy.eqR e
  refine (RE_univ_of hW hG ?_).conv hW (TyEq.refl _) e.symm
  have hucl : u.closedB 0 (k + 1) = true := closed_ty hu0
  refine RT_glue_intro hW hG hφ (fun k' σ => ((RE_univ_iff hW).1 (ha.isub hW σ)).2.2) (fun k' σ hh => ?_)
    (fun k' σ hh => ?_)
  · have h1 := tube_all hu (ISub.cons .one trivial σ) hh
    have e1 : (u.dinst .one).isub σ = u.isub (ISub.cons .one trivial σ) := by
      simp only [Tm.isub, Tm.dinst, Tm.dsubst, subst_subst]; congr 1; funext i; cases i <;> rfl
    rw [e1]; exact ((RE_univ_iff hW).1 h1).2.2
  have hsc : ∀ i < k + 1, ((revI i).subst (I.up σ.τ)).Scoped (k' + 1) := fun i _ =>
    I.scoped_subst_all (I.up_scoped_all σ.scAll) _
  have eB : (u.dsubst revI).subst (dupS Tm.var) (I.up σ.τ) = u.isub (ISub.ofFun (k + 1) _ hsc) := by
    rw [isub_ofFun hucl, Tm.dsubst, subst_subst]; rfl
  have f1 : ∀ i < k, (ISub.ofFun (k + 1) _ hsc).τ (i + 1) = (σ.τ i).shift := fun i hi => by
    simp only [ISub.ofFun, if_pos (show i + 1 < k + 1 by omega)]; rfl
  generalize ISub.ofFun (k + 1) _ hsc = ρB at eB f1
  have hent := entails_of_holds (I.scoped_subst hφs σ.sc) hh
  -- the restricted tube `D` at stage `k' + 1`, typed in the empty face
  have hDre := tube_all hu σ.up (holds_comp hφs σ hh σ.up.tail (fun j => .var (j + 1)) (fun i _ => rfl))
  have hD0 := spec_to_minimal hW ((RE_univ_iff hW).1 hDre).1
  have eqD : ∀ x1 x2 : I, x1.Scoped k' → x2.Scoped k' → I.Eq x1 x2 →
      EqTm S k' .one [] ((u.isub σ.up).dinst x1) ((u.isub σ.up).dinst x2) (.univ l) := fun x1 x2 h1 h2 he => by
    have sc : ∀ x : I, x.Scoped k' → ∀ i < k' + 1, ((I.inst0 x) i).Scoped k' := fun x hx i hi => by
      rcases i with _ | i
      · exact hx
      · show i < k'; omega
    exact ieq0 hW hD0 (sc x1 h1) (sc x2 h2) (fun i _ => by
      rcases i with _ | i
      · exact he
      · exact I_eq_refl _)
  have erev : ∀ x : I, ((u.dsubst revI).subst (dupS Tm.var) (I.up σ.τ)).dinst x = (u.isub σ.up).dinst (.neg x) := by
    intro x
    simp only [Tm.dinst, Tm.dsubst, Tm.isub, subst_subst]
    congr 1
    funext i; rcases i with _ | i
    · rfl
    · show ((σ.τ i).shift).subst _ = ((σ.τ i).shift).subst _; rw [I_shift_inst0, I_shift_inst0]
  have eend : ∀ x : I, x = .zero ∨ x = .one → (u.dinst x).isub σ = (u.isub σ.up).dinst x := by
    rintro x (rfl | rfl) <;>
    · simp only [Tm.dinst, Tm.dsubst, Tm.isub, subst_subst]
      congr 1
      funext i; rcases i with _ | i
      · rfl
      · show σ.τ i = ((σ.τ i).shift).subst _; rw [I_shift_inst0]
  have hRB : ∀ k'' (ρ : ISub k'' (k' + 1)), RE S k'' (.univ l) ((u.isub ρB).isub ρ) := fun k'' ρ => by
    rw [Tm.isub_isub]
    exact tube_all hu (ρB.comp ρ) (holds_comp hφs σ hh _ ρ.tail.τ (fun i hi => by
      show (ρB.τ (i + 1)).subst ρ.τ = _; rw [f1 i hi, I.shift, I.ren, I_subst_subst]; rfl))
  have hBt : HasTy S (k' + 1) .one [] (u.isub ρB) (.univ l) := by
    have := ((RE_univ_iff hW).1 (hRB _ (ISub.id _))).1; rwa [Tm.isub_isub, ISub.comp_id] at this
  have hLE := RE_lineEquiv hW hGC ih hl hBt (fun k'' ρ => ((RE_univ_iff hW).1 (hRB k'' ρ)).2.2)
  rw [← eB, erev, erev] at hLE
  show RE S k' _ ((Tm.lineEquiv _).subst Tm.var σ.τ)
  rw [lineEquiv_subst', eend _ (.inr rfl)]
  have hside' : EqTm S k' .one [] ((u.dinst .zero).isub σ) (a.isub σ) (.univ l) :=
    EqTm.restrict trivial (ent_cof_one hW hent) (EqTm.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩)
      (minimal_to_spec_eq hside) σ)
  rw [eend _ (.inl rfl)] at hside'
  have e0 := eqD (.neg .zero) .one trivial trivial I_eq_neg_zero
  have e1 := (eqD (.neg .one) .zero trivial trivial I_eq_neg_one).trans hside'
  have hU' : HasTy0 S k' .one [] (.univ l) (.univ (l + 1)) := HasTy0.univ hl (Wf0.nil trivial)
  have hX1 := spec_to_minimal hW (HasTy.eqL e1)
  have hY0 := spec_to_minimal hW (HasTy.eqR e0)
  have fam1 := minimal_to_spec (equiv_typed hS (HasTy0.var (x := 0) (Wf0.cons hU') rfl) (HasTy0.wk hS hU' hX1))
  have step1 := EqTm.subst (EqTm.refl fam1) e0
  rw [equiv_inst1, equiv_inst1] at step1
  have fam2 := minimal_to_spec (equiv_typed hS (HasTy0.wk hS hU' hY0) (HasTy0.var (x := 0) (Wf0.cons hU') rfl))
  have step2 := EqTm.subst (EqTm.refl fam2) e1
  rw [equiv_inst2, equiv_inst2] at step2
  exact hLE.conv_ty hW (.inr ⟨l, step1.trans step2⟩)


/-- Transport in the universe is the identity. -/
theorem kanT_univ (hW : WfSig S) {l : ℕ} : KanT S k (.univ l) := fun _ _ hty ha =>
  ha.conv hW (TyEq.refl _) (EqTm.transpU hty).symm

theorem kanP_univ (hW : WfSig S) (hGC : GlueCompat S) {l : ℕ} (ih : ∀ m' X, WF l m' X → KR S m' X ∧ KanP S m' X) :
    KanP S m (univC m l) := by
  refine ⟨fun k f T hT => ?_, fun k f T hT => ?_⟩
  · rw [Comp_univC] at hT
    exact kanH_retype hW hT.2 (kanH_univ hW hGC ih)
  · rw [Comp_univC] at hT
    rcases hT.2 with rfl | ⟨l', e⟩
    · exact kanT_univ hW
    · exact kanT_retype hW e (kanT_univ hW)

end

end Model.Canon
