import Model.Whnf.Kan2DataHC5

/-!
# The binary composition at inductive types without path constructors

By induction on the relation of the base (`hcomp_DR2`): at each stage the composition reduces to the
`hcompCon` contractum of the base's normal form, related by `HCC.hcompCon2`; the coherence of the
normal forms comes from the coherence of the base, and, where the face comes to hold, from
`face_con`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

theorem isList_dshift {ps : Tm} (h : IsList ps) : IsList ps.dshift := by
  rw [dshift_eq]; exact isList_subst h _ _

theorem dshift_toList_length {ps : Tm} (h : IsList ps) : ps.dshift.toList.length = ps.toList.length := by
  rw [dshift_toList' h]; simp

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

theorem tubeArgs_isub {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q u : Tm} (hq : IsList q)
    (hql : q.toList.length = D.params.length) (κ : ISub k' k) :
    (tubeArgs d D c C q u).map (·.subst Tm.var (I.up κ.τ)) = tubeArgs d D c C (q.isub κ) (u.isub κ.up) := by
  have hS := sigClosed_of_wfSig hW
  have hq1 : IsList q.dshift := isList_dshift hq
  have hql1 : q.dshift.toList.length = D.params.length := by rw [dshift_toList_length hq, hql]
  apply List.ext_getElem (by simp [tubeArgs])
  intro j h1 h2
  have hj : j < C.args.length := by simpa [tubeArgs] using h2
  simp only [tubeArgs, List.getElem_map, List.getElem_range]
  rw [proj_dsubst hS hD hC hj hq1 hql1]
  congr 1
  show q.dshift.isub κ.up = (q.isub κ).dshift
  exact isub_dshift q κ

omit hW hD in
theorem conOuts_eq_tele {c : ℕ} {C : Ctor} (q : Tm) (φ : I) (u : Tm) (X : List Tm) (hXl : X.length = C.args.length) :
    conOuts d D c C q φ u X = Tm.hcompTele C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ 0 []
      (tubeArgs d D c C q u) X := by
  have hul : (tubeArgs d D c C q u).length = C.args.length := by simp [tubeArgs]
  have heqT := Meta.hcompTele_eq C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ
    (tubeArgs d D c C q u) X (tubeArgs d D c C q u) X 0 rfl rfl (by rw [hul, hXl])
  simp only [hXl, ← List.range_eq_range'] at heqT
  rw [show ([] : List Tm) = (Meta.hFills C (C.argTy d D.params.length) (.data d q) q.dshift.toList
    φ (tubeArgs d D c C q u) X 0).reverse from rfl, heqT]
  rfl

omit hW in
/-- `hcompCon` as a step, with its contractum's arguments. -/
theorem step_hcompCon' (hH : D.isHIT = false) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q u qs : Tm}
    {φ : I} (hn : ¬ I.Entails .one φ) {X : List Tm} (hXl : X.length = C.args.length) :
    step S (.hcomp (.data d q) φ u (.con d c qs (Tm.ofList X) [])) =
      some (.con d c q (Tm.ofList (conOuts d D c C q φ u X)) []) := by
  rw [step_hcompCon hD hH hC hn X, conOuts_eq_tele q φ u X hXl]; rfl

/-- The arguments of the `hcompCon` contractum, restricted. -/
theorem conOuts_isub {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {q u : Tm} {φ : I} {X : List Tm}
    (hq : IsList q) (hql : q.toList.length = D.params.length) (hXl : X.length = C.args.length) (κ : ISub k' k) :
    (conOuts d D c C q φ u X).map (·.isub κ) =
      conOuts d D c C (q.isub κ) (φ.subst κ.τ) (u.isub κ.up) (X.map (·.isub κ)) := by
  have hS := sigClosed_of_wfSig hW
  have tele : ∀ (q : Tm) (φ : I) (u : Tm) (X : List Tm), X.length = C.args.length →
      conOuts d D c C q φ u X = Tm.hcompTele C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ 0 []
        (tubeArgs d D c C q u) X := by
    intro q φ u X hXl
    have hul : (tubeArgs d D c C q u).length = C.args.length := by simp [tubeArgs]
    have heqT := Meta.hcompTele_eq C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ
      (tubeArgs d D c C q u) X (tubeArgs d D c C q u) X 0 rfl rfl (by rw [hul, hXl])
    simp only [hXl, ← List.range_eq_range'] at heqT
    rw [show ([] : List Tm) = (Meta.hFills C (C.argTy d D.params.length) (.data d q) q.dshift.toList
      φ (tubeArgs d D c C q u) X 0).reverse from rfl, heqT]
    rfl
  have hq1 : IsList q.dshift := isList_dshift hq
  rw [tele q φ u X hXl, tele _ _ _ _ (by simp [hXl])]
  have hlen : q.dshift.toList.length = D.params.length := by rw [dshift_toList_length hq, hql]
  have := hcompTele_subst (σ := Tm.var) (τ := κ.τ) (C := C) (argTy := C.argTy d D.params.length)
    (np := D.params.length) (fun j => argTy_closed hS hD hC j) (dataT := .data d q) hlen φ
    (tubeArgs d D c C q u) X 0 [] rfl
  simp only [show (dupS Tm.var : ℕ → Tm) = Tm.var from funext fun n => rfl] at this
  show (Tm.hcompTele C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ 0 [] (tubeArgs d D c C q u) X).map
    (·.subst Tm.var κ.τ) = _
  rw [this, tubeArgs_isub hW hD hC hq hql κ]
  congr 1
  rw [← toList_subst hq1]
  show (q.dshift.isub κ.up).toList = _
  rw [isub_dshift]

end

/-- Compositions over given bases, in the types `L`, `L'`, related at `A` by the relation `R`. -/
def HC2R (S : Sig) (k : ℕ) (A L L' a a' : Tm) (R : Tm → Tm → Prop) : Prop :=
  ∀ (φ φ' : I) (u u' : Tm), HasTy S k .one [] (.hcomp L φ u a) A → HasTy S k .one [] (.hcomp L' φ' u' a') A →
    EqTm S k .one [] (.hcomp L φ u a) (.hcomp L' φ' u' a') A →
    EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift →
    I.Entails φ φ' → I.Entails φ' φ → Tube2 S k A φ u u' → RE2 S k A a a' →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ)) →
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) →
    R (.hcomp L φ u a) (.hcomp L' φ' u' a')

theorem HC2_iff {k : ℕ} {A L L' a a' : Tm} : HC2 S k A L L' a a' ↔ HC2R S k A L L' a a' (RE2 S k A) := Iff.rfl

section ind
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
  {K : ℕ} {P : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level)) (hPP : RT2 S K (.data d P) (.data d P))
  (hArgK : ∀ c j n (g : Hom n K) pre, (ΘK S D d K P).PtValid c n g pre → KanP2 S n ((ΘK S D d K P).ty c j n g pre))
include hW hD hH hP hPP

/-- An element is related to its normal form, a constructor. -/
theorem RE2_whnf_con {k3 : ℕ} (ρ' : ISub k3 K) {y y' : Tm} (hy : RE2 S k3 (.data d (P.isub ρ')) y y')
    {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs : Tm} {Z : List Tm}
    (hw : RedE S k3 (.data d (P.isub ρ')) y (.con d c qs (Tm.ofList Z) [])) :
    RE2 S k3 (.data d (P.isub ρ')) (.con d c qs (Tm.ofList Z) []) y := by
  have hPρ := RT2.isub hW (tyCode_of_univ hW hP) hPP ρ'
  have hyy := RE2.trans hW hPρ hy (RE2.symm hW hPρ hy)
  have hyc := closed_of_ty hW (RE2.typed hy).1
  refine RE2_conW hW hD hH hP hPP ρ' hC (HasTy.eqR hw.2) hyy hw.2.symm fun k'' κ => ?_
  obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP ρ').1 hy
  cases hdr with
  | intro _ _ hc _ =>
    have := hc k3 (ISub.id k3) _ (by rw [isub_id_of_closed hyc]; exact hw.1) k'' κ
    rw [ISub.id_comp, show (Tm.data d (P.isub ρ')).isub κ = .data d (P.isub (ρ'.comp κ)) by
      show Tm.data d ((P.isub ρ').isub κ) = _; rw [Tm.isub_isub], ← ISub.hom_comp] at this
    exact this

include hArgK in
/-- At one stage: compositions of related elements whose normal forms are constructors with related
arguments, given the compositions over the recursive arguments. -/
theorem mot2_con {k1 : ℕ} (ρ : ISub k1 K) {Q Q' : Tm} (hQ : RT2 S K (.data d P) (.data d Q))
    (hQ' : RT2 S K (.data d P) (.data d Q')) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {qs qs' : Tm}
    {X X' : List Tm} {y y' : Tm}
    (ht : RedE S k1 (.data d (P.isub ρ)) y (.con d c qs (Tm.ofList X) []))
    (ht' : RedE S k1 (.data d (P.isub ρ)) y' (.con d c qs' (Tm.ofList X') []))
    (hXl : X.length = C.args.length) (hXl' : X'.length = C.args.length)
    (hrecD : ∀ i (hi : i < X.length) (hi' : i < X'.length), C.isRec i = true →
      DR2 S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 ρ.hom
        (.data d (P.isub ρ)) X[i] X'[i])
    (hptD : ∀ i (hi : i < X.length) (hi' : i < X'.length), C.isRec i = false →
      dataP2 S (ΘK S D d K P) (Hom.id K) k1 ρ.hom c i ((X.take i).map (semK S k1))
        ((C.argTy d (dataD S d).params.length i).substList ((X.take i).reverse ++ (P.isub ρ).toList.reverse))
        X[i] X'[i])
    (ihrec : ∀ i (hi : i < X.length) (hi' : i < X'.length), C.isRec i = true → ∀ (Q1 Q1' : Tm),
      RT2 S K (.data d P) (.data d Q1) → RT2 S K (.data d P) (.data d Q1') → ∀ K2 (σ : ISub K2 k1),
      HC2 S K2 (.data d (P.isub (ρ.comp σ))) (.data d (Q1.isub (ρ.comp σ))) (.data d (Q1'.isub (ρ.comp σ)))
        (X[i].isub σ) (X'[i].isub σ)) :
    HC2R S k1 (.data d (P.isub ρ)) (.data d (Q.isub ρ)) (.data d (Q'.isub ρ)) y y'
      (DR2At S d (dataD S d) (dataMem S (ΘK S D d K P) (Hom.id K)) (dataP2 S (ΘK S D d K P) (Hom.id K)) k1 ρ.hom
        (.data d (P.isub ρ))) := by
  intro φ φ' u u' hty hty' heq hteq h12 h21 htube hyy hbd hbd'
  have hdD := dataD_eq hW hD
  have hXP := tyCode_of_univ hW hP
  have hPρ := RT2.isub hW hXP hPP ρ
  have hpσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), RT2 S k3 ((Tm.data d (P.isub ρ)).isub σ) ((Tm.data d (P.isub ρ)).isub σ) :=
    fun σ => RT2.isub hW (tyCode_of_univ hW (HasTy.isubS hW hP ρ)) hPρ σ
  obtain ⟨l0, ⟨hL, hφs, hu, hy, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨l0', ⟨hL', hφs', hu', hy', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl
  by_cases hf : I.Entails .one φ
  · -- the face holds: both sides are their tubes' ends
    have hf' : I.Entails .one φ' := ent_trans hf h12
    have hh : (ival (idEnv k1) (φ.subst (ISub.id k1).τ)).holds :=
      (holds_iff_entails (I.scoped_subst hφs (ISub.id k1).sc)).2 (ent_subst hf _)
    have h1 := htube k1 (ISub.id k1) .one .one trivial trivial (I_eq_refl _) hh
    rw [isub_id_of_closed (show (Tm.data d (P.isub ρ)).closedB 0 k1 = true from closed_of_ty hW (HasTy.isubS hW hP ρ)),
      isub_up_id_of_closed (closed_ty hu), isub_up_id_of_closed (closed_ty hu')] at h1
    obtain ⟨-, hdr⟩ := (RE2_dataLit_iff hW hD hP ρ).1 h1
    have hat := DR2.at_id hW (Θ := ΘK S D d K P) hdr
    exact DR2At.expandR hW (DR2At.expand hW hat (.step (step_hcomp_face hf) (.refl _)) (EqTm.hcompFace hf hty))
      (.step (step_hcomp_face hf') (.refl _)) (EqTm.hcompFace hf' hty')
  · -- the face does not hold: the compositions of the normal forms
    have hdq := (Comp2_ty_base (RT2.isub hW hXP hQ ρ)).2.2.2.2.2
    have hdq' := (Comp2_ty_base (RT2.isub hW hXP hQ' ρ)).2.2.2.2.2
    have hQP : TyEq S k1 (.data d (Q.isub ρ)) (.data d (P.isub ρ)) := TyEq.symm hdq
    have hQ'P : TyEq S k1 (.data d (Q'.isub ρ)) (.data d (P.isub ρ)) := TyEq.symm hdq'
    have hS := sigClosed_of_wfSig hW
    have hcs : (cof .one φ).Scoped k1 := ⟨trivial, hφs⟩
    have hcs' : (cof .one φ').Scoped k1 := ⟨trivial, hφs'⟩
    -- the compositions over the normal forms of the bases
    have eyQ := spec_to_minimal_eq hW (ht.2.tyConv hdq)
    have eyQ' := spec_to_minimal_eq hW (ht'.2.tyConv hdq')
    have hT0 := wf_typed _ S rfl hW
    have hcon := (pre_eq hS hT0.1 hT0.2 eyQ).2.1
    have hcon' := (pre_eq hS hT0.1 hT0.2 eyQ').2.1
    have hside2 := hside.trans (EqTm0.restrict hcs (ent_and_left _ _) eyQ)
    have hside2' := hside'.trans (EqTm0.restrict hcs' (ent_and_left _ _) eyQ')
    have hHL := HasTy0.hcomp hL hφs hu hcon hside2
    have hHL' := HasTy0.hcomp hL' hφs' hu' hcon' hside2'
    have hty0 := HasTy0.hcomp hL hφs hu hy hside
    have hty0' := HasTy0.hcomp hL' hφs' hu' hy' hside'
    have eL := (EqTm.hcomp (minimal_to_spec hty0) (minimal_to_spec hHL) (EqTm.refl (minimal_to_spec hL)) (ent_refl _)
      (ent_refl _) (EqTm.refl (minimal_to_spec hu)) (minimal_to_spec_eq eyQ)).tyConv hQP
    have eR := (EqTm.hcomp (minimal_to_spec hty0') (minimal_to_spec hHL') (EqTm.refl (minimal_to_spec hL'))
      (ent_refl _) (ent_refl _) (EqTm.refl (minimal_to_spec hu')) (minimal_to_spec_eq eyQ')).tyConv hQ'P
    have rL := red_hcomp_base hD hH hf ht.1.1 (u := u) (ps := Q.isub ρ)
    have rR := red_hcomp_base hD hH (fun h => hf (ent_trans h h21)) ht'.1.1 (u := u') (ps := Q'.isub ρ)
    have hyy' := RE2.trans hW hPρ (RE2.symm hW hPρ hyy) hyy
    have cy := RE2_whnf_con hW hD hH hP hPP ρ hyy hC ht
    have cy' := RE2_whnf_con hW hD hH hP hPP ρ hyy' hC ht'
    have H : HCC S d D K P Q Q' k1 ρ c C qs qs' X X' φ φ' u u' := {
      hW, hD, hH, hP, hPP, hQ, hQ', hArgK, hC, hXl, hXl'
      hrecR := fun i hi hri => by
        rw [getD_eq_get (by omega), getD_eq_get (by omega)]
        have h := hrecD i (by omega) (by omega) hri
        obtain ⟨he⟩ : Nonempty (EqTm S k1 .one [] X[i] X'[i] (.data d (P.isub ρ))) := by
          cases h with | intro he => exact ⟨he⟩
        exact (RE2_dataLit_iff hW hD hP ρ).2 ⟨⟨HasTy.eqL he, HasTy.eqR he, he⟩, h⟩
      hptR := fun i hi hri => by
        rw [getD_eq_get (by omega), getD_eq_get (by omega)]
        have := dataP2_RE2 hW hD hH hP hPP ρ hC (by omega) (by omega) hrecD hptD (by omega) (by omega) hri
        rwa [hdD] at this
      hrecH := fun i hi hri Q1 Q1' h1 h2 K2 σ => by
        rw [getD_eq_get (by omega), getD_eq_get (by omega)]
        exact ihrec i (by omega) (by omega) hri Q1 Q1' h1 h2 K2 σ
      hn := hf
      hty := (minimal_to_spec hHL).tyConv hQP
      hty' := (minimal_to_spec hHL').tyConv hQ'P
      heq := eL.symm.trans (heq.trans eR)
      hteq, h12, h21, htube
      hbd := fun k' σ hh => RE2.trans hW (hpσ σ) (hbd k' σ hh) (RE2.symm hW (hpσ σ) (RE2.isub hW cy' σ))
      hbd' := fun k' σ hh => RE2.trans hW (hpσ σ) (RE2.isub hW cy σ) (hbd' k' σ hh) }
    exact DR2At.expandR hW (DR2At.expand hW H.hcompCon2 rL eL) rR eR

end ind

end

end Model.Whnf
