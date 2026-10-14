import Model.Whnf.Kan2DataHCBase

/-!
# Composition of constructors along arbitrary tube lists

The generalization of `HCC` (`Kan2DataHC*.lean`) from the projections of a tube (`tubeArgs`) to an
arbitrary list of tubes related on the face: the `hcompCon` contracta built from two related tube
lists over related bases are related at one stage (`HCG.conRel`). `HCC` is the instance at the
projections of related tubes.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-- The arguments of an `hcompCon` contractum along the tube list `us`. -/
def gOuts (d : ℕ) (D : DataDecl) (C : Ctor) (q : Tm) (φ : I) (us X : List Tm) : List Tm :=
  (List.range C.args.length).map
    (Meta.hOut C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ us X)

/-- The fillers of the arguments of an `hcompCon` contractum along the tube list `us`. -/
def gFills (d : ℕ) (D : DataDecl) (C : Ctor) (q : Tm) (φ : I) (us X : List Tm) : List Tm :=
  Meta.hFills C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ us X C.args.length

/-- The type lines of the arguments of an `hcompCon` contractum along the tube list `us`. -/
def gLine (d : ℕ) (D : DataDecl) (C : Ctor) (q : Tm) (φ : I) (us X : List Tm) : ℕ → Tm :=
  Meta.hLine C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ us X

/-- The hypotheses of `HCG.conRel`: two `hcompCon` contracta along tube lists related on the face,
over related bases, in restrictions of literal inductive types with parameters `Q`, `Q'` related to
`P`. -/
structure HCG (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P Q Q' : Tm) (k1 : ℕ) (ρ : ISub k1 K) (c : ℕ) (C : Ctor)
    (X X' : List Tm) (φ φ' : I) (us us' : List Tm) : Prop where
  hW : WfSig S
  hD : S[d]? = some (.data D)
  hH : D.isHIT = false
  hP : HasTy S K .one [] (.data d P) (.univ D.level)
  hPP : RT2 S K (.data d P) (.data d P)
  hQ : RT2 S K (.data d P) (.data d Q)
  hQ' : RT2 S K (.data d P) (.data d Q')
  hArgK : KanShape S K (ΘK S D d K P)
  hC : D.ctors[c]? = some C
  hXl : X.length = C.args.length
  hXl' : X'.length = C.args.length
  hul : us.length = C.args.length
  hul' : us'.length = C.args.length
  hrecR : ∀ i (hi : i < C.args.length), C.isRec i = true →
    RE2 S k1 (.data d (P.isub ρ)) (X.getD i .abort) (X'.getD i .abort)
  hptR : ∀ i (hi : i < C.args.length), C.isRec i = false →
    RE2 S k1 ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (P.isub ρ).toList.reverse))
      (X.getD i .abort) (X'.getD i .abort)
  hrecH : ∀ i (hi : i < C.args.length), C.isRec i = true → ∀ (Q1 Q1' : Tm),
    RT2 S K (.data d P) (.data d Q1) → RT2 S K (.data d P) (.data d Q1') → ∀ K2 (σ : ISub K2 k1),
    HC2 S K2 (.data d (P.isub (ρ.comp σ))) (.data d (Q1.isub (ρ.comp σ))) (.data d (Q1'.isub (ρ.comp σ)))
      ((X.getD i .abort).isub σ) ((X'.getD i .abort).isub σ)
  h12 : I.Entails φ φ'
  h21 : I.Entails φ' φ
  hqT : HasTy S k1 .one [] (.data d (Q.isub ρ)) (.univ D.level)
  hq'T : HasTy S k1 .one [] (.data d (Q'.isub ρ)) (.univ D.level)
  hφs : φ.Scoped k1
  hφs' : φ'.Scoped k1
  hXq : HasTele0 S k1 .one [] (Tm.ofList X) (C.argTys d D.params.length) (Q.isub ρ).toList.reverse
  hXq' : HasTele0 S k1 .one [] (Tm.ofList X') (C.argTys d D.params.length) (Q'.isub ρ).toList.reverse
  G1 : HasTele0 S (k1 + 1) (cof .one φ).shift [] (Tm.ofList us) (C.argTys d D.params.length)
    (Q.isub ρ).dshift.toList.reverse
  G1' : HasTele0 S (k1 + 1) (cof .one φ').shift [] (Tm.ofList us') (C.argTys d D.params.length)
    (Q'.isub ρ).dshift.toList.reverse
  G3 : EqTele0 S k1 (cof .one φ) [] ((Tm.ofList us).dinst .zero) (Tm.ofList X) (C.argTys d D.params.length)
    (Q.isub ρ).toList.reverse
  G3' : EqTele0 S k1 (cof .one φ') [] ((Tm.ofList us').dinst .zero) (Tm.ofList X') (C.argTys d D.params.length)
    (Q'.isub ρ).toList.reverse
  G4 : ∀ i (hi : i < X.length), EqTm0 S k1 (cof .one φ) [] ((us.getD i .abort).dinst .zero) X[i]
    ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (Q.isub ρ).toList.reverse))
  G4' : ∀ i (hi : i < X'.length), EqTm0 S k1 (cof .one φ') [] ((us'.getD i .abort).dinst .zero) X'[i]
    ((C.argTy d D.params.length i).substList ((X'.take i).reverse ++ (Q'.isub ρ).toList.reverse))
  euu : ∀ i (hi : i < C.args.length), EqTm0 S (k1 + 1) (cof .one φ).shift [] (us.getD i .abort) (us'.getD i .abort)
    ((C.argTy d D.params.length i).substList ((us.take i).reverse ++ (Q.isub ρ).dshift.toList.reverse))
  eLR : EqTm S k1 .one [] (.con d c (Q.isub ρ) (Tm.ofList (gOuts d D C (Q.isub ρ) φ us X)) [])
    (.con d c (Q'.isub ρ) (Tm.ofList (gOuts d D C (Q'.isub ρ) φ' us' X')) []) (.data d (P.isub ρ))
  prj : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
    (ival (idEnv k3) (φ.subst σ.τ)).holds → ∀ (j : ℕ), j < C.args.length →
    RE2 S k3 ((C.argTy d D.params.length j).substList (((us.map (·.isub (ISub.cons r hr σ))).take j).reverse ++
        (Q.isub (ρ.comp σ)).toList.reverse))
      ((us.getD j .abort).isub (ISub.cons r hr σ)) ((us'.getD j .abort).isub (ISub.cons r' hr' σ))
  prjs : ∀ {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
    (ival (idEnv k3) (φ.subst σ.τ)).holds → ∀ (j : ℕ), j < C.args.length →
    RE2 S k3 ((C.argTy d D.params.length j).substList (((us.map (·.isub (ISub.cons r hr σ))).take j).reverse ++
        (Q.isub (ρ.comp σ)).toList.reverse))
      ((us.getD j .abort).isub (ISub.cons r hr σ)) ((us.getD j .abort).isub (ISub.cons r' hr' σ))
  prjb : ∀ {k3 : ℕ} (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds → ∀ (j : ℕ), j < C.args.length →
    RE2 S k3 ((C.argTy d D.params.length j).substList (((us.map (·.isub (ISub.cons .zero trivial σ))).take j).reverse ++
        (Q.isub (ρ.comp σ)).toList.reverse))
      ((us.getD j .abort).isub (ISub.cons .zero trivial σ)) ((X'.getD j .abort).isub σ)
  prjb' : ∀ {k3 : ℕ} (σ : ISub k3 k1), (ival (idEnv k3) (φ.subst σ.τ)).holds → ∀ (j : ℕ), j < C.args.length →
    RE2 S k3 ((C.argTy d D.params.length j).substList (((X.map (·.isub σ)).take j).reverse ++
        (P.isub (ρ.comp σ)).toList.reverse))
      ((X.getD j .abort).isub σ) ((us'.getD j .abort).isub (ISub.cons .zero trivial σ))

namespace HCG

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {X X' : List Tm} {φ φ' : I} {us us' : List Tm}
  (H : HCG S d D K P Q Q' k1 ρ c C X X' φ φ' us us')
include H

/-- Derived facts of `HCG`. -/
structure Basic (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P Q Q' : Tm) (k1 : ℕ) (ρ : ISub k1 K) (C : Ctor)
    (X X' : List Tm) (φ φ' : I) : Prop where
  hqT : HasTy S k1 .one [] (.data d (Q.isub ρ)) (.univ D.level)
  hq'T : HasTy S k1 .one [] (.data d (Q'.isub ρ)) (.univ D.level)
  hφs : φ.Scoped k1
  hφs' : φ'.Scoped k1
  hXq : HasTele0 S k1 .one [] (Tm.ofList X) (C.argTys d D.params.length) (Q.isub ρ).toList.reverse
  hXq' : HasTele0 S k1 .one [] (Tm.ofList X') (C.argTys d D.params.length) (Q'.isub ρ).toList.reverse
  hpT : HasTy S k1 .one [] (.data d (P.isub ρ)) (.univ D.level)
  hPQ : RT2 S k1 (.data d (P.isub ρ)) (.data d (Q.isub ρ))
  hPQ' : RT2 S k1 (.data d (P.isub ρ)) (.data d (Q'.isub ρ))
  hPPρ : RT2 S k1 (.data d (P.isub ρ)) (.data d (P.isub ρ))

theorem basic : Basic S d D K P Q Q' k1 ρ C X X' φ φ' := by
  have hXP := tyCode_of_univ H.hW H.hP
  exact ⟨H.hqT, H.hq'T, H.hφs, H.hφs', H.hXq, H.hXq', HasTy.isubS H.hW H.hP ρ, RT2.isub H.hW hXP H.hQ ρ, RT2.isub H.hW hXP H.hQ' ρ, RT2.isub H.hW hXP H.hPP ρ⟩

/-- The arguments of the two contracta are judgmentally equal. -/
theorem eYY' : ∀ i (hi : i < C.args.length), EqTm0 S k1 .one [] ((gOuts d D C (Q.isub ρ) φ us X).getD i .abort)
    ((gOuts d D C (Q'.isub ρ) φ' us' X').getD i .abort)
    ((C.argTy d D.params.length i).substList (((gOuts d D C (Q.isub ρ) φ us X).take i).reverse ++
      (P.isub ρ).toList.reverse)) := by
  have B := H.basic
  have e := H.eLR
  obtain ⟨hYp, eYp, -, -⟩ := con_retype H.hW H.hD H.hH H.hC (EqTm.refl (HasTy.eqL e)) (TyEq.refl _) B.hpT
  obtain ⟨hY'p, eY'p, -, -⟩ := con_retype H.hW H.hD H.hH H.hC (EqTm.refl (HasTy.eqR e)) (TyEq.refl _) B.hpT
  have Hp := PD.of H.hW H.hD H.hH (spec_to_minimal H.hW B.hpT)
  intro i hi
  exact con_args_eq H.hW H.hD H.hH Hp H.hC hYp hY'p (spec_to_minimal_eq H.hW (eYp.symm.trans (e.trans eY'p))) hi

theorem ePσ {k3 : ℕ} (σ : ISub k3 k1) : (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) := by
  show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]

theorem hPσ {k3 : ℕ} (σ : ISub k3 k1) : RT2 S k3 (.data d (P.isub (ρ.comp σ))) (.data d (P.isub (ρ.comp σ))) :=
  RT2.isub H.hW (tyCode_of_univ H.hW H.hP) H.hPP (ρ.comp σ)

end HCG

end

end Model.Whnf
