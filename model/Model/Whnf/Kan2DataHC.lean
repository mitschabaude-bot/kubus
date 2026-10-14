import Model.Whnf.Kan2DataLine
import Model.Whnf.Kan2DataFillC

/-!
# Composition of related constructors in an inductive type without path constructors

The `hcompCon` contracta of compositions of related constructors along related tubes are related at
one stage (`hcompCon2`): recursive arguments by the composition of the base's arguments (an
induction hypothesis), point arguments by heterogeneous composition along their related type
lines, whose earlier arguments are the related fillers.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hH : D.isHIT = false)
include hW hD hH

/-- A term judgmentally equal to a constructor of an inductive type without path constructors is that
constructor at the parameters of its type, in any context. -/
theorem con_retype0 {Ψ : ℕ} {Φ : I} {t qs p : Tm} {c : ℕ} {C : Ctor} {Z : List Tm} {rs : List I}
    (hC : D.ctors[c]? = some C) (he : EqTm0 S Ψ Φ [] t (.con d c qs (Tm.ofList Z) rs) (.data d p))
    (hpT : HasTy0 S Ψ Φ [] (.data d p) (.univ D.level)) :
    HasTele0 S Ψ Φ [] (Tm.ofList Z) (C.argTys d D.params.length) p.toList.reverse ∧
    EqTm0 S Ψ Φ [] t (.con d c p (Tm.ofList Z) []) (.data d p) ∧ rs = [] := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨hT, hCt⟩ := wf_typed _ S rfl hW
  obtain ⟨-, hcon, -⟩ := pre_eq hS hT hCt he
  obtain ⟨D', C', hD', hC', hpL, -, htele, hrs, m, eq0⟩ := con_args hW hcon hpT
  rw [hD] at hD'; cases hD'; rw [hC] at hC'; cases hC'
  have hrs0 : rs = [] := List.eq_nil_of_length_eq_zero (by rw [hrs, (nonHIT_ctor hH hC).1])
  subst hrs0
  obtain ⟨hq, -, -⟩ := pre_eq hS hT hCt eq0
  obtain ⟨D1, hD1, hqt⟩ := gen_data_tele hq rfl
  rw [hD] at hD1; cases hD1
  obtain ⟨D2, hD2, hpt⟩ := gen_data_tele hpT rfl
  rw [hD] at hD2; cases hD2
  have eps : EqTele0 S Ψ Φ [] p qs D.params [] := EqTele0.dataInj hD hpt hqt (EqTm0.symm eq0)
  have hc0 : HasTy0 S Ψ Φ [] (.con d c p (Tm.ofList Z) []) (.data d p) :=
    HasTy0.con hD hC (tele_isList hpt) hpT hpt htele (by simp [(nonHIT_ctor hH hC).1]) (by simp)
  have ec := EqTm0.con hD hC hc0 hcon eps (EqTele0.refl htele) rfl (fun _ _ _ h => by simp at h)
  exact ⟨htele, he.trans (EqTm0.symm ec), rfl⟩

end

theorem getD_take_lt {L : List Tm} {i j : ℕ} (h : i < j) : (L.take j).getD i .abort = L.getD i .abort := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem getD_map_isub (L : List Tm) (i : ℕ) (κ : ISub k' k) :
    (L.map (·.isub κ)).getD i .abort = (L.getD i .abort).isub κ := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases L[i]? with _ | a <;> rfl

/-! ### The data of a composition of related constructors -/

/-- The projections of a composition's tube, at the parameters `q`. -/
def tubeArgs (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (q u : Tm) : List Tm :=
  (List.range C.args.length).map fun j => proj d D q.dshift c C j u

/-- The arguments of the `hcompCon` contractum. -/
def conOuts (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (q : Tm) (φ : I) (u : Tm) (X : List Tm) : List Tm :=
  (List.range C.args.length).map
    (Meta.hOut C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ (tubeArgs d D c C q u) X)

/-- The fillers of the arguments of the `hcompCon` contractum. -/
def conFills (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (q : Tm) (φ : I) (u : Tm) (X : List Tm) : List Tm :=
  Meta.hFills C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ (tubeArgs d D c C q u) X C.args.length

/-- The type lines of the arguments of the `hcompCon` contractum. -/
def conLine (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (q : Tm) (φ : I) (u : Tm) (X : List Tm) : ℕ → Tm :=
  Meta.hLine C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ (tubeArgs d D c C q u) X

/-- The hypotheses of `hcompCon2`: compositions of related constructors along related tubes, in
restrictions of literal inductive types with parameters `Q`, `Q'` related to `P`. -/
structure HCC (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P Q Q' : Tm) (k1 : ℕ) (ρ : ISub k1 K) (c : ℕ) (C : Ctor)
    (qs qs' : Tm) (X X' : List Tm) (φ φ' : I) (u u' : Tm) : Prop where
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
  hrecR : ∀ i (hi : i < C.args.length), C.isRec i = true →
    RE2 S k1 (.data d (P.isub ρ)) (X.getD i .abort) (X'.getD i .abort)
  hptR : ∀ i (hi : i < C.args.length), C.isRec i = false →
    RE2 S k1 ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (P.isub ρ).toList.reverse))
      (X.getD i .abort) (X'.getD i .abort)
  hrecH : ∀ i (hi : i < C.args.length), C.isRec i = true → ∀ (Q1 Q1' : Tm),
    RT2 S K (.data d P) (.data d Q1) → RT2 S K (.data d P) (.data d Q1') → ∀ K2 (σ : ISub K2 k1),
    HC2 S K2 (.data d (P.isub (ρ.comp σ))) (.data d (Q1.isub (ρ.comp σ))) (.data d (Q1'.isub (ρ.comp σ)))
      ((X.getD i .abort).isub σ) ((X'.getD i .abort).isub σ)
  hn : ¬ I.Entails .one φ
  hty : HasTy S k1 .one [] (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) [])) (.data d (P.isub ρ))
  hty' : HasTy S k1 .one [] (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') [])) (.data d (P.isub ρ))
  heq : EqTm S k1 .one [] (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
    (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') [])) (.data d (P.isub ρ))
  hteq : EqTm S (k1 + 1) (cof .one φ).shift [] u u' (Tm.data d (P.isub ρ)).dshift
  h12 : I.Entails φ φ'
  h21 : I.Entails φ' φ
  htube : Tube2 S k1 (.data d (P.isub ρ)) φ u u'
  hbd : ∀ k' (σ : ISub k' k1), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' ((Tm.data d (P.isub ρ)).isub σ) ((u.isub σ.up).dinst .zero) ((Tm.con d c qs' (Tm.ofList X') []).isub σ)
  hbd' : ∀ k' (σ : ISub k' k1), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' ((Tm.data d (P.isub ρ)).isub σ) ((Tm.con d c qs (Tm.ofList X) []).isub σ) ((u'.isub σ.up).dinst .zero)

namespace HCC

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {qs qs' : Tm} {X X' : List Tm} {φ φ' : I} {u u' : Tm}
  (H : HCC S d D K P Q Q' k1 ρ c C qs qs' X X' φ φ' u u')
include H

/-- Derived facts of `HCC`. -/
structure Basic (S : Sig) (d : ℕ) (D : DataDecl) (K : ℕ) (P Q Q' : Tm) (k1 : ℕ) (ρ : ISub k1 K) (c : ℕ) (C : Ctor)
    (X X' : List Tm) (φ φ' : I) (u u' : Tm) : Prop where
  hqT : HasTy S k1 .one [] (.data d (Q.isub ρ)) (.univ D.level)
  hq'T : HasTy S k1 .one [] (.data d (Q'.isub ρ)) (.univ D.level)
  hpT : HasTy S k1 .one [] (.data d (P.isub ρ)) (.univ D.level)
  hφs : φ.Scoped k1
  hφs' : φ'.Scoped k1
  hut : HasTy0 S (k1 + 1) (cof .one φ).shift [] u (Tm.data d (Q.isub ρ)).dshift
  hut' : HasTy0 S (k1 + 1) (cof .one φ').shift [] u' (Tm.data d (Q'.isub ρ)).dshift
  hXq : HasTele0 S k1 .one [] (Tm.ofList X) (C.argTys d D.params.length) (Q.isub ρ).toList.reverse
  hXq' : HasTele0 S k1 .one [] (Tm.ofList X') (C.argTys d D.params.length) (Q'.isub ρ).toList.reverse
  hside : EqTm S k1 (cof .one φ) [] (u.dinst .zero) (.con d c (Q.isub ρ) (Tm.ofList X) []) (.data d (Q.isub ρ))
  hside' : EqTm S k1 (cof .one φ') [] (u'.dinst .zero) (.con d c (Q'.isub ρ) (Tm.ofList X') []) (.data d (Q'.isub ρ))
  hcan : TubeCanon S k1 d D (Q.isub ρ) φ u
  hcan' : TubeCanon S k1 d D (Q'.isub ρ) φ' u'
  hPQ : RT2 S k1 (.data d (P.isub ρ)) (.data d (Q.isub ρ))
  hPQ' : RT2 S k1 (.data d (P.isub ρ)) (.data d (Q'.isub ρ))
  hPPρ : RT2 S k1 (.data d (P.isub ρ)) (.data d (P.isub ρ))
  hn' : ¬ I.Entails .one φ'
  htubeL : Tube2 S k1 (.data d (P.isub ρ)) φ u u
  htubeR : Tube2 S k1 (.data d (P.isub ρ)) φ' u' u'

theorem basic : Basic S d D K P Q Q' k1 ρ c C X X' φ φ' u u' := by
  obtain ⟨hW, hD, hH, hP, hPP, hQ, hQ', -, hC, hXl, hXl', -, -, -, hn, hty, hty', -, -, -, h21, htube, -, -⟩ := H
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l0, ⟨hdq, hφs, hut, hb, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  obtain ⟨l0', ⟨hdq', hφs', hut', hb', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty') rfl
  obtain ⟨D1, hD1, hqt⟩ := gen_data_tele hdq rfl
  rw [hD] at hD1; cases hD1
  obtain ⟨D2, hD2, hqt'⟩ := gen_data_tele hdq' rfl
  rw [hD] at hD2; cases hD2
  have hqT : HasTy S k1 .one [] (.data d (Q.isub ρ)) (.univ D.level) :=
    minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hqt)
  have hq'T : HasTy S k1 .one [] (.data d (Q'.isub ρ)) (.univ D.level) :=
    minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hqt')
  have hpT : HasTy S k1 .one [] (.data d (P.isub ρ)) (.univ D.level) := HasTy.isubS hW hP ρ
  have hXP := tyCode_of_univ hW hP
  have hPQρ : RT2 S k1 (.data d (P.isub ρ)) (.data d (Q.isub ρ)) := RT2.isub hW hXP hQ ρ
  have hPQ'ρ : RT2 S k1 (.data d (P.isub ρ)) (.data d (Q'.isub ρ)) := RT2.isub hW hXP hQ' ρ
  have hPPρ : RT2 S k1 (.data d (P.isub ρ)) (.data d (P.isub ρ)) := RT2.isub hW hXP hPP ρ
  have hTPQ : TyEq S k1 (.data d (P.isub ρ)) (.data d (Q.isub ρ)) := (Comp2_ty_base hPQρ).2.2.2.2.2
  have hTPQ' : TyEq S k1 (.data d (P.isub ρ)) (.data d (Q'.isub ρ)) := (Comp2_ty_base hPQ'ρ).2.2.2.2.2
  have hXp : TyCode k1 (semK S k1 (.data d (P.isub ρ))) := tyCode_of_univ hW hpT
  have hpσ : ∀ {k3 : ℕ} (σ : ISub k3 k1), RT2 S k3 ((Tm.data d (P.isub ρ)).isub σ) ((Tm.data d (P.isub ρ)).isub σ) :=
    fun σ => RT2.isub hW hXp hPPρ σ
  have hn' : ¬ I.Entails .one φ' := fun h => hn (ent_trans h h21)
  have hholds : ∀ {k3 : ℕ} (σ : ISub k3 k1), (ival (idEnv k3) (φ'.subst σ.τ)).holds →
      (ival (idEnv k3) (φ.subst σ.τ)).holds := fun σ h => by
    rw [holds_iff_entails (I.scoped_subst hφs σ.sc)]
    exact ent_trans ((holds_iff_entails (I.scoped_subst hφs' σ.sc)).1 h) (ent_subst h21 σ.τ)
  have htubeL : Tube2 S k1 (.data d (P.isub ρ)) φ u u := fun k3 σ r r' hr hr' hE hh =>
    RE2.trans hW (hpσ σ) (htube k3 σ r r' hr hr' hE hh)
      (RE2.symm hW (hpσ σ) (htube k3 σ r' r' hr' hr' (I_eq_refl _) hh))
  have htubeR : Tube2 S k1 (.data d (P.isub ρ)) φ' u' u' := fun k3 σ r r' hr hr' hE hh =>
    RE2.trans hW (hpσ σ) (RE2.symm hW (hpσ σ) (htube k3 σ r r hr hr (I_eq_refl _) (hholds σ hh)))
      (htube k3 σ r r' hr hr' hE (hholds σ hh))
  obtain ⟨hXq, ebase, -, -⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb)) (TyEq.refl _) hqT
  obtain ⟨hXq', ebase', -, -⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb')) (TyEq.refl _) hq'T
  exact ⟨hqT, hq'T, hpT, hφs, hφs', hut, hut', hXq, hXq',
    (minimal_to_spec_eq hside).trans (EqTm.restrict (show (cof .one φ).Scoped k1 from ⟨trivial, hφs⟩)
      (ent_and_left _ _) ebase),
    (minimal_to_spec_eq hside').trans (EqTm.restrict (show (cof .one φ').Scoped k1 from ⟨trivial, hφs'⟩)
      (ent_and_left _ _) ebase'),
    tubeCanon_of hW hD hH hP ρ hTPQ hqT htubeL, tubeCanon_of hW hD hH hP ρ hTPQ' hq'T htubeR,
    hPQρ, hPQ'ρ, hPPρ, hn', htubeL, htubeR⟩

theorem hn'' : ¬ I.Entails .one φ' := H.basic.hn'

/-- The `hcompCon` steps and their soundness. -/
theorem contracta :
    (EqTm S k1 .one [] (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
      (.con d c (Q.isub ρ) (Tm.ofList (conOuts d D c C (Q.isub ρ) φ u X)) []) (.data d (P.isub ρ)) ∧
      Red S (.hcomp (.data d (Q.isub ρ)) φ u (.con d c qs (Tm.ofList X) []))
        (.con d c (Q.isub ρ) (Tm.ofList (conOuts d D c C (Q.isub ρ) φ u X)) [])) ∧
    (EqTm S k1 .one [] (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') []))
      (.con d c (Q'.isub ρ) (Tm.ofList (conOuts d D c C (Q'.isub ρ) φ' u' X')) []) (.data d (P.isub ρ)) ∧
      Red S (.hcomp (.data d (Q'.isub ρ)) φ' u' (.con d c qs' (Tm.ofList X') []))
        (.con d c (Q'.isub ρ) (Tm.ofList (conOuts d D c C (Q'.isub ρ) φ' u' X')) [])) := by
  have B := H.basic
  obtain ⟨hW, hD, hH, -, -, -, -, -, hC, hXl, hXl', -, -, -, hn, hty, hty', -, -, -, -, -, -, -⟩ := H
  have e_hc := hcompCon_sound hW hD hH hC hty B.hcan
  have e_hc' := hcompCon_sound hW hD hH hC hty' B.hcan'
  have hul : (tubeArgs d D c C (Q.isub ρ) u).length = C.args.length := by simp [tubeArgs]
  have hul' : (tubeArgs d D c C (Q'.isub ρ) u').length = C.args.length := by simp [tubeArgs]
  have heqT := Meta.hcompTele_eq C (C.argTy d D.params.length) (.data d (Q.isub ρ)) (Q.isub ρ).dshift.toList φ
    (tubeArgs d D c C (Q.isub ρ) u) X (tubeArgs d D c C (Q.isub ρ) u) X 0 rfl rfl (by rw [hul, hXl])
  simp only [hXl, ← List.range_eq_range'] at heqT
  have heqT' := Meta.hcompTele_eq C (C.argTy d D.params.length) (.data d (Q'.isub ρ)) (Q'.isub ρ).dshift.toList φ'
    (tubeArgs d D c C (Q'.isub ρ) u') X' (tubeArgs d D c C (Q'.isub ρ) u') X' 0 rfl rfl (by rw [hul', hXl'])
  simp only [hXl', ← List.range_eq_range'] at heqT'
  have e0 : Tm.hcompTele C (C.argTy d D.params.length) (.data d (Q.isub ρ)) (Q.isub ρ).dshift.toList φ 0 []
      ((List.range C.args.length).map fun j => proj d D (Q.isub ρ).dshift c C j u) X =
      conOuts d D c C (Q.isub ρ) φ u X := by
    rw [show ([] : List Tm) = (Meta.hFills C (C.argTy d D.params.length) (.data d (Q.isub ρ)) (Q.isub ρ).dshift.toList
      φ (tubeArgs d D c C (Q.isub ρ) u) X 0).reverse from rfl]
    exact heqT
  have e0' : Tm.hcompTele C (C.argTy d D.params.length) (.data d (Q'.isub ρ)) (Q'.isub ρ).dshift.toList φ' 0 []
      ((List.range C.args.length).map fun j => proj d D (Q'.isub ρ).dshift c C j u') X' =
      conOuts d D c C (Q'.isub ρ) φ' u' X' := by
    rw [show ([] : List Tm) = (Meta.hFills C (C.argTy d D.params.length) (.data d (Q'.isub ρ)) (Q'.isub ρ).dshift.toList
      φ' (tubeArgs d D c C (Q'.isub ρ) u') X' 0).reverse from rfl]
    exact heqT'
  rw [e0] at e_hc
  rw [e0'] at e_hc'
  refine ⟨⟨e_hc, .step (step_hcompCon hD hH hC hn X) ?_⟩, ⟨e_hc', .step (step_hcompCon hD hH hC B.hn' X') ?_⟩⟩
  · rw [e0]; exact .refl _
  · rw [e0']; exact .refl _

/-- The contracta are judgmentally equal. -/
theorem eLR : EqTm S k1 .one [] (.con d c (Q.isub ρ) (Tm.ofList (conOuts d D c C (Q.isub ρ) φ u X)) [])
    (.con d c (Q'.isub ρ) (Tm.ofList (conOuts d D c C (Q'.isub ρ) φ' u' X')) []) (.data d (P.isub ρ)) :=
  H.contracta.1.1.symm.trans (H.heq.trans H.contracta.2.1)

/-- The premises of `hcompCon`, on both sides. -/
theorem prem :
    (HasTele0 S (k1 + 1) (cof .one φ).shift [] (Tm.ofList (tubeArgs d D c C (Q.isub ρ) u))
      (C.argTys d D.params.length) (Q.isub ρ).dshift.toList.reverse ∧
    EqTm0 S (k1 + 1) (cof .one φ).shift [] u
      (.con d c (Q.isub ρ).dshift (Tm.ofList (tubeArgs d D c C (Q.isub ρ) u)) []) (.data d (Q.isub ρ).dshift) ∧
    EqTele0 S k1 (cof .one φ) [] ((Tm.ofList (tubeArgs d D c C (Q.isub ρ) u)).dinst .zero)
      (Tm.ofList X) (C.argTys d D.params.length) (Q.isub ρ).toList.reverse ∧
    ∀ i (hi : i < X.length), EqTm0 S k1 (cof .one φ) [] ((proj d D (Q.isub ρ).dshift c C i u).dinst .zero) X[i]
      ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (Q.isub ρ).toList.reverse))) ∧
    (HasTele0 S (k1 + 1) (cof .one φ').shift [] (Tm.ofList (tubeArgs d D c C (Q'.isub ρ) u'))
      (C.argTys d D.params.length) (Q'.isub ρ).dshift.toList.reverse ∧
    EqTm0 S (k1 + 1) (cof .one φ').shift [] u'
      (.con d c (Q'.isub ρ).dshift (Tm.ofList (tubeArgs d D c C (Q'.isub ρ) u')) []) (.data d (Q'.isub ρ).dshift) ∧
    EqTele0 S k1 (cof .one φ') [] ((Tm.ofList (tubeArgs d D c C (Q'.isub ρ) u')).dinst .zero)
      (Tm.ofList X') (C.argTys d D.params.length) (Q'.isub ρ).toList.reverse ∧
    ∀ i (hi : i < X'.length), EqTm0 S k1 (cof .one φ') [] ((proj d D (Q'.isub ρ).dshift c C i u').dinst .zero) X'[i]
      ((C.argTy d D.params.length i).substList ((X'.take i).reverse ++ (Q'.isub ρ).toList.reverse))) := by
  have B := H.basic
  exact ⟨hcompCon_premises H.hW H.hD H.hH H.hC B.hqT B.hφs B.hut B.hside B.hXq B.hcan,
    hcompCon_premises H.hW H.hD H.hH H.hC B.hq'T B.hφs' B.hut' B.hside' B.hXq' B.hcan'⟩

/-- The projections of the two tubes are judgmentally equal under the face. -/
theorem euu : ∀ i (hi : i < C.args.length), EqTm0 S (k1 + 1) (cof .one φ).shift []
    ((tubeArgs d D c C (Q.isub ρ) u).getD i .abort) ((tubeArgs d D c C (Q'.isub ρ) u').getD i .abort)
    ((C.argTy d D.params.length i).substList (((tubeArgs d D c C (Q.isub ρ) u).take i).reverse ++
      (Q.isub ρ).dshift.toList.reverse)) := by
  have B := H.basic
  obtain ⟨⟨G1, G2, -, -⟩, ⟨-, G2', -, -⟩⟩ := H.prem
  obtain ⟨hW, hD, hH, -, -, -, -, -, hC, -, -, -, -, -, -, -, -, -, hteq, h12, -, -, -, -⟩ := H
  have hS := sigClosed_of_wfSig hW
  have hΦs : ((cof .one φ).shift).Scoped (k1 + 1) := KubusCore.I.scoped_shift ⟨trivial, B.hφs⟩
  have hΦe : I.Entails (cof .one φ).shift (cof .one φ').shift := ent_shift (ent_and_mono (ent_refl _) h12)
  have hdq1 : HasTy0 S (k1 + 1) (cof .one φ).shift [] (.data d (Q.isub ρ).dshift) (.univ D.level) :=
    HasTy0.restrict hΦs (ent_one _) (HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal hW B.hqT))
  have H1 := PD.of hW hD hH hdq1
  have dwkΦ : ∀ {A B : Tm} {l : ℕ}, EqTm S k1 .one [] A B (.univ l) →
      EqTm0 S (k1 + 1) (cof .one φ).shift [] A.dshift B.dshift (.univ l) := fun e =>
    EqTm0.restrict hΦs (ent_one _) (EqTm0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal_eq hW e))
  have hTPQ := (Comp2_ty_base B.hPQ).2.2.2.2.2
  have hTPQ' := (Comp2_ty_base B.hPQ').2.2.2.2.2
  obtain ⟨lq'q, eq'q⟩ := tyEq_eq hW (hTPQ'.symm.trans hW hTPQ) ⟨_, B.hqT⟩
  obtain ⟨lpq, epq⟩ := tyEq_eq hW hTPQ ⟨_, B.hqT⟩
  have hteq0 : EqTm0 S (k1 + 1) (cof .one φ).shift [] u u' (.data d (Q.isub ρ).dshift) :=
    EqTm0.conv (spec_to_minimal_eq hW hteq) (dwkΦ epq)
  have G2'' : EqTm0 S (k1 + 1) (cof .one φ).shift [] u'
      (.con d c (Q'.isub ρ).dshift (Tm.ofList (tubeArgs d D c C (Q'.isub ρ) u')) []) (.data d (Q.isub ρ).dshift) :=
    EqTm0.conv (EqTm0.restrict hΦs hΦe G2') (dwkΦ eq'q)
  obtain ⟨hus't, eus', -⟩ := con_retype0 hW hD hH hC G2'' hdq1
  intro i hi
  exact con_args_eq hW hD hH H1 hC G1 hus't ((EqTm0.symm G2).trans (hteq0.trans eus')) hi

/-- The arguments of the two contracta are judgmentally equal. -/
theorem eYY' : ∀ i (hi : i < C.args.length), EqTm0 S k1 .one [] ((conOuts d D c C (Q.isub ρ) φ u X).getD i .abort)
    ((conOuts d D c C (Q'.isub ρ) φ' u' X').getD i .abort)
    ((C.argTy d D.params.length i).substList (((conOuts d D c C (Q.isub ρ) φ u X).take i).reverse ++
      (P.isub ρ).toList.reverse)) := by
  have B := H.basic
  have e := H.eLR
  obtain ⟨hW, hD, hH, -, -, -, -, -, hC, -⟩ := H
  obtain ⟨hYp, eYp, -, -⟩ := con_retype hW hD hH hC (EqTm.refl (HasTy.eqL e)) (TyEq.refl _) B.hpT
  obtain ⟨hY'p, eY'p, -, -⟩ := con_retype hW hD hH hC (EqTm.refl (HasTy.eqR e)) (TyEq.refl _) B.hpT
  have Hp := PD.of hW hD hH (spec_to_minimal hW B.hpT)
  intro i hi
  exact con_args_eq hW hD hH Hp hC hYp hY'p (spec_to_minimal_eq hW (eYp.symm.trans (e.trans eY'p))) hi

theorem tubeArgs_getD {q v : Tm} {i : ℕ} (hi : i < C.args.length) :
    (tubeArgs d D c C q v).getD i .abort = proj d D q.dshift c C i v := by
  simp [tubeArgs, List.getD_eq_getElem?_getD, hi]

/-- The projections of the left tube at a point. -/
theorem usσ {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) {j : ℕ} (hj : j < C.args.length) :
    ((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub (ISub.cons r hr σ) =
      proj d D (Q.isub (ρ.comp σ)) c C j ((u.isub σ.up).dinst r) := by
  have B := H.basic
  have hS := sigClosed_of_wfSig H.hW
  have hdq1 : HasTy0 S (k1 + 1) .one [] (.data d (Q.isub ρ).dshift) (.univ D.level) :=
    HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal H.hW B.hqT)
  have H1 := PD.of H.hW H.hD H.hH hdq1
  rw [H.tubeArgs_getD hj, proj_tube_isub H.hW H.hD H.hC hj H1.hpsL H1.hpl σ hr, Tm.isub_isub]

/-- The projections of the right tube at a point. -/
theorem usσ' {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) {j : ℕ} (hj : j < C.args.length) :
    ((tubeArgs d D c C (Q'.isub ρ) u').getD j .abort).isub (ISub.cons r hr σ) =
      proj d D (Q'.isub (ρ.comp σ)) c C j ((u'.isub σ.up).dinst r) := by
  have B := H.basic
  have hS := sigClosed_of_wfSig H.hW
  have hdq1 : HasTy0 S (k1 + 1) .one [] (.data d (Q'.isub ρ).dshift) (.univ D.level) :=
    HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal H.hW B.hq'T)
  have H1 := PD.of H.hW H.hD H.hH hdq1
  rw [H.tubeArgs_getD hj, proj_tube_isub H.hW H.hD H.hC hj H1.hpsL H1.hpl σ hr, Tm.isub_isub]

theorem usmap {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) :
    (tubeArgs d D c C (Q.isub ρ) u).map (·.isub (ISub.cons r hr σ)) =
      (List.range C.args.length).map fun j => proj d D (Q.isub (ρ.comp σ)) c C j ((u.isub σ.up).dinst r) := by
  apply List.ext_getElem (by simp [tubeArgs])
  intro j h1 h2
  have hj : j < C.args.length := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  rw [← H.usσ σ r hr hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa [tubeArgs] using h1)]
  rfl

theorem usmap' {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) :
    (tubeArgs d D c C (Q'.isub ρ) u').map (·.isub (ISub.cons r hr σ)) =
      (List.range C.args.length).map fun j => proj d D (Q'.isub (ρ.comp σ)) c C j ((u'.isub σ.up).dinst r) := by
  apply List.ext_getElem (by simp [tubeArgs])
  intro j h1 h2
  have hj : j < C.args.length := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  rw [← H.usσ' σ r hr hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa [tubeArgs] using h1)]
  rfl

theorem ePσ {k3 : ℕ} (σ : ISub k3 k1) : (Tm.data d (P.isub ρ)).isub σ = .data d (P.isub (ρ.comp σ)) := by
  show Tm.data d ((P.isub ρ).isub σ) = _; rw [Tm.isub_isub]

/-- The normal forms of the left tube at points of its face are the constructor `c`. -/
theorem tagL {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds)
    {c0 : ℕ} {C0 : Ctor} {qs0 : Tm} {Z : List Tm} (hC0 : D.ctors[c0]? = some C0)
    (ht : RedE S k3 (.data d (P.isub (ρ.comp σ))) ((u.isub σ.up).dinst r) (.con d c0 qs0 (Tm.ofList Z) [])) :
    c0 = c := by
  have B := H.basic
  have hTσ : TyEq S k3 (.data d (P.isub (ρ.comp σ))) (.data d ((Q.isub ρ).isub σ)) := by
    have := ((Comp2_ty_base B.hPQ).2.2.2.2.2).isub H.hW σ; rwa [H.ePσ] at this
  obtain ⟨-, e, -, -⟩ := con_retype H.hW H.hD H.hH hC0 ht.2 hTσ (HasTy.isubS H.hW B.hqT σ)
  exact tube_tag H.hW H.hD H.hH H.hC B.hqT B.hφs (closed_ty B.hut) B.hside B.hcan σ hr hh hC0 e

/-- The normal forms of the right tube at points of its face are the constructor `c`. -/
theorem tagR {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) (hh : (ival (idEnv k3) (φ'.subst σ.τ)).holds)
    {c0 : ℕ} {C0 : Ctor} {qs0 : Tm} {Z : List Tm} (hC0 : D.ctors[c0]? = some C0)
    (ht : RedE S k3 (.data d (P.isub (ρ.comp σ))) ((u'.isub σ.up).dinst r) (.con d c0 qs0 (Tm.ofList Z) [])) :
    c0 = c := by
  have B := H.basic
  have hTσ : TyEq S k3 (.data d (P.isub (ρ.comp σ))) (.data d ((Q'.isub ρ).isub σ)) := by
    have := ((Comp2_ty_base B.hPQ').2.2.2.2.2).isub H.hW σ; rwa [H.ePσ] at this
  obtain ⟨-, e, -, -⟩ := con_retype H.hW H.hD H.hH hC0 ht.2 hTσ (HasTy.isubS H.hW B.hq'T σ)
  exact tube_tag H.hW H.hD H.hH H.hC B.hq'T B.hφs' (closed_ty B.hut') B.hside' B.hcan' σ hr hh hC0 e

theorem hPσ {k3 : ℕ} (σ : ISub k3 k1) : RT2 S k3 (.data d (P.isub (ρ.comp σ))) (.data d (P.isub (ρ.comp σ))) :=
  RT2.isub H.hW (tyCode_of_univ H.hW H.hP) H.hPP (ρ.comp σ)

/-- The projections of the two tubes at points of their face. -/
theorem prj {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3) (hE : I.Eq r r')
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) (j : ℕ) (hj : j < C.args.length) :
    RE2 S k3 ((C.argTy d D.params.length j).substList ((((tubeArgs d D c C (Q.isub ρ) u).map
        (·.isub (ISub.cons r hr σ))).take j).reverse ++ (Q.isub (ρ.comp σ)).toList.reverse))
      (((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub (ISub.cons r hr σ))
      (((tubeArgs d D c C (Q'.isub ρ) u').getD j .abort).isub (ISub.cons r' hr' σ)) := by
  have hx := H.htube k3 σ r r' hr hr' hE hh
  rw [H.ePσ] at hx
  obtain ⟨c0, C0, qs0, Z, -, -, hC0, -, -, ht, -, -, -⟩ := dataLit_args H.hW H.hD H.hH H.hP H.hPP (ρ.comp σ) hx
  have hcc := H.tagL σ r hr hh hC0 ht
  rw [hcc] at hC0 ht
  rw [H.hC] at hC0; cases hC0
  have := (projs_rel H.hW H.hD H.hH H.hP H.hPP H.hQ H.hQ' (ρ.comp σ) hx H.hC ht.1 hj).1
  rw [H.usmap σ r hr, H.usσ σ r hr hj, H.usσ' σ r' hr' hj]
  exact this

/-- The projections of the left tube against themselves at points of their face. -/
theorem prjs {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3) (hE : I.Eq r r')
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) (j : ℕ) (hj : j < C.args.length) :
    RE2 S k3 ((C.argTy d D.params.length j).substList ((((tubeArgs d D c C (Q.isub ρ) u).map
        (·.isub (ISub.cons r hr σ))).take j).reverse ++ (Q.isub (ρ.comp σ)).toList.reverse))
      (((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub (ISub.cons r hr σ))
      (((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub (ISub.cons r' hr' σ)) := by
  have hx := H.basic.htubeL k3 σ r r' hr hr' hE hh
  rw [H.ePσ] at hx
  obtain ⟨c0, C0, qs0, Z, -, -, hC0, -, -, ht, -, -, -⟩ := dataLit_args H.hW H.hD H.hH H.hP H.hPP (ρ.comp σ) hx
  have hcc := H.tagL σ r hr hh hC0 ht
  rw [hcc] at hC0 ht
  rw [H.hC] at hC0; cases hC0
  have := (projs_rel H.hW H.hD H.hH H.hP H.hPP H.hQ H.hQ (ρ.comp σ) hx H.hC ht.1 hj).1
  rw [H.usmap σ r hr, H.usσ σ r hr hj, H.usσ σ r' hr' hj]
  exact this

theorem conIsub (q0 : Tm) (Z : List Tm) {k3 : ℕ} (σ : ISub k3 k1) :
    (Tm.con d c q0 (Tm.ofList Z) []).isub σ = .con d c (q0.isub σ) (Tm.ofList (Z.map (·.isub σ))) [] := by
  show Tm.con d c (q0.isub σ) ((Tm.ofList Z).isub σ) [] = _; rw [ofList_isub]

/-- The projections of the left tube against the right base. -/
theorem prjb {k3 : ℕ} (σ : ISub k3 k1) (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) (j : ℕ) (hj : j < C.args.length) :
    RE2 S k3 ((C.argTy d D.params.length j).substList ((((tubeArgs d D c C (Q.isub ρ) u).map
        (·.isub (ISub.cons .zero trivial σ))).take j).reverse ++ (Q.isub (ρ.comp σ)).toList.reverse))
      (((tubeArgs d D c C (Q.isub ρ) u).getD j .abort).isub (ISub.cons .zero trivial σ)) ((X'.getD j .abort).isub σ) := by
  have hx := H.hbd k3 σ hh
  rw [H.ePσ, H.conIsub] at hx
  have hxx := RE2.trans H.hW (H.hPσ σ) hx (RE2.symm H.hW (H.hPσ σ) hx)
  obtain ⟨c0, C0, qs0, Z, qs1, Z1, hC0, hZl, hZ1l, ht, ht1, hZZ⟩ :=
    dataLit_argsU H.hW H.hD H.hH H.hP H.hPP (ρ.comp σ) hx
  have e1 := RedW.unique ht1.1 (redW_self (step_con_nonHIT H.hD H.hH H.hC _ _ _))
  simp only [Tm.con.injEq] at e1
  obtain ⟨-, hc0, -, ea, -⟩ := e1
  have ea' := congrArg Tm.toList ea
  simp only [toList_ofList] at ea'
  subst ea'
  rw [hc0] at hC0 ht
  rw [H.hC] at hC0; cases hC0
  obtain ⟨-, p2, p3⟩ := projs_rel H.hW H.hD H.hH H.hP H.hPP H.hQ H.hQ (ρ.comp σ) hxx H.hC ht.1 hj
  have z := RE2.conv H.hW p3 (hZZ j hj)
  rw [H.usmap σ .zero trivial, H.usσ σ .zero trivial hj]
  rw [getD_map_isub] at z
  exact RE2.trans H.hW (RT2.refl' H.hW (RE2.tyCode H.hW (hZZ j hj)) p3) p2 z

/-- The left base against the projections of the right tube. -/
theorem prjb' {k3 : ℕ} (σ : ISub k3 k1) (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) (j : ℕ) (hj : j < C.args.length) :
    RE2 S k3 ((C.argTy d D.params.length j).substList (((X.map (·.isub σ)).take j).reverse ++
        (P.isub (ρ.comp σ)).toList.reverse))
      ((X.getD j .abort).isub σ) (((tubeArgs d D c C (Q'.isub ρ) u').getD j .abort).isub (ISub.cons .zero trivial σ)) := by
  have hx := H.hbd' k3 σ hh
  rw [H.ePσ, H.conIsub] at hx
  have hxx := RE2.trans H.hW (H.hPσ σ) (RE2.symm H.hW (H.hPσ σ) hx) hx
  obtain ⟨c0, C0, qs0, Z, qs1, Z1, hC0, hZl, hZ1l, ht, ht1, hZZ⟩ :=
    dataLit_argsU H.hW H.hD H.hH H.hP H.hPP (ρ.comp σ) hx
  have e1 := RedW.unique ht.1 (redW_self (step_con_nonHIT H.hD H.hH H.hC _ _ _))
  simp only [Tm.con.injEq] at e1
  obtain ⟨-, hc0, -, ea, -⟩ := e1
  have ea' := congrArg Tm.toList ea
  simp only [toList_ofList] at ea'
  subst ea'
  rw [hc0] at hC0 ht1
  rw [H.hC] at hC0; cases hC0
  obtain ⟨-, p2, p3⟩ := projs_rel H.hW H.hD H.hH H.hP H.hPP H.hQ' H.hQ' (ρ.comp σ) hxx H.hC ht1.1 hj
  have hPl := (dataLit_rel H.hW H.hD H.hP H.hPP (ρ.comp σ)).2.2.2.2.2.1
  have hplen : (P.isub (ρ.comp σ)).toList.length = D.params.length := by
    have := data_len_of H.hW (⟨_, .inl (HasTy.isubS H.hW H.hP (ρ.comp σ))⟩ : IsTyK S k3 (.data d (P.isub (ρ.comp σ))))
    rwa [dataD_eq H.hW H.hD] at this
  have TX := argTy_rt2 H.hW H.hD H.hP H.hPP H.hPP H.hPP (ρ.comp σ) H.hC hj (A := (X.map (·.isub σ)).take j)
    (B := Z1.take j) (by simp [H.hXl]; omega) (by simp [hZ1l]; omega) (fun i hi => by
      have h := hZZ i (by omega)
      rw [getD_take_lt hi, getD_take_lt hi, List.take_take, Nat.min_eq_left hi.le]
      cases hri : C.isRec i
      · exact ⟨fun h' => (by cases h'), fun _ => h⟩
      · refine ⟨fun _ => ?_, fun h' => (by cases h')⟩
        rwa [argTy_rec_inst hri hPl hplen (by simp [H.hXl]; omega)] at h)
  have hXT := RE2.tyCode H.hW (hZZ j hj)
  have hXZ := RT2.tyCode_r H.hW TX hXT
  have q1 := RE2.conv H.hW (RT2.symm H.hW hXT TX) (RE2.conv H.hW (RT2.symm H.hW hXZ p3)
    (RE2.symm H.hW (RT2.refl' H.hW hXZ p3) p2))
  rw [H.usσ' σ .zero trivial hj]
  have a1 := hZZ j hj
  rw [getD_map_isub] at a1
  exact RE2.trans H.hW (RT2.refl H.hW hXT TX) a1 q1

end HCC

end

end Model.Whnf
