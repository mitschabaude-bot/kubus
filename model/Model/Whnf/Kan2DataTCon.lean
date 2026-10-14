import Model.Whnf.Kan2DataTArgs

/-!
# Transport of constructors along related lines of inductive types: the data

`TC` collects the data of a transport of related constructors along related literal lines `data d PL`,
`data d QL` (at stage `k + 1`) of an inductive type without path constructors: robustness of the lines,
the Kan properties of the argument types' codes, typings, the related arguments, and the transports of
the recursive arguments (the induction hypothesis). The argument lines (`Meta.tLine`), the transport
fillers and the transported arguments are typed (`TC.basic`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The data of a transport of related constructors along related literal lines of an inductive type. -/
structure TC (S : Sig) (k d : ℕ) (D : DataDecl) (PL QL : Tm) (φ φ' : I) (c : ℕ) (C : Ctor) (q q' : Tm)
    (X X' : List Tm) : Prop where
  hW : WfSig S
  hD : S[d]? = some (.data D)
  hH : D.isHIT = false
  hp : D.params ≠ []
  hC : D.ctors[c]? = some C
  hPL : HasTy S (k + 1) .one [] (.data d PL) (.univ D.level)
  hR : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
    RT2 S k3 (.data d (PL.isub (ISub.cons y hy τ))) (.data d (QL.isub (ISub.cons y' hy' τ)))
  hRL : ∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
    RT2 S k3 (.data d (PL.isub (ISub.cons y hy τ))) (.data d (PL.isub (ISub.cons y' hy' τ)))
  hArgK : ∀ c j n (g : Hom n (k + 1)) pre, (ΘK S D d (k + 1) PL).PtValid c n g pre →
    KanP2 S n ((ΘK S D d (k + 1) PL).ty c j n g pre)
  hφs : φ.Scoped k
  h12 : I.Entails φ φ'
  h21 : I.Entails φ' φ
  hLC : LineConst S k (.data d PL) φ
  hty : HasTy S k .one [] (.transp (.data d PL) φ (.con d c q (Tm.ofList X) [])) (.data d (PL.dinst .one))
  hty' : HasTy S k .one [] (.transp (.data d QL) φ' (.con d c q' (Tm.ofList X') [])) (.data d (PL.dinst .one))
  heq : EqTm S k .one [] (.transp (.data d PL) φ (.con d c q (Tm.ofList X) []))
    (.transp (.data d QL) φ' (.con d c q' (Tm.ofList X') [])) (.data d (PL.dinst .one))
  hargs0 : ∀ i (hi : i < C.args.length), RE2 S k ((C.argTy d D.params.length i).substList
    ((X.take i).reverse ++ (PL.dinst .zero).toList.reverse)) (X.getD i .abort) (X'.getD i .abort)
  hrecT : ∀ i (hi : i < C.args.length), C.isRec i = true → ∀ k3 (τ : ISub k3 k) (y y' : I)
    (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
    KanT2At S k3 ((Tm.data d PL).isub (ISub.cons y hy τ.up.tail)) ((Tm.data d QL).isub (ISub.cons y' hy' τ.up.tail))
      ((X.getD i .abort).isub τ) ((X'.getD i .abort).isub τ)

/-- The argument line of a transported constructor. -/
abbrev tl (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) (j : ℕ) : Tm :=
  Meta.tLine (C.argTy d D.params.length) ps.toList φ X j

/-- The transport fillers of the arguments of a transported constructor. -/
abbrev tF (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) : List Tm :=
  Meta.tFills (C.argTy d D.params.length) ps.toList φ X C.args.length

theorem tF_getD (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) {j : ℕ} (hj : j < C.args.length) :
    (tF d D C ps φ X).getD j .abort = Tm.transpFill (tl d D C ps φ X j) φ (X.getD j .abort) :=
  Meta.tFills_get _ _ _ _ hj

theorem tF_length (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) :
    (tF d D C ps φ X).length = C.args.length := Meta.tFills_length _ _ _ _ _

theorem tl_eq (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) {j : ℕ} (hj : j ≤ C.args.length) :
    tl d D C ps φ X j = (C.argTy d D.params.length j).substList
      (((tF d D C ps φ X).take j).reverse ++ ps.toList.reverse) := by
  have := Meta.tFills_take (C.argTy d D.params.length) ps.toList φ X j (C.args.length - j)
  rw [show j + (C.args.length - j) = C.args.length by omega] at this
  show (C.argTy d D.params.length j).substList _ = _
  rw [this]

theorem tOuts_getD (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) {j : ℕ} (hj : j < C.args.length) :
    (tOuts d D C ps φ X).getD j .abort = Tm.transp (tl d D C ps φ X j) φ (X.getD j .abort) := by
  simp only [tOuts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]

theorem tOuts_length (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) :
    (tOuts d D C ps φ X).length = C.args.length := by simp [tOuts]

section typing
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ [])
  (hH : D.isHIT = false)
include hW hD hp hH

/-- The typings of the argument lines, transports and fillers of a transported constructor. -/
theorem tcon_typing {ps qs T : Tm} {φ : I} {c : ℕ} {C : Ctor} {X : List Tm} (hC : D.ctors[c]? = some C)
    (hty : HasTy S k .one [] (.transp (.data d ps) φ (.con d c qs (Tm.ofList X) [])) T) {j : ℕ}
    (hj : j < C.args.length) :
    ∃ l, HasTy S (k + 1) .one [] (tl d D C ps φ X j) (.univ l) ∧
      HasTy S k .one [] (.transp (tl d D C ps φ X j) φ (X.getD j .abort)) ((tl d D C ps φ X j).dinst .one) ∧
      HasTy S (k + 1) .one [] (Tm.transpFill (tl d D C ps φ X j) φ (X.getD j .abort)) (tl d D C ps φ X j) ∧
      HasTy S k .one [] (X.getD j .abort) ((tl d D C ps φ X j).dinst .zero) ∧
      HasTy S k .one [] (.transp (tl d D C ps φ X j) φ (X.getD j .abort))
        ((C.argTy d D.params.length j).substList (((tOuts d D C ps φ X).take j).reverse ++
          (ps.dinst .one).toList.reverse)) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨-, htp, hXl⟩ := transpCon_eq hW hD hp hH hC hty
  obtain ⟨l0, ⟨hLt, hφ, hc, -⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  obtain ⟨D', hD', hPt⟩ := gen_data_tele hLt rfl
  rw [hD] at hD'; cases hD'
  have hPl : ps = Tm.ofList ps.toList := tele_isList hPt
  obtain ⟨-, -, -, -, -, Tel⟩ := transpCon_inv hS hW (htr_of hW d) hD hC hPl (by simpa using htp) hLt hφ hc
    C.args.length (Nat.le_refl _)
  have h1 := Tel j hj
  simp only [toList_ofList] at h1
  have h1' : HasTy0 S k .one [] (.transp (tl d D C ps φ X j) φ (X.getD j .abort))
      ((C.argTy d D.params.length j).substList (((tOuts d D C ps φ X).take j).reverse ++
        (ps.dinst .one).toList.reverse)) := by
    rw [← tOuts_getD d D C ps φ X hj]; exact h1
  obtain ⟨lj, ⟨hLj, hψj, hcj, hbj⟩, -⟩ := gen_transpF h1' rfl
  exact ⟨lj, minimal_to_spec hLj, minimal_to_spec (HasTy0.transp hLj hψj hcj hbj),
    minimal_to_spec (transpFill_typed hS hLj hψj hcj hbj).1, minimal_to_spec hbj, minimal_to_spec h1'⟩

end typing

section lines
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- A restriction of an argument line. -/
theorem tl_isub {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps : Tm} (hps : IsList ps) (φ : I) (X : List Tm)
    {j : ℕ} (hj : j ≤ C.args.length) (σ : ISub k' k) :
    (tl d D C ps φ X j).isub σ = (C.argTy d D.params.length j).substList
      ((((tF d D C ps φ X).map (·.isub σ)).take j).reverse ++ (ps.isub σ).toList.reverse) := by
  rw [tl_eq d D C ps φ X hj, argTy_isub (sigClosed_of_wfSig hW) hD hC j _ hps σ]

omit hW hD in
/-- The argument line of a recursive argument is the line of the inductive type. -/
theorem tl_rec {C : Ctor} {ps : Tm} (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (φ : I)
    (X : List Tm) {j : ℕ} (hj : j ≤ C.args.length) (hr : C.isRec j = true) :
    tl d D C ps φ X j = .data d ps := by
  rw [tl_eq d D C ps φ X hj, argTy_rec_inst hr hps hpl (by simp [tF_length]; omega)]

end lines

/-- The facts about the `i`-th argument of a transported constructor, established along the arguments. -/
def Good (S : Sig) (k d : ℕ) (D : DataDecl) (PL QL : Tm) (φ φ' : I) (C : Ctor) (X X' : List Tm) (i : ℕ) : Prop :=
  (∀ k3 (σ σ' : ISub k3 (k + 1)), σ.tail = σ'.tail → I.Eq (σ.τ 0) (σ'.τ 0) →
    RE2 S k3 ((tl d D C PL φ X i).isub σ) ((Tm.transpFill (tl d D C PL φ X i) φ (X.getD i .abort)).isub σ)
      ((Tm.transpFill (tl d D C QL φ' X' i) φ' (X'.getD i .abort)).isub σ')) ∧
  (∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
    RT2 S k3 ((tl d D C PL φ X i).isub (ISub.cons y hy τ)) ((tl d D C QL φ' X' i).isub (ISub.cons y' hy' τ))) ∧
  (∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped k3) (hy' : y'.Scoped k3), I.Eq y y' →
    RT2 S k3 ((tl d D C PL φ X i).isub (ISub.cons y hy τ)) ((tl d D C PL φ X i).isub (ISub.cons y' hy' τ))) ∧
  LineConst S k (tl d D C PL φ X i) φ ∧
  RT2 S k ((C.argTy d D.params.length i).substList ((X.take i).reverse ++ (PL.dinst .zero).toList.reverse))
    ((tl d D C PL φ X i).dinst .zero) ∧
  RE2 S k ((tl d D C PL φ X i).dinst .one) (.transp (tl d D C PL φ X i) φ (X.getD i .abort))
    (.transp (tl d D C QL φ' X' i) φ' (X'.getD i .abort)) ∧
  RT2 S k ((tl d D C PL φ X i).dinst .one) ((C.argTy d D.params.length i).substList
    (((tOuts d D C PL φ X).take i).reverse ++ (PL.dinst .one).toList.reverse)) ∧
  (∀ k3 (τ : ISub k3 k) (y y' : I) (hy : y.Scoped (k3 + 1)) (hy' : y'.Scoped (k3 + 1)), I.Eq y y' →
    KanT2At S k3 ((tl d D C PL φ X i).isub (ISub.cons y hy τ.up.tail))
      ((tl d D C QL φ' X' i).isub (ISub.cons y' hy' τ.up.tail)) ((X.getD i .abort).isub τ) ((X'.getD i .abort).isub τ))

/-- The Kan properties of the argument types' codes, at a restriction of a literal inductive type. -/
theorem argK_restr {d : ℕ} {D : DataDecl} {K : ℕ} {P : Tm}
    (hArgK : ∀ c j n (g : Hom n K) pre, (ΘK S D d K P).PtValid c n g pre → KanP2 S n ((ΘK S D d K P).ty c j n g pre))
    (σ : ISub k' K) : ∀ c j n (g : Hom n k') pre, (ΘK S D d k' (P.isub σ)).PtValid c n g pre →
      KanP2 S n ((ΘK S D d k' (P.isub σ)).ty c j n g pre) := by
  rw [← ΘK_restr]
  intro c j n g pre hv
  exact hArgK c j n (σ.hom.comp g) pre hv

namespace TC

variable {d : ℕ} {D : DataDecl} {PL QL : Tm} {φ φ' : I} {c : ℕ} {C : Ctor} {q q' : Tm} {X X' : List Tm}
  (H : TC S k d D PL QL φ φ' c C q q' X X')
include H

/-- The basic facts: the `transpCon` equations, the arguments' telescopes, the parameters. -/
theorem basic :
    EqTm S k .one [] (.transp (.data d PL) φ (.con d c q (Tm.ofList X) [])) (tCon d D c C PL φ X)
      (.data d (PL.dinst .one)) ∧
    EqTm S k .one [] (.transp (.data d QL) φ' (.con d c q' (Tm.ofList X') [])) (tCon d D c C QL φ' X')
      (.data d (PL.dinst .one)) ∧
    HasTele0 S k .one [] (Tm.ofList X) (C.argTys d D.params.length) (PL.dinst .zero).toList.reverse ∧
    HasTele0 S k .one [] (Tm.ofList X') (C.argTys d D.params.length) (QL.dinst .zero).toList.reverse ∧
    X.length = C.args.length ∧ X'.length = C.args.length ∧
    IsList PL ∧ IsList QL ∧ PL.toList.length = D.params.length ∧ QL.toList.length = D.params.length ∧
    PL.closedB 0 (k + 1) = true ∧ QL.closedB 0 (k + 1) = true := by
  obtain ⟨e, ht, hl⟩ := transpCon_eq H.hW H.hD H.hp H.hH H.hC H.hty
  obtain ⟨e', ht', hl'⟩ := transpCon_eq H.hW H.hD H.hp H.hH H.hC H.hty'
  have hdD := dataD_eq H.hW H.hD
  obtain ⟨l0, ⟨hLt, -, -, -⟩, -⟩ := gen_transpF (spec_to_minimal H.hW H.hty') rfl
  obtain ⟨D', hD', hQt⟩ := gen_data_tele hLt rfl
  rw [H.hD] at hD'; cases hD'
  obtain ⟨D'', hD'', hPt⟩ := gen_data_tele (spec_to_minimal H.hW H.hPL) rfl
  rw [H.hD] at hD''; cases hD''
  refine ⟨e, e', ht, ht', hl, hl', tele_isList hPt, tele_isList hQt, by simpa using Meta.tele_length hPt,
    by simpa using Meta.tele_length hQt, ?_, ?_⟩
  · have := closed_of_ty H.hW H.hPL; simpa [Tm.closedB] using this
  · have := closed_ty hLt; simpa [Tm.closedB] using this

/-- The restricted fillers of the earlier arguments are related, at the restricted argument lines. -/
theorem pre_rel {j : ℕ} (hj : j ≤ C.args.length)
    (ih : ∀ i, i < j → Good S k d D PL QL φ φ' C X X' i) {k3 : ℕ} (τ : ISub k3 k) (y y' : I)
    (hy : y.Scoped k3) (hy' : y'.Scoped k3) (hE : I.Eq y y') :
    ∀ i (hi : i < j), RE2 S k3 ((C.argTy d D.params.length i).substList
      (((((tF d D C PL φ X).map (·.isub (ISub.cons y hy τ))).take j).take i).reverse ++
        (PL.isub (ISub.cons y hy τ)).toList.reverse))
      ((((tF d D C PL φ X).map (·.isub (ISub.cons y hy τ))).take j).getD i .abort)
      ((((tF d D C QL φ' X').map (·.isub (ISub.cons y' hy' τ))).take j).getD i .abort) := by
  intro i hi
  obtain ⟨-, -, -, -, -, -, hPl, -⟩ := H.basic
  have hlF := tF_length d D C PL φ X
  have hlF' := tF_length d D C QL φ' X'
  rw [List.take_take, Nat.min_eq_left hi.le, getD_take_lt hi, getD_take_lt hi,
    getD_map_isub' (by omega), getD_map_isub' (by omega), tF_getD d D C PL φ X (by omega),
    tF_getD d D C QL φ' X' (by omega), ← tl_isub H.hW H.hD H.hC hPl φ X (by omega)]
  exact (ih i hi).1 k3 _ _ rfl hE

/-- The restricted fillers of the earlier arguments, at `I.Eq`-equal points, are related. -/
theorem pre_self {j : ℕ} (hj : j ≤ C.args.length)
    (ih : ∀ i, i < j → Good S k d D PL QL φ φ' C X X' i) {k3 : ℕ} (τ : ISub k3 k) (y y' : I)
    (hy : y.Scoped k3) (hy' : y'.Scoped k3) (hE : I.Eq y y') :
    ∀ i (hi : i < j), RE2 S k3 ((C.argTy d D.params.length i).substList
      (((((tF d D C PL φ X).map (·.isub (ISub.cons y hy τ))).take j).take i).reverse ++
        (PL.isub (ISub.cons y hy τ)).toList.reverse))
      ((((tF d D C PL φ X).map (·.isub (ISub.cons y hy τ))).take j).getD i .abort)
      ((((tF d D C PL φ X).map (·.isub (ISub.cons y' hy' τ))).take j).getD i .abort) := by
  intro i hi
  obtain ⟨-, -, -, -, -, -, hPl, -⟩ := H.basic
  have hlF := tF_length d D C PL φ X
  rw [List.take_take, Nat.min_eq_left hi.le, getD_take_lt hi, getD_take_lt hi,
    getD_map_isub' (by omega), getD_map_isub' (by omega), tF_getD d D C PL φ X (by omega),
    ← tl_isub H.hW H.hD H.hC hPl φ X (by omega)]
  obtain ⟨G1, -, G3, -⟩ := ih i hi
  have a := G1 k3 (ISub.cons y hy τ) (ISub.cons y' hy' τ) rfl hE
  have b := G1 k3 (ISub.cons y' hy' τ) (ISub.cons y' hy' τ) rfl (I_eq_refl _)
  have r := G3 k3 τ y y' hy hy' hE
  have hX : TyCode k3 (semK S k3 ((tl d D C PL φ X i).isub (ISub.cons y hy τ))) := RE2.tyCode H.hW a
  have b' := RE2.conv H.hW (RT2.symm H.hW hX r) b
  exact RE2.trans H.hW r a (RE2.symm H.hW r b')

/-- A restricted argument line is related to the argument type at arguments related to the restricted
fillers. -/
theorem line_rt2 {j : ℕ} (hj : j < C.args.length) {k3 : ℕ} (σ : ISub k3 (k + 1)) {Q2 : Tm}
    (hσσ : RT2 S k3 (.data d (PL.isub σ)) (.data d (PL.isub σ)))
    (hQ2 : RT2 S k3 (.data d (PL.isub σ)) (.data d Q2)) {B : List Tm} (hBl : B.length = j)
    (hrel : ∀ i (hi : i < j), RE2 S k3 ((tl d D C PL φ X i).isub σ) (((tF d D C PL φ X).getD i .abort).isub σ)
      (B.getD i .abort)) :
    RT2 S k3 ((tl d D C PL φ X j).isub σ) ((C.argTy d D.params.length j).substList (B.reverse ++ Q2.toList.reverse)) := by
  obtain ⟨-, -, -, -, -, -, hPl, -⟩ := H.basic
  have hlF := tF_length d D C PL φ X
  rw [tl_isub H.hW H.hD H.hC hPl φ X hj.le]
  refine argTy_rt2' H.hW H.hD H.hH (HasTy.isubS H.hW H.hPL σ) hσσ hQ2 H.hC hj (by simp; omega) hBl fun i hi => ?_
  have h := hrel i hi
  rw [tl_isub H.hW H.hD H.hC hPl φ X (by omega), ← getD_map_isub' (by omega)] at h
  rw [List.take_take, Nat.min_eq_left hi.le, getD_take_lt hi]
  exact h

/-- Transport along restricted argument lines, at restricted fillers related to each other. -/
theorem line_kanT {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false) {k3 : ℕ} (θ θ' : ISub (k3 + 1) (k + 1))
    (hθθ : RT2 S (k3 + 1) (.data d (PL.isub θ)) (.data d (PL.isub θ)))
    (hθθ' : RT2 S (k3 + 1) (.data d (PL.isub θ)) (.data d (QL.isub θ')))
    (hrel : ∀ i (hi : i < j), RE2 S (k3 + 1) ((tl d D C PL φ X i).isub θ) (((tF d D C PL φ X).getD i .abort).isub θ)
      (((tF d D C QL φ' X').getD i .abort).isub θ')) :
    KanT2 S k3 ((tl d D C PL φ X j).isub θ) ((tl d D C QL φ' X' j).isub θ') := by
  obtain ⟨-, -, -, -, -, -, hPl, hQl, -⟩ := H.basic
  have hlF := tF_length d D C PL φ X
  have hlF' := tF_length d D C QL φ' X'
  have hAlen : (((tF d D C PL φ X).map (·.isub θ)).take j).length = j := by simp; omega
  have K := argLine_kanT H.hW H.hD H.hH (HasTy.isubS H.hW H.hPL θ) hθθ hθθ' (argK_restr H.hArgK θ) H.hC
    (A := ((tF d D C PL φ X).map (·.isub θ)).take j) (B := ((tF d D C QL φ' X').map (·.isub θ')).take j)
    (by rw [hAlen]; simp; omega) (by rw [hAlen]; exact hj) (by rw [hAlen]; exact hrj)
    (fun i hi => by
      have hi' : i < j := by simp at hi; omega
      have h := hrel i hi'
      rw [tl_isub H.hW H.hD H.hC hPl φ X (by omega), ← getD_map_isub' (by omega), ← getD_map_isub' (by omega)] at h
      rw [List.take_take, Nat.min_eq_left hi'.le, getD_take_lt hi', getD_take_lt hi']
      exact h)
  rw [hAlen] at K
  rw [tl_isub H.hW H.hD H.hC hPl φ X hj.le, tl_isub H.hW H.hD H.hC hQl φ' X' hj.le]
  exact K

end TC

end

end Model.Whnf
