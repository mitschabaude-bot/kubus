import Model.Whnf.HCCGen2

/-!
# Composition of related constructors: the data of each argument

For a recursive argument, the compositions of the projections of the tubes over the base's
arguments; for a point argument, the type lines (related, robust and Kan, at the code of the
inductive type) and the projections of the tubes along them.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

namespace HCG

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {X X' : List Tm} {φ φ' : I} {us us' : List Tm}
  (H : HCG S d D K P Q Q' k1 ρ c C X X' φ φ' us us')
include H

/-- The line of a point argument is Kan at all its restrictions. -/
theorem lineKan {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) {n : ℕ} (τ : ISub n k1) (r : I) (hr : r.Scoped n)
    {X'' : Tm} (hR : RT2 S n (argTyAt d D C (gFills d D C (Q.isub ρ) φ us X) Q ρ j τ r hr) X'') :
    KanH2 S n (argTyAt d D C (gFills d D C (Q.isub ρ) φ us X) Q ρ j τ r hr) X'' ∧
      ∀ {n' : ℕ} (e : n = n' + 1), KanT2 S n' (argTyAt d D C (gFills d D C (Q.isub ρ) φ us X) Q ρ j τ r hr) X'' := by
  have hFl := fills_len (d := d) (D := D) (C := C) (Q.isub ρ) φ us X
  have hFl' := fills_len (d := d) (D := D) (C := C) (Q'.isub ρ) φ' us' X'
  have hRR' := argRelH_QQ H.hW H.hD H.hP H.hQ H.hQ' (ρ.comp τ)
  have hQT : IsTyK S n (.data d (Q.isub (ρ.comp τ))) := ((Comp2_ty_base H.hQ).2.2.1).isub H.hW (ρ.comp τ)
  have hQ'T : IsTyK S n (.data d (Q'.isub (ρ.comp τ))) := ((Comp2_ty_base H.hQ').2.2.1).isub H.hW (ρ.comp τ)
  have hc1 : (Q.isub (ρ.comp τ)).closedB 0 n = true := by
    have := closed_of_isTyK H.hW hQT; simpa [Tm.closedB] using this
  have hc2 : (Q'.isub (ρ.comp τ)).closedB 0 n = true := by
    have := closed_of_isTyK H.hW hQ'T; simpa [Tm.closedB] using this
  have hcode := argTy_code_rel H.hW H.hD H.hP (ρ.comp τ) hRR' (semK_dataQ H.hW H.hD H.hP H.hQ (ρ.comp τ)) hc1 hc2
    H.hC (A := ((gFills d D C (Q.isub ρ) φ us X).map (·.isub (ISub.cons r hr τ))).take j)
    (A' := ((gFills d D C (Q'.isub ρ) φ' us' X').map (·.isub (ISub.cons r hr τ))).take j)
    (by simp [hFl, hFl'])
    (fun i hi hi' hri => by
      have hij : i < j := by simp [hFl] at hi; omega
      have h1 := (hV i hij).1 n τ r r hr hr (I_eq_refl _)
      rw [H.argTyAt_rec (by omega) hri τ r hr] at h1
      rw [← getD_eq_get hi, ← getD_eq_get hi', getD_take_lt hij,
        getD_take_lt hij, getD_map_isub, getD_map_isub]
      exact h1)
    (fun i hi hi' hri => by
      have hij : i < j := by simp [hFl] at hi; omega
      have h1 := (hV i hij).1 n τ r r hr hr (I_eq_refl _)
      rw [← getD_eq_get hi, ← getD_eq_get hi', getD_take_lt hij,
        getD_take_lt hij, getD_map_isub, getD_map_isub, List.take_take, Nat.min_eq_left hij.le]
      exact h1)
    (by simp [hFl]; omega) (by simp [hFl]; rw [Nat.min_eq_left (by omega)]; exact hrj)
  have hl : (((gFills d D C (Q.isub ρ) φ us X).map (·.isub (ISub.cons r hr τ))).take j).length = j := by
    simp [hFl]; omega
  rw [hl] at hcode
  have hb := Comp2_ty_base hcode.1
  have hR' := (Comp2_ty_iff hb.1 hb.2.2.2.1).2 hR
  exact ⟨hcode.2.1 n (Hom.id n) _ _ hR', fun {n'} e => by
    subst e
    exact hcode.2.2 n' (Hom.id (n' + 1)) _ _ hR'⟩

/-- The type line of a point argument, against the right one. -/
theorem ptLR {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    LineRob S k1 (gLine d D C (Q.isub ρ) φ us X j) (gLine d D C (Q'.isub ρ) φ' us' X' j) := by
  intro k3 τ r r' hr hr' hE
  rw [H.lineσ hj.le τ r hr, H.lineσ' hj.le τ r' hr']
  exact H.relLine hj hV τ r r' hr hr' hE

theorem ptXL {j : ℕ} (hj : j < C.args.length) {k3 : ℕ} (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3) :
    TyCode k3 (semK S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub (ISub.cons r hr τ))) := by
  have B := H.basic
  have G1 := H.G1
  have G3 := H.G3
  cases hrj : C.isRec j
  · obtain ⟨A0, hA0⟩ := argTy_point hj hrj
    obtain ⟨hLt, -, -, -⟩ := hcompCon_pt_types H.hW H.hD H.hH H.hC (spec_to_minimal H.hW B.hqT) B.hφs B.hXq G1 G3 hA0
    exact tyCode_of_univ H.hW (HasTy.isubS H.hW (minimal_to_spec hLt) (ISub.cons r hr τ))
  · rw [H.lineσ hj.le τ r hr, H.argTyAt_rec hj hrj τ r hr]
    have h := HasTy.isubS H.hW B.hqT τ
    rw [show (Tm.data d (Q.isub ρ)).isub τ = .data d (Q.isub (ρ.comp τ)) by
      show Tm.data d ((Q.isub ρ).isub τ) = _; rw [Tm.isub_isub]] at h
    exact tyCode_of_univ H.hW h

/-- The type line of a point argument, against itself. -/
theorem ptLRL {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    LineRob S k1 (gLine d D C (Q.isub ρ) φ us X j) (gLine d D C (Q.isub ρ) φ us X j) := by
  intro k3 τ r r' hr hr' hE
  have h1 := H.ptLR hj hV k3 τ r r' hr hr' hE
  have h2 := H.ptLR hj hV k3 τ r' r' hr' hr' (I_eq_refl _)
  exact RT2.trans H.hW (H.ptXL hj τ r hr) h1 (RT2.symm H.hW (H.ptXL hj τ r' hr') h2)

/-- Transport along the restrictions of the type line of a point argument. -/
theorem ptKT {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    ∀ k3 (Θ : ISub (k3 + 1) (k1 + 1)) X'', RT2 S (k3 + 1) ((gLine d D C (Q.isub ρ) φ us X j).isub Θ) X'' →
      KanT2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub Θ) X'' := by
  intro k3 Θ X'' hR
  rw [← ISub.cons_tail Θ, H.lineσ hj.le] at hR ⊢
  exact (H.lineKan hj hrj hV Θ.tail _ _ hR).2 rfl

/-- Composition at the restrictions of the type line of a point argument. -/
theorem ptKH {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    ∀ k3 (Θ : ISub k3 (k1 + 1)) X'', RT2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub Θ) X'' →
      KanH2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub Θ) X'' := by
  intro k3 Θ X'' hR
  rw [← ISub.cons_tail Θ, H.lineσ hj.le] at hR ⊢
  exact (H.lineKan hj hrj hV Θ.tail _ _ hR).1

/-- The projections of the tubes along the type line of a point argument. -/
theorem ptTube {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i)
    {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3) (hE : I.Eq r r')
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub (ISub.cons r hr σ))
      ((((us).getD j .abort).isub σ.up).dinst r)
      ((((us').getD j .abort).isub σ.up).dinst r') := by
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r' hr', H.lineσ hj.le σ r hr]
  have hF := H.relFU hj hV σ r hr hh
  have hX := H.ptXL hj σ r hr
  rw [H.lineσ hj.le σ r hr] at hX
  exact RE2.conv H.hW (RT2.symm H.hW hX hF) (H.prj σ r r' hr hr' hE hh j hj)

/-- The projections of the left tube along the type line of a point argument, against themselves. -/
theorem ptTubes {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i)
    {k3 : ℕ} (σ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3) (hE : I.Eq r r')
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub (ISub.cons r hr σ))
      ((((us).getD j .abort).isub σ.up).dinst r)
      ((((us).getD j .abort).isub σ.up).dinst r') := by
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r' hr', H.lineσ hj.le σ r hr]
  have hF := H.relFU hj hV σ r hr hh
  have hX := H.ptXL hj σ r hr
  rw [H.lineσ hj.le σ r hr] at hX
  exact RE2.conv H.hW (RT2.symm H.hW hX hF) (H.prjs σ r r' hr hr' hE hh j hj)


/-- The projections of the left tube at `0` along the type line, against the right base. -/
theorem ptBd {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i)
    {k3 : ℕ} (σ : ISub k3 k1) (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub (ISub.cons .zero trivial σ))
      ((((us).getD j .abort).isub σ.up).dinst .zero) ((X'.getD j .abort).isub σ) := by
  rw [isub_up_dinst _ σ .zero trivial, H.lineσ hj.le σ .zero trivial]
  have hF := H.relFU hj hV σ .zero trivial hh
  have hX := H.ptXL hj σ .zero trivial
  rw [H.lineσ hj.le σ .zero trivial] at hX
  exact RE2.conv H.hW (RT2.symm H.hW hX hF) (H.prjb σ hh j hj)

/-- The type at the base, restricted. -/
theorem baseTyσ {j : ℕ} (hj : j < C.args.length) {k3 : ℕ} (σ : ISub k3 k1) :
    ((C.argTy d D.params.length j).substList ((X.take j).reverse ++ (P.isub ρ).toList.reverse)).isub σ =
      (C.argTy d D.params.length j).substList (((X.map (·.isub σ)).take j).reverse ++
        (P.isub (ρ.comp σ)).toList.reverse) := by
  rw [argTy_isub (sigClosed_of_wfSig H.hW) H.hD H.hC j X (dataLit_rel H.hW H.hD H.hP H.hPP ρ).2.2.2.2.2.1 σ,
    Tm.isub_isub]

/-- The base arguments, restricted. -/
theorem baseσ {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false) {k3 : ℕ} (σ : ISub k3 k1) :
    RE2 S k3 ((C.argTy d D.params.length j).substList (((X.map (·.isub σ)).take j).reverse ++
        (P.isub (ρ.comp σ)).toList.reverse)) ((X.getD j .abort).isub σ) ((X'.getD j .abort).isub σ) := by
  have := RE2.isub H.hW (H.hptR j hj hrj) σ
  rwa [H.baseTyσ hj σ] at this

/-- The projections of the left tube at `0` along the type line, against the left base. -/
theorem ptBds {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i)
    {k3 : ℕ} (σ : ISub k3 k1) (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub (ISub.cons .zero trivial σ))
      ((((us).getD j .abort).isub σ.up).dinst .zero) ((X.getD j .abort).isub σ) := by
  have h1 := H.ptBd hj hV σ hh
  have hX := H.ptXL hj σ .zero trivial
  have hT := H.relFX hj hV σ
  rw [← H.lineσ hj.le σ .zero trivial] at hT
  have hXT := RT2.tyCode_r H.hW hT hX
  have h2 := RE2.conv H.hW (RT2.symm H.hW hX hT) (H.baseσ hj hrj σ)
  have hTT := RT2.refl H.hW hX hT
  exact RE2.trans H.hW hTT h1 (RE2.symm H.hW hTT h2)

/-- The left base against the projections of the right tube at `0`, along the type line. -/
theorem ptBd' {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i)
    {k3 : ℕ} (σ : ISub k3 k1) (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((gLine d D C (Q.isub ρ) φ us X j).isub (ISub.cons .zero trivial σ))
      ((X.getD j .abort).isub σ) ((((us').getD j .abort).isub σ.up).dinst .zero) := by
  rw [isub_up_dinst _ σ .zero trivial]
  have hX := H.ptXL hj σ .zero trivial
  have hT := H.relFX hj hV σ
  rw [← H.lineσ hj.le σ .zero trivial] at hT
  exact RE2.conv H.hW (RT2.symm H.hW hX hT) (H.prjb' σ hh j hj)

theorem X_closed {j : ℕ} (hj : j < C.args.length) : (X.getD j .abort).closedB 0 k1 = true := by
  have B := H.basic
  have := tele_get B.hXq j (X.getD j .abort) _ (by
    rw [toList_ofList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [H.hXl]; exact hj)]; rfl)
    (argTys_get hj)
  exact closed_ty this

theorem X_map_id : X.map (·.isub (ISub.id k1)) = X := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map]
  have := H.X_closed (j := i) (by rw [← H.hXl]; exact h2)
  rw [getD_eq_get h2] at this
  exact isub_id_of_closed this

/-- The type line of a point argument along `hcompCon`, with its endpoints and its face. -/
theorem ptTypes {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false) :
    ∃ A0, C.args[j]? = some (.point A0) ∧ C.argTy d D.params.length j = A0 ∧
    HasTy0 S (k1 + 1) .one [] (gLine d D C (Q.isub ρ) φ us X j) (.univ D.level) ∧
    EqTm S k1 .one [] ((gLine d D C (Q.isub ρ) φ us X j).dinst .zero)
      (A0.substList ((X.take j).reverse ++ (Q.isub ρ).toList.reverse)) (.univ D.level) ∧
    EqTm S k1 .one [] ((gLine d D C (Q.isub ρ) φ us X j).dinst .one)
      (A0.substList (((gOuts d D C (Q.isub ρ) φ us X).take j).reverse ++ (Q.isub ρ).toList.reverse)) (.univ D.level) ∧
    EqTm0 S (k1 + 1) (cof .one φ).shift [] (gLine d D C (Q.isub ρ) φ us X j)
      (A0.substList (((us).take j).reverse ++ (Q.isub ρ).dshift.toList.reverse))
      (.univ D.level) := by
  have B := H.basic
  have G1 := H.G1
  have G3 := H.G3
  obtain ⟨A0, hA0⟩ := argTy_point hj hrj
  obtain ⟨hLt, e0, e1, eφ⟩ := hcompCon_pt_types H.hW H.hD H.hH H.hC (spec_to_minimal H.hW B.hqT) B.hφs B.hXq G1 G3 hA0
  exact ⟨A0, hA0, by simp [Ctor.argTy, hA0], hLt, e0, e1, eφ⟩

/-- The type line of a point argument along `hcompCon`, on the right. -/
theorem ptTypes' {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false) :
    ∃ A0, C.args[j]? = some (.point A0) ∧ C.argTy d D.params.length j = A0 ∧
    HasTy0 S (k1 + 1) .one [] (gLine d D C (Q'.isub ρ) φ' us' X' j) (.univ D.level) ∧
    EqTm S k1 .one [] ((gLine d D C (Q'.isub ρ) φ' us' X' j).dinst .zero)
      (A0.substList ((X'.take j).reverse ++ (Q'.isub ρ).toList.reverse)) (.univ D.level) ∧
    EqTm S k1 .one [] ((gLine d D C (Q'.isub ρ) φ' us' X' j).dinst .one)
      (A0.substList (((gOuts d D C (Q'.isub ρ) φ' us' X').take j).reverse ++ (Q'.isub ρ).toList.reverse))
        (.univ D.level) ∧
    EqTm0 S (k1 + 1) (cof .one φ').shift [] (gLine d D C (Q'.isub ρ) φ' us' X' j)
      (A0.substList (((us').take j).reverse ++ (Q'.isub ρ).dshift.toList.reverse))
      (.univ D.level) := by
  have B := H.basic
  have G1 := H.G1'
  have G3 := H.G3'
  obtain ⟨A0, hA0⟩ := argTy_point hj hrj
  obtain ⟨hLt, e0, e1, eφ⟩ := hcompCon_pt_types H.hW H.hD H.hH H.hC (spec_to_minimal H.hW B.hq'T) B.hφs' B.hXq' G1 G3 hA0
  exact ⟨A0, hA0, by simp [Ctor.argTy, hA0], hLt, e0, e1, eφ⟩

theorem line_closed {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false) :
    (gLine d D C (Q.isub ρ) φ us X j).closedB 0 (k1 + 1) = true := by
  obtain ⟨A0, -, -, hLt, -⟩ := H.ptTypes hj hrj
  exact closed_ty hLt

/-- The bases, along the type line at `0`. -/
theorem ptU0 {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    RE2 S k1 ((gLine d D C (Q.isub ρ) φ us X j).dinst .zero) (X.getD j .abort) (X'.getD j .abort) := by
  have hX := H.ptXL hj (ISub.id k1) .zero trivial
  have hT := H.relFX hj hV (ISub.id k1)
  rw [← H.lineσ hj.le (ISub.id k1) .zero trivial, H.X_map_id, ISub.comp_id] at hT
  rw [isub_cons_id_of_closed (H.line_closed hj hrj)] at hT hX
  exact RE2.conv H.hW (RT2.symm H.hW hX hT) (H.hptR j hj hrj)


/-- The type lines of a point argument are judgmentally equal. -/
theorem ptLL' {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    RT2 S (k1 + 1) (gLine d D C (Q.isub ρ) φ us X j) (gLine d D C (Q'.isub ρ) φ' us' X' j) := by
  have h := H.ptLR hj hV (k1 + 1) (ISub.id (k1 + 1)).tail ((ISub.id (k1 + 1)).τ 0) ((ISub.id (k1 + 1)).τ 0)
    ((ISub.id (k1 + 1)).sc 0 (by omega)) ((ISub.id (k1 + 1)).sc 0 (by omega)) (I_eq_refl _)
  rw [ISub.cons_tail] at h
  obtain ⟨-, -, -, hLt, -⟩ := H.ptTypes hj hrj
  obtain ⟨-, -, -, hLt', -⟩ := H.ptTypes' hj hrj
  rwa [isub_id_of_closed (closed_ty hLt), isub_id_of_closed (closed_ty hLt')] at h

/-- The fillers and the composites of a point argument: typing and judgmental equality. -/
theorem ptFill {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = false)
    (hV : ∀ i, i < j → GInv S d D Q Q' ρ C X X' φ φ' us us' i) :
    HasTy S (k1 + 1) .one [] ((gFills d D C (Q.isub ρ) φ us X).getD j .abort) (gLine d D C (Q.isub ρ) φ us X j) ∧
    HasTy S (k1 + 1) .one [] ((gFills d D C (Q'.isub ρ) φ' us' X').getD j .abort)
      (gLine d D C (Q.isub ρ) φ us X j) ∧
    EqTm S (k1 + 1) .one [] ((gFills d D C (Q.isub ρ) φ us X).getD j .abort)
      ((gFills d D C (Q'.isub ρ) φ' us' X').getD j .abort) (gLine d D C (Q.isub ρ) φ us X j) ∧
    HasTy S k1 .one [] ((gOuts d D C (Q.isub ρ) φ us X).getD j .abort)
      ((gLine d D C (Q.isub ρ) φ us X j).dinst .one) ∧
    HasTy S k1 .one [] ((gOuts d D C (Q'.isub ρ) φ' us' X').getD j .abort)
      ((gLine d D C (Q.isub ρ) φ us X j).dinst .one) ∧
    EqTm S k1 .one [] ((gOuts d D C (Q.isub ρ) φ us X).getD j .abort)
      ((gOuts d D C (Q'.isub ρ) φ' us' X').getD j .abort) ((gLine d D C (Q.isub ρ) φ us X j).dinst .one) ∧
    EqTm S (k1 + 1) (cof .one φ).shift [] ((us).getD j .abort)
      ((us').getD j .abort) (gLine d D C (Q.isub ρ) φ us X j) := by
  have hS := sigClosed_of_wfSig H.hW
  have B := H.basic
  have G1 := H.G1
  have G4 := H.G4
  have G1' := H.G1'
  have G4' := H.G4'
  obtain ⟨A0, hA0, hAc, hLt, e0, -, eφ⟩ := H.ptTypes hj hrj
  obtain ⟨A0', hA0', hAc', hLt', e0', -, eφ'⟩ := H.ptTypes' hj hrj
  rw [hA0] at hA0'; cases hA0'
  have hXl := H.hXl
  have hXl' := H.hXl'
  set L := gLine d D C (Q.isub ρ) φ us X j with hL
  set L' := gLine d D C (Q'.isub ρ) φ' us' X' j with hL'
  -- the parts of the left side
  have hu : HasTy0 S (k1 + 1) (cof .one φ).shift [] ((us).getD j .abort) L := by
    have := tele_getD G1 (by simp [H.hul]; exact hj) (argTys_get hj)
    rw [hAc] at this
    exact HasTy0.conv this (EqTm0.symm eφ)
  have hu0 : HasTy0 S k1 .one [] (X.getD j .abort) (L.dinst .zero) := by
    have := tele_getD B.hXq (by omega) (argTys_get hj)
    rw [hAc] at this
    exact HasTy0.conv this (EqTm0.symm (spec_to_minimal_eq H.hW e0))
  have hcs : (cof .one φ).Scoped k1 := ⟨trivial, B.hφs⟩
  have hside : EqTm0 S k1 (cof .one φ) [] (((us).getD j .abort).dinst .zero)
      (X.getD j .abort) (L.dinst .zero) := by
    have := G4 j (by omega)
    rw [hAc, ← getD_eq_get (by omega)] at this
    exact EqTm0.conv this (EqTm0.symm (EqTm0.restrict hcs (ent_and_left _ _) (spec_to_minimal_eq H.hW e0)))
  -- the parts of the right side
  have hcs' : (cof .one φ').Scoped k1 := ⟨trivial, B.hφs'⟩
  have hu' : HasTy0 S (k1 + 1) (cof .one φ').shift [] ((us').getD j .abort) L' := by
    have := tele_getD G1' (by simp [H.hul']; exact hj) (argTys_get hj)
    rw [hAc] at this
    exact HasTy0.conv this (EqTm0.symm eφ')
  have hu0' : HasTy0 S k1 .one [] (X'.getD j .abort) (L'.dinst .zero) := by
    have := tele_getD B.hXq' (by omega) (argTys_get hj)
    rw [hAc] at this
    exact HasTy0.conv this (EqTm0.symm (spec_to_minimal_eq H.hW e0'))
  have hside' : EqTm0 S k1 (cof .one φ') [] (((us').getD j .abort).dinst .zero)
      (X'.getD j .abort) (L'.dinst .zero) := by
    have := G4' j (by omega)
    rw [hAc, ← getD_eq_get (by omega)] at this
    exact EqTm0.conv this (EqTm0.symm (EqTm0.restrict hcs' (ent_and_left _ _) (spec_to_minimal_eq H.hW e0')))
  -- the fillers and composites
  have hF := (fill_typed hS hLt B.hφs hu hu0 hside).1
  have hF' := (fill_typed hS hLt' B.hφs' hu' hu0' hside').1
  have hc := comp_typed hS hLt B.hφs hu hu0 hside
  have hc' := comp_typed hS hLt' B.hφs' hu' hu0' hside'
  have hLL := H.ptLL' hj hrj hV
  obtain ⟨lL, eLL⟩ := tyEq_eq H.hW (Comp2_ty_base hLL).2.2.2.2.2 ⟨_, minimal_to_spec hLt'⟩
  have eLL0 := spec_to_minimal_eq H.hW eLL
  have e1 : EqTm0 S k1 .one [] (L.dinst .one) (L'.dinst .one) (.univ lL) :=
    EqTm0.dsubst hS (Ψ := k1) (Φ := .one) (Γ := []) eLL0 (r := .one) trivial
  have hF'L : HasTy0 S (k1 + 1) .one [] (Tm.fill L' φ' ((us').getD j .abort)
      (X'.getD j .abort)) L := HasTy0.conv hF' (EqTm0.symm eLL0)
  have hc'L := HasTy0.conv hc' (EqTm0.symm e1)
  -- the tubes and bases
  have huu : EqTm0 S (k1 + 1) (cof .one φ).shift [] ((us).getD j .abort)
      ((us').getD j .abort) L := by
    have := H.euu j hj
    rw [hAc] at this
    exact EqTm0.conv this (EqTm0.symm eφ)
  have hb := (RE2.typed (H.ptU0 hj hrj hV)).2.2
  have eF := fill_cong H.hW hF hF'L ⟨_, eLL0⟩ huu (spec_to_minimal_eq H.hW hb) H.h12 H.h21
  have eC := comp_cong hS hc hc'L eLL0 H.h12 H.h21 huu (spec_to_minimal_eq H.hW hb)
  rw [fills_get_pt _ _ _ _ hj hrj, fills_get_pt _ _ _ _ hj hrj, outs_get_pt _ _ _ _ hj hrj,
    outs_get_pt _ _ _ _ hj hrj]
  exact ⟨minimal_to_spec hF, minimal_to_spec hF'L, minimal_to_spec_eq eF, minimal_to_spec hc,
    minimal_to_spec hc'L, minimal_to_spec_eq eC, minimal_to_spec_eq huu⟩


theorem eQσ {k3 : ℕ} (σ : ISub k3 k1) : (Tm.data d (Q.isub ρ)).isub σ = .data d (Q.isub (ρ.comp σ)) := by
  show Tm.data d ((Q.isub ρ).isub σ) = _; rw [Tm.isub_isub]

theorem eQ'σ {k3 : ℕ} (σ : ISub k3 k1) : (Tm.data d (Q'.isub ρ)).isub σ = .data d (Q'.isub (ρ.comp σ)) := by
  show Tm.data d ((Q'.isub ρ).isub σ) = _; rw [Tm.isub_isub]

theorem PQσ {k3 : ℕ} (σ : ISub k3 k1) : RT2 S k3 (.data d (P.isub (ρ.comp σ))) (.data d (Q.isub (ρ.comp σ))) :=
  RT2.isub H.hW (tyCode_of_univ H.hW H.hP) H.hQ (ρ.comp σ)

theorem PQ'σ {k3 : ℕ} (σ : ISub k3 k1) : RT2 S k3 (.data d (P.isub (ρ.comp σ))) (.data d (Q'.isub (ρ.comp σ))) :=
  RT2.isub H.hW (tyCode_of_univ H.hW H.hP) H.hQ' (ρ.comp σ)

theorem XPσ {k3 : ℕ} (σ : ISub k3 k1) : TyCode k3 (semK S k3 (.data d (P.isub (ρ.comp σ)))) :=
  tyCode_of_univ H.hW (HasTy.isubS H.hW H.hP (ρ.comp σ))

/-- From the type at `P` to the type at `Q`. -/
theorem toQ {k3 : ℕ} (σ : ISub k3 k1) {x y : Tm} (h : RE2 S k3 (.data d (P.isub (ρ.comp σ))) x y) :
    RE2 S k3 (.data d (Q.isub (ρ.comp σ))) x y := RE2.conv H.hW (H.PQσ σ) h

/-- The projections of the tubes of a recursive argument are related on the face. -/
theorem recTube {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) :
    Tube2 S k1 (.data d (Q.isub ρ)) φ ((us).getD j .abort)
      ((us').getD j .abort) := by
  intro k3 σ r r' hr hr' hE hh
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r' hr', H.eQσ]
  have := H.prj σ r r' hr hr' hE hh j hj
  rwa [argTy_rec_inst hrj (H.hQρl σ) (H.hQρlen σ) (by simp [H.hul]; omega)] at this

theorem recTubes {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) :
    Tube2 S k1 (.data d (Q.isub ρ)) φ ((us).getD j .abort)
      ((us).getD j .abort) := by
  intro k3 σ r r' hr hr' hE hh
  rw [isub_up_dinst _ σ r hr, isub_up_dinst _ σ r' hr', H.eQσ]
  have := H.prjs σ r r' hr hr' hE hh j hj
  rwa [argTy_rec_inst hrj (H.hQρl σ) (H.hQρlen σ) (by simp [H.hul]; omega)] at this

theorem recBd {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) {k3 : ℕ} (σ : ISub k3 k1)
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((Tm.data d (Q.isub ρ)).isub σ) ((((us).getD j .abort).isub σ.up).dinst .zero)
      ((X'.getD j .abort).isub σ) := by
  rw [isub_up_dinst _ σ .zero trivial, H.eQσ]
  have := H.prjb σ hh j hj
  rwa [argTy_rec_inst hrj (H.hQρl σ) (H.hQρlen σ) (by simp [H.hul]; omega)] at this

theorem hPρl {k3 : ℕ} (σ : ISub k3 k1) : P.isub (ρ.comp σ) = Tm.ofList (P.isub (ρ.comp σ)).toList :=
  (dataLit_rel H.hW H.hD H.hP H.hPP (ρ.comp σ)).2.2.2.2.2.1

theorem hPρlen {k3 : ℕ} (σ : ISub k3 k1) : (P.isub (ρ.comp σ)).toList.length = D.params.length := by
  have := data_len_of H.hW (⟨_, .inl (HasTy.isubS H.hW H.hP (ρ.comp σ))⟩ : IsTyK S k3 (.data d (P.isub (ρ.comp σ))))
  rwa [dataD_eq H.hW H.hD] at this

theorem recBd' {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) {k3 : ℕ} (σ : ISub k3 k1)
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((Tm.data d (Q.isub ρ)).isub σ) ((X.getD j .abort).isub σ)
      ((((us').getD j .abort).isub σ.up).dinst .zero) := by
  rw [isub_up_dinst _ σ .zero trivial, H.eQσ]
  have := H.prjb' σ hh j hj
  rw [argTy_rec_inst hrj (H.hPρl σ) (H.hPρlen σ) (by simp [H.hXl]; omega)] at this
  exact H.toQ σ this

theorem recU0 {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) {k3 : ℕ} (σ : ISub k3 k1) :
    RE2 S k3 ((Tm.data d (Q.isub ρ)).isub σ) ((X.getD j .abort).isub σ) ((X'.getD j .abort).isub σ) := by
  have := RE2.isub H.hW (H.hrecR j hj hrj) σ
  rw [H.ePσ] at this
  rw [H.eQσ]
  exact H.toQ σ this

theorem recBds {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) {k3 : ℕ} (σ : ISub k3 k1)
    (hh : (ival (idEnv k3) (φ.subst σ.τ)).holds) :
    RE2 S k3 ((Tm.data d (Q.isub ρ)).isub σ) ((((us).getD j .abort).isub σ.up).dinst .zero)
      ((X.getD j .abort).isub σ) := by
  have h1 := H.recBd hj hrj σ hh
  have h2 := H.recU0 hj hrj σ
  rw [H.eQσ] at h1 h2 ⊢
  have hQQ := RT2.refl' H.hW (H.XPσ σ) (H.PQσ σ)
  exact RE2.trans H.hW hQQ h1 (RE2.symm H.hW hQQ h2)

/-- Composition over the base of a recursive argument. -/
theorem recK {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) {k3 : ℕ} (τ : ISub k3 k1) :
    KanH2At S k3 ((Tm.data d (Q.isub ρ)).isub τ) ((Tm.data d (Q'.isub ρ)).isub τ)
      ((X.getD j .abort).isub τ) ((X'.getD j .abort).isub τ) := by
  rw [H.eQσ, H.eQ'σ]
  exact HC2.conv H.hW (H.PQσ τ) (H.XPσ τ) (H.hrecH j hj hrj Q Q' H.hQ H.hQ' k3 τ)

/-- Composition over the base of a recursive argument, against itself. -/
theorem recKs {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) {k3 : ℕ} (τ : ISub k3 k1) :
    KanH2At S k3 ((Tm.data d (Q.isub ρ)).isub τ) ((Tm.data d (Q.isub ρ)).isub τ)
      ((X.getD j .abort).isub τ) ((X.getD j .abort).isub τ) := by
  have h := H.recK hj hrj τ
  have hQT : HasTy S k3 .one [] ((Tm.data d (Q.isub ρ)).isub τ) (.univ D.level) := HasTy.isubS H.hW H.basic.hqT τ
  have hXQ := RT2.tyCode_r H.hW (H.PQσ τ) (H.XPσ τ)
  rw [← H.eQσ] at hXQ
  have hQQ := RT2.refl' H.hW (H.XPσ τ) (H.PQσ τ)
  rw [← H.eQσ] at hQQ
  have eQ'Q : TyEq S k3 ((Tm.data d (Q'.isub ρ)).isub τ) ((Tm.data d (Q.isub ρ)).isub τ) := by
    rw [H.eQσ, H.eQ'σ]
    exact (Comp2_ty_base (RT2.trans H.hW (RT2.tyCode_r H.hW (H.PQ'σ τ) (H.XPσ τ))
      (RT2.symm H.hW (H.XPσ τ) (H.PQ'σ τ)) (H.PQσ τ))).2.2.2.2.2
  obtain ⟨l', e'⟩ := tyEq_eq H.hW eQ'Q ⟨_, hQT⟩
  exact HC2.self H.hW hQQ (EqTm.refl hQT) e' (H.recU0 hj hrj τ) h


/-- The fillers and the composite of a recursive argument: typing and judgmental equality. -/
theorem recFill {j : ℕ} (hj : j < C.args.length) (hrj : C.isRec j = true) :
    HasTy S (k1 + 1) .one [] ((gFills d D C (Q.isub ρ) φ us X).getD j .abort) (Tm.data d (Q.isub ρ)).dshift ∧
    HasTy S (k1 + 1) .one [] ((gFills d D C (Q'.isub ρ) φ' us' X').getD j .abort) (Tm.data d (Q.isub ρ)).dshift ∧
    EqTm S (k1 + 1) .one [] ((gFills d D C (Q.isub ρ) φ us X).getD j .abort)
      ((gFills d D C (Q'.isub ρ) φ' us' X').getD j .abort) (Tm.data d (Q.isub ρ)).dshift ∧
    HasTy S k1 .one [] (.hcomp (.data d (Q.isub ρ)) φ ((us).getD j .abort) (X.getD j .abort))
      (.data d (Q.isub ρ)) ∧
    EqTm S (k1 + 1) (cof .one φ).shift [] ((us).getD j .abort)
      ((us').getD j .abort) (Tm.data d (Q.isub ρ)).dshift := by
  have hS := sigClosed_of_wfSig H.hW
  have B := H.basic
  have G1 := H.G1
  have G4 := H.G4
  have G1' := H.G1'
  have G4' := H.G4'
  have hXl := H.hXl
  have hXl' := H.hXl'
  have hdq1 : HasTy0 S (k1 + 1) .one [] (.data d (Q.isub ρ).dshift) (.univ D.level) :=
    HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal H.hW B.hqT)
  have H1 := PD.of H.hW H.hD H.hH hdq1
  have hdq1' : HasTy0 S (k1 + 1) .one [] (.data d (Q'.isub ρ).dshift) (.univ D.level) :=
    HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal H.hW B.hq'T)
  have H1' := PD.of H.hW H.hD H.hH hdq1'
  have Hq := PD.of H.hW H.hD H.hH (spec_to_minimal H.hW B.hqT)
  have Hq' := PD.of H.hW H.hD H.hH (spec_to_minimal H.hW B.hq'T)
  -- left
  have hu : HasTy0 S (k1 + 1) (cof .one φ).shift [] ((us).getD j .abort)
      (Tm.data d (Q.isub ρ)).dshift := by
    have := tele_getD G1 (by simp [H.hul]; exact hj) (argTys_get hj)
    rwa [argTy_rec_inst hrj H1.hpsL H1.hpl (by simp [H.hul]; omega)] at this
  have hu0 : HasTy0 S k1 .one [] (X.getD j .abort) (.data d (Q.isub ρ)) := by
    have := tele_getD B.hXq (by omega) (argTys_get hj)
    rwa [argTy_rec_inst hrj Hq.hpsL Hq.hpl (by simp; omega)] at this
  have hside : EqTm0 S k1 (cof .one φ) [] (((us).getD j .abort).dinst .zero)
      (X.getD j .abort) (.data d (Q.isub ρ)) := by
    have := G4 j (by omega)
    rw [argTy_rec_inst hrj Hq.hpsL Hq.hpl (by simp; omega), ← getD_eq_get (by omega)] at this
    exact this
  -- right
  have hu' : HasTy0 S (k1 + 1) (cof .one φ').shift [] ((us').getD j .abort)
      (Tm.data d (Q'.isub ρ)).dshift := by
    have := tele_getD G1' (by simp [H.hul']; exact hj) (argTys_get hj)
    rwa [argTy_rec_inst hrj H1'.hpsL H1'.hpl (by simp [H.hul']; omega)] at this
  have hu0' : HasTy0 S k1 .one [] (X'.getD j .abort) (.data d (Q'.isub ρ)) := by
    have := tele_getD B.hXq' (by omega) (argTys_get hj)
    rwa [argTy_rec_inst hrj Hq'.hpsL Hq'.hpl (by simp; omega)] at this
  have hside' : EqTm0 S k1 (cof .one φ') [] (((us').getD j .abort).dinst .zero)
      (X'.getD j .abort) (.data d (Q'.isub ρ)) := by
    have := G4' j (by omega)
    rw [argTy_rec_inst hrj Hq'.hpsL Hq'.hpl (by simp; omega), ← getD_eq_get (by omega)] at this
    exact this
  have hA := spec_to_minimal H.hW B.hqT
  have hA' := spec_to_minimal H.hW B.hq'T
  have hF := (hfill_typed hS hA B.hφs hu hu0 hside).1
  have hF' := (hfill_typed hS hA' B.hφs' hu' hu0' hside').1
  -- the types
  have eQ'Q : TyEq S k1 (.data d (Q'.isub ρ)) (.data d (Q.isub ρ)) :=
    (Comp2_ty_base (RT2.trans H.hW (RT2.tyCode_r H.hW B.hPQ' (tyCode_of_univ H.hW B.hpT))
      (RT2.symm H.hW (tyCode_of_univ H.hW B.hpT) B.hPQ') B.hPQ)).2.2.2.2.2
  obtain ⟨l1, e1⟩ := tyEq_eq H.hW eQ'Q ⟨_, B.hqT⟩
  have e10 := spec_to_minimal_eq H.hW e1
  have hF'L : HasTy0 S (k1 + 1) .one [] (Tm.hfill (.data d (Q'.isub ρ)) φ' ((us').getD j .abort)
      (X'.getD j .abort)) (Tm.data d (Q.isub ρ)).dshift :=
    HasTy0.conv hF' (EqTm0.dwk hS (Φ := .one) (Γ := []) e10)
  have huu : EqTm0 S (k1 + 1) (cof .one φ).shift [] ((us).getD j .abort)
      ((us').getD j .abort) (Tm.data d (Q.isub ρ)).dshift := by
    have := H.euu j hj
    rwa [argTy_rec_inst hrj H1.hpsL H1.hpl (by simp [H.hul]; omega)] at this
  have hv0 : EqTm0 S k1 .one [] (X.getD j .abort) (X'.getD j .abort) (.data d (Q.isub ρ)) := by
    have := (RE2.typed (H.recU0 hj hrj (ISub.id k1))).2.2
    rw [H.eQσ, ISub.comp_id, isub_id_of_closed (H.X_closed hj)] at this
    have hX' : (X'.getD j .abort).closedB 0 k1 = true := closed_ty hu0'
    rw [isub_id_of_closed hX'] at this
    exact spec_to_minimal_eq H.hW this
  have eF := hfill_cong H.hW hF hF'L (.inr ⟨_, EqTm0.symm e10⟩) huu hv0 H.h12 H.h21
  rw [fills_get_rec _ _ _ _ hj hrj, fills_get_rec _ _ _ _ hj hrj]
  exact ⟨minimal_to_spec hF, minimal_to_spec hF'L, minimal_to_spec_eq eF,
    minimal_to_spec (HasTy0.hcomp hA B.hφs hu hu0 hside), minimal_to_spec_eq huu⟩


end HCG

end

end Model.Whnf
