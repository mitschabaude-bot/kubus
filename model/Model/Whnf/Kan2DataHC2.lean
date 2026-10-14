import Model.Whnf.Kan2DataHC

/-!
# Composition of related constructors: the fillers of the arguments

The fillers of the arguments of the `hcompCon` contracta are related along their lines, by
induction along the arguments (`HCC.inv`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

/-- The argument type `i` at the restrictions of the first fillers, at the point `r`. -/
def argTyAt (d : ℕ) (D : DataDecl) (C : Ctor) (F : List Tm) (Q : Tm) {K k1 : ℕ} (ρ : ISub k1 K) (i : ℕ) {k3 : ℕ}
    (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3) : Tm :=
  (C.argTy d D.params.length i).substList (((F.map (·.isub (ISub.cons r hr τ))).take i).reverse ++
    (Q.isub (ρ.comp τ)).toList.reverse)

namespace HCC

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {qs qs' : Tm} {X X' : List Tm} {φ φ' : I} {u u' : Tm}
  (H : HCC S d D K P Q Q' k1 ρ c C qs qs' X X' φ φ' u u')
include H

omit H in
theorem fills_len (q : Tm) (φ : I) (u : Tm) (X : List Tm) : (conFills d D c C q φ u X).length = C.args.length :=
  Meta.hFills_length _ _ _ _ _ _ _ _

omit H in
theorem fills_take (q : Tm) (φ : I) (u : Tm) (X : List Tm) {j : ℕ} (hj : j ≤ C.args.length) :
    (conFills d D c C q φ u X).take j =
      Meta.hFills C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ (tubeArgs d D c C q u) X j := by
  have := Meta.hFills_take C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ (tubeArgs d D c C q u) X j
    (C.args.length - j)
  rwa [show j + (C.args.length - j) = C.args.length by omega] at this

omit H in
theorem fills_get (q : Tm) (φ : I) (u : Tm) (X : List Tm) {j : ℕ} (hj : j < C.args.length) :
    (conFills d D c C q φ u X).getD j .abort =
      Meta.hFill C (C.argTy d D.params.length) (.data d q) q.dshift.toList φ (tubeArgs d D c C q u) X j :=
  Meta.hFills_get _ _ _ _ _ _ _ hj

omit H in
theorem line_eq (q : Tm) (φ : I) (u : Tm) (X : List Tm) {j : ℕ} (hj : j ≤ C.args.length) :
    conLine d D c C q φ u X j = (C.argTy d D.params.length j).substList
      (((conFills d D c C q φ u X).take j).reverse ++ q.dshift.toList.reverse) := by
  rw [fills_take q φ u X hj]; rfl

omit H in
theorem fills_get_rec (q : Tm) (φ : I) (u : Tm) (X : List Tm) {j : ℕ} (hj : j < C.args.length)
    (hrj : C.isRec j = true) :
    (conFills d D c C q φ u X).getD j .abort =
      Tm.hfill (.data d q) φ ((tubeArgs d D c C q u).getD j .abort) (X.getD j .abort) := by
  rw [fills_get q φ u X hj]; simp [Meta.hFill, hrj]

omit H in
theorem fills_get_pt (q : Tm) (φ : I) (u : Tm) (X : List Tm) {j : ℕ} (hj : j < C.args.length)
    (hrj : C.isRec j = false) :
    (conFills d D c C q φ u X).getD j .abort =
      Tm.fill (conLine d D c C q φ u X j) φ ((tubeArgs d D c C q u).getD j .abort) (X.getD j .abort) := by
  rw [fills_get q φ u X hj]; simp [Meta.hFill, hrj]; rfl

omit H in
theorem outs_get_rec (q : Tm) (φ : I) (u : Tm) (X : List Tm) {j : ℕ} (hj : j < C.args.length)
    (hrj : C.isRec j = true) :
    (conOuts d D c C q φ u X).getD j .abort =
      Tm.hcomp (.data d q) φ ((tubeArgs d D c C q u).getD j .abort) (X.getD j .abort) := by
  simp [conOuts, List.getD_eq_getElem?_getD, hj, Meta.hOut, hrj]

omit H in
theorem outs_get_pt (q : Tm) (φ : I) (u : Tm) (X : List Tm) {j : ℕ} (hj : j < C.args.length)
    (hrj : C.isRec j = false) :
    (conOuts d D c C q φ u X).getD j .abort =
      Tm.comp (conLine d D c C q φ u X j) φ ((tubeArgs d D c C q u).getD j .abort) (X.getD j .abort) := by
  simp [conOuts, List.getD_eq_getElem?_getD, hj, Meta.hOut, hrj]; rfl

theorem hQρl {k3 : ℕ} (σ : ISub k3 k1) : Q.isub (ρ.comp σ) = Tm.ofList (Q.isub (ρ.comp σ)).toList :=
  (dataLit_rel H.hW H.hD H.hP H.hQ (ρ.comp σ)).2.2.2.2.2.2

theorem hQ'ρl {k3 : ℕ} (σ : ISub k3 k1) : Q'.isub (ρ.comp σ) = Tm.ofList (Q'.isub (ρ.comp σ)).toList :=
  (dataLit_rel H.hW H.hD H.hP H.hQ' (ρ.comp σ)).2.2.2.2.2.2

theorem hQρlen {k3 : ℕ} (σ : ISub k3 k1) : (Q.isub (ρ.comp σ)).toList.length = D.params.length := by
  have := data_len_of H.hW (((Comp2_ty_base H.hQ).2.2.1).isub H.hW (ρ.comp σ)); rwa [dataD_eq H.hW H.hD] at this

theorem hQ'ρlen {k3 : ℕ} (σ : ISub k3 k1) : (Q'.isub (ρ.comp σ)).toList.length = D.params.length := by
  have := data_len_of H.hW (((Comp2_ty_base H.hQ').2.2.1).isub H.hW (ρ.comp σ)); rwa [dataD_eq H.hW H.hD] at this

/-- The left line, restricted. -/
theorem lineσ {j : ℕ} (hj : j ≤ C.args.length) {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) :
    (conLine d D c C (Q.isub ρ) φ u X j).isub (ISub.cons r hr σ) =
      argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j σ r hr := by
  have hS := sigClosed_of_wfSig H.hW
  have hdq1 : HasTy0 S (k1 + 1) .one [] (.data d (Q.isub ρ).dshift) (.univ D.level) :=
    HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal H.hW H.basic.hqT)
  have hl := (PD.of H.hW H.hD H.hH hdq1).hpsL
  rw [line_eq _ φ u X hj, argTy_isub hS H.hD H.hC j _ hl (ISub.cons r hr σ), dshift_isub_cons, Tm.isub_isub]; rfl

/-- The right line, restricted. -/
theorem lineσ' {j : ℕ} (hj : j ≤ C.args.length) {k3 : ℕ} (σ : ISub k3 k1) (r : I) (hr : r.Scoped k3) :
    (conLine d D c C (Q'.isub ρ) φ' u' X' j).isub (ISub.cons r hr σ) =
      argTyAt d D C (conFills d D c C (Q'.isub ρ) φ' u' X') Q' ρ j σ r hr := by
  have hS := sigClosed_of_wfSig H.hW
  have hdq1 : HasTy0 S (k1 + 1) .one [] (.data d (Q'.isub ρ).dshift) (.univ D.level) :=
    HasTy0.dwk hS (Φ := .one) (Γ := []) (spec_to_minimal H.hW H.basic.hq'T)
  have hl := (PD.of H.hW H.hD H.hH hdq1).hpsL
  rw [line_eq _ φ' u' X' hj, argTy_isub hS H.hD H.hC j _ hl (ISub.cons r hr σ), dshift_isub_cons, Tm.isub_isub]; rfl

theorem argTyAt_rec {i : ℕ} (hi : i < C.args.length) (hri : C.isRec i = true) {k3 : ℕ} (τ : ISub k3 k1) (r : I)
    (hr : r.Scoped k3) :
    argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ r hr = .data d (Q.isub (ρ.comp τ)) :=
  argTy_rec_inst hri (H.hQρl τ) (H.hQρlen τ) (by simp [fills_len]; omega)

/-- The argument types at the left fillers against those at other prefixes. -/
theorem toRel {j : ℕ} (hj : j < C.args.length) {k3 : ℕ} (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3) (B : List Tm)
    {Q2 : Tm} (hQ2 : RT2 S K (.data d P) (.data d Q2)) (hBl : B.length = j)
    (h : ∀ i (hi : i < j), RE2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ r hr)
      (((conFills d D c C (Q.isub ρ) φ u X).getD i .abort).isub (ISub.cons r hr τ)) (B.getD i .abort)) :
    RT2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ r hr)
      ((C.argTy d D.params.length j).substList (B.reverse ++ (Q2.isub (ρ.comp τ)).toList.reverse)) := by
  have hrec : ∀ i (hi : i < C.args.length), C.isRec i = true →
      argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ r hr = .data d (Q.isub (ρ.comp τ)) :=
    fun i hi hri => H.argTyAt_rec hi hri τ r hr
  have hFl := fills_len (d := d) (D := D) (c := c) (C := C) (Q.isub ρ) φ u X
  unfold argTyAt at h hrec ⊢
  generalize conFills d D c C (Q.isub ρ) φ u X = F at h hrec hFl ⊢
  refine argTy_rt2 H.hW H.hD H.hP H.hPP H.hQ hQ2 (ρ.comp τ) H.hC hj
    (A := (F.map (·.isub (ISub.cons r hr τ))).take j)
    (B := B) (by simp [hFl]; omega) hBl (fun i hi => ⟨fun hri => ?_, fun hri => ?_⟩)
  · have h1 := h i hi
    rw [hrec i (by omega) hri] at h1
    rw [getD_take_lt hi, getD_map_isub]; exact h1
  · have h1 := h i hi
    rw [getD_take_lt hi, getD_map_isub, List.take_take, Nat.min_eq_left hi.le]; exact h1

end HCC

/-- The invariant along the arguments of the `hcompCon` contracta, at argument `i`: the fillers are
related along their lines, to the tube's projections on its face, to the base at `0` and to the
composite at `1`; the tube's projections are related on the face. -/
def Inv (S : Sig) (d : ℕ) (D : DataDecl) (Q Q' : Tm) {K k1 : ℕ} (ρ : ISub k1 K) (c : ℕ) (C : Ctor) (X X' : List Tm)
    (φ φ' : I) (u u' : Tm) (i : ℕ) : Prop :=
  (∀ k3 (τ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
    RE2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ r hr)
      (((conFills d D c C (Q.isub ρ) φ u X).getD i .abort).isub (ISub.cons r hr τ))
      (((conFills d D c C (Q'.isub ρ) φ' u' X').getD i .abort).isub (ISub.cons r' hr' τ))) ∧
  (∀ k3 (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3), (ival (idEnv k3) (φ.subst τ.τ)).holds →
    RE2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ r hr)
      (((conFills d D c C (Q.isub ρ) φ u X).getD i .abort).isub (ISub.cons r hr τ))
      (((tubeArgs d D c C (Q.isub ρ) u).getD i .abort).isub (ISub.cons r hr τ))) ∧
  (∀ k3 (τ : ISub k3 k1), RE2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ .zero trivial)
      (((conFills d D c C (Q.isub ρ) φ u X).getD i .abort).isub (ISub.cons .zero trivial τ))
      ((X.getD i .abort).isub τ)) ∧
  RE2 S k1 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i (ISub.id k1) .one trivial)
    (((conFills d D c C (Q.isub ρ) φ u X).getD i .abort).isub (ISub.cons .one trivial (ISub.id k1)))
    ((conOuts d D c C (Q.isub ρ) φ u X).getD i .abort) ∧
  (∀ k3 (τ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
    (ival (idEnv k3) (φ.subst τ.τ)).holds →
    RE2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ r hr)
      (((tubeArgs d D c C (Q.isub ρ) u).getD i .abort).isub (ISub.cons r hr τ))
      (((tubeArgs d D c C (Q.isub ρ) u).getD i .abort).isub (ISub.cons r' hr' τ))) ∧
  (∀ k3 (τ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3), I.Eq r r' →
    (ival (idEnv k3) (φ.subst τ.τ)).holds →
    RE2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ i τ r hr)
      (((tubeArgs d D c C (Q.isub ρ) u).getD i .abort).isub (ISub.cons r hr τ))
      (((tubeArgs d D c C (Q'.isub ρ) u').getD i .abort).isub (ISub.cons r' hr' τ)))

namespace HCC

variable {d : ℕ} {D : DataDecl} {K : ℕ} {P Q Q' : Tm} {k1 : ℕ} {ρ : ISub k1 K} {c : ℕ} {C : Ctor}
  {qs qs' : Tm} {X X' : List Tm} {φ φ' : I} {u u' : Tm}
  (H : HCC S d D K P Q Q' k1 ρ c C qs qs' X X' φ φ' u u')
include H

/-- The line of argument `j`, against the right one. -/
theorem relLine {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i)
    {k3 : ℕ} (τ : ISub k3 k1) (r r' : I) (hr : r.Scoped k3) (hr' : r'.Scoped k3) (hE : I.Eq r r') :
    RT2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ r hr)
      (argTyAt d D C (conFills d D c C (Q'.isub ρ) φ' u' X') Q' ρ j τ r' hr') := by
  refine H.toRel hj τ r hr _ H.hQ' (by simp [fills_len]; omega) fun i hi => ?_
  rw [getD_take_lt hi, getD_map_isub]
  exact (hV i hi).1 k3 τ r r' hr hr' hE

/-- The line of argument `j`, against the type at the tube's projections. -/
theorem relFU {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i)
    {k3 : ℕ} (τ : ISub k3 k1) (r : I) (hr : r.Scoped k3) (hh : (ival (idEnv k3) (φ.subst τ.τ)).holds) :
    RT2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ r hr)
      ((C.argTy d D.params.length j).substList ((((tubeArgs d D c C (Q.isub ρ) u).map
        (·.isub (ISub.cons r hr τ))).take j).reverse ++ (Q.isub (ρ.comp τ)).toList.reverse)) := by
  refine H.toRel hj τ r hr _ H.hQ (by simp [tubeArgs]; omega) fun i hi => ?_
  rw [getD_take_lt hi, getD_map_isub]
  exact (hV i hi).2.1 k3 τ r hr hh

/-- The line of argument `j` at `0`, against the type at the base. -/
theorem relFX {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i)
    {k3 : ℕ} (τ : ISub k3 k1) :
    RT2 S k3 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j τ .zero trivial)
      ((C.argTy d D.params.length j).substList (((X.map (·.isub τ)).take j).reverse ++
        (P.isub (ρ.comp τ)).toList.reverse)) := by
  refine H.toRel hj τ .zero trivial _ H.hPP (by simp [H.hXl]; omega) fun i hi => ?_
  rw [getD_take_lt hi, getD_map_isub]
  exact (hV i hi).2.2.1 k3 τ

/-- The line of argument `j` at `1`, against the type at the composites. -/
theorem relFY {j : ℕ} (hj : j < C.args.length) (hV : ∀ i, i < j → Inv S d D Q Q' ρ c C X X' φ φ' u u' i) :
    RT2 S k1 (argTyAt d D C (conFills d D c C (Q.isub ρ) φ u X) Q ρ j (ISub.id k1) .one trivial)
      ((C.argTy d D.params.length j).substList (((conOuts d D c C (Q.isub ρ) φ u X).take j).reverse ++
        (P.isub ρ).toList.reverse)) := by
  have := H.toRel hj (ISub.id k1) .one trivial ((conOuts d D c C (Q.isub ρ) φ u X).take j) H.hPP
    (by simp [conOuts]; omega) fun i hi => by rw [getD_take_lt hi]; exact (hV i hi).2.2.2.1
  rwa [ISub.comp_id] at this

end HCC

end

end Model.Whnf
