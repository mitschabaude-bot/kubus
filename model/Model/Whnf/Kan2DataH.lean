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

end

end Model.Whnf
