import Model.Whnf.Kan2DataTFill

/-!
# Transport at inductive types with parameters: reduction

Transport along a literal line of inductive types with parameters reduces its base, and then
computes on a constructor by `transpCon` (`step_transp_con`, `transpCon_eq`). Its contractum's
arguments are the transports along the argument lines `Meta.tLine` (`tOuts`), and they commute with
restriction (`tOuts_isub`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

/-- The arguments of the `transpCon` contractum. -/
def tOuts (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) : List Tm :=
  (List.range C.args.length).map fun j =>
    Tm.transp (Meta.tLine (C.argTy d D.params.length) ps.toList φ X j) φ (X.getD j .abort)

/-- The contractum of `transpCon`, at a constructor with interval arguments `rs`. -/
def tConR (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) (rs : List I) : Tm :=
  .con d c (ps.dinst .one) (Tm.ofList (tOuts d D C ps φ X)) rs

/-- The contractum of `transpCon`. -/
abbrev tCon (d : ℕ) (D : DataDecl) (c : ℕ) (C : Ctor) (ps : Tm) (φ : I) (X : List Tm) : Tm :=
  tConR d D c C ps φ X []

theorem transpTele_tOuts (d : ℕ) (D : DataDecl) (C : Ctor) (ps : Tm) (φ : I) {X : List Tm}
    (hXl : X.length = C.args.length) :
    Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] X = tOuts d D C ps φ X := by
  have heq := Meta.transpTele_eq (C.argTy d D.params.length) ps.toList φ X X 0 rfl
  simp only [hXl, ← List.range_eq_range'] at heq
  rw [show ([] : List Tm) = (Meta.tFills (C.argTy d D.params.length) ps.toList φ X 0).reverse from rfl, heq]
  rfl

section red
variable {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ [])
include hD hp

theorem step_transp_base {ps a a' : Tm} {φ : I} (hn : ¬ I.Entails .one φ) (ha : step S a = some a') :
    step S (.transp (.data d ps) φ a) = some (.transp (.data d ps) φ a') := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn', hD, hp, ha]

theorem red_transp_base {ps a a' : Tm} {φ : I} (hn : ¬ I.Entails .one φ) (h : Red S a a') :
    Red S (.transp (.data d ps) φ a) (.transp (.data d ps) φ a') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (step_transp_base hD hp hn hs) ih

/-- `transpCon` as a step. -/
theorem step_transp_con (hH : D.isHIT = false) {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps qs : Tm}
    {φ : I} (hn : ¬ I.Entails .one φ) {X : List Tm} (hXl : X.length = C.args.length) :
    step S (.transp (.data d ps) φ (.con d c qs (Tm.ofList X) [])) = some (tCon d D c C ps φ X) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  simp [step, hn', hD, hp, hC, toList_ofList, (nonHIT_ctor hH hC).2, firstBnd, tCon, tConR,
    transpTele_tOuts d D C ps φ hXl]

/-- `transpCon` as a step, at a normal constructor with interval arguments. -/
theorem step_transp_conR {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps qs : Tm} {rs : List I}
    {φ : I} (hn : ¬ I.Entails .one φ) {X : List Tm} (hXl : X.length = C.args.length)
    (hcs : step S (.con d c qs (Tm.ofList X) rs) = none) :
    step S (.transp (.data d ps) φ (.con d c qs (Tm.ofList X) rs)) = some (tConR d D c C ps φ X rs) := by
  have hn' : I.entails .one φ = false := by simpa [I.Entails] using hn
  have hfb : firstBnd C.bnd rs = none := by
    have := hcs; simp [step, hD, hC] at this; exact this
  simp [step, hn', hD, hp, hC, hfb, toList_ofList, tConR, transpTele_tOuts d D C ps φ hXl]

end red

section eq
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ [])
  (hH : D.isHIT = false)
include hW hD hp hH

/-- `transpCon` as a judgmental equality, and the arguments' telescope at the start of the line. -/
theorem transpCon_eq {ps qs T : Tm} {φ : I} {c : ℕ} {C : Ctor} {X : List Tm} (hC : D.ctors[c]? = some C)
    (hty : HasTy S k .one [] (.transp (.data d ps) φ (.con d c qs (Tm.ofList X) [])) T) :
    EqTm S k .one [] (.transp (.data d ps) φ (.con d c qs (Tm.ofList X) [])) (tCon d D c C ps φ X) T ∧
    HasTele0 S k .one [] (Tm.ofList X) (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse ∧
    X.length = C.args.length := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l0, ⟨hLt, hφ, hc, hb0⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  obtain ⟨D', hD', hPt⟩ := gen_data_tele hLt rfl
  rw [hD] at hD'; cases hD'
  have hPl : ps = Tm.ofList ps.toList := tele_isList hPt
  have hw : Wf0 S k .one [] := Wf0.nil trivial
  have hP0t : HasTele0 S k .one [] (ps.dinst .zero) D.params [] := by
    have := HasTele0.post (I.inst0 .zero) hw (fun t B h => HasTy0.dsubst hS h (r := .zero) trivial) hPt
      (params_closed hS hD)
    simpa using this
  have hd0 : HasTy S k .one [] (.data d (ps.dinst .zero)) (.univ D.level) :=
    minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hP0t)
  obtain ⟨htp, -, -, hXl⟩ := con_retype hW hD hH hC (EqTm.refl (minimal_to_spec hb0)) (TyEq.refl _) hd0
  have eT := EqTm.transpCon hD hp hC hPl (by rw [toList_ofList]) (toFull_tele htp) hty
  rw [toList_ofList, transpTele_tOuts d D C ps φ hXl] at eT
  exact ⟨eT, htp, hXl⟩

end eq

section eqR
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D)) (hp : D.params ≠ [])
include hW hD hp

/-- `transpCon` as a judgmental equality at a constructor with interval arguments. -/
theorem transpCon_eqR {ps qs T : Tm} {φ : I} {c : ℕ} {C : Ctor} {X : List Tm} {rs : List I}
    (hC : D.ctors[c]? = some C)
    (hty : HasTy S k .one [] (.transp (.data d ps) φ (.con d c qs (Tm.ofList X) rs)) T) :
    EqTm S k .one [] (.transp (.data d ps) φ (.con d c qs (Tm.ofList X) rs)) (tConR d D c C ps φ X rs) T ∧
    HasTele0 S k .one [] (Tm.ofList X) (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse ∧
    X.length = C.args.length ∧ rs.length = C.dims := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l0, ⟨hLt, hφ, hc, hb0⟩, -⟩ := gen_transpF (spec_to_minimal hW hty) rfl
  obtain ⟨D', hD', hPt⟩ := gen_data_tele hLt rfl
  rw [hD] at hD'; cases hD'
  have hPl : ps = Tm.ofList ps.toList := tele_isList hPt
  have hw : Wf0 S k .one [] := Wf0.nil trivial
  have hP0t : HasTele0 S k .one [] (ps.dinst .zero) D.params [] := by
    have := HasTele0.post (I.inst0 .zero) hw (fun t B h => HasTy0.dsubst hS h (r := .zero) trivial) hPt
      (params_closed hS hD)
    simpa using this
  have hd0 : HasTy0 S k .one [] (.data d (ps.dinst .zero)) (.univ D.level) := HasTy0.data hD (hW.2 d D hD).1 hP0t
  obtain ⟨D0, C0, hD0, hC0, -, -, htp, hrs, -⟩ := con_args hW hb0 hd0
  rw [hD] at hD0; cases hD0; rw [hC] at hC0; cases hC0
  have hXl : X.length = C.args.length := by
    have := Meta.tele_length htp; rwa [toList_ofList, argTys_length] at this
  have eT := EqTm.transpCon hD hp hC hPl (by rw [toList_ofList]) (toFull_tele htp) hty
  rw [toList_ofList, transpTele_tOuts d D C ps φ hXl] at eT
  exact ⟨eT, htp, hXl, hrs⟩

end eqR

section comm
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- The arguments of the `transpCon` contractum, restricted. -/
theorem tOuts_isub {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps : Tm} {φ : I} {X : List Tm}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (hXl : X.length = C.args.length)
    (κ : ISub k' k) :
    (tOuts d D C ps φ X).map (·.isub κ) = tOuts d D C (ps.isub κ.up) (φ.subst κ.τ) (X.map (·.isub κ)) := by
  have hS := sigClosed_of_wfSig hW
  rw [← transpTele_tOuts d D C ps φ hXl, ← transpTele_tOuts d D C _ _ (by simp [hXl])]
  have := transpTele_subst (σ := Tm.var) (τ := κ.τ) (argTy := C.argTy d D.params.length)
    (np := D.params.length) (fun j => argTy_closed hS hD hC j) hpl φ X 0 [] rfl
  simp only [show (dupS Tm.var : ℕ → Tm) = Tm.var from funext fun n => rfl] at this
  show (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] X).map (·.subst Tm.var κ.τ) = _
  rw [this, ← toList_subst hps]
  rfl

/-- The `transpCon` contractum, restricted. -/
theorem tCon_isub {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps : Tm} {φ : I} {X : List Tm}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (hXl : X.length = C.args.length)
    (κ : ISub k' k) :
    (tCon d D c C ps φ X).isub κ = tCon d D c C (ps.isub κ.up) (φ.subst κ.τ) (X.map (·.isub κ)) := by
  show Tm.con d c ((ps.dinst .one).isub κ) ((Tm.ofList (tOuts d D C ps φ X)).isub κ) [] = _
  rw [ofList_isub, tOuts_isub hW hD hC hps hpl hXl κ, isub_dinst]
  rfl

/-- The `transpCon` contractum at a constructor with interval arguments, restricted. -/
theorem tConR_isub {c : ℕ} {C : Ctor} (hC : D.ctors[c]? = some C) {ps : Tm} {φ : I} {X : List Tm} {rs : List I}
    (hps : IsList ps) (hpl : ps.toList.length = D.params.length) (hXl : X.length = C.args.length)
    (κ : ISub k' k) :
    (tConR d D c C ps φ X rs).isub κ =
      tConR d D c C (ps.isub κ.up) (φ.subst κ.τ) (X.map (·.isub κ)) (rs.map (·.subst κ.τ)) := by
  show Tm.con d c ((ps.dinst .one).isub κ) ((Tm.ofList (tOuts d D C ps φ X)).isub κ) _ = _
  rw [ofList_isub, tOuts_isub hW hD hC hps hpl hXl κ, isub_dinst]
  rfl

end comm

end

end Model.Whnf
