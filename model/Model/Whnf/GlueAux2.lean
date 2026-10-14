import Model.Whnf.Equiv2
import Model.Whnf.Local
import Model.Whnf.Sound
import Model.Whnf.Data2

/-!
# Auxiliary facts for the binary relation of Glue types
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' m : ℕ}

variable (hW : WfSig S)
include hW

omit hW in
/-- The family of the relations of a code at the restrictions of a restriction. -/
theorem famOK_comp2 {n0 n : ℕ} {X : V} (hX : PER2 S m X) (krX : KR2 S m X) (f : Hom n0 m) (ρ : ISub n n0) :
    FamOK S n (fun k3 σ3 => Comp2 S X m k3 (f.comp (ρ.comp σ3).hom)) where
  per k3 σ3 := hX k3 _
  kr k3 σ3 k4 σ4 Y Y' h := by
    have := (krX k3 _ k4 σ4 Y Y' Y Y).1 h
    rwa [ISub.comp_hom, ISub.comp_assoc] at this
  krEl k3 σ3 k4 σ4 Y t t' h := by
    have := (krX k3 _ k4 σ4 Y Y t t').2 h
    rwa [ISub.comp_hom, ISub.comp_assoc] at this
  tyEq k3 σ3 Y Y' h := (Comp2_ty_base h).2.2.2.2.2
  isTy k3 σ3 Y Y' h := ⟨(Comp2_ty_base h).2.1, (Comp2_ty_base h).2.2.1⟩
  elEB k3 σ3 Y t t' h := (Comp2_el h).1

/-- Equal types at the top universe. -/
theorem eqTop {X X' : Tm} {l : ℕ} (h : TyEq S k X X') (hX : HasTy S k .one [] X (.univ l)) :
    EqTm S k .one [] X X' (.univ maxLevel) := by
  rcases h with rfl | ⟨m', e⟩
  · exact minimal_to_spec_eq ((EqTm0.refl (spec_to_minimal hW hX)).lift (lvl_bound hW (spec_to_minimal hW hX))
      le_rfl)
  · exact minimal_to_spec_eq ((spec_to_minimal_eq hW e).lift (lvl_bound_eq hW (spec_to_minimal_eq hW e)) le_rfl)

/-- The parts of a type whose normal form is a Glue type. -/
theorem glue_parts {X A1 T1 e1 : Tm} {φ1 : I} (h : RedT S k X (.glue A1 φ1 T1 e1)) (hX : IsTyK S k X) :
    ∃ l, HasTy S k .one [] A1 (.univ l) ∧ φ1.Scoped k ∧ HasTy S k (cof .one φ1) [] T1 (.univ l) ∧
      HasTy S k (cof .one φ1) [] e1 (Tm.equiv T1 A1) := by
  obtain ⟨l, hg | he⟩ := hX.of_tyEq h.2
  · obtain ⟨l', ⟨h1, h2, h3, h4⟩, -⟩ := gen_glue (sigClosed_of_wfSig hW) (spec_to_minimal hW hg) rfl
    exact ⟨l', minimal_to_spec h1, h2, minimal_to_spec h3, minimal_to_spec h4⟩
  · cases he

/-- A term over a face, at a restriction where the face holds. -/
theorem face_ty {φ : I} (hφ : φ.Scoped k) {t X : Tm} (ht : HasTy S k (cof .one φ) [] t X) (σ : ISub k' k)
    (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) : HasTy S k' .one [] (t.isub σ) (X.isub σ) := by
  have := HasTy.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφ⟩) ht σ
  exact HasTy.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds (I.scoped_subst hφ σ.sc) hh)) this

theorem face_eq {φ : I} (hφ : φ.Scoped k) {t u X : Tm} (ht : EqTm S k (cof .one φ) [] t u X) (σ : ISub k' k)
    (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) : EqTm S k' .one [] (t.isub σ) (u.isub σ) (X.isub σ) := by
  have := EqTm.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφ⟩) ht σ
  exact EqTm.restrict (Φ' := .one) trivial (ent_cof_one hW (entails_of_holds (I.scoped_subst hφ σ.sc) hh)) this

omit hW in
/-- The family of the relations of a code at its restrictions. -/
theorem famOK_comp2_id {n : ℕ} {X : V} (hX : PER2 S n X) (krX : KR2 S n X) :
    FamOK S n (fun k3 σ3 => Comp2 S X n k3 σ3.hom) where
  per k3 σ3 := hX k3 _
  kr k3 σ3 k4 σ4 Y Y' h := by have := (krX k3 σ3.hom k4 σ4 Y Y' Y Y).1 h; rwa [← ISub.hom_comp] at this
  krEl k3 σ3 k4 σ4 Y t t' h := by have := (krX k3 σ3.hom k4 σ4 Y Y t t').2 h; rwa [← ISub.hom_comp] at this
  tyEq k3 σ3 Y Y' h := (Comp2_ty_base h).2.2.2.2.2
  isTy k3 σ3 Y Y' h := ⟨(Comp2_ty_base h).2.1, (Comp2_ty_base h).2.2.1⟩
  elEB k3 σ3 Y t t' h := (Comp2_el h).1

omit hW in
/-- A cofibration whose face is a restriction holds where that restriction holds. -/
theorem holds_of_face {k'' : ℕ} {φ1 : I} {ψ : Cof k'} (hf : (ival (idEnv k') φ1).face = ψ) (σ' : ISub k'' k')
    (h : (ψ.restr σ'.hom).holds) : (ival (idEnv k'') (φ1.subst σ'.τ)).holds := by
  rw [DM.holds_iff_face_holds, face_isub hf σ']; exact h

omit hW in
theorem face_of_holds {k'' : ℕ} {φ1 : I} {ψ : Cof k'} (hf : (ival (idEnv k') φ1).face = ψ) (σ' : ISub k'' k')
    (h : (ival (idEnv k'') (φ1.subst σ'.τ)).holds) : (ψ.restr σ'.hom).holds := by
  rw [DM.holds_iff_face_holds, face_isub hf σ'] at h; exact h

/-- The type of the equivalence of a Glue type, under its face, at the top universe. -/
theorem equiv_ty_cof {φ1 : I} (hs : φ1.Scoped k) {A1 T1 : Tm} {l : ℕ} (hA1 : HasTy S k .one [] A1 (.univ l))
    (hT1 : HasTy S k (cof .one φ1) [] T1 (.univ l)) :
    HasTy S k (cof .one φ1) [] (Tm.equiv T1 A1) (.univ maxLevel) := by
  have hS := sigClosed_of_wfSig hW
  have hA1' := HasTy0.restrict (show (cof .one φ1).Scoped k from ⟨trivial, hs⟩) (ent_and_left _ _)
    (spec_to_minimal hW hA1)
  have h := equiv_typed hS (spec_to_minimal hW hT1) hA1'
  exact minimal_to_spec (h.lift (lvl_bound hW h) le_rfl)

end

end Model.Whnf
