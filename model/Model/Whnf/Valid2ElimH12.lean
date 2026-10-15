import Model.Whnf.Valid2ElimH11

/-!
# Boundary coherence for higher inductive eliminator fillers

The formal composition clause stores each tube's agreement with its own base. Together with the
paired tube and base relations, this supplies the cross boundaries required by the filler relation.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ} (hW : WfSig S)
include hW

/-- Pointwise related tubes are related at equal interval points. -/
theorem TubeD.toTube2 {A X X' u u' a a' : Tm} {φ φ' : I}
    (hA : RT2 S k A A) (h12 : I.Entails φ φ')
    (ht : HasTy S k .one [] (.hcomp X φ u a) A)
    (ht' : HasTy S k .one [] (.hcomp X' φ' u' a') A)
    (hu : TubeD S k A φ u u') : Tube2 S k A φ u u' := by
  intro k' σ r r' hr hr' he hh
  have hs := (gen_hcomp (spec_to_minimal hW ht) rfl).choose_spec.1.2.1
  have hs' := (gen_hcomp (spec_to_minimal hW ht') rfl).choose_spec.1.2.1
  have hh' : (ival (idEnv k') (φ'.subst σ.τ)).holds :=
    (holds_iff_entails (I.scoped_subst hs' σ.sc)).2
      (ent_trans ((holds_iff_entails (I.scoped_subst hs σ.sc)).1 hh) (ent_subst h12 _))
  exact RE2_near hW (RT2.isub hW (tyCode_of_ty hW ht) hA σ) (hu k' σ r hr hh)
    ((TmNear.refl _).dinst he)
    (hcomp_tube_typed' hW (u := u'.isub σ.up) (HasTy.isubS hW ht' σ) r' hr' hh')

/-- Each side's boundary, paired bases and paired tubes give both cross boundary relations. -/
theorem hcompBnd_cross {A u u' a a' : Tm} {φ φ' : I}
    (hA : RT2 S k A A) (hs : φ.Scoped k) (hs' : φ'.Scoped k) (h12 : I.Entails φ φ')
    (ha : RE2 S k A a a') (hb : HcompBnd2 S k A φ u a) (hb' : HcompBnd2 S k A φ' u' a') :
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ)) ∧
    (∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) := by
  have hT := fun {k'} (σ : ISub k' k) => RT2.isub hW (RE2.tyCode hW ha) hA σ
  refine ⟨fun k' σ hh => RE2.trans hW (hT σ) (hb k' σ hh) (RE2.isub hW ha σ), ?_⟩
  intro k' σ hh
  have hh' : (ival (idEnv k') (φ'.subst σ.τ)).holds :=
    (holds_iff_entails (I.scoped_subst hs' σ.sc)).2
      (ent_trans ((holds_iff_entails (I.scoped_subst hs σ.sc)).1 hh) (ent_subst h12 _))
  exact RE2.trans hW (hT σ) (RE2.isub hW ha σ) (RE2.symm hW (hT σ) (hb' k' σ hh'))

/-- The code's own Kan operations relate fillers using the stored composition boundaries. -/
theorem hfill_rel_code {A A' u u' a a' : Tm} {φ φ' : I} {l : ℕ}
    (hA : HasTy S k .one [] A (.univ l)) (hAA' : RT2 S k A A')
    (hK : KanP2 S k (semK S k A)) (hs : φ.Scoped k) (hs' : φ'.Scoped k)
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift)
    (ht : HasTy S (k + 1) .one [] (Tm.hfill A φ u a) A.dshift)
    (ht' : HasTy S (k + 1) .one [] (Tm.hfill A' φ' u' a') A.dshift)
    (he : EqTm S (k + 1) .one [] (Tm.hfill A φ u a) (Tm.hfill A' φ' u' a') A.dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (hu : Tube2 S k A φ u u')
    (ha : RE2 S k A a a') (hb : HcompBnd2 S k A φ u a) (hb' : HcompBnd2 S k A φ' u' a')
    {k' : ℕ} (σ σ' : ISub k' (k + 1)) (et : σ.tail = σ'.tail) (e0 : I.Eq (σ.τ 0) (σ'.τ 0)) :
    RE2 S k' (A.dshift.isub σ) ((Tm.hfill A φ u a).isub σ) ((Tm.hfill A' φ' u' a').isub σ') := by
  have hX := tyCode_of_univ hW hA
  have hAA := RT2.refl hW hX hAA'
  obtain ⟨hbd, hbd'⟩ := hcompBnd_cross hW hAA hs hs' h12 ha hb hb'
  exact hfill_rel hW hs (fun k3 τ => (hK.isub hW hA τ).1 k3 (Hom.id k3) _ _
    (RT2.isub hW hX hAA' τ)) hAA (Comp2_ty_base hAA').2.2.2.2.2 hteq ht ht' he
    h12 h21 hu ha hbd hbd' σ σ' et e0

end

end Model.Whnf
