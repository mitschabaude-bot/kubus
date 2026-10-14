import Model.Whnf.NearAll
import Model.Whnf.Bridge

/-!
# Near invariance at equivalence types

`RE2_equiv_near`: related equivalences stay related when the right one is replaced by a near typed
term, through the pack `equivF` (`goodP_equivF`, `equivF_ni`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k : ℕ} (hW : WfSig S)
include hW

theorem RE2_equiv_near {T A e e' e'' : Tm} {lT lA : ℕ} (hT : HasTy S k .one [] T (.univ lT))
    (hA : HasTy S k .one [] A (.univ lA)) (hTT : RT2 S k T T) (hAA : RT2 S k A A)
    (h : RE2 S k (Tm.equiv T A) e e') (hn : TmNear e' e'') (hu : HasTy S k .one [] e'' (Tm.equiv T A)) :
    RE2 S k (Tm.equiv T A) e e'' := by
  have hT' := hT.cumulTo (lvl_of_ty hW hT) le_rfl
  have hA' := hA.cumulTo (lvl_of_ty hW hA) le_rfl
  have hXT := tyCode_of_univ hW hT
  have hXA := tyCode_of_univ hW hA
  have FT := famOK_comp2_id (per2_tyCode hW hXT) (kr2_tyCode hW hXT)
  have FA := famOK_comp2_id (per2_tyCode hW hXA) (kr2_tyCode hW hXA)
  have NT := famNI_comp2_id (ni2_tyCode hW hXT)
  have NA := famNI_comp2_id (ni2_tyCode hW hXA)
  obtain ⟨lE, hE | hE⟩ := isTyK_of_ty hW hu
  swap; · cases hE
  have G := goodP_equivF hW hE (goodP_comp hW hT) (goodP_comp hW hA)
  have hcE := closed_of_ty hW hE
  have hrefl := equivF_ty hW FT FA (EqTm.refl hT') (EqTm.refl hA')
    (by show (Comp2 S _ k k (ISub.id k).hom).ty T T; rw [ISub.hom_id]; exact hTT)
    (by show (Comp2 S _ k k (ISub.id k).hom).ty A A; rw [ISub.hom_id]; exact hAA)
  have h1 := (G k (ISub.id k) e e').2 (by rw [isub_id_of_closed hcE]; exact h)
  rw [isub_id_of_closed hcE] at h1
  have h2 := equivF_ni hW FT FA NT NA k (ISub.id k) _ _ _ _ ((equivF_ok hW _ _ FT FA).per _ _ |>.reflTy hrefl) h1 hn hu
  have := (G k (ISub.id k) e e'').1 (by rw [isub_id_of_closed hcE]; exact h2)
  rwa [isub_id_of_closed hcE] at this

/-- Equal types, at the top universe. -/
theorem tyEq_top {X X' : Tm} {l : ℕ} (hX : HasTy S k .one [] X (.univ l)) (e : TyEq S k X X') :
    EqTm S k .one [] X X' (.univ maxLevel) := by
  rcases e with rfl | ⟨l', e⟩
  · exact EqTm.refl (hX.cumulTo (lvl_of_ty hW hX) le_rfl)
  · exact e.cumulTo (lvl_of_ty hW (HasTy.eqL e)) le_rfl

theorem equiv_tyEq {T T' A A' : Tm} {lT lA : ℕ} (hT : HasTy S k .one [] T (.univ lT))
    (hA : HasTy S k .one [] A (.univ lA)) (eT : TyEq S k T T') (eA : TyEq S k A A') :
    TyEq S k (Tm.equiv T A) (Tm.equiv T' A') :=
  .inr ⟨maxLevel, equiv_congrS hW (tyEq_top hW hT eT) (tyEq_top hW hA eA)⟩

end

end Model.Whnf
