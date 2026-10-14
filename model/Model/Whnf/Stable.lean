import Model.Whnf.Bridge

/-!
# Expansion along steps that are stable under restriction

If every restriction of `t` reduces to the corresponding restriction of `u`, then `t` is related
wherever `u` is. This is head expansion (`HE2`) with the reducts given by `u` and its Kripke
restrictions.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

variable (hW : WfSig S)
include hW

theorem ty_expandS {X : V} (hX : TyCode k X) {A A' B : Tm} (hA : IsTyK S k A) (hA' : IsTyK S k A')
    (hs : StableT S k A B) (h : (Comp2 S X k k (Hom.id k)).ty B A') : (Comp2 S X k k (Hom.id k)).ty A A' :=
  (he2_tyCode hW hX k (Hom.id k) A A' A A).1 hA hA' fun k' σ =>
    ⟨B.isub σ, (hs k' σ).1, (hs k' σ).2, ((kr2_tyCode hW hX) k (Hom.id k) k' σ B A' B B).1 h⟩

theorem ty_expandSR {X : V} (hX : TyCode k X) {A A' B' : Tm} (hA : IsTyK S k A) (hA' : IsTyK S k A')
    (hs : StableT S k A' B') (h : (Comp2 S X k k (Hom.id k)).ty A B') : (Comp2 S X k k (Hom.id k)).ty A A' := by
  have P := per2_tyCode hW hX k (Hom.id k)
  exact P.symTy (ty_expandS hW hX hA' hA hs (P.symTy h))

theorem el_expandS {X : V} (hX : TyCode k X) {A t t' u : Tm} (hAA : (Comp2 S X k k (Hom.id k)).ty A A)
    (ht : HasTy S k .one [] t A) (ht' : HasTy S k .one [] t' A)
    (hs : StableE S k A t u) (h : (Comp2 S X k k (Hom.id k)).el A u t') : (Comp2 S X k k (Hom.id k)).el A t t' :=
  (he2_tyCode hW hX k (Hom.id k) A A t t').2 hAA ht ht' fun k' σ =>
    ⟨u.isub σ, (hs k' σ).1, (hs k' σ).2, ((kr2_tyCode hW hX) k (Hom.id k) k' σ A A u t').2 h⟩

theorem el_expandSR {X : V} (hX : TyCode k X) {A t t' u' : Tm} (hAA : (Comp2 S X k k (Hom.id k)).ty A A)
    (ht : HasTy S k .one [] t A) (ht' : HasTy S k .one [] t' A)
    (hs : StableE S k A t' u') (h : (Comp2 S X k k (Hom.id k)).el A t u') : (Comp2 S X k k (Hom.id k)).el A t t' := by
  have P := per2_tyCode hW hX k (Hom.id k)
  exact P.symEl hAA (el_expandS hW hX hAA ht' ht hs (P.symEl hAA h))

/-- Expansion on both sides. -/
theorem el_expandS2 {X : V} (hX : TyCode k X) {A t t' u u' : Tm} (hAA : (Comp2 S X k k (Hom.id k)).ty A A)
    (ht : HasTy S k .one [] t A) (ht' : HasTy S k .one [] t' A) (hu : HasTy S k .one [] u A)
    (hs : StableE S k A t u) (hs' : StableE S k A t' u') (h : (Comp2 S X k k (Hom.id k)).el A u u') :
    (Comp2 S X k k (Hom.id k)).el A t t' :=
  el_expandS hW hX hAA ht ht' hs (el_expandSR hW hX hAA hu ht' hs' h)

theorem ty_expandS2 {X : V} (hX : TyCode k X) {A A' B B' : Tm} (hA : IsTyK S k A) (hA' : IsTyK S k A')
    (hB : IsTyK S k B) (hs : StableT S k A B) (hs' : StableT S k A' B') (h : (Comp2 S X k k (Hom.id k)).ty B B') :
    (Comp2 S X k k (Hom.id k)).ty A A' :=
  ty_expandS hW hX hA hA' hs (ty_expandSR hW hX hB hA' hs' h)


/-- Reduction on the right, stable under restriction. -/
theorem el_reduceSR {X : V} (hX : TyCode k X) {A t t' u' : Tm} (hAA : (Comp2 S X k k (Hom.id k)).ty A A)
    (h : (Comp2 S X k k (Hom.id k)).el A t t') (hs : StableE S k A t' u') (hu : HasTy S k .one [] u' A) :
    (Comp2 S X k k (Hom.id k)).el A t u' :=
  (rc2_tyCode hW hX k (Hom.id k) A A A t t' u').2 hAA h hs hu

/-- Reduction on the left, stable under restriction. -/
theorem el_reduceSL {X : V} (hX : TyCode k X) {A t t' u : Tm} (hAA : (Comp2 S X k k (Hom.id k)).ty A A)
    (h : (Comp2 S X k k (Hom.id k)).el A t t') (hs : StableE S k A t u) (hu : HasTy S k .one [] u A) :
    (Comp2 S X k k (Hom.id k)).el A u t' := by
  have P := per2_tyCode hW hX k (Hom.id k)
  exact P.symEl hAA (el_reduceSR hW hX hAA (P.symEl hAA h) hs hu)

theorem ty_reduceSR {X : V} (hX : TyCode k X) {A A' B' : Tm} (h : (Comp2 S X k k (Hom.id k)).ty A A')
    (hs : StableT S k A' B') (hB : IsTyK S k B') : (Comp2 S X k k (Hom.id k)).ty A B' :=
  (rc2_tyCode hW hX k (Hom.id k) A A' B' A A A).1 h hs hB

theorem ty_reduceSL {X : V} (hX : TyCode k X) {A A' B : Tm} (h : (Comp2 S X k k (Hom.id k)).ty A A')
    (hs : StableT S k A B) (hB : IsTyK S k B) : (Comp2 S X k k (Hom.id k)).ty B A' := by
  have P := per2_tyCode hW hX k (Hom.id k)
  exact P.symTy (ty_reduceSR hW hX (P.symTy h) hs hB)

end

end Model.Whnf
