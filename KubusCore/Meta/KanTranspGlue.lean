import KubusCore.Meta.KanTranspGlueAux

/-!
# Metatheory: typing the contractum of `transp` in Glue types
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

/-! ## The parts of the contractum -/

section
variable (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) (δ : I)

def tgA0 : Tm := unglue (φ.subst (I.inst0 .zero)) (e.dinst .zero) u0
def tgTube : Tm := unglue φ e u0.dshift
def tgA1' : Tm := comp A ψ (tgTube φ e u0) (tgA0 φ e u0)
def tgT1 : Tm := transp T ψ u0
def tgSys : Tm :=
  split ψ.shift.shift (app (fst (e.dsubst (sk (.var 0) 2))) u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
    (split (.neg (.var 1)) (app (fst (e.dsubst (sk (.var 0) 2))) ((transpFill T ψ u0).dsubst (sk (.var 0) 2)))
      (.var 1) ((fill A ψ (tgTube φ e u0) (tgA0 φ e u0)).dsubst (sk (.var 0) 2)))
def tgBody : Tm :=
  comp (A.dsubst (sk (.var 0) 2)) (.or ψ.shift (.or (.neg (.var 0)) (.var 0))) (tgSys A φ T e ψ u0)
    (app (fst (e.dinst .zero).dshift) u0.dshift)
def tgOmega : Tm := plam (tgBody A φ T e ψ u0)
def tgC : Tm := app (snd (e.dinst .one)) (tgA1' A φ e ψ u0)
def tgFib : Tm := fiber (T.dinst .one) (A.dinst .one) (fst (e.dinst .one)) (tgA1' A φ e ψ u0)
def tgPd : Tm := app (snd (tgC A φ e ψ u0)) (pair (tgT1 T ψ u0) (tgOmega A φ T e ψ u0))
def tgPpsi : Tm := app (snd (tgC A φ e ψ u0)) (pair u0 (plam (tgA1' A φ e ψ u0).dshift))
def tgExt : Tm :=
  hcomp (tgFib A φ T e ψ u0) (.or δ ψ)
    (split δ.shift (papp (tgPd A φ T e ψ u0).dshift (.var 0)) ψ.shift (papp (tgPpsi A φ e ψ u0).dshift (.var 0)))
    (fst (tgC A φ e ψ u0))
def tgA1 : Tm :=
  hcomp (A.dinst .one) (.or (φ.subst (I.inst0 .one)) ψ)
    (split (φ.subst (I.inst0 .one)).shift (papp (snd (tgExt A φ T e ψ u0 δ)).dshift (.neg (.var 0)))
      ψ.shift (tgA1' A φ e ψ u0).dshift) (tgA1' A φ e ψ u0)

theorem plam_dshift_dshift (a : Tm) : (plam a.dshift).dshift = plam a.dshift.dshift := by
  show plam (a.dshift.ren id (upRen Nat.succ)) = _; congr 1; ssub

theorem transpGlueWith_eq : transpGlueWith δ A φ T e ψ u0 =
    glueEl (φ.subst (I.inst0 .one)) (e.dinst .one) (fst (tgExt A φ T e ψ u0 δ)) (tgA1 A φ T e ψ u0 δ) := by
  simp only [transpGlueWith, tgA1, tgExt, tgPd, tgPpsi, tgFib, tgC, tgOmega, tgBody, tgSys, tgT1, tgA1',
    tgTube, tgA0]
  rw [← plam_dshift_dshift]
  rfl

end

end KubusCore.Meta
