import KubusCore.Meta.Cof

/-!
# Metatheory: definitions

`transpGlueWith δ` is `Tm.transpGlue` with the cofibration `δ = ∀i. φ` as a parameter
(change M5 of the minimal judgments): `∀i. φ` is computed on disjunctive normal forms, so it
commutes with interval substitution only up to equivalence (`forall0_subst`).
-/

namespace KubusCore.Meta

open Tm

def transpGlueWith (δ : I) (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) : Tm :=
  let φ0 := φ.subst (I.inst0 .zero)
  let φ1 := φ.subst (I.inst0 .one)
  let A1 := A.dinst .one
  let T1 := T.dinst .one
  let e1 := e.dinst .one
  -- the base, composed along the unglued tube: on ψ the Glue line is constant, so
  -- `i ↦ unglue φ(i) e(i) u0` is a tube in the line `A`
  let a0 := unglue φ0 (e.dinst .zero) u0
  let tube := unglue φ e u0.dshift
  let a1' := comp A ψ tube a0
  -- on δ: transport in T, and a path from e(1).1 t1' to a1'
  let t1' := transp T ψ u0
  let ins1 : Nat → I := fun | 0 => .var 0 | n + 1 => .var (n + 2)
  let e' := e.dsubst ins1
  let sysω := split ψ.shift.shift (app (fst e') u0.dshift.dshift) (.or (.neg (.var 1)) (.var 1))
    (split (.neg (.var 1)) (app (fst e') ((transpFill T ψ u0).dsubst ins1))
      (.var 1) ((fill A ψ tube a0).dsubst ins1))
  let ω := plam (comp (A.dsubst ins1) (.or ψ.shift (.or (.neg (.var 0)) (.var 0))) sysω
    (app (fst (e.dinst .zero).dshift) u0.dshift))
  -- extend the partial fibre over a1' to a total one, by contractibility
  let c := app (snd e1) a1'
  let fib := fiber T1 A1 (fst e1) a1'
  let ext := hcomp fib (.or δ ψ)
    (split δ.shift (papp (app (snd c).dshift (pair t1'.dshift ω.dshift)) (.var 0))
      ψ.shift (papp (app (snd c).dshift (pair u0.dshift (plam a1'.dshift.dshift))) (.var 0)))
    (fst c)
  let a1 := hcomp A1 (.or φ1 ψ)
    (split φ1.shift (papp (snd ext).dshift (.neg (.var 0))) ψ.shift a1'.dshift) a1'
  glueEl φ1 e1 (fst ext) a1

theorem transpGlue_eq (A : Tm) (φ : I) (T e : Tm) (ψ : I) (u0 : Tm) :
    Tm.transpGlue A φ T e ψ u0 = transpGlueWith φ.forall0 A φ T e ψ u0 := rfl

end KubusCore.Meta
