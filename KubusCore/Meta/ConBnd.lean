import KubusCore.Meta.PresupB

/-!
# Metatheory: the boundary of a constructor is typed

For a simple boundary element `b` of constructor `c` (`Ctor.simpleB`: a recursive argument, or a
constructor `c' < c` at the same parameters whose recursive arguments are simple and whose point
arguments are point arguments of `c`), `Ctor.bndAt b ps args rs` is typed at `data d ps` wherever
`con d c ps args rs` is typed by the `con` rule and the restriction entails the boundary's
cofibration. The point arguments' type equations (`Ctor.bndTyped`) are checked in the prefix
signature over the parameters and point arguments (`DataDecl.pointCtx`); `htr` carries them
from the spec's judgments over the prefix to the minimal judgments over `S`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem conBnd_typed (hW : WfSig S) {d : Nat}
    (htr : ∀ {Ψ' Φ' Γ' t u A}, EqTm (S.take d) Ψ' Φ' Γ' t u A → EqTm0 S Ψ' Φ' Γ' t u A)
    {Ψ Φ Γ} {D : DataDecl} {c : Nat} {C : Ctor} {ps args : Tm} {rs : List I} {k : Nat} {ψ : I} {b : Tm}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) (hk : C.bnd[k]? = some (ψ, b))
    (hent : I.Entails Φ (Ctor.cofAt ψ rs)) (hps : ps = Tm.ofList ps.toList)
    (hargs : args = Tm.ofList args.toList)
    (hdata : HasTy0 S Ψ Φ Γ (data d ps) (univ D.level)) (hpt : HasTele0 S Ψ Φ Γ ps D.params [])
    (hat : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (hrs : rs.length = C.dims) (hrsc : ∀ r ∈ rs, r.Scoped Ψ) :
    HasTy0 S Ψ Φ Γ (Ctor.bndAt b ps.toList args.toList rs) (data d ps) := by
  sorry

end KubusCore.Meta
