import KubusCore.Meta.TranspCon

/-!
# Metatheory: typing the contractum of `hcompCon`

Composition in an inductive type without path constructors, componentwise (`Tm.hcompTele`):
recursive arguments by `hcomp`/`hfill` in the inductive type, point arguments by `comp`/`fill`
along their type lines, which are typed by the point argument clause of `DataDecl.Wf` over the
prefix signature (P11), carried to `S` by `htr`.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem hcompCon_of (hS : SigClosed S) (hW : WfSig S) {Ψ Φ Γ d D c C ps φ u qs uargs args T}
    (htr : ∀ {Ψ' Φ' Γ' t A}, HasTy (S.take d) Ψ' Φ' Γ' t A → HasTy0 S Ψ' Φ' Γ' t A)
    (h0 : S[d]? = some (.data D)) (h1 : D.isHIT = false) (h2 : D.ctors[c]? = some C)
    (h3 : ps = Tm.ofList ps.toList) (h4 : args = Tm.ofList args.toList)
    (h5 : uargs = Tm.ofList uargs.toList)
    (h6 : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (h7 : HasTele0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse)
    (h8 : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (con d c ps.dshift uargs []) (data d ps.dshift))
    (h9 : EqTele0 S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse)
    (h10 : HasTy0 S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args [])) T) :
    HasTy0 S Ψ Φ Γ (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d ps)
      ps.dshift.toList φ 0 [] uargs.toList args.toList)) []) T := by
  sorry

end KubusCore.Meta
