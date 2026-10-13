import Model.Rules.Inj

/-!
# Composition in inductive types without path constructors (`hcompCon`)
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore KubusCore.Tm

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k m n : ℕ}

theorem sem_EqTm_hcompCon {Ψ Φ Γ d D c C ps φ u qs uargs args T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.isHIT = false) (h2 : D.ctors[c]? = some C) (hpl : ps = Tm.ofList ps.toList)
    (hal : args = Tm.ofList args.toList) (hul : uargs = Tm.ofList uargs.toList)
    (h3 : SemTele S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (h4 : SemTele S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse)
    (h5 : SemEq S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (con d c ps.dshift uargs []) (data d ps.dshift))
    (h6 : SemEqTele S Ψ (cof Φ φ) Γ (uargs.dinst .zero) args (C.argTys d D.params.length) ps.toList.reverse)
    (h7 : SemTy S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args [])) T) :
    SemEq S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args []))
      (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d ps) ps.dshift.toList φ 0 []
        uargs.toList args.toList)) []) T := by
  sorry

end

end Model
