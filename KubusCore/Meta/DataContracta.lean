import KubusCore.Meta.DataTele

/-!
# Metatheory: typing the contracta of the computation rules of inductive types

The redex's typing is given by its generation data (computed in `Presup.lean`): the premises of
the eliminator (`ElimPrem`) or of `transp`, and the scrutinee's introduction typing at its
natural type `X` (`IntroTy`), related to the type the elimination expects by `Rel`. Injectivity
of inductive types in their parameters (`EqTele0.dataInj`) relates the scrutinee's parameters
to the eliminator's.
-/

namespace KubusCore.Meta

open Tm

variable {S : Sig}

theorem elimCon_of (hS : SigClosed S) {Ψ Φ Γ d D D' c C ps P bs b qs args rs m X l T}
    (hD : S[d]? = some (.data D)) (hC : D.ctors[c]? = some C) (hb : bs.toList[c]? = some b)
    (hps : ps = Tm.ofList ps.toList) (hargs : args = Tm.ofList args.toList)
    (hbs : bs = Tm.ofList bs.toList)
    (htele : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (hE : ElimPrem S Ψ Φ Γ d D' ps P bs m) (hI : IntroTy S Ψ Φ Γ (con d c qs args rs) X)
    (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel) (r : Rel S Ψ Φ Γ X (data d ps))
    (tb : TB S Ψ Φ Γ (data d ps)) (ch : TyChainC S Ψ Φ Γ (P.inst (con d c qs args rs)) T) :
    HasTy0 S Ψ Φ Γ (Tm.papps (Tm.apps b (args.toList ++
      C.recPos.map fun k => elim d ps P bs (args.toList.getD k .abort))) rs) T := by
  sorry

theorem elimHcomp_of (hS : SigClosed S) {Ψ Φ Γ d D D' ps P bs qs φ u a m X l T}
    (hD : S[d]? = some (.data D)) (hh : HasTy0 S Ψ Φ Γ (hcomp (data d ps) φ u a) (data d ps))
    (hE : ElimPrem S Ψ Φ Γ d D' ps P bs m)
    (hI : IntroTy S Ψ Φ Γ (hcomp (data d qs) φ u a) X)
    (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel) (r : Rel S Ψ Φ Γ X (data d ps))
    (tb : TB S Ψ Φ Γ (data d ps)) (ch : TyChainC S Ψ Φ Γ (P.inst (hcomp (data d qs) φ u a)) T) :
    HasTy0 S Ψ Φ Γ (comp (P.subst (consSub (hfill (data d ps) φ u a)) (fun i => .var (i + 1))) φ
      (elim d ps.dshift P.dshift bs.dshift u) (elim d ps P bs a)) T := by
  sorry

theorem transpCon_of (hS : SigClosed S) {Ψ Φ Γ d D c C ps φ qs args rs l0 X l T}
    (hD : S[d]? = some (.data D)) (hne : D.params ≠ []) (hC : D.ctors[c]? = some C)
    (hps : ps = Tm.ofList ps.toList) (hargs : args = Tm.ofList args.toList)
    (htele : HasTele0 S Ψ Φ Γ args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse)
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (data d ps) (univ l0)) (hφ : φ.Scoped Ψ)
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (data d ps) ((data d ps).dinst .zero).dshift (univ l0))
    (hI : IntroTy S Ψ Φ Γ (con d c qs args rs) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (r : Rel S Ψ Φ Γ X ((data d ps).dinst .zero)) (tb : TB S Ψ Φ Γ ((data d ps).dinst .zero))
    (ch : TyChainC S Ψ Φ Γ ((data d ps).dinst .one) T) :
    HasTy0 S Ψ Φ Γ (con d c (ps.dinst .one)
      (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T := by
  sorry

theorem transpHcomp_of (hS : SigClosed S) {Ψ Φ Γ d D ps φ qs ψ u a l0 X l T}
    (hD : S[d]? = some (.data D)) (hne : D.params ≠ [])
    (hh : HasTy0 S Ψ Φ Γ (hcomp (data d (ps.dinst .zero)) ψ u a) (data d (ps.dinst .zero)))
    (hL : HasTy0 S (Ψ + 1) Φ.shift Γ.dshift (data d ps) (univ l0)) (hφ : φ.Scoped Ψ)
    (hc : EqTm0 S (Ψ + 1) (cof Φ φ).shift Γ.dshift (data d ps) ((data d ps).dinst .zero).dshift (univ l0))
    (hI : IntroTy S Ψ Φ Γ (hcomp (data d qs) ψ u a) X) (hX : HasTy0 S Ψ Φ Γ X (univ l)) (hl : l ≤ maxLevel)
    (r : Rel S Ψ Φ Γ X ((data d ps).dinst .zero)) (tb : TB S Ψ Φ Γ ((data d ps).dinst .zero))
    (ch : TyChainC S Ψ Φ Γ ((data d ps).dinst .one) T) :
    HasTy0 S Ψ Φ Γ (hcomp (data d (ps.dinst .one)) ψ
      (transp ((data d ps).dsubst skip1I) φ.shift u) (transp (data d ps) φ a)) T := by
  sorry

end KubusCore.Meta
