import Model.Rules.Basic

/-!
# Rules of inductive types (phase 2)

One lemma per rule of inductive types. Work in progress: the lemmas proved by `sorry` are the
rules not yet validated (the model of inductive types is being built).
-/

set_option autoImplicit false

namespace Model

open KubusCore KubusCore.Tm

noncomputable section

variable {S : Sig}

/-! ### Telescopes -/

theorem sem_HasTele_nil {Ψ Φ Γ prev} (h0 : SemWf S Ψ Φ Γ) : SemTele S Ψ Φ Γ .tnil [] prev := h0

theorem sem_HasTele_cons {Ψ Φ Γ a as A Δ prev} (h0 : SemTy S Ψ Φ Γ a (A.substList prev))
    (h1 : SemTele S Ψ Φ Γ as Δ (a :: prev)) : SemTele S Ψ Φ Γ (.tcons a as) (A :: Δ) prev := ⟨h0, h1⟩

theorem sem_EqTele_nil {Ψ Φ Γ prev} (h0 : SemWf S Ψ Φ Γ) : SemEqTele S Ψ Φ Γ .tnil .tnil [] prev := h0

theorem sem_EqTele_cons {Ψ Φ Γ a a' as as' A Δ prev} (h0 : SemEq S Ψ Φ Γ a a' (A.substList prev))
    (h1 : SemEqTele S Ψ Φ Γ as as' Δ (a :: prev)) :
    SemEqTele S Ψ Φ Γ (.tcons a as) (.tcons a' as') (A :: Δ) prev := ⟨h0, h1⟩

/-! ### Typing -/

theorem sem_HasTy_data {Ψ Φ Γ d D ps} (hS : SigOK S) (h0 : S[d]? = some (.data D)) (h1 : D.level + 1 ≤ maxLevel)
    (h2 : SemTele S Ψ Φ Γ ps D.params []) : SemTy S Ψ Φ Γ (data d ps) (univ D.level) := by
  sorry

theorem sem_HasTy_con {Ψ Φ Γ d D c C ps args rs} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (h2 : SemTy S Ψ Φ Γ (data d ps) (univ D.level))
    (h3 : SemTele S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse)
    (h4 : rs.length = C.dims) (h5 : ∀ r ∈ rs, r.Scoped Ψ) :
    SemTy S Ψ Φ Γ (con d c ps args rs) (data d ps) := by
  sorry

theorem sem_HasTy_elim {Ψ Φ Γ d D ps P bs t m} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : SemTy S Ψ Φ Γ (data d ps) (univ D.level)) (h2 : SemTy S Ψ Φ (data d ps :: Γ) P (univ m))
    (h3 : bs = Tm.ofList bs.toList) (h4 : bs.toList.length = D.ctors.length)
    (h5 : ∀ (c : Nat) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      SemTy S Ψ Φ Γ b (D.branchTy d c C ps P))
    (h6 : ∀ (c : Nat) (C : Ctor) (b : Tm) (k : Nat) (ψ : I) (e : Tm), D.ctors[c]? = some C →
      bs.toList[c]? = some b → C.bnd[k]? = some (ψ, e) →
      SemEq S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P))
    (h7 : SemTy S Ψ Φ Γ t (data d ps)) : SemTy S Ψ Φ Γ (elim d ps P bs t) (P.inst t) := by
  sorry

/-! ### Congruence -/

theorem sem_EqTm_data {Ψ Φ Γ d D ps ps'} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : SemTy S Ψ Φ Γ (data d ps) (univ D.level)) (h2 : SemTy S Ψ Φ Γ (data d ps') (univ D.level))
    (h3 : SemEqTele S Ψ Φ Γ ps ps' D.params []) : SemEq S Ψ Φ Γ (data d ps) (data d ps') (univ D.level) := by
  sorry

theorem sem_EqTm_con {Ψ Φ Γ d D c C ps ps' args args' rs rs'} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (h2 : SemTy S Ψ Φ Γ (con d c ps args rs) (data d ps))
    (h3 : SemTy S Ψ Φ Γ (con d c ps' args' rs') (data d ps)) (h4 : SemEqTele S Ψ Φ Γ ps ps' D.params [])
    (h5 : SemEqTele S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse)
    (h6 : rs.length = rs'.length) (h7 : ∀ (k : Nat) (r r' : I), rs[k]? = some r → rs'[k]? = some r' → I.Eq r r') :
    SemEq S Ψ Φ Γ (con d c ps args rs) (con d c ps' args' rs') (data d ps) := by
  sorry

theorem sem_EqTm_elim {Ψ Φ Γ d D ps ps' P P' bs bs' t t' m} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : SemTy S Ψ Φ Γ (elim d ps P bs t) (P.inst t)) (h2 : SemTy S Ψ Φ Γ (elim d ps' P' bs' t') (P.inst t))
    (h3 : SemEqTele S Ψ Φ Γ ps ps' D.params []) (h4 : SemEq S Ψ Φ (data d ps :: Γ) P P' (univ m))
    (h5 : bs.toList.length = bs'.toList.length)
    (h6 : ∀ (c : Nat) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' → SemEq S Ψ Φ Γ b b' (D.branchTy d c C ps P))
    (h7 : SemEq S Ψ Φ Γ t t' (data d ps)) :
    SemEq S Ψ Φ Γ (elim d ps P bs t) (elim d ps' P' bs' t') (P.inst t) := by
  sorry

/-! ### Computation -/

theorem sem_EqTm_conBnd {Ψ Φ Γ d D c C ps args rs} {k : Nat} {ψ b T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (h2 : C.bnd[k]? = some (ψ, b)) (h3 : I.Entails Φ (Ctor.cofAt ψ rs))
    (h4 : SemTy S Ψ Φ Γ (con d c ps args rs) T) :
    SemEq S Ψ Φ Γ (con d c ps args rs) (Ctor.bndAt b ps.toList args.toList rs) T := by
  sorry

theorem sem_EqTm_elimCon {Ψ Φ Γ d D c C ps P bs b qs args rs T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.ctors[c]? = some C) (h2 : bs.toList[c]? = some b)
    (h3 : SemTy S Ψ Φ Γ (elim d ps P bs (con d c qs args rs)) T) :
    SemEq S Ψ Φ Γ (elim d ps P bs (con d c qs args rs))
      (Tm.papps (Tm.apps b (args.toList ++
        C.recPos.map fun k => elim d ps P bs (args.toList.getD k .abort))) rs) T := by
  sorry

theorem sem_EqTm_elimHcomp {Ψ Φ Γ d ps P bs qs φ u a T} (hS : SigOK S)
    (h0 : SemTy S Ψ Φ Γ (elim d ps P bs (hcomp (data d qs) φ u a)) T) :
    SemEq S Ψ Φ Γ (elim d ps P bs (hcomp (data d qs) φ u a))
      (comp (P.subst (fun | 0 => hfill (data d ps) φ u a | j + 1 => var j) (fun i => .var (i + 1))) φ
        (elim d ps.dshift P.dshift bs.dshift u) (elim d ps P bs a)) T := by
  sorry

theorem sem_EqTm_transpData0 {Ψ Φ Γ d D ps φ a T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.params = []) (h2 : SemTy S Ψ Φ Γ (transp (data d ps) φ a) T) :
    SemEq S Ψ Φ Γ (transp (data d ps) φ a) a T := by
  sorry

theorem sem_EqTm_transpCon {Ψ Φ Γ d D c C ps φ qs args rs T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.params ≠ []) (h2 : D.ctors[c]? = some C)
    (h3 : SemTy S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs)) T) :
    SemEq S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs))
      (con d c (ps.dinst .one)
        (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T := by
  sorry

theorem sem_EqTm_transpHcomp {Ψ Φ Γ d D ps φ qs ψ u a T} (hS : SigOK S) (h0 : S[d]? = some (.data D))
    (h1 : D.params ≠ []) (h2 : SemTy S Ψ Φ Γ (transp (data d ps) φ (hcomp (data d qs) ψ u a)) T) :
    SemEq S Ψ Φ Γ (transp (data d ps) φ (hcomp (data d qs) ψ u a))
      (hcomp (data d (ps.dinst .one)) ψ
        (transp ((data d ps).dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) φ.shift u)
        (transp (data d ps) φ a)) T := by
  sorry

end

end Model
