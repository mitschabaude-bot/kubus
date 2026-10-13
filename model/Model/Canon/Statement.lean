import KubusCore

/-!
# Canonicity: the statement (see `model/CANONICITY.md`)
-/

namespace KubusCore

/-- Canonical closed elements of a parameterless inductive type `d`: a constructor whose
boundary does not hold, with canonical recursive arguments and closed interval arguments, or a
formal composition with an empty system of a canonical element. Point arguments are arbitrary
closed terms of their types. -/
inductive Canon (S : Sig) (d : Nat) : Tm → Prop
  | con {D : DataDecl} {c : Nat} {C : Ctor} {L : List Tm} {rs : List I} :
      S[d]? = some (.data D) → D.ctors[c]? = some C →
      (∀ r ∈ rs, r = .zero ∨ r = .one) →
      (∀ ψ b, (ψ, b) ∈ C.bnd → ¬ I.Entails .one (Ctor.cofAt ψ rs)) →
      (∀ k (hk : k < L.length), C.isRec k = true → Canon S d L[k]) →
      HasTy S 0 .one [] (.con d c .tnil (Tm.ofList L) rs) (.data d .tnil) →
      Canon S d (.con d c .tnil (Tm.ofList L) rs)
  | hcomp {a : Tm} : Canon S d a → Canon S d (.hcomp (.data d .tnil) .zero a.dshift a)

/-- Canonicity for closed elements of parameterless inductive types. -/
def Canonicity : Prop :=
  ∀ (S : Sig) (d : Nat) (D : DataDecl) (t : Tm), WfSig S → S[d]? = some (.data D) → D.params = [] →
    HasTy S 0 .one [] t (.data d .tnil) → ∃ t', EqTm S 0 .one [] t t' (.data d .tnil) ∧ Canon S d t'

end KubusCore
