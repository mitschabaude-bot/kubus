import Model.Whnf.Valid2Kan
import Model.Whnf.Valid2GlueEta

/-!
# The hypotheses of the binary fundamental lemma

`Fund2` (`Fund2.lean`) proves every derivation of the minimal judgments valid (`Valid2`), for
derivations in a prefix `S'` of the signature `S`. It is parametrized by:

- `DefHyp2 S S'`: the definitions of `S'` are related to themselves (outer induction on the
  signature);
- `HITHyp2 S S'.length`: the constructor boundary relations and boundary argument typing for the prefix;
- `DataHyp2 S S'`: the remaining HIT elimination rules (`elim`, `elimEq`).

The `transpGlue` rule, whose reduct's `∀i. φ` commutes with substitution only up to equivalence, uses
that element relations are invariant under near terms (`NearEl2`, from `RE2_near`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

/-- Related telescopes: the elements are valid at the telescope's types, instantiated by the earlier
elements of the left list. -/
def VTele2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) : Tm → Tm → List Tm → List Tm → Prop
  | .tnil, .tnil, [], _ => True
  | .tcons a as, .tcons a' as', A :: Δ, prev => Valid2 S Ψ Φ Γ a a' (A.substList prev) ∧ VTele2 S Ψ Φ Γ as as' Δ (a :: prev)
  | _, _, _, _ => False

/-- Transfer of related elements from the instances of `X` to those of `Y`. -/
def ElTr2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (X Y : Tm) : Prop :=
  ∀ k (c : CSub2 S Ψ Φ Γ k) (x y : Tm), RE2 S k (c.L X) x y → RE2 S k (c.L Y) x y

/-- The definitions of `S'` are related to themselves (in `S`). -/
def DefHyp2 (S S' : Sig) : Prop :=
  ∀ (i : ℕ) (t A : Tm), S'[i]? = some (.defn t A) → ∀ k, RT2 S k A A ∧ RE2 S k A t t

/-- Valid components recovered by structural inversion of an eliminator's typing derivation. -/
def ElimInv2 (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (d : ℕ) (ps P bs t T : Tm) : Prop :=
  ∃ D m, S[d]? = some (.data D) ∧ IsList ps ∧ HasTele0 S Ψ Φ Γ ps D.params [] ∧ VTele2 S Ψ Φ Γ ps ps D.params [] ∧
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) ∧
    HasTy0 S Ψ Φ (.data d ps :: Γ) P (.univ m) ∧
    Valid2 S Ψ Φ (.data d ps :: Γ) P P (.univ m) ∧ IsList bs ∧ bs.toList.length = D.ctors.length ∧
    (∀ (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      Valid2 S Ψ Φ Γ b b (D.branchTy d c C ps P)) ∧
    (∀ (c : ℕ) (C : Ctor) (b : Tm) (kb : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b → C.bnd[kb]? = some (ψ, e) →
      Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)) ∧
    HasTy0 S Ψ Φ Γ (.elim d ps P bs t) (P.inst t) ∧ ElTr2 S Ψ Φ Γ (P.inst t) T

/-- The validity of the rules of the inductive types of `S'` (judgments in `S`), given the validity of
their premises. -/
structure DataHyp2 (S S' : Sig) : Prop where
  elim : ∀ {Ψ Φ Γ d D ps P bs t m}, S'[d]? = some (.data D) → D.isHIT = true →
    ps = Tm.ofList ps.toList →
    HasTy0 S Ψ Φ Γ (.data d ps) (.univ D.level) → HasTele0 S Ψ Φ Γ ps D.params [] →
    HasTy0 S Ψ Φ (.data d ps :: Γ) P (.univ m) →
    bs = Tm.ofList bs.toList → bs.toList.length = D.ctors.length →
    (∀ (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      HasTy0 S Ψ Φ Γ b (D.branchTy d c C ps P)) →
    (∀ (c : ℕ) (C : Ctor) (b : Tm) (k : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      C.bnd[k]? = some (ψ, e) →
      EqTm0 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)) →
    HasTy0 S Ψ Φ Γ t (.data d ps) →
    Valid2 S Ψ Φ Γ (.data d ps) (.data d ps) (.univ D.level) → VTele2 S Ψ Φ Γ ps ps D.params [] →
    Valid2 S Ψ Φ (.data d ps :: Γ) P P (.univ m) →
    (∀ (c : ℕ) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      Valid2 S Ψ Φ Γ b b (D.branchTy d c C ps P)) →
    (∀ (c : ℕ) (C : Ctor) (b : Tm) (k : ℕ) (ψ : I) (e : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      C.bnd[k]? = some (ψ, e) →
      Valid2 S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
        (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)) →
    Valid2 S Ψ Φ Γ t t (.data d ps) →
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps P bs t) (P.inst t)
  elimEq : ∀ {Ψ Φ Γ d D ps ps' P P' bs bs' t t' m}, S'[d]? = some (.data D) → D.isHIT = true →
    HasTy0 S Ψ Φ Γ (.elim d ps P bs t) (P.inst t) → HasTy0 S Ψ Φ Γ (.elim d ps' P' bs' t') (P.inst t) →
    EqTele0 S Ψ Φ Γ ps ps' D.params [] → EqTm0 S Ψ Φ (.data d ps :: Γ) P P' (.univ m) →
    bs = Tm.ofList bs.toList → bs' = Tm.ofList bs'.toList →
    bs.toList.length = bs'.toList.length →
    (∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' →
      EqTm0 S Ψ Φ Γ b b' (D.branchTy d c C ps P)) →
    EqTm0 S Ψ Φ Γ t t' (.data d ps) →
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps P bs t) (P.inst t) →
    Valid2 S Ψ Φ Γ (.elim d ps' P' bs' t') (.elim d ps' P' bs' t') (P.inst t) →
    VTele2 S Ψ Φ Γ ps ps' D.params [] → Valid2 S Ψ Φ (.data d ps :: Γ) P P' (.univ m) →
    (∀ (c : ℕ) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
      bs'.toList[c]? = some b' →
      Valid2 S Ψ Φ Γ b b' (D.branchTy d c C ps P)) →
    Valid2 S Ψ Φ Γ t t' (.data d ps) →
    Valid2 S Ψ Φ Γ (.elim d ps P bs t) (.elim d ps' P' bs' t') (P.inst t)

end

end Model.Whnf
