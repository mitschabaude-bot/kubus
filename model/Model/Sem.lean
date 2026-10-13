import Model.WFFib

/-!
# Semantic judgments

The interpretation `⟦t⟧_S` of a raw term in a signature `S` (constants are interpreted by their
bodies, `cstFn`), and the semantic counterparts of the spec's judgments:

* a *point* of a context `Ψ; Φ; Γ` at stage `m` is an interval environment `ρ` in which `Φ` holds
  and a term environment `γ` whose entries have the types of `Γ`;
* `SemTy S Ψ Φ Γ t A`: at every point, `⟦t⟧` is an element of the code `⟦A⟧`, `⟦A⟧` is a
  well-formed code of some level `≤ maxLevel`, and both are natural (commute with restriction);
* `SemEq`: both sides are `SemTy` and denote the same value at every point.

Constants: the syntactic side condition `ConstsLt` (all constants of a term are in the
signature) makes interpretations stable under extending the signature.
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Good codes: well-formed codes of some level `≤ maxLevel`, and universes. -/
def TyCode (m : ℕ) (c : V) : Prop := ∃ l ≤ maxLevel, (WF l m c ∧ c ∈ Vt l) ∨ c = univC m l

/-! ### Constants -/

/-- The value of constant `k` of the signature `S` at stage `m`: its body, interpreted with the
constants before `k`. -/
def cstFn (S : Sig) (m : ℕ) (k : ℕ) : V :=
  if h : k < S.length then
    interp (fun m' j => if j < k then cstFn S m' j else ∅) univC TyCode (S[k]'h).1 m (fun _ => DM.zero m)
      (fun _ => emptyC m)
  else ∅
termination_by k
decreasing_by assumption

/-- The interpretation of raw terms in the signature `S`. -/
abbrev sem (S : Sig) (t : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : V := interp (cstFn S) univC TyCode t m ρ γ

/-- All constants of a term are below `n`. -/
def _root_.KubusCore.Tm.ConstsLt (n : ℕ) : Tm → Prop
  | .var _ | .univ _ | .abort => True
  | .const k => k < n
  | .pi A B | .sigma A B | .lam A B | .app A B | .pair A B => A.ConstsLt n ∧ B.ConstsLt n
  | .fst p | .snd p | .plam p | .ipi p | .papp p _ => p.ConstsLt n
  | .unglue _ e g => e.ConstsLt n ∧ g.ConstsLt n
  | .path A a b => A.ConstsLt n ∧ a.ConstsLt n ∧ b.ConstsLt n
  | .split _ t _ u => t.ConstsLt n ∧ u.ConstsLt n
  | .transp A _ a => A.ConstsLt n ∧ a.ConstsLt n
  | .hcomp A _ u a => A.ConstsLt n ∧ u.ConstsLt n ∧ a.ConstsLt n
  | .glue A _ T e => A.ConstsLt n ∧ T.ConstsLt n ∧ e.ConstsLt n
  | .glueEl _ e t a => e.ConstsLt n ∧ t.ConstsLt n ∧ a.ConstsLt n

/-! ### Points, naturality, well-formed types -/

variable {S : Sig} {k m n : ℕ}

/-- A point of the context `Ψ; Φ; Γ` at stage `m`. -/
structure IsPoint (S : Sig) (Φ : I) (Γ : Ctx) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop where
  cof : (ival ρ Φ).holds
  typ : ∀ x A, Γ.lookup x = some A → γ x ∈ El (sem S A m ρ γ) (Hom.id m)
  kv : ∀ x, IsKV m (γ x)

/-- `t` commutes with restriction at the point `(ρ, γ)`. -/
def Natural (S : Sig) (t : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop :=
  ∀ k (f : Hom k m), sem S t k (ρ.restr f) (TEnv.restr γ f) = res f (sem S t m ρ γ)

/-- `A` denotes a well-formed code of some level `≤ maxLevel`, or a universe, at the point
`(ρ, γ)`. (The top universe `U_maxLevel` is a type but not an element of a universe.) -/
def TyOK (S : Sig) (A : Tm) (m : ℕ) (ρ : IEnv m) (γ : ℕ → V) : Prop := TyCode m (sem S A m ρ γ)

/-- Semantic well-formedness of a context. -/
def SemWf (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) : Prop :=
  Φ.Scoped Ψ ∧ (∀ x A, Γ.lookup x = some A → A.ConstsLt S.length) ∧
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → ∀ x A, Γ.lookup x = some A →
    TyOK S A m ρ γ ∧ Natural S A m ρ γ

/-- Semantic typing. -/
def SemTy (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t A : Tm) : Prop :=
  SemWf S Ψ Φ Γ ∧ t.ConstsLt S.length ∧ A.ConstsLt S.length ∧
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ →
    sem S t m ρ γ ∈ El (sem S A m ρ γ) (Hom.id m) ∧ Natural S t m ρ γ ∧
      TyOK S A m ρ γ ∧ Natural S A m ρ γ

/-- Semantic equality. -/
def SemEq (S : Sig) (Ψ : ℕ) (Φ : I) (Γ : Ctx) (t u A : Tm) : Prop :=
  SemTy S Ψ Φ Γ t A ∧ SemTy S Ψ Φ Γ u A ∧
  ∀ m (ρ : IEnv m) γ, IsPoint S Φ Γ m ρ γ → sem S t m ρ γ = sem S u m ρ γ

/-- The signature is semantically valid: every definition is well-typed in the model. -/
def SigOK (S : Sig) : Prop :=
  ∀ k t A, S[k]? = some (t, A) → t.closedB 0 0 ∧ A.closedB 0 0 ∧ SemTy (S.take k) 0 .one [] t A

end

end Model
