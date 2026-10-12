# Kubus Core: the theory to verify

This document fixes the kernel theory before anything gets formalized. It is the reference for all four verification steps:

1. a small trusted kernel that checks fully explicit core terms;
2. automated soundness checks: re-checking normal forms, stability of evaluation under substitution, and random well-typed terms;
3. a declarative specification of these rules in Lean, with a proof that the kernel is sound for it (kernel accepts ⇒ derivable);
4. a model of the specification in Lean, so that a closed term of `Empty` yields a proof of `False`.

Steps 3 and 4 together give consistency of whatever the kernel accepts. Neither needs normalization: soundness only needs every kernel step to be justified by a rule. Normalization stays a design constraint, since it is what makes type checking decidable, but it is not on the critical path for consistency.

## Changes from the current implementation

The current checker mixes elaboration and checking, and some of its rules are awkward to justify. The core theory therefore changes the following:

| current Kubus | Kubus Core | why |
|---|---|---|
| heterogeneous `comp` is primitive | `transp` and `hcomp` are primitive, `comp` is defined (CHM) | each rule is simpler and matches the HIT model of Coquand–Huber–Mörtberg |
| regularity only for closed first-order data | `transp` takes a cofibration on which the line is constant; `transp` on any closed data type is the identity | a principled rule, valid in the model |
| pattern matching with a termination checker | eliminators in the kernel; the elaborator compiles structural pattern matching to them | no termination checker in the trusted base |
| systems only as arguments of `comp`/`Glue` | systems are terms, typed under a cofibration | uniform rules for partial elements |
| nominal atoms in the evaluator | specified with de Bruijn interval variables; the kernel's evaluator is proven against substitution | provable |

The surface language stays as it is; the elaborator absorbs the differences.

## Judgments

Contexts have three parts: interval variables `Ψ`, a cofibration `Φ` restricting them, and term variables `Γ`, whose types may mention `Ψ`. The judgments are

```
Ψ; Φ; Γ ⊢            Ψ; Φ; Γ ⊢ A type_l         Ψ; Φ; Γ ⊢ t : A
Ψ; Φ; Γ ⊢ A ≡ B type_l                          Ψ; Φ; Γ ⊢ t ≡ u : A
```

with de Bruijn indices for both sorts of variable.

### Interval and cofibrations

Interval terms are `r ::= 0 | 1 | i | ~r | r ∧ s | r ∨ s`, with equality given by the free De Morgan algebra. Cofibrations are interval terms read as `r = 1`, so `i = 0` is `~i`. Entailment `φ ⊨ ψ` holds when every assignment of `0/1` to the variables that makes `φ` equal to 1 also makes `ψ` equal to 1. This is the face lattice of CCHM: `i ∧ ~i` is a false cofibration even though it is not `0` as an interval term.

### Structural rules for cofibrations

- **Weakening:** if `Φ' ⊨ Φ`, everything derivable under `Φ` is derivable under `Φ'`.
- **Absurdity:** if `Φ ⊨ 0`, then any two well-formed terms of the same type are equal, and every type is inhabited (by the empty system `[]`).
- **Local character:** if `Φ ⊨ φ ∨ ψ` and a judgment holds under both `Φ ∧ φ` and `Φ ∧ ψ`, then it holds under `Φ`.

### Systems

`[φ₁ ↦ t₁, …, φₙ ↦ tₙ] : A` is well-typed under `Φ` when `Φ ⊨ φ₁ ∨ … ∨ φₙ`, each `tₖ : A` under `Φ ∧ φₖ`, and `tₖ ≡ tₗ` under `Φ ∧ φₖ ∧ φₗ`. Under `Φ ⊨ φₖ` the system equals `tₖ`. The same holds for systems of types.

### Type formers

- `U_l type_(l+1)` and `U_l : U_(l+1)`. Cumulativity: `A : U_l` implies `A : U_(l+1)`, with the same equations. No other subtyping.
- `Π`, `Σ`, with β and η.
- `PathP (i. A) a b`, where `a : A(0/i)` and `b : A(1/i)`. The introduction `⟨i⟩ t` requires `t(0/i) ≡ a` and `t(1/i) ≡ b`. Application `p r` reduces: `p 0 ≡ a`, `p 1 ≡ b`, β, and η.
- `Glue A [φ ↦ (T, e)]` with `T` and `e : Equiv T A` under `φ`. Under `φ`, `Glue … ≡ T`, `glue [φ ↦ t] a ≡ t` and `unglue φ g ≡ e.1 g`. There are β and η rules for glue/unglue. `Equiv` is the contractible-fibers definition, built from `Π`, `Σ` and `PathP`.

### Kan operations

- `transp (i. A) φ a : A(1/i)` for `a : A(0/i)`, provided `A ≡ A(0/i)` under `Φ ∧ φ`. Under `φ` it equals `a`.
- `hcomp A [φ ↦ i. u] a : A`, with `u : A` under `Φ ∧ φ, i` and `u(0/i) ≡ a` under `φ`. Under `φ` it equals `u(1/i)`.
- `comp` and `fill` are defined terms.

The computation rules are those of CHM (§2 and §3 of *On Higher Inductive Types in Cubical Type Theory*):

- `transp` for `U` (identity), `Π`, `Σ`, `PathP` and `Glue`;
- `hcomp` for `Π`, `Σ`, `PathP` and `Glue`;
- `hcomp` in `U_l` produces `Glue` along an equivalence. That equivalence is defined by a fixed core term (transport along a line is an equivalence), so no extra type former is needed.

### Inductive types (phase 2)

These come after the core fragment above is verified end to end:

- **Schema:** parameters, strictly positive non-nested fields, and path constructors with boundary systems over the constructor's point arguments.
- **Elements:** each type also gets formal `hcomp` elements.
- **Kan operations:** `transp` acts componentwise on constructors and pushes through `hcomp`. On a type without parameters it is the identity.
- **Elimination:** eliminators with clauses for every constructor, a computation rule for `hcomp`, and boundary conditions on path-constructor clauses.

The model for this class is CHM's.

## The model (step 4)

The plan is the Orton–Pitts route. Their paper proves that CCHM's rules hold in any topos with an interval object and cofibrations satisfying a short list of axioms; the universe and univalence are added later by Licata–Orton–Pitts–Spitters.

1. **Formalize the axiomatic argument in Lean:**
   - the typing rules are interpreted as families over a category with families (CwF);
   - "fibrant" is defined as carrying a `transp`/`hcomp` structure;
   - the Kan rules are verified against the axioms.
2. **Instantiate the axioms with De Morgan cubical sets,** i.e. presheaves on the De Morgan cube category, using Mathlib's presheaf toposes.
3. **Construct the fibrant universe and Glue,** following Licata–Orton–Pitts–Spitters (the "tiny interval" construction).

Then a closed proof of `Empty` in the specification gives a global section of the empty presheaf, which is `False`.

## Order of work

Steps 1–3 cover the core fragment first: Π, Σ, paths, universes and Glue. Inductive types and HITs follow once the fragment is closed end to end.
