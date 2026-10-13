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

Interval terms are `r ::= 0 | 1 | i | ~r | r ∧ s | r ∨ s`. Two interval terms are equal if they agree under every assignment of the variables into the four-element De Morgan algebra `{0, a, b, 1}`, where `~a = a` and `~b = b`. By Kalman's theorem every De Morgan algebra embeds into a power of this one, so this is exactly equality in the free De Morgan algebra.

Cofibrations are interval terms read as `r = 1`, so `i = 0` is `~i`. They denote elements of the CCHM face lattice: put `r` in disjunctive normal form, read each literal `i` as the face `i = 1` and `~i` as `i = 0`, and drop clauses containing both. Then `φ ⊨ ψ` holds when every clause of `φ` contains some clause of `ψ`. In particular `i ∧ ~i` is false, but `i ∨ ~i` is *not* true. Checking entailment over 0/1 assignments would be unsound: it would make the system `[i=0 ↦ true, i=1 ↦ false]` total, and hence a path from `true` to `false`.

The judgments use a face rule: if `Φ ⊨ (i = d)` for an endpoint `d`, then `t ≡ t[d/i]` under `Φ`.

### Structural rules for cofibrations

- **Weakening:** if `Φ' ⊨ Φ`, everything derivable under `Φ` is derivable under `Φ'`.
- **Absurdity:** if `Φ ⊨ 0`, then any two well-formed terms of the same type are equal, and every type is inhabited (by the empty system `[]`).
- **Local character:** if `Φ ⊨ φ ∨ ψ` and a judgment holds under both `Φ ∧ φ` and `Φ ∧ ψ`, then it holds under `Φ`.

### Systems

`[φ₁ ↦ t₁, …, φₙ ↦ tₙ] : A` is well-typed under `Φ` when `Φ ⊨ φ₁ ∨ … ∨ φₙ`, each `tₖ : A` under `Φ ∧ φₖ`, and `tₖ ≡ tₗ` under `Φ ∧ φₖ ∧ φₗ`. Under `Φ ⊨ φₖ` the system equals `tₖ`. The same holds for systems of types.

### Type formers

- `U_l : U_(l+1)` for `l + 1 ≤ maxLevel` (currently 4). Cumulativity: `A : U_l` implies `A : U_(l+1)`, with the same equations. No other subtyping. Levels are bounded so that the model needs only finitely many Grothendieck universes, which Lean can construct; an unbounded tower would make the consistency theorem conditional.
- `Π`, `Σ`, with β and η. Lambdas are annotated with their domain, `λ (x : A). t`, so that raw terms have type-independent denotations in the set-valued model.
- `PathP (i. A) a b`, where `a : A(0/i)` and `b : A(1/i)`. The introduction `⟨i⟩ t` requires `t(0/i) ≡ a` and `t(1/i) ≡ b`. Application `p r` reduces: `p 0 ≡ a`, `p 1 ≡ b`, β, and η.
- `Glue A [φ ↦ (T, e)]` with `T` and `e : Equiv T A` under `φ`. Under `φ`, `Glue … ≡ T`, `glue [φ ↦ t] a ≡ t` and `unglue φ e g ≡ e.1 g`. `unglue` must carry the equivalence `e`: under `φ` an element of `T` inhabits the Glue type for *every* equivalence, so without it the rule would identify `e.1 g` and `e'.1 g` for any two equivalences, which is inconsistent. There are β and η rules for glue/unglue. The congruence rules for `glue [φ ↦ t] a` and `unglue φ e g` allow equivalences that are only judgmentally equal under `φ` (M4), as the Glue type former does. `Equiv` is the contractible-fibers definition, built from `Π`, `Σ` and `PathP`.

### Structural rules, presupposition and inversion

Weakening (by a term or interval variable), single substitution (of a term or an interval term), presupposition (both sides of an equation are well-typed) and inversion of type formers (`Π A B : U_l` gives `A : U_l` and `B : U_l`; similarly for `Σ`, `PathP`, `(i : I) → A`, and the fibre of `Glue`). Inversion for the base and equivalence of `Glue` is deliberately absent: a Glue type reduces to its fibre on its face, so those rules have no model. are rules, not metatheorems. They hold in the intended model, a partial interpretation indexed by universe level, and they let the certified kernel construct derivations without first proving metatheory. Each one is an obligation for the model.

### Global definitions

Judgments are parameterized by a signature `S` of closed definitions `(t, A)`. `const k` has type `A` and unfolds to `t`. A signature is well-formed when each definition checks against the ones before it. The consistency statement: for every well-formed `S`, no closed term has type `(A : U₀) → A`.

### Kan operations

- `transp (i. A) φ a : A(1/i)` for `a : A(0/i)`, provided `A ≡ A(0/i)` under `Φ ∧ φ`. Under `φ` it equals `a`.
- `hcomp A [φ ↦ i. u] a : A`, with `u : A` under `Φ ∧ φ, i` and `u(0/i) ≡ a` under `φ`. Under `φ` it equals `u(1/i)`.
- `comp` and `fill` are defined terms.

The computation rules are those of CHM (§2 and §3 of *On Higher Inductive Types in Cubical Type Theory*):

- `transp` for `U` (identity), `Π`, `Σ`, `PathP` and `Glue`; the Glue rule accepts any cofibration `δ` equivalent to `∀i. φ` in its contractum (M5). The syntactic `∀i. φ` commutes with interval substitution only up to equivalence;
- `hcomp` for `Π`, `Σ`, `PathP` and `Glue`;
- `hcomp` in `U_l` (`hcompU`): `hcomp U [φ ↦ i. u] u0 ≡ Glue u0 [φ ↦ (u(1/i), e)]`, where `e : u(1/i) ≃ u0` is transport backwards along the tube (`lineEquiv` of `u(~i/i)`; on `φ`, `u(0/i) ≡ u0`). `lineEquiv B` pairs `f_1` with a proof that it is an equivalence, where `f_i = λ x. transp (j. B(i ∧ j)) (i = 0) x : B(0) → B(i)`: `f_0` is the identity, so the evident proof `idIsEquiv` that it is an equivalence is transported along `i ↦ isEquiv f_i`. All of this is defined by core terms, so no extra type former is needed.

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

## Status

All four steps are done for the core fragment (Π, Σ, paths, `(i : I) → A`, universes, Glue):
- the kernel certifies the univalence development;
- self-checks and fuzzing run in CI;
- the specification is in Lean, and the kernel builds a derivation of it for everything it accepts;
- the model proves `KubusCore.Consistent` unconditionally, and `Model.kernel_consistent` connects it to the kernel.

Phase 2, inductive types and HITs (`docs/inductive-types.md`), is done as well: spec, kernel and model. The consistency theorem covers the whole library. Seventeen spec bugs were found along the way, by the model and by red-team reviews, and recorded in `model/README.md`. Three of them made the spec inconsistent: `unglue` and `glueEl` without their equivalence, and data declarations checked against themselves. The others were rules the model could not validate as stated.
