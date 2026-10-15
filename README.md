# Kubus

Kubus is a proof assistant for cubical type theory, written in Lean 4. Its kernel is verified and its theory is proven consistent in Lean.

It implements a CCHM-style cubical type theory with the De Morgan interval, Kan composition, Glue types and univalence, higher inductive types, and a cumulative universe hierarchy. Every definition is checked by a small kernel that builds a derivation in a formal specification of the theory. A cubical-sets model, also in Lean, proves that specification consistent.

```
data S1 : U := base | loop (i : I) [i = 0 -> base, i = 1 -> base]

def helix : S1 -> U
  | base => Int
  | loop i => sucPathInt i          -- ua of the successor equivalence

def winding (p : Path S1 base base) : Int := transport (\i -> helix (p i)) (pos zero)

#eval winding (compS1 loopP loopP)   -- pos (suc (suc zero))
```

The library (`lib/`) proves among other things that the loop space of the circle is the integers (`loopspace.ktt`), and that `Σ (T : U), Equiv T A` is contractible, i.e. univalence (`univalence.ktt`). Transport along these equivalences computes.

## What is verified

```
                          ┌── KubusCore/Kernel: returns derivations ──┐
.ktt ── elaborator ── bridge ──────────────────────────────────────────┴─→ WfSig S
       (Kubus/)                                                              │
                                                     model/: Consistent ─────┴─→ no closed term of (A : U₀) → A
```

- **Specification** (`KubusCore/`; `docs/core-theory.md`, `docs/inductive-types.md`). The theory is written as inductive typing and equality judgments over de Bruijn syntax with term and interval variables. It has the CCHM face lattice, `transp`/`hcomp` with the computation rules of Coquand–Huber–Mörtberg (CHM), Glue types, universes, data types and higher inductive types, and global definitions. `KubusCore/Meta/Minimal.lean` is its textbook form. The two presentations are proven equivalent over well-formed signatures (`docs/metatheory.md`).
- **Kernel** (`KubusCore/Kernel/`; `KubusCore/KERNEL.md`). Its functions are total, and each returns a derivation of the judgment it checks. A signature that the kernel accepts therefore comes with a proof that it is well formed. `kubus FILE` runs the kernel on every definition and data type, and all of `lib/` is certified. Each certified statement is also read back and checked to be convertible to the one the user wrote (translation adequacy, `KubusCore/KERNEL.md`), so a certificate is about the definition as written.
- **Consistency** (`model/`; `model/PROOF.md`). A cubical-sets model built on Mathlib validates every rule. `Model.kernel_consistent0` states that if the kernel accepts a signature, no closed term of `(A : U₀) → A` exists in the textbook theory. It depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and CI checks this on every push. `docs/metatheory.md` lists exactly what one has to read to trust the result.

Building the model turned up seventeen bugs in earlier versions of the specification. Three of them made it inconsistent. All are recorded in `model/README.md`.

Canonicity is proven unconditionally in Lean (`Model.Whnf.canonicity`, `model/CANONICITY.md`). Over a well-formed signature, every closed element of a parameterless inductive type is judgmentally equal to a canonical form: a numeral for `Nat`, or a constructor or formal composition for higher inductive types. The proof derives Glue compatibility through a binary logical relation with hereditary Kan evidence; it assumes no extra canonicity obligations. CI checks that the theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Full normalization remains a design goal.

## Getting started

```
lake build
KUBUS_PATH=lib .lake/build/bin/kubus lib/loopspace.ktt                  # check and certify
KUBUS_PATH=lib .lake/build/bin/kubus --interactive lib/loopspace.ktt    # REPL
tests/run.sh
```

`docs/tutorial.md` introduces the language, from paths to univalence and the circle. Its examples are run by the tests.

`editor/vscode` is a VS Code extension with syntax highlighting and a client for the language server `kubus --lsp`. The server reports errors with source ranges, shows `#eval` results and the goals of `?` holes, shows types on hover, and marks declarations the kernel has certified. To install:

```
lake build                                  # then put .lake/build/bin on PATH, or set kubus.path
cd editor/vscode && npm install && npm run package
code --install-extension kubus-0.1.0.vsix
```

## The language

```
def name (x : A) (i : I) : T := body              -- (i : I) binds an interval variable
def name {A : U} (x : A) : T := body               -- {A : U} is an implicit argument
def name := body                                   -- the type is inferred
def max : Nat -> Nat -> Nat                        -- pattern matching, several arguments, nested patterns
  | zero, n => n
  | suc m, zero => suc m
  | suc m, suc n => suc (max m n)
data D (params) : U n := c (x : A) | p (x : A) (i : I) [i = 0 -> ..., i = 1 -> ...]
import name                                        -- loads name.ktt (file directory, then KUBUS_PATH)
#eval t                                            -- normal form and type
#check t
```

Terms: `U`, `U 1`, `(x : A) -> B`, `A -> B`, `(x : A) × B`, `(a, b)`, `p.1`, `p.2`, `\x y -> t`, `\(x : A) -> t`, `let x : A := t in u`, `(t : A)`, `_` (solved by unification), and `?` (a hole that reports its goal).

**Implicit arguments** are inserted at application sites and solved by pattern unification: `trans p (sym q)`, `transport (\i -> helix (p i)) x`. They can be given as `f {a}`, `f {x := a}`, or all explicitly as `@f`. Goals, solutions and error messages keep definitions folded.

**Pattern matching** compiles nested, multi-argument clauses to case trees and checks coverage and reachability. Recursion must be structural.

**Cubical primitives:**

| syntax | meaning |
|---|---|
| `0`, `1`, `~r`, `r /\ s`, `r \/ s` | the interval (a De Morgan algebra) |
| `Path A a b`, `PathP (\i -> A) a b`, `a ≡ b` | path types; `\i -> t` introduces, `p r` eliminates |
| `(i : I) -> A` | interval-indexed families without fixed endpoints |
| `[i = 0 -> u, j = 1 /\ k = 0 -> v]` | systems; faces are interval formulas |
| `transp i A [φ] u0` | transport along the line `A`, which must be constant where `φ` holds |
| `comp i A [φ -> u] u0`, `hcomp i A [φ -> u] u0`, `fill i A [φ -> u] u0`, `hfill i A [φ -> u] u0` | heterogeneous and homogeneous composition, and their fillers |
| `Glue A [φ -> (T, e)]`, `glue [φ -> t] a`, `unglue g` | Glue types, with `e : Equiv T A` |
| `f^k` | `f` with all universe levels raised by `k` (universe polymorphism by displacement) |

## How it works

| directory | contents |
|---|---|
| `Kubus/` | parser, elaborator (bidirectional, with unification and checking under faces), NbE evaluator, pattern-match compiler, language server, self-checks; `Kubus/Bridge.lean` translates elaborated definitions to the kernel |
| `KubusCore/` | the specification (`Syntax.lean`, `Rules.lean`), the kernel (`Kernel/`) and the metatheory (`Meta/`) |
| `model/` | the cubical-sets model and the consistency theorems (separate Lake project, with Mathlib) |
| `lib/` | the standard library |
| `tests/` | golden tests, failure tests, kernel tests, fuzzer |
| `docs/` | the theory, the tutorial and the metatheory |

The elaborator's evaluator implements the specification's operations: `transp` and `hcomp` are primitive and compute by the Coquand–Huber–Mörtberg rules (`hcomp` in the universe is a Glue type along `lineEquiv`, composition in an inductive type without path constructors is componentwise, higher inductive types have formal compositions), and `comp`, `fill` and `hfill` are derived as in the specification. There is no regularity, so the elaborator's definitional equality is the specification's. Interval variables in values are nominal atoms, neutral variables carry their types, and applications of globals stay folded until a computation needs their value. The evaluator only helps the elaborator: what counts is the kernel's certificate.

## Testing

`tests/run.sh` runs:
- the library, with self-checks and kernel certification;
- golden tests;
- failure tests, which must be rejected with a given error;
- kernel regression tests;
- tutorial, REPL and language-server tests.

`kubus --selfcheck FILE` checks invariants of the evaluator on every definition: conversion is reflexive and symmetric, read-back round-trips, printed normal forms re-check at the same type, and evaluation is stable under interval substitution.

`tests/fuzz.sh N SEED` generates random well-typed programs over the library, together with ill-typed mutants that must be rejected.

CI runs the tests, a fuzz run, and the model build with its axiom check.

## Limitations

- **Universes:** levels are bounded (`U 0` to `U 4`), so the consistency theorem needs no large-cardinal assumptions.
- **Data types:**
  - they are finitary, with parameters that are small types or universes, and no indices or mutual definitions;
  - path-constructor boundaries may only use the constructor's point arguments and other constructors, so pushouts can't be declared yet;
  - clauses for path constructors can't use nested patterns.
- **Elaborator vs. kernel:** on the fuzzer, the kernel rejects or skips none of the programs the elaborator accepts, but on some programs with deeply nested compositions along `hcomp U` and Glue lines (from `ua`, `sucPathInt`, `winding`) it does not finish within minutes where the elaborator takes seconds. The fuzzer tracks them as kernel stress cases (see `KubusCore/KERNEL.md`).

## License

MIT
