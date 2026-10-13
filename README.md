# Kubus

A small proof assistant for cubical type theory, written in Lean 4.

Kubus implements a CCHM-style cubical type theory (De Morgan interval, Kan composition, Glue types) with univalence, higher inductive types and a cumulative universe hierarchy. Type checking is bidirectional; conversion is decided by type-directed normalization by evaluation, and `#eval` prints normal forms.

```
data S1 : U := base | loop (i : I) [i = 0 -> base, i = 1 -> base]

def helix : S1 -> U
  | base => Int
  | loop i => sucPathInt i          -- ua of the successor equivalence

def winding (p : Path S1 base base) : Int := transport (\i -> helix (p i)) (pos zero)

#eval winding (compS1 loopP loopP)   -- pos (suc (suc zero))
```

The library proves, among other things, that the loop space of the circle is the integers (`lib/loopspace.ktt`), and that `Σ (T : U), Equiv T A` is contractible, i.e. univalence (`lib/univalence.ktt`). Transport along these paths computes.

## Normalization by design

The type theory is set up so that every well-typed term has a normal form:

- **Universe hierarchy**: `U n : U (n+1)`, no `U : U`. Universe polymorphism is by displacement: `f^k` is the global `f` with all its universe levels raised by `k`.
- **Strictly positive data types**, no nesting (a type may not occur inside a parameter of another type), and constructor fields must live in the declared universe.
- **Structural recursion only**: pattern-matching definitions may call themselves only on a recursive argument of the matched constructor (possibly applied, for infinitary arguments). Ordinary definitions cannot refer to themselves.
- **Higher inductive types** are eliminated by pattern matching on point and path constructors. Clauses for path constructors are checked against the boundary, and composition is a formal canonical form handled by the eliminator.

The underlying theory is CCHM extended with higher inductive types following Coquand–Huber–Mörtberg. Canonicity is known for CCHM (Huber). Normalization has been proven for closely related cubical type theories (Sterling–Angiuli), but not specifically for this one, and the implementation is not verified.

## Language

`docs/tutorial.md` introduces the language, from paths to univalence and the circle; its examples are checked by the tests.

```
def name (x : A) (i : I) : T := body              -- definitions; (i : I) binds an interval variable
def name {A : U} (x : A) : T := body               -- {A : U} is an implicit argument
def name := body                                   -- the type is inferred
def f (params) : (x : D) -> B                      -- pattern matching
  | c x y => ...
  | p x i => ...                                   -- path constructors bind interval variables
def max : Nat -> Nat -> Nat                        -- several arguments, nested patterns
  | zero, n => n
  | suc m, zero => suc m
  | suc m, suc n => suc (max m n)
data D (params) : U n := c (x : A) | p (x : A) (i : I) [i = 0 -> ..., i = 1 -> ...]
import name                                        -- loads name.ktt (file directory, then KUBUS_PATH)
#eval t                                            -- print the normal form and type of t
#check t
```

Terms: `U`, `U 1`, `(x : A) -> B`, `A -> B`, `(x : A) × B`, `(a, b)`, `p.1`, `p.2`, `\x y -> t`, `\(x : A) -> t`, `let x : A := t in u`, `(t : A)`, and `?` (a hole that reports its goal).

Implicit arguments: `{x : A} -> B` is an implicit Π-type, `\{x} -> t` an implicit lambda. At application sites, implicit arguments are inserted as metavariables and solved by unification (pattern unification, with a first-order fallback): `trans p (sym q)`, `transport (\i -> helix (p i)) x`. They can be given explicitly as `f {a}` or by name as `f {x := a}`, and `@f` takes all arguments explicitly. A term checked against an implicit Π-type gets an implicit lambda inserted. `_` in term position is a metavariable to be solved by unification; an unsolved metavariable is an error. Elaborated core terms are fully explicit: metavariables are replaced by their solutions before a definition is added. Solutions, goals, inferred types and error messages keep definitions folded (`Equiv A B`, not its unfolding).

Pattern matching: clauses `| p1, ..., pn => t` match the first `n` arguments (after the parameters) against nested constructor patterns, variables and `_`; the first matching clause applies. They are compiled to a case tree of single-argument splits (auxiliary definitions `f#n`), checking that every case is covered and every clause is reachable. Recursion is structural: recursive calls are allowed only on a recursive argument of the constructor matched at the root of the case tree (under nested patterns, with the same earlier arguments).

Cubical primitives:

| syntax | meaning |
|---|---|
| `0`, `1`, `~r`, `r /\ s`, `r \/ s` | interval (De Morgan algebra) |
| `Path A a b`, `PathP (\i -> A) a b`, `a ≡ b` | path types; `\i -> t` and `p r` introduce/eliminate |
| `(i : I) -> A` | interval-indexed families without fixed endpoints |
| `[i = 0 -> u, j = 1 /\ k = 0 -> v]` | systems; faces are interval formulas (`r = 1`) |
| `comp i A [φ -> u] u0` | heterogeneous composition (`A`, `u` bind `i`) |
| `hcomp i A [φ -> u] u0` | homogeneous composition |
| `fill i A [φ -> u] u0` | the filler, a path from `u0` to the composition |
| `Glue A [φ -> (T, e)]`, `glue [φ -> t] a`, `unglue g` | Glue types; `e : Equiv T A` |
| `f^k` | `f` with universe levels displaced by `k` |

## Implementation

| file | contents |
|---|---|
| `Kubus/Interval.lean` | De Morgan formulas in canonical DNF, faces, systems |
| `Kubus/Syntax.lean` | core terms (de Bruijn) and surface syntax |
| `Kubus/Value.lean` | semantic values: closures, nominal interval atoms, typed neutrals |
| `Kubus/Eval.lean` | evaluation, nominal substitution, Kan operations for Π, Σ, paths, U, Glue, data and HITs |
| `Kubus/Conv.lean` | type-directed conversion with η for Π, Σ, paths and Glue |
| `Kubus/Quote.lean` | read-back to normal forms and pretty printing |
| `Kubus/Check.lean` | bidirectional elaborator, including checking under faces |
| `Kubus/Match.lean` | pattern matching: compilation to case trees, coverage, termination check |
| `Kubus/Top.lean` | definitions, data types, positivity checks |
| `Kubus/SelfCheck.lean` | invariant self-checks (`--selfcheck`) |
| `Kubus/Lsp.lean` | language server (`--lsp`) |

Evaluation follows the cubicaltt approach: interval variables in values are nominal atoms, and composition is defined by cases on the type. Neutral variables carry their types, so that `p 0` reduces to the endpoint of a neutral path. Composition in the universe produces a Glue-like composite type with an equivalence built from transport along the line. Values of applied globals are glued: they remember the global and its arguments next to the unfolded value, so that they can be printed folded and compared without unfolding when the arguments agree. Transport along a constant closed first-order data type (like `Nat` or `Int`) is the identity definitionally. This regularity holds stably for those types only.

## Usage

```
lake build
KUBUS_PATH=lib .lake/build/bin/kubus lib/loopspace.ktt
tests/run.sh
KUBUS_PATH=lib .lake/build/bin/kubus --interactive lib/loopspace.ktt
```

`kubus --interactive` loads the given files and then reads declarations, `#eval`/`#check` commands and terms (which are evaluated) from standard input; pattern-matching definitions and data types end with an empty line. `#check t` prints the elaborated term (without implicit arguments) and its type.

`tests/run.sh` checks the library, compares `tests/pass/*_test.ktt` against golden outputs, and checks that every file in `tests/fail/` is rejected with the expected error.

## Editor support

`editor/vscode` is a VS Code extension: syntax highlighting for `.ktt` files and a client for the language server `kubus --lsp`, which checks a file on open, change and save. Errors are reported with their source range, `#eval`/`#check` results and the goals of `?` holes as information (a definition with holes is checked to the end and then treated as an opaque constant), and hovering shows the type of the subterm under the cursor. To install:

```
lake build                                  # then put .lake/build/bin on PATH, or set kubus.path
cd editor/vscode && npm install && npm run package
code --install-extension kubus-0.1.0.vsix
```

Imports are found in the file's directory, in `kubus.libraryPath` (default: the workspace's `lib` folder) and in `KUBUS_PATH`.

## Self-checks and fuzzing

`kubus --selfcheck FILE` checks invariants of the evaluator and conversion checker on every definition body, pattern-matching clause, `#eval`/`#check`, path or interval lambda body and system element:

| invariant | check |
|---|---|
| `conv-refl` | every value is convertible to itself, and its type to itself |
| `conv-symmetry` | every conversion check made by the elaborator gives the same answer with the arguments swapped |
| `roundtrip` | `eval (quote v)` is convertible to `v`, both ways |
| `recheck` | the printed normal form parses and elaborates again at the same type, to a value convertible to `v` (for `#eval`, also the printed type) |
| `stability` | for each interval variable `i` in scope and `σ` among `i := 0, 1, ~i, i ∧ j, i ∨ j, k`: `(eval ρ t)σ` is convertible to `eval (ρσ) t` |

Violations are reported with the name of the invariant, and the exit code is 1. Each check has an evaluation budget (`--budget N`, default 1000000 steps); checks exceeding it are skipped and counted (`--verbose` lists them). `--selfcheck-main` checks only the files given on the command line, not their imports. Normal forms containing `compU`/`unglueU` (composition in the universe) have no surface syntax and are not re-checked. `tests/run.sh` runs the library and the passing tests under `--selfcheck`.

`tests/fuzz.sh N SEED` generates `N` random well-typed files over the library (Π, Σ, paths, Glue and `ua`, Bool, Nat, Int, S1, Susp, Trunc, `hcomp`/`comp`/`fill` with systems, composition in the universe, pattern matching on HITs), checks them under `--selfcheck`, and checks that mutated variants (a flipped path boundary, swapped endpoints, a base that disagrees with its system, a glue element that disagrees with its base, a HIT clause that violates its boundary, a type error) are rejected. `tests/fuzz.py --seed SEED --case K --keep DIR` regenerates a single case.

## Certified kernel

`kubus FILE` translates every definition and data type into KubusCore (`KubusCore/Syntax.lean`, `KubusCore/Rules.lean`) after elaboration and checks it with a kernel whose functions return derivations of the specification's judgments, so that a certified signature comes with a proof of `WfSig` (`KubusCore/KERNEL.md`). The Kubus evaluator only helps the elaborator; a definition the kernel rejects is an error (exit code 1), one the translation cannot handle is reported as skipped. `--verbose` lists the certified definitions with their checking times, and `--no-kernel` turns the kernel off. Everything in `lib/` is certified, including `EquivContr` and `loopSpaceS1`; the kernel takes about 2.5 s for `lib/loopspace.ktt` and its imports and well under a second for the other files.

## Verified kernel and consistency

The language is backed by a verified kernel for its core theory, Kubus Core (`docs/core-theory.md`):

- `KubusCore/Syntax.lean`, `KubusCore/Rules.lean`: the formal specification. It has de Bruijn syntax with term and interval variables, the CCHM face lattice, and typing and equality judgments with the Coquand–Huber–Mörtberg (CHM) computation rules for `transp`/`hcomp`, Glue types, universes, and global definitions.
- `KubusCore/Kernel/`: a small kernel whose functions return derivations of the specification's judgments. Its soundness holds by construction (`checkSig_sound`). `kubus FILE` translates the elaborated definitions and certifies them; all of `lib/` is certified.
- `KubusCore/Meta/`: metatheory of the specification (`docs/metatheory.md`). Over the judgments without the primitive structural, presupposition and inversion rules, renaming and substitution (with functionality) are admissible, and so are inversion of type formers and presupposition except for the computation rules whose contractum's typing needs injectivity of type formers.
- `model/`: the cubical-sets model in Lean (with Mathlib). It validates every rule of the specification and proves `KubusCore.Consistent`: in any well-formed signature there is no closed term of `(A : U₀) → A`. `Model.kernel_consistent` combines this with the kernel. Whatever the kernel certifies lives in a consistent theory. Both theorems depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Data types and higher inductive types are in the specification and the kernel (`docs/inductive-types.md`), but not yet in the model.

## Limitations

Pattern matching has no mutual or indexed definitions, and clauses for path constructors cannot use nested patterns or match on further arguments. For higher inductive types with parameters, path-constructor boundaries must be built from the constructor's point arguments and constructors. The evaluator is strict, and some composite Kan operations can still blow up.

## License

MIT
