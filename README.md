# Kubus

A small proof assistant for cubical type theory, written in Lean 4.

Kubus implements a CCHM-style cubical type theory (De Morgan interval, Kan composition, Glue types) with univalence, higher inductive types and a cumulative universe hierarchy. Type checking is bidirectional; conversion is decided by type-directed normalization by evaluation, and `#eval` prints normal forms.

```
data S1 : U := base | loop (i : I) [i = 0 -> base, i = 1 -> base]

def helix : S1 -> U
  | base => Int
  | loop i => sucPathInt i          -- ua of the successor equivalence

def winding (p : Path S1 base base) : Int := transport Int Int (\i -> helix (p i)) (pos zero)

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

```
def name (x : A) (i : I) : T := body              -- definitions; (i : I) binds an interval variable
def f (params) : (x : D) -> B                      -- pattern matching on the last argument
  | c x y => ...
  | p x i => ...                                   -- path constructors bind interval variables
data D (params) : U n := c (x : A) | p (x : A) (i : I) [i = 0 -> ..., i = 1 -> ...]
import name                                        -- loads name.ktt (file directory, then KUBUS_PATH)
#eval t                                            -- print the normal form and type of t
#check t
```

Terms: `U`, `U 1`, `(x : A) -> B`, `A -> B`, `(x : A) × B`, `(a, b)`, `p.1`, `p.2`, `\x y -> t`, `\(x : A) -> t`, `let x : A := t in u`, `(t : A)`, and `?` (a hole that reports its goal).

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
| `Kubus/Top.lean` | definitions, data types, termination and positivity checks |

Evaluation follows the cubicaltt approach: interval variables in values are nominal atoms, and composition is defined by cases on the type. Neutral variables carry their types, so that `p 0` reduces to the endpoint of a neutral path. Composition in the universe produces a Glue-like composite type with an equivalence built from transport along the line. Transport along a constant closed first-order data type (like `Nat` or `Int`) is the identity definitionally. This regularity holds stably for those types only.

## Usage

```
lake build
KUBUS_PATH=lib .lake/build/bin/kubus lib/loopspace.ktt
tests/run.sh
```

`tests/run.sh` checks the library, compares `tests/pass/*_test.ktt` against golden outputs, and checks that every file in `tests/fail/` is rejected with the expected error.

## Limitations

All arguments are explicit; there are no implicit arguments or unification. Pattern matching covers one argument, with no nested patterns and no mutual or indexed definitions. For higher inductive types with parameters, path-constructor boundaries must be built from the constructor's point arguments and constructors. The evaluator is strict, and some composite Kan operations can still blow up.
