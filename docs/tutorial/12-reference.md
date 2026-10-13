# 12. Reference

## Declarations

| syntax | meaning |
|---|---|
| `def f (x : A) {y : B} (i : I) : T := t` | a definition, with explicit, implicit and interval parameters |
| `def f := t` | a definition whose type is inferred |
| `def f (ps) : (x : D) -> (y : E) -> T` followed by clauses `\| p, q => t` | pattern matching on the arguments after the parameters |
| `data D (ps) : U n := c (x : A) \| p (x : A) (i : I) [i = 0 -> u, i = 1 -> v]` | a data type, with point and path constructors |
| `import name` | load `name.ktt` from the file's directory or `KUBUS_PATH` |
| `#eval t`, `#check t` | print the normal form and type, or the term and type |

## Terms

| syntax | meaning |
|---|---|
| `U`, `U n` | universes, `U : U 1` |
| `(x : A) -> B`, `A -> B`, `{x : A} -> B` | dependent, non-dependent, implicit function types |
| `\x y -> t`, `\(x : A) -> t`, `\{x} -> t` | functions; `λ` and `fun` work too |
| `f a`, `f {a}`, `f {x := a}`, `@f` | application, implicit application, explicit mode |
| `(x : A) × B`, `A × B`, `(a, b)`, `p.1`, `p.2` | dependent pairs |
| `let x : A := t in u`, `(t : A)` | local definitions and type ascriptions |
| `_`, `?` | a term to be inferred; a hole that reports its goal |
| `f^k` | `f` with its universe levels raised by `k` |
| `-- comment`, `{- comment -}` | comments (block comments nest) |

## Cubical primitives

| syntax | meaning |
|---|---|
| `i : I`, `0`, `1`, `~i`, `i /\ j`, `i \/ j` | interval variables and the De Morgan operations |
| `Path A a b`, `a ≡ b`, `PathP (\i -> A) a b` | path types and dependent path types |
| `\i -> t`, `p r` | path abstraction and application |
| `(i : I) -> A` | interval-indexed families without fixed endpoints |
| `[i = 0 -> u, i = 1 /\ j = 0 -> v]` | systems, defined on faces |
| `hcomp j A [φ -> u] u0` | homogeneous composition: the lid of a box |
| `comp i A [φ -> u] u0` | composition along a line of types |
| `fill i A [φ -> u] u0`, `hfill i A [φ -> u] u0` | the fillers of `comp` and `hcomp`: the box as a path from `u0` to the lid |
| `transp i A [φ] u0` | transport along the line `A`, constant (and the identity) where `φ` holds |
| `Glue A [φ -> (T, e)]`, `glue [φ -> t] a`, `unglue g` | Glue types, with `e : Equiv T A` |

## The command line

| command | |
|---|---|
| `kubus FILE…` | elaborate and certify the files |
| `kubus --interactive [FILE…]` | a REPL |
| `kubus --lsp` | the language server |
| `kubus --no-kernel FILE…` | elaborate only |
| `kubus --selfcheck FILE…` | also check the evaluator's invariants |
| `kubus --doc FILE` | elaboration data as JSON (used to build this site) |
