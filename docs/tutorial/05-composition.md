# 5. Composition

Interval expressions give reversal and connections, but not concatenation of paths. For that, every type comes with a *Kan composition* operation: given an open box, it computes the missing lid.

## Systems

A *system* `[φ1 -> u1, φ2 -> u2]` is a term that is only defined on some faces of a cube: `i = 0` is the face where the interval variable `i` is `0`, and faces can be combined with `/\` and `\/`. The elements of a system must agree where their faces overlap, which Kubus checks.

## Homogeneous composition

`hcomp j A [φ -> u] u0` takes

- a base `u0 : A`,
- sides `u` defined on the faces `φ`, which depend on a new variable `j`, and agree with the base at `j = 0`,

and returns the lid at `j = 1`, which agrees with the sides on the faces `φ`. To concatenate `p` and `q`, take `p i` as the base and extend it by `q` on the face `i = 1` (on the face `i = 0` the side stays at `a`):

```kubus
import basic

def concat {A : U} {a b c : A} (p : Path A a b) (q : Path A b c) : Path A a c :=
  \i -> hcomp j A [i = 0 -> a, i = 1 -> q j] (p i)
```

This is `trans` in the library. The same idea composes three paths at once, with `q` as the base and `p` reversed on the left:

```kubus
def doubleComp {A : U} {a b c d : A} (p : Path A a b) (q : Path A b c) (r : Path A c d) : Path A a d :=
  \i -> hcomp j A [i = 0 -> p (~j), i = 1 -> r j] (q i)
```

The sides must start where the base is. Here the side at `i = 1` starts at `c`, but the base is at `b` there:

```kubus fails
def bad {A : U} {a b c : A} (p : Path A a b) (q : Path A b c) : Path A a c :=
  \i -> hcomp j A [i = 0 -> a, i = 1 -> q (~j)] (p i)
```

## Fillers

`hfill j A [φ -> u] u0` is the whole box: a path from the base `u0` to the lid of `hcomp`. With it, the composite comes with a square that relates it to its parts. Here, the square has `p` at the bottom, `trans p q` at the top, and `q` on the right:

```kubus
def transSquare {A : U} {a b c : A} (p : Path A a b) (q : Path A b c)
  : PathP (\i -> Path A a (q i)) p (trans p q) :=
  \i j -> hfill k A [j = 0 -> a, j = 1 -> q k] (p j) i
```

Squares like this one prove the laws of path algebra. The library proves that `refl` is a unit for `trans` on both sides:

```kubus-lib basic rUnit lUnit
```

## Heterogeneous composition

`comp i A [φ -> u] u0` composes along a *line of types* `A`, which may depend on `i`: the base lives in `A` at `i = 0`, the lid in `A` at `i = 1`, and the sides in `A` at `i`; `fill` is its filler. Kubus defines `comp` from `hcomp` and *transport* `transp i A [φ] u0`, which carries `u0` along the line `A` and is the identity where `φ` holds (the line must be constant there). With an empty system, `comp` is transport, the subject of the next chapter.

## How composition computes

`hcomp` and `transp` are not primitives with a mysterious meaning: they compute by cases on the type, by the rules of Coquand, Huber and Mörtberg. In a function type they work pointwise, in a pair type componentwise, in a path type by adding the path's endpoints to the system, in a data type without path constructors constructor-wise (a higher inductive type has formal compositions as elements), and in Glue types and the universe by the constructions that make univalence work. The elaborator's evaluator implements exactly the rules of the kernel's specification. Chapter 8 shows transport along `ua` computing through these rules.
