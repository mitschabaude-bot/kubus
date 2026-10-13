# 6. Transport and path induction

A path between types is a line of types, and composition along a line of types with an empty system moves an element from one end to the other. This is *transport*, and from it follows the induction principle for paths.

## Transport

```kubus-lib basic transport
```

`comp i (p i) [] a` composes along the line `p` with no sides at all: the result is `a` carried over to the other end. Transport along a family of types over a path is *substitution*, the principle that equal elements have the same properties:

```kubus
import basic

def subst {A : U} (P : A -> U) {a b : A} (p : Path A a b) (x : P a) : P b :=
  transport (\i -> P (p i)) x
```

What does transport along a constant line do? For a data type without parameters, like the booleans, it is the identity, by computation:

```kubus
data Bool : U := false | true

#eval transport (\i -> Bool) true
```

For an arbitrary type `A`, transport along the constant line is not the identity by computation, but it is equal to it by a path. The filler of the composition gives that path, with the constant side at `i = 1`:

```kubus-lib basic transportRefl
```

## Path induction

The induction principle for paths, `J`, says: to prove something about every path `p` from a fixed `a` to some `x`, it suffices to prove it for `refl a`. In cubical type theory, `J` is not a primitive; it is transport along the contraction of singletons from chapter 4:

```kubus-lib basic singl contrSingl J
```

Its computation rule holds up to a path, again by `transportRefl`:

```kubus-lib basic JRefl
```

`J` derives the usual properties of paths. Symmetry, for example:

```kubus
def symJ {A : U} {a b : A} (p : Path A a b) : Path A b a :=
  J (\x q -> Path A x a) (refl a) p
```

`J` takes the *motive* `\x q -> Path A x a`, a family of types over the end point `x` and the path `q`, and the case `refl a`. The implicit arguments `A` and `a` and the end point `x` are found by unification (higher-order pattern unification, for the motive's type).

In practice, the cubical operations are often more direct than `J`: `sym` is a one-line interval lambda, and many equations hold by computation that `J` would only give up to a path.

## Transport in families computes

Transport is defined by cases on the line of types, so it computes in function types, pair types and path types too. Transporting a pair transports its components:

```kubus
def Pair : U := Bool × Bool

def moved : Pair := transport (\i -> Pair) (true, false)
#eval moved
```
