# 8. Equivalences, Glue and univalence

The univalence principle says that equivalent types are equal: an equivalence `e : Equiv A B` gives a path `ua e : Path U A B`, and every path between types arises this way. In Kubus, `ua` is a definition, and transport along `ua e` computes to `e`.

## Equivalences

A type is *contractible* if it has an element to which every element is connected by a path. A function is an *equivalence* if each of its fibers is contractible:

```kubus-lib equiv isContr fiber isEquiv Equiv
```

The identity is an equivalence, and so is every function with an inverse up to paths (an isomorphism); the library proves the latter in `lemIso`:

```kubus
import bool

#check isoToEquiv

def notEquiv : Equiv Bool Bool := isoToEquiv not not notnot notnot
```

## Glue types

To turn an equivalence into a path of types, we need a line of types that is `A` at one end and `B` at the other. *Glue types* build such lines. `Glue B [φ -> (T, e)]` is a type that

- is `T` on the faces `φ`,
- and elsewhere is `B`, with the elements of `T` glued on along the equivalence `e : Equiv T B`.

With `φ = (i = 0 \/ i = 1)`, gluing `A` along `e` at `i = 0` and `B` along the identity at `i = 1` gives exactly the line we want:

```kubus-lib equiv ua
```

On the faces, the Glue type reduces to the glued type, so the endpoints are right by computation:

```kubus
def G (i : I) : U := Glue Bool [i = 0 -> (Bool, notEquiv), i = 1 -> (Bool, idEquiv Bool)]

def g0 (b : Bool) : G 0 := b
def g1 (b : Bool) : G 1 := b
```

Elements of Glue types are introduced with `glue` and eliminated with `unglue`, which maps a glued element to the base `B`:

```kubus
def toBase (i : I) (x : G i) : Bool := unglue x
```

## Transport along `ua` computes

Composition in a Glue type is defined in terms of composition in the base and the equivalence (it is the most intricate case of the evaluator). The upshot: transporting along `ua e` applies `e`.

```kubus
#eval transport (ua notEquiv) true
#eval transport (ua notEquiv) false
#eval transport (sym^1 (ua notEquiv)) true
```

Transporting backwards (along the reversed path; the `^1` is explained in chapter 10) applies the inverse. In general, transport along `ua e` agrees with `e` up to a path, by unglueing the filler of the transport:

```kubus-lib equiv uaβ
```

## The univalence axiom, as a theorem

`ua` gives one direction of univalence. The full statement says that `ua` is an equivalence, or equivalently that for each type `A` the type of types `T` with an equivalence `T ≃ A` is contractible: there is essentially only one such pair, `(A, idEquiv A)`. The proof glues `A` along the given equivalence and shows that `unglue` is an equivalence:

```kubus
import univalence

#check EquivContr
```

The proof is in [lib/univalence.ktt](../lib/univalence.html#EquivContr). Like everything else in the library, it is certified by the kernel.
