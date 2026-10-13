# 10. Universes and displacement

## A hierarchy of universes

`U` is the universe of small types, and `U` itself is a type in the next universe `U 1`, which is in `U 2`, and so on. There is no `U : U`: such a universe makes the theory inconsistent (Girard's paradox), and Kubus rejects it:

```kubus fails
def typeInType : U := U
```

Universes are *cumulative*: a type in `U` is also a type in `U 1`.

```kubus
import bool

def Bool' : U 1 := Bool

def Types : U 1 := (A : U) × A
```

Levels are bounded: Kubus has the universes `U 0` to `U 4`. This keeps the consistency proof within Lean's own universes, without assuming large cardinals, and is plenty for the library.

## Universe polymorphism by displacement

Definitions like `refl` are stated for types `A : U`. Paths between types live one level up, since `U : U 1`, so `refl` cannot be applied to `Bool` as an element of `U`:

```kubus fails
def reflBool : Path U Bool Bool := refl Bool
```

Instead of quantifying over universe levels, Kubus uses *displacement* (after McBride): `f^k` is the global `f` with every universe level in its definition raised by `k`. `refl^1` is `refl` for types in `U 1`, so it applies to `Bool : U`:

```kubus
def reflBool : Path U Bool Bool := refl^1 Bool

#check refl^1
#check sym^1 notPath
```

Displacement is how univalence is stated: `EquivContr A` says that a type in `U 1` is contractible, using `isContr` displaced by one (chapter 8). It is also why transporting backwards along a path of types uses `sym^1` (chapter 9). A definition cannot be displaced inside its own definition, so displacement adds no new kinds of recursion.
