# 9. Higher inductive types

A higher inductive type has *path constructors* as well as point constructors. A path constructor takes interval arguments, and its *boundary* says what it is on the faces.

## The circle

The circle has a point `base` and a loop that starts and ends at `base`:

```kubus-lib circle S1 loopP
```

`loop` takes an interval argument; `loopP` packages it as a path.

```kubus
import loopspace

#check loopP
#eval loop 0
```

## Functions out of the circle

A function out of a higher inductive type has a clause for each constructor. The clause for a path constructor must agree with the clauses for its boundary, which Kubus checks. To map the circle to itself, send `base` somewhere and `loop i` to a loop there:

```kubus
def double : S1 -> S1
  | base => base
  | loop i => trans loopP loopP i
```

A clause that does not respect the boundary is rejected:

```kubus fails
def broken : S1 -> Int
  | base => pos zero
  | loop i => negsuc zero
```

## The universal cover and winding numbers

The universal cover of the circle sends `base` to the integers and `loop` to the path `Int = Int` given by the successor equivalence (`sucPathInt`, made with `ua`). Transporting `pos zero` along the lift of a loop counts how often the loop winds around the circle:

```kubus-lib circle helix winding
```

and because `ua` computes, so does `winding`:

```kubus
#eval winding loopP
#eval winding (trans loopP (trans loopP loopP))
#eval winding (trans (sym loopP) (sym loopP))
#eval winding (\i -> double (loop i))
```

## The loop space of the circle is the integers

`lib/loopspace.ktt` proves that the type of loops at `base` is equal to `Int`, by an encode-decode argument and `isoToPath`:

```kubus
#check loopSpaceS1
#eval transport loopSpaceS1 (trans loopP loopP)
```

Transport along this path in the other direction turns an integer into a loop (again with `sym^1`, chapter 10):

```kubus
#eval transport (sym^1 loopSpaceS1) (negsuc zero)
```

## Truncations and suspensions

Higher inductive types can have parameters. The propositional truncation of `A` has the elements of `A` and a path between any two elements; the suspension of `A` has two points and a path between them for every element of `A`:

```kubus-lib hits Trunc truncIsProp truncRec Susp
```

Functions on parameterized higher inductive types are defined the same way:

```kubus
import hits

def boolToSusp : Bool -> Susp Bool
  | false => north
  | true => south

#check suspMap not
```

Kubus does not yet support boundaries that apply functions to the constructor's arguments, so pushouts and general colimits cannot be declared directly yet.
