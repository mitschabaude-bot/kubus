# 4. The interval and paths

In cubical type theory, a proof that `a` equals `b` is a *path* from `a` to `b`: a function out of an abstract interval `I`, whose value at `0` is `a` and whose value at `1` is `b`. Everything about equality, from symmetry to function extensionality and univalence, follows from this one idea.

## The interval

`I` is not a type: you cannot form `I -> I` or pairs of interval points. But you can bind a variable `i : I` in a lambda or a definition, and interval expressions are built from

- the endpoints `0` and `1`,
- reversal `~i`,
- minimum `i /\ j` and maximum `i \/ j`,

subject to the laws of a De Morgan algebra: `~0 = 1`, `~(~i) = i`, `~(i /\ j) = ~i \/ ~j`, `i /\ 0 = 0`, `i \/ 1 = 1`, and so on. Kubus decides equality of interval expressions, so all of these hold by computation.

## Paths

`Path A a b` is the type of paths in `A` from `a` to `b`. A path is introduced by an interval lambda `\i -> t`, and applied to an interval expression: `p i`. The endpoints are part of the type, so `p 0` *computes* to `a`, even when `p` is a variable. The simplest path is constant:

```kubus
def refl {A : U} (a : A) : Path A a a := \i -> a
```

Reversing the interval reverses a path, and applying a function pointwise maps a path:

```kubus
def sym {A : U} {a b : A} (p : Path A a b) : Path A b a := \i -> p (~i)

def cong {A B : U} (f : A -> B) {a b : A} (p : Path A a b) : Path B (f a) (f b) :=
  \i -> f (p i)
```

Kubus checks the endpoints. A lambda whose ends do not match the type is rejected, with the face that fails:

```kubus fails
def notSym {A : U} {a b : A} (p : Path A a b) : Path A b a := \i -> p i
```

Because `~(~i)` is `i`, reversing twice gives back the same path, and the proof is `refl`:

```kubus
def symInv {A : U} {a b : A} (p : Path A a b) : Path (Path A a b) (sym (sym p)) p := refl p
```

## Function extensionality

Two functions are equal if they are pointwise equal. In most type theories this is an axiom; here it is a one-line program, because a path between functions and a function into paths are the same thing with the arguments swapped:

```kubus
def funext {A B : U} {f g : A -> B} (h : (x : A) -> Path B (f x) (g x)) : Path (A -> B) f g :=
  \i x -> h x i
```

For example, double negation on the booleans is equal to the identity function:

```kubus
data Bool : U := false | true

def not : Bool -> Bool
  | false => true
  | true => false

def notnot : (b : Bool) -> Path Bool (not (not b)) b
  | false => refl false
  | true => refl true

#check funext notnot
```

## Dependent paths

`PathP (\i -> A) a b` is a path over a line of types: `A` may mention `i`, and the path goes from `a : A[0/i]` to `b : A[1/i]`. `Path A a b` is the special case of a constant line. The connections `i /\ j` and `i \/ j` give squares for free; for instance, as `i` goes from 0 to 1, the path `\j -> p (i \/ j)` shrinks from `p` to the constant path at `b`:

```kubus
def toEnd {A : U} {a b : A} (p : Path A a b) : PathP (\i -> Path A (p i) b) p (refl b) :=
  \i j -> p (i \/ j)
```

Paths in Σ-types are pairs of paths, the second one dependent:

```kubus
def sigmaPath {A : U} {B : A -> U} {u v : (x : A) × B x}
    (p : Path A u.1 v.1) (q : PathP (\i -> B (p i)) u.2 v.2) : Path ((x : A) × B x) u v :=
  \i -> (p i, q i)
```

## Singletons are contractible

A path from `a` to `b`, together with its end point `b`, can be contracted to `a` and the constant path. The square that does it is again a connection:

```kubus
def contr {A : U} {a b : A} (p : Path A a b)
  : Path ((x : A) × Path A a x) (a, refl a) (b, p) :=
  \i -> (p i, \j -> p (i /\ j))
```

This fact is the basis of the path induction principle `J` (chapter 6). What paths cannot do on their own is compose: from `p : Path A a b` and `q : Path A b c` no interval expression gives a path from `a` to `c`. That needs a new operation, the subject of the next chapter.
