# 7. Data types and recursion

## Declaring data types

A data type declaration gives the type's parameters, its universe, and its constructors, each with named arguments:

```kubus
import basic

data Nat : U := zero | suc (n : Nat)

data List (A : U) : U := nil | cons (x : A) (xs : List A)
```

Data types must be *strictly positive*: the type being defined may appear in a constructor argument only as the result of a function type, never to the left of an arrow. Without this restriction one could write non-terminating programs:

```kubus fails
data Bad : U := mk (f : Bad -> Nat)
```

## Pattern matching

Functions out of a data type are defined by pattern matching. Clauses can match several arguments, and patterns can be nested; the clauses are tried from top to bottom, `_` matches anything, and a variable matches anything and names it:

```kubus
def add : Nat -> Nat -> Nat
  | zero, n => n
  | suc m, n => suc (add m n)

def pred : Nat -> Nat
  | zero => zero
  | suc n => n

def isZero : Nat -> Nat -> Nat
  | zero, _ => suc zero
  | _, _ => zero

def max : Nat -> Nat -> Nat
  | zero, n => n
  | suc m, zero => suc m
  | suc m, suc n => suc (max m n)

def two : Nat := suc (suc zero)
#eval max two (add two two)
```

Kubus compiles the clauses to a tree of case distinctions on one argument at a time, which is what the core language and the kernel understand. On the way it checks that every case is covered:

```kubus fails
def partial : Nat -> Nat -> Nat
  | zero, zero => zero
  | suc m, n => n
```

and that every clause can be reached:

```kubus fails
def redundant : Nat -> Nat
  | zero => zero
  | n => n
  | suc n => n
```

Parameters of a data type are inferred at constructors, and functions can take parameters before the matched arguments:

```kubus
def length {A : U} : List A -> Nat
  | nil => zero
  | cons _ xs => suc (length xs)

def map {A B : U} (f : A -> B) : List A -> List B
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

#eval map (add two) (cons zero (cons two nil))
#eval length (cons zero (cons two nil))
```

## Structural recursion, and why

A function may call itself only on a *structurally smaller* argument: a recursive argument of the constructor matched at the root of the case tree. `add m n` in the clause for `suc m` is fine. But Kubus rejects a call on anything else, even on a deeper subterm:

```kubus fails
def half : Nat -> Nat
  | zero => zero
  | suc zero => zero
  | suc (suc n) => suc (half n)
```

The restriction keeps the theory *normalizing*: every term reduces to a normal form, and every closed term of a data type to a constructor. Together with universe stratification and strict positivity, this is what makes type checking decidable and `#eval` meaningful. The kernel itself knows no recursion at all: it works with eliminators, and the elaborator's case trees translate to them, which is exactly what structural recursion allows. (`half` can be written with an auxiliary function that returns a pair.)

## Proofs by induction

A proof by induction is a recursive function into a family of path types:

```kubus
def addZero : (n : Nat) -> Path Nat (add n zero) n
  | zero => refl zero
  | suc n => \i -> suc (addZero n i)
```

The recursive call `addZero n` is the induction hypothesis, a path from `add n zero` to `n`, and `\i -> suc (addZero n i)` applies `suc` to it pointwise. (Constructors are not functions on their own: `cong suc` would need `\(m : Nat) -> suc m`.)
