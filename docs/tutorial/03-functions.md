# 3. Functions, pairs and implicit arguments

This chapter covers the part of Kubus that is ordinary dependent type theory: universes, functions, pairs, data types, and how implicit arguments are inferred.

## Universes and functions

Types are terms whose type is a universe. `U` (short for `U 0`) is the universe of small types; `U 1` contains `U`, and so on (chapter 10). The dependent function type is written `(x : A) -> B`, or `A -> B` when `B` does not mention `x`; `→` works as well. Functions are written `\x -> t` (or `λ x → t`), and a definition can take its arguments before the colon:

```kubus
def const (A B : U) (a : A) (b : B) : A := a

def flip (A B C : U) (f : A -> B -> C) : B -> A -> C := \b a -> f a b
```

## A first data type

A data type lists its constructors, and functions out of it are defined by pattern matching, one clause per constructor:

```kubus
data Bool : U := false | true

def not : Bool -> Bool
  | false => true
  | true => false
```

## Implicit arguments

Writing `A B` at every use of `const` is tedious, since they can be read off the other arguments. Arguments in braces are *implicit*: they are omitted at use sites, and Kubus fills them in by unification.

```kubus
def id {A : U} (x : A) : A := x

def compose {A B C : U} (g : B -> C) (f : A -> B) : A -> C := \x -> g (f x)

#check compose not not
```

An implicit argument can still be given explicitly, positionally as `f {a}` or by name as `f {A := a}`, and `@f` turns all of `f`'s implicit arguments into explicit ones:

```kubus
#check id {Bool} true
#check compose {A := Bool} not not
#check @id Bool true
```

`_` is a placeholder for any term that Kubus should infer, and a definition without a type gets the type of its body:

```kubus
def yes := id {_} true
#check yes
```

If unification cannot determine an implicit argument, Kubus says which one:

```kubus fails
def nope := id
```

## Pairs

Dependent pairs `(x : A) × B` have the projections `.1` and `.2`; `A × B` is the non-dependent case. A pair is written `(a, b)`.

```kubus
def swap {A B : U} (p : A × B) : B × A := (p.2, p.1)

def Pointed : U 1 := (A : U) × A
```

## More pattern matching

Pattern matching can look at several arguments at once; `_` matches anything:

```kubus
def and : Bool -> Bool -> Bool
  | true, b => b
  | false, _ => false

#eval swap (not true, and true true)
```

`#eval` prints the normal form of a term together with its type. Chapter 7 covers data types and recursion in depth.

## Local definitions

`let x : A := t in u` names an intermediate result, and `(t : A)` annotates a term with a type:

```kubus
def nand (a b : Bool) : Bool :=
  let c : Bool := and a b in
  not c

#eval (nand true false : Bool)
```
