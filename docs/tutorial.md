# A Kubus tutorial

Kubus is a proof assistant for cubical type theory. This tutorial goes from functions and paths to transport, univalence and the circle. Every `kubus` code block below is checked by `tests/tutorial.py`, and the output blocks after `#eval` and `#check` are what Kubus prints. Part 1 (sections 1–5) is one self-contained file; part 2 (sections 6–7) is a second file that imports the library in `lib/`.

To follow along, build Kubus with `lake build` and either put the code into a file and run `.lake/build/bin/kubus file.ktt`, or type it into `.lake/build/bin/kubus --interactive`. Set `KUBUS_PATH=lib` so that imports find the library.

## 1. Functions and types

`U` is the universe of small types (`U 1` is the next one up, and `U : U 1`). Function types are written `(x : A) -> B` or `A -> B`. A parameter in braces is implicit: it is not written at call sites, but inferred by unification.

```kubus
def id {A : U} (x : A) : A := x
#check id
```

```text
id : {A : U} → A → A
```

Pairs inhabit Σ-types `(x : A) × B`, written `A × B` when `B` does not depend on `x`, with projections `.1` and `.2`. Data types are declared with their constructors, and functions on them are defined by pattern matching.

```kubus
def swap {A B : U} (p : A × B) : B × A := (p.2, p.1)

data Bool : U := false | true

#eval swap (true, false)

def not : Bool -> Bool
  | false => true
  | true => false
```

```text
(false, true)
  : Bool × Bool
```

`#eval t` prints the normal form of `t` and its type. `#check t` prints `t` and its type.

## 2. The interval and paths

The interval `I` is not a type, but a variable `i : I` can be bound. It has endpoints `0` and `1`, and the operations `~i` (reversal), `i /\ j` and `i \/ j` (minimum and maximum), with the laws of a De Morgan algebra.

A path `p : Path A a b` is a function from the interval to `A`, written `\i -> t`, with `p 0 = a` and `p 1 = b`. These endpoints are checked when a path is constructed, and they hold definitionally when a path is applied. Equality in Kubus is this notion of path. The constant path is reflexivity, and reversing the interval gives symmetry:

```kubus
def refl {A : U} (a : A) : Path A a a := \i -> a

def sym {A : U} {a b : A} (p : Path A a b) : Path A b a := \i -> p (~i)

#check sym
#eval sym (refl true)
```

```text
sym : {A : U} → {a b : A} → Path A a b → Path A b a
λ i → true
  : Path Bool true true
```

Functions preserve paths: apply them pointwise. Function extensionality is just as direct, because a path between functions is a function into paths with its arguments swapped:

```kubus
def cong {A B : U} (f : A -> B) {a b : A} (p : Path A a b) : Path B (f a) (f b) :=
  \i -> f (p i)

def funext {A B : U} {f g : A -> B} (h : (x : A) -> Path B (f x) (g x)) : Path (A -> B) f g :=
  \i x -> h x i

def notnot : (b : Bool) -> Path Bool (not (not b)) b
  | false => refl false
  | true => refl true

#check funext notnot
```

```text
funext notnot : Path (Bool → Bool) (λ x → not (not x)) (λ x → x)
```

Many equations hold by computation. Since `~(~i) = i`, reversing twice is the identity definitionally:

```kubus
def symInv {A : U} {a b : A} (p : Path A a b) : Path (Path A a b) (sym (sym p)) p := refl p
```

A dependent path `PathP (\i -> A i) a b` lies over a line of types, from `a : A 0` to `b : A 1`. The connection `i \/ j` contracts a path onto its end point. For each `i`, `\j -> p (i \/ j)` is a path from `p i` to `b`:

```kubus
def toEnd {A : U} {a b : A} (p : Path A a b) : PathP (\i -> Path A (p i) b) p (refl b) :=
  \i j -> p (i \/ j)
```

## 3. Composition

Paths cannot be concatenated by interval operations alone. This is what composition is for. A system `[i = 0 -> u, i = 1 -> v]` is a partial element: it is defined on the faces `i = 0` and `i = 1`, and its elements must agree where faces overlap. `hcomp j A [φ -> u] u0` takes a base `u0 : A` and sides `u` (which depend on `j`, and agree with `u0` at `j = 0`), and returns the lid of the box, at `j = 1`. To concatenate `p` and `q`, take `p` as the base and `q` as the side at `i = 1`:

```kubus
def trans {A : U} {a b c : A} (p : Path A a b) (q : Path A b c) : Path A a c :=
  \i -> hcomp j A [i = 0 -> a, i = 1 -> q j] (p i)
```

`fill j A [φ -> u] u0` is the whole box, a path from `u0` to the lid. `comp i A [φ -> u] u0` is composition along a line of types `A`, which may depend on `i`.

## 4. Transport

Composition with an empty system transports along a line of types. A path between types is such a line:

```kubus
def transport {A B : U} (p : Path U A B) (a : A) : B := comp i (p i) [] a

def subst {A : U} (P : A -> U) {a b : A} (p : Path A a b) (x : P a) : P b :=
  transport (\i -> P (p i)) x
```

Transport along a constant line is the identity only up to a path. The filler gives it:

```kubus
def transportRefl {A : U} (x : A) : Path A (transport (\i -> A) x) x :=
  \i -> comp j A [i = 1 -> x] x
```

The library derives the eliminator `J` from transport and the contractibility of singletons (`lib/basic.ktt`).

## 5. Data types and recursion

Pattern matching can cover several arguments and nested patterns. The clauses are tried in order, and Kubus checks that every case is covered and every clause is reachable.

```kubus
data Nat : U := zero | suc (n : Nat)

def add : Nat -> Nat -> Nat
  | zero, n => n
  | suc m, n => suc (add m n)

def two : Nat := suc (suc zero)
#eval add two two
```

```text
suc (suc (suc (suc zero)))
  : Nat
```

Proofs about recursive functions are recursive functions into path types:

```kubus
def addZero : (n : Nat) -> Path Nat (add n zero) n
  | zero => refl zero
  | suc n => \i -> suc (addZero n i)
```

Recursion must be structural: a recursive call is allowed only on an argument of the constructor matched at the root of the case tree, so `suc (suc n) => f n` is rejected. This guarantees that every term has a normal form. Definitions by `:=` cannot refer to themselves.

## 6. Equivalences, Glue and univalence

Part 2 uses the library. `lib/equiv.ktt` defines equivalences (functions with contractible fibers) and builds them from isomorphisms. `lib/bool.ktt` proves `notnot` and the other lemmas about `Bool` from part 1.

```kubus
import bool
import loopspace

#check Equiv
#check isoToEquiv

def notEquiv : Equiv Bool Bool := isoToEquiv not not notnot notnot
```

```text
Equiv : U → U → U
isoToEquiv : {A B : U} → (f : A → B) → (g : B → A) → section f g → retract f g → Equiv A B
```

Univalence turns an equivalence into a path between types. Kubus implements it with Glue types. `Glue A [φ -> (T, e)]` is a type that is `T` on the faces `φ`, and `A` elsewhere, with `e : Equiv T A` describing how it is glued. The library's `ua` glues `A` at `i = 0` and `B` at `i = 1` onto `B`:

```kubus-lib
def ua {A B : U} (e : Equiv A B) : Path U A B :=
  \i -> Glue B [i = 0 -> (A, e), i = 1 -> (B, idEquiv B)]
```

Transport along `ua e` computes, and applies `e`:

```kubus
def notPath' : Path U Bool Bool := ua notEquiv
#eval transport notPath' true
#eval transport (\i -> notPath' (~i)) true
```

```text
false
  : Bool
false
  : Bool
```

`glue` and `unglue` introduce and eliminate elements of Glue types. On the faces of the system, a Glue type reduces to the glued type:

```kubus
def G (i : I) : U := Glue Bool [i = 0 -> (Bool, notEquiv), i = 1 -> (Bool, idEquiv Bool)]
def g0 (b : G 0) : Bool := b
def unglueG (i : I) (x : G i) : Bool := unglue x
```

The full univalence axiom holds in the form "the type of types equivalent to `A` is contractible" (`EquivContr` in `lib/univalence.ktt`). It is certified by the verified kernel, which checks every definition, together with the rest of `lib/`.

## 7. Higher inductive types: the circle

A higher inductive type has path constructors, which take interval arguments and have a boundary. The circle (`lib/circle.ktt`) is a point with a loop:

```kubus-lib
data S1 : U := base | loop (i : I) [i = 0 -> base, i = 1 -> base]

def loopP : Path S1 base base := \i -> loop i
```

```kubus
#check loopP
```

```text
loopP : Path S1 base base
```

A function out of a higher inductive type gives a clause for each constructor, and the clause for `loop i` must agree with the clause for `base` at `i = 0` and `i = 1`. The universal cover of the circle sends `base` to the integers and `loop` to the path given by the successor equivalence. Transporting `pos zero` along `helix` counts how often a loop winds around the circle:

```kubus-lib
def helix : S1 -> U
  | base => Int
  | loop i => sucPathInt i

def winding (p : Path S1 base base) : Int := transport (\i -> helix (p i)) (pos zero)
```

```kubus
#eval winding (trans loopP (trans loopP loopP))
#eval winding (sym loopP)
```

```text
pos (suc (suc (suc zero)))
  : Int
negsuc zero
  : Int
```

`lib/loopspace.ktt` proves that the loop space of the circle is the integers. The proof uses an encode-decode argument and `J`, and then `isoToPath`. Transport along the resulting path computes in both directions. A path between types lives in `U 1`, so reversing it needs `sym` one universe up. `sym^1` is `sym` with all universe levels raised by one:

```kubus
#check loopSpaceS1
#eval transport loopSpaceS1 (trans loopP loopP)
#eval transport (sym^1 loopSpaceS1) (negsuc zero)
```

```text
loopSpaceS1 : Path U (Path S1 base base) Int
pos (suc (suc zero))
  : Int
λ i → hcomp k S1 [i = 0 -> base, i = 1 -> base] (hcomp k S1 [i = 0 -> base, i = 1 -> base] (loop ~i))
  : Path S1 base base
```

## Where to go next

The library files are short and are worth reading in order: `basic`, `equiv`, `univalence`, `int`, `circle`, `loopspace`, `hits` (propositional truncation and suspensions). The README describes the full syntax, the self-checks and the verified kernel. The editor support in `editor/vscode` shows goals of `?` holes and types on hover.
