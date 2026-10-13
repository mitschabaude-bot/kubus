# 1. What Kubus is

Kubus is a proof assistant for **cubical type theory**: a dependent type theory in which equality is a *path*, a function out of an interval, and in which univalence and higher inductive types are not axioms but definitions that compute.

Three things set it apart.

**Univalence computes.** Equivalent types are equal (`ua`), and transporting along that equality runs the equivalence. This is not an axiom that blocks evaluation, as in Book HoTT: it is a theorem with computational content, proved in [the library](../lib/univalence.html).

**Higher inductive types compute.** The circle is a data type with a point and a loop. The loop space of the circle is the integers, and the winding number of a loop is a program that you can run:

```kubus
import loopspace

#eval winding (trans loopP (trans loopP loopP))
#eval winding (trans loopP (sym loopP))
```

**A verified kernel and a consistency proof.** Every definition is certified by a small kernel that does not just say "yes": it returns a derivation in a formal specification of the theory, written in Lean. A model of that specification in cubical sets, also in Lean, proves that no closed term of the empty type `(A : U) -> A` exists. You do not have to trust the elaborator, the evaluator, or this website. You have to read the specification and two theorem statements ([chapter 11](11-trust.html)).

## What you will learn

This tutorial introduces the language from the ground up and assumes some familiarity with a functional language or another proof assistant, but no knowledge of cubical type theory.

- Chapters 2–3: getting started, functions and implicit arguments.
- Chapters 4–6: the interval, paths, composition and transport, the heart of cubical type theory.
- Chapter 7: data types and structural recursion.
- Chapters 8–9: univalence through Glue types, and higher inductive types: the circle, truncations and suspensions.
- Chapter 10: universes and universe displacement.
- Chapter 11: what is verified, and what you need to read to trust it.
- Chapter 12: a syntax reference.

Every code block on this site is checked by Kubus when the site is built, and every declaration in it is certified by the kernel (marked ✓). Hover over a name to see its type; click it to go to its definition.

## Where Kubus comes from

Kubus implements a variant of the cubical type theory of Cohen, Coquand, Huber and Mörtberg (CCHM), with a De Morgan interval, Kan composition, Glue types, and higher inductive types following Coquand, Huber and Mörtberg. Its evaluator follows [cubicaltt](https://github.com/mortberg/cubicaltt); its surface language is close to [Cubical Agda](https://agda.readthedocs.io/en/latest/language/cubical.html). What is new is the verification: the kernel, the specification and the model are all developed in [Lean 4](https://lean-lang.org).
