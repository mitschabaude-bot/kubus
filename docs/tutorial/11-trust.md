# 11. Trust: the kernel and the consistency proof

What does it mean that Kubus accepts a proof? This chapter explains what is verified, how, and what you need to read to trust it.

## Three layers

```text
                          ┌── KubusCore/Kernel: returns derivations ──┐
.ktt ── elaborator ── bridge ──────────────────────────────────────────┴─→ WfSig S
       (Kubus/)                                                              │
                                                     model/: Consistent ─────┴─→ no closed term of (A : U₀) → A
```

**The elaborator** (`Kubus/`) turns the surface language into fully explicit core terms: it inserts implicit arguments, compiles pattern matching to case trees, and checks types with its own evaluator (normalization by evaluation, following cubicaltt). It is large and fast, and it is *not* trusted.

**The kernel** (`KubusCore/Kernel/`) checks the core terms against the *specification* of the theory: a definition of the typing and equality judgments as inductive relations in Lean (`KubusCore/Syntax.lean`, `KubusCore/Rules.lean`). Every kernel function returns a derivation of the judgment it checks, so a signature that the kernel accepts comes with a Lean proof that it is well formed (`WfSig S`). The kernel's code does not need to be read: its soundness holds by construction. `kubus FILE` runs the kernel on every definition and data type; on this site, a ✓ marks each certified declaration.

**The model** (`model/`, built on Mathlib) interprets the specification in cubical sets and validates every rule. The theorem `Model.kernel_consistent0` states that if the kernel accepts a signature, there is no closed term of `(A : U₀) → A` over it. It depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and CI checks this on every push.

## What you need to read

To trust a Kubus development, you need to read neither the elaborator, nor the kernel, nor the proofs. You need to read

1. the syntax and the definitions the rules mention (`KubusCore/Syntax.lean`),
2. the rules in their textbook form (`KubusCore/Meta/Minimal.lean`), without primitive weakening, substitution or inversion rules, which are proven admissible,
3. the two statements in `model/Model/Minimal.lean`: consistency of the minimal judgments, and consistency of what the kernel accepts,
4. the signature of `Kernel.checkSig`, which returns a proof of well-formedness.

[docs/metatheory.md](https://github.com/mitschabaude-bot/kubus/blob/main/docs/metatheory.md) lists exactly what to read, with file and definition names.

## What the model found

A specification of a type theory with this many rules is easy to get wrong, and the model found out. Building it turned up seventeen bugs in earlier versions of the specification, recorded in [model/README.md](https://github.com/mitschabaude-bot/kubus/blob/main/model/README.md). Most were rules that no model could validate as stated, for instance because a rule read a list of terms syntactically without a premise that it is a list. Three made the theory inconsistent. In one of them, the boundary of a path constructor was checked against the declaration that it was part of: the check could use the constructor's own boundary rule, and so accepted ill-typed boundaries. A two-constructor data type, transported along `ua not`, then proved `false = true`. The fix checks each constructor against the declaration truncated to the constructors before it.

A kernel proven sound for an inconsistent specification certifies nothing, which is the point of the exercise: a proof assistant is only as trustworthy as the rules it implements, and those rules need a model.

## What is not verified (yet)

- **Canonicity** is proven, conditional on one hypothesis. Every closed term of a parameterless inductive type is judgmentally equal to a canonical form: for `Nat`, a numeral. The theorem `Model.Canon.canonicity_of_glueCompat` assumes `GlueCompat`: two judgmentally equal Glue types whose faces are equivalent and not trivially true have judgmentally equal bases, and equal equivalences under the face. It holds in the model and for every rule that equates Glue types directly. Proving it in general needs a normalization argument for types, which is open. Full **normalization** is a design goal (stratified universes, strict positivity, structural recursion) but is not proven. Consistency depends on neither.
- **The elaborator's evaluator** is tested, not verified: `kubus --selfcheck` checks invariants on every definition, and a fuzzer generates random well-typed programs and ill-typed mutants. When the elaborator and the kernel disagree, the kernel wins.
- **The specification** has to be read: no proof can show that it says what you mean. This is why its textbook form is kept small.
