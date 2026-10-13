# The KubusCore kernel

`KubusCore/Kernel/` is a type checker for KubusCore whose soundness holds by construction: every kernel function returns a derivation of a judgment of the specification (`HasTy`, `EqTm`, `WfSig` in `Rules.lean`), so a successful run *is* a proof. The entry points are

```lean
def checkSig (S : Sig) : Except String (PLift (WfSig S))
theorem checkSig_sound (_ : checkSig S = .ok h) : WfSig S        -- h.down
def CheckedSig.extend (C : CheckedSig) (t A : Tm) : Except String CheckedSig   -- CheckedSig carries WfSig
```

## Trusted base

- Lean 4 and its kernel; the kernel's definitions use only the axioms `propext`, `Classical.choice` and `Quot.sound` (`#print axioms KubusCore.Kernel.checkSig`).
- The specification: `KubusCore/Syntax.lean` and `KubusCore/Rules.lean`.

Nothing in `KubusCore/Kernel/` is trusted. All kernel functions are total (recursion on fuel), and contain no `sorry`, `partial`, `unsafe` or `implemented_by`. No rules were added to the spec (no "PENDING REVIEW" section).

The bridge `Kubus/Bridge.lean` (`kubus --kernel`) is not trusted either: it produces KubusCore terms, which the kernel checks.

## Architecture

| file | contents |
|---|---|
| `Lemmas.lean` | syntactic lemmas: renaming fusion, substitution after renaming (`t.shift.inst a = t`, `t.dshift.dinst r = t`), closed terms, `Ctx.lookup` under interval weakening, entailment facts (`Φ ∧ φ ⊨ Φ`, reflexivity), and a decision procedure for `I.Eq` (enumerate the M4-assignments of the variables that occur) |
| `Ctx.lean` | kernel contexts `KCtx S Ψ Φ Γ`: the universe level of every variable's and constant's type with derivations that they are types, `Wf`, and scoping of `Φ`; extension by a term or interval variable, restriction |
| `Basic.lean` | result types (`Inf`: inferred type with level and derivations; `Red`: a reduct with its equation), the record `Rec S` of recursive calls, runtime checks that return proofs, moving equations between convertible types (`bridge`), the premises of `transp`/`hcomp` |
| `Infer.lean` | bidirectional inference and checking; Glue types (`toGlue`, `reglue`) |
| `Whnf.lean` | typed weak-head reduction |
| `Conv.lean` | conversion |
| `Main.lean` | tying the knot, canonical restrictions, signatures |

Each kernel function is a separate definition taking a record `R : Rec S` of the recursive calls (infer, check, whnf, whnf-with-inference, conversion, neutral comparison). `Kernel.rec S n` ties the knot with fuel `n`, the nesting depth of calls (default 20000); each level of the record is built lazily. Side conditions that are decidable are checked at run time and the check yields the proof: syntactic equality of terms (`DecidableEq Tm`), `I.Entails` (a `Bool` function), `I.Scoped`, `I.Eq` (via `I.eqB_sound`), level bounds. This avoids proving metatheory: the kernel computes what a rule needs and compares.

There is no subject reduction or inversion of elimination forms, so the kernel re-derives typings when it needs them: reducing `f a` infers `f` (its type in weak-head normal form gives the inversion rules something to decompose) and re-checks `a`. Equations are always derived at a type; when a congruence produces an equation at a different (convertible) type, `bridge` converts it with a type conversion. Rules stated for "any type of the redex" (β, endpoints, face rules, CHM rules) apply directly at the type at hand.

### Inference and checking

Inferable: variables, constants, universes, Π, Σ, annotated λ, application, projections, non-dependent pairs, path types, path abstractions (as `(i : I) → A`), path application, `(i : I) → A`, systems whose branch is entailed by the restriction, `transp`, `hcomp`, Glue types, `glue` (the fibres come from the type of its equivalence) and `unglue`. Checking handles λ (also with an annotation that is only convertible to the expected domain, via context conversion), path abstractions against `PathP` (with endpoint checks) or `(i : I) → A`, pairs, systems, `[]`, `glue`, type formers against a universe (componentwise, so that systems of types can be checked), and β-redexes whose head is not inferable. Everything else is inferred and compared.

Glue types have no inversion rules for the base and the equivalence, so the kernel checks those components itself when it decomposes a Glue type. When `unglue φ e g` meets a type in which the Glue type has already reduced (under `φ`), the Glue type is rebuilt from the type of `e`.

### Weak-head reduction

At a given type: β for Π, Σ (`fst`/`snd`), paths; path endpoints `p 0`, `p 1` (also for interval terms equal to 0/1, and after substituting endpoints that the restriction fixes, by the face rule); systems (`splitL`/`splitR`); δ-unfolding of constants; `transpFace`, `hcompFace`, `glueFace`, `glueElFace`, `unglueFace`, `glueBeta`; the CHM computation rules `transpU/Pi/Sigma/Path/Glue/IPi` and `hcompPi/Sigma/Path/Glue/IPi`, after reducing the line (resp. type) to weak-head normal form with the congruence rules. Eliminations reduce their head first.

### Conversion

1. Syntactically equal terms are equal.
2. The restriction `Φ` is split into its maximal faces with `EqTm.local` (no faces: `EqTm.absurd`).
3. Under a single face, the endpoints the face fixes are substituted into both sides (`EqTm.face`).
4. The type is brought to weak-head normal form and the comparison is type-directed: η for Π, Σ, `PathP`, `(i : I) → A` and Glue (comparing `unglue` and, under `φ`, the elements themselves); types are compared structurally (Π and Σ codomains via a derived context conversion); otherwise both sides are reduced and compared as neutrals (variables, applications, projections, path applications with `I.Eq` on the interval arguments, stuck `transp`/`hcomp` with entailment both ways on the cofibrations, `unglue`).

### Canonical restrictions

Nested systems make the syntactic restriction `Φ ∧ φ₁ ∧ φ₂ …` grow, and computing its faces blows up. Each kernel call therefore replaces `Φ` by an equivalent canonical form (the disjunction of its maximal faces), checks entailment both ways, works under the canonical form, and moves the result back with the restriction rule.

## The bridge (`kubus --kernel`)

After normal elaboration each definition is translated and checked with `CheckedSig.extend`; the driver prints `certified`, `skipped` (with the reason) or `REJECTED`, and fails if anything is rejected.

- Indices are split into term and interval variables. Globals become constants; `f^k` becomes a separate constant with the body and type displaced by `k`.
- KubusCore λ carries its domain and `glue`/`unglue` carry the Glue equivalence; Kubus core terms record neither. The translation is type-directed: it runs alongside the kernel (`elabT`), taking λ domains from the expected Π type and equivalences from the expected Glue type of `glue` and the Glue type of `unglue`'s argument.
- `let` is inlined before translation (Kubus core terms don't record the type of a `let`-bound value, so it is translated at each use against the type expected there).
- Systems become nested `split`s (empty: `abort`); cofibrations of `Glue`, `glue` and `unglue` are put in a canonical form so that they agree syntactically.
- `comp` becomes `Tm.comp`, `hcomp` becomes `Tm.hcomp`; `fill` becomes the homogeneous filler `Tm.hfill` when the line is constant (so that `fill … 1` is the `hcomp`, as in Kubus), and `⟨j⟩ comp (i. A(i ∧ j)) [ψ ↦ u(i ∧ j), j = 0 ↦ u0] u0` otherwise.
- `PathP P a b` becomes `path` with the body of `P` if `P` is a path abstraction, `papp P.dshift (var 0)` otherwise; `(i : I) → A` becomes `ipi`.
- Data types, constructors and pattern-matching definitions are phase 2 and skipped, together with everything that uses them.

`kubus --kernel lib/univalence.ktt` certifies all 39 definitions of `basic`, `equiv` and `univalence` except `absurd` (pattern matching), in about 10 seconds, including `ua`, `isoToEquiv`, `lemIso` and `EquivContr`. `uaβ` used to state Kubus's own computation of transport along `ua` definitionally; Kubus and the spec compute it differently (Kubus's `comp` along a constant line is `hcomp`, and CCHM's `transpGlue` composes the base along the unglued tube), so no such definitional statement holds in both. It is now the path `\i -> unglue (fill j (ua A B e j) [] x i) : Path B (e.1 x) (transport A B (ua A B e) x)`, which both accept; checking its endpoint is the one place in the library where the kernel uses the `transpGlue` contractum (with that rule disabled, only `uaβ` is rejected).

## Known incompleteness

- No regularity: `transp` along a constant line does not reduce unless the line is a type former or the cofibration holds. This is the spec's theory; Kubus's evaluator differs here (it treats `comp` along a constant line as `hcomp`), so Kubus terms whose typing depends on that are rejected.
- Systems under a restriction with several faces are not inferable (nor is `glue` when its equivalence is such a system and its fibres can't be guessed branchwise). The kernel checks them against types instead, and handles redexes whose head is not inferable (`(a, b).1`, `unglue (glue …)`, comparing pairs componentwise). An elimination of such a term in a position where its type is needed but cannot be reconstructed is rejected.
- `unglue φ e g` and `unglue φ' e' g'` are compared only if `e` and `e'` are syntactically equal (the spec has no congruence rule for the equivalence argument).
- The bridge cannot translate a λ without an expected type (e.g. as the head of an application in Kubus core).
- Universe levels are bounded by `maxLevel` (spec); types at the top level cannot be reduced or compared.
- `hcomp` in the universe is stuck (the spec has no computation rule for it).
- Cost: without subject reduction the kernel re-infers heads and re-checks arguments while reducing, so checking is slower than evaluation-based conversion.
