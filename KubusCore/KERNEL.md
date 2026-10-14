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

`KubusCore/Meta` (the metatheory) is not trusted either: it consists of theorems, checked by Lean, about the specification. The kernel imports it and uses its theorems in derivations, so `#print axioms` of the kernel covers them as well.

Nothing in `KubusCore/Kernel/` is trusted. All kernel functions are total (recursion on fuel), and contain no `sorry`, `partial`, `unsafe` or `implemented_by`. No rules were added to the spec (no "PENDING REVIEW" section).

The bridge `Kubus/Bridge.lean` is not trusted either: it produces KubusCore terms, which the kernel checks.

The kernel uses the metatheory: when the signature is known to be well-formed (`SigInfo.wf`, from the `CheckedSig`), a full-spec derivation is moved to the minimal judgments (`Meta.spec_to_minimal`), a generation or renaming theorem is applied, and the result is moved back (`Meta.minimal_to_spec`). Its conclusions are propositions, so they are used only where the kernel needs no witnesses from them. The theorems used: generation lemmas (`gen_hcomp`, `gen_transpF`, `gen_elimHead`, `gen_pi`, `gen_sigma`, `gen_path`, `gen_univ`), presupposition (`pre_ty`), renaming (`ren_ty`, `ren_eq`, `wfAll_of_wf`) and replacement of β-redexes (`beta_replace`, `Meta/Replace.lean`). Importing them makes a clean build of the kernel take about 3 minutes instead of 20 s; the binary grows by about 0.1 MB.

What a certification means for the user's statement is checked separately (see Translation adequacy).

The cache (see Memoization) compares terms with Lean core's `withPtrEq`, which is logically the structural comparison; its pointer-equality shortcut is part of Lean's runtime, like the compiler.

## Architecture

| file | contents |
|---|---|
| `Lemmas.lean` | syntactic lemmas: renaming fusion, substitution after renaming (`t.shift.inst a = t`, `t.dshift.dinst r = t`), closed terms, `Ctx.lookup` under interval weakening, entailment facts (`Φ ∧ φ ⊨ Φ`, reflexivity), and a decision procedure for `I.Eq` (enumerate the M4-assignments of the variables that occur) |
| `Ctx.lean` | kernel contexts `KCtx S Ψ Φ Γ`: the universe level of every variable's and constant's type with derivations that they are types, `Wf`, and scoping of `Φ`; extension by a term or interval variable, restriction |
| `Basic.lean` | result types (`Inf`: inferred type with level and derivations; `Red`: a reduct with its equation), the record `Rec S` of recursive calls, runtime checks that return proofs, moving equations between convertible types (`bridge`), the premises of `transp`/`hcomp` |
| `Data.lean` | inductive types: telescopes, typing of `data`/`con`/`elim` with the branch types and boundary conditions of branches, typing applications of branches from their branch types |
| `Infer.lean` | bidirectional inference and checking; Glue types (`toGlue`, `reglue`) |
| `Whnf.lean` | typed weak-head reduction |
| `Conv.lean` | conversion |
| `Rename.lean` | judgments in the smallest context, moved back by the renaming theorem |
| `Main.lean` | tying the knot, memoization, signatures |

Kernel functions run in the monad `K S := EStateM String (Cache S)`: errors, and a cache of derived judgments (see Memoization). Each kernel function is a separate definition taking a record `R : Rec S` of the recursive calls (infer, check, whnf, whnf-with-inference, conversion, neutral comparison). `Kernel.rec S n` ties the knot with fuel `n`, the nesting depth of calls (default 20000); each level of the record is built lazily. Side conditions that are decidable are checked at run time and the check yields the proof: syntactic equality of terms (`DecidableEq Tm`), `I.Entails` (a `Bool` function), `I.Scoped`, `I.Eq` (via `I.eqB_sound`), level bounds. This avoids proving metatheory: the kernel computes what a rule needs and compares.

The spec has no subject reduction or inversion of elimination forms, so the kernel re-derives typings when it needs them: reducing `f a` infers `f` (its type in weak-head normal form gives the inversion rules something to decompose) and re-checks `a`. Where the metatheory gives the needed facts as propositions, the kernel uses them instead (typed facts, smallest contexts, replacement). Equations are always derived at a type; when a congruence produces an equation at a different (convertible) type, `bridge` converts it with a type conversion. Rules stated for "any type of the redex" (β, endpoints, face rules, CHM rules) apply directly at the type at hand.

### Inference and checking

Inferable: variables, constants, universes, Π, Σ, annotated λ, application, projections, non-dependent pairs, path types, path abstractions (as `(i : I) → A`), path application, `(i : I) → A`, systems whose branch is entailed by the restriction, `transp`, `hcomp`, Glue types, `glue` (the fibres come from the type of its equivalence) and `unglue`. Checking handles λ (also with an annotation that is only convertible to the expected domain, via context conversion), path abstractions against `PathP` (with endpoint checks) or `(i : I) → A`, pairs, systems, `[]`, `glue`, type formers against a universe (componentwise, so that systems of types can be checked), and β-redexes whose head is not inferable. Everything else is inferred and compared.

Glue types have no inversion rules for the base and the equivalence, so the kernel checks those components itself when it decomposes a Glue type. When `unglue φ e g` meets a type in which the Glue type has already reduced (under `φ`), the Glue type is rebuilt from the type of `e`.

### Weak-head reduction

At a given type: β for Π, Σ (`fst`/`snd`), paths; path endpoints `p 0`, `p 1` (also for interval terms equal to 0/1, and after substituting endpoints that the restriction fixes, by the face rule); systems (`splitL`/`splitR`); δ-unfolding of constants; `transpFace`, `hcompFace`, `glueFace`, `glueElFace`, `unglueFace`, `glueBeta`; the CHM computation rules `transpU/Pi/Sigma/Path/Glue/IPi` and `hcompPi/Sigma/Path/Glue/IPi`, after reducing the line (resp. type) to weak-head normal form with the congruence rules. Eliminations reduce their head first, after contracting the β-redexes `(λ x. b) a` inside them (replacement, `Meta.beta_replace`: a λ in head position has no informative inferred type).

Typed reduction: the contracta of `transp` along Π, Σ, path, Glue and `(i : I) → A` lines eliminate the base (`app u0 w`, `fst u0`, `unglue u0`, …). When the base is an introduction form (λ, pair, path abstraction), inference in the contractum would only give it a weak, non-dependent type, so before contracting the kernel annotates it with the type `L(0)` known from the redex's typing: `transp (_. L(0)) 1 u0`, which equals `u0` by `transpFace` and has an inferable type. The annotation is a spec term, so it survives the substitutions that later act on the contractum. `unglue φ e (glue [φ' ↦ t] a)` with `φ'`, `e'` equal to `φ`, `e` only up to the interval laws resp. conversion is aligned by the congruence of glue elements before `glueBeta`.

### Conversion

1. Syntactically equal terms are equal.
2. The restriction `Φ` is split into its maximal faces with `EqTm.local` (no faces: `EqTm.absurd`).
3. Under a single face, the endpoints the face fixes are substituted into both sides (`EqTm.face`).
4. The type is brought to weak-head normal form and the comparison is type-directed: η for Π, Σ, `PathP`, `(i : I) → A` and Glue (comparing `unglue` and, under `φ`, the elements themselves); types are compared structurally (Π and Σ codomains via a derived context conversion); otherwise both sides are reduced and compared as neutrals (variables, applications, projections, path applications with `I.Eq` on the interval arguments, stuck `transp`/`hcomp` with entailment both ways on the cofibrations, `unglue`).

### Canonical restrictions

Nested systems make the syntactic restriction `Φ ∧ φ₁ ∧ φ₂ …` grow, and computing its faces blows up. Each kernel call therefore replaces `Φ` by an equivalent canonical form (the disjunction of its maximal faces), checks entailment both ways, works under the canonical form, and moves the result back with the restriction rule. A kernel context computes the faces of its restriction and its canonical form (with the entailment proofs) once, lazily (`KCtx.fs`, `KCtx.cn`).

### Memoization

`infer`, `check`, `whnf`, `whnfI`, `conv` and the premises of eliminators (`inferElimInfo`) store their results, derivations included, in a cache keyed by the context and the terms (`Cache` in `Basic.lean`). A lookup compares the keys structurally, which yields the equations along which the cached derivation is transported; nothing is trusted. A result derived under a weaker restriction `Φ₀` is reused under `Φ` when `Φ ⊨ Φ₀` (decided with the cached faces), moved by the restriction rule. For weak-head normal forms this is done only if the result is a canonical form (Π, Σ, a path type, λ, a pair, `data`, a constructor without interval arguments, …), which no stronger restriction reduces further, so reuse cannot make the kernel less complete. Variables, constants, weak-head reduction of canonical forms and conversion of identical terms bypass the cache. The cache lives for one definition (its translation and its check).

### Typed facts

Reduction produces terms that are known to be typed (the contractum of a typed redex, the heads of the eliminations being reduced, the terms being compared), at a type the kernel may not know. `noteTyped` records `∃ T, t : T` for such terms and, by the generation lemmas (`Meta.gen_elimHead`, `gen_hcomp`, `gen_transpF`, `gen_pi`, `gen_sigma`, `gen_path`), for their subterms in the same restriction. Inferring a composition or transport that is known to be typed then reads the premises (the tube, the base, the boundary agreement, the constancy of the line on `φ`) off the generation lemma instead of checking them; only the level of the type is inferred.

### Judgments in the smallest context

The contracta of the Kan operations bind many interval variables around subterms that mention few of them, so the same judgment recurs in many contexts. `infer` and `conv` first move the judgment to the context of just the variables it mentions (term variables closed under the dependencies of their types, the interval variables of all of these, the restriction projected onto them), derive it there, and rename the result back by the renaming theorem (`Meta.ren_ty`, `Meta.ren_eq`; `Rename.lean`). The kernel checks the conditions of the renaming (injectivity and bounds of the interval renaming, entailment of the restriction, the context lookups) and that renaming the small terms gives back the terms. The cache keyed by the small context shares the result between all the contexts the judgment occurs in. If the small derivation fails, the judgment is derived in the full context.

## The bridge

`kubus` runs the kernel on every definition and data type by default (`--no-kernel` turns it off). After normal elaboration each definition is translated and checked in one kernel run, sharing the cache (`translateCheck`), and data types with `CheckedSig.extendData`. The driver reports `skipped` (with the reason) and `REJECTED`, and fails if anything is rejected; `--verbose` also lists the certified definitions with their checking times. Declarations of the files given on the command line are certified; imported declarations are certified when they are used. The language server (`kubus --lsp`) runs the kernel on every declaration of the document, caching the results per declaration (keyed by its source text, reused while the document is unchanged up to it).

- Indices are split into term and interval variables. Globals become constants; `f^k` becomes a separate constant with the body and type displaced by `k`.
- KubusCore λ carries its domain and `glue`/`unglue` carry the Glue equivalence; Kubus core terms record neither. The translation is type-directed: it runs alongside the kernel (`elabT`), taking λ domains from the expected Π type and equivalences from the expected Glue type of `glue` and the Glue type of `unglue`'s argument.
- `let` is inlined before translation (Kubus core terms don't record the type of a `let`-bound value, so it is translated at each use against the type expected there).
- Systems become nested `split`s (empty: `abort`); cofibrations of `Glue`, `glue` and `unglue` are put in a canonical form so that they agree syntactically.
- `comp` becomes `Tm.comp`, `hcomp` becomes `Tm.hcomp`; `fill` becomes the homogeneous filler `Tm.hfill` when the line is constant (so that `fill … 1` is the `hcomp`, as in Kubus), and `⟨j⟩ comp (i. A(i ∧ j)) [ψ ↦ u(i ∧ j), j = 0 ↦ u0] u0` otherwise.
- `PathP P a b` becomes `path` with the body of `P` if `P` is a path abstraction, `papp P.dshift (var 0)` otherwise; `(i : I) → A` becomes `ipi`.
- Data types become data declarations (recursive arguments must be exactly `D params`; infinitary ones are not supported). Constructors take their parameters from the expected type. A pattern-matching definition becomes `λ x. elim d ps (x. B) bs x`, with one branch per clause: λs over the arguments and induction hypotheses and path abstractions over the interval arguments, where structurally recursive calls `f params y` become the hypothesis for `y`.
- Implicit arguments are inserted by Kubus as normal forms of its own evaluator, which can rely on computation the spec lacks (regularity). The translation recovers implicit arguments of applications of globals by matching the head's parameter types against the kernel-inferred types of the explicit arguments, and only falls back to Kubus's solutions for the rest.

The kernel certifies every definition and data type in `lib/`, including `ua`, `isoToEquiv`, `lemIso`, `EquivContr` and `loopSpaceS1`. `uaβ` used to state Kubus's own computation of transport along `ua` definitionally; Kubus and the spec compute it differently (Kubus's `comp` along a constant line is `hcomp`, and CCHM's `transpGlue` composes the base along the unglued tube), so no such definitional statement holds in both. It is now the path `\i -> unglue (fill j (ua A B e j) [] x i) : Path B (e.1 x) (transport A B (ua A B e) x)`, which both accept; checking its endpoint is the one place in the library where the kernel uses the `transpGlue` contractum (with that rule disabled, only `uaβ` is rejected).

## Known incompleteness

- No regularity: `transp` along a constant line does not reduce unless the line is a type former or the cofibration holds. This is the spec's theory, and since October 2026 also the Kubus evaluator's.
- Triage of the fuzzer's kernel-only rejections (October 2026): Kubus's evaluator equates terms the spec does not. Minimal examples: `comp i A [] a ≡ hcomp i A [] a` for any type `A` (regularity), and `transport (λ i → Int) a ≡ a` for a variable `a` (a first-order shortcut; in the spec `hcomp Int [] a` is stuck on a neutral `a`). The evaluator also composes in Glue types and in the universe with cubicaltt's comp-based algorithms (`compGlue`, `compU`) instead of the spec's CHM `transpGlue`/`hcompGlue`/`hcompU`. The remaining Glue and composition-in-the-universe rejections came from these differences, so the evaluator was aligned with the spec's operations (`Kubus/Eval.lean`); the library needed `hfill` instead of `fill` along a constant line in two places (`rUnit`, `unglueIsEquivI`).
- Systems under a restriction with several faces get the common type of their branches if there is one, and otherwise the system of the branch types (`[φ ↦ T₁, ψ ↦ T₂]`, a type by the system rule). `glue` with such an equivalence is not inferable when its fibres can't be guessed branchwise. The kernel checks these terms against types instead, and handles redexes whose head is not inferable (`(a, b).1`, `unglue (glue …)`, comparing pairs componentwise). `unglue` of a system of glue elements is checked against the expected base (with the fibre from the equivalence), contracted to a branch where that branch's face holds (`Meta.unglue_split`, a replacement theorem), and otherwise stuck. An elimination of such a term in a position where its type is needed but cannot be reconstructed is rejected.
- Universe levels are bounded by `maxLevel` (spec); types at the top level cannot be reduced or compared.
- Cost: without subject reduction the kernel re-infers heads and re-checks arguments while reducing, so checking is slower than evaluation-based conversion.
- Known stress cases (fuzzer, 20 seeds × 40 cases, 60 s per case, October 2026): 11 cases where elaboration succeeds but the kernel times out; no kernel-only rejections or skips. They share a shape: compositions whose tubes and bases are `winding (comp … (Path S1 base base) …)` or compositions along `hcomp U` lines, which unfold into nested `transpGlue`/`hcompU`/`lineEquiv` contracta (along `sucPathInt`, `ua`, `notPath`). With 300 s, 6 of the 14 earlier stress cases are certified and 8 still time out. Profiling (`fuzz_11_31`'s minimal form, a two-face `hcomp` in `Int` over such tubes; and `comp k (H k) [i = 0 -> fill m (H m) [] (T j) k] (T j)` with `H k = hcomp U [k = 0 -> Bool, k = 1 -> notPath]`) shows a genuine blowup of distinct terms, not missing sharing: in 60 s about 75 thousand comparisons on 47 thousand distinct triples of terms, and about 3,800 compositions whose premises must be checked (no typing of them is known), all distinct, of 9,500 characters on average and up to 480 thousand. The elaborator evaluates the same compositions in seconds, with shared values and no typing; the kernel derives a typing for every composition it reduces into a data type (`hcompCon` needs the tube's constructor and argument telescope). Making this cheaper needs typed reduction beyond the head (carrying the typings of the contracta's subterms), not a cache.

## Translation adequacy

The kernel certifies the translated statement. `kubus` checks for every certified definition that this is the statement the user wrote (`Kubus/Adequacy.lean`, run by the command-line driver): the kernel's type is read back into a Kubus core term by a syntactic inverse of the kernel's term formers (written independently of the translation: term and interval indices are merged again, constants and inductive types are named again, systems are rebuilt from nested `split`s, λ domains are dropped), evaluated by Kubus, and compared with the elaborated type by Kubus's conversion check, in both directions. A mismatch is reported as `kernel: ADEQUACY MISMATCH` and fails the run; `--verbose` lists the adequate definitions and prints a summary (`adequacy: n adequate, m not covered, k mismatches`).

Covered: types built from Π, Σ, λ, application, pairs and projections, universes, constants (with displacement), path types, path abstraction and application, `(i : I) → A`, `transp`, `hcomp` and the heterogeneous `comp` of the translation, Glue types, `glue`, inductive types and constructors. Not covered (reported with `--verbose`, not an error): statements whose kernel form contains `unglue` (Kubus's `unglue` records the Glue type, which the kernel term does not), eliminators (Kubus represents them by named pattern-matching definitions) or bare systems. Also not covered: data type declarations (their parameter and constructor types), the bodies of definitions (the kernel checks the translated body against the translated type; a body translated into a different term of the same type is not detected), and the language server and website builds, which certify without this check.

The comparison uses Kubus's evaluator and conversion, so it relies on them agreeing with the reading of the statement (both are untrusted; a disagreement can only produce a false mismatch or, if both the translation and the read-back are wrong in the same way, a missed one). `tests/run.sh` runs the check over `lib/` and `tests/pass/` and a self-test: with `KUBUS_ADEQUACY_SELFTEST` set, the kernel's statements are deliberately corrupted before the comparison (path endpoints swapped, or an extra Π), and every definition of `lib/basic.ktt` but at most one (a symmetric path type) must mismatch. Currently every certified definition of `lib/` (208) and `tests/pass/` (157) is adequate, none not covered.

## Performance

Kernel time (translation and check, summed over the definitions, `--verbose`), on a shared machine:

| | `lib/loopspace.ktt` | each other `lib/` file |
|---|---|---|
| start of the performance work | ~95 s | ~5.6 s |
| lazy δ, faces cached in the context, canonicalization shortcuts | ~50 s | ~4.7 s |
| per-definition cache of judgments | 7.3 s | ~0.65 s |
| cache state not copied under `tryCatch` (`EStateM`) | 5.7 s | |
| canonical restriction computed once per context | 4.9 s | ~0.49 s |
| reuse of results from weaker restrictions | 3.4 s | ~0.14 s |
| fast paths before the cache | 2.5 s | 0.12–0.17 s |
| cache entries grouped by context and terms (restrictions as variants) | 1.4 s | 0.04–0.08 s |
| typed reduction, glue congruence, strengthening by an unused interval variable | ≈ 1.1 s | |
| typed facts and generation lemmas, judgments in the smallest context, replacement | ≈ 0.35 s | |

On the fuzzer (20 seeds × 40 cases), the last two rows took the kernel stress timeouts (elaboration succeeds, the kernel times out at 60 s) from 42 to 13, and the system typing and typed facts recorded only for compositions and transports to 11, with no kernel-only rejections and no skips (see Known incompleteness). Profiling the stress cases showed about 127 thousand comparisons on only about 1.6 thousand distinct triples of terms, repeated across contexts and restrictions; the smallest context removes most of the repetition.

Since imported declarations are certified only when used, the times for the other files cover their own declarations and dependencies. `kubus lib/loopspace.ktt` takes 1.8 s end to end (elaboration 0.33 s, after the evaluator stopped applying interval substitutions to values that do not mention the substituted variable).

Findings from profiling (`perf`), in order:

- **Eager reduction in conversion.** Without lazy δ, comparing `winding (intLoopPos (suc n))` with the right-hand side of `windingPos` fully reduced both sides (δ-unfolding, the eliminator on `S¹`, `ua`'s Glue line, the CHM `transpGlue` contractum), and the `windingPos` successor case alone took over 15 minutes. Conversion now unfolds the head constant defined later one δ step at a time and compares applications of the same constant argumentwise first (`lazyDelta` in `Conv.lean`).
- **Re-derivation.** Without subject reduction the kernel re-derives typings: `whnfI` re-infers heads, eliminations re-check their branches and boundary conditions, and conversion re-checks arguments. On `loopspace`, `infer` ran 9.4 million times on 257 thousand distinct inputs, and each `whnfI` input was reduced about 21 times. The per-definition cache removes this.
- **Cache copies.** In `StateT σ (Except ε)`, `tryCatch` captures the state for the handler, so every cache insertion under `mapErr`/`tryOpt` copied the hash table. `EStateM` threads the state through errors instead.
- **Cofibration arithmetic.** `I.dnf`/`I.faces` for canonicalization and entailment were recomputed on every call; the faces and the canonical form are now computed once per context.
- **Many restrictions.** Nested systems (up to 14 interval variables in `lemIso`) produce many distinct restrictions over the same context and terms, so exact-match lookups missed; reusing results from weaker restrictions fixed this. Entries for the same context and terms then piled up under different restrictions, each compared in full; grouping them (one comparison of the keys, then a scan of the restrictions) fixed that.
- **What remains.** Comparing cache keys is still the largest item: contexts and terms rebuilt by substitution or interval weakening are structurally equal but not pointer-equal, so a hit costs a full structural comparison (hash-consing would need a sharing-preserving substitution, which is in the spec). The other large item is `inferElimInfo` (re-checking an eliminator's branches and boundary conditions), whose cached results are only reused under the same restriction; reusing them under stronger restrictions needs a lemma that entailment is stable under the interval renaming of the branch contexts.
