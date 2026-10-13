# Kubus Core: semantic model (step 4)

This Lake project builds the cubical-sets model of Kubus Core (`../KubusCore`) towards the theorem `KubusCore.Consistent`. It depends on Mathlib and on the root package (for `KubusCore`).

## Spec issues (read first)

### 1. The spec is inconsistent: `unglue φ g` does not carry the equivalence

`unglueFace` says `unglue φ g ≡ e.1 g : A` whenever `Φ ⊨ φ` and `g : Glue A [φ ↦ (T, e)]`. Under `Φ ⊨ φ` the type `Glue A [φ ↦ (T, e)]` is judgmentally `T` (by `glueFace`), so the same `g : T` inhabits `Glue A [φ ↦ (T, e)]` for *every* equivalence `e : Equiv T A`. Since the term `unglue φ g` does not mention `e`, the rule identifies `e.1 g ≡ e'.1 g` for any two equivalences. Derivation of a closed term of `(X : U₀) → X`, with `Ψ = 0`, `Φ = 1`, signature `[]`:

1. Let `P := Σ (_ : U₀), U₀ : U₁`, `swap := λ p. (p.2, p.1) : P → P`. `swap (swap p) ≡ p` holds judgmentally (β and Σ-η), and every judgmental involution `f` gives a closed `Equiv P P` with first component `f`: the fiber over `y` has centre `(f y, ⟨_⟩ y)` and contraction `λ (x, p). ⟨i⟩ (f (p (~i)), ⟨j⟩ p (~i ∨ j))`. This gives closed `e_id, e_sw : Equiv P P` with `e_id.1 ≡ λx.x` and `e_sw.1 ≡ swap`.
2. In context `g : P`: `glueFace` gives `Glue P [1 ↦ (P, e)] ≡ P : U₁` for `e ∈ {e_id, e_sw}`, so by `conv`, `g : Glue P [1 ↦ (P, e)]` for both.
3. `unglueFace` twice: `g ≡ e_id.1 g ≡ unglue 1 g ≡ e_sw.1 g ≡ (g.2, g.1) : P`. Taking `fst`: `g.1 ≡ g.2 : U₀`.
4. `subst` with `g := (X, X → X)` in context `X : U₀`, plus `fstBeta`/`sndBeta`: `X ≡ (X → X) : U₀`.
5. `λx.x : X → X`, so by `conv` `λx.x : X`, and `λX. λx. x : (X : U₀) → X`.

So `KubusCore.Consistent` is false as stated. Fix: `unglue` must carry the equivalence (as in Cubical Agda, where `e` is an implicit argument), e.g. `unglue (A : Tm) (φ : I) (T e g : Tm)` or at least `unglue φ e g`. The same applies wherever the contracta use `unglue` (`hcompGlue`, `transpGlue`).

### 2. `glueBase` and `glueEquiv` are not valid in the model

Under `Φ ⊨ φ`, `glueFace` forces `Glue A [φ ↦ (T, e)]` to *denote* `T`. So the premise of `glueBase` (`Glue A [φ ↦ (T, e)] : U_l`) holds semantically as soon as `T : U_l`, whatever `A` and `e` are (even ill-typed junk); the conclusion `A : U_l` does not follow, and likewise `glueEquiv`'s conclusion about `e`. A soundness proof by induction on derivations cannot validate these rules with any interpretation in which judgmental equality at `U_l` is equality of denotations. A "level-indexed partial interpretation" where `⟦glue A φ T e⟧_l` is defined only if `⟦A⟧_l` is, does not help: definedness is then not stable under β (`(λY. Glue Y [1 ↦ …]) a` versus its contractum) and congruence, because function values do not remember how their bodies were typed. They may well be *admissible*, but proving that needs syntactic metatheory (inversion/generation lemmas), which is exactly what the primitive rules were meant to avoid.

The other inversion rules are fine: the model interprets type formers as *intensional codes* (a Π-code records its domain and codomain family, a path-code its line and endpoints), so `piDom`, `piCod`, `sigmaDom`, `sigmaCod`, `pathLine`, `pathLeft`, `pathRight`, `ipiLine` hold by inversion on the inductive definition of level-`l` codes. `glueFib` is also fine (under `φ` the Glue type denotes `T`). Only Glue reduces on a face, which is why only `glueBase`/`glueEquiv` break.

Suggested fix: drop `glueBase` and `glueEquiv` (keep `glueFib`), and if the kernel needs `A : U_l` for a Glue type, have it carry that derivation itself.

### 3. Unannotated `lam` blocks the presheaf (set-valued) model

In a set-valued model a function is its graph, so `λx. x : A → A` and `λx. x : B → B` must denote different sets, while `lam (var 0)` is one raw term. Partial interpretation of raw syntax (Streicher's method, the standard way to prove soundness of a spec with a conversion rule and Prop-valued derivations) therefore needs `lam` annotated with its domain: `lam (A t : Tm)`. All other term formers are fine unannotated (`app` is graph lookup, `pair`/`plam`/`glueEl`/`split` have type-independent denotations, `transp`/`hcomp`/`glue` carry their types). Unannotated `lam` is not inconsistent (realizability/PER models interpret Curry-style terms), but a realizability model of CCHM is a much larger project (Huber's canonicity proof). Recommendation: annotate `lam` with its domain.

### 4. Universe levels: no uniform set-valued model in Lean

A model in which `U_l` collects all small fibrant types, for every `l : ℕ` simultaneously, needs a sequence of Grothendieck universes `V₀ ∈ V₁ ∈ …` inside one Lean universe, i.e. ω inaccessibles below it. Lean proves the existence of finitely many (`Type 0 ∈ Type 1 ∈ …`, or `PSet.embed`), but cannot quantify over universe levels, so a single theorem covering derivations with arbitrary `l` cannot be proven from a set-valued model; the cardinality argument is that any `U_l` closed under Π with arbitrary families and containing an infinite type has inaccessible cardinality. Options:

- state consistency relative to an assumed ω-tower of Grothendieck universes (the plan here: the model is parametric in a tower `V : ℕ → ZFSet`, and the final theorem takes it as a hypothesis);
- bound the universe levels in the spec (a fixed maximum `N`), in which case a finite tower is constructible in Lean and the theorem is unconditional;
- a realizability model (handles all levels in `Type 0`), at much higher cost.

Note also that the core fragment has no base types, so the model must put an empty type into `U₀` itself to refute `(X : U₀) → X`; that is fine.

## Architecture

The model is the CCHM cubical-sets model over the De Morgan cube category, presented concretely so that *raw* syntax can be interpreted (Streicher-style partial interpretation), which is how a spec with a conversion rule and Prop-valued derivations is validated.

| file | contents |
|---|---|
| `Model/Interval.lean` | `M4` laws; soundness of the spec's DNF; the face lattice is the Kleene algebra `{0, a, 1} ⊆ M4` (`entails_sound`: the spec's `I.Entails` is sound for it); `r = 1` iff `r(a, …, a) = 1` |
| `Model/Cube.lean` | the cube category: `DM m` (definable functions `M4^m → M4`, i.e. the free De Morgan algebra), cube maps `Hom k m`, interval environments, faces at a stage (`Cof m`, canonical Kleene reading), join-primeness of the true face (local character) |
| `Model/Enc.lean` | the value universe `V = ZFSet`; encodings of countable data, graphs, lookup |
| `Model/Val.lean` | *Kripke values*: a value at stage `m` is the graph of its data at all `(k, f : Hom k m)`; restriction is uniform reindexing (`res`), strictly functorial, independent of types; Glue reduction on faces is automatic in this representation |
| `Model/Codes.lean` | type codes: Kripke values whose datum at `(k, f)` stores the *shape* (tag + components, so codes are intensional), the element set, and the graphs of `transp` (along the last variable) and `hcomp`; tubes, keys and graph builders |
| `Model/Fib.lean` | `Fib c m`: lawful fibrant code (element sets closed under restriction; `hcomp`/`transp` typed, with face conditions, natural) |
| `Model/Pi.lean`, `PiFib.lean`, `PiTransp.lean` | Π-types: Kripke function elements; `hcompPiF`/`transpPiF` read off the spec's `Tm.hcompPi`/`Tm.transpPi`; `fib_piC` |

Design decisions:

- **Values are ZFC sets** (`Mathlib.SetTheory.ZFC`), because raw terms must have type-independent denotations (`app` is graph lookup). Typed Lean semantics (values in Lean types) cannot interpret unannotated `app`/`fst` without injectivity of Π-types of Lean types, which is not provable.
- **Kripke representation**: storing the restrictions inside each value makes restriction type-independent and definitionally functorial, avoids recursion, and makes Glue types/elements reduce on their face for free.
- **Codes store their Kan operations as data**, computed non-recursively by the constructors from the components. Derived codes (the fiber types in `transpGlue`, the isEquiv types needed for `hcomp` in `U`) can then be built freely, with no well-founded recursion on codes.
- **Faces** are represented canonically by their Kleene reading (a set of `K3`-points), so Kan operations depend only on the face, as `EqTm.transp`/`hcomp` congruence (mutual entailment) requires.
- **Universes**: `U_l` will be `{c ∈ V_l | c is a well-formed level-l code}` for an assumed tower `V_l` of Grothendieck universes (see spec issue 4). Well-formedness is an inductive predicate on intensional codes, which validates `piDom`/`piCod`/… by inversion.

## Status

Proven (no `sorry`):

- face lattice semantics; soundness of `I.Entails`; the face rule's key fact (`holds_lit`: if `Φ ⊨ i = d` then the environment sends `i` to `d`); local character (`holds_or`);
- cube category laws; interval environments and their restriction;
- Kripke values, uniform restriction;
- **Π-types are fibrant** (`fib_piC`): `hcomp` and `transp` given by the spec's contracta `Tm.hcompPi` and `Tm.transpPi` are typed, satisfy the face conditions, and are natural.

Remaining, in order:

1. Σ (`hcompSigma` uses `hfill` and `comp`; `transpSigma` uses `transpFill`), paths (`transpPath`, `hcompPath`), `(i : I) → A` (`transpIPi`, `hcompIPi`), the empty type.
2. Universes: the level-indexed well-formedness predicate, `U_l` as a code (`transp` = identity), `hcomp` in `U` via Glue along the transport equivalence (the spec has no computation rule for it, but the model needs one).
3. Glue: elements, `unglue` (with the equivalence, see spec issue 1), `transpGlue`, `hcompGlue`.
4. Interpretation of raw syntax with Kripke environments; substitution lemmas.
5. Soundness of every rule, then `Consistent` (relative to the universe tower, and only after spec issues 1–3 are fixed).

Rule checklist: no typing rule is validated yet; the semantic ingredients for the Π rules (formation, λ, application, β, η, `transpPi`, `hcompPi`) are in place.
