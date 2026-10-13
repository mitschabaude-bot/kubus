# The consistency proof of Kubus Core

This is an account of `Model.consistent : KubusCore.Consistent` for a reader who knows cubical type theory (CCHM / CHM) and wants to check the argument without reading the Lean. The statement is: for every well-formed signature `S`, no closed term has type `(X : U₀) → X`. `Model.kernel_consistent` composes it with the kernel's soundness theorem (`Kernel.checkSig_sound`): whatever the certified kernel accepts lives in a consistent theory. Both depend only on `propext`, `Classical.choice` and `Quot.sound` (checked in CI by `model/ci/Axioms.lean`).

The proof is a model construction: a cubical-sets model built inside Mathlib's ZFC sets, an interpretation of raw syntax into it, and a soundness theorem by induction on derivations. The spec is `KubusCore/Syntax.lean` (raw syntax, defined terms, contracta) and `KubusCore/Rules.lean` (the judgments `Wf`, `HasTy`, `EqTm`, `WfSig`, as inductive Props).

## 1. Semantic setup

### 1.1 The cube category

The interval is the free De Morgan algebra. An interval value at stage `m` (`DM m`) is a function `M4^m → M4` definable by an interval term, where `M4 = {0, a, b, 1}` is the four-element De Morgan algebra; since `M4` generates the variety, equality of these functions is equality in the free De Morgan algebra on `m` generators. A cube map `Hom k m` is an `m`-tuple of values at stage `k`; it acts on points `M4^k → M4^m`, and composition is substitution. Presheaves are contravariant in this category: values at stage `m` restrict along `f : Hom k m` to stage `k`.

An interval environment `IEnv m` assigns a value at stage `m` to every interval variable; `ival ρ r` evaluates an interval term. Restriction of environments is pointwise, and the category laws hold definitionally on the actions, which keeps most coherence goals `rfl` or `simp`.

### 1.2 Faces

A face (cofibration) at stage `m` is represented by its Kleene reading `Cof m := Set (Pt m)`: the set of points with coordinates in `K3 = {0, a, 1}` where the formula evaluates to `1`. This representation is canonical: two interval formulas that entail each other in the spec's face lattice (`I.Entails`, defined via DNF) have the same Kleene reading (`entails_sound`), so the Kan operations, which receive the face as a `Cof`, respect the spec's congruence rules for `transp`/`hcomp` (stated up to mutual entailment).

A face holds at stage `m` iff it contains the all-`a` point (`eval_allA_eq_one`: `r = 1` in the free algebra iff `r(a, …, a) = 1`). The true face is join-prime at the all-`a` point (`φ ∨ ψ` holds iff `φ` or `ψ` holds, since `K3`-join is `1` only if one argument is), so local character is trivial: a system `split φ t ψ u` under `Φ ⊨ φ ∨ ψ` can be interpreted pointwise by cases. `∀ i. φ` (`I.forall0`, used by `transpGlue`) is interpreted as `Cof.forall0`: the points `p` with `(p, a) ∈ φ` (`face_ival_forall0` proves that the spec's syntactic definition denotes it).

### 1.3 Values: Kripke values in ZFC

Values live in `V := ZFSet.{5}`. Raw terms need type-independent denotations (`app` is graph lookup, `fst` is projection), which rules out typed Lean semantics. A value at stage `m` is a *Kripke value* (`mkKV m F`): the graph of `F` on `Σ k, Hom k m`, where `F k f` is the value restricted along `f`. Restriction is reindexing, `res f v := mkKV k (fun n g => dat v n (f ∘ g))`, which is independent of types and strictly functorial. Values that are not Kripke values (notably `∅`) are junk and belong to no type.

The Kripke representation is what makes Glue work without effort: a Glue type or Glue element has, at maps into its face, simply the data of its reduct, so `Glue A [φ ↦ (T, e)] ≡ T` under `φ` holds as an equality of sets.

Elements of the type formers are: Kripke functions `lamV` (the graph of a function on the element set at every stage, natural in the stage), pairs `pairV`, paths `pathOfLine p` (a line `p` at stage `m+1`, the path variable last), and Glue elements `glueV`.

### 1.4 Codes

A type at stage `m` is a *code*: a Kripke value whose datum at `(k, f)` is a quadruple (`quad`) of

- the *shape*: a tag and the components (e.g. a Π-code records its domain and its codomain family), so codes are intensional;
- the element set at stage `k`;
- the graph of `transp` along the last interval variable (when `k = n + 1`), keyed by (face, base);
- the graph of `hcomp` at stage `k`, keyed by (face, tube restricted to the face, base).

The constructors (`piC`, `sigmaC`, `pathC`, `ipiC`, `glueC`, `univC`, `emptyC`) compute all four components non-recursively from the components' data, reading the spec's computation rules (`Tm.hcompPi`, `Tm.transpPi`, `Tm.transpGlue`, …) as the definition of the graphs. Since nothing is defined by recursion on codes, derived codes (fiber types, `isContr`, `isEquiv`, the line of `isEquiv` types used for `hcomp` in `U`) can be built freely. `transpAt c f φ a0` and `hcompAt c f φ u u0` look up the graphs of `c` at `f`.

### 1.5 Fibrancy

`Fib c m` (the CCHM fibration structure, in the `transp`/`hcomp` formulation of CHM) says: elements are Kripke values; element sets are closed under restriction; `hcomp` and `transp` are typed (for tubes satisfying `TubeOK` and lines constant on the face, `ConstOn`), satisfy their face conditions (on `φ`, `hcomp` is the tube's end and `transp` is the identity), and are natural in the stage. Fibrancy is proven for every constructor (`fib_piC`, `fib_sigmaC`, `fib_pathC`, `fib_ipiC`, `GlueOK.fib`, `fib_univC`); `comp`, `fill`, `hfill`, `transpFill` are derived (`Kan.lean`, `CompFill.lean`).

### 1.6 Universes and the finite tower

A universe of all small fibrant types at every level `l : ℕ` would need ω inaccessibles, which Lean cannot provide uniformly (spec issue 4). The spec therefore bounds levels by `maxLevel = 4`, and the model uses the finite tower `Vt l` (`l ≤ 4`): the embedded copy of `ZFSet.{l}` in `ZFSet.{5}` (Mathlib's `PSet.embed`), a Grothendieck universe with `Vt l ∈ Vt (l+1)`.

`WF l m c` (well-formed code of level `l`) is an inductive predicate on the intensional shape: empty, Π/Σ with well-formed domain and family (as a graph over the domain's elements, natural in the stage), path types with a well-formed line and endpoints in it, `(i : I) → A`, universes `U_l'` for `l' < l`, and Glue types with well-formed base and fibre, a coherent partial equivalence, and `¬ φ.holds` (on the face the Glue code *is* its fibre). `U_l := univC m l`, with elements `{c ∈ Vt l | WF l c}`. Universe codes are defined by recursion on the level (`Ucodes`), since `WF l` refers to the universes below. Every well-formed code is fibrant and stable under restriction (`wf_props`, by induction on the level and on `WF`).

`transp` in `U` is the identity (the line of universe codes is constant). `hcomp` in `U` is Glue along transport, see 4.2.

### 1.7 Smallness

For `U_l` to be closed under the type formers, every code built from members of `Vt l` must be in `Vt l` (`Small.lean`). The characterisation used: `x ∈ Vt l` iff all members of `x` are in `Vt l` and `x` is `l`-small. From it, `Vt l` is closed under pairs, countable graphs, graphs over members, separation, powerset, products, function sets and unions; the Kan graphs only need the code itself to be small (results are lookups below it). `interp_mem_Vt` proves by induction on terms that the interpretation of any term in a small environment is small.

## 2. Interpretation of raw syntax

`interp cst uc good t m ρ γ` (`Interp.lean`) gives every raw term a value at stage `m`, for an interval environment `ρ` and a term environment `γ`; `sem S` instantiates constants by their bodies (`cstFn`), universes by `univC`, and `good` by "well-formed code of some level ≤ 4, or a universe" (`TyCode`). Binders: `lam A t` is the Kripke function whose value at `(k, f, a)` is `t` at `(ρ·f, γ·f, a)`; `plam t` is `pathOfLine` of `t` at the generic point `(ρ.ext, γ·wk)`; type formers are the corresponding code constructors applied to the interpreted components and families.

The interpretation is *defensive*. Where a rule of the spec only knows that a redex has a value in its type, the interpretation checks the side conditions the rule needs and returns `∅` otherwise; since `∅` belongs to no type, a redex that is well-typed in the model passes the checks. The checks:

- `transp`/`hcomp`: the type (line) is good, constant on the face, the base/tube are typed, and type and base are natural (commute with restriction);
- `app f a`: the argument is natural; `plam t`: the body is natural; `pair a b` and the components of `pi`/`sigma`/`path`/`ipi`: Kripke values (and the lines of `path`/`ipi` natural);
- `glue A φ T e`: `T` and `e` are natural on the face; `glueEl φ e t a`: on `φ`, it is `t` only if `e.1 t = a`; `unglue` on `φ` requires a Kripke value;
- `split φ t ψ u`: one of the faces holds and `t = u` where both do.

Constants are interpreted by their bodies in the signature prefix (`cstFn`); `ConstsLt` (all constants below the signature length) makes interpretations stable under extending the signature (`sem_take`).

## 3. The soundness theorem

Semantic judgments (`Sem.lean`): a *point* of `Ψ; Φ; Γ` at stage `m` (`IsPoint`) is an interval environment `ρ` in which `Φ` holds and a term environment `γ` of Kripke values whose entries are elements of the interpreted types of `Γ`. `t` is *natural* at a point if its interpretation commutes with restriction. Then

- `SemTy S Ψ Φ Γ t A`: at every point, `⟦t⟧ ∈ El ⟦A⟧`, `⟦A⟧` is a good code (`TyCode`), and both are natural;
- `SemEq S Ψ Φ Γ t u A`: both sides are `SemTy`, and `⟦t⟧ = ⟦u⟧` at every point;
- `SigOK S`: every definition is closed and `SemTy` in the signature before it.

Quantifying over all stages and all points (rather than over a fixed generic context) is what makes restriction, interval substitution and the face rules (`restrict`, `split`, `…Face` rules) direct: a point of the restricted context is a point of the original one.

`sound_wf`/`sound_ty`/`sound_eq` (`Sound.lean`) are proven by mutual induction on derivations, dispatching to one lemma per rule (`Rules/Stubs.lean`, sorry-free). `sigOK_of_wfSig` turns `WfSig S` into `SigOK S` by induction on the signature.

Typical rule proofs: congruence and β/η rules compute both sides; inversion rules (`piDom`, `pathLine`, …) invert `WF` on intensional codes (`WF.pi_inv`, `piC_inj`, …); computation rules for the Kan operations show that the contractum denotes the code's `transp`/`hcomp` graph entry, whose definition is the semantic reading of that contractum, using the defensive checks of the redex for the needed naturality and typing.

Consistency (`Consistency.lean`): if `t : (X : U₀) → X` in a well-formed signature, soundness at stage 0 gives `⟦t⟧` in the interpreted Π-code; `emptyC` is a well-formed small code of level 0, so applying `⟦t⟧` to it gives an element of `El emptyC = ∅`.

## 4. The non-obvious arguments

### 4.1 Glue transport (`GlueTransp.lean`, `Rules/TranspGlue.lean`)

The transport graph of a Glue line `i ↦ Glue A(i) [φ(i) ↦ (T(i), e(i))]` is `gtResult`, the semantic reading of `Tm.transpGlue` (CCHM's `compGlue` specialised to `transp`):

- `a0 = unglue u0`, the tube `i ↦ unglue φ(i) e(i) u0` on `ψ`, and `a1' = comp (i. A) [ψ ↦ that tube] a0` (heterogeneous composition, see issue 6);
- on `δ = ∀ i. φ`: `t1' = transp (i. T) ψ u0` and a path `ω` from `e(1).1 t1'` to `a1'` (a composition in `A` with the transport filler of `T` and the composition filler of `A` as sides);
- on `φ(1)`: `ext`, the extension of the partial element `[δ ↦ (t1', ω), ψ ↦ (u0, refl)]` of the fibre of `e(1).1` over `a1'` to a total one, by `hcomp` in the fibre from the centre of contraction;
- `a1 = hcomp A(1) [φ(1) ↦ (snd ext)(~j), ψ ↦ a1'] a1'`, and the result is `glue [φ(1) ↦ fst ext] a1`.

Proving `Fib` for Glue requires: each piece is typed, the partial elements agree on overlaps (e.g. `(t1', ω) = (u0, refl)` on `δ ∧ ψ`, which uses that `ω` reduces on `ψ`), the face condition (on `ψ` the result is `u0`, via Glue η), and naturality. Naturality is the subtle part: `transp` at a restricted stage is computed from the *restricted data* `A·lift h, φ·lift h, …`, so every ingredient needs a "data change" lemma (`gd_A0`, `gd_A1'`, `gd_Ω`, `gd_Ext`, …) saying it equals the original ingredient restricted along `h`. The rule `transpGlue` is then validated by computing the denotation of every subterm of the contractum at every point, including the spec's syntactic `I.forall0` and the interval substitutions `φ(0/i)`, `φ(1/i)`.

### 4.2 `hcomp` in the universe (`UnivHc.lean`, `UnivHcFib.lean`, `Rules/HcompU.lean`)

`hcomp U [φ ↦ i. u] u0 := Glue u0 [φ ↦ (u(1), e)]`, with `e : u(1) ≃ u0` transport backwards along the tube. That transport is an equivalence is proven without any homotopy-theoretic reasoning about specific types: for a line `B`, let `f_i = λ x. transp (j. B(i ∧ j)) (i = 0) x : B(0) → B(i)`. At `i = 0` the face is true, so `f_0` acts as the identity (`trFace`), and the identity has an explicit proof of contractible fibres: centre `(y, refl)`, contraction `(x, p) ↦ ⟨i⟩ (p(~i), ⟨j⟩ p(~i ∨ j))` (`idEqV`; only connections and restriction are used). Transporting this proof along the line of codes `i ↦ isEquiv f_i` (which is fibrant because `isEquiv`, `isContr`, fibres are built from Π, Σ, paths) gives a proof that `f_1` is an equivalence (`eqTr`). The resulting Glue code is well-formed (needs `¬ φ.holds`; on `φ` the `hcomp` is `u(1)` directly), small, equals `u(1)` on `φ`, and is natural (via the naturality of `eqTr` under restriction of the line). The spec's rule `hcompU` uses exactly these terms (`Tm.lineFun`, `Tm.idIsEquiv`, `Tm.lineEquiv`), so its validation is a computation of denotations.

### 4.3 Face rules and systems

All face-dependent rules (`hcompFace`, `transpFace`, `glueFace`, `glueElFace`, `unglueFace`, `splitL/R`) are validated pointwise: at a point, `Φ` holds, so an entailed face holds (`entails_holds`), and the model's operations reduce by their face conditions or by the Kripke representation. `split` needs no gluing argument because the true face is join-prime at the all-`a` point (1.2).

### 4.4 The empty type in `U₀`

`emptyC` has no elements at any stage and trivially satisfies `Fib`; it is a well-formed level-0 code (`WFI.empty`) and small (`emptyC_mem_Vt`), hence an element of `U₀`. This is the only place where the model needs a type with no elements, and it is what refutes `(X : U₀) → X`.

## 5. How the spec issues showed up

All six were found while validating rules and are fixed in the spec; `README.md` keeps the detailed write-ups.

1. `unglue φ g` without the equivalence: `unglueFace` identifies `e.1 g` and `e'.1 g` for any two equivalences (under `φ` the Glue type is `T` whatever `e` is); with `swap` on `Σ U₀ U₀` this derives `(X : U₀) → X`. Found while designing the interpretation of `unglue`, which must not depend on the type; the derivation above is a counterexample to the original spec. Fix: `unglue φ e g`.
2. `glueBase`/`glueEquiv` (inverting a Glue type to its base and equivalence) have no model: under `φ` a Glue type denotes `T`, so its base can be junk. Found in the inversion lemmas. Fix: dropped.
3. Unannotated `lam`: in a set-valued model a function is its graph, so `λx.x` at different domains must denote different sets. Fix: `lam A t`.
4. Unbounded universe levels need ω inaccessibles. Fix: `maxLevel = 4` and the finite tower.
5. `glueEl φ t a` without the equivalence: `conv` moves it into the Glue type of another equivalence, and `glueBeta`/`unglueFace` again identify two equivalences. Found when validating `glueBeta`. Fix: `glueEl φ e t a`, interpreted defensively (`t` on `φ` only if `e.1 t = a`).
6. `transpGlue` used `transp A ψ a0`, which is ill-typed when the Glue line is constant on `ψ` only through its reduct (`A` may vary on `ψ ∧ φ`). Found when the model's Glue transport could not satisfy its face condition. Fix: compose the base along the unglued tube (`comp`, `fill`).

## 6. Map from concepts to Lean

| Concept | File | Main definitions / theorems |
|---|---|---|
| `M4`, DNF soundness, Kleene reading of faces | `Model/Interval.lean`, `Cube.lean` | `entails_sound`, `eval_allA_eq_one`, `entails_holds` |
| Cube category, environments, faces | `Model/Cube.lean`, `CubeLemmas.lean` | `DM`, `Hom`, `IEnv`, `ival`, `Cof`, `Cof.holds`, `holds_or` |
| `∀ i. φ` | `Model/CofForall.lean`, `Rules/TranspGlue.lean` | `Cof.forall0`, `face_ival_forall0` |
| ZFC encodings | `Model/Enc.lean` | `natZ`, `enc`, `fnC`, `fnZ`, `apZ`, `Below` |
| Kripke values | `Model/Val.lean` | `mkKV`, `dat`, `res`, `IsKV` |
| Codes, tubes, Kan graphs | `Model/Codes.lean` | `quad`, `El`, `trG`, `hcG`, `hcompAt`, `transpAt`, `hcGraph`, `trGraph` |
| Fibrancy | `Model/Fib.lean` | `Fib`, `TubeOK`, `ConstOn` |
| Π | `Model/Pi.lean`, `PiFib.lean`, `PiTransp.lean` | `piC`, `lamV`, `appV`, `fib_piC` |
| Σ, paths, `(i : I) → A` | `Model/Sigma.lean`, `SigmaFib.lean`, `Path.lean`, `PathFib.lean`, `IPiFib.lean` | `sigmaC`, `pathC`, `ipiC`, `pathOfLine`, `fib_sigmaC`, `fib_pathC`, `fib_ipiC` |
| Derived Kan operations | `Model/Kan.lean`, `CompFill.lean` | `hfillF`, `compF`, `transpFillF`, `fillF` |
| Glue | `Model/Glue.lean`, `GlueElem.lean`, `GlueFib.lean`, `GlueTransp.lean` | `glueC`, `glueV`, `ungAt`, `GlueOK`, `gtResult`, `GlueOK.fib` |
| Equivalence codes | `Model/Glue.lean`, `EquivCode.lean` | `fiberM`, `isContrM`, `isEquivM`, `equivM`, `equivCode_eq_equivM` |
| Tower, smallness | `Model/Tower.lean`, `Small.lean` | `Vt`, `mem_Vt_of`, `isSmallAt_of_mem_Vt`, `interp_mem_Vt` |
| Empty type, well-formed codes, universes | `Model/Univ.lean`, `WFFib.lean` | `emptyC`, `WFI`, `WF`, `univC`, `wf_props`, `fib_univC` |
| `hcomp` in `U` | `Model/UnivHc.lean`, `UnivHcFib.lean` | `eqFunL`, `idEqV`, `eqTr`, `univHcF`, `eqTr_mem`, `univHcF_wf` |
| Interpretation | `Model/Interp.lean`, `InterpLemmas.lean`, `SemBasic.lean` | `interp`, `sem_subst`, `sem_ren` |
| Semantic judgments | `Model/Sem.lean` | `sem`, `cstFn`, `IsPoint`, `Natural`, `SemTy`, `SemEq`, `SigOK` |
| Rule lemmas | `Model/Rules/*.lean` | one `sem_*` lemma per rule in `Stubs.lean`; `TranspGlue.lean`, `HcompU.lean`, `GlueComp.lean`, `CompLemmas.lean` for the large ones |
| Soundness, consistency | `Model/Sound.lean`, `Consistency.lean`, `EndToEnd.lean` | `sound_ty`, `sound_eq`, `sigOK_of_wfSig`, `consistent`, `kernel_consistent` |
