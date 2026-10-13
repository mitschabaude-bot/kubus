# Kubus Core: semantic model (step 4)

This Lake project builds the cubical-sets model of Kubus Core (`../KubusCore`) towards the theorem `KubusCore.Consistent`. It depends on Mathlib and on the root package (for `KubusCore`).

## Phase 2 spec issues (read first)

Status: P5 fixed in `ff388bc`. P4 fixed in `288a259`. P2 fixed in `dc30dbb` (`Ctor.bndTyped`), P3 in `2e8fc06`. P1 is fixed on `phase2` in `5534868`/`8017fc7` (constructor `c` is checked against the declaration truncated to the constructors before `c`; parameters against the signature before the declaration; point arguments against the declaration without constructors). Kept as a record; new issues are added at the top of this section.

### P5. Not modelable as stated: nested constructor argument lists in simple boundaries may have a non-literal tail

Modelability gap, small. `Ctor.simpleArgs` walks the nested argument list `as` of a boundary constructor `con d c' ps as rs'` through its `tcons` cells and accepts *any* tail (`| _ => true`), while `simpleB` compares `as.toList.length` (which ignores the tail) with the arity. So `con d c' ps (tcons x (split φ (tcons a tnil) ψ (tcons b tnil))) rs'` is simple. Syntactically such a boundary is never well-typed (its `HasTy` check needs `HasTele`, which forces a literal), but the model cannot see that, and the denotation of a constructor term must then tell well-formed from ill-formed argument lists by their values: the model guards constructor terms (they denote junk unless the arguments are a list of the right length, typed, with valid parameters — this is what lets `conBnd`/`elimCon` read off typed arguments from the typing of the left-hand side), and a tail that denotes a list (as `split` of literals does) fails the length guard, so the boundary term would not denote its value.

Suggested fix: require nested argument lists to be literals, e.g. in `simpleArgs` replace the catch-all `| _ => true` by `| t => t == .tnil`. (Wf boundaries produced by the elaborator are literals already.)

### P4. Not modelable as stated: rules read parameter/argument lists syntactically (`ps.toList`) without a premise that they are list literals

Again a modelability gap, not an inconsistency. Several rules use the syntactic list of a list term: `con` types its arguments in the telescope instantiated by `ps.toList.reverse`, `elim` builds branch types from `ps.toList`, `conBnd` uses `bndAt b ps.toList args.toList rs`, `elimCon` uses `args.toList` and `bs.toList[c]?`, `transpCon` uses `ps.toList` and `args.toList`. But their premises only type the type former or the left-hand side (`HasTy (data d ps) (univ l)`, `HasTy (con d c ps args rs) T`, …), which in a model says something about the *value* of `ps`, not its syntax. A term that is not a list literal can denote a list: e.g. `ps := split (i = 0) (tcons Bool tnil) (i = 1) (tcons Bool tnil)` under `Φ = (i = 0 ∨ i = 1)` denotes `[Bool]`, so `data D ps` is semantically a type, while `ps.toList = []`. With `data D (A : U₀) := c (a : A)` and `Γ = (X : U₀)`, the `con` premise `HasTele [a] [A] ps.toList.reverse` then types `a` at `X` (the parameter variable is not substituted), and the conclusion `con D c ps [a] : D ps` (i.e. `a : Bool`) fails in the model. Syntactically such premises are not derivable (`data d ps` is typed only via `HasTele ps`, which forces a literal), but the model cannot see that without an inversion lemma for typing derivations, and the denotation cannot depend on syntax (it must commute with substitution, which can turn `tcons a (var 0)` into a literal).

Suggested fix, in the style of the existing `bs = Tm.ofList bs.toList` premise of `elim`: add the premise `t = Tm.ofList t.toList` for every list term `t` whose `toList` a rule reads and which is not already a `HasTele`/`EqTele` subject: `ps` in `con`, `elim`, `conBnd`, `transpCon`; `args` in `conBnd`, `elimCon`, `transpCon`; `bs` in `elimCon`. (Alternatively, `con` and `elim` could take `HasTele S Ψ Φ Γ ps D.params []` instead of `HasTy (data d ps) (univ D.level)`; the computation rules still need the literal premises.) The kernel only produces literals, so this costs nothing there.

### P3. Not modelable as stated: the checks of `DataDecl.Wf` happen in contexts whose recursive arguments have an empty (or too small) type

Also a modelability gap, not an inconsistency. Point argument types are checked in `S ++ [.data (D.truncate 0)]`, and the boundary, its overlaps and the P2 type equalities of constructor `c` in `S ++ [.data (D.truncate c)]`. In both, the recursive arguments in the context have type `data d …` of the *truncated* declaration. In any model, a judgment in a context containing an empty type holds vacuously, and a judgment over a smaller type says nothing about the actual arguments, which may use constructors `≥ c`:

- `D.truncate 0` has no constructors, so it is empty in the model: whenever a point argument follows a recursive argument (`node (l : T) (a : A) …`), the check of `A` gives the model nothing (it cannot even show that `A` is a type at the actual arguments).
- `D.truncate c` is empty whenever the constructors before `c` have no base case (e.g. `c0 (x : D) | c1 (x y : D) (i : I) [i = 0 ↦ c0 x, …] | base`), and even when inhabited it does not contain the actual recursive arguments. The model needs the overlap agreement `b ≡ b'` for the actual arguments of `c` (for `conBnd` when two clauses hold).

Syntactic derivations do not exploit the emptiness (no eta for empty types), so this is no inconsistency, but no model can see that.

Suggested fix (three small changes):

1. Point argument types must not mention the variables of earlier recursive arguments (a syntactic check, like `mentionsData`). They cannot use them meaningfully anyway, since every consumer of a value of type `data d …` mentions `d`.
2. The truncated declarations used in `DataDecl.Wf` (`D.truncate 0` for point arguments, `D.truncate c` for constructor `c`) get one extra nullary constructor without boundary, appended at the end (index `c`, which no boundary of `c` can refer to). Then the data type of the checking signature is inhabited. From one inhabitant, the model builds infinitely many fresh elements (iterated formal compositions with an empty face), substitutes them for the recursive arguments, and transfers the overlap agreement to arbitrary arguments by a generic-element argument. With change 1, the point argument types and the P2 equalities do not depend on the recursive arguments at all.
3. `Ctor.simpleB` also checks that a nested `con d c' ps as rs'` has `rs'.length = C'.dims` (currently only the argument count is checked; the model needs it to recognise boundary values as elements without inverting typing derivations).

### P2. Not modelable as stated: boundary typing only gives membership, `transpCon` needs equal argument types

This is a modelability gap, not (as far as I can see) an inconsistency. `transpCon` transports each point argument along its own type line (`Tm.transpTele`). Take a boundary clause of `c` that passes the point argument `x` of `c` (type `B` in `c`'s telescope) as point argument `k` of an earlier constructor `c'` (expected type `A' := (C'.argTy d np k)` instantiated at the nested arguments), as in `c1 (x : B) (i : I) [i = 1 ↦ c0 x]`. `transp` of `c1 x 1` is `c1 (transp_B x) 1 ≡ c0 (transp_B x)`, while `transp` of the equal term `c0 x` is `c0 (transp_A' x)`. So the rule set is only coherent if transport along the `B` line equals transport along the `A'` line, i.e. (in any model where transport is part of the type) if `B ≡ A'` along every line of parameters (and fillers of the earlier arguments). Syntactically this holds, because the derivation of the boundary's type must convert `B` to `A'`; but `DataDecl.Wf` only asks for `HasTy … b (data d …)`, and the soundness of a typing judgment in a model only says that the value of `x` lies in the element set of `A'`, not that the codes `B` and `A'` (hence their transports) agree. Types with the same elements and different transport exist (e.g. a constant line of `Bool` and the line `ua not`), so the model cannot recover the equality from `HasTy`, and a syntactic inversion lemma ("`var j : T` implies `Γ(j) ≡ T`") is out of reach (`eqL`/`eqR`, `subst`, `restrict`, … all produce typings of variables).

Suggested fix: state the conversion that the kernel performs anyway. In `DataDecl.Wf`, for every boundary clause `(ψ, b)` of `c` and every point argument `var j` at position `k` of a nested `con d c' ps as rs'` in `b`: `EqTm Sc C.dims ψ (argCtx d C n) T_j A' (univ D.level)`, where `T_j` is the type of variable `j` in `argCtx d C n` (`n = C.args.length`) and `A' := (C'.argTy d np k).substList ((as.toList.take k).reverse ++ paramVars-instantiation)` is the type the `con` rule's `HasTele` assigns to position `k`. (Equivalently: a recursive Prop `Ctor.bndTyped` over the simple term, alongside `simpleB`.) With it, the model gets equal type codes from the soundness of `EqTm`, and `transpCon` is coherent with `conBnd`.

### P1. Inconsistent: boundary typing in `DataDecl.Wf` is vacuous (it can use the constructor's own boundary)

`DataDecl.Wf` checks a boundary `[ψ ↦ b]` of constructor `c` by `HasTy S C.dims ψ (argCtx …) b (data d (paramVars …))` in `S.take (k + 1)`, which contains the full declaration. That judgment is always derivable, whatever `b` is: in the boundary context, `con d c (paramVars) (vars) (ivars) : data d …` by the `con` rule (its arguments are variables of the right types), and `conBnd` for this very constructor and clause (`Φ = ψ` entails `ψ`) gives `con d c … ≡ bndAt b … = b`, so `b : data d …` by `eqR`. The overlap condition is equally vacuous. So simplicity (`Ctor.simpleB`) is the only real check, and simplicity does not check that the point arguments passed to an earlier constructor have the right types.

Counterexample. Let `Bool` be the usual data type (no parameters) and declare

```
data D (A B : U₀) : U₀ :=
  | c0 (a : A)
  | c1 (b : B) (i : I) [i = 1 ↦ c0 b]
```

It satisfies `DataDecl.Wf` (the boundary `c0 b` is simple; its typing is derived as above, although `b : B` is passed where `A` is expected). Let `L i := ua not i : U₀` be the univalence line of `not : Bool ≃ Bool` (constructible with `Bool`'s eliminator and `Glue`), so `L 0 ≡ L 1 ≡ Bool` and `transp (i. L i) 0 true ≡ not true` (up to formal `hcomp`s in `Bool` with empty systems, which `elim` sees through by `elimHcomp`). In `D Bool Bool`:

1. `con c1 [true] [1] ≡ c0 true` (`conBnd`).
2. Transport along `i. D Bool (L i)` (parameters non-empty, so `transpCon` applies). On the left, `transpCon` transports `c1`'s argument along its type line `L`, then `conBnd`: `transp (i. D Bool (L i)) 0 (con c1 [true] [1]) ≡ con c1 [not true] [1] ≡ c0 (not true) ≡ c0 false`. On the right (by congruence with step 1), `transpCon` transports `c0`'s argument along its type line, the constant line `Bool`, which is the identity (`transpData0`): `transp (…) 0 (c0 true) ≡ c0 true`.
3. Hence `c0 false ≡ c0 true : D Bool Bool`. The eliminator of `D Bool Bool` is available: with motive `Bool`, branches `λ a. a` and `λ b i. b`, the boundary condition `b ≡ b` holds because the parameters are equal. So `false ≡ true : Bool`, then `Empty ≡ Unit : U₀` by eliminating `Bool` into `U₀` (the `hcomp`s with empty systems in `U₀` become Glue types with a false face, which `unglue` removes), and every type is inhabited.

So the spec is inconsistent as stated. The root cause is that the declaration is checked against itself: well-formedness of constructor `c` may use the rules (`conBnd`, `elimCon`, …) of `c` and of later constructors, which presuppose that very well-formedness. This is also a problem for the model independently of the counterexample: the soundness proof proceeds by induction on the signature and cannot use derivations whose soundness depends on the entry being validated.

Suggested fix: check constructor `c` (its point argument types and its boundary) against the declaration truncated to the constructors before `c`, e.g. `D.Wf` quantifies over `c` and checks in `S.take k ++ [.data { D with ctors := D.ctors.take c }]` (boundaries only use earlier constructors, and point argument types do not mention `d` at all, so nothing is lost for the intended examples). Then `conBnd` for `c` is not available while checking `c`, and the model can validate declarations constructor by constructor.

## Spec issues (read first)

Status: all issues below are fixed in the spec: 1–4 in `91505c9` (`unglue φ e g`, annotated `lam A t`, `glueBase`/`glueEquiv` removed, `maxLevel = 4`), 5–6 in `1c637f0` (`glueEl φ e t a`, `transpGlue` composes the base along the unglued tube). They are kept here as a record. New issues are added at the top of this section.

Check requested after issue 6 (other contracta with the "constant only through its reduct" pattern): in the model the only type formers whose codes reduce on a face are Glue and the universe's `hcomp` (its rule `hcompU` reduces to a Glue type whose components are not lines of types constant on a face, so the pattern does not arise). The transport proofs for Π, Σ, `PathP` and `(i : I) → A` use, and prove, injectivity of their codes (`piC_inj`, `sigmaC_inj`, `pathC_inj`, `ipiC_inj`): a line of such codes that is constant on `ψ` has constant components on `ψ`. So `transpPi`, `transpSigma`, `transpPath`, `transpIPi` cannot hit the issue-6 pattern; the `hcomp` contracta involve no lines of types. Systems of types (`split`) also reduce on faces, but no computation rule matches on a `split` head.

### 6. `transpGlue` is ill-typed when the Glue line is constant on `ψ` only through its reduct

The `transp` rule only asks the *type* line to be constant on `ψ`. For a Glue line this is weaker than constancy of its components: where `φ` holds, `Glue A [φ ↦ (T, e)] ≡ T`, so the line can be constant on `ψ` while `A` and `e` vary there. Example (`Ψ = {k}`, `Φ = 1`, context `T : U, B : (i : I) → U, E : (i : I) → Equiv T (B i), u0 : Glue (B 0) [k ↦ (T, E 0)]`):

- the line `i. Glue (B i) [k ↦ (T, E i)]` is constant on `ψ := k` (both sides are `≡ T` by `glueFace`), so `R := transp (i. Glue (B i) [k ↦ (T, E i)]) k u0` is well-typed, and `R ≡ u0` under `k` (`transpFace`);
- but the contractum `Tm.transpGlue` uses `a1' := transp A ψ a0` and `transpFill A ψ a0`, which need `A = B i` constant on `ψ = k`; it is not. Under `k`, `ω` becomes the constant path at `e(1).1 u0` while it must end at `a1'`, so the pair `(t1', ω)` is not in the fiber, and the extension `ext` (hence the contractum) has no meaning there.

The rule `transpGlue` still asserts `R ≡ contractum`, so in a model the contractum must denote `u0` under `k`, and the standard model cannot validate this: the contractum's subterms are ill-typed at those points (no choice of the Glue fibration structure helps, since under `k` everything has reduced). I have not derived a contradiction from it (the spec's rules do not let one descend into the ill-typed subterms without inversion), so this is a *modelability* problem rather than a proven inconsistency, but a kernel that applies `transpGlue` here builds ill-typed terms.

Fix (this is what CCHM's composition for Glue does): transport the base by *heterogeneous composition* with the unglued tube instead of `transp A ψ`. On `ψ` the Glue line is constant, so `u0 : Glue A(i) [φ(i) ↦ (T(i), e(i))]` for every `i`, and `i ↦ unglue φ(i) e(i) u0` is a valid tube in the line `A` (where `φ` fails, the Glue components are constant and it is the constant `a0`; where `φ` holds it is `e(i).1 u0 : A(i)`). So:

- `a1' := comp (i. A) [ψ ↦ i. unglue φ e u0] a0` instead of `transp A ψ a0`;
- in `ω`, the `j = 1` face `fill (i. A) [ψ ↦ i. unglue φ e u0] a0` (the `comp` filler) instead of `transpFill A ψ a0`.

`t1' := transp T ψ u0` is fine: it is only used on `δ = ∀i. φ`, where the Glue line is the `T` line. The ψ-face of `ext`, `(u0, ⟨_⟩ a1')`, is then a fiber element (`a1' = e(1).1 u0` on `ψ ∧ φ1`). With this change the model can validate the rule (`transpGlue` becomes CCHM's `compGlue` specialised to the tube `[ψ ↦ u0]`). A `fill` for heterogeneous composition is not yet among the spec's defined terms (`hfill` is homogeneous); it is `fill (i. A) [ψ ↦ u] a0 = comp (j. A(i ∧ j)) [ψ ↦ j. u(i ∧ j), i = 0 ↦ a0] a0` at the interval variable `i`.

### 5. Still inconsistent (after `91505c9`): `glueBeta` with an un-annotated `glueEl`

`glueEl φ t a` does not record the equivalence it was checked against, but `glueBeta` (`unglue φ e (glueEl φ t a) ≡ a`) is stated for any `e`. Under `Φ ⊨ φ` all Glue types `Glue A [φ ↦ (T, e)]` are judgmentally `T`, so `conv` moves a `glueEl` checked against one equivalence into the Glue type of another. With `P`, `swap`, `e_id`, `e_sw` as in issue 1, in context `g : P` (`Ψ = 0`, `Φ = φ = 1`):

1. `glueEl 1 g (swap g) : Glue P [1 ↦ (P, e_sw)]` by the `glueEl` rule (`e_sw.1 g ≡ swap g`).
2. `Glue P [1 ↦ (P, e_sw)] ≡ P ≡ Glue P [1 ↦ (P, e_id)] : U₁` (`glueFace`), so by `conv` `glueEl 1 g (swap g) : Glue P [1 ↦ (P, e_id)]`, and by the `unglue` rule `unglue 1 e_id (glueEl 1 g (swap g)) : P`.
3. `glueBeta`: `unglue 1 e_id (glueEl 1 g (swap g)) ≡ swap g`.
4. `unglueFace`: the same term `≡ e_id.1 (glueEl 1 g (swap g)) ≡ e_id.1 g ≡ g` (`glueElFace`, `app` congruence, β).
5. Hence `swap g ≡ g`, and the rest is as in issue 1: `λX. λx. x : (X : U₀) → X`.

The root cause is the same as in issue 1: a reduct (here `glueEl φ t a ↦ t` under `φ`) forgets type information that a later rule depends on. Fix: `glueEl` carries the equivalence, `glueEl (φ : I) (e t a : Tm)`, with
- `glueEl`: `… → EqTm (cof Φ φ) (app (fst e) t) a A → HasTy (glueEl φ e t a) (glue A φ T e)` (annotation = the type's `e`);
- `glueBeta`: `unglue φ e (glueEl φ e t a) ≡ a` (the *same* `e` on both);
- `glueEta`: `g ≡ glueEl φ e g (unglue φ e g)`; the congruence rule keeps `e` fixed; the contracta `hcompGlue`/`transpGlue` pass `e` (resp. `e(1)`).

The step-2 retyping then only yields `unglue φ e_id (glueEl φ e_sw t a)`, to which `glueBeta` does not apply. This version is modelable: the model interprets `glueEl φ e t a` as `t` on `φ` *only if* `e.1 t = a` there, and as an untypable junk value otherwise; then `glueElFace` and `glueBeta` are validated from the typing premise of the redex alone. (Cubical Agda's `glue` also takes `e` as an implicit argument.)

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

- state consistency relative to an assumed ω-tower of Grothendieck universes;
- bound the universe levels in the spec (a fixed maximum `N`), in which case a finite tower is constructible in Lean and the theorem is unconditional (chosen: `maxLevel = 4`; the model's values live in `ZFSet.{5}`, and `V_l` will be the embedded copy of `ZFSet.{l}`);
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
| `Model/Kan.lean` | derived operations `hfillF`, `compF`, `transpFillF` |
| `Model/Sigma.lean`, `SigmaFib.lean`, `Path.lean`, `PathFib.lean`, `IPiFib.lean` | Σ, path and `(i : I) → A` codes and their fibrancy (`fib_sigmaC`, `fib_pathC`, `fib_ipiC`) |
| `Model/Glue.lean`, `GlueElem.lean`, `GlueFib.lean` | Glue elements, `unglue`, `hcompGlue`; `glueC`; `GlueOK` (the Glue hypotheses) and the `hcomp` fields |
| `Model/GlueTransp.lean`, `EquivCode.lean`, `CompFill.lean`, `CofForall.lean` | Glue transport (`gtResult`, the semantic reading of `Tm.transpGlue` after CCHM) and its fields; model codes for fibers/`isContr`/`isEquiv`/`Equiv`; heterogeneous `fill`; `∀i. φ` |
| `Model/Interp.lean` | defensive interpretation `interp` of raw syntax (see its header for the side conditions it checks) |
| `Model/Tower.lean`, `Small.lean`, `Univ.lean`, `UnivHc.lean`, `UnivHcFib.lean`, `WFFib.lean` | the tower `Vt l` (embedded `ZFSet.{l}`), the empty type, well-formed codes `WF l` (inductive), `univC m l`; well-formed codes are fibrant and stable under restriction |
| `Model/Sem.lean`, `InterpLemmas.lean` | `sem S`, constants from the signature, points, naturality, the semantic judgments `SemWf`/`SemTy`/`SemEq`/`SigOK`; renaming and substitution lemmas |
| `Model/Rules/*.lean` | one lemma per rule (`Stubs.lean`, generated by `scripts/gen_stubs.py`) and helpers |
| `Model/Sound.lean`, `Consistency.lean` | soundness by mutual induction on derivations; `consistent : KubusCore.Consistent` |

Design decisions:

- **Values are ZFC sets** (`Mathlib.SetTheory.ZFC`), because raw terms must have type-independent denotations (`app` is graph lookup). Typed Lean semantics (values in Lean types) cannot interpret unannotated `app`/`fst` without injectivity of Π-types of Lean types, which is not provable.
- **Kripke representation**: storing the restrictions inside each value makes restriction type-independent and definitionally functorial, avoids recursion, and makes Glue types/elements reduce on their face for free.
- **Codes store their Kan operations as data**, computed non-recursively by the constructors from the components. Derived codes (the fiber types in `transpGlue`, the isEquiv types needed for `hcomp` in `U`) can then be built freely, with no well-founded recursion on codes.
- **Faces** are represented canonically by their Kleene reading (a set of `K3`-points), so Kan operations depend only on the face, as `EqTm.transp`/`hcomp` congruence (mutual entailment) requires.
- **Universes**: `U_l` is `{c ∈ V_l | c is a well-formed level-l code}` where `V_l ⊆ ZFSet.{5}` is the embedded copy of `ZFSet.{l}` (a Grothendieck universe), `l ≤ maxLevel = 4`. Well-formedness is an inductive predicate on intensional codes, which validates `piDom`/`piCod`/… by inversion.

## Status

`Model/Consistency.lean` proves `consistent : KubusCore.Consistent` unconditionally: the model has no `sorry`s, and `#print axioms Model.consistent` shows only `propext`, `Classical.choice`, `Quot.sound`.

All rules of `KubusCore/Rules.lean` are validated (sorry-free lemma in `Model/Rules/Stubs.lean`); `transpGlue` is in `Model/Rules/TranspGlue.lean` (the contractum denotes the Glue code's transport `gtResult`), `hcompU` in `Model/Rules/HcompU.lean` (the contractum denotes the universe's `hcomp`, `univHcF`).

`hcomp` in a universe is `Glue u0 [φ ↦ (u(1), e)]` with `e` transport backwards along the tube (`Model/UnivHc.lean`). That transport is an equivalence is proven by transporting the proof that the identity is an equivalence along `i ↦ isEquiv (transp (j. B(i ∧ j)) (i = 0))` (`Model/UnivHcFib.lean`). Smallness of all codes (`Vt l` is closed under the code constructors) is in `Model/Small.lean`.
