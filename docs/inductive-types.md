# Kubus Core, phase 2: inductive types and HITs

This fixes the design of inductive types and higher inductive types (HITs) in the kernel theory, and records how it is formalized in `KubusCore/Syntax.lean` and `KubusCore/Rules.lean`. It extends `docs/core-theory.md` and follows Coquand–Huber–Mörtberg, *On Higher Inductive Types in Cubical Type Theory* (CHM), restricted to a schema whose transport rules are simple enough to validate.

## Declarations

Data types are declared in the signature, next to definitions: a signature is a list of entries `Entry.defn t A` or `Entry.data D`, and entry `k` is referred to by `const k` or by `data k …`, `con k …`, `elim k …`. A declaration `D : DataDecl` has

- **a level** `l` and **a parameter telescope** `Δ` (`params`: parameter `j` lives in the context of the parameters before it);
- **constructors** `c (x₁ : A₁) … (xₙ : Aₙ) (i₁ … iₘ : I) [ψ ↦ b]` (`Ctor`), where each argument is
  - a *point* argument `point A`, with `A` in the context of the parameters and the arguments before it, of level at most `l`, and not mentioning the type being declared, or
  - a *recursive* argument `recur`, whose type is the type being declared at the same parameters, `data d Δ`;
  - a constructor with interval arguments has a *boundary*: a list of faces `ψ` over its interval arguments (interval variable 0 is `iₘ`) with elements `b` in the context of the parameters and all arguments.

**Decision: finitary recursive arguments only.** `D` occurs in an argument type only as the whole type `D Δ`, never as `(y : B) → D Δ`. This covers the library (`Nat`, `Int`, `Bool`, `Unit`, `Empty`, `S1`, `Susp`, `Trunc`) and keeps the induction hypotheses and boundary computations first-order. Infinitary arguments can be added later with induction hypotheses `(y : B) → P (x y)`.

**Decision: positivity as "does not mention".** Point arguments and parameters must not mention the declared type at all (`Tm.mentionsData`, a syntactic check), so the type occurs only as the type of recursive arguments: strictly positive and not nested.

**Simple boundaries** (`Ctor.simpleB`, a decidable syntactic check): a boundary element of constructor `c` is either a recursive argument of `c`, or a constructor `c' < c` of the same type at the parameters passed unchanged, whose recursive arguments are simple boundary elements and whose point arguments are point arguments of `c` (variables). Simple boundaries are what make transport componentwise: transporting `c (args) r` gives `c (transported args) r`, and its boundary is again the transported boundary. General boundaries (for example pushouts `inl (f c) = inr (g c)`) need CHM's correction terms and are left out. **Decision: boundaries only use earlier constructors** (`c' < c`), as in Kubus, so that boundaries are well-founded.

**Well-formedness** (`DataDecl.Wf`, part of `WfSig`): the level is below `maxLevel`; parameter types are closed over the earlier parameters, do not mention the type, and are types; point argument types are closed over their context, do not mention the type, and have the declared level; boundary faces are scoped in the interval arguments; boundary elements are closed, simple, have type `data d Δ` under their face, and agree on overlaps.

**Decision: constructor `c` is checked against the declaration truncated to the constructors before `c`.** The parameters are checked in the signature before the declaration; point argument types in that signature extended by `D` without constructors; the boundary of constructor `c` and its agreement on overlaps in that signature extended by `D` with only the constructors `0 … c-1` (`DataDecl.truncate`). Recursive arguments in the context of later arguments and of the boundary need the type former `data d`, and boundaries need the earlier constructors, so some form of the declaration must be present; but `c` itself must not be. *Counterexample to checking against the full declaration* (found by the model red-team): in the boundary context, `con d c params vars ivars` is typed by the `con` rule and `conBnd` (with `Φ = ψ`) gives `con … ≡ b`, so `b : data d …` by presupposition whatever `b` is, and overlaps agree likewise. Then `data D (A B : U₀) := c0 (a : A) | c1 (b : B) (i : I) [i = 1 ↦ c0 b]` passes, and transport along `i. D Bool (ua not i)` yields `c0 false ≡ c0 true`, hence `false ≡ true`. With truncation, `c0 b` is checked without `c1`'s boundary rule and is ill-typed. The same root cause let conflicting overlaps through (`tt | ff | seg (i : I) [i = 1 ↦ tt, i = 1 ↦ ff]`); with truncation `tt ≡ ff` is not derivable and the overlap check fails. Both are regression tests (`tests/kernel/BadData.lean`, and `tests/fail` for the elaborator). The typing rules of `data`, `con` and `elim` use only the declaration's data (telescopes, boundaries), not its well-formedness, and the restrictions above (no mention of `d` in point arguments, boundaries only using earlier constructors) keep the check well-founded.

## Terms

| term | typing |
|---|---|
| `data d ps` | `: U_l` when `ps : Δ` |
| `con d c ps args rs` | `: data d ps` when `args` match the arguments of `c` at `ps` and `rs` has one interval term per interval argument |
| `elim d ps (x. P) bs t` | `: P[t/x]` for `t : data d ps`, with one branch per constructor |

**Decision: annotations.** Constructors carry `d` and `ps`, and the eliminator carries `ps` and the motive `P`, so that the denotation of every term is independent of the type it is checked at (the lesson of phase 1: a term whose denotation depends on type information must carry it).

**Decision: argument lists are terms.** `ps`, `args` and `bs` are list terms built from `tnil` and `tcons`, so that `Tm` stays a plain (non-nested) inductive type and structural recursion and induction over terms work unchanged in the kernel and in the model. List terms have no typing rules of their own; telescopes are typed by the auxiliary judgments `HasTele` / `EqTele` (`as : Δ`, with the telescope's types instantiated by the earlier elements). Interval arguments `rs` are a `List I` field.

There is no separate formal `hcomp` constructor: `hcomp (data d ps) φ u a` itself is the formal composition, a canonical form of an inductive type. It is typed by the existing `hcomp` rule.

**Decision: branches are functions.** The branch for constructor `c` is an ordinary term of type

```
branchTy c = Π (x₁ : A₁) … (xₙ : Aₙ). Π (h₁ : P[x_{k₁}]) … (h_r : P[x_{k_r}]). (i₁ : I) → … → (iₘ : I) → P[con d c ps x̄ ī]
```

(one hypothesis per recursive argument `x_{k_s}`), computed from the declaration by `DataDecl.branchTy`. The β rules then apply the branch, and the result reduces by the ordinary β rules.

**Boundary condition of branches.** For a path constructor with boundary `[ψ ↦ b]`, its branch must agree with the eliminator on the boundary: in the *branch context* (the arguments, the hypotheses, and the interval arguments, restricted to `ψ`), the branch applied to the variables equals the eliminator on `b`. **Decision: the eliminator on `b` is computed syntactically** (`DataDecl.bndElim`) rather than written as `elim … b`: a recursive argument gives its hypothesis, a constructor `c'` gives the branch for `c'` applied to its arguments, the hypotheses for its recursive arguments (recursively), and its interval arguments. Writing `elim … b` would make the typing rule of `elim` depend on derivations of `elim` itself. With simple boundaries the two agree by the β rules.

## Equations

All computation rules have the form "if the redex has some type `T`, it equals its contractum at `T`".

- **Boundary** (`conBnd`): if `Φ ⊨ ψ[rs]`, then `con d c ps args rs ≡ b[ps, args, rs]`.
- **β for constructors** (`elimCon`): `elim d ps P bs (con d c qs args rs) ≡ bₖ args (ihs) rs`, where each hypothesis is `elim d ps P bs` applied to the recursive argument. The rule matches constructors of the same `d`; the parameters of the eliminator are used, the constructor's `qs` are only presupposed to be equal to them by the typing of the redex.
- **β for formal composition** (`elimHcomp`, CHM):
  `elim … (hcomp (data d qs) φ u a) ≡ comp (i. P[hfill (data d ps) φ u a / x]) [φ ↦ i. elim … u] (elim … a)`.
- **Transport:**
  - without parameters (`transpData0`), `transp (i. data d []) φ a ≡ a`, for any `a`;
  - with parameters (`transpCon`), transport is componentwise on constructors: the arguments are transported as a telescope along `Δ(i)` (`Tm.transpTele`: argument `k` along its type line, in which the earlier arguments are their transport fillers), interval arguments are unchanged, and the result is annotated with `ps(1)`;
  - with parameters (`transpHcomp`), transport of a formal composition is the formal composition of the transports: `transp (i. D) φ (hcomp D(0) ψ u a) ≡ hcomp D(1) ψ (j. transp (i. D) φ u(j)) (transp (i. D) φ a)`;
  - on neutral elements, transport is stuck.

  **Decision: the componentwise rules only apply with parameters.** For a type without parameters, transport is the identity; the componentwise rule would additionally equate `con … args` with `con … (transported args)`, and transport of an argument along a constant closed line (say `Path U₀ U₀ U₀`) is not the identity in CCHM, so the two rules would disagree.
- **Homogeneous composition:** `hcomp` in a data type never reduces, except by its face rule. This keeps evaluation stable under interval substitution: a componentwise rule would have to agree with the eliminator's composition rule after a later substitution, and in general it doesn't.
- **Congruence** for `data`, `con` (parameters and arguments as telescopes, interval arguments up to `I.Eq`) and `elim` (parameters, motive, branches at their branch types, target).

No inversion rules are added (none is needed by a kernel that can re-check parameters), so no rule infers well-typedness of a component from a type that could hold via a face reduct. Inductive types never reduce on faces.

Strict positivity, the absence of nesting, and the eliminator form (no general recursion) keep the theory normalizing. Structural recursion in the surface language is compiled to `elim`.

## Signature and consistency

`WfSig S` now requires every definition entry to be well-formed as before (checked against the entries before it) and every data entry `k` to satisfy `DataDecl.Wf (S.take k) k` (with the truncated declarations described above). The consistency statement is unchanged: for every well-formed `S`, no closed term has type `(A : U₀) → A`.

## Model obligations

- **Fibrant inductive types:** initial algebras in cubical sets built as least fixed points of the constructor signature, closed under formal `hcomp` (CHM §3), at the declared level.
- **Boundaries:** constructors with interval arguments are glued to their boundary (simple boundaries only use earlier constructors and recursive arguments).
- **Transport:** for simple boundaries, componentwise transport preserves the boundary, so it is well-defined on path constructors; for parameterless types transport is the identity.
- **Eliminator:** defined by well-founded recursion on the construction of the least fixed point; the boundary premises make it well-defined on path constructors, and the `hcomp` clause is CHM's.
