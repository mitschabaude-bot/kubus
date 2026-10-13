# Canonicity for Kubus Core: statement and plan

## Design question first (C1): numerals are not canonical forms of `Nat`

In Kubus Core every inductive type treats `hcomp` formally: there is no rule computing `hcomp (data d ps) φ u a` when `φ` is false, not even for constructors without boundaries. In the model, `hcomp` in a data type at a false face is the formal composition `hcV`, which is different from `a`. So the closed term `hcomp (data Nat []) 0 zero.dshift zero` has type `Nat`, and it is *provably not* judgmentally equal to any numeral (the model separates them). Canonicity therefore has to list formal compositions as canonical forms for every inductive type, not only for HITs. The statement below does this.

If numeral canonicity for ordinary inductive types is wanted, the spec needs a CHM-style computation rule for `hcomp` at constructors without boundaries (e.g. `hcomp [φ ↦ con c us] (con c as) ≡ con c (hcomp …)` componentwise, and in particular `hcomp (data d ps) φ u a ≡ a`-like behaviour on empty systems for non-HIT types), and the model's data `hcomp` would have to compute structurally there. This is a design decision for you/Gregor; the plan below works for the spec as it is and would extend to such a rule.

## Statement

Closed terms live in `Ψ = 0`, `Φ = .one`, `Γ = []`. There every interval term is equal (`I.Eq`) to `0` or `1`, and every cofibration is equivalent to `0` or `1`. For a data type without parameters, the parameter list of a typed `data d ps` is `.tnil`.

```lean
namespace KubusCore

/-- Canonical closed elements of a parameterless inductive type `d`: a constructor whose
boundary does not hold, with canonical recursive arguments and closed interval arguments, or a
formal composition with an empty system (`hcomp … 0 …`) of a canonical element. The point
arguments are arbitrary closed terms of their types. -/
inductive Canon (S : Sig) (d : Nat) : Tm → Prop
  | con {D : DataDecl} {c : Nat} {C : Ctor} {L : List Tm} {rs : List I} :
      S[d]? = some (.data D) → D.ctors[c]? = some C →
      (∀ r ∈ rs, r = .zero ∨ r = .one) →
      (∀ ψ b, (ψ, b) ∈ C.bnd → ¬ I.Entails .one (Ctor.cofAt ψ rs)) →
      (∀ k (hk : k < L.length), C.isRec k = true → Canon S d L[k]) →
      HasTy S 0 .one [] (.con d c .tnil (Tm.ofList L) rs) (.data d .tnil) →
      Canon S d (.con d c .tnil (Tm.ofList L) rs)
  | hcomp {a : Tm} : Canon S d a → Canon S d (.hcomp (.data d .tnil) .zero a.dshift a)

theorem canonicity {S : Sig} {d : Nat} {D : DataDecl} {t : Tm} (hS : WfSig S)
    (hd : S[d]? = some (.data D)) (hp : D.params = [])
    (ht : HasTy S 0 .one [] t (.data d .tnil)) :
    ∃ t', EqTm S 0 .one [] t t' (.data d .tnil) ∧ Canon S d t'
```

Remarks on the canonical forms:

- `rs` literally `0`/`1`: interval arguments can be normalized by the `con` congruence (`I.Eq`).
- The boundary of `c` does not hold at `rs` (at `Ψ = 0` the closed cofibration `cofAt ψ rs` is `0` or `1`); where it holds, `conBnd` rewrites the constructor to its boundary, which is canonical by induction.
- A composition whose face is true is its tube's end (`hcompFace`). A false face is normalized to `.zero` (congruence) and the tube is irrelevant (`EqTm.absurd`), so the canonical tube is `a.dshift`. This is the CHM canonical form of HITs at the empty interval context: a formal composition with an empty system.
- `transp` in a parameterless data type is the identity (`transpData0`); eliminators, applications etc. compute away.
- Point arguments are only claimed to be closed and typed. The proof will give more (a computability witness for their types); natural strengthenings — canonicity for closed `Π`/`Σ`/path types, data types with closed parameters, and for terms in an interval context `Ψ > 0` (canonical up to faces) — come out of the same construction and can be stated afterwards.

## Route

A proof-relevant logical relation over the cube category, i.e. the gluing of the existing cubical-sets model with the syntax (Coquand–Huber–Sattler, "Canonicity and homotopy canonicity for cubical type theory", LMCS 2022; Huber's canonicity for CCHM is the operational precursor). Concretely:

1. **Syntax as a presheaf on the model's cubes.** The model's `Hom k m` are tuples of definable de Morgan functions, i.e. interval substitutions modulo `I.Eq` (the free de Morgan algebra). For a closed syntactic type, its closed elements at stage `m` (`HasTy S m .one [] t A`) modulo `EqTm`, restricted along interval substitutions, form a presheaf. This needs admissibility of interval substitution and its functionality for `HasTy`/`EqTm` — exactly what the `metatheory` branch proves (`Ren`, `Substitution`, `SubFace`, `spec_to_minimal`). So the canonicity branch will build on `metatheory` once it is merged (I will merge it into `canonicity` meanwhile, read-only).
2. **Computability structures.** A computable type at stage `m` is a syntactic type `A` together with, for every restriction, a set of *witnesses* for its closed elements, natural in the restriction, plus Kan operations on witnesses (transport along computable lines, composition with computable tubes) that agree with the syntactic Kan operations up to `EqTm`. Witnesses for data types: canonical forms with witnesses for the arguments (an inductive family, like `DElem`, now over pairs (term, value)); for Π: functions on witnesses commuting with application; for paths, `(i : I) → A`, Σ: componentwise; for the universe `U_l`: a computable type of level `l` (levels are bounded by `maxLevel = 4`, so the universe hierarchy is defined by an outer recursion on the level, as for the model's `Vt l`); Glue: as in CCHM, using the equivalence's computability.
3. **Fundamental lemma.** Every rule of `Rules.lean` is validated: typed terms in a context have computability witnesses at every computable instance of the context, and judgmentally equal terms get the same witnesses (proof relevance up to `EqTm`). This mirrors `Sound.lean` rule by rule, reusing the model's Kan-operation constructions (`hcompAt`, `transpAt`, `compF`, the Glue and universe Kan structures, `elimD`/`TR` for data), now carrying syntax along.
4. **Canonicity** at `Ψ = 0`: a witness for a closed element of a parameterless data type is a canonical form together with the equation `t ≡ canonical`.

The infrastructure that carries over: the cube category, cofibrations and `Fib`-style Kan structures, the Kripke encoding (`mkKV`, restriction), the data machinery (`DElem`, `TR`, `elimD`, `BranchesOK`, the overlap argument), and the rule-by-rule structure of the soundness proof. What is new: the syntactic component and the coherence of every Kan operation with its syntactic counterpart up to `EqTm`.

## Milestones

1. This statement (`model/Model/Canon/Statement.lean`, typechecks) — for review.
2. Merge `metatheory`; derive the presheaf structure of closed syntax (interval substitution on derivations, compatibility with `Hom` composition).
3. Computability structures for the non-Kan fragment (Π, Σ, paths, `(i : I) → A`, universes, data) and the fundamental lemma for their rules.
4. Kan operations on witnesses: transp/hcomp per type former, then Glue and `hcomp` in universes (the hardest part, as in the model).
5. Inductive types: canonical forms with boundaries, eliminator, transport and composition rules.
6. `canonicity`, sorry-free.

## Risks and expected spec issues

- **C1** above (formal `hcomp` in ordinary inductive types).
- Every computation rule must be stable under interval substitution *syntactically up to `EqTm`* (the model only needed semantic stability). The metatheory branch found M4/M5 for this reason; more may show up where a computability witness has to match a contractum after restriction.
- Rules stated "at any type `T`" (contracta) need the presupposition/inversion results of the metatheory branch to relate `T` to the canonical type.
