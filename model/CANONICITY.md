# Canonicity for Kubus Core: statement and plan

## Decision C1: numerals are canonical forms of `Nat`

Originally every inductive type treated `hcomp` formally, so `hcomp (data Nat []) 0 zero.dshift zero` was a closed `Nat` not equal to any numeral. Decision C1 (spec on this branch): in a type without path constructors composition is componentwise (`hcompCon`), and formal compositions exist only in HITs (`elimHcomp`/`transpHcomp` require `D.isHIT`). The model validates this (`Model/DataHR.lean`, `Model/Rules/DataHcomp.lean`). Canonical forms of a non-HIT are constructor terms with canonical recursive arguments; formal compositions remain canonical forms of HITs only.

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
  | hcomp {D : DataDecl} {a : Tm} : S[d]? = some (.data D) → D.isHIT = true → Canon S d a →
      Canon S d (.hcomp (.data d .tnil) .zero a.dshift a)

theorem canonicity {S : Sig} {d : Nat} {D : DataDecl} {t : Tm} (hS : WfSig S)
    (hd : S[d]? = some (.data D)) (hp : D.params = [])
    (ht : HasTy S 0 .one [] t (.data d .tnil)) :
    ∃ t', EqTm S 0 .one [] t t' (.data d .tnil) ∧ Canon S d t'
```

Remarks on the canonical forms:

- `rs` literally `0`/`1`: interval arguments can be normalized by the `con` congruence (`I.Eq`).
- The boundary of `c` does not hold at `rs` (at `Ψ = 0` the closed cofibration `cofAt ψ rs` is `0` or `1`); where it holds, `conBnd` rewrites the constructor to its boundary, which is canonical by induction.
- A composition whose face is true is its tube's end (`hcompFace`). In a non-HIT, a composition of a canonical constructor computes componentwise (`hcompCon`), so only HITs keep formal compositions. There, a false face is normalized to `.zero` (congruence) and the tube is irrelevant (`EqTm.absurd`), so the canonical tube is `a.dshift`. This is the CHM canonical form of HITs at the empty interval context: a formal composition with an empty system.
- `transp` in a parameterless data type is the identity (`transpData0`); eliminators, applications etc. compute away.
- Point arguments are only claimed to be closed and typed. The proof will give more (a computability witness for their types); natural strengthenings — canonicity for closed `Π`/`Σ`/path types, data types with closed parameters, and for terms in an interval context `Ψ > 0` (canonical up to faces) — come out of the same construction and can be stated afterwards.

## Route (refined)

A computability predicate on closed syntax, indexed by the model's semantics (Coquand–Huber–Sattler style gluing, with the set model supplying the well-founded index). Fix `S` with `WfSig S`.

1. **Closed syntax at stage `k`**: terms typed in `k; .one; []` (full spec judgments). Restriction along a syntactic interval substitution `τ` (stage `k'` to `k`) is `dsubst τ`, primitive in the spec; its semantic counterpart is the cube map `homOf τ` (every cube map is one, by definability). The value of a closed term is `sem t` at the identity environment, natural in `τ` by soundness.
2. **Computability** `RT X k f A` (a type) and `RE X k f A t` (an element), for a code `X` at stage `m`, at every restriction `f : Hom k m`, defined by well-founded recursion on the rank of `X` (Prop cannot be eliminated into relations, so not on `WF` proofs). Per code former: `Π`/`Σ`/paths/`(i : I) → A` by the usual clauses over all further restrictions; universes by `RT` of the element's code (smaller rank); Glue by `unglue` computable in the base and computable in `T` where the face holds; inductive types by an inductive predicate: canonical constructors with computable arguments, and for HITs formal compositions with a false face. Each clause includes typing, `sem A = res f X`, and the syntactic canonical shape of the type (`A ≡ Π A₁ B₁`, …), so that types are canonical as well.
3. **Basic lemmas**: closure under judgmental equality of terms and types, restriction (Kripke), cumulativity.
4. **Kan lemma**: `transp`/`hcomp` of computable data along computable lines are computable, by induction on the code, using the CHM computation rules syntactically (`transpPi`, …, `hcompU`, `transpGlue`, `hcompCon`, …) and the model's equations semantically.
5. **Fundamental lemma**: by induction on minimal typing derivations (`HasTy0`); equations need no case (presupposition gives typings of both sides, and computability is up to `≡`).
6. **Canonicity**: computability at a parameterless inductive type at stage 0 is `Canon`.

## Risks and expected spec issues

- For `hcompCon` the proof must show that the tube of a composition in a non-HIT is the base's constructor *syntactically*: build `uargs` from the tube's reducts per face of `φ` (nested splits), with "same constructor" from the logical relation.
- Every computation rule must be stable under interval substitution *syntactically up to `EqTm`* (the model only needed semantic stability). The metatheory branch found M4/M5 for this reason; more may show up where a computability witness has to match a contractum after restriction.
- Rules stated "at any type `T`" (contracta) need the presupposition/inversion results of the metatheory branch to relate `T` to the canonical type.

## Status

`Model.Canon.canonicity_of_glueCompat` (`Model/Canon/CanonForm.lean`) is proven without `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`): for every `S` with `WfSig S` and `GlueCompat S`, the statement `Canonicity` of `Model/Canon/Statement.lean` holds at `S`. The only hypothesis beyond the statement is `GlueCompat` (below).

## Proof structure

- `Comp.lean`, `Unfold.lean`: the logical relation `Comp S X m k f` (`.ty`/`.el`), by well-founded recursion on the rank of the code `X`; `RT`/`RE` are its instances at `semK A`. Inductive types use the relation `DR` (constructors with computable arguments; formal `hcomp` only for HITs).
- `Conv`, `Kripke*`, `CSub`, `Closed`, `Sub`, `Syn`: closure under `≡` and restriction, closing substitutions.
- `Formers*`, `ArgConv`, `GlueEquiv`, `GlueRT`, `Elim`: the introduction and elimination clauses per type former. `RE_glue_elim` is the one use of `GlueCompat`.
- `Kan*`: the Kan lemma, by induction on codes. The universe case (`KanUniv`, `KanGlue`, `KanGlueT`: `hcompU`, `transpU`, `transpGlue`) needs the fundamental lemma for the generic terms of the contracta, so the fundamental lemma is parametrized by a Kan oracle (`KOK`, `KanOracle`), which is discharged in `KanAll.lean` after the fact.
- Composition in an inductive type without path constructors (`KanDataH.lean`, decision C1): a computable base is a constructor, and so is the tube at each of its faces (`tube_canon`). The tube's arguments are given uniformly by projections `proj_j` (eliminators into the argument types, `Proj.lean`, `ProjFace.lean`), which reduce to the arguments on every face (`hcompCon_premises`, `ProjHcomp.lean`), so `hcompCon` applies. The composites are then computable: recursive arguments by induction on the relation of the base, point arguments by `comp`/`fill` along their type lines, which are computable at valid earlier fillers (`hcomp_data_DR`, `hcompCon_RE`).
- `Fund.lean`: the fundamental lemma, by induction on `HasTy0` derivations; `Final.lean`, `CanonForm.lean`: computability at a parameterless inductive type at stage 0 gives `Canon`.

## The hypothesis `GlueCompat`

```lean
def GlueCompat (S : Sig) : Prop :=
  ∀ (k : Nat) (A A' T T' e e' : Tm) (φ φ' : I) (l : Nat),
    EqTm S k .one [] (.glue A φ T e) (.glue A' φ' T' e') (.univ l) → ¬ I.Entails .one φ →
    EqTm S k .one [] A A' (.univ l) ∧ I.Entails φ φ' ∧ I.Entails φ' φ ∧
      EqTm S k (cof .one φ) [] e e' (Tm.equiv T A)
```

Injectivity of `glue` away from its face, for closed types (stage `k`, no term variables). The relation of a Glue type records one decomposition `glue A1 φ1 T1 e1` of it; to use the components of an element against another decomposition `glue A φ T e` of the same type (`unglue φ e g` versus `unglue φ1 e1 g`), `RE_glue_elim` needs the two decompositions to agree. This is the Glue analogue of the spec's `dataInj`/`ipiInj`. It cannot be a rule: where the face holds, `glue A φ T e ≡ T` leaves `A` and `e` unconstrained, so the premise `¬ φ` is not stable under interval substitution, and a rule with it would break the substitution lemma of the metatheory.

Why it is believed true:

- It holds semantically. The set model's Glue code (`glueC`, `Model/Glue.lean`) is, where the face does not hold, a datum recording the base family, the face and the equivalence. So two Glue types with equal semantics and a face that does not hold at the identity have equal bases, equivalent faces, and equal equivalences under the face.
- It holds syntactically for every way the spec equates two Glue types directly. Congruence gives the components. `glueFace` needs the face to hold, which is excluded. The universe contracta that produce Glue types (`hcompU`, `transpU`, `transpGlue`) are functions of their redex, so equal redexes give equal components.

What discharging it involves: the remaining gap is equalities that go through types that are not Glue types (β-redexes, eliminators into the universe, `hcomp`/`transp` in `U`), joined by transitivity. Semantic equality is not enough, because there is no completeness, so the model cannot return `EqTm A A'`. The admissibility proof is an injectivity theorem for type formers up to `≡`, like Π-injectivity in MLTT. The usual routes are (a) a confluent, type-preserving reduction whose conversion is `≡`, with Glue types in head normal form keeping their components (the Church–Rosser route), or (b) a normalization/NbE argument that produces normal forms of closed types (synthetic Tait computability, as in Sterling–Angiuli's normalization for cubical type theory). Either is a development on the scale of the canonicity proof. A cheaper option changes the statement rather than the spec. The logical relation could quantify over all Glue decompositions of a type instead of recording one. Then `RE_glue_elim` needs no comparison, but the formation case of the fundamental lemma must show that the components of an arbitrary other decomposition are computable. That is again an injectivity property, now stated for computable types.
