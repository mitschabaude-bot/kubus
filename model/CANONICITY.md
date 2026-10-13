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
    I.Entails φ φ' → I.Entails φ' φ →
    EqTm S k .one [] A A' (.univ l) ∧ EqTm S k (cof .one φ) [] e e' (Tm.equiv T A)
```

The faces are a premise, not a conclusion. The first version concluded `φ ⟺ φ'` and was false, which made `canonicity_of_glueCompat` vacuous: `glue A φ T e ≡ glue (glue A φ T e) 1 (glue A φ T e) idEquiv` by `glueFace` (symmetrically), with `¬ φ` but `1 ⇏ φ`. In the canonicity proof the faces come from the model. The relation records the face of the Glue code, and cofibrations with equal faces entail each other (`ent_of_face_eq`, `Model/Canon/Sub.lean`), so `RE_glue_elim` supplies the premises.

Injectivity of `glue` in its base and equivalence, between Glue types with the same face that does not hold, for closed types (stage `k`, no term variables). The relation of a Glue type records one decomposition `glue A1 φ1 T1 e1` of it; to use the components of an element against another decomposition `glue A φ T e` of the same type (`unglue φ e g` versus `unglue φ1 e1 g`), `RE_glue_elim` needs the two decompositions to agree. This is the Glue analogue of the spec's `dataInj`/`ipiInj`. It cannot be a rule: where the face holds, `glue A φ T e ≡ T` leaves `A` and `e` unconstrained, so the premise `¬ φ` is not stable under interval substitution, and a rule with it would break the substitution lemma of the metatheory.

The trivial context `Φ = .one` is essential. At `Φ = i ∨ ~i` with `φ = i`, `glue A i T e ≡ glue A' i T e'` is derivable with `A(1) ≢ A'(1)`, using `local` and `face`. So the statement must not be generalized to arbitrary `Φ`. Taking the premise by reflexivity, `GlueCompat` also gives base inversion (`glue A φ T e : U l` implies `A : U l`). That is not a rule (`glueBase` was removed) and is an obligation of milestone (d).

Why it is believed true:

- It holds semantically. The set model's Glue code (`glueC`, `Model/Glue.lean`) is, where the face does not hold, a datum recording the base family, the face and the equivalence. So two Glue types with equal semantics and the same face that does not hold at the identity have equal bases and equal equivalences under the face.
- It holds syntactically for every way the spec equates two Glue types directly. Congruence gives the components. `glueFace` needs the face to hold, which is excluded. The only contractum that is a Glue type, `hcompU`, is built from the components of its redex, and the `hcomp` congruence equates those.

What discharging it involves: the remaining gap is equalities that go through types that are not Glue types (β-redexes, eliminators into the universe, `hcomp`/`transp` in `U`), joined by transitivity. Semantic equality is not enough, because there is no completeness, so the model cannot return `EqTm A A'`. The admissibility proof is an injectivity theorem for type formers up to `≡`, like Π-injectivity in MLTT. The usual routes are (a) a confluent, type-preserving reduction whose conversion is `≡`, with Glue types in head normal form keeping their components (the Church–Rosser route), or (b) a normalization/NbE argument that produces normal forms of closed types (synthetic Tait computability, as in Sterling–Angiuli's normalization for cubical type theory). Either is a development on the scale of the canonicity proof. A cheaper option changes the statement rather than the spec. The logical relation could quantify over all Glue decompositions of a type instead of recording one. Then `RE_glue_elim` needs no comparison, but the formation case of the fundamental lemma must show that the components of an arbitrary other decomposition are computable. That is again an injectivity property, now stated for computable types.

## Plan for discharging `GlueCompat`

Strengthening the existing relation at `U` alone does not work. Its type clauses record *some* decomposition of a type up to `≡` (`∃ A1 φ1 T1 e1, G ≡ glue A1 φ1 T1 e1 ∧ …`). Two such records for the same type are related only semantically, because the relation is closed under `≡` by the model. Requiring the records to agree up to `≡` is `GlueCompat` itself. A record that quantifies over all decompositions makes the formation case need `GlueCompat` again. Semantic agreement does not give syntactic agreement either: the base may be any closed type, e.g. `Π n. Vec (n+0)` versus `Π n. Vec n`, whose semantics agree but which are not `≡`. The faces are the exception (decidable, complete, recorded by the model), which is why they are now a premise discharged semantically.

The route is Huber's canonicity for cubical type theory with an equality relation. Determinism of reduction makes the record of a Glue type in weak-head normal form the type's own components, and a PER with a fundamental lemma for equality derivations carries `≡` between types to their records. Milestones, each merge-ready on its own:

- **(a) Reduction.** A deterministic weak-head reduction `⇒` on closed terms at stage `k`: the spec's computation rules (β, eliminators, Kan operations per type former, Glue, HITs), oriented, under head contexts, as a function `step : Tm → Option Tm`. Theorems: determinism (by construction), soundness `t ⇒ t'` and `HasTy t A` give `EqTm t t' A` (from the typings of the contracta in `KubusCore/Meta`), and whnfs do not step.
- **(b) Subject reduction and restriction.** Typing is preserved along `⇒`. Interaction with interval restriction, documented precisely: a step commutes with restriction except where the redex is chosen by a face, i.e. a `hcomp`/`transp` whose face holds after restriction (`hcompFace`, `transpFace`), or a Glue type, element or `unglue` whose face comes to hold. There the restricted reduct is `≡` to the reduct of the restriction, not equal. The PER is Kripke over restrictions, as the current relation is, and only uses `≡`-closure at restricted stages, so this is enough.
- **(c) PER and fundamental lemma.** A relation `t ~ t' : X` per code, indexed by the same ranks: for types at `U`, both reduce to whnfs with the same head and related components (Glue: equal faces, bases related and `≡`, equivalences related and `≡` under the face), and similarly for the other formers; elements are related pointwise or by canonical forms. Fundamental lemma for `EqTm0` derivations, with `HasTy0` as the diagonal. Type equalities arise from term equalities at any type (`app`, `elim`, `fst` into `U`), so the PER is defined at every code.
- **(d) Corollaries.** `GlueCompat` as the PER at `glue A φ T e ≡ glue A' φ' T' e'`, giving `canonicity` without hypotheses. If cheap: canonicity with equality (equal closed elements of a data type have equal canonical forms) and injectivity of the type formers as stated theorems.

Reduction is not stable under interval substitution, so (c) has to commute reduction with restriction up to `≡`, as in Huber. The existing development is reused for the semantic indexing (ranks), the Kan lemma's syntactic contracta, and the projections. This is also a step toward normalization.

### Milestone (a): done

`Model/Whnf/Step.lean` defines `step : Sig → Tm → Option Tm`, one step of weak-head reduction, structurally recursive, so deterministic by construction. `Red` is its reflexive-transitive closure, `IsWhnf S t := step S t = none`, and `RedW.unique` says normal forms are unique. Notes on the definition:

- Faces are decided by `I.entails .one`. A step taken at `.one` is valid in every context, since `Φ ⊨ .one`.
- `transp`/`hcomp` reduce their line to a whnf, then compute by its head. At an inductive type they first reduce the base, and they fire only on a constructor or formal `hcomp` of the same inductive type.
- `transpGlue` uses `δ := φ.forall0`.
- `hcompCon` takes the tube's arguments to be the projections `proj_j u`.
- `unglue φ e (glueEl φ' e' t a) ⇒ a` regardless of annotations.
- `con` reduces by its first boundary that holds.

`Model/Whnf/Sound.lean`, `step_sound`: a typed term's step is a judgmental equality at its type (minimal judgments, any `Ψ`, `Φ`, and `Γ = []`); `red_sound`/`red_sound_spec` extend this to `Red`. Two steps need side conditions that typing alone does not give, stated as hypotheses about closed terms and discharged in milestone (c):

- `HCSound`: the `hcompCon` step, where the tube must be a constructor on its face (cf. `tube_canon`).
- `UGSound`: `unglue φ e (glueEl φ' e' t a) ≡ a` with different annotations, which needs the annotations to agree up to `≡` under the face. This is `GlueCompat` again, at the element level.

### Milestone (b): subject reduction and restriction

Subject reduction for closed terms is `red_typed` (from soundness and presupposition), under the same side conditions as (a).

Restriction does not commute with `step`. For `σ : ISub k' k` and `step S t = some t'`, the step of `t.isub σ` is `t'.isub σ` except in these cases:

- A face decided false at stage `k` holds after `σ`, while true faces stay true (`entails_one_subst`). This happens for the face of `transp`/`hcomp` (`transpFace`, `hcompFace` instead of computing by the type), for `split`, for the face of `glue`/`glueEl`/`unglue` (`glueFace`, `glueElFace`, `unglueFace`), and for the boundaries of a constructor (`conBnd`), where an earlier boundary may come to hold.
- The same deviations occur in head positions below, for the line of a Kan operation and the scrutinee of an eliminator.
- `transpGlue` uses `δ := φ.forall0`. Restriction gives `(φ.forall0).subst τ`, which is equivalent (`forall0_subst`) but not equal to `(φ.subst τ⁺).forall0`.

In every case both results are `≡` to `t.isub σ`, by soundness and substitution.

The PER of (c) does not need a commutation lemma. Like the current relation, it is Kripke by definition: each clause quantifies over all restrictions `σ` and reduces `t.isub σ` at stage `k'` from scratch. Closure under restriction is then composition of restrictions. The fundamental lemma handles each redex at each restriction separately: if the face holds after `σ`, the face rule applies and its reduct is related by the induction hypothesis; otherwise the computation rule applies. This is how `RE_hcomp_face`/`RE_transp_face` already split the Kan lemma. Weak-head normal forms with a type-former head (`univ`, `pi`, `sigma`, `path`, `ipi`, `data`) never step, so they stay normal under restriction. The heads that can start to step after restriction are `glue`, `glueEl`, `split`, `con` with boundaries, and stuck eliminations. These are exactly the cases above.

### Milestone (c): design

`Model/Whnf/Rel.lean` (sub-step c1, done) defines `Comp2 S X m k f : Pack2` by the same rank recursion as `Comp`. It has a type relation `ty A A'` and an element relation `el A t t'`; `RT2`/`RE2` are its instances at `semK A`.

- Every element relation includes `EB`: both sides typed and judgmentally equal.
- Every type relation includes typing, the code, and `TyEq A A'`.
- Types of every former, and elements of inductive types, are observed through their weak-head normal forms at every restriction (`∀ σ, RedW S (A.isub σ) (head …)`). Normal forms are unique, so the relations are transitive without injectivity of type formers or constructors.
- Elements of Π, Σ, path, `(i : I) → A` and Glue types are observed through their eliminations.
- The Glue type clause relates the two whnfs' bases, faces (both equal to the code's face), fibres and equivalences. So `RT2 U (glue A φ T e) (glue A' φ' T' e')`, where both sides are their own whnfs, gives `A ≡ A'` and, from the equivalences at the restrictions where `φ` holds and `eq_local_faces`, `e ≡ e'` under `φ`.

Remaining sub-steps:

- (c2) Unfolding lemmas per code. Kripke restriction (re-indexing the `∀ σ` clauses). Symmetry and transitivity (rank induction, using uniqueness of whnfs). Transfer of elements along related types. Semantics and typing of related terms.
- (c3) Head expansion along substitution-stable steps (`∀ σ, step (t.isub σ) = some (t1.isub σ)`). Faces that come to hold under restriction are handled per stage where the redex is known.
- (c4) Introduction and elimination clauses per former, and the Kan lemma for related lines and data, including the binary `hcompCon` via projections, which also discharges `HCSound`.
- (c5) The fundamental lemma for `HasTy0` and `EqTm0`, with related closing substitutions. `UGSound` and `GlueCompat` are corollaries.
