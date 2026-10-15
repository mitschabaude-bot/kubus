# Canonicity for Kubus Core

Canonicity is proven unconditionally in Lean as `Model.Whnf.canonicity` (`Model/Whnf/Canon2.lean`). It assumes a well-formed signature and the term's typing, with no additional Glue compatibility or HIT elimination obligation. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`, checked by `ci/Axioms.lean`.

## Statement

Closed terms live in `Ψ = 0`, `Φ = .one`, `Γ = []`. The theorem is:

```lean
theorem Model.Whnf.canonicity (S : Sig) (d : Nat) (D : DataDecl) (t : Tm)
    (hW : WfSig S) (hD : S[d]? = some (.data D)) (hp : D.params = [])
    (ht : HasTy S 0 .one [] t (.data d .tnil)) :
    ∃ t', EqTm S 0 .one [] t t' (.data d .tnil) ∧ Canon S d t'
```

`Canon` and the corresponding proposition `Canonicity` are defined in `Model/Canon/Statement.lean`. A canonical element is a constructor whose boundary does not hold, with canonical recursive arguments and interval arguments literally `0` or `1`; for HITs it can also be a formal composition with an empty system over a canonical element. Point arguments are closed and typed, without a claim that they themselves are canonical.

- For ordinary inductive types, the canonical forms are constructor terms. For `Nat`, they are numerals.
- Closed interval arguments normalize to `0` or `1` using constructor congruence and `I.Eq`.
- A constructor whose boundary holds computes to that boundary; boundaries use recursive arguments and earlier constructors.
- A composition whose face holds computes to its tube's end. In a non-HIT, composition computes componentwise (`hcompCon`). In a HIT, a closed false face is equivalent to `.zero`, and the tube under that face is irrelevant, giving the canonical form `.hcomp (.data d .tnil) .zero a.dshift a`.
- Transport in a parameterless data type is the identity (`transpData0`).

The minimal judgments inherit the result through `wfSig_of_wfSig0` and `minimal_to_spec`. The statement covers parameterless data types, including HITs; it is not a theorem of full normalization for all open terms.

## Proof structure

The final proof combines the canonical form construction in `Model/Canon/` with the binary logical relation in `Model/Whnf/`. The set model supplies well-founded semantic codes. The logical relation produces syntactic typing and judgmental equality evidence, rather than inferring syntactic equality from semantic equality.

`Comp2` (`Whnf/Rel.lean`) is defined by well-founded recursion on code rank. Its type and element relations are instantiated as `RT2` and `RE2`. They are partial equivalence relations, stable under restriction, near-invariance and local head expansion. Types are observed through their deterministic weak-head normal forms at every interval restriction. Coherence relates a restricted normal form to the normal form found after further restriction, since reduction steps need not commute with interval substitution.

Universe elements carry their code's Kan operations. The type clauses carry hereditary Kan evidence for Π/Σ domains and fibres at related syntactic arguments, path and interval lines, Glue bases and face fibres, and data parameters and constructor argument types at related prefixes. `RE2_univ_kan` and component inversion recover this evidence for the validity rules. There is no global Kan oracle, `KTAt`, or stronger mutual fundamental lemma.

The data element relation is the mutual inductive pair `DR2`/`DR2At`. Its heads are constructors with related arguments, or formal compositions in a HIT. The formal composition clause stores both sides' boundary coherence: the tube at zero is related to the base at every restriction where its face holds. Every construction site supplies this from its own premises, including composition, transport, expansion, restriction and near-invariance.

The fundamental lemma (`fund2`, `Whnf/Fund2.lean`) proves validity of every minimal equality derivation, with typing as the diagonal. The outer signature-prefix induction `hyps_take` constructs definition validity, declared type validity and `HITHyp2`. Boundary type validity comes from `bndTy_of_valid` and the fundamental lemma at `S.take d`. `Boundary2.constructors_and_boundaries` derives constructor relatedness and boundary expansion jointly from the checked overlap agreement and prefix boundary typing. These are derived invariants; no `DataHyp2` or `Obl2` bundle remains.

## Higher inductive elimination

The complete validity lemmas are `valid_elimH` and `valid_elimEqH` (`Whnf/Valid2ElimH33.lean`), `valid_elimConH` (`Valid2ElimH18.lean`) and `valid_elimHcompH` (`Valid2ElimH22.lean`). The four rules require no additional elimination hypothesis.

`Valid2ElimH3.lean` through `Valid2ElimH11.lean` close the branch telescopes and interval binders with related arguments and interpret boundary equations. `bndInterp_rel2` identifies elimination of a simple boundary tree with its constructor algebra, including arbitrary typed parameter annotations. `elimCon_compH` (`Valid2ElimH14.lean`) proves constructor computation at every restriction, including where a boundary holds.

`Valid2ElimH12.lean` through `Valid2ElimH17.lean` relate tubes, fillers, motive lines and the formal composition contracta, using the code's own Kan evidence. `elimHcomp_compH` (`Valid2ElimH19.lean`) proves composition computation at every restriction, including where the face holds. `ElimInv2` and `fund2_elimInv` recover valid components by structural inversion of typing. `ElimValid2` packages them and preserves the branch boundary premises under faces and interval binders.

The raw relation induction also records normalization to the eliminator contractum of each scrutinee normal form (`ElimNormH`). `elimNorm_hcompH`, `bndNormH` and `elimNorm_conH` handle formal compositions, simple boundary trees and constructors. The two raw stage cases and `elimRedH_coh` compare contracta across restrictions, including when a new boundary or face holds. Head expansion then proves `elim_DR2H` (`Valid2ElimH32.lean`): eliminations of related HIT elements are related. This is an induction on `DR2`/`DR2At`, not a strengthening of the fundamental lemma.

## Glue compatibility is derived

`Model.Whnf.glueCompat` (`Whnf/Canon2.lean`) proves `GlueCompat S` from `WfSig S`. The binary fundamental lemma relates judgmentally equal Glue types, and inversion of their weak-head type relation supplies judgmentally equal bases and equivalences under their equivalent faces. This discharges the premise of `Model.Canon.canonicity_of_glueCompat`, the internal canonical form construction, to obtain the unconditional theorem.

The compatibility statement concerns terms with no term variables, at any interval stage `k`, under the trivial face `.one`. Its premises include equivalent faces that do not hold at that stage. It is a metatheorem, not an extra typing rule: where a Glue face holds, the base and equivalence annotations are unconstrained. The restriction to the trivial face is essential; the statement is not generalized to arbitrary face contexts.

## History: the false Glue formulation

The earlier canonicity development was conditional on a Glue compatibility statement. Its first formulation concluded equivalence of the faces instead of assuming it, and was false. This would have made the corresponding conditional canonicity theorem vacuous: `glue A φ T e ≡ glue (glue A φ T e) 1 (glue A φ T e) idEquiv` by `glueFace` (symmetrically), with `¬ φ` but `1 ⇏ φ`.

The corrected statement assumes face equivalence. In the canonical form construction it follows from the semantic code of the Glue type and completeness for cofibrations (`ent_of_face_eq`, `Model/Canon/Sub.lean`). The binary logical relation now proves the remaining annotation compatibility syntactically. The unconditional theorem uses the corrected, derived statement; it does not assume the false formulation.

Decision C1 also changed an earlier design in which every inductive type treated `hcomp` formally: `hcomp (data Nat []) 0 zero.dshift zero` would then have been a closed `Nat` with no numeral canonical form. The current theory computes composition componentwise in types without path constructors, and keeps formal compositions only for HITs. The set model validates this in `Model/DataHR.lean` and `Model/Rules/DataHcomp.lean`.

## Verification

From `model/`:

```sh
lake build
lake env lean ci/Axioms.lean | diff - ci/axioms.expected
```

The proofs contain no `sorry`. The axiom audit includes `Model.Whnf.canonicity` and permits only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.
