# Metatheory: a textbook specification

The spec (`KubusCore/Rules.lean`) has primitive rules for weakening (`wk`, `dwk`), single substitution (`subst`, `dsubst`), presupposition (`eqL`, `eqR`) and inversion of type formers (`piDom`, …, `glueFib`). `KubusCore/Meta/` defines the judgments without these rules and proves which of them are admissible. Everything below is proven without `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`); `KubusCore/Meta/Main.lean` has the summary and `KubusCore/Meta/Final.lean` the end result.

## The minimal judgments

`Wf0`, `HasTy0`, `HasTele0`, `EqTele0`, `EqTm0` (`Meta/Minimal.lean`) are generated from `Rules.lean` by `Meta/scripts/gen_minimal.py`, which drops the 19 primitive rules and applies the changes below. It fails if a spec change touches an edited rule. The two anonymous substitutions in `elimHcomp` and `transpHcomp` are named (`consSub`, `skip1I`, definitionally equal), so that lemmas can refer to them.

Premises added (presupposition-style; recovered from the spec's premises in `Equiv.lean`, by generation lemmas and, for M3, validity):

- M1 `ipi` (typing and congruence): the context is well-formed. Every other rule already has a premise in the same context.
- M2 `HasTy0.glueEl`: the equivalence `e` is typed.
- M3 `face`: the type is a type; `faceU` is the face rule at a universe.
- M6 `con`, `elim`: the parameters match the parameter telescope.

The spec carries M4 and M5 (`EqTm.glueEl`/`EqTm.unglue` congruent in the equivalence; `EqTm.transpGlue` at any `δ` equivalent to `∀i. φ`), see issues 1 and 2 below.

## Spec patches on this branch (not yet on phase2)

Three commits change only `Rules.lean`, `Syntax.lean` and the kernel, in order:

1. "spec: injectivity of type formers; glueBeta takes the typing of the base element": `EqTm.piInjDom`, `piInjCod`, `sigmaInjDom`, `sigmaInjCod`, `pathInjLine`, `pathInjLeft`, `pathInjRight`, `ipiInj`, and `EqTele.dataInj` (with the two parameter telescopes as premises). Codomains and lines are instantiated (`B[a] ≡ B'[a]` for `a : A`, `A(r) ≡ A'(r)`), so that every conclusion lives in the context of its premise; the forms with the conclusion in an extended context are not stable under substitution by an induction on derivations. `glueBeta` gets the premise `a : G`: a Glue type does not determine its base (on `φ` it is `T`), so this cannot be recovered by injectivity. The kernel checks `a` against the type it already has (one check per `glueBeta` step).
2. "spec: no-confusion of type formers": `EqTm.noConf`: an equation between type formers with different heads (`Tm.headClash`: `Π`, `Σ`, `PathP`, `(i : I) → A`, universes, inductive types by index) makes any two terms of a type equal. Injectivity alone does not invert conversion chains: a chain from a `Π` type to a `Π` type may pass through a universe (via cumulativity, a `λ` typed in a universe), and `plam` is typed both at path types and at `(i : I) → A`. The kernel never uses it.
3. "spec: P11": point argument types are also typed in the prefix signature over the parameters and earlier point arguments (`DataDecl.pointCtx`), like P8 for the boundary equations. `transpCon` transports along argument types at arbitrary parameters; the existing check in `S ++ [truncate 0]` over `argCtx` does not carry over to `S` (issue 4). The kernel checks the new clause once per constructor (`checkCtorArgsPoint`). The old clause is now redundant up to the model's needs.

`transpGlue` needs no change: its contractum is typed from the current premises (`KanTranspGlue.lean`), since under `δ` (`∀i. φ`) the Glue line is `T` at every `i` (`glueFace`), so the line's constancy gives `T`'s. The lib certifies with all three patches. The model's `Sound.lean` needs cases for the new rules (injectivity via the code injectivity lemmas, `noConf` vacuously since equal codes have equal heads, `glueBeta`'s and `Wf`'s extra premises are only more assumptions).

## Results

All results assume `SigClosed S` (implied by `WfSig S`).

| spec rule | admissible for the minimal judgments | file |
|---|---|---|
| `wk`, `dwk` (typing and equality) | yes | `Weaken.lean` |
| `HasTy.subst`, `HasTy.dsubst`, `EqTm.dsubst` | yes | `Structural.lean` |
| `EqTm.subst` | given that the right-hand sides are typed | `Structural.lean` |
| `piDom`, `piCod`, `sigmaDom`, `sigmaCod`, `pathLine`, `pathLeft`, `pathRight`, `ipiLine`, `glueFib` | yes | `Inversion.lean` |
| `eqL`, `eqR` | yes, for `WfSig S` | `Presup.lean`, `Final.lean` |

`spec_to_minimal` (`Final.lean`): `WfSig S → HasTy S Ψ Φ Γ t A → HasTy0 S Ψ Φ Γ t A` (and `spec_to_minimal_eq`), with no other hypothesis; `minimal_to_spec` (`Main.lean`) is unconditional. Build with `lake build KubusCore.Meta` (the executable does not depend on it).

The general theorems behind these:

- **Renaming** (`Ren.lean`, `ren_ty`/`ren_eq`): term variables arbitrarily, interval variables injectively.
- **Substitution and functionality** (`Substitution.lean`, `sub_ty`/`sub_eq`): simultaneous substitution of term and interval variables. For typing derivations also functionality: judgmentally equal term substitutions and interval substitutions equal in the free De Morgan algebra give judgmentally equal results.
- **Cofibrations** (`Cof.lean`): `I.Entails` is entailment over assignments into the Kleene algebra `{0, a, 1}`. Hence it is stable under all interval substitutions, and `∀i. φ` commutes with substitution up to equivalence.
- **The face rule under substitution** (`SubFace.lean`): an instance `t ≡ t[d/i]` under `Φ ⊨ i = d` becomes `t[τ] ≡ t[τ[i:=d]]` under `Φ' ⊨ τ(i) = d`, proven by splitting `Φ'` into its faces (`EqTm.local`), the face rule on each, and functionality.
- **Inversion** by generation lemmas: a typing of `Π A B` comes from the formation rule followed by conversions at universes, along which typings transport.
- **Presupposition** (`Presup.lean`, generated by `Meta/scripts/presup.py`): by a mutual structural recursion that also computes generation data. The third component is `IsTypB` (a type, or a universe of level at most `maxLevel`), which bounds the levels of all type equations, so that a conversion chain from an introduction form's natural type to the expected type collapses into one equation by cumulativity (`Rel`, `Rel.collapse` in `PresupB.lean`), or is explosive by `noConf` when it passes through a universe. The functions `genI`, `genApp`, `genFst`, `genSnd`, `genPapp`, `genElim`, `genTransp` recurse on the redex's typing derivation and call `pre_eq` on its conversion steps. Then:
  - β-rules (`BetaTyped.lean`): injectivity relates the natural type of the `λ`/pair/`plam` to the expected one.
  - `transp` in `Π`, `Σ`, path types, `(i : I) → A` (`KanTransp.lean`): the line's constancy gives its components' constancy by injectivity; the contracta are typed with the transport filler and `comp`.
  - `transpGlue` (`KanTranspGlue.lean`): no injectivity needed.
  - `hcomp` in every type former (`HcompTyped.lean`, `KanPath.lean`, `KanSigma.lean`, `KanGlue.lean`, `KanU.lean`), resting on `hfill`, `comp`, `fill` (`KanFill.lean`) and the equivalence machinery `isContr`, `fiber`, `isEquiv`, `idIsEquiv`, `lineEquiv` (`KanU.lean`).
  - inductive types (`DataContracta.lean`, `DataTele.lean`): `elimCon`, `elimHcomp`, `transpHcomp`, `transpCon`, with `dataInj` relating the scrutinee's parameters to the eliminator's.
  - `conBnd` (`ConBnd.lean`): the boundary is typed by recursion on the simple boundary, with the point arguments' type equations from `Ctor.bndTyped` (P8).
  - `conBnd` and `transpCon` read the signature's checks in the prefix before the inductive type; `ContractaTyped` collects them and `Final.lean` discharges it for `WfSig S` by induction on the signature (the prefix's spec judgments are minimal ones by the induction hypothesis).
- **Equivalence** (`Equiv.lean`, `SigWk.lean`, `Final.lean`).

## Spec issues (resolved)

1. **Interval substitution needs congruence of `unglue`/`glueEl` in the equivalence (M4).** Functionality is needed for the face rule's case of substitution, and functionality for `unglue φ e g` needs `e ≡ e' ⇒ unglue φ e g ≡ unglue φ e' g`. M4 is in the spec.
2. **`transpGlue` is not syntactically stable under interval substitution (M5).** `(φ.forall0)[τ]` and `(φ[τ⁺]).forall0` are equivalent but different terms. M5 is in the spec.
3. **Presupposition needs injectivity of type formers** for the computation rules stated at any type `T`: resolved by the primitive injectivity and no-confusion rules (patches 1 and 2), with `glueBeta` taking the base element's typing.
4. **Checks in signatures that do not embed into `S`.** `DataDecl.Wf` checks boundaries and argument types in `S.take d ++ [data (D.truncate c)]`, whose index-`c` constructor is a dummy and whose eliminators have fewer branches, so derivations there do not carry over to `S`. The checks the metatheory needs are in the prefix `S.take d` instead: the boundary equations (P8, on phase2) and the point argument types (P11, patch 3).
