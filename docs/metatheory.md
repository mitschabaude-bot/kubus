# Metatheory: a textbook specification

The spec (`KubusCore/Rules.lean`) has primitive rules for weakening (`wk`, `dwk`), single substitution (`subst`, `dsubst`), presupposition (`eqL`, `eqR`) and inversion of type formers (`piDom`, …, `glueFib`). `KubusCore/Meta/` defines the judgments without these rules and proves which of them are admissible. Everything below is proven without `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`); `KubusCore/Meta/Main.lean` has the summary.

## The minimal judgments

`Wf0`, `HasTy0`, `HasTele0`, `EqTele0`, `EqTm0` (`Meta/Minimal.lean`) are generated from `Rules.lean` by `Meta/scripts/gen_minimal.py`, which drops the 19 primitive rules and applies the changes below. It fails if a spec change touches an edited rule. The two anonymous substitutions in `elimHcomp` and `transpHcomp` are named (`consSub`, `skip1I`, definitionally equal), so that lemmas can refer to them.

Premises added (presupposition-style; recovered from the spec's premises in `Equiv.lean`, by generation lemmas and, for M3, validity):

- M1 `ipi` (typing and congruence): the context is well-formed. Every other rule already has a premise in the same context.
- M2 `HasTy0.glueEl`: the equivalence `e` is typed.
- M3 `face`: the type is a type; `faceU` is the face rule at a universe.
- M6 `con`, `elim`: the parameters match the parameter telescope.

The spec itself carries M4 and M5 since commit "spec: M4 M5" (`EqTm.glueEl`/`EqTm.unglue` congruent in the equivalence; `EqTm.transpGlue` at any `δ` equivalent to `∀i. φ`, via `transpGlueWith`), see issues 1 and 2 below. The kernel is unaffected (it passes `refl` and `entails_refl`); the model's `Sound.lean` has to be adapted to the new premises.

## Results

All results assume `SigClosed S`: the declarations of the signature are closed (implied by `WfSig S`). Without it weakening fails, e.g. for a constant whose type has a free variable.

| spec rule | admissible for the minimal judgments | file |
|---|---|---|
| `wk`, `dwk` (typing and equality) | yes | `Weaken.lean` |
| `HasTy.subst`, `HasTy.dsubst`, `EqTm.dsubst` | yes | `Structural.lean` |
| `EqTm.subst` | given that the right-hand sides are typed | `Structural.lean` |
| `piDom`, `piCod`, `sigmaDom`, `sigmaCod`, `pathLine`, `pathLeft`, `pathRight`, `ipiLine`, `glueFib` | yes | `Inversion.lean` |
| `eqL`, `eqR` | given `ContractaTyped` (15 computation rules) | `Presup.lean` |

Build with `lake build KubusCore.Meta` (the executable does not depend on it).

The general theorems behind these:

- **Renaming** (`Ren.lean`, `ren_ty`/`ren_eq`): term variables arbitrarily, interval variables injectively.
- **Substitution and functionality** (`Substitution.lean`, `sub_ty`/`sub_eq`): simultaneous substitution of term and interval variables. For typing derivations also functionality: judgmentally equal term substitutions and interval substitutions equal in the free De Morgan algebra give judgmentally equal results.
- **Cofibrations** (`Cof.lean`): `I.Entails` is entailment over assignments into the Kleene algebra `{0, a, 1}`. Hence it is stable under all interval substitutions, and `∀i. φ` commutes with substitution up to equivalence.
- **The face rule under substitution** (`SubFace.lean`): an instance `t ≡ t[d/i]` under `Φ ⊨ i = d` becomes `t[τ] ≡ t[τ[i:=d]]` under `Φ' ⊨ τ(i) = d`, which is not a face rule instance when `τ(i)` is compound. It is proven by splitting `Φ'` into its faces (`EqTm.local`), substituting each face's endpoints with the face rule, and then functionality, since on a face `τ(i)` and `d` are equal in the free De Morgan algebra.
- **Inversion** by generation lemmas: a typing of `Π A B` comes from the formation rule followed by conversions at universes, along which typings transport. No injectivity is needed since inversion starts from a syntactic type former.
- **Validity** (`Valid.lean`) and **presupposition** (`Presup.lean`): proven for all rules except the 15 computation rules in `ContractaTyped` (assumed: their contractum is typed whenever the redex is). Proven are the structural rules, all congruences, the η-rules, the face rules, the boundary rules of systems, `transp` and `hcomp`, `transpU`, `transpData0`, the Glue face and η rules, and all `hcomp` computation rules: `hcompPi`, `hcompIPi` (`HcompTyped.lean`), `hcompPath` (`KanPath.lean`), `hcompSigma` (`KanSigma.lean`), `hcompGlue` (`KanGlue.lean`), `hcompU` (`KanU.lean`). These rest on typings of the derived operations: `hfill` with its boundary and `comp` (`KanFill.lean`), `isContr`/`fiber`/`isEquiv`/`equiv`, the transport filler, `lineFun`, `idIsEquiv` (the identity is an equivalence) and `lineEquiv` (transport along a line is an equivalence) (`KanU.lean`), and interval substitution lemmas (`Derived.lean`).
- **Equivalence** (`Equiv.lean`, `SigWk.lean`): `spec_to_minimal'`: `HasTy S ⊆ HasTy0 S` for `WfSig S`, given `ContractaTyped` for the prefixes of `S`. `minimal_to_spec`: `HasTy0 S ⊆ HasTy S`, unconditionally with M4 and M5 in the spec.

## Spec issues

1. **Interval substitution needs congruence of `unglue`/`glueEl` in the equivalence (M4).** Functionality is needed for the face rule's case of substitution, and functionality for `unglue φ e g` needs `e ≡ e' ⇒ unglue φ e g ≡ unglue φ e' g`, which the spec does not provide. I believe `dsubst` is not admissible over the spec's other rules. With interval variables `i, l`, a context `g : Glue A [l ↦ (T, e₀)]` and `E(r) := split r e₀ r e₀`, the term `hcomp A [i ↦ _. unglue l E(i) g] (unglue l E(1) g)` is typable: its side condition `unglue l E(i) g ≡ unglue l E(1) g` under `i` is the face rule. At `i := j ∨ k` the side condition becomes, on the face `j = 1`, `unglue l E(1 ∨ k) g ≡ unglue l E(1) g` with syntactically different equivalences that are equal only judgmentally, and no rule other than `dsubst` relates them. (Not formally proven non-derivable.) M4 is valid in the intended model, and `EqTm.glue` already has this form.
2. **`transpGlue` is not syntactically stable under interval substitution (M5).** `(φ.forall0)[τ]` and `(φ[τ⁺]).forall0` are equivalent cofibrations but different terms, so a substituted rule instance is not a rule instance. Relating the two contracta needs the contractum to be typed (then congruence gives it), which needs injectivity (issue 3).
3. **Presupposition needs injectivity of type formers.** Computation rules are stated for a redex of any type `T`. To type the contractum at `T` one has to decompose the redex's typing, and conversions on the way require injectivity: for `piBeta`, `lam A t : Π A' B'` only gives `Π A B ≡ Π A' B'` for the `B` the body was checked against. Injectivity of `Π`, `Σ`, `PathP`, `(i : I) → A`, Glue and inductive types is a normalization-strength property, not provable by induction on derivations, so `eqR` is not admissible by elementary means for: `piBeta`, `fstBeta`, `sndBeta`, `pathBeta`; `glueBeta` (the base of the `glue` element's type versus the `unglue`'s; Glue types determine their base only off `φ`); `transpPi`, `transpSigma`, `transpPath`, `transpIPi`, `transpGlue` (the contracta need the components of the line to be constant on `φ`, which only follows from the line's constancy by injectivity); `elimCon`, `elimHcomp`, `transpCon`, `transpHcomp` (parameters of the scrutinee versus the eliminator). `conBnd` is blocked for a different reason, issue 4. The `hcomp` rules need no injectivity and are all proven.
4. **`conBnd` is not derivable from the signature's boundary typing.** Presupposition for `conBnd` needs `bndAt b ps args rs : T`. For a simple boundary `b` this reduces, by substituting the constructor's arguments, to `Ctor.bndTyped`: the point arguments of nested constructors have the nested constructor's argument types. But `DataDecl.Wf` checks these equations (and the typing of `b`) in `Sc = S.take d ++ [data (D.truncate c)]`, and `Sc` does not embed into `S`: its index-`c` constructor is a nullary dummy, while in `S` constructor `c` has arguments, and an `elim` over `d` in `Sc` has `c + 1` branches, in `S` it needs all of them. A derivation in `Sc` may go through such terms (e.g. a large elimination in a conversion), so neither induction nor any term translation carries it to `S`. Proposed fix: check the `bndTyped` equations in `S.take d` (the signature before the declaration), in the context of the parameters and the point arguments only. This is possible because point argument types do not mention `d` (`mentionsData d = false`) nor earlier recursive arguments (`noRecDeps`); the nested constructor's argument type at position `k` is instantiated with the outer point arguments at point positions, and at recursive positions (on which it does not depend, `noRecDeps` of the nested constructor) with anything. Then `conBnd`'s presupposition follows from prefix weakening (`SigWk.lean`), substitution, and the `con` rule, by recursion on the simple boundary. Kernel: compute the strengthened context and lower the indices (both types are free of the recursive arguments); the check runs once per declaration. Model: unaffected or easier (equations in a smaller signature).

## Proposal: computation rules at the type of their premises

The 14 injectivity-blocked rules in `ContractaTyped` (all except `conBnd`) are stated for a redex of any type `T` (premise `HasTy Γ redex T`). Textbook form: replace that premise by the typing premises of the redex's constituents, and conclude at the type they determine. Then presupposition is the typing of the contractum from those premises, without inverting `T`: for the β-rules a corollary of substitution, for the others typing derivations of the same kind as the `hcomp` ones (not yet done; `comp` and the fillers they use are).

| rule | premises (replacing `redex : T`) | conclusion type |
|---|---|---|
| `piBeta` | `t : B` in `A :: Γ`, `a : A` | `B[a]` |
| `fstBeta`, `sndBeta` | `Σ A B : U l`, `a : A`, `b : B[a]` | `A`, `B[a]` |
| `pathBeta` | `t : A` in `Ψ+1`, `r` scoped | `A[r]` |
| `glueBeta` | the `glueEl` premises: `Glue A φ T e : U l`, `e : Equiv T A` and `t : T` under `φ`, `a : A`, `e.1 t ≡ a` under `φ` | `A` |
| `transpPi`, `transpSigma` | `A : U l` and `B : U l` (in `A :: Γ`) at `Ψ+1`, `φ` scoped, under `φ`: `A ≡ A(0)` and `B ≡ B(0)`, `u0 : line(0)` | `line(1)` |
| `transpPath` | `A : U l` at `Ψ+2`, `a`, `b` at the ends, under `φ`: `A`, `a`, `b` constant, `p0 : line(0)` | `line(1)` |
| `transpIPi` | `A : U l` at `Ψ+2`, under `φ`: `A` constant, `u0 : line(0)` | `line(1)` |
| `transpGlue` | as now (`A : U l`, `e : Equiv T A` under `φ`), plus under `ψ`: `A`, `T`, `e` and `φ` constant, `u0 : line(0)` | `line(1)` |
| `elimCon`, `elimHcomp` | the `elim` premises at parameters `ps`, the scrutinee at the same `ps` (`con d c ps args rs` with `args` in the telescope at `ps`; `hcomp (data d ps) …`) | `P[scrutinee]` |
| `transpCon`, `transpHcomp` | the line `data d ps` at `Ψ+1` constant under `φ`, the scrutinee's parameters `ps(0)` | `data d ps(1)` |

What blocks the current form is visible in the table: the contractum needs the constituents' types (the body's `B`, the components of a line and their constancy under `φ`, the scrutinee's parameters), and from `redex : T` they are only reachable through conversions, which needs injectivity of `Π`, `Σ`, `PathP`, `(i : I) → A` and `data` in its parameters (Glue in its base off `φ`).

**Kernel cost: it does not have these premises at hand.** `whnfStep` receives only `ht : HasTy Γ redex T` (in checking mode; in inference mode the redex typing comes from `HasTy.eqR` of a congruence), and builds `EqTm.piBeta ht` etc. in constant time. With textbook rules it has to produce, per reduction step:

- β-rules: the typing of the λ-body / pair components / path body. Inference computed them when the redex was first checked, but they are not kept (`Inf` stores the typing of the term, not of its subterms), and redexes created by substitution were never inferred. So each step re-infers the redex's constituents (re-checking a λ-body is linear in its size, so a chain of β-steps can become quadratic), then converts `B[a]` to the expected `T`, which in inference mode is literally `B1[a]` after `whnfTy` of the function's type and needs a conversion check (or injectivity) when the inferred `Π` was not syntactically the λ's. Alternatively thread subterm typings through `Inf`/`Red`, a larger refactor.
- `transp` rules: infer the line's components (as `transpRule` already does for Glue) and check their constancy under `φ`, i.e. two to four conversion checks per transport step under a restricted context. `transpGlue`'s constancy of `φ` is an entailment check.
- data rules: check that the scrutinee's parameters are convertible to the eliminator's, or re-check `args` in the telescope at `ps` (one conversion check per parameter, or a telescope check per step).

**Model cost: about the same.** The model validates the current rules without injectivity: `sem` is a partial interpretation that is defined (non-empty) only where the redex's semantic conditions hold, so `redex : T` gives the contractum's value equals the redex's on all points (`sem_EqTm_piBeta`, `cond_of_sem_transp`, …). For textbook rules the same value equation applies, after assembling the redex's semantic typing from the premises with the existing semantic typing rules (`app` of `lam`, `transp`, `elim`); no new semantic content, some bookkeeping per rule. `piC_inj` and friends stay unused by these rules.

**Alternative: primitive injectivity.** Add inversion rules for equations, `Π A B ≡ Π A' B' : U l ⊢ A ≡ A'` and `B ≡ B'` (in `A :: Γ`), likewise for `Σ`, `PathP` (line and ends), `(i : I) → A`, and `data d ps ≡ data d ps' ⊢ ps ≡ ps'`. Then the current "any `T`" rules stay, the kernel is unchanged (rules are only added), and presupposition of the 12 rules other than `glueBeta` and `transpGlue` becomes provable by generation, injectivity and the contractum typings. These rules are stable under substitution and renaming, and their own presupposition follows from inversion and context conversion. The model validates them with the code injectivity lemmas it has (`piC_inj`, `sigmaC_inj`, `pathC_inj`, `ipiC_inj`; data codes would need one). `glueBeta` and `transpGlue` still need the textbook form, since a Glue type determines neither its base nor `T`, `e` everywhere (on `φ` it is `T`). The price is a less minimal spec: injectivity is a theorem of a normalizing system, here an axiom of the judgment, which the model has to justify.

Recommendation: the injectivity alternative, plus textbook `glueBeta` and `transpGlue`. Kernel cost of those two: `glueBeta` needs one inference of the `glueEl` per step (its Glue type gives `A`, `T`, `e`); `transpGlue` already infers `A` and checks `e`, and adds the constancy checks of `A`, `T`, `e` under `ψ` and one entailment for `φ`. Full textbook form for all 14 only if a cheaper kernel path to the premises is found.
