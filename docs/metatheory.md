# Metatheory: a textbook specification

The spec (`KubusCore/Rules.lean`) has primitive rules for weakening (`wk`, `dwk`), single substitution (`subst`, `dsubst`), presupposition (`eqL`, `eqR`) and inversion of type formers (`piDom`, …, `glueFib`). `KubusCore/Meta/` defines the judgments without these rules and proves which of them are admissible. Everything below is proven without `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`); `KubusCore/Meta/Main.lean` has the summary.

## The minimal judgments

`Wf0`, `HasTy0`, `HasTele0`, `EqTele0`, `EqTm0` (`Meta/Minimal.lean`) are generated from `Rules.lean` by `Meta/scripts/gen_minimal.py`, which drops the 19 primitive rules and applies the changes below. It fails if a spec change touches an edited rule. The two anonymous substitutions in `elimHcomp` and `transpHcomp` are named (`consSub`, `skip1I`, definitionally equal), so that lemmas can refer to them.

Premises added (presupposition-style; recovered from the spec's premises in `Equiv.lean`, by generation lemmas and, for M3, validity):

- M1 `ipi` (typing and congruence): the context is well-formed. Every other rule already has a premise in the same context.
- M2 `HasTy0.glueEl`: the equivalence `e` is typed.
- M3 `face`: the type is a type; `faceU` is the face rule at a universe.
- M6 `con`, `elim`: the parameters match the parameter telescope.

Rules generalized (not derivable in the spec, see the issues below):

- M4 `EqTm0.glueEl`, `EqTm0.unglue`: congruence also in the equivalence (`e ≡ e'` under `φ`), as `EqTm.glue` already is.
- M5 `EqTm0.transpGlue`: any `δ` equivalent to `∀i. φ` in the face lattice, instead of the syntactic `φ.forall0`.

## Results

All results assume `SigClosed S`: the declarations of the signature are closed (implied by `WfSig S`). Without it weakening fails, e.g. for a constant whose type has a free variable.

| spec rule | admissible for the minimal judgments | file |
|---|---|---|
| `wk`, `dwk` (typing and equality) | yes | `Weaken.lean` |
| `HasTy.subst`, `HasTy.dsubst`, `EqTm.dsubst` | yes | `Structural.lean` |
| `EqTm.subst` | given that the right-hand sides are typed | `Structural.lean` |
| `piDom`, `piCod`, `sigmaDom`, `sigmaCod`, `pathLine`, `pathLeft`, `pathRight`, `ipiLine`, `glueFib` | yes | `Inversion.lean` |
| `eqL`, `eqR` | given `ContractaTyped` (19 computation rules) | `Presup.lean` |

The general theorems behind these:

- **Renaming** (`Ren.lean`, `ren_ty`/`ren_eq`): term variables arbitrarily, interval variables injectively.
- **Substitution and functionality** (`Substitution.lean`, `sub_ty`/`sub_eq`): simultaneous substitution of term and interval variables. For typing derivations also functionality: judgmentally equal term substitutions and interval substitutions equal in the free De Morgan algebra give judgmentally equal results.
- **Cofibrations** (`Cof.lean`): `I.Entails` is entailment over assignments into the Kleene algebra `{0, a, 1}`. Hence it is stable under all interval substitutions, and `∀i. φ` commutes with substitution up to equivalence.
- **The face rule under substitution** (`SubFace.lean`): an instance `t ≡ t[d/i]` under `Φ ⊨ i = d` becomes `t[τ] ≡ t[τ[i:=d]]` under `Φ' ⊨ τ(i) = d`, which is not a face rule instance when `τ(i)` is compound. It is proven by splitting `Φ'` into its faces (`EqTm.local`), substituting each face's endpoints with the face rule, and then functionality, since on a face `τ(i)` and `d` are equal in the free De Morgan algebra.
- **Inversion** by generation lemmas: a typing of `Π A B` comes from the formation rule followed by conversions at universes, along which typings transport. No injectivity is needed since inversion starts from a syntactic type former.
- **Validity** (`Valid.lean`) and **presupposition** (`Presup.lean`): proven for all rules except the 19 computation rules in `ContractaTyped` (assumed: their contractum is typed whenever the redex is). Proven are the structural rules, all congruences, the η-rules, the face rules, the boundary rules of systems, `transp` and `hcomp`, `transpU`, `transpData0`, `hcompPi`, `hcompIPi` (`HcompTyped.lean`), and the Glue face and η rules.
- **Equivalence** (`Equiv.lean`, `SigWk.lean`): `spec_to_minimal'`: `HasTy S ⊆ HasTy0 S` for `WfSig S`, given `ContractaTyped` for the prefixes of `S`. `minimal_to_spec`: `HasTy0 S ⊆ HasTy S` given that the spec derives M4 and M5.

## Spec issues

1. **Interval substitution needs congruence of `unglue`/`glueEl` in the equivalence (M4).** Functionality is needed for the face rule's case of substitution, and functionality for `unglue φ e g` needs `e ≡ e' ⇒ unglue φ e g ≡ unglue φ e' g`, which the spec does not provide. I believe `dsubst` is not admissible over the spec's other rules. With interval variables `i, l`, a context `g : Glue A [l ↦ (T, e₀)]` and `E(r) := split r e₀ r e₀`, the term `hcomp A [i ↦ _. unglue l E(i) g] (unglue l E(1) g)` is typable: its side condition `unglue l E(i) g ≡ unglue l E(1) g` under `i` is the face rule. At `i := j ∨ k` the side condition becomes, on the face `j = 1`, `unglue l E(1 ∨ k) g ≡ unglue l E(1) g` with syntactically different equivalences that are equal only judgmentally, and no rule other than `dsubst` relates them. (Not formally proven non-derivable.) M4 is valid in the intended model, and `EqTm.glue` already has this form.
2. **`transpGlue` is not syntactically stable under interval substitution (M5).** `(φ.forall0)[τ]` and `(φ[τ⁺]).forall0` are equivalent cofibrations but different terms, so a substituted rule instance is not a rule instance. Relating the two contracta needs the contractum to be typed (then congruence gives it), which needs injectivity (issue 3).
3. **Presupposition needs injectivity of type formers.** Computation rules are stated for a redex of any type `T`. To type the contractum at `T` one has to decompose the redex's typing, and conversions on the way require injectivity: for `piBeta`, `lam A t : Π A' B'` only gives `Π A B ≡ Π A' B'` for the `B` the body was checked against. Injectivity of `Π`, `Σ`, `PathP`, `(i : I) → A`, Glue and inductive types is a normalization-strength property, not provable by induction on derivations, so `eqR` is not admissible by elementary means for: `piBeta`, `fstBeta`, `sndBeta`, `pathBeta`; `glueBeta` (the base of the `glue` element's type versus the `unglue`'s; Glue types determine their base only off `φ`); `transpPi`, `transpSigma`, `transpPath`, `transpIPi`, `transpGlue` (the contracta need the components of the line to be constant on `φ`, which only follows from the line's constancy by injectivity); `elimCon`, `elimHcomp`, `transpCon`, `transpHcomp` (parameters of the scrutinee versus the eliminator). The model validates them through injectivity of codes (`piC_inj`, …). `conBnd` needs the signature's boundary typing, instantiated at the constructor's arguments; not done. The remaining `hcomp` rules (`hcompSigma`, `hcompPath`, `hcompGlue`, `hcompU`) need no injectivity but are long typing derivations (`comp`, `hfill`, equivalences); they are in `ContractaTyped` for now. `hcompPi` and `hcompIPi` are done.

A textbook spec would state the computation rules at the type determined by the typing premises of the redex (e.g. `piBeta` from `t : B` in `A :: Γ` and `a : A`, at `B[a]`); then presupposition for the β-rules is a corollary of substitution, and the spec's "any `T`" form is the step that needs injectivity.
