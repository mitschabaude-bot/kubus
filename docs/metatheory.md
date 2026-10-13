# Metatheory: a textbook specification

The spec (`KubusCore/Rules.lean`) has primitive rules for weakening (`wk`, `dwk`), single substitution (`subst`, `dsubst`), presupposition (`eqL`, `eqR`) and inversion of type formers (`piDom`, …, `glueFib`). `KubusCore/Meta/` defines the judgments without these rules and proves which of them are admissible.

## The minimal judgments

`Wf0`, `HasTy0`, `HasTele0`, `EqTele0`, `EqTm0` (`Meta/Minimal.lean`) are generated from `Rules.lean` by `Meta/scripts/gen_minimal.py`, which drops the 19 primitive rules and applies the changes below (it fails if a spec change touches an edited rule). The two anonymous substitutions in `elimHcomp` and `transpHcomp` are named (`consSub`, `skip1I`, definitionally equal), so that lemmas can refer to them.

Premises added (presupposition-style, derivable from the other premises by generation):

- M1 `ipi` (typing and congruence): the context is well-formed. Every other rule has a premise in the same context.
- M2 `HasTy0.glueEl`: the equivalence `e` is typed (it is a premise of the Glue type's formation).
- M3 `face`: the type is a type; `faceU` is the face rule at a universe.
- M6 `con`, `elim`: the parameters match the parameter telescope.

Rules generalized:

- M4 `EqTm0.glueEl`, `EqTm0.unglue`: congruence also in the equivalence (`e ≡ e'` under `φ`), as `EqTm.glue` already is. The spec's versions require the same `e` on both sides.
- M5 `EqTm0.transpGlue`: any `δ` equivalent to `∀i. φ` in the face lattice, instead of the syntactic `φ.forall0`.

## Results

All results assume `SigClosed S` (the declarations of the signature are closed; implied by `WfSig S`). Without it weakening fails, e.g. for a constant whose type has a free variable.

Proven, without `sorry`:

- **Renaming** (`Meta/Ren.lean`, `ren_ty`/`ren_eq`): renaming term variables arbitrarily and interval variables injectively. Corollaries (`Meta/Weaken.lean`): `HasTy.wk`, `EqTm.wk`, `HasTy.dwk`, `EqTm.dwk` are admissible.
- **Substitution and functionality** (`Meta/Substitution.lean`, `sub_ty`/`sub_eq`): simultaneous substitution of term and interval variables, and, for typing derivations, judgmentally equal substitutions (term variables judgmentally equal, interval variables equal in the free De Morgan algebra) give judgmentally equal results.
- **Cofibrations** (`Meta/Cof.lean`): `I.Entails` is entailment over assignments into the Kleene algebra `{0, a, 1}`; hence it is stable under all interval substitutions, and `∀i. φ` commutes with substitution up to equivalence.

The face rule is the delicate case of substitution: an instance `t ≡ t[d/i]` under `Φ ⊨ i = d` becomes `t[τ] ≡ t[τ[i:=d]]` under `Φ' ⊨ τ(i) = d`, which is not a face rule instance when `τ(i)` is compound. `Meta/SubFace.lean` proves it by splitting `Φ'` into its faces (`EqTm.local`), substituting each face's endpoints with the face rule, and then using functionality, since `τ(i)` and `d` become equal in the free De Morgan algebra.

## Spec issues

1. **Interval substitution needs congruence of `unglue`/`glueEl` in the equivalence (M4).** Functionality is needed for the face rule's case, and functionality for `unglue φ e g` needs `e ≡ e' ⇒ unglue φ e g ≡ unglue φ e' g`, which the spec does not provide. I believe `dsubst` is not admissible over the spec's other rules: with `Ψ = {i, l}`, `g : Glue A [l ↦ (T, e₀)]`, the term `hcomp A [i ↦ _. unglue l (split i e₀ i e₀) g] (unglue l (split 1 e₀ 1 e₀) g)` is typable (its side condition holds by the face rule at `i`), but at `i := j ∨ k` the side condition becomes `unglue l E₁ g ≡ unglue l E₂ g` with syntactically different `E₁ = split (1 ∨ k) …` and `E₂ = split 1 …`, which no rule other than `dsubst` relates. (Not formally proven non-derivable.) The generalized rules M4 are valid in the intended model.
2. **`transpGlue` is not syntactically stable under interval substitution (M5).** `(φ.forall0)[τ]` and `(φ[τ⁺]).forall0` differ syntactically (they are equivalent), so the substituted rule instance is not a rule instance. Relating the two contracta needs the contractum to be well-typed, which needs injectivity (see 3).
3. **Presupposition needs injectivity of type formers.** Computation rules are stated for a redex of any type `T`. To show the contractum has type `T` (`eqR`), one has to decompose the redex's typing, and conversions on the way require injectivity, e.g. for `piBeta`: `lam A t : Π A' B'` only gives `Π A B ≡ Π A' B'`. Injectivity of `Π`, `Σ`, `PathP`, `Glue` and inductive types is a normalization-strength result, not provable by induction on derivations. So `eqL`/`eqR` are not admissible by elementary means for the β-rules, `glueBeta`, the `transp` rules of `Π`/`Σ`/`PathP`/`(i : I) → A`/Glue (their contracta need the components of the line constant on `φ`, from the line's constancy) and the eliminator rules. The model validates them via injectivity of codes (`piC_inj`, …).

## Open

- Presupposition (`eqL`/`eqR`): see issue 3; the rules not needing injectivity are listed as they are done.
- Inversion (`piDom`, …): by generation lemmas (no injectivity needed, since inversion starts from a syntactic type former).
- Equivalence: `HasTy ⊆ HasTy0` given presupposition for the minimal judgments; `HasTy0 ⊆ HasTy` given M4 and M5 in the spec.
