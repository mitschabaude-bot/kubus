import KubusCore.Syntax

/-!
# Kubus Core: typing and equality

`HasTy S Ψ Φ Γ t A` and `EqTm S Ψ Φ Γ t u A`, over a signature `S` of global definitions, with `Ψ` interval variables, the cofibration
`Φ` (read as `Φ = 1`) restricting them, and the term context `Γ`. Universes are à la
Russell: `A` is a type of level `l` when `HasTy Ψ Φ Γ A (univ l)`.

Weakening, substitution, presupposition and inversion of type formers are included as
rules: they hold in the intended model (a level-indexed partial interpretation), and
having them as rules lets the kernel build derivations without proving metatheory first.

Computation rules are stated as: if the redex has some type `T`, it equals its contractum
at `T`. Rules that bind an interval variable move to `Ψ + 1`, `Φ.shift` and `Γ.dshift`.
-/

namespace KubusCore

open Tm

/-- The restriction `Φ ∧ φ`. -/
abbrev cof (Φ φ : I) : I := .and Φ φ

mutual

inductive Wf (S : Sig) : Nat → I → Ctx → Prop
  | nil {Ψ Φ} : Φ.Scoped Ψ → Wf S Ψ Φ []
  | cons {Ψ Φ Γ A l} : HasTy S Ψ Φ Γ A (univ l) → Wf S Ψ Φ (A :: Γ)

inductive HasTy (S : Sig) : Nat → I → Ctx → Tm → Tm → Prop
  /- structural -/
  | var {Ψ Φ Γ x A} : Wf S Ψ Φ Γ → Γ.lookup x = some A → HasTy S Ψ Φ Γ (var x) A
  | conv {Ψ Φ Γ t A B l} : HasTy S Ψ Φ Γ t A → EqTm S Ψ Φ Γ A B (univ l) → HasTy S Ψ Φ Γ t B
  | restrict {Ψ Φ Φ' Γ t A} : Φ'.Scoped Ψ → I.Entails Φ' Φ → HasTy S Ψ Φ Γ t A → HasTy S Ψ Φ' Γ t A
  | const {Ψ Φ Γ k t A} : Wf S Ψ Φ Γ → S[k]? = some (t, A) → HasTy S Ψ Φ Γ (const k) A
  | wk {Ψ Φ Γ t A B l} : HasTy S Ψ Φ Γ B (univ l) → HasTy S Ψ Φ Γ t A →
      HasTy S Ψ Φ (B :: Γ) t.shift A.shift
  | dwk {Ψ Φ Γ t A} : HasTy S Ψ Φ Γ t A → HasTy S (Ψ + 1) Φ.shift Γ.dshift t.dshift A.dshift
  | subst {Ψ Φ Γ A B t a} : HasTy S Ψ Φ (A :: Γ) t B → HasTy S Ψ Φ Γ a A →
      HasTy S Ψ Φ Γ (t.inst a) (B.inst a)
  | dsubst {Ψ Φ Γ t A r} : HasTy S (Ψ + 1) Φ.shift Γ.dshift t A → r.Scoped Ψ →
      HasTy S Ψ Φ Γ (t.dinst r) (A.dinst r)
  /- presupposition -/
  | eqL {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A → HasTy S Ψ Φ Γ t A
  | eqR {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A → HasTy S Ψ Φ Γ u A
  /- inversion of type formers -/
  | piDom {Ψ Φ Γ A B l} : HasTy S Ψ Φ Γ (pi A B) (univ l) → HasTy S Ψ Φ Γ A (univ l)
  | piCod {Ψ Φ Γ A B l} : HasTy S Ψ Φ Γ (pi A B) (univ l) → HasTy S Ψ Φ (A :: Γ) B (univ l)
  | sigmaDom {Ψ Φ Γ A B l} : HasTy S Ψ Φ Γ (sigma A B) (univ l) → HasTy S Ψ Φ Γ A (univ l)
  | sigmaCod {Ψ Φ Γ A B l} : HasTy S Ψ Φ Γ (sigma A B) (univ l) →
      HasTy S Ψ Φ (A :: Γ) B (univ l)
  | pathLine {Ψ Φ Γ A a b l} : HasTy S Ψ Φ Γ (path A a b) (univ l) →
      HasTy S (Ψ + 1) Φ.shift Γ.dshift A (univ l)
  | pathLeft {Ψ Φ Γ A a b l} : HasTy S Ψ Φ Γ (path A a b) (univ l) →
      HasTy S Ψ Φ Γ a (A.dinst .zero)
  | pathRight {Ψ Φ Γ A a b l} : HasTy S Ψ Φ Γ (path A a b) (univ l) →
      HasTy S Ψ Φ Γ b (A.dinst .one)
  | glueBase {Ψ Φ Γ A φ T e l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) → HasTy S Ψ Φ Γ A (univ l)
  | glueFib {Ψ Φ Γ A φ T e l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) →
      HasTy S Ψ (cof Φ φ) Γ T (univ l)
  | glueEquiv {Ψ Φ Γ A φ T e l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) →
      HasTy S Ψ (cof Φ φ) Γ e (equiv T A)
  /- universes -/
  | univ {Ψ Φ Γ l} : Wf S Ψ Φ Γ → HasTy S Ψ Φ Γ (univ l) (univ (l + 1))
  | cumul {Ψ Φ Γ A l} : HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ Φ Γ A (univ (l + 1))
  /- Π -/
  | pi {Ψ Φ Γ A B l} : HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ Φ (A :: Γ) B (univ l) →
      HasTy S Ψ Φ Γ (pi A B) (univ l)
  | lam {Ψ Φ Γ A B t l} : HasTy S Ψ Φ Γ (pi A B) (univ l) → HasTy S Ψ Φ (A :: Γ) t B →
      HasTy S Ψ Φ Γ (lam t) (pi A B)
  | app {Ψ Φ Γ A B f a} : HasTy S Ψ Φ Γ f (pi A B) → HasTy S Ψ Φ Γ a A →
      HasTy S Ψ Φ Γ (app f a) (B.inst a)
  /- Σ -/
  | sigma {Ψ Φ Γ A B l} : HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ Φ (A :: Γ) B (univ l) →
      HasTy S Ψ Φ Γ (sigma A B) (univ l)
  | pair {Ψ Φ Γ A B a b l} : HasTy S Ψ Φ Γ (sigma A B) (univ l) → HasTy S Ψ Φ Γ a A →
      HasTy S Ψ Φ Γ b (B.inst a) → HasTy S Ψ Φ Γ (pair a b) (sigma A B)
  | fst {Ψ Φ Γ A B p} : HasTy S Ψ Φ Γ p (sigma A B) → HasTy S Ψ Φ Γ (fst p) A
  | snd {Ψ Φ Γ A B p} : HasTy S Ψ Φ Γ p (sigma A B) → HasTy S Ψ Φ Γ (snd p) (B.inst (fst p))
  /- paths -/
  | path {Ψ Φ Γ A a b l} : HasTy S (Ψ + 1) Φ.shift Γ.dshift A (univ l) →
      HasTy S Ψ Φ Γ a (A.dinst .zero) → HasTy S Ψ Φ Γ b (A.dinst .one) →
      HasTy S Ψ Φ Γ (path A a b) (univ l)
  | plam {Ψ Φ Γ A a b t l} : HasTy S Ψ Φ Γ (path A a b) (univ l) →
      HasTy S (Ψ + 1) Φ.shift Γ.dshift t A →
      EqTm S Ψ Φ Γ (t.dinst .zero) a (A.dinst .zero) → EqTm S Ψ Φ Γ (t.dinst .one) b (A.dinst .one) →
      HasTy S Ψ Φ Γ (plam t) (path A a b)
  | papp {Ψ Φ Γ A a b p r} : HasTy S Ψ Φ Γ p (path A a b) → r.Scoped Ψ →
      HasTy S Ψ Φ Γ (papp p r) (A.dinst r)
  | ipi {Ψ Φ Γ A l} : HasTy S (Ψ + 1) Φ.shift Γ.dshift A (univ l) → HasTy S Ψ Φ Γ (ipi A) (univ l)
  | ilam {Ψ Φ Γ A t l} : HasTy S Ψ Φ Γ (ipi A) (univ l) → HasTy S (Ψ + 1) Φ.shift Γ.dshift t A →
      HasTy S Ψ Φ Γ (plam t) (ipi A)
  | iapp {Ψ Φ Γ A p r} : HasTy S Ψ Φ Γ p (ipi A) → r.Scoped Ψ → HasTy S Ψ Φ Γ (papp p r) (A.dinst r)
  | ipiLine {Ψ Φ Γ A l} : HasTy S Ψ Φ Γ (ipi A) (univ l) →
      HasTy S (Ψ + 1) Φ.shift Γ.dshift A (univ l)
  /- systems -/
  | split {Ψ Φ Γ A φ ψ t u l} : φ.Scoped Ψ → ψ.Scoped Ψ → I.Entails Φ (.or φ ψ) →
      HasTy S Ψ Φ Γ A (univ l) →
      HasTy S Ψ (cof Φ φ) Γ t A → HasTy S Ψ (cof Φ ψ) Γ u A → EqTm S Ψ (cof (cof Φ φ) ψ) Γ t u A →
      HasTy S Ψ Φ Γ (split φ t ψ u) A
  | abort {Ψ Φ Γ A l} : I.Entails Φ .zero → HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ Φ Γ abort A
  /- Kan operations -/
  | transp {Ψ Φ Γ A φ a l} : HasTy S (Ψ + 1) Φ.shift Γ.dshift A (univ l) → φ.Scoped Ψ →
      EqTm S (Ψ + 1) (cof Φ φ).shift Γ.dshift A (A.dinst .zero).dshift (univ l) →
      HasTy S Ψ Φ Γ a (A.dinst .zero) → HasTy S Ψ Φ Γ (transp A φ a) (A.dinst .one)
  | hcomp {Ψ Φ Γ A φ u a l} : HasTy S Ψ Φ Γ A (univ l) → φ.Scoped Ψ →
      HasTy S (Ψ + 1) (cof Φ φ).shift Γ.dshift u A.dshift → HasTy S Ψ Φ Γ a A →
      EqTm S Ψ (cof Φ φ) Γ (u.dinst .zero) a A → HasTy S Ψ Φ Γ (hcomp A φ u a) A
  /- Glue -/
  | glue {Ψ Φ Γ A φ T e l} : HasTy S Ψ Φ Γ A (univ l) → φ.Scoped Ψ →
      HasTy S Ψ (cof Φ φ) Γ T (univ l) → HasTy S Ψ (cof Φ φ) Γ e (equiv T A) →
      HasTy S Ψ Φ Γ (glue A φ T e) (univ l)
  | glueEl {Ψ Φ Γ A φ T e t a l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) →
      HasTy S Ψ (cof Φ φ) Γ t T → HasTy S Ψ Φ Γ a A → EqTm S Ψ (cof Φ φ) Γ (app (fst e) t) a A →
      HasTy S Ψ Φ Γ (glueEl φ t a) (glue A φ T e)
  | unglue {Ψ Φ Γ A φ T e g l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) →
      HasTy S Ψ Φ Γ g (glue A φ T e) → HasTy S Ψ Φ Γ (unglue φ g) A

inductive EqTm (S : Sig) : Nat → I → Ctx → Tm → Tm → Tm → Prop
  /- equivalence and structure -/
  | refl {Ψ Φ Γ t A} : HasTy S Ψ Φ Γ t A → EqTm S Ψ Φ Γ t t A
  | symm {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ u t A
  | trans {Ψ Φ Γ t u v A} : EqTm S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ u v A → EqTm S Ψ Φ Γ t v A
  | conv {Ψ Φ Γ t u A B l} : EqTm S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ A B (univ l) → EqTm S Ψ Φ Γ t u B
  | restrict {Ψ Φ Φ' Γ t u A} : Φ'.Scoped Ψ → I.Entails Φ' Φ → EqTm S Ψ Φ Γ t u A →
      EqTm S Ψ Φ' Γ t u A
  | cumul {Ψ Φ Γ A B l} : EqTm S Ψ Φ Γ A B (univ l) → EqTm S Ψ Φ Γ A B (univ (l + 1))
  | wk {Ψ Φ Γ t u A B l} : HasTy S Ψ Φ Γ B (univ l) → EqTm S Ψ Φ Γ t u A →
      EqTm S Ψ Φ (B :: Γ) t.shift u.shift A.shift
  | dwk {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A →
      EqTm S (Ψ + 1) Φ.shift Γ.dshift t.dshift u.dshift A.dshift
  | subst {Ψ Φ Γ A B t t' a a'} : EqTm S Ψ Φ (A :: Γ) t t' B → EqTm S Ψ Φ Γ a a' A →
      EqTm S Ψ Φ Γ (t.inst a) (t'.inst a') (B.inst a)
  | dsubst {Ψ Φ Γ t t' A r} : EqTm S (Ψ + 1) Φ.shift Γ.dshift t t' A → r.Scoped Ψ →
      EqTm S Ψ Φ Γ (t.dinst r) (t'.dinst r) (A.dinst r)
  | delta {Ψ Φ Γ k t A} : HasTy S Ψ Φ Γ (const k) A → S[k]? = some (t, A) →
      EqTm S Ψ Φ Γ (const k) t A
  /- cofibrations -/
  | absurd {Ψ Φ Γ t u A} : I.Entails Φ .zero → HasTy S Ψ Φ Γ t A → HasTy S Ψ Φ Γ u A →
      EqTm S Ψ Φ Γ t u A
  | local {Ψ Φ Γ φ ψ t u A} : φ.Scoped Ψ → ψ.Scoped Ψ → I.Entails Φ (.or φ ψ) →
      HasTy S Ψ Φ Γ t A → HasTy S Ψ Φ Γ u A →
      EqTm S Ψ (cof Φ φ) Γ t u A → EqTm S Ψ (cof Φ ψ) Γ t u A → EqTm S Ψ Φ Γ t u A
  | face {Ψ Φ Γ t A i d} : i < Ψ → I.Entails Φ (I.lit i d) → HasTy S Ψ Φ Γ t A →
      EqTm S Ψ Φ Γ t (t.dset i (I.ofDir d)) A
  /- congruence -/
  | pi {Ψ Φ Γ A A' B B' l} : EqTm S Ψ Φ Γ A A' (univ l) → EqTm S Ψ Φ (A :: Γ) B B' (univ l) →
      EqTm S Ψ Φ Γ (pi A B) (pi A' B') (univ l)
  | lam {Ψ Φ Γ A B t t' l} : HasTy S Ψ Φ Γ (pi A B) (univ l) → EqTm S Ψ Φ (A :: Γ) t t' B →
      EqTm S Ψ Φ Γ (lam t) (lam t') (pi A B)
  | app {Ψ Φ Γ A B f f' a a'} : EqTm S Ψ Φ Γ f f' (pi A B) → EqTm S Ψ Φ Γ a a' A →
      EqTm S Ψ Φ Γ (app f a) (app f' a') (B.inst a)
  | sigma {Ψ Φ Γ A A' B B' l} : EqTm S Ψ Φ Γ A A' (univ l) → EqTm S Ψ Φ (A :: Γ) B B' (univ l) →
      EqTm S Ψ Φ Γ (sigma A B) (sigma A' B') (univ l)
  | pair {Ψ Φ Γ A B a a' b b' l} : HasTy S Ψ Φ Γ (sigma A B) (univ l) → EqTm S Ψ Φ Γ a a' A →
      EqTm S Ψ Φ Γ b b' (B.inst a) → EqTm S Ψ Φ Γ (pair a b) (pair a' b') (sigma A B)
  | fst {Ψ Φ Γ A B p p'} : EqTm S Ψ Φ Γ p p' (sigma A B) → EqTm S Ψ Φ Γ (fst p) (fst p') A
  | snd {Ψ Φ Γ A B p p'} : EqTm S Ψ Φ Γ p p' (sigma A B) →
      EqTm S Ψ Φ Γ (snd p) (snd p') (B.inst (fst p))
  | path {Ψ Φ Γ A A' a a' b b' l} : EqTm S (Ψ + 1) Φ.shift Γ.dshift A A' (univ l) →
      EqTm S Ψ Φ Γ a a' (A.dinst .zero) → EqTm S Ψ Φ Γ b b' (A.dinst .one) →
      EqTm S Ψ Φ Γ (path A a b) (path A' a' b') (univ l)
  | plam {Ψ Φ Γ A a b t t' l} : HasTy S Ψ Φ Γ (path A a b) (univ l) →
      HasTy S Ψ Φ Γ (plam t) (path A a b) → HasTy S Ψ Φ Γ (plam t') (path A a b) →
      EqTm S (Ψ + 1) Φ.shift Γ.dshift t t' A → EqTm S Ψ Φ Γ (plam t) (plam t') (path A a b)
  | papp {Ψ Φ Γ A a b p p' r r'} : EqTm S Ψ Φ Γ p p' (path A a b) → r.Scoped Ψ → r'.Scoped Ψ →
      I.Eq r r' → EqTm S Ψ Φ Γ (papp p r) (papp p' r') (A.dinst r)
  | split {Ψ Φ Γ A φ ψ t t' u u'} : HasTy S Ψ Φ Γ (split φ t ψ u) A →
      HasTy S Ψ Φ Γ (split φ t' ψ u') A →
      EqTm S Ψ (cof Φ φ) Γ t t' A → EqTm S Ψ (cof Φ ψ) Γ u u' A →
      EqTm S Ψ Φ Γ (split φ t ψ u) (split φ t' ψ u') A
  | transp {Ψ Φ Γ A A' φ φ' a a' l} : HasTy S Ψ Φ Γ (transp A φ a) (A.dinst .one) →
      HasTy S Ψ Φ Γ (transp A' φ' a') (A.dinst .one) →
      EqTm S (Ψ + 1) Φ.shift Γ.dshift A A' (univ l) → I.Entails φ φ' → I.Entails φ' φ →
      EqTm S Ψ Φ Γ a a' (A.dinst .zero) → EqTm S Ψ Φ Γ (transp A φ a) (transp A' φ' a') (A.dinst .one)
  | hcomp {Ψ Φ Γ A A' φ φ' u u' a a' l} : HasTy S Ψ Φ Γ (hcomp A φ u a) A →
      HasTy S Ψ Φ Γ (hcomp A' φ' u' a') A → EqTm S Ψ Φ Γ A A' (univ l) →
      I.Entails φ φ' → I.Entails φ' φ →
      EqTm S (Ψ + 1) (cof Φ φ).shift Γ.dshift u u' A.dshift → EqTm S Ψ Φ Γ a a' A →
      EqTm S Ψ Φ Γ (hcomp A φ u a) (hcomp A' φ' u' a') A
  | glue {Ψ Φ Γ A A' φ φ' T T' e e' l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) →
      HasTy S Ψ Φ Γ (glue A' φ' T' e') (univ l) → EqTm S Ψ Φ Γ A A' (univ l) →
      I.Entails φ φ' → I.Entails φ' φ →
      EqTm S Ψ (cof Φ φ) Γ T T' (univ l) → EqTm S Ψ (cof Φ φ) Γ e e' (equiv T A) →
      EqTm S Ψ Φ Γ (glue A φ T e) (glue A' φ' T' e') (univ l)
  | glueEl {Ψ Φ Γ φ φ' t t' a a' A T e} : HasTy S Ψ Φ Γ (glueEl φ t a) (glue A φ T e) →
      HasTy S Ψ Φ Γ (glueEl φ' t' a') (glue A φ T e) →
      I.Entails φ φ' → I.Entails φ' φ →
      EqTm S Ψ (cof Φ φ) Γ t t' T → EqTm S Ψ Φ Γ a a' A →
      EqTm S Ψ Φ Γ (glueEl φ t a) (glueEl φ' t' a') (glue A φ T e)
  | unglue {Ψ Φ Γ A φ φ' T e g g'} : HasTy S Ψ Φ Γ (unglue φ g) A → HasTy S Ψ Φ Γ (unglue φ' g') A →
      I.Entails φ φ' → I.Entails φ' φ →
      EqTm S Ψ Φ Γ g g' (glue A φ T e) → EqTm S Ψ Φ Γ (unglue φ g) (unglue φ' g') A
  | ipi {Ψ Φ Γ A A' l} : EqTm S (Ψ + 1) Φ.shift Γ.dshift A A' (univ l) →
      EqTm S Ψ Φ Γ (ipi A) (ipi A') (univ l)
  | ilam {Ψ Φ Γ A t t' l} : HasTy S Ψ Φ Γ (ipi A) (univ l) →
      EqTm S (Ψ + 1) Φ.shift Γ.dshift t t' A → EqTm S Ψ Φ Γ (plam t) (plam t') (ipi A)
  | iapp {Ψ Φ Γ A p p' r r'} : EqTm S Ψ Φ Γ p p' (ipi A) → r.Scoped Ψ → r'.Scoped Ψ →
      I.Eq r r' → EqTm S Ψ Φ Γ (papp p r) (papp p' r') (A.dinst r)
  /- β and η -/
  | piBeta {Ψ Φ Γ t a T} : HasTy S Ψ Φ Γ (app (lam t) a) T → EqTm S Ψ Φ Γ (app (lam t) a) (t.inst a) T
  | piEta {Ψ Φ Γ A B f} : HasTy S Ψ Φ Γ f (pi A B) →
      EqTm S Ψ Φ Γ f (lam (app f.shift (var 0))) (pi A B)
  | fstBeta {Ψ Φ Γ a b T} : HasTy S Ψ Φ Γ (fst (pair a b)) T → EqTm S Ψ Φ Γ (fst (pair a b)) a T
  | sndBeta {Ψ Φ Γ a b T} : HasTy S Ψ Φ Γ (snd (pair a b)) T → EqTm S Ψ Φ Γ (snd (pair a b)) b T
  | sigmaEta {Ψ Φ Γ A B p} : HasTy S Ψ Φ Γ p (sigma A B) →
      EqTm S Ψ Φ Γ p (pair (fst p) (snd p)) (sigma A B)
  | pathBeta {Ψ Φ Γ t r T} : HasTy S Ψ Φ Γ (papp (plam t) r) T →
      EqTm S Ψ Φ Γ (papp (plam t) r) (t.dinst r) T
  | pathEta {Ψ Φ Γ A a b p} : HasTy S Ψ Φ Γ p (path A a b) →
      EqTm S Ψ Φ Γ p (plam (papp p.dshift (.var 0))) (path A a b)
  | ipiEta {Ψ Φ Γ A p} : HasTy S Ψ Φ Γ p (ipi A) →
      EqTm S Ψ Φ Γ p (plam (papp p.dshift (.var 0))) (ipi A)
  | pathZero {Ψ Φ Γ A a b p} : HasTy S Ψ Φ Γ p (path A a b) →
      EqTm S Ψ Φ Γ (papp p .zero) a (A.dinst .zero)
  | pathOne {Ψ Φ Γ A a b p} : HasTy S Ψ Φ Γ p (path A a b) →
      EqTm S Ψ Φ Γ (papp p .one) b (A.dinst .one)
  /- systems -/
  | splitL {Ψ Φ Γ φ ψ t u T} : I.Entails Φ φ → HasTy S Ψ Φ Γ (split φ t ψ u) T →
      EqTm S Ψ Φ Γ (split φ t ψ u) t T
  | splitR {Ψ Φ Γ φ ψ t u T} : I.Entails Φ ψ → HasTy S Ψ Φ Γ (split φ t ψ u) T →
      EqTm S Ψ Φ Γ (split φ t ψ u) u T
  /- Kan operations: boundaries -/
  | transpFace {Ψ Φ Γ A φ a T} : I.Entails Φ φ → HasTy S Ψ Φ Γ (transp A φ a) T →
      EqTm S Ψ Φ Γ (transp A φ a) a T
  | hcompFace {Ψ Φ Γ A φ u a T} : I.Entails Φ φ → HasTy S Ψ Φ Γ (hcomp A φ u a) T →
      EqTm S Ψ Φ Γ (hcomp A φ u a) (u.dinst .one) T
  /- Kan operations: computation (Coquand–Huber–Mörtberg) -/
  | transpU {Ψ Φ Γ l φ a T} : HasTy S Ψ Φ Γ (transp (univ l) φ a) T →
      EqTm S Ψ Φ Γ (transp (univ l) φ a) a T
  | transpPi {Ψ Φ Γ A B φ u0 T} : HasTy S Ψ Φ Γ (transp (pi A B) φ u0) T →
      EqTm S Ψ Φ Γ (transp (pi A B) φ u0) (transpPi A B φ u0) T
  | transpSigma {Ψ Φ Γ A B φ u0 T} : HasTy S Ψ Φ Γ (transp (sigma A B) φ u0) T →
      EqTm S Ψ Φ Γ (transp (sigma A B) φ u0) (transpSigma A B φ u0) T
  | transpPath {Ψ Φ Γ A a b φ p0 T} : HasTy S Ψ Φ Γ (transp (path A a b) φ p0) T →
      EqTm S Ψ Φ Γ (transp (path A a b) φ p0) (transpPath A a b φ p0) T
  | transpGlue {Ψ Φ Γ A φ T' e ψ u0 T} : HasTy S Ψ Φ Γ (transp (glue A φ T' e) ψ u0) T →
      EqTm S Ψ Φ Γ (transp (glue A φ T' e) ψ u0) (transpGlue A φ T' e ψ u0) T
  | transpIPi {Ψ Φ Γ A φ u0 T} : HasTy S Ψ Φ Γ (transp (ipi A) φ u0) T →
      EqTm S Ψ Φ Γ (transp (ipi A) φ u0) (transpIPi A φ u0) T
  | hcompIPi {Ψ Φ Γ A φ u u0 T} : HasTy S Ψ Φ Γ (hcomp (ipi A) φ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (ipi A) φ u u0) (hcompIPi A φ u u0) T
  | hcompPi {Ψ Φ Γ A B φ u u0 T} : HasTy S Ψ Φ Γ (hcomp (pi A B) φ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (pi A B) φ u u0) (hcompPi B φ u u0) T
  | hcompSigma {Ψ Φ Γ A B φ u u0 T} : HasTy S Ψ Φ Γ (hcomp (sigma A B) φ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (sigma A B) φ u u0) (hcompSigma A B φ u u0) T
  | hcompPath {Ψ Φ Γ A a b φ u p0 T} : HasTy S Ψ Φ Γ (hcomp (path A a b) φ u p0) T →
      EqTm S Ψ Φ Γ (hcomp (path A a b) φ u p0) (hcompPath A a b φ u p0) T
  | hcompGlue {Ψ Φ Γ A φ T' e ψ u u0 T} : HasTy S Ψ Φ Γ (hcomp (glue A φ T' e) ψ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (glue A φ T' e) ψ u u0) (hcompGlue A φ T' e ψ u u0) T
  /- Glue -/
  | glueFace {Ψ Φ Γ A φ T e G} : I.Entails Φ φ → HasTy S Ψ Φ Γ (glue A φ T e) G →
      EqTm S Ψ Φ Γ (glue A φ T e) T G
  | glueElFace {Ψ Φ Γ φ t a G} : I.Entails Φ φ → HasTy S Ψ Φ Γ (glueEl φ t a) G →
      EqTm S Ψ Φ Γ (glueEl φ t a) t G
  | unglueFace {Ψ Φ Γ A φ T e g} : I.Entails Φ φ → HasTy S Ψ Φ Γ g (glue A φ T e) →
      EqTm S Ψ Φ Γ (unglue φ g) (app (fst e) g) A
  | glueBeta {Ψ Φ Γ φ t a G} : HasTy S Ψ Φ Γ (unglue φ (glueEl φ t a)) G →
      EqTm S Ψ Φ Γ (unglue φ (glueEl φ t a)) a G
  | glueEta {Ψ Φ Γ A φ T e g} : HasTy S Ψ Φ Γ g (glue A φ T e) →
      EqTm S Ψ Φ Γ g (glueEl φ g (unglue φ g)) (glue A φ T e)

end

/-- A well-formed signature: definition `k` is a closed term of a closed type, checked
against the definitions before it. -/
def WfSig (S : Sig) : Prop :=
  ∀ k t A, S[k]? = some (t, A) →
    (∃ l, HasTy (S.take k) 0 .one [] A (.univ l)) ∧ HasTy (S.take k) 0 .one [] t A

/-- Consistency: in a well-formed signature there is no closed term of `(A : U₀) → A`. -/
def Consistent : Prop :=
  ∀ S t, WfSig S → ¬ HasTy S 0 .one [] t (.pi (.univ 0) (.var 0))

end KubusCore
