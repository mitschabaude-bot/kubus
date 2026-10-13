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
  | const {Ψ Φ Γ k t A} : Wf S Ψ Φ Γ → S[k]? = some (.defn t A) → HasTy S Ψ Φ Γ (const k) A
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
  | glueFib {Ψ Φ Γ A φ T e l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) →
      HasTy S Ψ (cof Φ φ) Γ T (univ l)
  | univ {Ψ Φ Γ l} : l + 1 ≤ maxLevel → Wf S Ψ Φ Γ → HasTy S Ψ Φ Γ (univ l) (univ (l + 1))
  | cumul {Ψ Φ Γ A l} : l + 1 ≤ maxLevel → HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ Φ Γ A (univ (l + 1))
  /- Π -/
  | pi {Ψ Φ Γ A B l} : HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ Φ (A :: Γ) B (univ l) →
      HasTy S Ψ Φ Γ (pi A B) (univ l)
  | lam {Ψ Φ Γ A B t l} : HasTy S Ψ Φ Γ (pi A B) (univ l) → HasTy S Ψ Φ (A :: Γ) t B →
      HasTy S Ψ Φ Γ (lam A t) (pi A B)
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
      HasTy S Ψ Φ Γ (glueEl φ e t a) (glue A φ T e)
  | unglue {Ψ Φ Γ A φ T e g l} : HasTy S Ψ Φ Γ (glue A φ T e) (univ l) →
      HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ (cof Φ φ) Γ e (equiv T A) →
      HasTy S Ψ Φ Γ g (glue A φ T e) → HasTy S Ψ Φ Γ (unglue φ e g) A

  /- inductive types -/
  | data {Ψ Φ Γ d D ps} : S[d]? = some (.data D) → D.level + 1 ≤ maxLevel →
      HasTele S Ψ Φ Γ ps D.params [] → HasTy S Ψ Φ Γ (data d ps) (univ D.level)
  | con {Ψ Φ Γ d D c C ps args rs} : S[d]? = some (.data D) → D.ctors[c]? = some C →
      ps = Tm.ofList ps.toList → HasTy S Ψ Φ Γ (data d ps) (univ D.level) →
      HasTele S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse →
      rs.length = C.dims → (∀ r ∈ rs, r.Scoped Ψ) →
      HasTy S Ψ Φ Γ (con d c ps args rs) (data d ps)
  | elim {Ψ Φ Γ d D ps P bs t m} : S[d]? = some (.data D) →
      ps = Tm.ofList ps.toList →
      HasTy S Ψ Φ Γ (data d ps) (univ D.level) → HasTy S Ψ Φ (data d ps :: Γ) P (univ m) →
      bs = Tm.ofList bs.toList → bs.toList.length = D.ctors.length →
      (∀ (c : Nat) (C : Ctor) (b : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
        HasTy S Ψ Φ Γ b (D.branchTy d c C ps P)) →
      (∀ (c : Nat) (C : Ctor) (b : Tm) (k : Nat) (ψ : I) (e : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b → C.bnd[k]? = some (ψ, e) →
        EqTm S (Ψ + C.dims) (cof (Φ.ren (· + C.dims)) ψ) (D.branchCtx d C ps P Γ)
          (DataDecl.branchApp C b) (D.bndElim C ps bs e) (DataDecl.branchBody d c C ps P)) →
      HasTy S Ψ Φ Γ t (data d ps) → HasTy S Ψ Φ Γ (elim d ps P bs t) (P.inst t)

/-- `as : Δ`: the list term `as` matches the telescope `Δ`, whose types are instantiated by
`prev` (the earlier elements and the outer instantiation, most recent first). -/
inductive HasTele (S : Sig) : Nat → I → Ctx → Tm → List Tm → List Tm → Prop
  | nil {Ψ Φ Γ prev} : Wf S Ψ Φ Γ → HasTele S Ψ Φ Γ .tnil [] prev
  | cons {Ψ Φ Γ a as A Δ prev} : HasTy S Ψ Φ Γ a (A.substList prev) →
      HasTele S Ψ Φ Γ as Δ (a :: prev) → HasTele S Ψ Φ Γ (.tcons a as) (A :: Δ) prev

/-- Equality of list terms in a telescope. -/
inductive EqTele (S : Sig) : Nat → I → Ctx → Tm → Tm → List Tm → List Tm → Prop
  | nil {Ψ Φ Γ prev} : Wf S Ψ Φ Γ → EqTele S Ψ Φ Γ .tnil .tnil [] prev
  | cons {Ψ Φ Γ a a' as as' A Δ prev} : EqTm S Ψ Φ Γ a a' (A.substList prev) →
      EqTele S Ψ Φ Γ as as' Δ (a :: prev) → EqTele S Ψ Φ Γ (.tcons a as) (.tcons a' as') (A :: Δ) prev
  /-- Injectivity of inductive types in their parameters. -/
  | dataInj {Ψ Φ Γ d D ps ps' l} : S[d]? = some (.data D) →
      HasTele S Ψ Φ Γ ps D.params [] → HasTele S Ψ Φ Γ ps' D.params [] →
      EqTm S Ψ Φ Γ (data d ps) (data d ps') (univ l) → EqTele S Ψ Φ Γ ps ps' D.params []

inductive EqTm (S : Sig) : Nat → I → Ctx → Tm → Tm → Tm → Prop
  /- equivalence and structure -/
  | refl {Ψ Φ Γ t A} : HasTy S Ψ Φ Γ t A → EqTm S Ψ Φ Γ t t A
  | symm {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ u t A
  | trans {Ψ Φ Γ t u v A} : EqTm S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ u v A → EqTm S Ψ Φ Γ t v A
  | conv {Ψ Φ Γ t u A B l} : EqTm S Ψ Φ Γ t u A → EqTm S Ψ Φ Γ A B (univ l) → EqTm S Ψ Φ Γ t u B
  | restrict {Ψ Φ Φ' Γ t u A} : Φ'.Scoped Ψ → I.Entails Φ' Φ → EqTm S Ψ Φ Γ t u A →
      EqTm S Ψ Φ' Γ t u A
  | cumul {Ψ Φ Γ A B l} : l + 1 ≤ maxLevel → EqTm S Ψ Φ Γ A B (univ l) →
      EqTm S Ψ Φ Γ A B (univ (l + 1))
  | wk {Ψ Φ Γ t u A B l} : HasTy S Ψ Φ Γ B (univ l) → EqTm S Ψ Φ Γ t u A →
      EqTm S Ψ Φ (B :: Γ) t.shift u.shift A.shift
  | dwk {Ψ Φ Γ t u A} : EqTm S Ψ Φ Γ t u A →
      EqTm S (Ψ + 1) Φ.shift Γ.dshift t.dshift u.dshift A.dshift
  | subst {Ψ Φ Γ A B t t' a a'} : EqTm S Ψ Φ (A :: Γ) t t' B → EqTm S Ψ Φ Γ a a' A →
      EqTm S Ψ Φ Γ (t.inst a) (t'.inst a') (B.inst a)
  | dsubst {Ψ Φ Γ t t' A r} : EqTm S (Ψ + 1) Φ.shift Γ.dshift t t' A → r.Scoped Ψ →
      EqTm S Ψ Φ Γ (t.dinst r) (t'.dinst r) (A.dinst r)
  | delta {Ψ Φ Γ k t A} : HasTy S Ψ Φ Γ (const k) A → S[k]? = some (.defn t A) →
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
      EqTm S Ψ Φ Γ (lam A t) (lam A t') (pi A B)
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
  | glueEl {Ψ Φ Γ φ φ' t t' a a' A T e e'} : HasTy S Ψ Φ Γ (glueEl φ e t a) (glue A φ T e) →
      HasTy S Ψ Φ Γ (glueEl φ' e' t' a') (glue A φ T e) →
      I.Entails φ φ' → I.Entails φ' φ → EqTm S Ψ (cof Φ φ) Γ e e' (equiv T A) →
      EqTm S Ψ (cof Φ φ) Γ t t' T → EqTm S Ψ Φ Γ a a' A →
      EqTm S Ψ Φ Γ (glueEl φ e t a) (glueEl φ' e' t' a') (glue A φ T e)
  | unglue {Ψ Φ Γ A φ φ' T e e' g g'} : HasTy S Ψ Φ Γ (unglue φ e g) A →
      HasTy S Ψ Φ Γ (unglue φ' e' g') A →
      I.Entails φ φ' → I.Entails φ' φ → EqTm S Ψ (cof Φ φ) Γ e e' (equiv T A) →
      EqTm S Ψ Φ Γ g g' (glue A φ T e) → EqTm S Ψ Φ Γ (unglue φ e g) (unglue φ' e' g') A
  | ipi {Ψ Φ Γ A A' l} : EqTm S (Ψ + 1) Φ.shift Γ.dshift A A' (univ l) →
      EqTm S Ψ Φ Γ (ipi A) (ipi A') (univ l)
  | ilam {Ψ Φ Γ A t t' l} : HasTy S Ψ Φ Γ (ipi A) (univ l) →
      EqTm S (Ψ + 1) Φ.shift Γ.dshift t t' A → EqTm S Ψ Φ Γ (plam t) (plam t') (ipi A)
  | iapp {Ψ Φ Γ A p p' r r'} : EqTm S Ψ Φ Γ p p' (ipi A) → r.Scoped Ψ → r'.Scoped Ψ →
      I.Eq r r' → EqTm S Ψ Φ Γ (papp p r) (papp p' r') (A.dinst r)
  /- injectivity of type formers (codomains and lines instantiated, so that the conclusion
  is in the context of the premise) -/
  | piInjDom {Ψ Φ Γ A A' B B' l} : EqTm S Ψ Φ Γ (pi A B) (pi A' B') (univ l) →
      EqTm S Ψ Φ Γ A A' (univ l)
  | piInjCod {Ψ Φ Γ A A' B B' a l} : EqTm S Ψ Φ Γ (pi A B) (pi A' B') (univ l) →
      HasTy S Ψ Φ Γ a A → EqTm S Ψ Φ Γ (B.inst a) (B'.inst a) (univ l)
  | sigmaInjDom {Ψ Φ Γ A A' B B' l} : EqTm S Ψ Φ Γ (sigma A B) (sigma A' B') (univ l) →
      EqTm S Ψ Φ Γ A A' (univ l)
  | sigmaInjCod {Ψ Φ Γ A A' B B' a l} : EqTm S Ψ Φ Γ (sigma A B) (sigma A' B') (univ l) →
      HasTy S Ψ Φ Γ a A → EqTm S Ψ Φ Γ (B.inst a) (B'.inst a) (univ l)
  | pathInjLine {Ψ Φ Γ A A' a a' b b' r l} : EqTm S Ψ Φ Γ (path A a b) (path A' a' b') (univ l) →
      r.Scoped Ψ → EqTm S Ψ Φ Γ (A.dinst r) (A'.dinst r) (univ l)
  | pathInjLeft {Ψ Φ Γ A A' a a' b b' l} : EqTm S Ψ Φ Γ (path A a b) (path A' a' b') (univ l) →
      EqTm S Ψ Φ Γ a a' (A.dinst .zero)
  | pathInjRight {Ψ Φ Γ A A' a a' b b' l} : EqTm S Ψ Φ Γ (path A a b) (path A' a' b') (univ l) →
      EqTm S Ψ Φ Γ b b' (A.dinst .one)
  | ipiInj {Ψ Φ Γ A A' r l} : EqTm S Ψ Φ Γ (ipi A) (ipi A') (univ l) →
      r.Scoped Ψ → EqTm S Ψ Φ Γ (A.dinst r) (A'.dinst r) (univ l)
  | dataInjAt {Ψ Φ Γ d} {D : DataDecl} {ps ps' : Tm} {l k : Nat} {p p' A : Tm} : S[d]? = some (.data D) →
      ps = Tm.ofList ps.toList → ps' = Tm.ofList ps'.toList →
      EqTm S Ψ Φ Γ (data d ps) (data d ps') (univ l) →
      ps.toList[k]? = some p → ps'.toList[k]? = some p' → D.params[k]? = some A →
      HasTy S Ψ Φ Γ p (A.substList (ps.toList.take k).reverse) →
      HasTy S Ψ Φ Γ p' (A.substList (ps.toList.take k).reverse) →
      EqTm S Ψ Φ Γ p p' (A.substList (ps.toList.take k).reverse)
  /- no-confusion of type formers: an equation between different ones holds only where the
  restriction is unsatisfiable -/
  | noConf {Ψ Φ Γ X Y l t u T} : X.headClash Y = true → EqTm S Ψ Φ Γ X Y (univ l) →
      HasTy S Ψ Φ Γ t T → HasTy S Ψ Φ Γ u T → EqTm S Ψ Φ Γ t u T
  /- β and η -/
  | piBeta {Ψ Φ Γ A t a T} : HasTy S Ψ Φ Γ (app (lam A t) a) T →
      EqTm S Ψ Φ Γ (app (lam A t) a) (t.inst a) T
  | piEta {Ψ Φ Γ A B f} : HasTy S Ψ Φ Γ f (pi A B) →
      EqTm S Ψ Φ Γ f (lam A (app f.shift (var 0))) (pi A B)
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
  | transpGlue {Ψ Φ Γ A φ T' e ψ u0 T l δ} : HasTy S Ψ Φ Γ (transp (glue A φ T' e) ψ u0) T →
      HasTy S (Ψ + 1) Φ.shift Γ.dshift A (univ l) →
      HasTy S (Ψ + 1) (cof Φ.shift φ) Γ.dshift e (equiv T' A) →
      δ.Scoped Ψ → I.Entails δ φ.forall0 → I.Entails φ.forall0 δ →
      EqTm S Ψ Φ Γ (transp (glue A φ T' e) ψ u0) (transpGlueWith δ A φ T' e ψ u0) T
  | transpIPi {Ψ Φ Γ A φ u0 T} : HasTy S Ψ Φ Γ (transp (ipi A) φ u0) T →
      EqTm S Ψ Φ Γ (transp (ipi A) φ u0) (transpIPi A φ u0) T
  | hcompIPi {Ψ Φ Γ A φ u u0 T} : HasTy S Ψ Φ Γ (hcomp (ipi A) φ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (ipi A) φ u u0) (hcompIPi A φ u u0) T
  | hcompPi {Ψ Φ Γ A B φ u u0 T} : HasTy S Ψ Φ Γ (hcomp (pi A B) φ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (pi A B) φ u u0) (hcompPi A B φ u u0) T
  | hcompSigma {Ψ Φ Γ A B φ u u0 T} : HasTy S Ψ Φ Γ (hcomp (sigma A B) φ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (sigma A B) φ u u0) (hcompSigma A B φ u u0) T
  | hcompPath {Ψ Φ Γ A a b φ u p0 T} : HasTy S Ψ Φ Γ (hcomp (path A a b) φ u p0) T →
      EqTm S Ψ Φ Γ (hcomp (path A a b) φ u p0) (hcompPath A a b φ u p0) T
  | hcompGlue {Ψ Φ Γ A φ T' e ψ u u0 T l} : HasTy S Ψ Φ Γ (hcomp (glue A φ T' e) ψ u u0) T →
      HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ (cof Φ φ) Γ e (equiv T' A) →
      EqTm S Ψ Φ Γ (hcomp (glue A φ T' e) ψ u u0) (hcompGlue A φ T' e ψ u u0) T
  | hcompU {Ψ Φ Γ φ u u0 T l} : HasTy S Ψ Φ Γ (hcomp (univ l) φ u u0) T →
      EqTm S Ψ Φ Γ (hcomp (univ l) φ u u0) (hcompU φ u u0) T
  /- Glue -/
  | glueFace {Ψ Φ Γ A φ T e G} : I.Entails Φ φ → HasTy S Ψ Φ Γ (glue A φ T e) G →
      EqTm S Ψ Φ Γ (glue A φ T e) T G
  | glueElFace {Ψ Φ Γ φ e t a G} : I.Entails Φ φ → HasTy S Ψ Φ Γ (glueEl φ e t a) G →
      EqTm S Ψ Φ Γ (glueEl φ e t a) t G
  | unglueFace {Ψ Φ Γ A φ T e g l} : I.Entails Φ φ → HasTy S Ψ Φ Γ g (glue A φ T e) →
      HasTy S Ψ Φ Γ A (univ l) → HasTy S Ψ Φ Γ e (equiv T A) →
      EqTm S Ψ Φ Γ (unglue φ e g) (app (fst e) g) A
  | glueBeta {Ψ Φ Γ φ e t a G} : HasTy S Ψ Φ Γ (unglue φ e (glueEl φ e t a)) G →
      HasTy S Ψ Φ Γ a G → EqTm S Ψ Φ Γ (unglue φ e (glueEl φ e t a)) a G
  | glueEta {Ψ Φ Γ A φ T e g} : HasTy S Ψ Φ Γ g (glue A φ T e) →
      EqTm S Ψ Φ Γ g (glueEl φ e g (unglue φ e g)) (glue A φ T e)
  /- inductive types: congruence -/
  | data {Ψ Φ Γ d D ps ps'} : S[d]? = some (.data D) →
      HasTy S Ψ Φ Γ (data d ps) (univ D.level) → HasTy S Ψ Φ Γ (data d ps') (univ D.level) →
      EqTele S Ψ Φ Γ ps ps' D.params [] → EqTm S Ψ Φ Γ (data d ps) (data d ps') (univ D.level)
  | con {Ψ Φ Γ d D c C ps ps' args args' rs rs'} : S[d]? = some (.data D) → D.ctors[c]? = some C →
      HasTy S Ψ Φ Γ (con d c ps args rs) (data d ps) →
      HasTy S Ψ Φ Γ (con d c ps' args' rs') (data d ps) →
      EqTele S Ψ Φ Γ ps ps' D.params [] →
      EqTele S Ψ Φ Γ args args' (C.argTys d D.params.length) ps.toList.reverse →
      rs.length = rs'.length → (∀ (k : Nat) (r r' : I), rs[k]? = some r → rs'[k]? = some r' → I.Eq r r') →
      EqTm S Ψ Φ Γ (con d c ps args rs) (con d c ps' args' rs') (data d ps)
  | elim {Ψ Φ Γ d D ps ps' P P' bs bs' t t' m} : S[d]? = some (.data D) →
      HasTy S Ψ Φ Γ (elim d ps P bs t) (P.inst t) → HasTy S Ψ Φ Γ (elim d ps' P' bs' t') (P.inst t) →
      EqTele S Ψ Φ Γ ps ps' D.params [] → EqTm S Ψ Φ (data d ps :: Γ) P P' (univ m) →
      bs = Tm.ofList bs.toList → bs' = Tm.ofList bs'.toList →
      bs.toList.length = bs'.toList.length →
      (∀ (c : Nat) (C : Ctor) (b b' : Tm), D.ctors[c]? = some C → bs.toList[c]? = some b →
        bs'.toList[c]? = some b' →
        EqTm S Ψ Φ Γ b b' (D.branchTy d c C ps P)) →
      EqTm S Ψ Φ Γ t t' (data d ps) →
      EqTm S Ψ Φ Γ (elim d ps P bs t) (elim d ps' P' bs' t') (P.inst t)
  /- inductive types: boundaries of path constructors -/
  | conBnd {Ψ Φ Γ d D c C ps args rs} {k : Nat} {ψ b T} : S[d]? = some (.data D) → D.ctors[c]? = some C →
      C.bnd[k]? = some (ψ, b) → I.Entails Φ (Ctor.cofAt ψ rs) →
      ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
      HasTy S Ψ Φ Γ (con d c ps args rs) T →
      EqTm S Ψ Φ Γ (con d c ps args rs) (Ctor.bndAt b ps.toList args.toList rs) T
  /- inductive types: elimination -/
  | elimCon {Ψ Φ Γ d D c C ps P bs b qs args rs T} : S[d]? = some (.data D) →
      D.ctors[c]? = some C → bs.toList[c]? = some b →
      ps = Tm.ofList ps.toList → args = Tm.ofList args.toList → bs = Tm.ofList bs.toList →
      HasTele S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse →
      HasTy S Ψ Φ Γ (elim d ps P bs (con d c qs args rs)) T →
      EqTm S Ψ Φ Γ (elim d ps P bs (con d c qs args rs))
        (Tm.papps (Tm.apps b (args.toList ++
          C.recPos.map fun k => elim d ps P bs (args.toList.getD k .abort))) rs) T
  | elimHcomp {Ψ Φ Γ d D ps P bs qs φ u a T} : S[d]? = some (.data D) → D.isHIT = true →
      HasTy S Ψ Φ Γ (hcomp (data d ps) φ u a) (data d ps) →
      HasTy S Ψ Φ Γ (elim d ps P bs (hcomp (data d qs) φ u a)) T →
      EqTm S Ψ Φ Γ (elim d ps P bs (hcomp (data d qs) φ u a))
        (comp (P.subst (fun | 0 => hfill (data d ps) φ u a | j + 1 => var j) (fun i => .var (i + 1))) φ
          (elim d ps.dshift P.dshift bs.dshift u) (elim d ps P bs a)) T
  /- inductive types without path constructors: composition is componentwise (CCHM) -/
  | hcompCon {Ψ Φ Γ d D c C ps φ u qs uargs args T} : S[d]? = some (.data D) → D.isHIT = false →
      D.ctors[c]? = some C → ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
      uargs = Tm.ofList uargs.toList →
      HasTele S Ψ Φ Γ args (C.argTys d D.params.length) ps.toList.reverse →
      HasTele S (Ψ + 1) (cof Φ φ).shift Γ.dshift uargs (C.argTys d D.params.length) ps.dshift.toList.reverse →
      EqTm S (Ψ + 1) (cof Φ φ).shift Γ.dshift u (con d c ps.dshift uargs []) (data d ps.dshift) →
      HasTy S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args [])) T →
      EqTm S Ψ Φ Γ (hcomp (data d ps) φ u (con d c qs args []))
        (con d c ps (Tm.ofList (Tm.hcompTele C (C.argTy d D.params.length) (data d ps) ps.dshift.toList φ 0 []
          uargs.toList args.toList)) []) T
  /- inductive types: transport (`hcomp` in a higher inductive type is a canonical form) -/
  | transpData0 {Ψ Φ Γ d D ps φ a T} : S[d]? = some (.data D) → D.params = [] →
      HasTy S Ψ Φ Γ (transp (data d ps) φ a) T → EqTm S Ψ Φ Γ (transp (data d ps) φ a) a T
  | transpCon {Ψ Φ Γ d D c C ps φ qs args rs T} : S[d]? = some (.data D) → D.params ≠ [] →
      D.ctors[c]? = some C → ps = Tm.ofList ps.toList → args = Tm.ofList args.toList →
      HasTele S Ψ Φ Γ args (C.argTys d D.params.length) (ps.dinst .zero).toList.reverse →
      HasTy S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs)) T →
      EqTm S Ψ Φ Γ (transp (data d ps) φ (con d c qs args rs))
        (con d c (ps.dinst .one)
          (Tm.ofList (Tm.transpTele (C.argTy d D.params.length) ps.toList φ 0 [] args.toList)) rs) T
  | transpHcomp {Ψ Φ Γ d D ps φ qs ψ u a T} : S[d]? = some (.data D) → D.params ≠ [] → D.isHIT = true →
      HasTy S Ψ Φ Γ (hcomp (data d (ps.dinst .zero)) ψ u a) (data d (ps.dinst .zero)) →
      HasTy S Ψ Φ Γ (transp (data d ps) φ (hcomp (data d qs) ψ u a)) T →
      EqTm S Ψ Φ Γ (transp (data d ps) φ (hcomp (data d qs) ψ u a))
        (hcomp (data d (ps.dinst .one)) ψ
          (transp ((data d ps).dsubst fun | 0 => .var 0 | n + 1 => .var (n + 2)) φ.shift u)
          (transp (data d ps) φ a)) T

end

namespace Ctor

mutual
/-- The point arguments of the nested constructors of a boundary element of constructor `C`
have, judgmentally, the argument types of those constructors (instantiated as in the `con`
rule), not merely types the arguments also belong to: transport of a constructor is computed
from its argument types (`transpCon`), so the boundary and the constructor must agree on them.
The boundary lives in `Γ` (parameters and all arguments of `C`); the equations are stated in
`Γp` (parameters and point arguments of `C`), after dropping the recursive arguments, which
neither side may mention. -/
def bndTyped (S : Sig) (m : Nat) (ψ : I) (Γ : Ctx) (C : Ctor) (Γp : Ctx) (lvl : Nat)
    (ctors : List Ctor) (d np : Nat) : Tm → Prop
  | .con _ c' ps as _ =>
    match ctors[c']? with
    | some C' => bndTypedArgs S m ψ Γ C Γp lvl ctors d np C' ps 0 [] as
    | none => True
  | _ => True
/-- The same for the arguments of a nested constructor `C'`, from position `k` on, with the
earlier arguments `prev` (most recent first). -/
def bndTypedArgs (S : Sig) (m : Nat) (ψ : I) (Γ : Ctx) (C : Ctor) (Γp : Ctx) (lvl : Nat)
    (ctors : List Ctor) (d np : Nat) (C' : Ctor) (ps : Tm) (k : Nat) (prev : List Tm) : Tm → Prop
  | .tcons a as =>
    (∀ (j : Nat) (T : Tm), a = .var j → C'.isRec k = false → Γ.lookup j = some T →
      C.mentionsRec C.args.length T = false ∧
      C.mentionsRec C.args.length ((C'.argTy d np k).substList (prev ++ ps.toList.reverse)) = false ∧
      EqTm S m ψ Γp (T.ren (C.pointRen C.args.length) id)
        (((C'.argTy d np k).substList (prev ++ ps.toList.reverse)).ren (C.pointRen C.args.length) id)
        (.univ lvl)) ∧
    (C'.isRec k = true → bndTyped S m ψ Γ C Γp lvl ctors d np a) ∧
    bndTypedArgs S m ψ Γ C Γp lvl ctors d np C' ps (k + 1) (a :: prev) as
  | _ => True
end

end Ctor

namespace DataDecl

/-- The context of the parameters before parameter `j`. -/
def paramCtx (D : DataDecl) (j : Nat) : Ctx := (D.params.take j).reverse

/-- The context of the parameters and the arguments of `C` before argument `k`. -/
def argCtx (D : DataDecl) (d : Nat) (C : Ctor) (k : Nat) : Ctx :=
  (List.range k).reverse.map (C.argTy d D.params.length) ++ D.paramCtx D.params.length

/-- The context of the parameters and the point arguments of `C` before argument `n`: `argCtx`
without the recursive arguments (point argument types do not mention them, `Ctor.noRecDeps`). -/
def pointCtx (D : DataDecl) (d : Nat) (C : Ctor) (n : Nat) : Ctx :=
  (((List.range n).filter fun k => !C.isRec k).map fun k =>
    (C.argTy d D.params.length k).ren (C.pointRen k) id).reverse ++ D.paramCtx D.params.length

/-- The declaration with only the constructors before `c`, and an extra constructor without
arguments or boundary (at index `c`, which no boundary of constructor `c` can refer to) so that
the type is inhabited: judgments in a context with an empty type would hold vacuously in the
model. The extra constructor has an interval argument exactly when `D` is a higher inductive
type, so that the truncation is one exactly when `D` is (`isHIT`): only higher inductive types
have formal compositions, which the model uses as generic elements. -/
def truncate (D : DataDecl) (c : Nat) : DataDecl :=
  { D with ctors := D.ctors.take c ++ [{ args := [], dims := if D.isHIT then 1 else 0, bnd := [] }] }

/-- A well-formed declaration of the inductive type `d = S.length`, checked against the
signature `S` before it: the parameters in `S` itself, the point arguments in `S` extended by
the declaration without constructors, and the boundary of constructor `c` and its agreement on
overlaps in `S` extended by the declaration truncated to the constructors before `c`, so that neither `c`'s own boundary rule nor later constructors are
available (otherwise `conBnd` would make the boundary check vacuous). Parameters and point
arguments do not mention `d` (so `d` occurs only as the type of recursive arguments: strictly
positive, not nested), point arguments do not mention earlier recursive arguments and live in
the declared universe (also in `S` itself, over the parameters and earlier point arguments, so
that their types are typed wherever the parameters are: `transpCon` transports along them), and boundaries are simple, well-typed (with the argument types of their
nested constructors, `Ctor.bndTyped`) and agree on overlaps. -/
def Wf (D : DataDecl) (S : Sig) (d : Nat) : Prop :=
  let np := D.params.length
  D.level + 1 ≤ maxLevel ∧
  (∀ (j : Nat) (A : Tm), D.params[j]? = some A → A.closedB j 0 = true ∧ A.mentionsData d = false ∧
    (HasTy S 0 .one (D.paramCtx j) A (.univ D.level) ∨ ∃ k ≤ D.level, A = .univ k)) ∧
  ∀ (c : Nat) (C : Ctor), D.ctors[c]? = some C →
    let Sc := S ++ [.data (D.truncate c)]
    (∀ (k : Nat) (A : Tm), C.args[k]? = some (.point A) → A.closedB (np + k) 0 = true ∧
      A.mentionsData d = false ∧ C.noRecDeps k A = true ∧
      HasTy (S ++ [.data (D.truncate 0)]) 0 .one (D.argCtx d C k) A (.univ D.level) ∧
      HasTy S 0 .one (D.pointCtx d C k) (A.ren (C.pointRen k) id) (.univ D.level)) ∧
    (∀ (k : Nat) (ψ : I) (b : Tm), C.bnd[k]? = some (ψ, b) → ψ.Scoped C.dims ∧
      b.closedB (np + C.args.length) C.dims = true ∧
      Ctor.simpleB D.ctors d np c C.args.length C b = true ∧
      HasTy Sc C.dims ψ (D.argCtx d C C.args.length) b
        (.data d (Ctor.paramVars np C.args.length)) ∧
      Ctor.bndTyped S C.dims ψ (D.argCtx d C C.args.length) C (D.pointCtx d C C.args.length)
        D.level D.ctors d np b) ∧
    (∀ (k k' : Nat) (ψ ψ' : I) (b b' : Tm), C.bnd[k]? = some (ψ, b) → C.bnd[k']? = some (ψ', b') →
      EqTm Sc C.dims (.and ψ ψ') (D.argCtx d C C.args.length) b b'
        (.data d (Ctor.paramVars np C.args.length)))

end DataDecl

/-- A well-formed signature: definition `k` is a closed term of a closed type, checked
against the entries before it; a data declaration is well-formed against the entries before
it (`DataDecl.Wf`). -/
def WfSig (S : Sig) : Prop :=
  (∀ (k : Nat) (t A : Tm), S[k]? = some (.defn t A) →
    t.closedB 0 0 ∧ A.closedB 0 0 ∧
    (∃ l, HasTy (S.take k) 0 .one [] A (.univ l)) ∧ HasTy (S.take k) 0 .one [] t A) ∧
  (∀ (k : Nat) (D : DataDecl), S[k]? = some (.data D) → D.Wf (S.take k) k)

/-- Consistency: in a well-formed signature there is no closed term of `(A : U₀) → A`. -/
def Consistent : Prop :=
  ∀ S t, WfSig S → ¬ HasTy S 0 .one [] t (.pi (.univ 0) (.var 0))

end KubusCore
