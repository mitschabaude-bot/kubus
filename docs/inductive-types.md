# Kubus Core, phase 2: inductive types and HITs

This fixes the design of inductive types and higher inductive types (HITs) in the kernel theory before it is formalized. It extends `docs/core-theory.md`; the formalization starts once the core fragment is verified end to end. It follows Coquand–Huber–Mörtberg, *On Higher Inductive Types in Cubical Type Theory* (CHM), restricted to a schema whose transport rules are simple enough to validate.

## Declarations

Data types are declared in the signature, next to definitions. A declaration has:
- **a level and parameters:** a level `l` and a parameter telescope `Δ`;
- **constructors** `c (x₁ : A₁) … (xₙ : Aₙ) (i₁ … iₘ : I) [ψ ↦ b]`, where
  - each argument type `Aₖ` lives in `Δ, x₁ … xₖ₋₁` and has level at most `l`;
  - `D` occurs in each `Aₖ` only strictly positively, as `(y : B) → D Δ` with `D` not in `B` and the parameters passed unchanged (no nesting, no indices);
  - a constructor with interval arguments has a *boundary* system `[ψ ↦ b]` over `i₁ … iₘ`, whose elements are built from constructor applications and the constructor's own point arguments ("simple boundaries").

Simple boundaries are what make transport componentwise: transporting `c (args) r` gives `c (transported args) r`, and its boundary is again the transported boundary. General boundaries (for example pushouts `inl (f c) = inr (g c)`) need CHM's correction terms and are left out.

A declaration is well-formed if its argument types check in order, the boundaries have type `D Δ` under their faces and agree on overlaps, and positivity holds. The check is decidable and done by the kernel.

## Terms

| term | typing |
|---|---|
| `data d ps` | `: U_l` when `ps : Δ` |
| `con d c ps args rs` | `: data d ps`; annotated with `d` and `ps` so that denotations are type-independent |
| `elim d ps (x. P) bs t` | `: P[t/x]` for `t : data d ps` |

There is no separate formal `hcomp` constructor: `hcomp (data d ps) φ u a` itself is the formal composition, a canonical form of a higher inductive type.

A branch `bₖ` for constructor `c` binds its point arguments, an induction hypothesis for each recursive argument (`(y : B) → P[x y]` for an infinitary one), and its interval arguments. It must agree with the eliminator on the boundary: under `ψ`, `bₖ ≡ elim … b`.

## Equations

- **Boundary:** under `ψ`, `con d c ps args rs ≡ b[args, rs]`.
- **β for constructors:** `elim … (con d c ps args rs) ≡ bₖ[args, ihs, rs]`, where each `ih` is `elim` applied to the recursive argument (under the binder `y` for infinitary arguments).
- **β for formal composition** (CHM):
  `elim … (hcomp (data d ps) φ u a) ≡ comp (i. P[hfill (data d ps) φ u a / x]) [φ ↦ i. elim … u] (elim … a)`.
- **Transport:**
  - without parameters, `transp (i. data d []) φ a ≡ a`;
  - with parameters varying in `i`, transport is componentwise on constructors: telescope transport of the arguments along `Δ(i)`, interval arguments unchanged;
  - transport of a formal composition is the formal composition of the transports: `transp (i. D) φ (hcomp D(0) ψ u a) ≡ hcomp D(1) ψ (j. transp (i. D) φ u(j)) (transp (i. D) φ a)`;
  - on neutral elements, transport is stuck.
- **Homogeneous composition:** `hcomp` in a data type never reduces, except by its face rule. This keeps evaluation stable under interval substitution: a componentwise rule would have to agree with the eliminator's composition rule after a later substitution, and in general it doesn't.

Strict positivity, the absence of nesting, and the eliminator form (no general recursion) keep the theory normalizing. Structural recursion in the surface language is compiled to `elim`.

## Model obligations

- **Fibrant inductive types:** initial algebras in cubical sets built as least fixed points of the constructor signature, closed under formal `hcomp` (CHM §3).
- **Transport:** for simple boundaries, componentwise transport preserves the boundary, so it is well-defined on path constructors.
- **Eliminator:** defined by well-founded recursion on the construction of the least fixed point.
