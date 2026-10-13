import Model.Glue
import KubusCore.Rules

/-!
# Interpretation of raw syntax

`interp cst uc good t m ρ γ`: the value of the raw term `t` at stage `m`, in the interval environment
`ρ` and the term environment `γ`. `cst m k` is the value of the global constant `k` and
`uc m l` the code of the universe `U_l`; both are parameters here (constants are interpreted
from the signature in `Model.Sound`, universes in `Model.Univ`).

Every term former has a type-independent denotation; the only places that look at a face are
systems, `glueEl` and `unglue` (where the spec's rules force the value), and the Kan operations,
which pass the face to the code's operation.

The interpretation is *defensive*: where a computation rule of the spec only knows that the
redex has a value in its type, the interpretation of the redex checks the side conditions that
the rule needs and otherwise returns `∅`. `∅` is not a Kripke value, so it belongs to no type;
hence a redex with a value in a type satisfies the checks. Concretely:

* `glueEl φ e t a` denotes `t` on `φ` only if `e.1 t = a` there (spec issue 5);
* `split φ t ψ u` requires one of the faces to hold and `t = u` where both hold (for `splitR`
  and the congruence rule, whose premises do not say that the faces cover);
* `pair a b` requires Kripke values (for `fstBeta`/`sndBeta`);
* `app f a` requires the argument to be natural (for the substitution in `piBeta`);
* `plam t` requires the body to be natural (for `pathBeta`);
* `transp`/`hcomp` require the type to be a good code (`good`, instantiated by the well-formed
  codes and universes), the line to be constant on the face, and the tube and base to be typed
  (for `transpFace`, `hcompFace` and the Kan computation rules).
-/

set_option autoImplicit false

namespace Model

open KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-- Restrict a term environment. -/
def TEnv.restr (γ : ℕ → V) (f : Hom k m) : ℕ → V := fun x => res f (γ x)

/-- Extend a term environment (de Bruijn index 0). -/
def TEnv.cons (γ : ℕ → V) (a : V) : ℕ → V := fun
  | 0 => a
  | x + 1 => γ x

/-- A family of codes over the code `A` at stage `m`, from its values. -/
def famV (m : ℕ) (A : V) (F : (k : ℕ) → Hom k m → V → V) : V := lamV m (fun _ f => El A f) F

def interp (cst : ℕ → ℕ → V) (uc : ℕ → ℕ → V) (good : (m : ℕ) → V → Prop) :
    Tm → (m : ℕ) → IEnv m → (ℕ → V) → V
  | .var x, _, _, γ => γ x
  | .const c, m, _, _ => cst m c
  | .univ l, m, _, _ => uc m l
  | .pi A B, m, ρ, γ =>
    piC m (interp cst uc good A m ρ γ)
      (famV m (interp cst uc good A m ρ γ) fun k f a => interp cst uc good B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a))
  | .lam A t, m, ρ, γ =>
    lamV m (fun _ f => El (interp cst uc good A m ρ γ) f)
      fun k f a => interp cst uc good t k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)
  | .app f a, m, ρ, γ =>
    if ∀ k (g : Hom k m), interp cst uc good a k (ρ.restr g) (TEnv.restr γ g) = res g (interp cst uc good a m ρ γ)
    then appV m (interp cst uc good f m ρ γ) (interp cst uc good a m ρ γ) else ∅
  | .sigma A B, m, ρ, γ =>
    sigmaC m (interp cst uc good A m ρ γ)
      (famV m (interp cst uc good A m ρ γ) fun k f a => interp cst uc good B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a))
  | .pair a b, m, ρ, γ =>
    if IsKV m (interp cst uc good a m ρ γ) ∧ IsKV m (interp cst uc good b m ρ γ)
    then pairV m (interp cst uc good a m ρ γ) (interp cst uc good b m ρ γ) else ∅
  | .fst p, m, ρ, γ => fstV m (interp cst uc good p m ρ γ)
  | .snd p, m, ρ, γ => sndV m (interp cst uc good p m ρ γ)
  | .path A a b, m, ρ, γ =>
    pathC m (interp cst uc good A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
      (interp cst uc good a m ρ γ) (interp cst uc good b m ρ γ)
  | .plam t, m, ρ, γ =>
    if ∀ k (g : Hom k (m + 1)), interp cst uc good t k (ρ.ext.restr g) (TEnv.restr (TEnv.restr γ (Hom.wk m)) g) =
        res g (interp cst uc good t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
    then pathOfLine m (interp cst uc good t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) else ∅
  | .papp p r, m, ρ, γ => pappV m (interp cst uc good p m ρ γ) (ival ρ r)
  | .ipi A, m, ρ, γ => ipiC m (interp cst uc good A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
  | .split φ t ψ u, m, ρ, γ =>
    if (ival ρ φ).holds then
      (if (ival ρ ψ).holds → interp cst uc good t m ρ γ = interp cst uc good u m ρ γ
        then interp cst uc good t m ρ γ else ∅)
    else if (ival ρ ψ).holds then interp cst uc good u m ρ γ else ∅
  | .abort, _, _, _ => ∅
  | .transp A φ a, m, ρ, γ =>
    if good (m + 1) (interp cst uc good A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) ∧
        ConstOn (interp cst uc good A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (Hom.id (m + 1)) (ival ρ φ).face ∧
        interp cst uc good a m ρ γ ∈
          El (interp cst uc good A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) ((Hom.id (m + 1)).comp (Hom.endpt m (DM.zero m)))
    then transpAt (interp cst uc good A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (Hom.id (m + 1))
      (ival ρ φ).face (interp cst uc good a m ρ γ) else ∅
  | .hcomp A φ u a, m, ρ, γ =>
    if good m (interp cst uc good A m ρ γ) ∧
        TubeOK (interp cst uc good A m ρ γ) (Hom.id m) (ival ρ φ).face
          (fun n h r => interp cst uc good u n ((ρ.restr h).cons r) (TEnv.restr γ h)) (interp cst uc good a m ρ γ) ∧
        interp cst uc good a m ρ γ ∈ El (interp cst uc good A m ρ γ) (Hom.id m)
    then hcompAt (interp cst uc good A m ρ γ) (Hom.id m) (ival ρ φ).face
      (fun n h r => interp cst uc good u n ((ρ.restr h).cons r) (TEnv.restr γ h)) (interp cst uc good a m ρ γ)
    else ∅
  | .glue A φ T e, m, ρ, γ =>
    glueC m (interp cst uc good A m ρ γ) (ival ρ φ).face
      (partialKV m (ival ρ φ).face fun k f => interp cst uc good T k (ρ.restr f) (TEnv.restr γ f))
      (partialKV m (ival ρ φ).face fun k f => interp cst uc good e k (ρ.restr f) (TEnv.restr γ f))
  | .glueEl φ e t a, m, ρ, γ =>
    if (ival ρ φ).holds then
      (if eqFun m (interp cst uc good e m ρ γ) (interp cst uc good t m ρ γ) = interp cst uc good a m ρ γ
        then interp cst uc good t m ρ γ else ∅)
    else glueV m (ival ρ φ).face
      (partialKV m (ival ρ φ).face fun k f => interp cst uc good t k (ρ.restr f) (TEnv.restr γ f))
      (interp cst uc good a m ρ γ)
  | .unglue φ e g, m, ρ, γ =>
    ungAt m (ival ρ φ).face (interp cst uc good e m ρ γ) (interp cst uc good g m ρ γ)

end

end Model
