import Model.Glue
import KubusCore.Rules

/-!
# Interpretation of raw syntax

`interp cst uc t m ρ γ`: the value of the raw term `t` at stage `m`, in the interval environment
`ρ` and the term environment `γ`. `cst m k` is the value of the global constant `k` and
`uc m l` the code of the universe `U_l`; both are parameters here (constants are interpreted
from the signature in `Model.Sound`, universes in `Model.Univ`).

Every term former has a type-independent denotation; the only places that look at a face are
systems, `glueEl` and `unglue` (where the spec's rules force the value), and the Kan operations,
which pass the face to the code's operation.

`glueEl φ e t a` denotes `t` on `φ` only if `e.1 t = a` there, and `∅` otherwise. `∅` is not a
Kripke value, so it belongs to no type: this is what validates `glueElFace` and `glueBeta`
from the typing of the redex alone (spec issue 5).
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

def interp (cst : ℕ → ℕ → V) (uc : ℕ → ℕ → V) : Tm → (m : ℕ) → IEnv m → (ℕ → V) → V
  | .var x, _, _, γ => γ x
  | .const c, m, _, _ => cst m c
  | .univ l, m, _, _ => uc m l
  | .pi A B, m, ρ, γ =>
    piC m (interp cst uc A m ρ γ)
      (famV m (interp cst uc A m ρ γ) fun k f a => interp cst uc B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a))
  | .lam A t, m, ρ, γ =>
    lamV m (fun _ f => El (interp cst uc A m ρ γ) f)
      fun k f a => interp cst uc t k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a)
  | .app f a, m, ρ, γ => appV m (interp cst uc f m ρ γ) (interp cst uc a m ρ γ)
  | .sigma A B, m, ρ, γ =>
    sigmaC m (interp cst uc A m ρ γ)
      (famV m (interp cst uc A m ρ γ) fun k f a => interp cst uc B k (ρ.restr f) (TEnv.cons (TEnv.restr γ f) a))
  | .pair a b, m, ρ, γ => pairV m (interp cst uc a m ρ γ) (interp cst uc b m ρ γ)
  | .fst p, m, ρ, γ => fstV m (interp cst uc p m ρ γ)
  | .snd p, m, ρ, γ => sndV m (interp cst uc p m ρ γ)
  | .path A a b, m, ρ, γ =>
    pathC m (interp cst uc A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
      (interp cst uc a m ρ γ) (interp cst uc b m ρ γ)
  | .plam t, m, ρ, γ => pathOfLine m (interp cst uc t (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
  | .papp p r, m, ρ, γ => pappV m (interp cst uc p m ρ γ) (ival ρ r)
  | .ipi A, m, ρ, γ => ipiC m (interp cst uc A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m)))
  | .split φ t ψ u, m, ρ, γ =>
    if (ival ρ φ).holds then interp cst uc t m ρ γ else interp cst uc u m ρ γ
  | .abort, _, _, _ => ∅
  | .transp A φ a, m, ρ, γ =>
    transpAt (interp cst uc A (m + 1) ρ.ext (TEnv.restr γ (Hom.wk m))) (Hom.id (m + 1))
      (ival ρ φ).face (interp cst uc a m ρ γ)
  | .hcomp A φ u a, m, ρ, γ =>
    hcompAt (interp cst uc A m ρ γ) (Hom.id m) (ival ρ φ).face
      (fun n h r => interp cst uc u n ((ρ.restr h).cons r) (TEnv.restr γ h)) (interp cst uc a m ρ γ)
  | .glue A φ T e, m, ρ, γ =>
    glueC m (interp cst uc A m ρ γ) (ival ρ φ).face
      (partialKV m (ival ρ φ).face fun k f => interp cst uc T k (ρ.restr f) (TEnv.restr γ f))
      (partialKV m (ival ρ φ).face fun k f => interp cst uc e k (ρ.restr f) (TEnv.restr γ f))
  | .glueEl φ e t a, m, ρ, γ =>
    if (ival ρ φ).holds then
      (if eqFun m (interp cst uc e m ρ γ) (interp cst uc t m ρ γ) = interp cst uc a m ρ γ
        then interp cst uc t m ρ γ else ∅)
    else glueV m (ival ρ φ).face
      (partialKV m (ival ρ φ).face fun k f => interp cst uc t k (ρ.restr f) (TEnv.restr γ f))
      (interp cst uc a m ρ γ)
  | .unglue φ e g, m, ρ, γ =>
    ungAt m (ival ρ φ).face (interp cst uc e m ρ γ) (interp cst uc g m ρ γ)

end

end Model
