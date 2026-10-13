import Model.IPiFib

/-!
# Glue types: definitions

`glueC m A φ Tp ep`: the code `Glue A [φ ↦ (T, e)]` at stage `m`. `Tp` and `ep` are *partial*
Kripke values: their data at `(k, f)` with `φ·f` true are the code `T` and the equivalence `e`
restricted along `f` (and `∅` elsewhere). Where `φ·f` holds, the datum of the Glue code is the
datum of `T`, so the Glue type reduces to `T` on `φ` with no extra work.

Elements at a stage where `φ` fails are Kripke values `glueV k φ tp a` whose datum is the datum of
the `T`-element `tp` on `φ`, and records `(tp, a)` elsewhere; `unglue` reads off `a`.

The `hcomp` operation is the spec's `Tm.hcompGlue`. The `transp` operation is not defined yet
(see spec issue 6 in the README); `glueTr` is a placeholder.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

/-- A partial Kripke value on the face `φ`. -/
def partialKV (m : ℕ) (φ : Cof m) (F : (k : ℕ) → Hom k m → V) : V :=
  mkKV m fun k f => if (φ.restr f).holds then F k f else ∅

/-- The function of an equivalence, applied at stage `n`: `e.1 x`. -/
def eqFun (n : ℕ) (e x : V) : V := appV n (fstV n e) x

/-- `unglue` at stage `n`, for the face `φ` and the equivalence `e` (used only on `φ`). -/
def ungAt (n : ℕ) (φ : Cof n) (e g : V) : V := if φ.holds then eqFun n e g else π2 (π2 (here n g))

/-- A Glue element at stage `k` where `φ` fails: `glue [φ ↦ tp] a`. -/
def glueV (k : ℕ) (φ : Cof k) (tp a : V) : V :=
  mkKV k fun n g => if (φ.restr g).holds then here n (dat tp n g) else tagZ tGlue (pair (res g tp) (res g a))

/-- Elements of `Glue A [φ ↦ (T, e)]` at stage `k` (where `φ` fails). -/
def glueElSet (k : ℕ) (A : V) (φ : Cof k) (Tp ep : V) : V :=
  ZFSet.sep (fun v => ∃ tp a, v = glueV k φ tp a ∧ a ∈ El A (Hom.id k) ∧
      tp = partialKV k φ (fun n g => dat tp n g) ∧
      (∀ n (g : Hom n k), (φ.restr g).holds → dat tp n g ∈ El (dat Tp n g) (Hom.id n)) ∧
      (∀ n (g : Hom n k), (φ.restr g).holds → ∀ n' (h : Hom n' n), res h (dat tp n g) = dat tp n' (g.comp h)) ∧
      (∀ n (g : Hom n k), (φ.restr g).holds → eqFun n (dat ep n g) (dat tp n g) = res g a))
    (range fun x : ((y : Dom k) → ↥(insert ∅ (El (dat Tp y.1 y.2) (Hom.id y.1)))) × ↥(El A (Hom.id k)) =>
      glueV k φ (partialKV k φ fun n g => (x.1 ⟨n, g⟩).1) x.2.1)

/-- `hcomp (Glue A [φ ↦ (T, e)]) [ψ ↦ u] u0 =
  glue [φ ↦ hcomp T [ψ ↦ u] u0] (hcomp A [ψ ↦ unglue u, φ ↦ e.1 (hfill T [ψ ↦ u] u0)] (unglue u0))`
(spec: `Tm.hcompGlue`), at a stage `k` where `φ` fails. -/
def glueHcF (k : ℕ) (A : V) (φ : Cof k) (Tp ep : V) (ψ : Cof k) (u : Tube k) (u0 : V) : V :=
  let tp := partialKV k φ fun n g => hcompAt (dat Tp n g) (Hom.id n) (ψ.restr g) (u.restr g) (res g u0)
  let tube : Tube k := fun n h r =>
    if (ψ.restr h).holds then ungAt n (φ.restr h) (dat ep n h) (u n h r)
    else if (φ.restr h).holds then
      eqFun n (dat ep n h) (res (Hom.endpt n r) (hfillF (dat Tp n h) (Hom.id n) (ψ.restr h) (u.restr h) (res h u0)))
    else ∅
  glueV k φ tp (hcompAt A (Hom.id k) (Cof.or ψ φ) tube (π2 (π2 (here k u0))))

def glueHc (k : ℕ) (A : V) (φ : Cof k) (Tp ep : V) : V :=
  hcGraph k (fun n g => if (φ.restr g).holds then El (dat Tp n g) (Hom.id n)
      else glueElSet n (res g A) (φ.restr g) (res g Tp) (res g ep))
    (glueHcF k A φ Tp ep)

/-- Placeholder for the transport graph of Glue types (see the module doc). -/
def glueTr (_k : ℕ) (_A : V) (_φ : Cof _k) (_Tp _ep : V) : V := ∅

def glueDatum (k : ℕ) (A : V) (φ : Cof k) (Tp ep : V) : V :=
  quad (tagZ tGlue (pair A (pair (enc φ) (pair Tp ep)))) (glueElSet k A φ Tp ep) (glueTr k A φ Tp ep)
    (glueHc k A φ Tp ep)

/-- The code `Glue A [φ ↦ (T, e)]` at stage `m`. -/
def glueC (m : ℕ) (A : V) (φ : Cof m) (Tp ep : V) : V :=
  mkKV m fun k f => if (φ.restr f).holds then here k (dat Tp k f)
    else glueDatum k (res f A) (φ.restr f) (res f Tp) (res f ep)

end

end Model
