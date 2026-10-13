import Model.IPiFib
import Model.CompFill
import Model.CofForall

/-!
# Glue types: definitions

`glueC m A φ Tp ep`: the code `Glue A [φ ↦ (T, e)]` at stage `m`. `Tp` and `ep` are *partial*
Kripke values: their data at `(k, f)` with `φ·f` true are the code `T` and the equivalence `e`
restricted along `f` (and `∅` elsewhere). Where `φ·f` holds, the datum of the Glue code is the
datum of `T`, so the Glue type reduces to `T` on `φ` with no extra work.

Elements at a stage where `φ` fails are Kripke values `glueV k φ tp a` whose datum is the datum of
the `T`-element `tp` on `φ`, and records `(tp, a)` elsewhere; `unglue` reads off `a`.

The `hcomp` operation is the spec's `Tm.hcompGlue`, the `transp` operation the spec's
`Tm.transpGlue` (`gtResult`).
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
def ungAt (n : ℕ) (φ : Cof n) (e g : V) : V :=
  if φ.holds then (if IsKV n g then eqFun n e g else ∅) else π2 (π2 (here n g))

/-- A Glue element at stage `k` where `φ` fails: `glue [φ ↦ tp] a`. -/
def glueV (k : ℕ) (φ : Cof k) (tp a : V) : V :=
  mkKV k fun n g => if (φ.restr g).holds then here n (dat tp n g) else tagZ tGlue (pair (res g tp) (res g a))

/-- A family of codes over the code `A` at stage `m`, from its values. -/
def famV (m : ℕ) (A : V) (F : (k : ℕ) → Hom k m → V → V) : V := lamV m (fun _ f => El A f) F

/-- `fiber f y = Σ (t : T), Path A (f t) y`. -/
def fiberM (k : ℕ) (T A f y : V) : V :=
  sigmaC k T (famV k T fun k' g t => pathC k' (res (Hom.wk k') (res g A)) (appV k' (res g f) t) (res g y))

/-! ### The equivalence codes -/

/-- `isContr X = Σ (c : X), (x : X) → Path X c x`. -/
def isContrM (k : ℕ) (X : V) : V :=
  sigmaC k X (famV k X fun k' g c => piC k' (res g X)
    (famV k' (res g X) fun k'' h x => pathC k'' (res (Hom.wk k'') (res h (res g X))) (res h c) x))

/-- `isEquiv f = (y : A) → isContr (fiber f y)`. -/
def isEquivM (k : ℕ) (T A f : V) : V :=
  piC k A (famV k A fun k' g y => isContrM k' (fiberM k' (res g T) (res g A) (res g f) y))

/-- `T → A`. -/
def arrowM (k : ℕ) (T A : V) : V := piC k T (famV k T fun _ g _ => res g A)

/-- `Equiv T A = Σ (f : T → A), isEquiv f`. -/
def equivM (k : ℕ) (T A : V) : V :=
  sigmaC k (arrowM k T A) (famV k (arrowM k T A) fun k' g p => isEquivM k' (res g T) (res g A) p)

/-! ### Transport (the spec's `Tm.transpGlue`) -/

/-- The endpoint maps at stage `n`. -/
abbrev eZ (n : ℕ) : Hom n (n + 1) := Hom.endpt n (DM.zero n)
abbrev eO (n : ℕ) : Hom n (n + 1) := Hom.endpt n (DM.one n)

section defs

variable (A : V) (φ : Cof (n + 1)) (Tp ep : V) (ψ : Cof n) (u0 : V)

/-- `a0 = unglue φ(0) e(0) u0`. -/
def gtA0 : V := ungAt n (φ.restr (eZ n)) (dat ep n (eZ n)) u0

/-- The tube `i ↦ unglue φ(i) e(i) u0` (a tube in the line `A` on `ψ`). -/
def gtTube : Tube n := fun n' h r => ungAt n' (φ.restr (Hom.snoc h r)) (dat ep n' (Hom.snoc h r)) (res h u0)

/-- `a1' = comp (i. A) [ψ ↦ unglue u0] a0`, at stage `n` (in `A(1)`). -/
def gtA1' : V := compF A (Hom.id (n + 1)) ψ (gtTube φ ep u0) (gtA0 φ ep u0)

/-- `fill (i. A) [ψ ↦ unglue u0] a0`, at stage `n + 1`. -/
def gtFillA : V := fillF A (Hom.id (n + 1)) ψ (gtTube φ ep u0) (gtA0 φ ep u0)

/-- `δ = ∀ i. φ`. -/
def gtδ : Cof n := Cof.forall0 φ

/-- The line `T` above `g` (on `δ`). -/
def gtTL (g : Hom k n) : V := dat Tp (k + 1) (Hom.lift g)

/-- `t1' = transp (i. T) ψ u0`, above `g` (on `δ`). -/
def gtT1' (g : Hom k n) : V := transpAt (gtTL Tp g) (Hom.id (k + 1)) (ψ.restr g) (res g u0)

/-- The line of the composition defining `ω`: `A(i)` above `g`, at stage `k + 2` (`j`, then `i`). -/
def gtΩLine (g : Hom k n) : Hom (k + 2) (n + 1) :=
  Hom.snoc ((g.comp (Hom.wk k)).comp (Hom.wk (k + 1))) (lastVar (k + 1))

/-- The system `[ψ ↦ e(i).1 u0, j = 0 ↦ e(i).1 (transpFill T ψ u0)(i), j = 1 ↦ fill A (i)]`. -/
def gtΩTube (g : Hom k n) : Tube (k + 1) := fun n' h r =>
  if (ψ.restr ((g.comp (Hom.wk k)).comp h)).holds then
    eqFun n' (dat ep n' (Hom.snoc ((g.comp (Hom.wk k)).comp h) r)) (res ((g.comp (Hom.wk k)).comp h) u0)
  else if ((Cof.eq0 (lastVar k)).restr h).holds then
    eqFun n' (dat ep n' (Hom.snoc ((g.comp (Hom.wk k)).comp h) r))
      (res (Hom.snoc ((Hom.wk k).comp h) r) (transpFillF (gtTL Tp g) (Hom.id (k + 1)) (ψ.restr g) (res g u0)))
  else res (Hom.snoc ((g.comp (Hom.wk k)).comp h) r) (gtFillA A φ ep ψ u0)

/-- The base `e(0).1 u0` of the composition defining `ω`. -/
def gtΩBase (g : Hom k n) : V :=
  eqFun (k + 1) (dat ep (k + 1) (Hom.snoc (g.comp (Hom.wk k)) (DM.zero (k + 1)))) (res (g.comp (Hom.wk k)) u0)

/-- The line of `ω` (`j` last), above `g`. -/
def gtΩ (g : Hom k n) : V :=
  compF A (gtΩLine g) (pathFace (ψ.restr g)) (gtΩTube A φ Tp ep ψ u0 g) (gtΩBase ep u0 g)

/-- `ω`: a path in `A(1)` from `e(1).1 t1'` to `a1'`, above `g` (on `δ`). -/
def gtω (g : Hom k n) : V := pathOfLine k (gtΩ A φ Tp ep ψ u0 g)

/-- `e(1)`, `T(1)` and `A(1)` above `g`. -/
def gtE1 (g : Hom k n) : V := dat ep k ((eO n).comp g)
def gtT1 (g : Hom k n) : V := dat Tp k ((eO n).comp g)
def gtAA1 (g : Hom k n) : V := res ((eO n).comp g) A

/-- `c = e(1).2 a1'`: the contractibility data of the fiber over `a1'`, above `g` (on `φ(1)`). -/
def gtC (g : Hom k n) : V := appV k (sndV k (gtE1 ep g)) (res g (gtA1' A φ ep ψ u0))

/-- The fiber of `e(1).1` over `a1'`, above `g`. -/
def gtFib (g : Hom k n) : V :=
  fiberM k (gtT1 Tp g) (gtAA1 A g) (fstV k (gtE1 ep g)) (res g (gtA1' A φ ep ψ u0))

/-- The partial element `[δ ↦ (t1', ω), ψ ↦ (u0, refl)]`, connected to the center by contractibility. -/
def gtExtTube (g : Hom k n) : Tube k := fun n' h r =>
  pappV n' (appV n' (res h (sndV k (gtC A φ ep ψ u0 g)))
    (if ((gtδ φ).restr (g.comp h)).holds then
      pairV n' (gtT1' Tp ψ u0 (g.comp h)) (gtω A φ Tp ep ψ u0 (g.comp h))
    else pairV n' (res (g.comp h) u0) (pathOfLine n' (res (Hom.wk n') (res (g.comp h) (gtA1' A φ ep ψ u0)))))) r

/-- `ext`, above `g` (on `φ(1)`). -/
def gtExt (g : Hom k n) : V :=
  hcompAt (gtFib A φ Tp ep ψ u0 g) (Hom.id k) (Cof.or ((gtδ φ).restr g) (ψ.restr g))
    (gtExtTube A φ Tp ep ψ u0 g) (fstV k (gtC A φ ep ψ u0 g))

/-- The tube `[φ(1) ↦ (snd ext)(~j), ψ ↦ a1']` of `a1`. -/
def gtA1Tube : Tube n := fun n' h r =>
  if (φ.restr ((eO n).comp h)).holds then pappV n' (sndV n' (gtExt A φ Tp ep ψ u0 h)) (DM.neg r)
  else res h (gtA1' A φ ep ψ u0)

/-- `a1 = hcomp A(1) [φ(1) ↦ (snd ext)(~j), ψ ↦ a1'] a1'`. -/
def gtA1 : V := hcompAt A (eO n) (Cof.or (φ.restr (eO n)) ψ) (gtA1Tube A φ Tp ep ψ u0) (gtA1' A φ ep ψ u0)

/-- The transport: `glue [φ(1) ↦ fst ext] a1`. -/
def gtResult : V :=
  if (φ.restr (eO n)).holds then fstV n (gtExt A φ Tp ep ψ u0 (Hom.id n))
  else glueV n (φ.restr (eO n)) (partialKV n (φ.restr (eO n)) fun k g => fstV k (gtExt A φ Tp ep ψ u0 g))
    (gtA1 A φ Tp ep ψ u0)

end defs

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

/-- The transport graph of Glue types: the spec's `Tm.transpGlue` (`gtResult`), along the last
variable of stage `n + 1`. -/
def glueTr : (k : ℕ) → V → (φ : Cof k) → V → V → V
  | 0, _, _, _, _ => ∅
  | n + 1, A, φ, Tp, ep =>
    trGraph n (if (φ.restr (eZ n)).holds then El (dat Tp n (eZ n)) (Hom.id n)
        else glueElSet n (res (eZ n) A) (φ.restr (eZ n)) (res (eZ n) Tp) (res (eZ n) ep))
      (gtResult A φ Tp ep)

def glueDatum (k : ℕ) (A : V) (φ : Cof k) (Tp ep : V) : V :=
  quad (tagZ tGlue (pair A (pair (enc φ) (pair Tp ep)))) (glueElSet k A φ Tp ep) (glueTr k A φ Tp ep)
    (glueHc k A φ Tp ep)

/-- The code `Glue A [φ ↦ (T, e)]` at stage `m`. -/
def glueC (m : ℕ) (A : V) (φ : Cof m) (Tp ep : V) : V :=
  mkKV m fun k f => if (φ.restr f).holds then here k (dat Tp k f)
    else glueDatum k (res f A) (φ.restr f) (res f Tp) (res f ep)

end

end Model
