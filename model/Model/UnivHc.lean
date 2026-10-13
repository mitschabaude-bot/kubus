import Model.Glue

/-!
# `hcomp` in the universe: definitions

`hcomp U [φ ↦ u] u0` is `Glue u0 [φ ↦ (u(1), e)]` where `e : u(1) ≃ u0` is transport backwards
along the tube (CCHM). That transport is an equivalence is proven by transporting the identity
equivalence: along `i`, the function `f_i = transp (j. B(i ∧ j)) (i = 0) : B(0) → B(i)` is the
identity at `i = 0`, so transporting the evident proof `idEqV` that it is an equivalence along
`i ↦ isEquiv f_i` gives a proof for `f_1`.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-- The line `j ↦ B(i ∧ j)` seen from `g` (`i` the last variable of `n + 1`). -/
def eqLine (n : ℕ) (g : Hom k (n + 1)) : Hom (k + 1) (n + 1) :=
  Hom.snoc ((Hom.wk n).comp (g.comp (Hom.wk k))) (DM.min ((lastVar n).restr (g.comp (Hom.wk k))) (lastVar k))

/-- `f_i = transp (j. B(i ∧ j)) (i = 0) : B(0) → B(i)`, at stage `n + 1`. -/
def eqFunL (n : ℕ) (B : V) : V :=
  lamV (n + 1) (fun _ g => El (res (Hom.wk n) (res (eZ n) B)) g)
    fun _ g x => transpAt B (eqLine n g) (Cof.eq0 ((lastVar n).restr g)) x

/-- The line of types `i ↦ isEquiv f_i`. -/
def eqQ (n : ℕ) (B : V) : V := isEquivM (n + 1) (res (Hom.wk n) (res (eZ n) B)) B (eqFunL n B)

/-- `(i, j) ↦ ~i ∨ j`, at stage `k + 2`. -/
def connHom (k : ℕ) : Hom (k + 2) (k + 1) :=
  Hom.snoc ((Hom.wk k).comp (Hom.wk (k + 1))) (DM.max (DM.neg (iVar k)) (jVar k))

/-- The contraction of the fiber of the identity: `(x, p) ↦ ⟨i⟩ (p(~i), ⟨j⟩ p(~i ∨ j))`, as a line. -/
def connV (k : ℕ) (z : V) : V :=
  pairV (k + 1) (pappV (k + 1) (res (Hom.wk k) (sndV k z)) (DM.neg (lastVar k)))
    (pathOfLine (k + 1) (res (connHom k) (lineOf k (sndV k z))))

/-- The identity is an equivalence: for `F` acting as the identity on `T`. -/
def idEqV (n : ℕ) (T F : V) : V :=
  lamV n (fun _ g => El T g) fun k g y =>
    pairV k (pairV k y (pathOfLine k (res (Hom.wk k) y)))
      (lamV k (fun _ g' => El (fiberM k (res g T) (res g T) (res g F) y) g') fun k' _ z => pathOfLine k' (connV k' z))

/-- Transport backwards along `B`, as an equivalence `B(0) ≃ B(1)`. -/
def eqTr (n : ℕ) (B : V) : V :=
  pairV n (res (eO n) (eqFunL n B))
    (transpAt (eqQ n B) (Hom.id (n + 1)) (Cof.bot n) (idEqV n (res (eZ n) B) (res (eZ n) (eqFunL n B))))

/-- Reversal of the last variable. -/
def revLine (n : ℕ) : Hom (n + 1) (n + 1) := Hom.snoc (Hom.wk n) (DM.neg (lastVar n))

/-- `hcomp U [φ ↦ u] u0`, at stage `k`. -/
def univHcF (k : ℕ) (φ : Cof k) (u : Tube k) (u0 : V) : V :=
  if φ.holds then u k (Hom.id k) (DM.one k)
  else glueC k u0 φ (partialKV k φ fun n g => u n g (DM.one n))
    (partialKV k φ fun n g => eqTr n (res (revLine n) (u (n + 1) (g.comp (Hom.wk n)) (lastVar n))))

end

end Model
