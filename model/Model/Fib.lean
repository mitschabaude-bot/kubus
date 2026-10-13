import Model.Codes

/-!
# Fibrant codes

`Fib c m`: the code `c` at stage `m` is a lawful fibrant type. Its element sets consist of
Kripke values and are closed under restriction; `hcomp` and `transp` are typed, satisfy their
face (boundary) conditions, and are natural (uniform) in the stage. This is the CCHM notion of a
fibration structure, in the `transp`/`hcomp` formulation of Coquand–Huber–Mörtberg.
-/

set_option autoImplicit false

namespace Model

noncomputable section

variable {k m n : ℕ}

/-- `u` is a tube in `c` restricted along `f`, on the face `φ`, with base `u0`. -/
structure TubeOK (c : V) (f : Hom k m) (φ : Cof k) (u : Tube k) (u0 : V) : Prop where
  mem : ∀ n (h : Hom n k) r, (φ.restr h).holds → u n h r ∈ El c (f.comp h)
  coh : ∀ n (h : Hom n k) r, (φ.restr h).holds → ∀ n' (g : Hom n' n),
    res g (u n h r) = u n' (h.comp g) (r.restr g)
  base : ∀ n (h : Hom n k), (φ.restr h).holds → u n h (DM.zero n) = res h u0

/-- The line `c·f` (direction: the last variable) is constant on the face `φ`. -/
def ConstOn (c : V) (f : Hom (n + 1) m) (φ : Cof n) : Prop :=
  ∀ n' (h : Hom n' n), (φ.restr h).holds → ∀ r : DM n',
    res (f.comp (Hom.snoc h r)) c = res (f.comp (Hom.snoc h (DM.zero n'))) c

/-- `c` is a lawful fibrant type at stage `m`. -/
structure Fib (c : V) (m : ℕ) : Prop where
  kv : IsKV m c
  elKV : ∀ k (f : Hom k m) v, v ∈ El c f → IsKV k v
  elRes : ∀ k (f : Hom k m) v, v ∈ El c f → ∀ n (h : Hom n k), res h v ∈ El c (f.comp h)
  hcMem : ∀ k (f : Hom k m) φ u u0, φ.IsCof → u0 ∈ El c f → TubeOK c f φ u u0 →
    hcompAt c f φ u u0 ∈ El c f
  hcFace : ∀ k (f : Hom k m) φ u u0, φ.IsCof → u0 ∈ El c f → TubeOK c f φ u u0 → φ.holds →
    hcompAt c f φ u u0 = u k (Hom.id k) (DM.one k)
  hcRes : ∀ k (f : Hom k m) φ u u0, φ.IsCof → u0 ∈ El c f → TubeOK c f φ u u0 →
    ∀ n (h : Hom n k), res h (hcompAt c f φ u u0) = hcompAt c (f.comp h) (φ.restr h) (u.restr h) (res h u0)
  trMem : ∀ n (f : Hom (n + 1) m) φ a0, φ.IsCof → ConstOn c f φ →
    a0 ∈ El c (f.comp (Hom.endpt n (DM.zero n))) → transpAt c f φ a0 ∈ El c (f.comp (Hom.endpt n (DM.one n)))
  trFace : ∀ n (f : Hom (n + 1) m) φ a0, φ.IsCof → ConstOn c f φ →
    a0 ∈ El c (f.comp (Hom.endpt n (DM.zero n))) → φ.holds → transpAt c f φ a0 = a0
  trRes : ∀ n (f : Hom (n + 1) m) φ a0, φ.IsCof → ConstOn c f φ →
    a0 ∈ El c (f.comp (Hom.endpt n (DM.zero n))) → ∀ n' (h : Hom n' n),
    res h (transpAt c f φ a0) = transpAt c (f.comp (Hom.lift h)) (φ.restr h) (res h a0)

end

end Model
