import Model.Fib

/-!
# Π-types

Elements of `Π A B` at stage `k` are coherent Kripke families of functions: the datum at
`(n, g)` is the graph of a function on the elements of `A·g` at stage `n`.

The Kan operations are the spec's contracta `Tm.hcompPi` and `Tm.transpPi` (CHM), read
semantically.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

/-! ### Kripke functions -/

/-- Elements of a Π-type at stage `k`, given the domain sets `D n g` and codomain sets
`R n g a`. -/
def piEl (k : ℕ) (D : (n : ℕ) → Hom n k → V) (R : (n : ℕ) → Hom n k → V → V) : V :=
  ZFSet.sep (fun v => IsKV k v ∧
      (∀ n (g : Hom n k), dat v n g = fnZ (D n g) (apZ (dat v n g)) ∧
        ∀ a ∈ D n g, apZ (dat v n g) a ∈ R n g a) ∧
      (∀ n (g : Hom n k), ∀ a ∈ D n g, ∀ n' (h : Hom n' n),
        res h (apZ (dat v n g) a) = apZ (dat v n' (g.comp h)) (res h a)))
    (range fun G : (x : Dom k) → ↥(funs (D x.1 x.2) (⋃ a : ↥(D x.1 x.2), R x.1 x.2 a.1)) =>
      mkKV k fun n g => (G ⟨n, g⟩).1)

theorem mem_piEl {D : (n : ℕ) → Hom n k → V} {R : (n : ℕ) → Hom n k → V → V} {v : V} :
    v ∈ piEl k D R ↔ IsKV k v ∧
      (∀ n (g : Hom n k), dat v n g = fnZ (D n g) (apZ (dat v n g)) ∧
        ∀ a ∈ D n g, apZ (dat v n g) a ∈ R n g a) ∧
      (∀ n (g : Hom n k), ∀ a ∈ D n g, ∀ n' (h : Hom n' n),
        res h (apZ (dat v n g) a) = apZ (dat v n' (g.comp h)) (res h a)) := by
  rw [piEl, ZFSet.mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨hkv, hfun, -⟩ := h
  rw [mem_range]
  refine ⟨fun x => ⟨dat v x.1 x.2, ?_⟩, ?_⟩
  · rw [(hfun x.1 x.2).1]
    refine fnZ_mem_funs fun a ha => ?_
    rw [mem_iUnion]
    exact ⟨⟨a, ha⟩, (hfun x.1 x.2).2 a ha⟩
  · exact hkv.eq.symm

/-- A Kripke function from its graphs. -/
def lamV (k : ℕ) (D : (n : ℕ) → Hom n k → V) (F : (n : ℕ) → Hom n k → V → V) : V :=
  mkKV k fun n g => fnZ (D n g) (F n g)

/-- Application at the function's own stage. -/
def appV (k : ℕ) (v a : V) : V := apZ (here k v) a

@[simp] theorem dat_lamV (D : (n : ℕ) → Hom n k → V) (F : (n : ℕ) → Hom n k → V → V) (g : Hom n k) :
    dat (lamV k D F) n g = fnZ (D n g) (F n g) := dat_mkKV _ _

theorem res_lamV (D : (n : ℕ) → Hom n k → V) (F : (n : ℕ) → Hom n k → V → V) (h : Hom n k) :
    res h (lamV k D F) = lamV n (fun n' g => D n' (h.comp g)) (fun n' g => F n' (h.comp g)) := by
  simp [lamV]

theorem appV_lamV {D : (n : ℕ) → Hom n k → V} (F : (n : ℕ) → Hom n k → V → V) {a : V}
    (ha : a ∈ D k (Hom.id k)) : appV k (lamV k D F) a = F k (Hom.id k) a := by
  simp [appV, here, apZ_fnZ _ ha]

theorem appV_res (v : V) (g : Hom n k) (a : V) : appV n (res g v) a = apZ (dat v n g) a := by
  simp [appV, here]

theorem lamV_mem_piEl {D : (n : ℕ) → Hom n k → V} {R : (n : ℕ) → Hom n k → V → V}
    {F : (n : ℕ) → Hom n k → V → V}
    (hD : ∀ n (g : Hom n k), ∀ a ∈ D n g, ∀ n' (h : Hom n' n), res h a ∈ D n' (g.comp h))
    (hF : ∀ n (g : Hom n k), ∀ a ∈ D n g, F n g a ∈ R n g a)
    (hcoh : ∀ n (g : Hom n k), ∀ a ∈ D n g, ∀ n' (h : Hom n' n),
      res h (F n g a) = F n' (g.comp h) (res h a)) :
    lamV k D F ∈ piEl k D R := by
  rw [mem_piEl]
  refine ⟨isKV_mkKV _, fun n g => ⟨?_, fun a ha => ?_⟩, fun n g a ha n' h => ?_⟩
  · simp only [dat_lamV]; exact fnZ_congr fun a ha => (apZ_fnZ _ ha).symm
  · simp only [dat_lamV, apZ_fnZ _ ha]; exact hF n g a ha
  · simp only [dat_lamV, apZ_fnZ _ ha, apZ_fnZ _ (hD n g a ha n' h)]; exact hcoh n g a ha n' h

/-- Elements of `piEl` are determined by their applications. -/
theorem piEl_ext {D : (n : ℕ) → Hom n k → V} {R : (n : ℕ) → Hom n k → V → V} {v w : V}
    (hv : v ∈ piEl k D R) (hw : w ∈ piEl k D R)
    (h : ∀ n (g : Hom n k), ∀ a ∈ D n g, apZ (dat v n g) a = apZ (dat w n g) a) : v = w := by
  rw [mem_piEl] at hv hw
  refine hv.1.ext hw.1 fun n g => ?_
  rw [(hv.2.1 n g).1, (hw.2.1 n g).1]
  exact fnZ_congr fun a ha => h n g a ha

theorem eq_lamV_of_mem_piEl {D : (n : ℕ) → Hom n k → V} {R : (n : ℕ) → Hom n k → V → V} {v : V}
    (hv : v ∈ piEl k D R) : v = lamV k D fun n g a => apZ (dat v n g) a := by
  rw [mem_piEl] at hv
  refine hv.1.ext (isKV_mkKV _) fun n g => ?_
  rw [dat_lamV]; exact (hv.2.1 n g).1

/-! ### The Π code -/

/-- Elements of `Π A B` at stage `k`, for components `A`, `B` at stage `k`. -/
def piElSet (k : ℕ) (A B : V) : V :=
  piEl k (fun _ g => El A g) (fun n g a => El (apZ (dat B n g) a) (Hom.id n))

/-- `hcomp (Π A B) [φ ↦ u] u0 = λ v. hcomp (B v) [φ ↦ u v] (u0 v)` (spec: `Tm.hcompPi`). -/
def hcompPiF (k : ℕ) (A B : V) (φ : Cof k) (u : Tube k) (u0 : V) : V :=
  lamV k (fun _ g => El A g) fun n g v =>
    hcompAt (apZ (dat B n g) v) (Hom.id n) (φ.restr g)
      (fun n' g' r => appV n' (u n' (g.comp g') r) (res g' v)) (appV n (res g u0) v)

/-- At stage `n + 2`: the second-to-last variable. -/
def iVar (n : ℕ) : DM (n + 2) := DM.var (Fin.last n).castSucc
/-- At stage `n + 2`: the last variable. -/
def jVar (n : ℕ) : DM (n + 2) := DM.var (Fin.last (n + 1))

/-- `transp (i. Π A B) φ u0 = λ v. transp (i. B[w(i)]) φ (u0 w0)` with
`w(i) = transp (j. A(i ∨ ~j)) (φ ∨ i = 1) v` and `w0 = transp (j. A(~j)) φ v`
(spec: `Tm.transpPi`). Here `A`, `B` are at stage `n + 1`, the line variable being the last. -/
def transpPiF (n : ℕ) (A B : V) (φ : Cof n) (u0 : V) : V :=
  lamV n (fun _ g => El A ((Hom.endpt n (DM.one n)).comp g)) fun n' g v =>
    let w := transpAt A
      (Hom.snoc (g.comp ((Hom.wk n').comp (Hom.wk (n' + 1)))) (DM.max (iVar n') (DM.neg (jVar n'))))
      (Cof.or (φ.restr (g.comp (Hom.wk n'))) (Cof.eq1 (DM.var (Fin.last n')))) (res (Hom.wk n') v)
    let w0 := transpAt A (Hom.snoc (g.comp (Hom.wk n')) (DM.neg (DM.var (Fin.last n')))) (φ.restr g) v
    transpAt (apZ (dat B (n' + 1) (Hom.lift g)) w) (Hom.id (n' + 1)) (φ.restr g) (appV n' (res g u0) w0)

def piHc (k : ℕ) (A B : V) : V := hcGraph k (fun n g => piElSet n (res g A) (res g B)) (hcompPiF k A B)

def piTr : (k : ℕ) → V → V → V
  | 0, _, _ => ∅
  | n + 1, A, B => trGraph n (piElSet n (res (Hom.endpt n (DM.zero n)) A) (res (Hom.endpt n (DM.zero n)) B))
      (transpPiF n A B)

def piDatum (k : ℕ) (A B : V) : V := quad (tagZ tPi (pair A B)) (piElSet k A B) (piTr k A B) (piHc k A B)

/-- The code `Π A B` at stage `m`: `A` a code, `B` a family of codes over `A`. -/
def piC (m : ℕ) (A B : V) : V := mkKV m fun k f => piDatum k (res f A) (res f B)

@[simp] theorem El_piC (A B : V) (f : Hom k m) : El (piC m A B) f = piElSet k (res f A) (res f B) := by
  simp [piC, piDatum]

theorem res_piC (A B : V) (h : Hom k m) : res h (piC m A B) = piC k (res h A) (res h B) := by
  simp [piC, res_res]

theorem hcG_piC (A B : V) (f : Hom k m) : hcG (piC m A B) f = piHc k (res f A) (res f B) := by
  simp [piC, piDatum]

theorem trG_piC (A B : V) (f : Hom (n + 1) m) : trG (piC m A B) f = piTr (n + 1) (res f A) (res f B) := by
  simp [piC, piDatum]

end

end Model
