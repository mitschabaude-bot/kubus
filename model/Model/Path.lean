import Model.SigmaFib

/-!
# Path types and interval function types

A path (or element of `(i : I) → A`) at stage `k` is determined by an element `p` of the line
at stage `k + 1` (the exponential by the interval is the shift `k ↦ k + 1`); as a Kripke value
it is `pathOfLine k p`, whose datum at `(n, g)` is the graph `r ↦ p(g, r)`.

The Kan operations are the spec's `Tm.transpPath`, `Tm.hcompPath`, `Tm.transpIPi`,
`Tm.hcompIPi`, read semantically.
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

/-! ### Paths as Kripke values -/

/-- A path at stage `k` from its value `p` at stage `k + 1`. -/
def pathOfLine (k : ℕ) (p : V) : V := mkKV k fun _ g => fnC fun r : DM _ => res (Hom.snoc g r) p

/-- Path application at the path's own stage. -/
def pappV (k : ℕ) (v : V) (r : DM k) : V := apC (here k v) r

theorem pappV_pathOfLine (p : V) (r : DM k) : pappV k (pathOfLine k p) r = res (Hom.endpt k r) p := by
  simp [pappV, pathOfLine, Hom.endpt]

theorem res_pathOfLine (p : V) (h : Hom n k) : res h (pathOfLine k p) = pathOfLine n (res (Hom.lift h) p) := by
  simp only [pathOfLine, res_mkKV, res_res, lift_comp_snoc]

theorem pappV_res (v : V) (h : Hom n k) (r : DM n) : pappV n (res h v) r = apC (dat v n h) r := by
  simp [pappV, here]

theorem snoc_wk_last : Hom.snoc (Hom.wk k) (lastVar k) = Hom.id (k + 1) := by
  apply Hom.ext_snoc <;> intro p <;> simp

theorem pathOfLine_inj {p p' : V} (hp : IsKV (k + 1) p) (hp' : IsKV (k + 1) p')
    (h : pathOfLine k p = pathOfLine k p') : p = p' := by
  have := congrArg (fun v => apC (dat v (k + 1) (Hom.wk k)) (lastVar k)) h
  simp only [pathOfLine, dat_mkKV, apC_fnC, snoc_wk_last] at this
  rwa [res_id hp, res_id hp'] at this

/-- Elements of a path type at stage `k`, given the elements of the line at stage `k + 1`. -/
def pathEl (k : ℕ) (EL : V) (a0 a1 : V) : V :=
  ZFSet.sep (fun v => ∃ p ∈ EL, v = pathOfLine k p ∧
      res (Hom.endpt k (DM.zero k)) p = a0 ∧ res (Hom.endpt k (DM.one k)) p = a1)
    (range fun p : ↥EL => pathOfLine k p.1)

theorem mem_pathEl {EL a0 a1 v : V} :
    v ∈ pathEl k EL a0 a1 ↔ ∃ p ∈ EL, v = pathOfLine k p ∧
      res (Hom.endpt k (DM.zero k)) p = a0 ∧ res (Hom.endpt k (DM.one k)) p = a1 := by
  rw [pathEl, ZFSet.mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨p, hp, rfl, -⟩ := h
  exact mem_range.2 ⟨⟨p, hp⟩, rfl⟩

/-- Elements of `(i : I) → A` at stage `k`. -/
def ipiEl (k : ℕ) (EL : V) : V := range fun p : ↥EL => pathOfLine k p.1

theorem mem_ipiEl {EL v : V} : v ∈ ipiEl k EL ↔ ∃ p ∈ EL, v = pathOfLine k p := by
  simp only [ipiEl, mem_range, Subtype.exists]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h.symm⟩⟩

/-! ### Kan operations -/

/-- The face `φ ∨ j = 0 ∨ j = 1` at stage `k + 1`. -/
def pathFace (φ : Cof k) : Cof (k + 1) :=
  Cof.or (φ.restr (Hom.wk k)) (Cof.or (Cof.eq0 (lastVar k)) (Cof.eq1 (lastVar k)))

/-- The tube `[φ ↦ u j, j = 0 ↦ a, j = 1 ↦ b]` of `hcompPath`, at stage `k + 1`. -/
def pathHTube (φ : Cof k) (u : Tube k) (a0 a1 : V) : Tube (k + 1) := fun n h r =>
  if (φ.restr ((Hom.wk k).comp h)).holds then pappV n (u n ((Hom.wk k).comp h) r) ((lastVar k).restr h)
  else if ((Cof.eq0 (lastVar k)).restr h).holds then res ((Hom.wk k).comp h) a0
  else res ((Hom.wk k).comp h) a1

/-- `hcomp (PathP (j. A) a b) [φ ↦ u] p0 = ⟨j⟩ hcomp A [φ ↦ u j, j = 0 ↦ a, j = 1 ↦ b] (p0 j)`
(spec: `Tm.hcompPath`). `L` is the line at stage `k + 1`, `a0`, `a1` at stage `k`. -/
def hcompPathF (k : ℕ) (L a0 a1 : V) (φ : Cof k) (u : Tube k) (p0 : V) : V :=
  pathOfLine k (hcompAt L (Hom.id (k + 1)) (pathFace φ) (pathHTube φ u a0 a1)
    (pappV (k + 1) (res (Hom.wk k) p0) (lastVar k)))

/-- `hcomp ((j : I) → A) [φ ↦ u] u0 = ⟨j⟩ hcomp A [φ ↦ u j] (u0 j)` (spec: `Tm.hcompIPi`). -/
def hcompIPiF (k : ℕ) (L : V) (φ : Cof k) (u : Tube k) (p0 : V) : V :=
  pathOfLine k (hcompAt L (Hom.id (k + 1)) (φ.restr (Hom.wk k))
    (fun n h r => pappV n (u n ((Hom.wk k).comp h) r) ((lastVar k).restr h))
    (pappV (k + 1) (res (Hom.wk k) p0) (lastVar k)))

/-- Exchange the last two variables: from the stage `(Ψ, j, i)` of the composition to the stage
`(Ψ, i, j)` of the line of a path type in a line of types. -/
def swapHom (n : ℕ) : Hom (n + 2) (n + 2) :=
  Hom.snoc (Hom.snoc ((Hom.wk n).comp (Hom.wk (n + 1))) (jVar n)) (iVar n)

/-- The tube `[φ ↦ p0 j, j = 0 ↦ a(i), j = 1 ↦ b(i)]` of `transpPath`, at stage `n + 1` (`j` last),
the tube direction being `i`. `a0`, `a1` are at stage `n + 1` (`i` last). -/
def pathTTube (φ : Cof n) (p0 a0 a1 : V) : Tube (n + 1) := fun n' h r =>
  if (φ.restr ((Hom.wk n).comp h)).holds then pappV n' (res ((Hom.wk n).comp h) p0) ((lastVar n).restr h)
  else if ((Cof.eq0 (lastVar n)).restr h).holds then res (Hom.snoc ((Hom.wk n).comp h) r) a0
  else res (Hom.snoc ((Hom.wk n).comp h) r) a1

/-- `transp (i. PathP (j. A) a b) φ p0 = ⟨j⟩ comp (i. A) [φ ↦ p0 j, j = 0 ↦ a, j = 1 ↦ b] (p0 j)`
(spec: `Tm.transpPath`). `L` is at stage `n + 2` (`i`, then `j` last), `a0`, `a1` at stage `n + 1`. -/
def transpPathF (n : ℕ) (L a0 a1 : V) (φ : Cof n) (p0 : V) : V :=
  pathOfLine n (compF L (swapHom n) (pathFace φ) (pathTTube φ p0 a0 a1)
    (pappV (n + 1) (res (Hom.wk n) p0) (lastVar n)))

/-- `transp (i. (j : I) → A) φ u0 = ⟨j⟩ transp (i. A) φ (u0 j)` (spec: `Tm.transpIPi`). -/
def transpIPiF (n : ℕ) (L : V) (φ : Cof n) (p0 : V) : V :=
  pathOfLine n (transpAt L (swapHom n) (φ.restr (Hom.wk n)) (pappV (n + 1) (res (Hom.wk n) p0) (lastVar n)))

/-! ### The codes -/

def pathElSet (k : ℕ) (L a0 a1 : V) : V := pathEl k (El L (Hom.id (k + 1))) a0 a1

def pathHc (k : ℕ) (L a0 a1 : V) : V :=
  hcGraph k (fun n g => pathElSet n (res (Hom.lift g) L) (res g a0) (res g a1)) (hcompPathF k L a0 a1)

def pathTr : (k : ℕ) → V → V → V → V
  | 0, _, _, _ => ∅
  | n + 1, L, a0, a1 => trGraph n (pathElSet n (res (Hom.lift (Hom.endpt n (DM.zero n))) L)
      (res (Hom.endpt n (DM.zero n)) a0) (res (Hom.endpt n (DM.zero n)) a1)) (transpPathF n L a0 a1)

def pathDatum (k : ℕ) (L a0 a1 : V) : V :=
  quad (tagZ tPath (pair L (pair a0 a1))) (pathElSet k L a0 a1) (pathTr k L a0 a1) (pathHc k L a0 a1)

/-- The code `PathP (j. L) a0 a1` at stage `m`: `L` a code at stage `m + 1`. -/
def pathC (m : ℕ) (L a0 a1 : V) : V :=
  mkKV m fun k f => pathDatum k (res (Hom.lift f) L) (res f a0) (res f a1)

def ipiElSet (k : ℕ) (L : V) : V := ipiEl k (El L (Hom.id (k + 1)))

def ipiHc (k : ℕ) (L : V) : V :=
  hcGraph k (fun n g => ipiElSet n (res (Hom.lift g) L)) (hcompIPiF k L)

def ipiTr : (k : ℕ) → V → V
  | 0, _ => ∅
  | n + 1, L => trGraph n (ipiElSet n (res (Hom.lift (Hom.endpt n (DM.zero n))) L)) (transpIPiF n L)

def ipiDatum (k : ℕ) (L : V) : V :=
  quad (tagZ tIPi (pair L ∅)) (ipiElSet k L) (ipiTr k L) (ipiHc k L)

/-- The code `(i : I) → L` at stage `m`. -/
def ipiC (m : ℕ) (L : V) : V := mkKV m fun k f => ipiDatum k (res (Hom.lift f) L)

@[simp] theorem El_pathC (L a0 a1 : V) (f : Hom k m) :
    El (pathC m L a0 a1) f = pathElSet k (res (Hom.lift f) L) (res f a0) (res f a1) := by
  simp [pathC, pathDatum]

@[simp] theorem El_ipiC (L : V) (f : Hom k m) : El (ipiC m L) f = ipiElSet k (res (Hom.lift f) L) := by
  simp [ipiC, ipiDatum]

theorem res_pathC (L a0 a1 : V) (h : Hom k m) :
    res h (pathC m L a0 a1) = pathC k (res (Hom.lift h) L) (res h a0) (res h a1) := by
  simp [pathC, res_res, Hom.lift_comp]

theorem res_ipiC (L : V) (h : Hom k m) : res h (ipiC m L) = ipiC k (res (Hom.lift h) L) := by
  simp [ipiC, res_res, Hom.lift_comp]

theorem pathC_inj {L1 a1 b1 L2 a2 b2 : V} (hL1 : IsKV (k + 1) L1) (ha1 : IsKV k a1) (hb1 : IsKV k b1)
    (hL2 : IsKV (k + 1) L2) (ha2 : IsKV k a2) (hb2 : IsKV k b2)
    (h : pathC k L1 a1 b1 = pathC k L2 a2 b2) : L1 = L2 ∧ a1 = a2 ∧ b1 = b2 := by
  have := congrArg (fun c => shapeOf c (Hom.id k)) h
  simp only [pathC, shapeOf_mkKV, pathDatum, π1_quad, tagZ_inj, pair_inj', true_and, Hom.lift_id] at this
  rwa [res_id hL1, res_id ha1, res_id hb1, res_id hL2, res_id ha2, res_id hb2] at this

theorem ipiC_inj {L1 L2 : V} (hL1 : IsKV (k + 1) L1) (hL2 : IsKV (k + 1) L2)
    (h : ipiC k L1 = ipiC k L2) : L1 = L2 := by
  have := congrArg (fun c => shapeOf c (Hom.id k)) h
  simp only [ipiC, shapeOf_mkKV, ipiDatum, π1_quad, tagZ_inj, pair_inj', true_and, Hom.lift_id,
    and_true] at this
  rwa [res_id hL1, res_id hL2] at this

end

end Model
