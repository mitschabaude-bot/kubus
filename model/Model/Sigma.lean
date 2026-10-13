import Model.Kan

/-!
# Σ-types

Elements are Kripke pairs. The Kan operations are the spec's `Tm.transpSigma` (using
`transpFill`) and `Tm.hcompSigma` (using `hfill` and `comp`).
-/

set_option autoImplicit false

namespace Model

open ZFSet

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

/-! ### Pairs -/

/-- Pairs as Kripke values. -/
def pairV (k : ℕ) (a b : V) : V := mkKV k fun _ g => pair (res g a) (res g b)

def fstV (k : ℕ) (p : V) : V := π1 (here k p)
def sndV (k : ℕ) (p : V) : V := π2 (here k p)

theorem res_pairV (a b : V) (h : Hom n k) : res h (pairV k a b) = pairV n (res h a) (res h b) := by
  simp [pairV, res_res]

theorem fstV_pairV {a b : V} (ha : IsKV k a) : fstV k (pairV k a b) = a := by
  simp [fstV, pairV, res_id ha]

theorem sndV_pairV {a b : V} (hb : IsKV k b) : sndV k (pairV k a b) = b := by
  simp [sndV, pairV, res_id hb]

theorem fstV_res (p : V) (h : Hom n k) : fstV n (res h p) = π1 (dat p n h) := by
  simp [fstV, here]

/-- Elements of a Σ-type at stage `k`. -/
def sigmaEl (k : ℕ) (DA : V) (R : V → V) : V :=
  range fun x : (Σ a : ↥DA, ↥(R a.1)) => pairV k x.1.1 x.2.1

theorem mem_sigmaEl {DA : V} {R : V → V} {v : V} :
    v ∈ sigmaEl k DA R ↔ ∃ a ∈ DA, ∃ b ∈ R a, v = pairV k a b := by
  simp only [sigmaEl, mem_range, Sigma.exists, Subtype.exists]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

/-! ### The Σ code -/

def sigmaElSet (k : ℕ) (A B : V) : V :=
  sigmaEl k (El A (Hom.id k)) fun a => El (apZ (dat B k (Hom.id k)) a) (Hom.id k)

/-- `transp (i. Σ A B) φ u0 = (transp A φ u0.1, transp (i. B[a(i)]) φ u0.2)`, `a` the transport
filler (spec: `Tm.transpSigma`). `A`, `B` at stage `n + 1`. -/
def transpSigmaF (n : ℕ) (A B : V) (φ : Cof n) (u0 : V) : V :=
  pairV n (transpAt A (Hom.id (n + 1)) φ (fstV n u0))
    (transpAt (apZ (dat B (n + 1) (Hom.id (n + 1))) (transpFillF A (Hom.id (n + 1)) φ (fstV n u0)))
      (Hom.id (n + 1)) φ (sndV n u0))

/-- The first and second components of a tube. -/
def Tube.fst (u : Tube k) : Tube k := fun n h r => fstV n (u n h r)
def Tube.snd (u : Tube k) : Tube k := fun n h r => sndV n (u n h r)

/-- `hcomp (Σ A B) [φ ↦ u] u0 = (hcomp A [φ ↦ u.1] u0.1, comp (i. B[hfill]) [φ ↦ u.2] u0.2)`
(spec: `Tm.hcompSigma`). `A`, `B` at stage `k`. -/
def hcompSigmaF (k : ℕ) (A B : V) (φ : Cof k) (u : Tube k) (u0 : V) : V :=
  pairV k (hcompAt A (Hom.id k) φ u.fst (fstV k u0))
    (compF (apZ (dat B (k + 1) (Hom.wk k)) (hfillF A (Hom.id k) φ u.fst (fstV k u0))) (Hom.id (k + 1))
      φ u.snd (sndV k u0))

def sigmaHc (k : ℕ) (A B : V) : V :=
  hcGraph k (fun n g => sigmaElSet n (res g A) (res g B)) (hcompSigmaF k A B)

def sigmaTr : (k : ℕ) → V → V → V
  | 0, _, _ => ∅
  | n + 1, A, B => trGraph n (sigmaElSet n (res (Hom.endpt n (DM.zero n)) A) (res (Hom.endpt n (DM.zero n)) B))
      (transpSigmaF n A B)

def sigmaDatum (k : ℕ) (A B : V) : V :=
  quad (tagZ tSigma (pair A B)) (sigmaElSet k A B) (sigmaTr k A B) (sigmaHc k A B)

/-- The code `Σ A B` at stage `m`. -/
def sigmaC (m : ℕ) (A B : V) : V := mkKV m fun k f => sigmaDatum k (res f A) (res f B)

@[simp] theorem El_sigmaC (A B : V) (f : Hom k m) :
    El (sigmaC m A B) f = sigmaElSet k (res f A) (res f B) := by
  simp [sigmaC, sigmaDatum]

theorem res_sigmaC (A B : V) (h : Hom k m) : res h (sigmaC m A B) = sigmaC k (res h A) (res h B) := by
  simp [sigmaC, res_res]

theorem hcG_sigmaC (A B : V) (f : Hom k m) : hcG (sigmaC m A B) f = sigmaHc k (res f A) (res f B) := by
  simp [sigmaC, sigmaDatum]

theorem trG_sigmaC (A B : V) (f : Hom (n + 1) m) :
    trG (sigmaC m A B) f = sigmaTr (n + 1) (res f A) (res f B) := by
  simp [sigmaC, sigmaDatum]

theorem sigmaC_inj {A1 B1 A2 B2 : V} (hA1 : IsKV k A1) (hB1 : IsKV k B1) (hA2 : IsKV k A2)
    (hB2 : IsKV k B2) (h : sigmaC k A1 B1 = sigmaC k A2 B2) : A1 = A2 ∧ B1 = B2 := by
  have := congrArg (fun c => shapeOf c (Hom.id k)) h
  simp only [sigmaC, shapeOf_mkKV, sigmaDatum, π1_quad, tagZ_inj, pair_inj', true_and] at this
  rwa [res_id hA1, res_id hB1, res_id hA2, res_id hB2] at this

/-! ### Elements -/

section elements

variable {A B : V} (hA : Fib A m) (hB : FamOK A B m)
include hA hB

theorem mem_sigmaC {f : Hom k m} {v : V} :
    v ∈ El (sigmaC m A B) f ↔ ∃ a ∈ El A f, ∃ b ∈ El (apZ (dat B k f) a) (Hom.id k), v = pairV k a b := by
  rw [El_sigmaC, sigmaElSet, mem_sigmaEl, El_res, Hom.comp_id, dat_res, Hom.comp_id]

theorem sigma_eta {f : Hom k m} {v : V} (hv : v ∈ El (sigmaC m A B) f) :
    v = pairV k (fstV k v) (sndV k v) ∧ fstV k v ∈ El A f ∧
      sndV k v ∈ El (apZ (dat B k f) (fstV k v)) (Hom.id k) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sigmaC hA hB).1 hv
  have hka := hA.elKV _ _ a ha
  have hkb := (hB.fib _ _ a ha).elKV _ _ b hb
  rw [fstV_pairV hka, sndV_pairV hkb]
  exact ⟨rfl, ha, hb⟩

theorem sigma_elKV {f : Hom k m} {v : V} (hv : v ∈ El (sigmaC m A B) f) : IsKV k v := by
  obtain ⟨a, -, b, -, rfl⟩ := (mem_sigmaC hA hB).1 hv; exact isKV_mkKV _

theorem sigma_elRes {f : Hom k m} {v : V} (hv : v ∈ El (sigmaC m A B) f) (h : Hom n k) :
    res h v ∈ El (sigmaC m A B) (f.comp h) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sigmaC hA hB).1 hv
  rw [res_pairV, mem_sigmaC hA hB]
  refine ⟨res h a, hA.elRes _ _ a ha _ h, res h b, ?_, rfl⟩
  have := (hB.fib _ _ a ha).elRes _ _ b hb _ h
  rwa [Hom.id_comp, ← Hom.comp_id h, ← El_res, hB.coh _ _ a ha _ h, Hom.comp_id] at this

theorem sigma_fst_res {f : Hom k m} {v : V} (hv : v ∈ El (sigmaC m A B) f) (h : Hom n k) :
    fstV n (res h v) = res h (fstV k v) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sigmaC hA hB).1 hv
  rw [res_pairV, fstV_pairV (isKV_res _ _), fstV_pairV (hA.elKV _ _ a ha)]

theorem sigma_snd_res {f : Hom k m} {v : V} (hv : v ∈ El (sigmaC m A B) f) (h : Hom n k) :
    sndV n (res h v) = res h (sndV k v) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sigmaC hA hB).1 hv
  rw [res_pairV, sndV_pairV (isKV_res _ _), sndV_pairV ((hB.fib _ _ a ha).elKV _ _ b hb)]

end elements

end

end Model
