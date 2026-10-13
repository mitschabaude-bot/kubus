import Model.Univ

/-!
# Glue elements, equivalences, and generic lemmas about Kripke values

Lemmas about the data of Glue codes and their elements, and about the first component of an
element of `equivCode` (the function of an equivalence), used for the fibrancy of Glue types
and for the Glue rules.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n : ℕ}

theorem not_isKV_empty : ¬ IsKV m (∅ : V) := by
  rintro ⟨F, h⟩
  have : ZFSet.pair (enc (⟨m, Hom.id m⟩ : Dom m)) (F m (Hom.id m)) ∈ (∅ : V) := by
    rw [h]; exact mem_fnC.2 ⟨⟨m, Hom.id m⟩, rfl⟩
  exact ZFSet.notMem_empty _ this

theorem dat_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) (f : Hom k m) :
    dat (famV m A F) k f = fnZ (El A f) (F k f) := by simp [famV]

theorem apZ_dat_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) (f : Hom k m) {a : V} (ha : a ∈ El A f) :
    apZ (dat (famV m A F) k f) a = F k f a := by rw [dat_famV, apZ_fnZ _ ha]

theorem res_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) (h : Hom n m) :
    res h (famV m A F) = famV n (res h A) (fun k' g => F k' (h.comp g)) := by
  simp only [famV, res_lamV, El_res]

theorem isKV_famV (A : V) (F : (k : ℕ) → Hom k m → V → V) : IsKV m (famV m A F) := by
  unfold famV lamV; exact isKV_mkKV _

theorem dat_empty' (f : Hom k m) : dat (∅ : V) k f = ∅ := by
  simp only [dat, apC, apZ]; rw [dif_neg]; rintro ⟨y, hy⟩; exact ZFSet.notMem_empty _ hy

theorem ne_pair_empty : ¬ ∃ a b : V, (∅ : V) = ZFSet.pair a b := by
  rintro ⟨a, b, h⟩
  have : ({a} : V) ∈ ZFSet.pair a b := by simp [ZFSet.pair]
  rw [← h] at this; exact ZFSet.notMem_empty _ this

theorem π1_empty : π1 (∅ : V) = ∅ := by simp only [π1]; rw [dif_neg ne_pair_empty]

theorem π2_empty : π2 (∅ : V) = ∅ := by simp only [π2]; rw [dif_neg ne_pair_empty]

theorem fstV_empty : fstV m (∅ : V) = ∅ := by simp only [fstV, here, dat_empty', π1_empty]

theorem sndV_empty : sndV m (∅ : V) = ∅ := by simp only [sndV, here, dat_empty', π2_empty]

theorem isKV_glueC (A : V) (φ : Cof m) (Tp ep : V) : IsKV m (glueC m A φ Tp ep) := by
  unfold glueC; exact isKV_mkKV _

theorem partialKV_self (φ : Cof m) (F : (k : ℕ) → Hom k m → V) :
    partialKV m φ F = partialKV m φ (fun k f => dat (partialKV m φ F) k f) := by
  unfold partialKV; congr 1; funext k f; by_cases h : (φ.restr f).holds <;> simp [h]

/-- On its face, a Glue code is its `T`. -/
theorem glueC_holds {A : V} {φ : Cof m} {Tp ep : V} (hφ : φ.IsCof) (hh : φ.holds)
    (hcoh : ∀ k (f : Hom k m), (φ.restr f).holds → dat Tp k f = res f (dat Tp m (Hom.id m)))
    (hkv : IsKV m (dat Tp m (Hom.id m))) : glueC m A φ Tp ep = dat Tp m (Hom.id m) := by
  refine (isKV_glueC _ _ _ _).ext hkv fun k f => ?_
  have hf : (φ.restr f).holds := hφ.holds_restr hh f
  rw [glueC, dat_mkKV, if_pos hf, hcoh k f hf, here_res]

theorem El_empty' (f : Hom k m) : El (∅ : V) f = ∅ := by
  have : π1 (∅ : V) = ∅ := by simp only [π1]; rw [dif_neg ne_pair_empty]
  have h2 : π2 (∅ : V) = ∅ := by simp only [π2]; rw [dif_neg ne_pair_empty]
  simp only [El, dat_empty', h2, this]

theorem equivCode_kv_of_mem {T A v : V} (f : Hom k m) (hv : v ∈ El (equivCode m T A) f) :
    IsKV m (equivCode m T A) := by
  unfold equivCode Tm.equiv at *
  simp only [interp] at hv ⊢
  split at hv
  · rename_i h; rw [if_pos h]; exact isKV_mkKV _
  · rw [El_empty'] at hv; exact absurd hv (ZFSet.notMem_empty _)

theorem equivCode_eq {T A : V} (hT : IsKV m T) :
    ∃ Q, equivCode m T A = sigmaC m (piC m T (famV m T fun _ f _ => res f A)) Q := by
  have hP : IsKV m (piC m T (famV m T fun _ f _ => res f A)) := by unfold piC; exact isKV_mkKV _
  unfold equivCode Tm.equiv Tm.arrow
  simp only [interp, Tm.shift, Tm.ren, TEnv.cons_zero, TEnv.cons_succ, TEnv.restr, Nat.succ_eq_add_one, zero_add,
    hT, if_true]
  rw [if_pos hP]
  exact ⟨_, rfl⟩

theorem equiv_fst {T A v : V} (hT : IsKV m T) (hv : v ∈ El (equivCode m T A) (Hom.id m)) :
    fstV m v ∈ piElSet m T (famV m T fun _ f _ => res f A) := by
  obtain ⟨Q, hQ⟩ := equivCode_eq (A := A) hT
  rw [hQ, El_sigmaC, sigmaElSet, mem_sigmaEl] at hv
  obtain ⟨p, hp, q, -, rfl⟩ := hv
  have hPkv : IsKV m (piC m T (famV m T fun _ f _ => res f A)) := by unfold piC; exact isKV_mkKV _
  rw [res_id hPkv, El_piC, res_id hT, res_id (isKV_famV _ _)] at hp
  have hpkv : IsKV m p := (mem_piEl.1 hp).1
  rw [fstV_pairV hpkv]; exact hp

theorem eqFun_mem {T A v x : V} (hT : IsKV m T) (hA : IsKV m A) (hv : v ∈ El (equivCode m T A) (Hom.id m))
    (hx : x ∈ El T (Hom.id m)) : eqFun m v x ∈ El A (Hom.id m) := by
  have := appV_mem_piElSet (equiv_fst hT hv) hx
  rwa [apZ_dat_famV _ _ _ hx, res_id hA] at this

theorem eqFun_res {T A v x : V} (hT : IsKV m T) (hv : v ∈ El (equivCode m T A) (Hom.id m))
    (hx : x ∈ El T (Hom.id m)) (h : Hom k m) :
    res h (eqFun m v x) = appV k (res h (fstV m v)) (res h x) :=
  res_appV (equiv_fst hT hv) hx h

theorem res_glueV (φ : Cof m) (tp a : V) (g : Hom k m) :
    res g (glueV m φ tp a) = glueV k (φ.restr g) (res g tp) (res g a) := by
  simp only [glueV, res_mkKV, dat_mkKV, Cof.restr_restr, dat_res, res_res]

theorem unglue_glueV {φ : Cof m} (hn : ¬ φ.holds) (hφ : φ.IsCof) (tp : V) {a : V} (ha : IsKV m a) :
    π2 (π2 (here m (glueV m φ tp a))) = a := by
  simp only [here, glueV, dat_mkKV, hφ.restr_id, if_neg hn, tagZ, π2_pair, res_id ha]

theorem res_glueV_holds {φ : Cof m} (hφ : φ.IsCof) {tp a : V} {g : Hom k m} (hg : (φ.restr g).holds)
    (hcoh : ∀ n (h : Hom n k), res h (dat tp k g) = dat tp n (g.comp h)) (hkv : IsKV k (dat tp k g)) :
    res g (glueV m φ tp a) = dat tp k g := by
  refine (isKV_res _ _).ext hkv fun n h => ?_
  have hgh : (φ.restr (g.comp h)).holds := by rw [← Cof.restr_restr]; exact (hφ.restr g).holds_restr hg h
  rw [dat_res, glueV, dat_mkKV, if_pos hgh, ← hcoh n h, here_res]

theorem El_glueC_id {A : V} {φ : Cof m} {Tp ep : V} (hn : ¬ φ.holds) (hφ : φ.IsCof) (hA : IsKV m A)
    (hTp : IsKV m Tp) (hep : IsKV m ep) :
    El (glueC m A φ Tp ep) (Hom.id m) = glueElSet m A φ Tp ep := by
  simp only [El, glueC, dat_mkKV, hφ.restr_id, if_neg hn, glueDatum, π1π2_quad, res_id hA, res_id hTp,
    res_id hep]

theorem isKV_partialKV (φ : Cof m) (F : (k : ℕ) → Hom k m → V) : IsKV m (partialKV m φ F) := by
  unfold partialKV; exact isKV_mkKV _

theorem mem_glueElSet {A : V} {φ : Cof k} {Tp ep v : V} :
    v ∈ glueElSet k A φ Tp ep ↔ ∃ tp a, v = glueV k φ tp a ∧ a ∈ El A (Hom.id k) ∧
      tp = partialKV k φ (fun n g => dat tp n g) ∧
      (∀ n (g : Hom n k), (φ.restr g).holds → dat tp n g ∈ El (dat Tp n g) (Hom.id n)) ∧
      (∀ n (g : Hom n k), (φ.restr g).holds → ∀ n' (h : Hom n' n), res h (dat tp n g) = dat tp n' (g.comp h)) ∧
      (∀ n (g : Hom n k), (φ.restr g).holds → eqFun n (dat ep n g) (dat tp n g) = res g a) := by
  rw [glueElSet, ZFSet.mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨tp, a, rfl, ha, htp, htm, -, -⟩ := h
  refine ZFSet.mem_range.2 ⟨⟨fun y => ⟨if (φ.restr y.2).holds then dat tp y.1 y.2 else ∅, ?_⟩, ⟨a, ha⟩⟩, ?_⟩
  · split
    · exact ZFSet.mem_insert_of_mem _ (htm _ _ ‹_›)
    · exact ZFSet.mem_insert _ _
  · dsimp only
    congr 1
    conv_rhs => rw [htp]
    unfold partialKV; congr 2; funext n g; by_cases hg : (φ.restr g).holds <;> simp [hg]

theorem res_partialKV (φ : Cof m) (F : (k : ℕ) → Hom k m → V) (g : Hom k m) :
    res g (partialKV m φ F) = partialKV k (φ.restr g) (fun n h => F n (g.comp h)) := by
  simp only [partialKV, res_mkKV, Cof.restr_restr]

theorem equiv_pair {T A v : V} (hT : IsKV m T) (hv : v ∈ El (equivCode m T A) (Hom.id m)) :
    ∃ p q, IsKV m p ∧ v = pairV m p q := by
  obtain ⟨Q, hQ⟩ := equivCode_eq (A := A) hT
  rw [hQ, El_sigmaC, sigmaElSet, mem_sigmaEl] at hv
  obtain ⟨p, hp, q, -, rfl⟩ := hv
  have hPkv : IsKV m (piC m T (famV m T fun _ f _ => res f A)) := by unfold piC; exact isKV_mkKV _
  rw [res_id hPkv, El_piC] at hp
  exact ⟨p, q, (mem_piEl.1 hp).1, rfl⟩

theorem fstV_res_pairV {p q : V} (f : Hom k m) : fstV k (res f (pairV m p q)) = res f p := by
  rw [fstV_res]; simp [pairV]

theorem eqFun_res' {T A v x : V} (hT : IsKV m T) (hv : v ∈ El (equivCode m T A) (Hom.id m))
    (hx : x ∈ El T (Hom.id m)) (f : Hom k m) :
    res f (eqFun m v x) = eqFun k (res f v) (res f x) := by
  rw [eqFun_res hT hv hx f, eqFun]
  obtain ⟨p, q, hp, rfl⟩ := equiv_pair hT hv
  rw [fstV_res_pairV, fstV_pairV hp]

theorem here_empty : here m (∅ : V) = ∅ := dat_empty' _

theorem ungAt_empty (φ : Cof m) (e : V) : ungAt m φ e ∅ = ∅ := by
  unfold ungAt
  split
  · rw [if_neg (not_isKV_empty)]
  · rw [here_empty, π2_empty, π2_empty]

theorem glueC_shape {A : V} {φ : Cof m} {Tp ep : V} (hn : ¬ φ.holds) (hφ : φ.IsCof) :
    shapeOf (glueC m A φ Tp ep) (Hom.id m) =
      tagZ tGlue (ZFSet.pair (res (Hom.id m) A) (ZFSet.pair (enc φ) (ZFSet.pair (res (Hom.id m) Tp)
        (res (Hom.id m) ep)))) := by
  unfold glueC
  rw [shapeOf_mkKV, hφ.restr_id, if_neg hn]
  simp [glueDatum]

theorem El_glueC_id' {A : V} {φ : Cof m} {Tp ep : V} (hn : ¬ φ.holds) (hφ : φ.IsCof)
    (hTp : IsKV m Tp) (hep : IsKV m ep) :
    El (glueC m A φ Tp ep) (Hom.id m) = glueElSet m (Model.res (Hom.id m) A) φ Tp ep := by
  simp only [El, glueC, dat_mkKV, hφ.restr_id, if_neg hn, glueDatum, π1π2_quad, res_id hTp, res_id hep]

@[simp] theorem dat_partialKV (φ : Cof m) (F : (k : ℕ) → Hom k m → V) (f : Hom k m) :
    dat (partialKV m φ F) k f = if (φ.restr f).holds then F k f else ∅ := by
  simp [partialKV]

theorem res_partialKV_self {φ : Cof m} {X : V} (hX : X = partialKV m φ (fun k f => dat X k f))
    (h : Hom k m) : res h X = partialKV k (φ.restr h) (fun n g => dat (res h X) n g) := by
  conv_lhs => rw [hX]
  simp only [partialKV, res_mkKV, dat_res, Cof.restr_restr]

/-- Restriction of a Glue code: it reduces to `T` where `φ` holds. -/
theorem res_glueC {A : V} {φ : Cof m} {Tp ep : V}
    (hTp : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h))
    (hTkv : ∀ k (f : Hom k m), (φ.restr f).holds → IsKV k (dat Tp k f))
    (hφ : φ.IsCof) (h : Hom k m) :
    res h (glueC m A φ Tp ep) =
      if (φ.restr h).holds then dat Tp k h else glueC k (res h A) (φ.restr h) (res h Tp) (res h ep) := by
  split
  · rename_i hh
    refine (isKV_res _ _).ext (hTkv k h hh) fun n g => ?_
    have hg : (φ.restr (h.comp g)).holds := by
      rw [← Cof.restr_restr]; exact (hφ.restr h).holds_restr hh g
    rw [dat_res, glueC, dat_mkKV, if_pos hg, ← hTp k h hh n g, here_res]
  · rename_i hh
    refine (isKV_res _ _).ext (isKV_glueC _ _ _ _) fun n g => ?_
    simp only [dat_res, glueC, dat_mkKV, Cof.restr_restr, res_res]

end

end Model
