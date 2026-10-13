import Model.GlueElem

/-!
# Glue types are fibrant: `hcomp`

The Kan composition of Glue types is the spec's `Tm.hcompGlue` (`glueHcF`). Here we show that
it is typed, satisfies the face condition and is natural. On the face `φ` the Glue code *is* `T`
(its data are those of `T`), so only the stages where `φ` fails need work.
-/

set_option autoImplicit false

namespace Model

open ZFSet KubusCore

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k m n n' : ℕ}

theorem TubeOK.of_res {c : V} {f : Hom k m} {g : Hom n k} {φ : Cof n} {u : Tube n} {u0 : V}
    (hu : TubeOK (res f c) g φ u u0) : TubeOK c (f.comp g) φ u u0 where
  mem n' h r hh := by have := hu.mem n' h r hh; rwa [El_res, ← Hom.comp_assoc] at this
  coh := hu.coh
  base := hu.base

theorem TubeOK.to_res {c : V} {f : Hom k m} {g : Hom n k} {φ : Cof n} {u : Tube n} {u0 : V}
    (hu : TubeOK c (f.comp g) φ u u0) : TubeOK (res f c) g φ u u0 where
  mem n' h r hh := by rw [El_res, ← Hom.comp_assoc]; exact hu.mem n' h r hh
  coh := hu.coh
  base := hu.base

theorem ConstOn.of_res {c : V} {f : Hom k m} {g : Hom (n + 1) k} {φ : Cof n} (h : ConstOn (res f c) g φ) :
    ConstOn c (f.comp g) φ := by
  intro n' h' hh r
  have := h n' h' hh r
  rwa [res_res, res_res, ← Hom.comp_assoc, ← Hom.comp_assoc] at this

/-- Restrictions of fibrant codes are fibrant. -/
theorem Fib.restr {c : V} (hc : Fib c m) (f : Hom k m) : Fib (res f c) k where
  kv := isKV_res _ _
  elKV n g v hv := by rw [El_res] at hv; exact hc.elKV _ _ _ hv
  elRes n g v hv n' h := by rw [El_res] at hv ⊢; rw [← Hom.comp_assoc]; exact hc.elRes _ _ _ hv n' h
  hcMem n g ψ u u0 hψ hu0 hu := by
    rw [El_res] at hu0 ⊢; rw [hcompAt_eq_res_id, res_res, ← hcompAt_eq_res_id]
    exact hc.hcMem n _ ψ u u0 hψ hu0 hu.of_res
  hcFace n g ψ u u0 hψ hu0 hu hh := by
    rw [El_res] at hu0; rw [hcompAt_eq_res_id, res_res, ← hcompAt_eq_res_id]
    exact hc.hcFace n _ ψ u u0 hψ hu0 hu.of_res hh
  hcRes n g ψ u u0 hψ hu0 hu n' h := by
    rw [El_res] at hu0
    rw [hcompAt_eq_res_id, res_res, ← hcompAt_eq_res_id, hc.hcRes n _ ψ u u0 hψ hu0 hu.of_res n' h,
      hcompAt_eq_res_id, hcompAt_eq_res_id (res f c), res_res, Hom.comp_assoc]
  trMem n g ψ a0 hψ hcon ha := by
    rw [El_res] at ha ⊢; rw [transpAt_res]
    rw [← Hom.comp_assoc] at ha ⊢
    exact hc.trMem n _ ψ a0 hψ hcon.of_res ha
  trFace n g ψ a0 hψ hcon ha hh := by
    rw [El_res, ← Hom.comp_assoc] at ha; rw [transpAt_res]
    exact hc.trFace n _ ψ a0 hψ hcon.of_res ha hh
  trRes n g ψ a0 hψ hcon ha n' h := by
    rw [El_res, ← Hom.comp_assoc] at ha
    rw [transpAt_res, transpAt_res, hc.trRes n _ ψ a0 hψ hcon.of_res ha n' h, Hom.comp_assoc]

/-- The hypotheses on the components of a Glue code (those of `WFI.glue`, with fibrancy). -/
structure GlueOK (A : V) (φ : Cof m) (Tp ep : V) : Prop where
  fibA : Fib A m
  cof : φ.IsCof
  hTp : Tp = partialKV m φ (fun k f => dat Tp k f)
  hep : ep = partialKV m φ (fun k f => dat ep k f)
  fibT : ∀ k (f : Hom k m), (φ.restr f).holds → Fib (dat Tp k f) k
  Tcoh : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat Tp k f) = dat Tp n (f.comp h)
  mem_e : ∀ k (f : Hom k m), (φ.restr f).holds → dat ep k f ∈ El (equivCode k (dat Tp k f) (res f A)) (Hom.id k)
  ecoh : ∀ k (f : Hom k m), (φ.restr f).holds → ∀ n (h : Hom n k), res h (dat ep k f) = dat ep n (f.comp h)

namespace GlueOK

variable {A : V} {φ : Cof m} {Tp ep : V} (hG : GlueOK A φ Tp ep)
include hG

theorem TpKV : IsKV m Tp := by rw [hG.hTp]; exact isKV_partialKV _ _
theorem epKV : IsKV m ep := by rw [hG.hep]; exact isKV_partialKV _ _

theorem restr (h : Hom k m) : GlueOK (res h A) (φ.restr h) (res h Tp) (res h ep) where
  fibA := hG.fibA.restr h
  cof := hG.cof.restr h
  hTp := res_partialKV_self hG.hTp h
  hep := res_partialKV_self hG.hep h
  fibT n g hg := by rw [Cof.restr_restr] at hg; rw [dat_res]; exact hG.fibT n _ hg
  Tcoh n g hg n' g' := by rw [Cof.restr_restr] at hg; rw [dat_res, dat_res, hG.Tcoh n _ hg n' g', Hom.comp_assoc]
  mem_e n g hg := by rw [Cof.restr_restr] at hg; rw [dat_res, dat_res, res_res]; exact hG.mem_e n _ hg
  ecoh n g hg n' g' := by rw [Cof.restr_restr] at hg; rw [dat_res, dat_res, hG.ecoh n _ hg n' g', Hom.comp_assoc]

end GlueOK

/-! ### The data of a Glue code -/

theorem El_glueC (A : V) (φ : Cof m) (Tp ep : V) (f : Hom k m) :
    El (glueC m A φ Tp ep) f = if (φ.restr f).holds then El (dat Tp k f) (Hom.id k)
      else glueElSet k (res f A) (φ.restr f) (res f Tp) (res f ep) := by
  simp only [El, glueC, dat_mkKV]; split
  · rfl
  · simp [glueDatum]

theorem hcG_glueC (A : V) (φ : Cof m) (Tp ep : V) (f : Hom k m) :
    hcG (glueC m A φ Tp ep) f = if (φ.restr f).holds then hcG (dat Tp k f) (Hom.id k)
      else glueHc k (res f A) (φ.restr f) (res f Tp) (res f ep) := by
  simp only [hcG, glueC, dat_mkKV]; split
  · rfl
  · simp [glueDatum]

theorem trG_glueC (A : V) (φ : Cof m) (Tp ep : V) (f : Hom (k + 1) m) :
    trG (glueC m A φ Tp ep) f = if (φ.restr f).holds then trG (dat Tp (k + 1) f) (Hom.id (k + 1))
      else glueTr (k + 1) (res f A) (φ.restr f) (res f Tp) (res f ep) := by
  simp only [trG, glueC, dat_mkKV]; split
  · rfl
  · simp [glueDatum]

theorem hcompAt_glueC_holds {A : V} {φ : Cof m} {Tp ep : V} {f : Hom k m} (hf : (φ.restr f).holds)
    (ψ : Cof k) (u : Tube k) (u0 : V) :
    hcompAt (glueC m A φ Tp ep) f ψ u u0 = hcompAt (dat Tp k f) (Hom.id k) ψ u u0 := by
  simp only [hcompAt, hcG_glueC, if_pos hf]

theorem hcompAt_glueC_not {A : V} {φ : Cof m} {Tp ep : V} {f : Hom k m} (hf : ¬ (φ.restr f).holds)
    {ψ : Cof k} {u : Tube k} {u0 : V}
    (hu : ∀ n (h : Hom n k) r, (ψ.restr h).holds → u n h r ∈ El (glueC m A φ Tp ep) (f.comp h))
    (hu0 : u0 ∈ El (glueC m A φ Tp ep) f) :
    hcompAt (glueC m A φ Tp ep) f ψ u u0 =
      glueHcF k (res f A) (φ.restr f) (res f Tp) (res f ep) ψ (Tube.canon ψ u) u0 := by
  rw [hcompAt, hcG_glueC, if_neg hf, glueHc, apZ_hcGraph]
  · intro n h r hh
    have := hu n h r hh
    rw [El_glueC] at this
    simp only [Cof.restr_restr, dat_res, res_res]
    exact this
  · rw [El_glueC, if_neg hf] at hu0
    simp only [Cof.restr_restr, Hom.comp_id, if_neg hf, dat_res, res_res]
    exact hu0

/-! ### Elements and `unglue` -/

section elems

variable {A : V} {φ : Cof m} {Tp ep : V} (hG : GlueOK A φ Tp ep)
include hG

theorem GlueOK.elem {v : V} (hn : ¬ φ.holds) (hv : v ∈ glueElSet m A φ Tp ep) :
    ∃ tp a, v = glueV m φ tp a ∧ a ∈ El A (Hom.id m) ∧ IsKV m a ∧
      tp = partialKV m φ (fun n g => dat tp n g) ∧
      (∀ n (g : Hom n m), (φ.restr g).holds → dat tp n g ∈ El (dat Tp n g) (Hom.id n)) ∧
      (∀ n (g : Hom n m), (φ.restr g).holds → ∀ n' (h : Hom n' n), res h (dat tp n g) = dat tp n' (g.comp h)) ∧
      (∀ n (g : Hom n m), (φ.restr g).holds → eqFun n (dat ep n g) (dat tp n g) = res g a) := by
  rw [mem_glueElSet] at hv
  obtain ⟨tp, a, h1, ha, h2, h3, h4, h5⟩ := hv
  exact ⟨tp, a, h1, ha, hG.fibA.elKV _ _ _ ha, h2, h3, h4, h5⟩

theorem GlueOK.face_kv {tp : V} {n : ℕ} {g : Hom n m} (hg : (φ.restr g).holds)
    (hcoh : ∀ n' (h : Hom n' n), res h (dat tp n g) = dat tp n' (g.comp h)) : IsKV n (dat tp n g) := by
  have := hcoh n (Hom.id n); rw [Hom.comp_id] at this; rw [← this]; exact isKV_res _ _

/-- Elements of a Glue code are Kripke values. -/
theorem GlueOK.elKV {f : Hom k m} {v : V} (hv : v ∈ El (glueC m A φ Tp ep) f) : IsKV k v := by
  rw [El_glueC] at hv
  split at hv
  · exact (hG.fibT k f ‹_›).elKV _ _ _ hv
  · rw [mem_glueElSet] at hv
    obtain ⟨tp, a, rfl, -⟩ := hv
    unfold glueV; exact isKV_mkKV _

/-- `unglue` is typed. -/
theorem GlueOK.ung_mem {f : Hom k m} {v : V} (hv : v ∈ El (glueC m A φ Tp ep) f) :
    ungAt k (φ.restr f) (dat ep k f) v ∈ El A f := by
  rw [El_glueC] at hv
  unfold ungAt
  split
  · rename_i hf
    rw [if_pos hf] at hv
    rw [if_pos ((hG.fibT k f hf).elKV _ _ _ hv)]
    have := eqFun_mem (hG.fibT k f hf).kv (isKV_res f A) (hG.mem_e k f hf) hv
    rwa [El_res, Hom.comp_id] at this
  · rename_i hf
    rw [if_neg hf] at hv
    obtain ⟨tp, a, rfl, ha, hakv, -⟩ := (hG.restr f).elem hf hv
    rw [unglue_glueV hf (hG.cof.restr f) tp hakv]
    rwa [El_res, Hom.comp_id] at ha

/-- `unglue` is natural. -/
theorem GlueOK.ung_res {f : Hom k m} {v : V} (hv : v ∈ El (glueC m A φ Tp ep) f) (h : Hom n k) :
    res h (ungAt k (φ.restr f) (dat ep k f) v) = ungAt n (φ.restr (f.comp h)) (dat ep n (f.comp h)) (res h v) := by
  have hvkv := hG.elKV hv
  rw [El_glueC] at hv
  by_cases hf : (φ.restr f).holds
  · rw [if_pos hf] at hv
    have hfh : (φ.restr (f.comp h)).holds := by rw [← Cof.restr_restr]; exact (hG.cof.restr f).holds_restr hf h
    rw [ungAt, ungAt, if_pos hf, if_pos hfh, if_pos hvkv, if_pos (isKV_res _ _),
      eqFun_res' (hG.fibT k f hf).kv (hG.mem_e k f hf) hv h, hG.ecoh k f hf n h]
  · rw [if_neg hf] at hv
    obtain ⟨tp, a, rfl, ha, hakv, -, -, hcoh, heq⟩ := (hG.restr f).elem hf hv
    rw [ungAt, if_neg hf, unglue_glueV hf (hG.cof.restr f) tp hakv]
    by_cases hfh : (φ.restr (f.comp h)).holds
    · have hfh' : ((φ.restr f).restr h).holds := by rw [Cof.restr_restr]; exact hfh
      rw [res_glueV_holds (hG.cof.restr f) hfh' (hcoh n h hfh')
        ((hG.restr f).face_kv hfh' (hcoh n h hfh')), ungAt, if_pos hfh,
        if_pos ((hG.restr f).face_kv hfh' (hcoh n h hfh')), ← heq n h hfh', dat_res]
    · have hfh' : ¬ ((φ.restr f).restr h).holds := by rw [Cof.restr_restr]; exact hfh
      rw [res_glueV, ungAt, if_neg hfh, unglue_glueV hfh' ((hG.cof.restr f).restr h) _ (isKV_res _ _)]

end elems

theorem GlueOK.elRes {A : V} {φ : Cof m} {Tp ep : V} (hG : GlueOK A φ Tp ep) {f : Hom k m} {v : V}
    (hv : v ∈ El (glueC m A φ Tp ep) f) (h : Hom n k) : res h v ∈ El (glueC m A φ Tp ep) (f.comp h) := by
  rw [El_glueC] at hv ⊢
  by_cases hf : (φ.restr f).holds
  · have hfh : (φ.restr (f.comp h)).holds := by rw [← Cof.restr_restr]; exact (hG.cof.restr f).holds_restr hf h
    rw [if_pos hf] at hv; rw [if_pos hfh, ← hG.Tcoh k f hf n h, El_res, Hom.comp_id]
    have := (hG.fibT k f hf).elRes _ _ _ hv n h; rwa [Hom.id_comp] at this
  · rw [if_neg hf] at hv
    obtain ⟨tp, a, rfl, ha, hakv, htp, htm, hcoh, heq⟩ := (hG.restr f).elem hf hv
    by_cases hfh : (φ.restr (f.comp h)).holds
    · have hfh' : ((φ.restr f).restr h).holds := by rw [Cof.restr_restr]; exact hfh
      rw [if_pos hfh, res_glueV_holds (hG.cof.restr f) hfh' (hcoh n h hfh') ((hG.restr f).face_kv hfh' (hcoh n h hfh'))]
      have := htm n h hfh'; rwa [dat_res] at this
    · rw [if_neg hfh, res_glueV, mem_glueElSet, Cof.restr_restr]
      have hfh' : ∀ {n'} {g : Hom n' n}, ((φ.restr (f.comp h)).restr g).holds → ((φ.restr f).restr (h.comp g)).holds :=
        fun hg => by rw [Cof.restr_restr] at hg ⊢; exact hg
      refine ⟨res h tp, res h a, rfl, ?_, by have := res_partialKV_self htp h; rwa [Cof.restr_restr] at this,
        fun n' g hg => ?_, fun n' g hg n'' g' => ?_, fun n' g hg => ?_⟩
      · rw [El_res, Hom.comp_id] at ha ⊢
        exact hG.fibA.elRes _ _ _ ha n h
      · have := htm n' (h.comp g) (hfh' hg)
        simp only [dat_res] at this ⊢; exact this
      · simp only [dat_res]; rw [hcoh n' (h.comp g) (hfh' hg) n'' g']; rfl
      · have := heq n' (h.comp g) (hfh' hg)
        simp only [dat_res] at this ⊢; rw [res_res]; exact this

/-! ### `hcomp` at a stage where the face fails -/

/-- The `T`-component of `hcompGlue`. -/
def glueTp (m : ℕ) (φ : Cof m) (Tp : V) (ψ : Cof m) (u : Tube m) (u0 : V) : V :=
  partialKV m φ fun n g => hcompAt (dat Tp n g) (Hom.id n) (ψ.restr g) (u.restr g) (res g u0)

/-- The tube `[ψ ↦ unglue u, φ ↦ e.1 (hfill T [ψ ↦ u] u0)]` of `hcompGlue`. -/
def glueTube (m : ℕ) (φ : Cof m) (Tp ep : V) (ψ : Cof m) (u : Tube m) (u0 : V) : Tube m := fun n h r =>
  if (ψ.restr h).holds then ungAt n (φ.restr h) (dat ep n h) (u n h r)
  else if (φ.restr h).holds then
    eqFun n (dat ep n h) (res (Hom.endpt n r) (hfillF (dat Tp n h) (Hom.id n) (ψ.restr h) (u.restr h) (res h u0)))
  else ∅

theorem glueHcF_eq (A : V) (φ : Cof m) (Tp ep : V) (ψ : Cof m) (u : Tube m) (u0 : V) :
    glueHcF m A φ Tp ep ψ u u0 = glueV m φ (glueTp m φ Tp ψ u u0)
      (hcompAt A (Hom.id m) (Cof.or ψ φ) (glueTube m φ Tp ep ψ u u0) (π2 (π2 (here m u0)))) := rfl

section hcomp

variable {A : V} {φ : Cof m} {Tp ep : V} (hG : GlueOK A φ Tp ep) (hn : ¬ φ.holds) {ψ : Cof m}
  (hψ : ψ.IsCof) {u : Tube m} {u0 : V} (hu0 : u0 ∈ El (glueC m A φ Tp ep) (Hom.id m))
  (hu : TubeOK (glueC m A φ Tp ep) (Hom.id m) ψ u u0)

include hG hu0 hu in
/-- The `T`-part of the tube, at a point of the face `φ`. -/
theorem glue_Ttube {n : ℕ} {g : Hom n m} (hg : (φ.restr g).holds) :
    res g u0 ∈ El (dat Tp n g) (Hom.id n) ∧ TubeOK (dat Tp n g) (Hom.id n) (ψ.restr g) (u.restr g) (res g u0) := by
  have h0 := hG.elRes hu0 g
  rw [El_glueC, Hom.id_comp, if_pos hg] at h0
  refine ⟨h0, fun n' h' r hh => ?_, fun n' h' r hh n'' g' => ?_, fun n' h' hh => ?_⟩
  · rw [Cof.restr_restr] at hh
    have hgh : (φ.restr (g.comp h')).holds := by rw [← Cof.restr_restr]; exact (hG.cof.restr g).holds_restr hg h'
    have := hu.mem n' (g.comp h') r hh
    rw [El_glueC, Hom.id_comp, if_pos hgh, ← hG.Tcoh n g hg n' h', El_res, Hom.comp_id] at this
    rw [Hom.id_comp]; exact this
  · rw [Cof.restr_restr] at hh; exact hu.coh n' (g.comp h') r hh n'' g'
  · rw [Cof.restr_restr] at hh; simp only [Tube.restr]; rw [hu.base n' (g.comp h') hh, res_res]

include hG hψ hu0 hu in
theorem glueTp_mem {n : ℕ} {g : Hom n m} (hg : (φ.restr g).holds) :
    hcompAt (dat Tp n g) (Hom.id n) (ψ.restr g) (u.restr g) (res g u0) ∈ El (dat Tp n g) (Hom.id n) := by
  obtain ⟨h0, hT⟩ := glue_Ttube hG hu0 hu hg
  exact (hG.fibT n g hg).hcMem n _ _ _ _ (hψ.restr g) h0 hT

include hG hψ hu0 hu in
theorem glueTp_coh {n : ℕ} {g : Hom n m} (hg : (φ.restr g).holds) (n' : ℕ) (h : Hom n' n) :
    res h (hcompAt (dat Tp n g) (Hom.id n) (ψ.restr g) (u.restr g) (res g u0)) =
      hcompAt (dat Tp n' (g.comp h)) (Hom.id n') (ψ.restr (g.comp h)) (u.restr (g.comp h)) (res (g.comp h) u0) := by
  obtain ⟨h0, hT⟩ := glue_Ttube hG hu0 hu hg
  rw [(hG.fibT n g hg).hcRes n _ _ _ _ (hψ.restr g) h0 hT n' h, Hom.id_comp, hcompAt_eq_res_id,
    hG.Tcoh n g hg n' h, Cof.restr_restr, res_res]
  rfl

end hcomp

section hcomp2

variable {A : V} {φ : Cof m} {Tp ep : V} (hG : GlueOK A φ Tp ep) (hn : ¬ φ.holds) {ψ : Cof m}
  (hψ : ψ.IsCof) {u : Tube m} {u0 : V} (hu0 : u0 ∈ El (glueC m A φ Tp ep) (Hom.id m))
  (hu : TubeOK (glueC m A φ Tp ep) (Hom.id m) ψ u u0)

include hG hn in
theorem glue_a0 : π2 (π2 (here m u0)) = ungAt m (φ.restr (Hom.id m)) (dat ep m (Hom.id m)) u0 := by
  rw [hG.cof.restr_id, ungAt, if_neg hn]

include hG hn hu0 in
theorem glue_a0_mem : π2 (π2 (here m u0)) ∈ El A (Hom.id m) := by
  rw [glue_a0 hG hn]; exact hG.ung_mem hu0

include hG hψ hu0 hu in
theorem glue_hfill_mem {n : ℕ} {h : Hom n m} (hh : (φ.restr h).holds) (r : DM n) :
    res (Hom.endpt n r) (hfillF (dat Tp n h) (Hom.id n) (ψ.restr h) (u.restr h) (res h u0)) ∈
      El (dat Tp n h) (Hom.id n) := by
  obtain ⟨h0, hT⟩ := glue_Ttube hG hu0 hu hh
  have hfib := hG.fibT n h hh
  have := hfib.elRes _ _ _ (hfillF_mem hfib (hψ.restr h) h0 hT) n (Hom.endpt n r)
  rwa [Hom.id_comp, Hom.wk_comp_endpt] at this

include hG hn hψ hu0 hu in
theorem glueTube_ok :
    TubeOK A (Hom.id m) (Cof.or ψ φ) (glueTube m φ Tp ep ψ u u0) (π2 (π2 (here m u0))) where
  mem n h r hh := by
    unfold glueTube
    split
    · have := hG.ung_mem (hu.mem n h r ‹_›); rwa [Hom.id_comp] at this ⊢
    · rename_i h1
      rw [Cof.or_restr, Cof.holds_or] at hh
      have hφh := hh.resolve_left h1
      rw [if_pos hφh, Hom.id_comp]
      have := eqFun_mem (hG.fibT n h hφh).kv (isKV_res h A) (hG.mem_e n h hφh) (glue_hfill_mem hG hψ hu0 hu hφh r)
      rwa [El_res, Hom.comp_id] at this
  coh n h r hh n' g := by
    have hghl : ∀ {X : Cof m}, (X.restr h).holds → X.IsCof → (X.restr (h.comp g)).holds := fun hX hXc => by
      rw [← Cof.restr_restr]; exact (hXc.restr h).holds_restr hX g
    unfold glueTube
    by_cases h1 : (ψ.restr h).holds
    · rw [if_pos h1, if_pos (hghl h1 hψ)]
      have hm := hu.mem n h r h1; rw [Hom.id_comp] at hm
      rw [hG.ung_res hm g, hu.coh n h r h1 n' g]
    · rw [if_neg h1]
      rw [Cof.or_restr, Cof.holds_or] at hh
      have hφh := hh.resolve_left h1
      have hφhg := hghl hφh hG.cof
      rw [if_pos hφh]
      obtain ⟨h0, hT⟩ := glue_Ttube hG hu0 hu hφh
      have hfib := hG.fibT n h hφh
      have hX := glue_hfill_mem hG hψ hu0 hu hφh r
      rw [eqFun_res' hfib.kv (hG.mem_e n h hφh) hX g, hG.ecoh n h hφh n' g, res_res, Hom.endpt_comp,
        ← res_res]
      by_cases h2 : (ψ.restr (h.comp g)).holds
      · rw [if_pos h2]
        have h2' : ((ψ.restr h).restr g).holds := by rw [Cof.restr_restr]; exact h2
        rw [res_res, Hom.lift_comp_endpt', hfillF_face hfib (hψ.restr h) h0 hT g h2' (r.restr g)]
        have hm := hu.mem n' (h.comp g) (r.restr g) h2; rw [Hom.id_comp] at hm
        have hkv := hG.elKV hm
        rw [ungAt, if_pos hφhg, if_pos hkv]; rfl
      · rw [if_neg h2, if_pos hφhg, hfillF_natural hfib (hψ.restr h) h0 hT g, ← hfillF_res_id, Hom.id_comp,
          hG.Tcoh n h hφh n' g, Cof.restr_restr, res_res]
        rfl
  base n h hh := by
    unfold glueTube
    have hu0h := hG.elRes hu0 h
    rw [Hom.id_comp] at hu0h
    rw [glue_a0 hG hn, hG.ung_res hu0 h, Hom.id_comp]
    split
    · rw [hu.base n h ‹_›]
    · rename_i h1
      rw [Cof.or_restr, Cof.holds_or] at hh
      have hφh := hh.resolve_left h1
      obtain ⟨h0, hT⟩ := glue_Ttube hG hu0 hu hφh
      have hfib := hG.fibT n h hφh
      rw [if_pos hφh, hfillF_endpt0 hfib (hψ.restr h) h0 hT, ungAt, if_pos hφh, if_pos (hG.elKV hu0h)]

end hcomp2

section hcomp3

variable {A : V} {φ : Cof m} {Tp ep : V} (hG : GlueOK A φ Tp ep) (hn : ¬ φ.holds) {ψ : Cof m}
  (hψ : ψ.IsCof) {u : Tube m} {u0 : V} (hu0 : u0 ∈ El (glueC m A φ Tp ep) (Hom.id m))
  (hu : TubeOK (glueC m A φ Tp ep) (Hom.id m) ψ u u0)

include hG hn hψ hu0 hu in
theorem glueHc_eqFun {n : ℕ} {g : Hom n m} (hg : (φ.restr g).holds) :
    eqFun n (dat ep n g) (hcompAt (dat Tp n g) (Hom.id n) (ψ.restr g) (u.restr g) (res g u0)) =
      res g (hcompAt A (Hom.id m) (Cof.or ψ φ) (glueTube m φ Tp ep ψ u u0) (π2 (π2 (here m u0)))) := by
  have hT := glueTube_ok hG hn hψ hu0 hu
  have ha0 := glue_a0_mem hG hn hu0
  have hFg : ((Cof.or ψ φ).restr g).holds := by rw [Cof.or_restr, Cof.holds_or]; exact Or.inr hg
  rw [hG.fibA.hcRes m _ _ _ _ (hψ.or hG.cof) ha0 hT n g,
    hG.fibA.hcFace n _ _ _ _ ((hψ.or hG.cof).restr g) (hG.fibA.elRes _ _ _ ha0 n g) (hT.restr g) hFg]
  simp only [Tube.restr, Hom.comp_id, glueTube]
  obtain ⟨h0, hTT⟩ := glue_Ttube hG hu0 hu hg
  have hfib := hG.fibT n g hg
  split
  · rename_i h1
    have hid : ((ψ.restr g).restr (Hom.id n)).holds := by rw [(hψ.restr g).restr_id]; exact h1
    have hm := hu.mem n g (DM.one n) h1; rw [Hom.id_comp] at hm
    rw [hfib.hcFace n _ _ _ _ (hψ.restr g) h0 hTT h1, ungAt, if_pos hg, if_pos (hG.elKV hm)]
    simp only [Tube.restr, Hom.comp_id]
  · rw [hfillF_endpt1 hfib (hψ.restr g) h0 hTT]

include hG hn hψ hu0 hu in
/-- `hcompGlue` is typed. -/
theorem glueHcF_mem : glueHcF m A φ Tp ep ψ u u0 ∈ El (glueC m A φ Tp ep) (Hom.id m) := by
  rw [glueHcF_eq, El_glueC, hG.cof.restr_id, if_neg hn, res_id hG.fibA.kv, res_id hG.TpKV, res_id hG.epKV,
    mem_glueElSet]
  refine ⟨_, _, rfl, hG.fibA.hcMem m _ _ _ _ (hψ.or hG.cof) (glue_a0_mem hG hn hu0) (glueTube_ok hG hn hψ hu0 hu),
    partialKV_self _ _, fun n g hg => ?_, fun n g hg n' h => ?_, fun n g hg => ?_⟩
  · rw [glueTp, dat_partialKV, if_pos hg]; exact glueTp_mem hG hψ hu0 hu hg
  · have hgh : (φ.restr (g.comp h)).holds := by rw [← Cof.restr_restr]; exact (hG.cof.restr g).holds_restr hg h
    rw [glueTp, dat_partialKV, if_pos hg, dat_partialKV, if_pos hgh]; exact glueTp_coh hG hψ hu0 hu hg n' h
  · rw [glueTp, dat_partialKV, if_pos hg]; exact glueHc_eqFun hG hn hψ hu0 hu hg

include hG hn hψ hu0 hu in
/-- `hcompGlue` satisfies the face condition. -/
theorem glueHcF_face (hh : ψ.holds) : glueHcF m A φ Tp ep ψ u u0 = u m (Hom.id m) (DM.one m) := by
  have hid : (ψ.restr (Hom.id m)).holds := by rw [hψ.restr_id]; exact hh
  have hm := hu.mem m (Hom.id m) (DM.one m) hid
  rw [Hom.id_comp, El_glueC, hG.cof.restr_id, if_neg hn, res_id hG.fibA.kv, res_id hG.TpKV,
    res_id hG.epKV] at hm
  obtain ⟨tp1, a1, h1, -, ha1kv, htp1, -, hcoh1, -⟩ := hG.elem hn hm
  have hT := glueTube_ok hG hn hψ hu0 hu
  have hFh : (Cof.or ψ φ).holds := Cof.holds_or.2 (Or.inl hh)
  rw [glueHcF_eq, hG.fibA.hcFace m _ _ _ _ (hψ.or hG.cof) (glue_a0_mem hG hn hu0) hT hFh, h1]
  congr 1
  · rw [htp1]; unfold glueTp partialKV; congr 1; funext n g; split
    · rename_i hg
      have hψg : (ψ.restr g).holds := hψ.holds_restr hh g
      obtain ⟨h0, hTT⟩ := glue_Ttube hG hu0 hu hg
      dsimp only
      rw [(hG.fibT n g hg).hcFace n _ _ _ _ (hψ.restr g) h0 hTT hψg,
        ← res_glueV_holds hG.cof hg (hcoh1 n g hg) (hG.face_kv hg (hcoh1 n g hg)), ← h1,
        hu.coh m (Hom.id m) (DM.one m) hid n g]
      simp only [Tube.restr, Hom.comp_id, Hom.id_comp, DM.one_restr]
    · rfl
  · simp only [glueTube, if_pos hid]
    rw [h1, ungAt, hG.cof.restr_id, if_neg hn, unglue_glueV hn hG.cof tp1 ha1kv]

end hcomp3

end

end Model
