import Model.Whnf.Formers2

/-!
# Hereditary Kan at the components of a code
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore ZFSet Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {m k : ℕ}

/-- Every cube map has a scoped syntactic interval substitution. -/
def ISub.ofHom (f : Hom k m) : ISub k m :=
  ⟨tyOf f, fun i _ => tyOf_scoped f i, fun i hi => by
    simp only [tyOf, dif_neg (show ¬ i < m by omega)]⟩

theorem ISub.ofHom_hom (f : Hom k m) : (ISub.ofHom f).hom = f := by
  funext j
  change ival (idEnv k) (tyOf f (m - 1 - j)) = f j
  rw [ival_tyOf]
  apply DM.ext; funext p
  simp only [IEnv.restr, idEnv, dif_pos (show m - 1 - j.val < m by omega), DM.restr_fn, DM.var_fn, Hom.app]
  congr 2
  apply Fin.ext
  simp only [Fin.val_mk]; omega

variable (hW : WfSig S)
include hW

theorem KanP2.restrict {X : V} (hX : X ≠ ∅) (h : KanP2 S m X) (g : Hom k m) :
    KanP2 S k (res g X) :=
  (kanPG_iff hW).1 (((kanPG_iff hW).2 h).restrict hX g)

/-- The domain and the fibres at related arguments of a hereditary Kan Π-code. -/
theorem HerKan2.pi_parts {A B : V} (hA : IsKV m A) (h : HerKan2 S m (piC m A B)) :
    HerKan2 S m A ∧ ∀ k (f : Hom k m) A0 a a', (Comp2 S A m k f).el A0 a a' →
      HerKan2 S k (apZ (dat B k f) (semK S k a)) := by
  have hp := ((HerKan2_eq S _ _).1 h).2
  have parts : ∀ k (f : Hom k m), HerKan2 S k (res f A) ∧
      ∀ A0 a a', (Comp2 S A m k f).el A0 a a' → HerKan2 S k (apZ (dat B k f) (semK S k a)) := by
    intro k f
    have hh := hp k f
    rw [dif_pos (show piC m A B ≠ ∅ from mkKV_ne_empty _)] at hh
    simpa only [kanParts2, piC, dat_mkKV, piDatum, π1_quad, tagZ, π1_pair, π2_pair,
      Hom.comp_id, natZ_inj, true_or, if_true, Comp2_res (IsKV.ne_empty hA), appV, here,
      dat_res, Hom.comp_id] using hh
  exact ⟨by simpa only [res_id hA] using (parts m (Hom.id m)).1,
    fun k f A0 a a' ha => (parts k f).2 A0 a a' ha⟩

/-- The domain and the fibres at related arguments of a hereditary Kan Σ-code. -/
theorem HerKan2.sigma_parts {A B : V} (hA : IsKV m A) (h : HerKan2 S m (sigmaC m A B)) :
    HerKan2 S m A ∧ ∀ k (f : Hom k m) A0 a a', (Comp2 S A m k f).el A0 a a' →
      HerKan2 S k (apZ (dat B k f) (semK S k a)) := by
  have hp := ((HerKan2_eq S _ _).1 h).2
  have parts : ∀ k (f : Hom k m), HerKan2 S k (res f A) ∧
      ∀ A0 a a', (Comp2 S A m k f).el A0 a a' → HerKan2 S k (apZ (dat B k f) (semK S k a)) := by
    intro k f
    have hh := hp k f
    rw [dif_pos (show sigmaC m A B ≠ ∅ from mkKV_ne_empty _)] at hh
    simpa only [kanParts2, sigmaC, dat_mkKV, sigmaDatum, π1_quad, tagZ, π1_pair, π2_pair,
      Hom.comp_id, natZ_inj, or_true, if_true, tPi, tSigma, show ¬ (3 = 2) by decide, if_false, Comp2_res (IsKV.ne_empty hA), appV, here,
      dat_res, Hom.comp_id] using hh
  exact ⟨by simpa only [res_id hA] using (parts m (Hom.id m)).1,
    fun k f A0 a a' ha => (parts k f).2 A0 a a' ha⟩


/-- Construct hereditary Kan for a Π-code from its own Kan operations and its components. -/
theorem HerKan2.pi_of {A B : V} (hA : IsKV m A) (hK : KanP2 S m (piC m A B))
    (hKA : HerKan2 S m A)
    (hKB : ∀ k (f : Hom k m) A0 a a', (Comp2 S A m k f).el A0 a a' →
      HerKan2 S k (apZ (dat B k f) (semK S k a))) : HerKan2 S m (piC m A B) := by
  refine (HerKan2_eq S _ _).2 ⟨(kanPG_iff hW).2 hK, fun k f => ?_⟩
  rw [dif_pos (show piC m A B ≠ ∅ from mkKV_ne_empty _)]
  simpa only [kanParts2, piC, dat_mkKV, piDatum, π1_quad, tagZ, π1_pair, π2_pair,
    Hom.comp_id, natZ_inj, true_or, if_true, Comp2_res (IsKV.ne_empty hA), appV, here,
    dat_res, Hom.comp_id] using
    (show HerKan2 S k (res f A) ∧ ∀ A0 a a', (Comp2 S A m k f).el A0 a a' →
      HerKan2 S k (apZ (dat B k f) (semK S k a)) from
      ⟨hKA.restrict (IsKV.ne_empty hA) f, hKB k f⟩)

/-- Construct hereditary Kan for a Σ-code from its own Kan operations and its components. -/
theorem HerKan2.sigma_of {A B : V} (hA : IsKV m A) (hK : KanP2 S m (sigmaC m A B))
    (hKA : HerKan2 S m A)
    (hKB : ∀ k (f : Hom k m) A0 a a', (Comp2 S A m k f).el A0 a a' →
      HerKan2 S k (apZ (dat B k f) (semK S k a))) : HerKan2 S m (sigmaC m A B) := by
  refine (HerKan2_eq S _ _).2 ⟨(kanPG_iff hW).2 hK, fun k f => ?_⟩
  rw [dif_pos (show sigmaC m A B ≠ ∅ from mkKV_ne_empty _)]
  simpa only [kanParts2, sigmaC, dat_mkKV, sigmaDatum, π1_quad, tagZ, π1_pair, π2_pair,
    Hom.comp_id, natZ_inj, or_true, if_true, tPi, tSigma, show ¬ (3 = 2) by decide, if_false, Comp2_res (IsKV.ne_empty hA), appV, here,
    dat_res, Hom.comp_id] using
    (show HerKan2 S k (res f A) ∧ ∀ A0 a a', (Comp2 S A m k f).el A0 a a' →
      HerKan2 S k (apZ (dat B k f) (semK S k a)) from
      ⟨hKA.restrict (IsKV.ne_empty hA) f, hKB k f⟩)

/-- A hereditary Kan path code carries hereditary Kan of its line. -/
theorem HerKan2.path_parts {L a0 a1 : V} (hL : IsKV (m + 1) L) (h : HerKan2 S m (pathC m L a0 a1)) :
    HerKan2 S (m + 1) L := by
  have hp := ((HerKan2_eq S _ _).1 h).2 m (Hom.id m)
  rw [dif_pos (show pathC m L a0 a1 ≠ ∅ from mkKV_ne_empty _)] at hp
  simpa only [kanParts2, pathC, dat_mkKV, pathDatum, π1_quad, tagZ, π1_pair, π2_pair,
    Hom.comp_id, natZ_inj, tPi, tSigma, tPath, if_false, show ¬ (4 = 2) by decide,
    show ¬ (4 = 3) by decide, false_or, true_or, if_true, Hom.lift_id, res_id hL] using hp

/-- Construct hereditary Kan of a path code from its own Kan operations and its line. -/
theorem HerKan2.path_of {L a0 a1 : V} (hL : IsKV (m + 1) L) (hK : KanP2 S m (pathC m L a0 a1))
    (hKL : HerKan2 S (m + 1) L) : HerKan2 S m (pathC m L a0 a1) := by
  refine (HerKan2_eq S _ _).2 ⟨(kanPG_iff hW).2 hK, fun k f => ?_⟩
  rw [dif_pos (show pathC m L a0 a1 ≠ ∅ from mkKV_ne_empty _)]
  simpa only [kanParts2, pathC, dat_mkKV, pathDatum, π1_quad, tagZ, π1_pair, π2_pair,
    Hom.comp_id, natZ_inj, tPi, tSigma, tPath, if_false, show ¬ (4 = 2) by decide,
    show ¬ (4 = 3) by decide, false_or, true_or, if_true] using
    hKL.restrict (IsKV.ne_empty hL) (Hom.lift f)

/-- A hereditary Kan interval function code carries hereditary Kan of its line. -/
theorem HerKan2.ipi_parts {L : V} (hL : IsKV (m + 1) L) (h : HerKan2 S m (ipiC m L)) :
    HerKan2 S (m + 1) L := by
  have hp := ((HerKan2_eq S _ _).1 h).2 m (Hom.id m)
  rw [dif_pos (show ipiC m L ≠ ∅ from mkKV_ne_empty _)] at hp
  simpa only [kanParts2, ipiC, dat_mkKV, ipiDatum, π1_quad, tagZ, π1_pair, π2_pair,
    Hom.comp_id, natZ_inj, tPi, tSigma, tPath, tIPi, if_false, show ¬ (5 = 2) by decide,
    show ¬ (5 = 3) by decide, show ¬ (5 = 4) by decide, or_true, if_false, if_true, Hom.lift_id, res_id hL] using hp

/-- Construct hereditary Kan of a interval function code from its own Kan operations and its line. -/
theorem HerKan2.ipi_of {L : V} (hL : IsKV (m + 1) L) (hK : KanP2 S m (ipiC m L))
    (hKL : HerKan2 S (m + 1) L) : HerKan2 S m (ipiC m L) := by
  refine (HerKan2_eq S _ _).2 ⟨(kanPG_iff hW).2 hK, fun k f => ?_⟩
  rw [dif_pos (show ipiC m L ≠ ∅ from mkKV_ne_empty _)]
  simpa only [kanParts2, ipiC, dat_mkKV, ipiDatum, π1_quad, tagZ, π1_pair, π2_pair,
    Hom.comp_id, natZ_inj, tPi, tSigma, tPath, tIPi, if_false, show ¬ (5 = 2) by decide,
    show ¬ (5 = 3) by decide, show ¬ (5 = 4) by decide, or_true, if_false, if_true] using
    hKL.restrict (IsKV.ne_empty hL) (Hom.lift f)

end

end Model.Whnf
