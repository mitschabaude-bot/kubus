import Model.Whnf.Kan2Comp
import Model.Whnf.Valid2GlueEta

/-!
# Binary Kan lemma: composition in Glue types

Composition in a Glue type whose face does not hold computes to `hcompGlue`, a Glue introduction whose
fiber is a composition in the fiber type and whose base is a composition in the base type along a system
of the unglued tube and the equivalence applied to the fiber filler.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- Related types with Glue normal forms whose faces do not hold have related bases, and related fibers
and equivalences where the face holds. -/
theorem RT2_glueW_inv {X X' A T e A' T' e' : Tm} {φ φ' : I} {l l' : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hG' : HasTy S k .one [] (.glue A' φ' T' e') (.univ l'))
    (hn : ¬ I.Entails .one φ) (hn' : ¬ I.Entails .one φ') (h : RT2 S k X X')
    (hR : RedT S k X (.glue A φ T e)) (hR' : RedT S k X' (.glue A' φ' T' e')) :
    RT2 S k A A' ∧ ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RT2 S k' (T.isub σ) (T'.isub σ) ∧ RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ) := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hnh : ¬ (ival (idEnv k) φ).holds := fun hh => hn ((holds_iff_entails hφs).1 hh)
  have hnf : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hXK : IsTyK S k X := (show IsTyK S k (.glue A φ T e) from ⟨l, .inl hG⟩).of_tyEq (TyEq.symm hR.2)
  have hXK' : IsTyK S k X' := (show IsTyK S k (.glue A' φ' T' e') from ⟨l', .inl hG'⟩).of_tyEq (TyEq.symm hR'.2)
  unfold RT2 at h
  rw [semK_tyEq hW hR.2, semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hnf] at h
  obtain ⟨-, hloc, -, -⟩ := h
  have h0 := hloc k (ISub.id k)
  unfold glueLocT at h0
  rw [if_neg (by rw [Hom.id_comp, ISub.hom_id, (isCof_ival_face _ _).restr_id]; exact hnf)] at h0
  obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', r1, r2, -, -, -, -, hAA, hfib⟩ := h0
  rw [isub_id_of_closed (closed_of_isTyK hW hXK)] at r1
  rw [isub_id_of_closed (closed_of_isTyK hW hXK')] at r2
  have eq1 := RedW.unique r1.1 hR.1
  have eq2 := RedW.unique r2.1 hR'.1
  simp only [Tm.glue.injEq] at eq1 eq2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq2
  refine ⟨?_, fun k' σ hh => ?_⟩
  · rw [Hom.id_comp, ISub.hom_id] at hAA; exact hAA
  have hface : (Cof.restr (ival (idEnv k) φ1).face ((Hom.id k).comp ((ISub.id k).comp σ).hom)).holds := by
    rw [ISub.id_comp, Hom.id_comp]; exact (face_holds_iff hφs σ).2 hh
  obtain ⟨hT, hE⟩ := hfib k' σ hface
  rw [ISub.id_comp, Hom.id_comp, dat_glue_fiber σ ((face_holds_iff hφs σ).2 hh)] at hT hE
  obtain ⟨lT, hTσ, heσ⟩ := glue_fiber_ty hW hG σ hh
  refine ⟨hT, ?_⟩
  obtain ⟨lE, hE0⟩ := ty_of_tyEq hW (isTyK_of_ty hW heσ) (TyEq.refl _) (fun l h => by cases h)
  have gT : GoodP S k' (fun k3 σ3 => Comp2 S (semK S k' (T1.isub σ)) k' k3 σ3.hom) (T1.isub σ) :=
    goodP_comp hW hTσ
  have gA : GoodP S k' (fun k3 σ3 => Comp2 S (semK S k A1) k k3 (Hom.id k |>.comp (σ.comp σ3).hom))
      (A1.isub σ) := by
    intro k3 σ3 t t'
    show (Comp2 S (semK S k A1) k k3 ((Hom.id k).comp (σ.comp σ3).hom)).el _ t t' ↔ _
    rw [Hom.id_comp, Comp2_res_el hW hA0, Tm.isub_isub]; rfl
  refine (goodP_id hW (goodP_equivF hW hE0 gT gA) (closed_of_ty hW hE0) (e1.isub σ) (e1'.isub σ)).1 ?_
  convert hE using 3



/-- A type with a Glue normal form whose face does not hold is related to that normal form, which is
related to itself. -/
theorem RT2_glue_whnf {X A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hn : ¬ I.Entails .one φ) (hXX : RT2 S k X X) (hR : RedT S k X (.glue A φ T e)) :
    RT2 S k (.glue A φ T e) X ∧ RT2 S k (.glue A φ T e) (.glue A φ T e) := by
  obtain ⟨hφs, lA, hA0, -⟩ := glue_data hW hG
  have hnh : ¬ (ival (idEnv k) φ).holds := fun hh => hn ((holds_iff_entails hφs).1 hh)
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hinv := RT2_glueW_inv hW hG hG hn hn hXX hR hR
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hXT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → TyCode k' (semK S k' (T.isub σ)) :=
    fun k' σ hh => tyCode_of_univ hW (glue_fiber_ty hW hG σ hh).choose_spec.1
  have hGG : RT2 S k (.glue A φ T e) (.glue A φ T e) :=
    RT2_glue_intro hW hG hG (EqTm.refl hG) hnh (ent_refl _) (ent_refl _) (fun k' σ => RT2.isub hW hXA hinv.1 σ)
      (fun k' σ hh => (hinv.2 k' σ hh).1) (fun k' σ hh => (hinv.2 k' σ hh).2) (fun k' σ hh => (hinv.2 k' σ hh).2)
      (fun k' σ hh => (hinv.2 k' σ hh).2)
  refine ⟨?_, hGG⟩
  have hXK : IsTyK S k X := (show IsTyK S k (.glue A φ T e) from ⟨l, .inl hG⟩).of_tyEq (TyEq.symm hR.2)
  have hsem : semK S k X = semK S k (.glue A φ T e) := semK_tyEq hW hR.2
  have hGG' := hGG
  have hXX' := hXX
  unfold RT2 at hGG' hXX' ⊢
  rw [hsem] at hXX'
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
    at hGG' hXX' ⊢
  obtain ⟨⟨hGK, -, hsG, -, -⟩, -, cohG, -⟩ := hGG'
  obtain ⟨⟨-, -, hsX, -, -⟩, -, cohX, -⟩ := hXX'
  have hc := closed_of_isTyK hW hXK
  have hloc := cohX k (ISub.id k) (by
    rw [Hom.id_comp, ISub.hom_id, (isCof_ival_face _ _).restr_id]; exact hn') _ (by rw [isub_id_of_closed hc]; exact hR.1)
  refine ⟨⟨hGK, hXK, hsG, hsX, hR.2.symm⟩, fun k' σ => ?_, cohG, cohX⟩
  have := hloc k' σ
  rwa [ISub.id_comp] at this


/-- A related pair of a Glue type whose face holds is a related pair of its fiber. -/
theorem RE2_glue_fib {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hφe : I.Entails .one φ) (hTT : RT2 S k T T) {x y : Tm} (hxy : RE2 S k (.glue A φ T e) x y) :
    RE2 S k T x y := by
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  have hface := glue_face_tyEq hW hGK hφe
  have hTK : IsTyK S k T := hGK.of_tyEq hface
  have hX : TyCode k (semK S k T) := by have := RE2.tyCode hW hxy; rwa [semK_tyEq hW hface] at this
  have hTG : (Comp2 S (semK S k T) k k (Hom.id k)).ty T (.glue A φ T e) :=
    ty_expandSR hW hX hTK hGK (stable_glue hW hGK hφe) hTT
  have P := per2_tyCode hW hX k (Hom.id k)
  unfold RE2 at hxy
  rw [semK_tyEq hW hface] at hxy
  exact P.conv (P.symTy hTG) hxy


/-- `unglue` of related elements of a Glue type, whether or not its face holds. -/
theorem RE2_unglue_gen {A T e e' g g' : Tm} {φ φ' : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hgg : RE2 S k (.glue A φ T e) g g')
    (hu : HasTy S k .one [] (.unglue φ e g) A) (hu' : HasTy S k .one [] (.unglue φ' e' g') A)
    (hφ' : φ'.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ee' : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A))
    (hAA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A.isub σ))
    (hTT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ))
    (hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)) :
    RE2 S k A (.unglue φ e g) (.unglue φ' e' g') := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  by_cases hh : (ival (idEnv k) φ).holds
  swap
  · exact RE2_unglue hW hG hh hgg hu hu' hφ' h12 h21 ee' hAA hTT hE
  have hφe : I.Entails .one φ := (holds_iff_entails hφs).1 hh
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  have hh0 : (ival (idEnv k) (φ.subst (ISub.id k).τ)).holds := by rwa [I_subst_id hφs]
  have hT0 := hTT k (ISub.id k) hh0
  have hE0 := hE k (ISub.id k) hh0
  have hA00 := hAA k (ISub.id k)
  rw [isub_id_of_closed hc.1.2] at hT0
  have heL : HasTy S k .one [] e (Tm.equiv T A) :=
    HasTy.restrict (Φ := cof .one φ) trivial (ent_and_intro (ent_refl _) hφe) he0
  have heR : HasTy S k .one [] e' (Tm.equiv T A) :=
    HasTy.restrict (Φ := cof .one φ) trivial (ent_and_intro (ent_refl _) hφe) (HasTy.eqL ee')
  rw [isub_id_of_closed hc.1.2, isub_id_of_closed hc.1.1.1, isub_id_of_closed hc.2,
    isub_id_of_closed (closed_of_ty hW heR)] at hE0
  rw [isub_id_of_closed hc.1.1.1] at hA00
  have hgT := RE2_glue_fib hW hG hφe hT0 hgg
  have happ := RE2_equiv_app hW hE0 hgT
  obtain ⟨l2, hG2, eG2⟩ := glue_annot_eq hW hG hφ' h12 h21 ee'
  have hg2 : HasTy S k .one [] g' (.glue A φ' T e') := (RE2.typed hgg).2.1.conv eG2
  exact RE2.expand2 hW hA00 hu hu' (stable_unglueFace hW hφe hu (RE2.typed hgg).1 hA0 heL (TyEq.refl _))
    (stable_unglueFace hW (ent_trans hφe h12) hu' hg2 hA0 heR (TyEq.refl _)) happ


/-- Related types with Glue normal forms whose faces do not hold have equivalent faces. -/
theorem RT2_glueW_face {X X' A T e A' T' e' : Tm} {φ φ' : I} {l l' : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hG' : HasTy S k .one [] (.glue A' φ' T' e') (.univ l'))
    (hn : ¬ I.Entails .one φ) (h : RT2 S k X X')
    (hR : RedT S k X (.glue A φ T e)) (hR' : RedT S k X' (.glue A' φ' T' e')) :
    I.Entails φ φ' ∧ I.Entails φ' φ := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hφs' := (glue_data hW hG').1
  have hnf : ¬ Cof.holds (ival (idEnv k) φ).face := by
    rw [← DM.holds_iff_face_holds]; exact fun hh => hn ((holds_iff_entails hφs).1 hh)
  have hXK : IsTyK S k X := (show IsTyK S k (.glue A φ T e) from ⟨l, .inl hG⟩).of_tyEq (TyEq.symm hR.2)
  have hXK' : IsTyK S k X' := (show IsTyK S k (.glue A' φ' T' e') from ⟨l', .inl hG'⟩).of_tyEq (TyEq.symm hR'.2)
  unfold RT2 at h
  rw [semK_tyEq hW hR.2, semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hnf] at h
  obtain ⟨-, hloc, -, -⟩ := h
  have h0 := hloc k (ISub.id k)
  unfold glueLocT at h0
  rw [if_neg (by rw [Hom.id_comp, ISub.hom_id, (isCof_ival_face _ _).restr_id]; exact hnf)] at h0
  obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', r1, r2, -, -, f1, f2, -⟩ := h0
  rw [isub_id_of_closed (closed_of_isTyK hW hXK)] at r1
  rw [isub_id_of_closed (closed_of_isTyK hW hXK')] at r2
  have eq1 := RedW.unique r1.1 hR.1
  have eq2 := RedW.unique r2.1 hR'.1
  simp only [Tm.glue.injEq] at eq1 eq2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq2
  rw [Hom.id_comp, ISub.hom_id, (isCof_ival_face _ _).restr_id] at f1 f2
  exact ⟨ent_of_face_eq hφs hφs' (f1.trans f2.symm), ent_of_face_eq hφs' hφs (f2.trans f1.symm)⟩

end

end Model.Whnf
