import Model.Whnf.Kan2Comp
import Model.Whnf.Valid2GlueEta
import Model.Canon.KanGlue

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


/-- The data of a composition at a pair of Glue types (as left and right instances): related bases, fibers
and equivalences, Kan bases and fibers, and related composition data at the left Glue type. -/
structure GHD (S : Sig) (k : ℕ) (A T e A' T' e' : Tm) (φ φ' ψ ψ' : I) (u u' a0 a0' : Tm) : Prop where
  hG : ∃ l, HasTy S k .one [] (.glue A φ T e) (.univ l)
  hG' : ∃ l, HasTy S k .one [] (.glue A' φ' T' e') (.univ l)
  hA : RT2 S k A A'
  hT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T'.isub σ)
  hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)
  f12 : I.Entails φ φ'
  f21 : I.Entails φ' φ
  ee : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A)
  kA : ∀ k' (σ : ISub k' k), KanH2 S k' (A.isub σ) (A'.isub σ)
  kT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → KanH2 S k' (T.isub σ) (T'.isub σ)
  hty : HasTy S k .one [] (.hcomp (.glue A φ T e) ψ u a0) (.glue A φ T e)
  hty' : HasTy S k .one [] (.hcomp (.glue A' φ' T' e') ψ' u' a0') (.glue A φ T e)
  heq : EqTm S k .one [] (.hcomp (.glue A φ T e) ψ u a0) (.hcomp (.glue A' φ' T' e') ψ' u' a0') (.glue A φ T e)
  hteq : EqTm S (k + 1) (cof .one ψ).shift [] u u' (Tm.glue A φ T e).dshift
  p12 : I.Entails ψ ψ'
  p21 : I.Entails ψ' ψ
  tube : Tube2 S k (.glue A φ T e) ψ u u'
  ha0 : RE2 S k (.glue A φ T e) a0 a0'
  bd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds →
    RE2 S k' ((Tm.glue A φ T e).isub σ) ((u.isub σ.up).dinst .zero) (a0'.isub σ)
  bd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds →
    RE2 S k' ((Tm.glue A φ T e).isub σ) (a0.isub σ) ((u'.isub σ.up).dinst .zero)

theorem GHD.isub {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (ρ : ISub k' k) :
    GHD S k' (A.isub ρ) (T.isub ρ) (e.isub ρ) (A'.isub ρ) (T'.isub ρ) (e'.isub ρ) (φ.subst ρ.τ) (φ'.subst ρ.τ)
      (ψ.subst ρ.τ) (ψ'.subst ρ.τ) (u.isub ρ.up) (u'.isub ρ.up) (a0.isub ρ) (a0'.isub ρ) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, -⟩ := glue_data hW hG
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hc : ∀ {k''} (σ : ISub k'' k'), (ival (idEnv k'') ((φ.subst ρ.τ).subst σ.τ)).holds →
      (ival (idEnv k'') (φ.subst (ρ.comp σ).τ)).holds := fun σ h => by rwa [I_subst_comp]
  refine ⟨⟨l, HasTy.isubS hW hG ρ⟩, ⟨l', HasTy.isubS hW hG' ρ⟩, RT2.isub hW hXA D.hA ρ, fun k'' σ hh => ?_,
    fun k'' σ hh => ?_, ent_subst D.f12 ρ.τ, ent_subst D.f21 ρ.τ, ?_, fun k'' σ => ?_, fun k'' σ hh => ?_,
    HasTy.isubS hW D.hty ρ, HasTy.isubS hW D.hty' ρ, EqTm.isubS hW D.heq ρ, ?_, ent_subst D.p12 ρ.τ,
    ent_subst D.p21 ρ.τ, D.tube.isub ρ, RE2.isub hW D.ha0 ρ, bdry_isub D.bd ρ, bdry_isub' D.bd' ρ⟩
  · rw [Tm.isub_isub, Tm.isub_isub]; exact D.hT k'' (ρ.comp σ) (hc σ hh)
  · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact D.hE k'' (ρ.comp σ) (hc σ hh)
  · have := EqTm.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩) D.ee ρ
    rwa [isub_equiv] at this
  · rw [Tm.isub_isub, Tm.isub_isub]; exact D.kA k'' (ρ.comp σ)
  · rw [Tm.isub_isub, Tm.isub_isub]; exact D.kT k'' (ρ.comp σ) (hc σ hh)
  · have := EqTm.cofIsub hW hψs D.hteq ρ
    rwa [isub_dshift] at this


/-- The fiber of `hcompGlue`, where the face of the Glue type holds. -/
theorem GHD.fib {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hφe : I.Entails .one φ) :
    RE2 S k T (.hcomp T ψ u a0) (.hcomp T' ψ' u' a0') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, -⟩ := glue_data hW hG
  have hφs' := (glue_data hW hG').1
  have hφe' : I.Entails .one φ' := ent_trans hφe D.f12
  have hc := closed_of_ty hW hG
  have hc' := closed_of_ty hW hG'
  simp only [Tm.closedB, Bool.and_eq_true] at hc hc'
  have hh : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds := fun σ =>
    (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 (ent_one_subst hφe σ.τ)
  have hh0 : (ival (idEnv k) (φ.subst (ISub.id k).τ)).holds := hh (ISub.id k)
  have hT0 := D.hT k (ISub.id k) hh0
  have hK0 := D.kT k (ISub.id k) hh0
  rw [isub_id_of_closed hc.1.2, isub_id_of_closed hc'.1.2] at hT0 hK0
  have hTT' : TyEq S k T T' := (Comp2_ty_base hT0).2.2.2.2.2
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  have hG'K : IsTyK S k (.glue A' φ' T' e') := ⟨l', .inl hG'⟩
  have hGT : TyEq S k (.glue A φ T e) T := glue_face_tyEq hW hGK hφe
  have hG'T' : TyEq S k (.glue A' φ' T' e') T' := glue_face_tyEq hW hG'K hφe'
  -- typings
  obtain ⟨-, ⟨-, hψs, hu, ha0, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  obtain ⟨l1', ⟨hG'0, hψs', hu', ha0', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty') rfl
  have parts := hcompGlue_parts hS (spec_to_minimal hW D.hty) (spec_to_minimal hW hG)
  have hty'G' : HasTy0 S k .one [] (.hcomp (.glue A' φ' T' e') ψ' u' a0') (.glue A' φ' T' e') :=
    HasTy0.hcomp hG'0 hψs' hu' ha0' hside'
  have parts' := hcompGlue_parts hS hty'G' (spec_to_minimal hW hG')
  have hcT : HasTy S k .one [] (.hcomp T ψ u a0) T :=
    HasTy.restrict (Φ := cof .one φ) trivial (ent_and_intro (ent_refl _) hφe) (minimal_to_spec parts.1)
  have hcT' : HasTy S k .one [] (.hcomp T' ψ' u' a0') T' :=
    HasTy.restrict (Φ := cof .one φ') trivial (ent_and_intro (ent_refl _) hφe') (minimal_to_spec parts'.1)
  have e1 : EqTm S k .one [] (.hcomp T ψ u a0) (.hcomp (.glue A φ T e) ψ u a0) T :=
    EqTm.hcomp hcT (D.hty.tyConv hGT) (EqTm.glueFace hφe hG).symm (ent_refl _) (ent_refl _)
      (EqTm.cofConv hψs (EqTm.refl (minimal_to_spec hu)) hGT) (EqTm.refl ((minimal_to_spec ha0).tyConv hGT))
  have e3 : EqTm S k .one [] (.hcomp (.glue A' φ' T' e') ψ' u' a0') (.hcomp T' ψ' u' a0') (.glue A' φ' T' e') :=
    EqTm.hcomp (minimal_to_spec hty'G') (hcT'.tyConv (TyEq.symm hG'T')) (EqTm.glueFace hφe' hG') (ent_refl _)
      (ent_refl _) (EqTm.refl (minimal_to_spec hu')) (EqTm.refl (minimal_to_spec ha0'))
  have hG'T : TyEq S k (.glue A' φ' T' e') T := TyEq.trans hW hG'T' (TyEq.symm hTT')
  have heqT : EqTm S k .one [] (.hcomp T ψ u a0) (.hcomp T' ψ' u' a0') T :=
    e1.trans ((D.heq.tyConv hGT).trans (e3.tyConv hG'T))
  have toT : ∀ k' (σ : ISub k' k) (x y : Tm), RE2 S k' ((Tm.glue A φ T e).isub σ) x y → RE2 S k' (T.isub σ) x y := by
    intro k' σ x y h
    rw [isub_glue] at h
    have hGσ := HasTy.isubS hW hG σ
    rw [isub_glue] at hGσ
    have hX : TyCode k' (semK S k' (T.isub σ)) := tyCode_of_univ hW (glue_fiber_ty hW hG σ (hh σ)).choose_spec.1
    exact RE2_glue_fib hW hGσ (ent_one_subst hφe σ.τ) (RT2.refl hW hX (D.hT k' σ (hh σ))) h
  have hXT : TyCode k (semK S k T) := RT2.tyCode_l hW hT0 (by
    rw [RT2.semK_eq hW hT0]; exact tyCode_of_ty hW hcT)
  exact hK0 ψ ψ' u u' a0 a0' hcT (hcT'.tyConv (TyEq.symm hTT')) heqT (EqTm.cofConv hψs D.hteq hGT) D.p12 D.p21
    (fun k' σ r r' hr hr' hE hhψ => toT k' σ _ _ (D.tube k' σ r r' hr hr' hE hhψ))
    (RE2_glue_fib hW hG hφe (RT2.refl hW hXT hT0) D.ha0)
    (fun k' σ hhψ => toT k' σ _ _ (D.bd k' σ hhψ)) (fun k' σ hhψ => toT k' σ _ _ (D.bd' k' σ hhψ))

end

end Model.Whnf
