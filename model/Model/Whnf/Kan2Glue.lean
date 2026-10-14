import Model.Whnf.Kan2GlueEq
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


/-- The equivalences of related Glue types agree under the face. -/
theorem glue_ee {A T e A' T' e' : Tm} {φ φ' : I} {l l' : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hG' : HasTy S k .one [] (.glue A' φ' T' e') (.univ l'))
    (f12 : I.Entails φ φ') (hA : RT2 S k A A')
    (hT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T'.isub σ))
    (hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)) :
    EqTm S k (cof .one φ) [] e' e (Tm.equiv T A) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨hA1, hφs, hT1, he1⟩, -⟩ := gen_glue hS (spec_to_minimal hW hG) rfl
  obtain ⟨l2, ⟨hA2, hφs', hT2, he2⟩, -⟩ := gen_glue hS (spec_to_minimal hW hG') rfl
  have hΦ : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  have c12 : I.Entails (cof .one φ) (cof .one φ') := ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) f12)
  have hE1 := equiv_ty_cof hW hφs (minimal_to_spec hA1) (minimal_to_spec hT1)
  have hE2 := HasTy.restrict hΦ c12 (equiv_ty_cof hW hφs' (minimal_to_spec hA2) (minimal_to_spec hT2))
  have eqv : EqTm S k (cof .one φ) [] (Tm.equiv T A) (Tm.equiv T' A') (.univ maxLevel) := by
    refine eq_of_restr hW hφs (.inr rfl) hE1 hE2 fun k'' σ hh => ?_
    rw [isub_equiv, isub_equiv, isub_univ]
    have hTσ := face_ty hW hφs (minimal_to_spec hT1) σ hh
    rw [isub_univ] at hTσ
    have eT := eqTop hW (Comp2_ty_base (hT k'' σ hh)).2.2.2.2.2 hTσ
    have eA := eqTop hW (Comp2_ty_base (RT2.isub hW (tyCode_of_univ hW (minimal_to_spec hA1)) hA σ)).2.2.2.2.2
      (HasTy.isubS hW (minimal_to_spec hA1) σ)
    exact equiv_congrS hW eT eA
  have key : EqTm S k (cof .one φ) [] e e' (Tm.equiv T A) := by
    refine eq_of_restr hW hφs (.inl hE1) (minimal_to_spec he1)
      (HasTy.conv (HasTy.restrict hΦ c12 (minimal_to_spec he2)) (EqTm.symm eqv)) fun k'' σ hh => ?_
    rw [isub_equiv]
    exact (RE2.typed (hE k'' σ hh)).2.2
  exact key.symm

/-- The data of a composition at a pair of related types, as taken by `KanH2`. -/
structure KD (S : Sig) (k : ℕ) (X X' : Tm) (ψ ψ' : I) (u u' a0 a0' : Tm) : Prop where
  hty : HasTy S k .one [] (.hcomp X ψ u a0) X
  hty' : HasTy S k .one [] (.hcomp X' ψ' u' a0') X
  heq : EqTm S k .one [] (.hcomp X ψ u a0) (.hcomp X' ψ' u' a0') X
  hteq : EqTm S (k + 1) (cof .one ψ).shift [] u u' X.dshift
  p12 : I.Entails ψ ψ'
  p21 : I.Entails ψ' ψ
  tube : Tube2 S k X ψ u u'
  ha0 : RE2 S k X a0 a0'
  bd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds →
    RE2 S k' (X.isub σ) ((u.isub σ.up).dinst .zero) (a0'.isub σ)
  bd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (ψ.subst σ.τ)).holds →
    RE2 S k' (X.isub σ) (a0.isub σ) ((u'.isub σ.up).dinst .zero)

omit hW in
theorem KD.kan {X X' : Tm} {ψ ψ' : I} {u u' a0 a0' : Tm} (D : KD S k X X' ψ ψ' u u' a0 a0')
    (hK : KanH2 S k X X') : RE2 S k X (.hcomp X ψ u a0) (.hcomp X' ψ' u' a0') :=
  hK ψ ψ' u u' a0 a0' D.hty D.hty' D.heq D.hteq D.p12 D.p21 D.tube D.ha0 D.bd D.bd'

/-- Fillers of related compositions, at `I.Eq`-equal points. -/
theorem KD.fillPt {X X' : Tm} {ψ ψ' : I} {u u' a0 a0' : Tm} (D : KD S k X X' ψ ψ' u u' a0 a0')
    (hK : ∀ k3 (τ : ISub k3 k), KanH2 S k3 (X.isub τ) (X'.isub τ)) (hXX : RT2 S k X X') {r r' : I}
    (hr : r.Scoped k) (hr' : r'.Scoped k) (hE : I.Eq r r') :
    RE2 S k X ((Tm.hfill X ψ u a0).dinst r) ((Tm.hfill X' ψ' u' a0').dinst r') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨hX0, hψs, hu, ha, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  obtain ⟨l2, ⟨hX0', hψs', hu', ha', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty') rfl
  have hTA : TyEq S k X X' := (Comp2_ty_base hXX).2.2.2.2.2
  have hXc : TyCode k (semK S k X) := RE2.tyCode hW D.ha0
  have hAA0 : X = X' ∨ ∃ l, EqTm0 S k .one [] X X' (.univ l) := by
    rcases hTA with e | ⟨l, e⟩
    · exact .inl e
    · exact .inr ⟨l, spec_to_minimal_eq hW e⟩
  have F := hfill_typed hS hX0 hψs hu ha hside
  have F' := hfill_typed hS hX0' hψs' hu' ha' hside'
  have hF : HasTy S (k + 1) .one [] (Tm.hfill X ψ u a0) X.dshift := minimal_to_spec F.1
  have hF'0 : HasTy S (k + 1) .one [] (Tm.hfill X' ψ' u' a0') X'.dshift := minimal_to_spec F'.1
  have eXd : TyEq S (k + 1) X'.dshift X.dshift := by
    rcases hTA with e | ⟨l, e⟩
    · exact .inl (by rw [e])
    · exact .inr ⟨l, EqTm.dwk e.symm⟩
  have hF' := hF'0.tyConv eXd
  have heqF := minimal_to_spec_eq (hfill_cong hW (spec_to_minimal hW hF) (spec_to_minimal hW hF') hAA0
    (spec_to_minimal_eq hW D.hteq) (spec_to_minimal_eq hW (RE2.typed D.ha0).2.2) D.p12 D.p21)
  have h := hfill_rel hW hψs hK (RT2.refl hW hXc hXX) hTA D.hteq hF hF' heqF D.p12 D.p21 D.tube D.ha0 D.bd D.bd'
    (ISub.cons r hr (ISub.id k)) (ISub.cons r' hr' (ISub.id k)) (by rw [ISub.tail_cons, ISub.tail_cons]) hE
  rw [dshift_isub_tail, ISub.tail_cons, isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW D.hty)),
    isub_cons_id_dinst hW (closed_of_ty hW hF) r hr, isub_cons_id_dinst hW (closed_of_ty hW hF') r' hr'] at h
  exact h

/-- The data of a composition at a pair of Glue types (as left and right instances): related bases, fibers
and equivalences, Kan bases and fibers, and related composition data at the left Glue type. -/
structure GHD (S : Sig) (k : ℕ) (A T e A' T' e' : Tm) (φ φ' ψ ψ' : I) (u u' a0 a0' : Tm) : Prop where
  hG : ∃ l, HasTy S k .one [] (.glue A φ T e) (.univ l)
  hG' : ∃ l, HasTy S k .one [] (.glue A' φ' T' e') (.univ l)
  gG : TyEq S k (.glue A φ T e) (.glue A' φ' T' e')
  hGG : RT2 S k (.glue A φ T e) (.glue A φ T e)
  hA : RT2 S k A A'
  hT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T'.isub σ)
  hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)
  hEL : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e.isub σ)
  f12 : I.Entails φ φ'
  f21 : I.Entails φ' φ
  ee : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A)
  kA : ∀ k' (σ : ISub k' k) X', RT2 S k' (A.isub σ) X' → KanH2 S k' (A.isub σ) X'
  kT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → ∀ X', RT2 S k' (T.isub σ) X' →
    KanH2 S k' (T.isub σ) X'
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
  refine ⟨⟨l, HasTy.isubS hW hG ρ⟩, ⟨l', HasTy.isubS hW hG' ρ⟩, TyEq.isub hW ρ D.gG,
    RT2.isub hW (tyCode_of_univ hW hG) D.hGG ρ, RT2.isub hW hXA D.hA ρ, fun k'' σ hh => ?_,
    fun k'' σ hh => ?_, fun k'' σ hh => ?_, ent_subst D.f12 ρ.τ, ent_subst D.f21 ρ.τ, ?_, fun k'' σ => ?_,
    fun k'' σ hh => ?_,
    HasTy.isubS hW D.hty ρ, HasTy.isubS hW D.hty' ρ, EqTm.isubS hW D.heq ρ, ?_, ent_subst D.p12 ρ.τ,
    ent_subst D.p21 ρ.τ, D.tube.isub ρ, RE2.isub hW D.ha0 ρ, bdry_isub D.bd ρ, bdry_isub' D.bd' ρ⟩
  · rw [Tm.isub_isub, Tm.isub_isub]; exact D.hT k'' (ρ.comp σ) (hc σ hh)
  · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact D.hE k'' (ρ.comp σ) (hc σ hh)
  · rw [Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; exact D.hEL k'' (ρ.comp σ) (hc σ hh)
  · have := EqTm.isubF hW (show (cof .one φ).Scoped k from ⟨trivial, hφs⟩) D.ee ρ
    rwa [isub_equiv] at this
  · rw [Tm.isub_isub]; exact D.kA k'' (ρ.comp σ)
  · rw [Tm.isub_isub]; exact D.kT k'' (ρ.comp σ) (hc σ hh)
  · have := EqTm.cofIsub hW hψs D.hteq ρ
    rwa [isub_dshift] at this


/-- The composition data at the fibers, where the face of the Glue type holds. -/
theorem GHD.fibKD {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hφe : I.Entails .one φ) :
    KD S k T T' ψ ψ' u u' a0 a0' := by
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
  rw [isub_id_of_closed hc.1.2, isub_id_of_closed hc'.1.2] at hT0
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
  exact ⟨hcT, hcT'.tyConv (TyEq.symm hTT'), heqT, EqTm.cofConv hψs D.hteq hGT, D.p12, D.p21,
    (fun k' σ r r' hr hr' hE hhψ => toT k' σ _ _ (D.tube k' σ r r' hr hr' hE hhψ)),
    (RE2_glue_fib hW hG hφe (RT2.refl hW hXT hT0) D.ha0),
    (fun k' σ hhψ => toT k' σ _ _ (D.bd k' σ hhψ)), (fun k' σ hhψ => toT k' σ _ _ (D.bd' k' σ hhψ))⟩

/-- The relations at the fibers, where the face of the Glue type holds. -/
theorem GHD.fibRel {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hφe : I.Entails .one φ) :
    RT2 S k T T' ∧ ∀ k3 (τ : ISub k3 k), KanH2 S k3 (T.isub τ) (T'.isub τ) := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  have hφs := (glue_data hW hG).1
  have hc := closed_of_ty hW hG
  have hc' := closed_of_ty hW hG'
  simp only [Tm.closedB, Bool.and_eq_true] at hc hc'
  have hh : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds := fun σ =>
    (holds_iff_entails (I.scoped_subst hφs σ.sc)).2 (ent_one_subst hφe σ.τ)
  have hT0 := D.hT k (ISub.id k) (hh _)
  rw [isub_id_of_closed hc.1.2, isub_id_of_closed hc'.1.2] at hT0
  exact ⟨hT0, fun k3 τ => D.kT k3 τ (hh τ) _ (D.hT k3 τ (hh τ))⟩

/-- The fiber of `hcompGlue`, where the face of the Glue type holds. -/
theorem GHD.fib {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hφe : I.Entails .one φ) :
    RE2 S k T (.hcomp T ψ u a0) (.hcomp T' ψ' u' a0') := by
  have h := (D.fibRel hW hφe).2 k (ISub.id k)
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  have hc := closed_of_ty hW hG
  have hc' := closed_of_ty hW hG'
  simp only [Tm.closedB, Bool.and_eq_true] at hc hc'
  rw [isub_id_of_closed hc.1.2, isub_id_of_closed hc'.1.2] at h
  exact (D.fibKD hW hφe).kan h


/-- `unglue` of related elements of the left Glue type, with the respective annotations. -/
theorem GHD.ug0 {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') {g g' : Tm} (h : RE2 S k (.glue A φ T e) g g') :
    RE2 S k A (.unglue φ e g) (.unglue φ' e' g') := by
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  obtain ⟨hφs', lA', hA0', he0'⟩ := glue_data hW hG'
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA' : TyEq S k A A' := (Comp2_ty_base D.hA).2.2.2.2.2
  have hu := unglue_ty hW ⟨l, .inl hG⟩ ⟨lA, hA0, he0⟩ (RE2.typed h).1
  have hu' := (unglue_ty hW ⟨l', .inl hG'⟩ ⟨lA', hA0', he0'⟩ ((RE2.typed h).2.1.tyConv D.gG)).tyConv
    (TyEq.symm hAA')
  exact RE2_unglue_gen hW hG h hu hu' hφs' D.f12 D.f21 D.ee (fun k' σ => RT2.isub hW hXA (RT2.refl hW hXA D.hA) σ)
    (fun k' σ hh => RT2.refl hW (tyCode_of_univ hW (glue_fiber_ty hW hG σ hh).choose_spec.1) (D.hT k' σ hh)) D.hE

/-- `unglue` of related elements of the left Glue type, at a restriction. -/
theorem GHD.ug {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (σ : ISub k' k) {g g' : Tm}
    (h : RE2 S k' ((Tm.glue A φ T e).isub σ) g g') :
    RE2 S k' (A.isub σ) (.unglue (φ.subst σ.τ) (e.isub σ) g) (.unglue (φ'.subst σ.τ) (e'.isub σ) g') :=
  (D.isub hW σ).ug0 hW h

/-- Fillers of the fibers at points, where the face of the Glue type holds. -/
theorem GHD.fillPt {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hφe : I.Entails .one φ) {r r' : I}
    (hr : r.Scoped k) (hr' : r'.Scoped k) (hE : I.Eq r r') :
    RE2 S k T ((Tm.hfill T ψ u a0).dinst r) ((Tm.hfill T' ψ' u' a0').dinst r') :=
  (D.fibKD hW hφe).fillPt hW (D.fibRel hW hφe).2 (D.fibRel hW hφe).1 hr hr' hE


omit hW in
/-- A related tube is related to itself. -/
theorem KD.tubeL {X X' : Tm} {ψ ψ' : I} {u u' a0 a0' : Tm} (hW : WfSig S) (D : KD S k X X' ψ ψ' u u' a0 a0')
    (hXX : RT2 S k X X') : Tube2 S k X ψ u u := by
  have hXc : TyCode k (semK S k X) := RE2.tyCode hW D.ha0
  intro k' σ r r' hr hr' hE hh
  have hXσ := RT2.isub hW hXc hXX σ
  exact RE2.trans hW hXσ (D.tube k' σ r r' hr hr' hE hh)
    (RE2.symm hW hXσ (D.tube k' σ r' r' hr' hr' (I_eq_refl _) hh))

/-- A filler at a point where its face holds. -/
theorem KD.facePt {X X' : Tm} {ψ ψ' : I} {u u' a0 a0' : Tm} (D : KD S k X X' ψ ψ' u u' a0 a0')
    (hXX : RT2 S k X X') (hψe : I.Entails .one ψ) {r : I} (hr : r.Scoped k) :
    RE2 S k X ((Tm.hfill X ψ u a0).dinst r) (u.dinst r) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨hX0, hψs, hu, ha, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have hXc : TyCode k (semK S k X) := RE2.tyCode hW D.ha0
  have F := hfill_typed hS hX0 hψs hu ha hside
  have hF : HasTy S (k + 1) .one [] (Tm.hfill X ψ u a0) X.dshift := minimal_to_spec F.1
  have h := hfill_face_pt hW hψs hXc (RT2.refl hW hXc hXX) hF (D.tubeL hW hXX) (ISub.id k) r hr
    (by rw [I_subst_id hψs]; exact (holds_iff_entails hψs).2 hψe)
  have hc := closed_of_ty hW D.hty
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  rw [isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW D.hty)), isub_cons_id_dinst hW (closed_of_ty hW hF) r hr,
    isub_up_id_of_closed hc.1.2] at h
  exact h


/-- The tubes at a point, where their face holds. -/
theorem GHD.tube0 {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hψe : I.Entails .one ψ) {r r' : I}
    (hr : r.Scoped k) (hr' : r'.Scoped k) (hE : I.Eq r r') :
    RE2 S k (.glue A φ T e) (u.dinst r) (u'.dinst r') := by
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have h := D.tube k (ISub.id k) r r' hr hr' hE (by rw [I_subst_id hψs]; exact (holds_iff_entails hψs).2 hψe)
  have hc := closed_of_ty hW D.hty
  have hc' := closed_of_ty hW D.hty'
  simp only [Tm.closedB, Bool.and_eq_true] at hc hc'
  obtain ⟨l, hG⟩ := D.hG
  rw [isub_id_of_closed (closed_of_ty hW hG), isub_up_id_of_closed hc.1.2, isub_up_id_of_closed hc'.1.2] at h
  exact h

/-- The tube of the base composition at a point, where its face holds. -/
theorem GHD.tubePt {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hor : I.Entails .one (.or ψ φ)) {r r' : I}
    (hr : r.Scoped k) (hr' : r'.Scoped k) (hE : I.Eq r r') :
    RE2 S k A (.split ψ (.unglue φ e (u.dinst r)) φ (.app (.fst e) ((Tm.hfill T ψ u a0).dinst r)))
      (.split ψ' (.unglue φ' e' (u'.dinst r')) φ' (.app (.fst e') ((Tm.hfill T' ψ' u' a0').dinst r'))) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hφs' := (glue_data hW hG').1
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  obtain ⟨l1', ⟨hG'0, hψs', hu', ha0', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty') rfl
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA : RT2 S k A A := RT2.refl hW hXA D.hA
  have hAA' : TyEq S k A A' := (Comp2_ty_base D.hA).2.2.2.2.2
  have parts := hcompGlue_parts hS (spec_to_minimal hW D.hty) (spec_to_minimal hW hG)
  have parts' := hcompGlue_parts hS (HasTy0.hcomp hG'0 hψs' hu' ha0' hside') (spec_to_minimal hW hG')
  have hor' : I.Entails .one (.or ψ' φ') :=
    ent_trans hor (ent_or_elim (ent_trans D.p12 (ent_or_left _ _)) (ent_trans D.f12 (ent_or_right _ _)))
  have hsp := hcomp_tube_typed' hW (minimal_to_spec parts.2.1) r hr
    ((holds_iff_entails (show (I.or ψ φ).Scoped k from ⟨hψs, hφs⟩)).2 hor)
  have hsp' := hcomp_tube_typed' hW ((minimal_to_spec parts'.2.1).tyConv (TyEq.symm hAA')) r' hr'
    ((holds_iff_entails (show (I.or ψ' φ').Scoped k from ⟨hψs', hφs'⟩)).2 hor')
  rw [glueTube_d] at hsp hsp'
  have hhold : ∀ {k'} {x : I} (σ : ISub k' k), x.Scoped k → I.Entails .one (x.subst σ.τ) →
      (ival (idEnv k') (x.subst σ.τ)).holds := fun σ hx h => (holds_iff_entails (I.scoped_subst hx σ.sc)).2 h
  have hrσ : ∀ {k'} (σ : ISub k' k), (r.subst σ.τ).Scoped k' := fun σ => I.scoped_subst hr σ.sc
  have hrσ' : ∀ {k'} (σ : ISub k' k), (r'.subst σ.τ).Scoped k' := fun σ => I.scoped_subst hr' σ.sc
  have tubeσ : ∀ {k'} (σ : ISub k' k), I.Entails .one (ψ.subst σ.τ) →
      RE2 S k' ((Tm.glue A φ T e).isub σ) ((u.dinst r).isub σ) ((u'.dinst r').isub σ) := fun σ h => by
    rw [isub_dinst, isub_dinst]
    exact D.tube _ σ _ _ (hrσ σ) (hrσ' σ) (I_eq_subst hE σ.τ) (hhold σ hψs h)
  refine RE2_sys2 hW hψs hψs' hφs hφs' D.p12 D.p21 D.f12 D.f21 hor hAA hsp hsp'
    (fun k' σ hψσ => D.ug hW σ (tubeσ σ hψσ)) (fun k' σ hψσ hφσ => ?_) (fun k' σ hψσ hφσ => ?_)
    (fun k' σ hφσ => ?_)
  · -- both faces: the left `unglue` against the right fiber image
    have Dσ := D.isub hW σ
    have hGσ : HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) :=
      HasTy.isubS hW hG σ
    have hAσ := RT2.isub hW hXA hAA σ
    have hpp := D.ug hW σ (tubeσ σ hψσ)
    have hTσ := (Dσ.fibRel hW hφσ).1
    have hTTσ := RT2.refl hW (RE2.tyCode hW ((Dσ.fibKD hW hφσ).ha0)) hTσ
    have x1 := RE2_glue_fib hW hGσ hφσ hTTσ (tubeσ σ hψσ)
    rw [isub_dinst] at x1
    have x2 := (Dσ.fibKD hW hφσ).facePt hW hTσ hψσ (hrσ σ)
    have x3 := Dσ.fillPt hW hφσ (hrσ σ) (hrσ' σ) (I_eq_subst hE σ.τ)
    have x := RE2.trans hW hTTσ (RE2.symm hW hTTσ x2) x3
    have happ := RE2_equiv_app hW (D.hE k' σ (hhold σ hφs hφσ)) x
    have heσ : HasTy S k' .one [] (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := by
      have := face_ty hW hφs he0 σ (hhold σ hφs hφσ); rwa [isub_equiv] at this
    have hst := stable_unglueFace hW hφσ (RE2.typed hpp).1 (RE2.typed (tubeσ σ hψσ)).1 (HasTy.isubS hW hA0 σ) heσ
      (TyEq.refl _)
    simp only [isub_unglue, isub_app, isub_fst, isub_dinst, isub_hfill]
    simp only [isub_dinst] at hpp
    rw [isub_dinst] at hst
    exact RE2.expandL hW hAσ (RE2.typed hpp).1 (RE2.typed happ).2.1 hst happ
  · -- both faces: the left fiber image against the right `unglue`
    have Dσ := D.isub hW σ
    have hGσ : HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) :=
      HasTy.isubS hW hG σ
    have hAσ := RT2.isub hW hXA hAA σ
    have hpp := D.ug hW σ (tubeσ σ hψσ)
    have hTσ := (Dσ.fibRel hW hφσ).1
    have hTTσ := RT2.refl hW (RE2.tyCode hW ((Dσ.fibKD hW hφσ).ha0)) hTσ
    have x1 := RE2_glue_fib hW hGσ hφσ hTTσ (tubeσ σ hψσ)
    rw [isub_dinst, isub_dinst] at x1
    have x2 := (Dσ.fibKD hW hφσ).facePt hW hTσ hψσ (hrσ σ)
    have x := RE2.trans hW hTTσ x2 x1
    have happ := RE2_equiv_app hW (D.hE k' σ (hhold σ hφs hφσ)) x
    have hφσ' : I.Entails .one (φ'.subst σ.τ) := ent_trans hφσ (ent_subst D.f12 σ.τ)
    have ee'σ : EqTm S k' (cof .one (φ.subst σ.τ)) [] (e'.isub σ) (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) :=
      Dσ.ee
    obtain ⟨l2, hG2, eG2⟩ := glue_annot_eq hW hGσ (I.scoped_subst hφs' σ.sc) (ent_subst D.f12 σ.τ)
      (ent_subst D.f21 σ.τ) ee'σ
    have he'σ : HasTy S k' .one [] (e'.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := by
      have := face_ty hW hφs (HasTy.eqL D.ee) σ (hhold σ hφs hφσ); rwa [isub_equiv] at this
    have hg2 := (RE2.typed (tubeσ σ hψσ)).2.1.conv eG2
    rw [isub_dinst] at hg2
    simp only [isub_dinst] at hpp
    have hst := stable_unglueFace hW hφσ' (RE2.typed hpp).2.1 hg2 (HasTy.isubS hW hA0 σ) he'σ (TyEq.refl _)
    simp only [isub_unglue, isub_app, isub_fst, isub_dinst, isub_hfill]
    exact RE2.expandR hW hAσ (RE2.typed happ).1 (RE2.typed hpp).2.1 hst happ
  · -- the fiber images
    simp only [isub_app, isub_fst, isub_dinst, isub_hfill]
    exact RE2_equiv_app hW (D.hE k' σ (hhold σ hφs hφσ))
      ((D.isub hW σ).fillPt hW hφσ (hrσ σ) (hrσ' σ) (I_eq_subst hE σ.τ))


/-- A filler at `0` is the base. -/
theorem KD.zeroPt {X X' : Tm} {ψ ψ' : I} {u u' a0 a0' : Tm} (D : KD S k X X' ψ ψ' u u' a0 a0')
    (hXX : RT2 S k X X') : RE2 S k X ((Tm.hfill X ψ u a0).dinst .zero) a0 := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨hX0, hψs, hu, ha, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have hXc : TyCode k (semK S k X) := RE2.tyCode hW D.ha0
  have F := hfill_typed hS hX0 hψs hu ha hside
  have hF : HasTy S (k + 1) .one [] (Tm.hfill X ψ u a0) X.dshift := minimal_to_spec F.1
  have hv0 : RE2 S k X a0 a0 := RE2.trans hW hXX D.ha0 (RE2.symm hW hXX D.ha0)
  have h := hfill_zero_pt hW hψs hXc (RT2.refl hW hXc hXX) hF (D.tubeL hW hXX) hv0 (fun k' σ hh => by
    have hXσ := RT2.isub hW hXc hXX σ
    exact RE2.trans hW hXσ (D.bd k' σ hh) (RE2.symm hW hXσ (RE2.isub hW D.ha0 σ))) (ISub.id k)
  rw [isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW D.hty)), isub_cons_id_dinst hW (closed_of_ty hW hF) .zero trivial,
    isub_id_of_closed (closed_of_ty hW (RE2.typed D.ha0).1)] at h
  exact h


/-- The boundary of the base composition of `hcompGlue`, against the right base. -/
theorem GHD.bdL {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hor : I.Entails .one (.or ψ φ)) :
    RE2 S k A (.split ψ (.unglue φ e (u.dinst .zero)) φ (.app (.fst e) ((Tm.hfill T ψ u a0).dinst .zero)))
      (.unglue φ' e' a0') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hφs' := (glue_data hW hG').1
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA : RT2 S k A A := RT2.refl hW hXA D.hA
  have parts := hcompGlue_parts hS (spec_to_minimal hW D.hty) (spec_to_minimal hW hG)
  have hsp := hcomp_tube_typed' hW (minimal_to_spec parts.2.1) .zero trivial
    ((holds_iff_entails (show (I.or ψ φ).Scoped k from ⟨hψs, hφs⟩)).2 hor)
  rw [glueTube_d] at hsp
  have hhold : ∀ {k'} {x : I} (σ : ISub k' k), x.Scoped k → I.Entails .one (x.subst σ.τ) →
      (ival (idEnv k') (x.subst σ.τ)).holds := fun σ hx h => (holds_iff_entails (I.scoped_subst hx σ.sc)).2 h
  refine RE2_split_l hW hψs hφs hor hAA hsp (RE2.typed (D.ug0 hW D.ha0)).2.1 (fun k' σ hψσ => ?_)
    (fun k' σ hφσ => ?_)
  · have := D.ug hW σ (D.bd k' σ (hhold σ hψs hψσ))
    simp only [isub_unglue, isub_dinst]
    exact this
  · have Dσ := D.isub hW σ
    have hGσ : HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) :=
      HasTy.isubS hW hG σ
    have hAσ := RT2.isub hW hXA hAA σ
    have hTσ := (Dσ.fibRel hW hφσ).1
    have hTTσ := RT2.refl hW (RE2.tyCode hW ((Dσ.fibKD hW hφσ).ha0)) hTσ
    have z := (Dσ.fibKD hW hφσ).zeroPt hW hTσ
    have f := RE2_glue_fib hW hGσ hφσ hTTσ (RE2.isub hW D.ha0 σ)
    have happ := RE2_equiv_app hW (D.hE k' σ (hhold σ hφs hφσ)) (RE2.trans hW hTTσ z f)
    have hφσ' : I.Entails .one (φ'.subst σ.τ) := ent_trans hφσ (ent_subst D.f12 σ.τ)
    obtain ⟨l2, hG2, eG2⟩ := glue_annot_eq hW hGσ (I.scoped_subst hφs' σ.sc) (ent_subst D.f12 σ.τ)
      (ent_subst D.f21 σ.τ) Dσ.ee
    have he'σ : HasTy S k' .one [] (e'.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := by
      have := face_ty hW hφs (HasTy.eqL D.ee) σ (hhold σ hφs hφσ); rwa [isub_equiv] at this
    have hug := RE2.isub hW (D.ug0 hW D.ha0) σ
    have hst := stable_unglueFace hW hφσ' (RE2.typed hug).2.1 ((RE2.typed (RE2.isub hW D.ha0 σ)).2.1.conv eG2)
      (HasTy.isubS hW hA0 σ) he'σ (TyEq.refl _)
    simp only [isub_app, isub_fst, isub_dinst, isub_hfill]
    exact RE2.expandR hW hAσ (RE2.typed happ).1 (RE2.typed hug).2.1 hst happ

/-- The left base, against the boundary of the right base composition of `hcompGlue`. -/
theorem GHD.bdR {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hor : I.Entails .one (.or ψ φ)) :
    RE2 S k A (.unglue φ e a0)
      (.split ψ' (.unglue φ' e' (u'.dinst .zero)) φ' (.app (.fst e') ((Tm.hfill T' ψ' u' a0').dinst .zero))) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hφs' := (glue_data hW hG').1
  obtain ⟨l1', ⟨hG'0, hψs', hu', ha0', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty') rfl
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA : RT2 S k A A := RT2.refl hW hXA D.hA
  have hAA' : TyEq S k A A' := (Comp2_ty_base D.hA).2.2.2.2.2
  have parts' := hcompGlue_parts hS (HasTy0.hcomp hG'0 hψs' hu' ha0' hside') (spec_to_minimal hW hG')
  have hor' : I.Entails .one (.or ψ' φ') :=
    ent_trans hor (ent_or_elim (ent_trans D.p12 (ent_or_left _ _)) (ent_trans D.f12 (ent_or_right _ _)))
  have hsp' := hcomp_tube_typed' hW ((minimal_to_spec parts'.2.1).tyConv (TyEq.symm hAA')) .zero trivial
    ((holds_iff_entails (show (I.or ψ' φ').Scoped k from ⟨hψs', hφs'⟩)).2 hor')
  rw [glueTube_d] at hsp'
  have hhold : ∀ {k'} {x : I} (σ : ISub k' k), x.Scoped k → I.Entails .one (x.subst σ.τ) →
      (ival (idEnv k') (x.subst σ.τ)).holds := fun σ hx h => (holds_iff_entails (I.scoped_subst hx σ.sc)).2 h
  have hψs : ψ.Scoped k := (gen_hcomp (spec_to_minimal hW D.hty) rfl).choose_spec.1.2.1
  refine RE2_split_r hW hψs' hφs' hor' hAA hsp' (RE2.typed (D.ug0 hW D.ha0)).1 (fun k' σ hψσ' => ?_)
    (fun k' σ hφσ' => ?_)
  · have := D.ug hW σ (D.bd' k' σ (hhold σ hψs (ent_trans hψσ' (ent_subst D.p21 σ.τ))))
    simp only [isub_unglue, isub_dinst]
    exact this
  · have hφσ : I.Entails .one (φ.subst σ.τ) := ent_trans hφσ' (ent_subst D.f21 σ.τ)
    have Dσ := D.isub hW σ
    have hAσ := RT2.isub hW hXA hAA σ
    have hTσ := (Dσ.fibRel hW hφσ).1
    have hTTσ := RT2.refl hW (RE2.tyCode hW ((Dσ.fibKD hW hφσ).ha0)) hTσ
    have z := (Dσ.fibKD hW hφσ).zeroPt hW hTσ
    have fp := Dσ.fillPt hW hφσ (r := .zero) (r' := .zero) trivial trivial (I_eq_refl _)
    have happ := RE2_equiv_app hW (D.hE k' σ (hhold σ hφs hφσ)) (RE2.trans hW hTTσ (RE2.symm hW hTTσ z) fp)
    have heσ : HasTy S k' .one [] (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := by
      have := face_ty hW hφs he0 σ (hhold σ hφs hφσ); rwa [isub_equiv] at this
    have hug := RE2.isub hW (D.ug0 hW D.ha0) σ
    have hst := stable_unglueFace hW hφσ (RE2.typed hug).1 (RE2.typed (RE2.isub hW D.ha0 σ)).1
      (HasTy.isubS hW hA0 σ) heσ (TyEq.refl _)
    simp only [isub_app, isub_fst, isub_dinst, isub_hfill]
    exact RE2.expandL hW hAσ (RE2.typed hug).1 (RE2.typed happ).2.1 hst happ

/-- The composition data of the base of `hcompGlue`. -/
theorem GHD.baseKD {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') :
    KD S k A A' (.or ψ φ) (.or ψ' φ') (KubusCore.Meta.glueTube φ T e ψ u a0)
      (KubusCore.Meta.glueTube φ' T' e' ψ' u' a0') (.unglue φ e a0) (.unglue φ' e' a0') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  obtain ⟨hφs', lA', hA0', he0'⟩ := glue_data hW hG'
  obtain ⟨-, ⟨hG00, hψs, hu, ha0t, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  obtain ⟨l1', ⟨hG'0, hψs', hu', ha0', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty') rfl
  have hty'G' : HasTy0 S k .one [] (.hcomp (.glue A' φ' T' e') ψ' u' a0') (.glue A' φ' T' e') :=
    HasTy0.hcomp hG'0 hψs' hu' ha0' hside'
  have parts := hcompGlue_parts hS (spec_to_minimal hW D.hty) (spec_to_minimal hW hG)
  have parts' := hcompGlue_parts hS hty'G' (spec_to_minimal hW hG')
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  have hG'K : IsTyK S k (.glue A' φ' T' e') := ⟨l', .inl hG'⟩
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA : RT2 S k A A := RT2.refl hW hXA D.hA
  have hAA' : TyEq S k A A' := (Comp2_ty_base D.hA).2.2.2.2.2
  -- the judgmental equality of the bases, through `unglue` of the compositions
  have eG := EqTm.hcompGlue D.hty hA0 he0
  have eG' := EqTm.hcompGlue (minimal_to_spec hty'G') hA0' he0'
  rw [KubusCore.Meta.hcompGlue_eq] at eG eG'
  have v1 := EqTm.glueBeta (unglue_ty hW hGK ⟨lA, hA0, he0⟩ (HasTy.eqR eG)) (minimal_to_spec parts.2.1)
  have v2 := EqTm.unglue (unglue_ty hW hGK ⟨lA, hA0, he0⟩ D.hty) (unglue_ty hW hGK ⟨lA, hA0, he0⟩ (HasTy.eqR eG))
    (ent_refl _) (ent_refl _) (EqTm.refl he0) eG
  have v3 := EqTm.unglue (unglue_ty hW hGK ⟨lA, hA0, he0⟩ D.hty)
    ((unglue_ty hW hG'K ⟨lA', hA0', he0'⟩ (minimal_to_spec hty'G')).tyConv (TyEq.symm hAA')) D.f12 D.f21 D.ee.symm
    D.heq
  have v4 := EqTm.unglue (unglue_ty hW hG'K ⟨lA', hA0', he0'⟩ (minimal_to_spec hty'G'))
    (unglue_ty hW hG'K ⟨lA', hA0', he0'⟩ (HasTy.eqR eG')) (ent_refl _) (ent_refl _) (EqTm.refl he0') eG'
  have v5 := EqTm.glueBeta (unglue_ty hW hG'K ⟨lA', hA0', he0'⟩ (HasTy.eqR eG')) (minimal_to_spec parts'.2.1)
  have heqb := v1.symm.trans (v2.symm.trans (v3.trans ((v4.trans v5).tyConv (TyEq.symm hAA'))))
  -- the judgmental equality of the base tubes
  obtain ⟨l0, ⟨-, -, hT0, -⟩, -⟩ := gen_glue hS (spec_to_minimal hW hG) rfl
  obtain ⟨l0', ⟨-, -, hT0', -⟩, -⟩ := gen_glue hS (spec_to_minimal hW hG') rfl
  have hφc : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  have hφψc : (cof (cof .one φ) ψ).Scoped k := ⟨hφc, hψs⟩
  have hTT0 : T = T' ∨ ∃ l, EqTm0 S k (cof .one φ) [] T T' (.univ l) := by
    rcases D.gG with e1 | ⟨l2, e2⟩
    · left; simp only [Tm.glue.injEq] at e1; exact e1.2.2.1
    · right; refine ⟨l2, spec_to_minimal_eq hW ?_⟩
      have r1 := EqTm.restrict hφc (ent_and_left _ _) e2
      have g1 := EqTm.glueFace (ent_and_right _ _) (HasTy.eqL r1)
      have g2 := EqTm.glueFace (ent_trans (ent_and_right _ _) D.f12) (HasTy.eqR r1)
      exact g1.symm.trans (r1.trans g2)
  have hGT0 : EqTm0 S k (cof .one φ) [] (.glue A φ T e) T (.univ l) :=
    spec_to_minimal_eq hW (EqTm.glueFace (ent_and_right _ _) (HasTy.restrict hφc (ent_and_left _ _) hG))
  have eψ : I.Entails (cof (cof .one φ) ψ) (cof .one ψ) :=
    ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
  have hsideφ : EqTm0 S k (cof (cof .one φ) ψ) [] (u.dinst .zero) a0 T :=
    EqTm0.conv (EqTm0.restrict hφψc eψ hside) (EqTm0.restrict hφψc (ent_and_left _ _) hGT0)
  have F := hfill_typed hS hT0 hψs parts.2.2.2.1 parts.2.2.2.2 hsideφ
  -- the right filler, in the context of the left face
  have hφc' : (cof .one φ').Scoped k := ⟨trivial, hφs'⟩
  have hφψc' : (cof (cof .one φ') ψ').Scoped k := ⟨hφc', hψs'⟩
  have hG'T0 : EqTm0 S k (cof .one φ') [] (.glue A' φ' T' e') T' (.univ l') :=
    spec_to_minimal_eq hW (EqTm.glueFace (ent_and_right _ _) (HasTy.restrict hφc' (ent_and_left _ _) hG'))
  have eψ' : I.Entails (cof (cof .one φ') ψ') (cof .one ψ') :=
    ent_and_intro (ent_trans (ent_and_left _ _) (ent_and_left _ _)) (ent_and_right _ _)
  have hsideφ' : EqTm0 S k (cof (cof .one φ') ψ') [] (u'.dinst .zero) a0' T' :=
    EqTm0.conv (EqTm0.restrict hφψc' eψ' hside') (EqTm0.restrict hφψc' (ent_and_left _ _) hG'T0)
  have F' := hfill_typed hS hT0' hψs' parts'.2.2.2.1 parts'.2.2.2.2 hsideφ'
  have hsh : (cof .one φ).shift.Scoped (k + 1) := KubusCore.I.scoped_shift hφc
  have hF' : HasTy0 S (k + 1) (cof .one φ).shift [] (Tm.hfill T' ψ' u' a0') T.dshift := by
    have h1 := HasTy0.restrict hsh (ent_shift (ent_and_mono (ent_refl _) D.f12)) F'.1
    rcases hTT0 with rfl | ⟨l2, e2⟩
    · exact h1
    · exact HasTy0.conv h1 (EqTm0.symm (EqTm0.dwk hS e2))
  have huuT : EqTm0 S (k + 1) (cof (cof .one φ) ψ).shift [] u u' T.dshift :=
    EqTm0.conv (EqTm0.restrict (KubusCore.I.scoped_shift hφψc) (ent_shift eψ) (spec_to_minimal_eq hW D.hteq))
      (EqTm0.restrict (KubusCore.I.scoped_shift hφψc) (ent_shift (ent_and_left _ _)) (EqTm0.dwk hS hGT0))
  have hv0T : EqTm0 S k (cof .one φ) [] a0 a0' T :=
    EqTm0.conv (EqTm0.restrict hφc (ent_and_left _ _) (spec_to_minimal_eq hW (RE2.typed D.ha0).2.2)) hGT0
  have hFF0 := hfill_congΦ hW F.1 hF' hTT0 huuT hv0T D.p12 D.p21
  have hAA0 : A = A' ∨ ∃ l, EqTm0 S k .one [] A A' (.univ l) := by
    rcases hAA' with e1 | ⟨l2, e2⟩
    · exact .inl e1
    · exact .inr ⟨l2, spec_to_minimal_eq hW e2⟩
  have hteqb := minimal_to_spec_eq (glueTube_eq hW parts.2.2.1 parts'.2.2.1 hAA0 (spec_to_minimal_eq hW D.hteq)
    (spec_to_minimal_eq hW D.ee.symm) hFF0 D.p12 D.f12 D.f21)
  have hor_s : (I.or ψ φ).Scoped k := ⟨hψs, hφs⟩
  have hent : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') ((I.or ψ φ).subst σ.τ)).holds →
      I.Entails .one (I.or (ψ.subst σ.τ) (φ.subst σ.τ)) := fun σ hh =>
    (holds_iff_entails (I.scoped_subst hor_s σ.sc)).1 hh
  refine ⟨minimal_to_spec parts.2.1, (minimal_to_spec parts'.2.1).tyConv (TyEq.symm hAA'), heqb, hteqb,
    ent_or_elim (ent_trans D.p12 (ent_or_left _ _)) (ent_trans D.f12 (ent_or_right _ _)),
    ent_or_elim (ent_trans D.p21 (ent_or_left _ _)) (ent_trans D.f21 (ent_or_right _ _)),
    fun k' σ r r' hr hr' hE hh => ?_, D.ug0 hW D.ha0, fun k' σ hh => ?_, fun k' σ hh => ?_⟩
  · rw [glueTube_isub, glueTube_isub, glueTube_d, glueTube_d]
    exact (D.isub hW σ).tubePt hW (hent σ hh) hr hr' hE
  · rw [glueTube_isub, glueTube_d]
    exact (D.isub hW σ).bdL hW (hent σ hh)
  · rw [glueTube_isub, glueTube_d]
    exact (D.isub hW σ).bdR hW (hent σ hh)

/-- The base of `hcompGlue`. -/
theorem GHD.base {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') :
    RE2 S k A (.hcomp A (.or ψ φ) (KubusCore.Meta.glueTube φ T e ψ u a0) (.unglue φ e a0))
      (.hcomp A' (.or ψ' φ') (KubusCore.Meta.glueTube φ' T' e' ψ' u' a0') (.unglue φ' e' a0')) := by
  obtain ⟨l, hG⟩ := D.hG
  have hc := closed_of_ty hW hG
  simp only [Tm.closedB, Bool.and_eq_true] at hc
  have h := D.kA k (ISub.id k) A' (by rw [isub_id_of_closed hc.1.1.1]; exact D.hA)
  rw [isub_id_of_closed hc.1.1.1] at h
  exact (D.baseKD hW).kan h


/-- A filler at `1` is the composition. -/
theorem KD.onePt {X X' : Tm} {ψ ψ' : I} {u u' a0 a0' : Tm} (D : KD S k X X' ψ ψ' u u' a0 a0')
    (hXX : RT2 S k X X') (hK : ∀ k3 (τ : ISub k3 k), KanH2 S k3 (X.isub τ) (X.isub τ)) :
    RE2 S k X ((Tm.hfill X ψ u a0).dinst .one) (.hcomp X ψ u a0) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l1, ⟨hX0, hψs, hu, ha, hside⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have hXc : TyCode k (semK S k X) := RE2.tyCode hW D.ha0
  have F := hfill_typed hS hX0 hψs hu ha hside
  have hF : HasTy S (k + 1) .one [] (Tm.hfill X ψ u a0) X.dshift := minimal_to_spec F.1
  have hv0 : RE2 S k X a0 a0 := RE2.trans hW hXX D.ha0 (RE2.symm hW hXX D.ha0)
  have h := hfill_one_pt hW hψs hXc (RT2.refl hW hXc hXX) hK D.hty hF (D.tubeL hW hXX) hv0 (fun k' σ hh => by
    have hXσ := RT2.isub hW hXc hXX σ
    exact RE2.trans hW hXσ (D.bd k' σ hh) (RE2.symm hW hXσ (RE2.isub hW D.ha0 σ))) (ISub.id k)
  rw [isub_id_of_closed (closed_of_isTyK hW (isTyK_of_ty hW D.hty)), isub_cons_id_dinst hW (closed_of_ty hW hF) .one trivial,
    isub_id_of_closed (closed_of_ty hW D.hty)] at h
  exact h

/-- Composition in the fibers is Kan on the diagonal, where the face holds. -/
theorem GHD.kTd {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hφe : I.Entails .one φ) :
    ∀ k3 (τ : ISub k3 k), KanH2 S k3 (T.isub τ) (T.isub τ) := by
  obtain ⟨l, hG⟩ := D.hG
  have hφs := (glue_data hW hG).1
  intro k3 τ
  have hh : (ival (idEnv k3) (φ.subst τ.τ)).holds :=
    (holds_iff_entails (I.scoped_subst hφs τ.sc)).2 (ent_one_subst hφe τ.τ)
  have hX : TyCode k3 (semK S k3 (T.isub τ)) := tyCode_of_univ hW (glue_fiber_ty hW hG τ hh).choose_spec.1
  exact D.kT k3 τ hh _ (RT2.refl hW hX (D.hT k3 τ hh))

/-- The base of `hcompGlue` agrees with the image of its fiber, where the face of the Glue type holds. -/
theorem GHD.hat {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hφe : I.Entails .one φ) :
    RE2 S k A (.hcomp A (.or ψ φ) (KubusCore.Meta.glueTube φ T e ψ u a0) (.unglue φ e a0))
      (.app (.fst e) (.hcomp T ψ u a0)) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA : RT2 S k A A := RT2.refl hW hXA D.hA
  have parts := hcompGlue_parts hS (spec_to_minimal hW D.hty) (spec_to_minimal hW hG)
  have hor : I.Entails .one (.or ψ φ) := ent_trans hφe (ent_or_right _ _)
  have htyb := minimal_to_spec parts.2.1
  have hst := stable_hcompFace hW hor htyb
  have hsp := hcomp_tube_typed' hW htyb .one trivial
    ((holds_iff_entails (show (I.or ψ φ).Scoped k from ⟨hψs, hφs⟩)).2 hor)
  have hhold : ∀ {k'} {x : I} (σ : ISub k' k), x.Scoped k → I.Entails .one (x.subst σ.τ) →
      (ival (idEnv k') (x.subst σ.τ)).holds := fun σ hx h => (holds_iff_entails (I.scoped_subst hx σ.sc)).2 h
  have K0 := D.fibKD hW hφe
  have heL : HasTy S k .one [] e (Tm.equiv T A) :=
    HasTy.restrict (Φ := cof .one φ) trivial (ent_and_intro (ent_refl _) hφe) he0
  have hx : HasTy S k .one [] (.app (.fst e) (.hcomp T ψ u a0)) A :=
    minimal_to_spec (app_fst_equiv (spec_to_minimal hW heL) (spec_to_minimal hW K0.hty))
  refine RE2.expandL hW hAA htyb hx hst ?_
  rw [glueTube_d] at hsp ⊢
  refine RE2_split_l hW hψs hφs hor hAA hsp hx (fun k' σ hψσ => ?_) (fun k' σ hφσ => ?_)
  · have Dσ := D.isub hW σ
    have hφσ : I.Entails .one (φ.subst σ.τ) := ent_one_subst hφe σ.τ
    have K := Dσ.fibKD hW hφσ
    have R := Dσ.fibRel hW hφσ
    have hTTσ := RT2.refl hW (RE2.tyCode hW K.ha0) R.1
    have hAσ := RT2.isub hW hXA hAA σ
    have hGσ : HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) :=
      HasTy.isubS hW hG σ
    have tub := D.tube k' σ .one .one trivial trivial (I_eq_refl _) (hhold σ hψs hψσ)
    have yT0 := RE2_glue_fib hW hGσ hφσ hTTσ tub
    have yT := RE2.trans hW hTTσ yT0 (RE2.symm hW hTTσ yT0)
    have hstT := stable_hcompFace hW hψσ K.hty
    have ty := RE2.expandR hW hTTσ (RE2.typed yT).1 K.hty hstT yT
    have happ := RE2_equiv_app hW (D.hEL k' σ (hhold σ hφs hφσ)) ty
    have ugσ := D.ug hW σ tub
    have heσ : HasTy S k' .one [] (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := by
      have := face_ty hW hφs he0 σ (hhold σ hφs hφσ); rwa [isub_equiv] at this
    have hstU := stable_unglueFace hW hφσ (RE2.typed ugσ).1 (RE2.typed tub).1 (HasTy.isubS hW hA0 σ) heσ
      (TyEq.refl _)
    simp only [isub_unglue, isub_dinst, isub_app, isub_fst, isub_hcomp, I.subst]
    exact RE2.expandL hW hAσ (RE2.typed ugσ).1 (RE2.typed happ).2.1 hstU happ
  · have Dσ := D.isub hW σ
    have K := Dσ.fibKD hW hφσ
    have R := Dσ.fibRel hW hφσ
    simp only [isub_app, isub_fst, isub_dinst, isub_hfill, isub_hcomp, I.subst]
    exact RE2_equiv_app hW (D.hEL k' σ (hhold σ hφs hφσ)) (K.onePt hW R.1 (Dσ.kTd hW hφσ))


/-- `hcompGlue` at related Glue types whose face does not hold. -/
theorem GHD.core {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hn : ¬ (ival (idEnv k) φ).holds) :
    RE2 S k (.glue A φ T e) (Tm.hcompGlue A φ T e ψ u a0) (Tm.hcompGlue A' φ' T' e' ψ' u' a0') := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨l', hG'⟩ := D.hG'
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  obtain ⟨hφs', lA', hA0', he0'⟩ := glue_data hW hG'
  obtain ⟨l1', ⟨hG'0, hψs', hu', ha0', hside'⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty') rfl
  have hty'G' : HasTy0 S k .one [] (.hcomp (.glue A' φ' T' e') ψ' u' a0') (.glue A' φ' T' e') :=
    HasTy0.hcomp hG'0 hψs' hu' ha0' hside'
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA : RT2 S k A A := RT2.refl hW hXA D.hA
  have eG := EqTm.hcompGlue D.hty hA0 he0
  have eG' := EqTm.hcompGlue (minimal_to_spec hty'G') hA0' he0'
  have hhold : ∀ {k'} {x : I} (σ : ISub k' k), x.Scoped k → (ival (idEnv k') (x.subst σ.τ)).holds →
      I.Entails .one (x.subst σ.τ) := fun σ hx h => (holds_iff_entails (I.scoped_subst hx σ.sc)).1 h
  have ha : ∀ k' (σ : ISub k' k), RE2 S k' (A.isub σ)
      ((Tm.hcomp A (.or ψ φ) (KubusCore.Meta.glueTube φ T e ψ u a0) (.unglue φ e a0)).isub σ)
      ((Tm.hcomp A' (.or ψ' φ') (KubusCore.Meta.glueTube φ' T' e' ψ' u' a0') (.unglue φ' e' a0')).isub σ) := by
    intro k' σ
    rw [isub_hcomp, isub_hcomp, glueTube_isub, glueTube_isub, isub_unglue, isub_unglue]
    exact (D.isub hW σ).base hW
  have ht : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) ((Tm.hcomp T ψ u a0).isub σ) ((Tm.hcomp T' ψ' u' a0').isub σ) := by
    intro k' σ hh
    rw [isub_hcomp, isub_hcomp]
    exact (D.isub hW σ).fib hW (hhold σ hφs hh)
  have hat : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((Tm.hcomp A (.or ψ φ) (KubusCore.Meta.glueTube φ T e ψ u a0) (.unglue φ e a0)).isub σ)
        (.app (.fst (e.isub σ)) ((Tm.hcomp T ψ u a0).isub σ)) := by
    intro k' σ hh
    rw [isub_hcomp, isub_hcomp, glueTube_isub, isub_unglue]
    exact (D.isub hW σ).hat hW (hhold σ hφs hh)
  rw [KubusCore.Meta.hcompGlue_eq, KubusCore.Meta.hcompGlue_eq]
  rw [KubusCore.Meta.hcompGlue_eq] at eG eG'
  refine RE2_glueEl_intro hW hG hn ⟨HasTy.eqR eG, (HasTy.eqR eG').tyConv (TyEq.symm D.gG),
      eG.symm.trans (D.heq.trans (eG'.tyConv (TyEq.symm D.gG)))⟩ D.f12 D.f21 D.ee D.hGG
    (fun k' σ => RT2.isub hW hXA hAA σ)
    (fun k' σ hh => RT2.refl hW (tyCode_of_univ hW (glue_fiber_ty hW hG σ hh).choose_spec.1) (D.hT k' σ hh))
    ha ht hat (fun k' σ hh => ?_)
  have hAσ := RT2.isub hW hXA hAA σ
  have hTσ := RT2.refl hW (tyCode_of_univ hW (glue_fiber_ty hW hG σ hh).choose_spec.1) (D.hT k' σ hh)
  exact RE2.trans hW hAσ (RE2.symm hW hAσ (ha k' σ))
    (RE2.trans hW hAσ (hat k' σ hh) (RE2_equiv_app hW (D.hEL k' σ hh) (ht k' σ hh)))


/-- `hcompGlue` is its tube's end, where the face of the composition holds. -/
theorem GHD.bdry {A T e A' T' e' : Tm} {φ φ' ψ ψ' : I} {u u' a0 a0' : Tm}
    (D : GHD S k A T e A' T' e' φ φ' ψ ψ' u u' a0 a0') (hn : ¬ (ival (idEnv k) φ).holds)
    (hψe : I.Entails .one ψ) :
    RE2 S k (.glue A φ T e) (Tm.hcompGlue A φ T e ψ u a0) (u.dinst .one) := by
  have hS := sigClosed_of_wfSig hW
  obtain ⟨l, hG⟩ := D.hG
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW D.hty) rfl
  have hXA : TyCode k (semK S k A) := tyCode_of_univ hW hA0
  have hAA : RT2 S k A A := RT2.refl hW hXA D.hA
  have hAAσ : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A.isub σ) := fun k' σ => RT2.isub hW hXA hAA σ
  have hTT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ) :=
    fun k' σ hh => RT2.refl hW (tyCode_of_univ hW (glue_fiber_ty hW hG σ hh).choose_spec.1) (D.hT k' σ hh)
  have hhold : ∀ {k'} {x : I} (σ : ISub k' k), x.Scoped k → (ival (idEnv k') (x.subst σ.τ)).holds →
      I.Entails .one (x.subst σ.τ) := fun σ hx h => (holds_iff_entails (I.scoped_subst hx σ.sc)).1 h
  have t1 := D.tube0 hW hψe (r := .one) (r' := .one) trivial trivial (I_eq_refl _)
  have hyG := RE2.trans hW D.hGG t1 (RE2.symm hW D.hGG t1)
  have hy := (RE2.typed hyG).1
  have parts := hcompGlue_parts hS (spec_to_minimal hW D.hty) (spec_to_minimal hW hG)
  have eG := EqTm.hcompGlue D.hty hA0 he0
  rw [KubusCore.Meta.hcompGlue_eq] at eG ⊢
  have eF := EqTm.hcompFace hψe D.hty
  have eEta := EqTm.glueEta hy
  have eta := RE2_glue_eta hW hG hn hyG eEta hφs (ent_refl _) (ent_refl _) (EqTm.refl he0) hAAσ hTT D.hEL
  -- the base against the `unglue` of the tube's end
  have hug := RE2_unglue_gen hW hG hyG (unglue_ty hW ⟨l, .inl hG⟩ ⟨lA, hA0, he0⟩ hy)
    (unglue_ty hW ⟨l, .inl hG⟩ ⟨lA, hA0, he0⟩ hy) hφs (ent_refl _) (ent_refl _) (EqTm.refl he0) hAAσ hTT D.hEL
  have hor : I.Entails .one (.or ψ φ) := ent_trans hψe (ent_or_left _ _)
  have htyb := minimal_to_spec parts.2.1
  have hsp := hcomp_tube_typed' hW htyb .one trivial
    ((holds_iff_entails (show (I.or ψ φ).Scoped k from ⟨hψs, hφs⟩)).2 hor)
  have s1 := stable_hcompFace hW hor htyb
  rw [glueTube_d] at hsp s1
  have s2 := stable_splitL hW hψe hsp
  have hb : RE2 S k A (.hcomp A (.or ψ φ) (KubusCore.Meta.glueTube φ T e ψ u a0) (.unglue φ e a0))
      (.unglue φ e (u.dinst .one)) :=
    RE2.expandL hW hAA htyb (RE2.typed hug).1 s1 (RE2.expandL hW hAA hsp (RE2.typed hug).1 s2 hug)
  have intro := RE2_glueEl_intro hW hG hn ⟨HasTy.eqR eG, HasTy.eqR eEta, eG.symm.trans (eF.trans eEta)⟩
    (ent_refl _) (ent_refl _) (EqTm.refl he0) D.hGG hAAσ hTT (fun k' σ => RE2.isub hW hb σ)
    (fun k' σ hh => ?_) (fun k' σ hh => ?_) (fun k' σ hh => ?_)
  · exact RE2.trans hW D.hGG intro (RE2.symm hW D.hGG eta)
  · -- the fiber composition, against the tube's end
    have hφσ := hhold σ hφs hh
    have K := (D.isub hW σ).fibKD hW hφσ
    have hGσ : HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) :=
      HasTy.isubS hW hG σ
    have yy := RE2_glue_fib hW hGσ hφσ (hTT k' σ hh) (RE2.isub hW hyG σ)
    have st := stable_hcompFace hW (ent_one_subst hψe σ.τ) K.hty
    simp only [isub_dinst, I.subst] at yy
    simp only [isub_hcomp, isub_dinst, I.subst]
    exact RE2.expandL hW (hTT k' σ hh) K.hty (RE2.typed yy).1 st yy
  · have := (D.isub hW σ).hat hW (hhold σ hφs hh)
    rw [isub_hcomp, isub_hcomp, glueTube_isub, isub_unglue]
    exact this
  · -- the `unglue` of the tube's end, against the image of the tube's end
    have hφσ := hhold σ hφs hh
    have hGσ : HasTy S k' .one [] (.glue (A.isub σ) (φ.subst σ.τ) (T.isub σ) (e.isub σ)) (.univ l) :=
      HasTy.isubS hW hG σ
    have yy := RE2_glue_fib hW hGσ hφσ (hTT k' σ hh) (RE2.isub hW hyG σ)
    have happ := RE2_equiv_app hW (D.hEL k' σ hh) yy
    have heσ : HasTy S k' .one [] (e.isub σ) (Tm.equiv (T.isub σ) (A.isub σ)) := by
      have := face_ty hW hφs he0 σ hh; rwa [isub_equiv] at this
    have hugσ := RE2.isub hW hug σ
    have st := stable_unglueFace hW hφσ (RE2.typed hugσ).1 (RE2.typed (RE2.isub hW hyG σ)).1
      (HasTy.isubS hW hA0 σ) heσ (TyEq.refl _)
    exact RE2.expandL hW (hAAσ k' σ) (RE2.typed hugσ).1 (RE2.typed happ).2.1 st happ

end

end Model.Whnf
