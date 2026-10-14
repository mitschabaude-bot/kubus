import Model.Whnf.Closed2

/-!
# Closed Glue inversion, expansion and eta
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' : ℕ}

variable (hW : WfSig S)
include hW

/-- Related Glue types whose faces do not hold have related bases, and related fibers and
equivalences where the face holds. -/
theorem RT2_glue_inv {A T e A' T' e' : Tm} {φ φ' : I} {l l' : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hG' : HasTy S k .one [] (.glue A' φ' T' e') (.univ l'))
    (hn : ¬ I.Entails .one φ) (hn' : ¬ I.Entails .one φ') (h : RT2 S k (.glue A φ T e) (.glue A' φ' T' e')) :
    RT2 S k A A' ∧ ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RT2 S k' (T.isub σ) (T'.isub σ) ∧ RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ) := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hnh : ¬ (ival (idEnv k) φ).holds := fun hh => hn ((holds_iff_entails hφs).1 hh)
  have hnf : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  unfold RT2 at h
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hnf] at h
  obtain ⟨-, hloc, -, -⟩ := h
  have h0 := hloc k (ISub.id k)
  unfold glueLocT at h0
  rw [if_neg (by rw [Hom.id_comp, ISub.hom_id, (isCof_ival_face _ _).restr_id]; exact hnf)] at h0
  obtain ⟨A1, φ1, T1, e1, A1', φ1', T1', e1', r1, r2, -, -, -, -, hAA, hfib⟩ := h0
  rw [isub_id_of_closed (closed_of_ty hW hG)] at r1
  rw [isub_id_of_closed (closed_of_ty hW hG')] at r2
  have eq1 := RedW.unique r1.1 (redT_glue_self (S := S) (k := k) (A1 := A) (T1 := T) (e1 := e) hn).1
  have eq2 := RedW.unique r2.1 (redT_glue_self (S := S) (k := k) (A1 := A') (T1 := T') (e1 := e') hn').1
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

/-- Expansion of related types along stable steps on both sides, at the level of `RT2`. -/
theorem RT2.expand2 {A A' B B' : Tm} (hX : TyCode k (semK S k A)) (hA : IsTyK S k A) (hA' : IsTyK S k A')
    (hB : IsTyK S k B) (hs : StableT S k A B) (hs' : StableT S k A' B') (h : RT2 S k B B') : RT2 S k A A' := by
  have e : semK S k B = semK S k A := by
    have := (semK_tyEq hW (hs k (ISub.id k)).2).symm
    rwa [isub_id_of_closed (closed_of_isTyK hW hA), isub_id_of_closed (closed_of_isTyK hW hB)] at this
  unfold RT2 at h ⊢
  rw [e] at h
  exact ty_expandS2 hW hX hA hA' hB hs hs' h

/-- A related pair in the fiber of a Glue type whose face holds is a related pair of the Glue type. -/
theorem RE2_glue_of_fiber {A T e : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hφe : I.Entails .one φ) (hTT : RT2 S k T T) {x y : Tm} (hxy : RE2 S k T x y) :
    RE2 S k (.glue A φ T e) x y := by
  obtain ⟨hφs, -⟩ := glue_data hW hG
  have hh : (ival (idEnv k) (φ.subst (ISub.id k).τ)).holds := by
    rw [show φ.subst (ISub.id k).τ = φ from ISub.I.subst_scoped_id hφs fun j hj => by simp [ISub.id, hj]]
    exact (holds_iff_entails hφs).2 hφe
  have hcG := closed_of_ty hW hG
  have hcT : T.closedB 0 k = true := by
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG (ISub.id k) hh
    have := closed_of_ty hW hTσ
    rwa [isub_id_of_closed (show T.closedB 0 k = true by
      simp only [Tm.closedB, Bool.and_eq_true] at hcG; exact hcG.1.2)] at this
  have := glue_fiber_conv hW hG (ISub.id k) hh (by rwa [isub_id_of_closed hcT]) (by rwa [isub_id_of_closed hcT])
  rw [isub_id_of_closed hcT, isub_id_of_closed hcG] at this
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  unfold RE2
  rw [← semK_tyEq hW (glue_face_tyEq hW hGK hφe)] at this
  exact this

/-- Related elements of a Glue type whose face does not hold: their bases agree with their fibers
through the type's equivalence, where the face holds. -/
theorem RE2_glueEl_base {A T e x y : Tm} {φ : I} {l : ℕ} (hG : HasTy S k .one [] (.glue A φ T e) (.univ l))
    (hn : ¬ (ival (idEnv k) φ).holds) (h : RE2 S k (.glue A φ T e) x y) {ψ ψ' : I} {e0 t0 a0 e0' t0' a0' : Tm}
    (hx : RedW S x (.glueEl ψ e0 t0 a0)) (hy : RedW S y (.glueEl ψ' e0' t0' a0')) :
    ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a0.isub σ) (.app (.fst (e.isub σ)) (t0.isub σ)) ∧
      RE2 S k' (A.isub σ) (a0'.isub σ) (.app (.fst (e.isub σ)) (t0'.isub σ)) := by
  obtain ⟨hφs, lA, hA0, -⟩ := glue_data hW hG
  have hnf : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hE := RE2.typed h
  unfold RE2 at h
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hnf] at h
  obtain ⟨-, -, -, hmain, -, -⟩ := h
  have hm := hmain k (ISub.id k)
  unfold glueLocE at hm
  rw [if_neg (by rw [Hom.id_comp, ISub.hom_id, (isCof_ival_face _ _).restr_id]; exact hnf)] at hm
  obtain ⟨A1, φ1, T1, e1, ψ1, e01, t01, a01, ψ1', e01', t01', a01', r1, rg, rg', -, -, -, -, -, -, -, hfibs⟩ := hm
  have hn' : ¬ I.Entails .one φ := fun h' => hn ((holds_iff_entails hφs).2 h')
  rw [isub_id_of_closed (closed_of_ty hW hG)] at r1
  rw [isub_id_of_closed (closed_of_ty hW hE.1)] at rg
  rw [isub_id_of_closed (closed_of_ty hW hE.2.1)] at rg'
  have eq1 := RedW.unique r1.1 (redT_glue_self (S := S) (k := k) (A1 := A) (T1 := T) (e1 := e) hn').1
  simp only [Tm.glue.injEq] at eq1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq1
  have ex := RedW.unique rg.1 hx
  have ey := RedW.unique rg'.1 hy
  simp only [Tm.glueEl.injEq] at ex ey
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ex
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ey
  intro k' σ hh
  have hface : (Cof.restr (ival (idEnv k) φ1).face ((Hom.id k).comp ((ISub.id k).comp σ).hom)).holds := by
    rw [ISub.id_comp, Hom.id_comp]; exact (face_holds_iff hφs σ).2 hh
  obtain ⟨-, h1, h2⟩ := hfibs k' σ hface
  rw [ISub.id_comp, Hom.id_comp, Comp2_res_el hW hA0] at h1 h2
  exact ⟨h1, h2⟩

/-- `unglue` where the face holds is the application of the equivalence, at every restriction. -/
theorem stable_unglueFace {X A T e g : Tm} {φ : I} {l : ℕ} (hφe : I.Entails .one φ)
    (hu : HasTy S k .one [] (.unglue φ e g) X) (hg : HasTy S k .one [] g (.glue A φ T e))
    (hA : HasTy S k .one [] A (.univ l)) (he : HasTy S k .one [] e (Tm.equiv T A)) (hX : TyEq S k X A) :
    StableE S k X (.unglue φ e g) (.app (.fst e) g) := by
  intro k' σ
  have hφσ : I.Entails .one (φ.subst σ.τ) := by have := ent_subst hφe σ.τ; simpa [I.subst] using this
  have hgσ := HasTy.isubS hW hg σ
  have heσ := HasTy.isubS hW he σ
  rw [isub_glue] at hgσ
  rw [isub_equiv] at heσ
  rw [isub_unglue, isub_app, isub_fst]
  refine ⟨.step (by simp [step, show I.entails .one (φ.subst σ.τ) = true from hφσ]) (.refl _), ?_⟩
  exact (EqTm.unglueFace hφσ hgσ (HasTy.isubS hW hA σ) heσ).tyConv (TyEq.symm (hX.isub hW σ))

/-- Glue eta at one stage: an element of a Glue type whose face does not hold is related to the Glue
introduction of itself and its `unglue`, for agreeing annotations. -/
theorem RE2_glue_eta {A T e e' y : Tm} {φ φ' : I} {l : ℕ}
    (hG : HasTy S k .one [] (.glue A φ T e) (.univ l)) (hn : ¬ (ival (idEnv k) φ).holds)
    (hyy : RE2 S k (.glue A φ T e) y y)
    (hyη : EqTm S k .one [] y (.glueEl φ' e' y (.unglue φ' e' y)) (.glue A φ T e))
    (hφ' : φ'.Scoped k) (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ)
    (ee' : EqTm S k (cof .one φ) [] e' e (Tm.equiv T A))
    (hAA : ∀ k' (σ : ISub k' k), RT2 S k' (A.isub σ) (A.isub σ))
    (hTT : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → RT2 S k' (T.isub σ) (T.isub σ))
    (hE : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (Tm.equiv (T.isub σ) (A.isub σ)) (e.isub σ) (e'.isub σ)) :
    RE2 S k (.glue A φ T e) y (.glueEl φ' e' y (.unglue φ' e' y)) := by
  obtain ⟨hφs, lA, hA0, he0⟩ := glue_data hW hG
  have hn' : ¬ Cof.holds (ival (idEnv k) φ).face := by rwa [← DM.holds_iff_face_holds]
  have hGK : IsTyK S k (.glue A φ T e) := ⟨l, .inl hG⟩
  have hyE := RE2.typed hyy
  have hu : HasTy S k .one [] (.unglue φ e y) A := unglue_ty hW hGK ⟨lA, hA0, he0⟩ hyE.1
  have hη := HasTy.eqR hyη
  obtain ⟨l2, hG2, eG2⟩ := glue_annot_eq hW hG hφ' h12 h21 ee'
  have hy2 : HasTy S k .one [] y (.glue A φ' T e') := hyE.1.conv eG2
  have c21 : I.Entails (cof .one φ') (cof .one φ) :=
    ent_and_intro (ent_and_left _ _) (ent_trans (ent_and_right _ _) h21)
  have he0' : HasTy S k (cof .one φ') [] e' (Tm.equiv T A) :=
    HasTy.restrict (show (cof .one φ').Scoped k from ⟨trivial, hφ'⟩) c21 (HasTy.eqL ee')
  have hu' : HasTy S k .one [] (.unglue φ' e' y) A := unglue_ty hW ⟨l2, .inl hG2⟩ ⟨lA, hA0, he0'⟩ hy2
  have hΦ : (cof .one φ).Scoped k := ⟨trivial, hφs⟩
  have hUA := RE2_unglue_and hW hG hn hyy hu hu' hφ' h12 h21 ee' hAA hTT hE
  have hent : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds → I.Entails .one (φ.subst σ.τ) :=
    fun σ hh => (holds_iff_entails (I.scoped_subst hφs σ.sc)).1 hh
  have hne : ∀ {k'} (σ : ISub k' k), ¬ (ival (idEnv k') (φ.subst σ.τ)).holds → ¬ I.Entails .one (φ.subst σ.τ) :=
    fun σ hh h => hh ((holds_iff_entails (I.scoped_subst hφs σ.sc)).2 h)
  have hXA : ∀ k' (σ : ISub k' k), TyCode k' (semK S k' (A.isub σ)) := fun k' σ =>
    tyCode_of_univ hW (HasTy.isubS hW hA0 σ)
  have hησ : ∀ {k'} (σ : ISub k' k), HasTy S k' .one []
      (.glueEl (φ'.subst σ.τ) (e'.isub σ) (y.isub σ) ((Tm.unglue φ' e' y).isub σ)) ((Tm.glue A φ T e).isub σ) :=
    fun σ => HasTy.isubS hW hη σ
  have ee'σ : ∀ {k'} (σ : ISub k' k), EqTm S k' (cof .one (φ.subst σ.τ)) [] (e'.isub σ) (e.isub σ)
      (Tm.equiv (T.isub σ) (A.isub σ)) := fun σ => by
    have := EqTm.isubF hW hΦ ee' σ; rwa [isub_equiv] at this
  have hyy' := hyy
  unfold RE2 at hyy'
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
    at hyy'
  obtain ⟨-, hmem, -, hmain, hcoh, -⟩ := hyy'
  -- the fiber relation at the Glue type, as a relation at the fiber type
  have fib : ∀ {k'} (σ : ISub k' k) (hh : (ival (idEnv k') (φ.subst σ.τ)).holds) {x z : Tm},
      (Comp2 S (dat (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k))) k' ((Hom.id k).comp σ.hom))
        k' k' (Hom.id k')).el ((Tm.glue A φ T e).isub σ) x z → RE2 S k' (T.isub σ) x z := by
    intro k' σ hh x z h
    rw [Hom.id_comp, dat_glue_fiber σ ((face_holds_iff hφs σ).2 hh)] at h
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh
    have hX := tyCode_of_univ hW hTσ
    have hGσ : IsTyK S k' ((Tm.glue A φ T e).isub σ) := ⟨l, .inl (HasTy.isubS hW hG σ)⟩
    have hfc : TyEq S k' ((Tm.glue A φ T e).isub σ) (T.isub σ) := by
      rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ (hent σ hh)
    have hTG : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
      refine ty_expandSR hW hX (hGσ.of_tyEq hfc) hGσ ?_ (hTT k' σ hh)
      rw [isub_glue] at hGσ ⊢
      exact stable_glue hW hGσ (hent σ hh)
    have P := per2_tyCode hW hX k' (Hom.id k')
    exact P.conv (P.symTy hTG) h
  -- `y` with itself in the fiber, where the face holds
  have fibY : ∀ {k'} (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (T.isub σ) (y.isub σ) (y.isub σ) := fun σ hh => fib σ hh (by
    have := hmain _ σ; unfold glueLocE at this
    rwa [if_pos (by rw [Hom.id_comp]; exact (face_holds_iff hφs σ).2 hh)] at this)
  -- the relation at a stage where the face holds
  have faceη : ∀ {k'} (σ : ISub k' k) (hh : (Cof.restr (ival (idEnv k) φ).face ((Hom.id k).comp σ.hom)).holds),
      (Comp2 S (dat (partialKV k (ival (idEnv k) φ).face (faceVals S T (idEnv k) (γ0 k))) k' ((Hom.id k).comp σ.hom))
        k' k' (Hom.id k')).el ((Tm.glue A φ T e).isub σ) (y.isub σ)
        ((Tm.glueEl φ' e' y (.unglue φ' e' y)).isub σ) := by
    intro k' σ hh
    have hfy := hmain k' σ
    unfold glueLocE at hfy; rw [if_pos hh] at hfy
    rw [Hom.id_comp] at hh hfy ⊢
    rw [dat_glue_fiber σ hh] at hfy ⊢
    have hh' := (face_holds_iff hφs σ).1 hh
    obtain ⟨lT, hTσ, -⟩ := glue_fiber_ty hW hG σ hh'
    have hX := tyCode_of_univ hW hTσ
    have hGσ : IsTyK S k' ((Tm.glue A φ T e).isub σ) := ⟨l, .inl (HasTy.isubS hW hG σ)⟩
    have hface : TyEq S k' ((Tm.glue A φ T e).isub σ) (T.isub σ) := by
      rw [isub_glue] at hGσ ⊢; exact glue_face_tyEq hW hGσ (hent σ hh')
    have hTG : (Comp2 S (semK S k' (T.isub σ)) k' k' (Hom.id k')).ty (T.isub σ) ((Tm.glue A φ T e).isub σ) := by
      refine ty_expandSR hW hX (hGσ.of_tyEq hface) hGσ ?_ (hTT k' σ hh')
      rw [isub_glue] at hGσ ⊢
      exact stable_glue hW hGσ (hent σ hh')
    have hGGT := (per2_tyCode hW hX k' (Hom.id k')).reflTy' hTG
    rw [isub_glueEl]
    exact el_expandSR hW hX hGGT (HasTy.isubS hW hyE.1 σ) (hησ σ)
      (stable_glueEl hW (hησ σ) (ent_trans (hent σ hh') (ent_subst h12 σ.τ))) hfy
  -- the right `unglue`, related to the image of the fiber where the face holds
  have hatη : ∀ {k'} (τ : ISub k' k), (ival (idEnv k') (φ.subst τ.τ)).holds →
      RE2 S k' (A.isub τ) ((Tm.unglue φ' e' y).isub τ) (.app (.fst (e.isub τ)) (y.isub τ)) := by
    intro k' τ hh
    have hφ'e : I.Entails .one (φ'.subst τ.τ) := ent_trans (hent τ hh) (ent_subst h12 τ.τ)
    have hgτ : HasTy S k' .one [] (y.isub τ) (.glue (A.isub τ) (φ'.subst τ.τ) (T.isub τ) (e'.isub τ)) := by
      have := HasTy.isubS hW hy2 τ; rwa [isub_glue] at this
    have heτ : HasTy S k' .one [] (e'.isub τ) (Tm.equiv (T.isub τ) (A.isub τ)) := by
      have := face_ty hW hφs (HasTy.eqL ee') τ hh; rwa [isub_equiv] at this
    have hs := stable_unglueFace hW hφ'e (HasTy.isubS hW hu' τ) hgτ (HasTy.isubS hW hA0 τ) heτ (TyEq.refl _)
    have happ := RE2.symm hW (hAA k' τ) (RE2_equiv_app hW (hE k' τ hh) (fibY τ hh))
    exact RE2.expandL hW (hAA k' τ) (HasTy.isubS hW hu' τ) (RE2.typed happ).2.1 hs happ
  unfold RE2
  rw [semK_glueT hW hG, Comp2_glueC (kv_semK_of_univ hW hA0) (isKV_partialKV _ _) (isCof_ival_face _ _) hn']
  refine ⟨⟨hyE.1, hη, hyη⟩, hmem, ⟨hyE.1, hη, hyη⟩, fun k' σ => ?_, hcoh, ?_⟩
  · unfold glueLocE
    split_ifs with hh
    · exact faceη σ hh
    have hh' : ¬ (ival (idEnv k') (φ.subst σ.τ)).holds := fun h => hh (by
      rw [Hom.id_comp]; exact (face_holds_iff hφs σ).2 h)
    have hfy := hmain k' σ
    unfold glueLocE at hfy; rw [if_neg hh] at hfy
    obtain ⟨A1, φ1, T1, e1, ψ, e0, t0, a0, ψ', e0', t0', a0', r1, rg, rg', q1, q1', q2, q2', ee0, ee0', ha0, hfibs⟩ :=
      hfy
    have eq1 := RedW.unique r1.1 (by rw [isub_glue]; exact (redT_glue_self (S := S) (k := k') (hne σ hh')).1)
    simp only [Tm.glue.injEq] at eq1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := eq1
    have hne' : ¬ I.Entails .one (φ'.subst σ.τ) := fun h => hne σ hh' (ent_trans h (ent_subst h21 σ.τ))
    rw [isub_glueEl]
    refine ⟨_, _, _, _, ψ, e0, t0, a0, _, _, _, _, r1, rg, redE_glueEl_self hne' (hησ σ), q1, q1',
      ent_subst h21 σ.τ, ent_subst h12 σ.τ, ee0, ee'σ σ, ?_, fun k'' σ' hh2 => ?_⟩
    · rw [Hom.id_comp, Comp2_res_el hW hA0]
      exact hUA.2 k' σ hh' ψ e0 t0 a0 rg.1
    · have hh2' : (ival (idEnv k'') (φ.subst (σ.comp σ').τ)).holds := by
        rw [Hom.id_comp] at hh2; exact (face_holds_iff hφs _).1 hh2
      refine ⟨?_, hfibs k'' σ' hh2 |>.2.1, ?_⟩
      · have hc := (hcoh k' σ hh _ rg.1 k'' σ').1 hh2 ψ e0 t0 a0 rfl
        have := fib (σ.comp σ') hh2' hc
        rw [Hom.id_comp, dat_glue_fiber (σ.comp σ') ((face_holds_iff hφs _).2 hh2'), Tm.isub_isub, Tm.isub_isub]
        exact this
      · rw [Hom.id_comp, Comp2_res_el hW hA0, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
        exact hatη (σ.comp σ') hh2'
  · -- the coherence of the Glue introduction
    intro k' σ hnσ w hw k'' ρ
    have hh' : ¬ (ival (idEnv k') (φ.subst σ.τ)).holds := fun h => hnσ (by
      rw [Hom.id_comp]; exact (face_holds_iff hφs σ).2 h)
    have hne' : ¬ I.Entails .one (φ'.subst σ.τ) := fun h => hne σ hh' (ent_trans h (ent_subst h21 σ.τ))
    rw [isub_glueEl] at hw
    obtain rfl := RedW.unique hw (redE_glueEl_self hne' (hησ σ)).1
    refine ⟨fun hh ψ0 e00 t00 a00 hwe => ?_, fun hh => ?_⟩
    · simp only [Tm.glueEl.injEq] at hwe
      obtain ⟨-, -, rfl, -⟩ := hwe
      rw [Tm.isub_isub]
      exact faceη (σ.comp ρ) hh
    · have hτ : ¬ (ival (idEnv k'') (φ.subst (σ.comp ρ).τ)).holds := fun h => hh (by
        rw [Hom.id_comp]; exact (face_holds_iff hφs _).2 h)
      have hneτ : ¬ I.Entails .one (φ'.subst (σ.comp ρ).τ) :=
        fun h => hne _ hτ (ent_trans h (ent_subst h21 _))
      rw [show (Tm.glueEl (φ'.subst σ.τ) (e'.isub σ) (y.isub σ) ((Tm.unglue φ' e' y).isub σ)).isub ρ =
        (Tm.glueEl φ' e' y (.unglue φ' e' y)).isub (σ.comp ρ) by
          show Tm.glueEl ((φ'.subst σ.τ).subst ρ.τ) ((e'.isub σ).isub ρ) ((y.isub σ).isub ρ)
            (((Tm.unglue φ' e' y).isub σ).isub ρ) = _
          rw [← I_subst_comp, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]; rfl]
      unfold glueLocE
      rw [if_neg hh, isub_glueEl]
      have r1 : RedT S k'' ((Tm.glue A φ T e).isub (σ.comp ρ)) (.glue (A.isub (σ.comp ρ)) (φ.subst (σ.comp ρ).τ)
          (T.isub (σ.comp ρ)) (e.isub (σ.comp ρ))) := by
        rw [isub_glue]; exact redT_glue_self (S := S) (k := k'') (hne _ hτ)
      have rη := redE_glueEl_self hneτ (hησ (σ.comp ρ))
      -- the right `unglue` with itself, from the base of `y`'s normal form at this stage
      have hfy := hmain k'' (σ.comp ρ)
      unfold glueLocE at hfy; rw [if_neg hh] at hfy
      obtain ⟨-, -, -, -, ψ, e0, t0, a0, -, -, -, -, -, rg, -⟩ := hfy
      have hb := hUA.2 k'' (σ.comp ρ) hτ ψ e0 t0 a0 rg.1
      have hbb := (perK hW (hXA k'' (σ.comp ρ))).reflEl' (hAA k'' (σ.comp ρ)) hb
      refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, r1, rη, rη, ent_subst h21 _, ent_subst h12 _,
        ent_subst h21 _, ent_subst h12 _, ee'σ _, ee'σ _, ?_, fun k3 σ3 hh3 => ?_⟩
      · rw [Hom.id_comp, Comp2_res_el hW hA0]; exact hbb
      · have hh3' : (ival (idEnv k3) (φ.subst ((σ.comp ρ).comp σ3).τ)).holds := by
          rw [Hom.id_comp] at hh3; exact (face_holds_iff hφs _).1 hh3
        have hft := fibY ((σ.comp ρ).comp σ3) hh3'
        have hat := hatη ((σ.comp ρ).comp σ3) hh3'
        refine ⟨?_, ?_, ?_⟩
        · rw [Hom.id_comp, dat_glue_fiber _ ((face_holds_iff hφs _).2 hh3'), Tm.isub_isub, Tm.isub_isub]
          exact hft
        · rw [Hom.id_comp, Comp2_res_el hW hA0, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
          exact hat
        · rw [Hom.id_comp, Comp2_res_el hW hA0, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub, Tm.isub_isub]
          exact hat

end

end Model.Whnf
