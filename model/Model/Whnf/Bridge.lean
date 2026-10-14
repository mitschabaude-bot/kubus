import Model.Whnf.Formers2

/-!
# The relation of equivalences is the relation at `equiv T A`

For closed types `T` and `A`, the pack `equivF` built from the relations of `T` and `A` (as in
the Glue type relation) relates the same elements as `RE2` at the type `equiv T A`.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' k'' n : ℕ}

/-- A family of packs relates the elements of the restrictions of `X0` as `RE2` does. -/
def GoodP (S : Sig) (n : ℕ) (P : (k' : ℕ) → ISub k' n → Pack2) (X0 : Tm) : Prop :=
  ∀ k' (σ : ISub k' n) t t', (P k' σ).el (X0.isub σ) t t' ↔ RE2 S k' (X0.isub σ) t t'

/-- The same for the codomain packs of `Σ` and `Π` (which do not depend on the argument). -/
def CodGoodP (S : Sig) (n : ℕ) (Cf : (k' : ℕ) → ISub k' n → Pack2) (A0 B0 : Tm) : Prop :=
  ∀ k' (σ : ISub k' n) a, HasTy S k' .one [] a (A0.isub σ) → ∀ t t',
    (Cf k' σ).el ((B0.isub σ).inst a) t t' ↔ RE2 S k' ((B0.isub σ).inst a) t t'

theorem GoodP.restr {P : (k' : ℕ) → ISub k' n → Pack2} {X0 : Tm} (h : GoodP S n P X0) (ρ : ISub k' n) :
    GoodP S k' (fun k'' σ'' => P k'' (ρ.comp σ'')) (X0.isub ρ) := fun k'' σ'' t t' => by
  rw [Tm.isub_isub]; exact h k'' (ρ.comp σ'') t t'

variable (hW : WfSig S)
include hW

theorem goodP_comp {X : Tm} {l : ℕ} (hX : HasTy S n .one [] X (.univ l)) :
    GoodP S n (fun k' σ => Comp2 S (semK S n X) n k' σ.hom) X := fun k' σ t t' => by
  show (Comp2 S (semK S n X) n k' σ.hom).el _ t t' ↔ _
  rw [Comp2_res_el hW hX]; rfl

theorem goodP_sigF {A0 B0 : Tm} {l : ℕ} (hsig : HasTy S n .one [] (.sigma A0 B0) (.univ l))
    {D Cf : (k' : ℕ) → ISub k' n → Pack2} (hD : GoodP S n D A0) (hC : CodGoodP S n Cf A0 B0) :
    GoodP S n (sigF S D Cf) (.sigma A0 B0) := by
  intro k' σ t t'
  have hsigσ := HasTy.isubS hW hsig σ
  rw [isub_sigma] at hsigσ ⊢
  have hcl := closed_of_ty hW hsigσ
  simp only [Tm.closedB, Bool.and_eq_true] at hcl
  constructor
  · rintro ⟨hE, hall⟩
    obtain ⟨A1, B1, h0, h1, h2⟩ := hall k' (ISub.id k')
    rw [isub_id_of_closed (closed_of_ty hW hsigσ)] at h0
    obtain ⟨rfl, rfl⟩ : A0.isub σ = A1 ∧ B0.isub σ = B1 := by
      have := RedW.unique (redW_self rfl) h0.1; injection this; constructor <;> assumption
    rw [isub_id_of_closed (closed_of_ty hW hE.1), isub_id_of_closed (closed_of_ty hW hE.2.1)] at h1 h2
    simp only [ISub.comp_id] at h1 h2
    have h1' := (hD k' σ _ _).1 h1
    have h2' := (hC k' σ _ (RE2.typed h1').1 _ _).1 h2
    exact RE2_sigma_intro hW hsigσ hE h1' h2'
  · intro h
    refine ⟨RE2.typed h, fun k3 σ3 => ⟨(A0.isub σ).isub σ3, (B0.isub σ).isub σ3, ?_, ?_, ?_⟩⟩
    · rw [isub_sigma]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · have := (RE2_sigma_elim hW (by have := RE2.isub hW h σ3; rwa [isub_sigma] at this)).1
      simp only [ISub.id_comp]
      rw [Tm.isub_isub] at this ⊢
      exact (hD k3 (σ.comp σ3) _ _).2 this
    · have := (RE2_sigma_elim hW (by have := RE2.isub hW h σ3; rwa [isub_sigma] at this))
      simp only [ISub.id_comp, ISub.comp_id]
      simp only [Tm.isub_isub] at this ⊢
      exact (hC k3 (σ.comp σ3) _ (RE2.typed this.1).1 _ _).2 this.2

theorem goodP_piF {A0 B0 : Tm} {l : ℕ} (hpi : HasTy S n .one [] (.pi A0 B0) (.univ l))
    {D Cf : (k' : ℕ) → ISub k' n → Pack2} (hD : GoodP S n D A0) (hC : CodGoodP S n Cf A0 B0) :
    GoodP S n (piF S D Cf) (.pi A0 B0) := by
  intro k' σ t t'
  have hpiσ := HasTy.isubS hW hpi σ
  rw [isub_pi] at hpiσ ⊢
  constructor
  · rintro ⟨hE, hall⟩
    refine RE2_pi_intro hW hpiσ hE fun k3 σ3 a a' ha => ?_
    obtain ⟨A1, B1, h0, h1⟩ := hall k3 σ3
    rw [isub_pi] at h0
    obtain ⟨rfl, rfl⟩ : (A0.isub σ).isub σ3 = A1 ∧ (B0.isub σ).isub σ3 = B1 := by
      have := RedW.unique (redW_self rfl) h0.1; injection this; constructor <;> assumption
    simp only [ISub.id_comp, ISub.comp_id] at h1
    simp only [Tm.isub_isub] at ha h1 ⊢
    have := h1 a a' ((hD k3 (σ.comp σ3) _ _).2 ha)
    exact (hC k3 (σ.comp σ3) _ (RE2.typed ha).1 _ _).1 this
  · intro h
    refine ⟨RE2.typed h, fun k3 σ3 => ⟨(A0.isub σ).isub σ3, (B0.isub σ).isub σ3, ?_, fun a a' ha => ?_⟩⟩
    · rw [isub_pi]; exact ⟨redW_self rfl, TyEq.refl _⟩
    · simp only [ISub.id_comp, ISub.comp_id] at ha ⊢
      rw [Tm.isub_isub] at ha ⊢
      have ha' := (hD k3 (σ.comp σ3) _ _).1 ha
      have hσ3 := RE2.isub hW h σ3
      rw [isub_pi, Tm.isub_isub, Tm.isub_isub] at hσ3
      exact (hC k3 (σ.comp σ3) _ (RE2.typed ha').1 _ _).2 (RE2_pi_elim hW hσ3 ha')

omit hW in
theorem isub_pathC (X a b : Tm) (σ : ISub k' n) :
    (Tm.pathC X a b).isub σ = Tm.pathC (X.isub σ) (a.isub σ) (b.isub σ) := by
  show Tm.path (X.dshift.isub σ.up) _ _ = _; rw [isub_dshift]; rfl

theorem goodP_pathF {X0 a b : Tm} {l : ℕ} (hP : HasTy S n .one [] (Tm.pathC X0 a b) (.univ l))
    {P : (k' : ℕ) → ISub k' n → Pack2} (hX : GoodP S n P X0) : GoodP S n (pathF S P) (Tm.pathC X0 a b) := by
  intro k' σ p p'
  have hPσ := HasTy.isubS hW hP σ
  rw [isub_pathC] at hPσ ⊢
  constructor
  · rintro ⟨hE, hall⟩
    obtain ⟨L1, b0, b1, h0, -, e0, e1⟩ := hall k' (ISub.id k')
    have hcl := closed_of_ty hW hPσ
    rw [isub_id_of_closed hcl] at h0
    obtain ⟨rfl, rfl, rfl⟩ : (X0.isub σ).dshift = L1 ∧ a.isub σ = b0 ∧ b.isub σ = b1 := by
      have := RedW.unique (redW_self rfl) h0.1; injection this
      exact ⟨by assumption, by assumption, by assumption⟩
    refine RE2_path_intro hW hPσ hE (fun k3 σ3 r r' hr hr' hE' => ?_) ?_ ?_
    · obtain ⟨L3, c0, c1, h3, h4, -, -⟩ := hall k3 σ3
      rw [show (Tm.pathC (X0.isub σ) (a.isub σ) (b.isub σ)).isub σ3 =
        Tm.path ((X0.isub σ).dshift.isub σ3.up) _ _ from rfl] at h3
      obtain rfl : (X0.isub σ).dshift.isub σ3.up = L3 := by
        have := RedW.unique (redW_self rfl) h3.1; injection this
      have := h4 r r' hr hr' hE'
      simp only [ISub.id_comp, ISub.tail_cons] at this
      rw [dshift_up_dinst, Tm.isub_isub] at this ⊢
      exact (hX k3 (σ.comp σ3) _ _).1 this
    · simp only [ISub.tail_cons, ISub.comp_id] at e0
      rw [Meta.dshift_dinst, isub_id_of_closed (closed_of_ty hW hE.1)] at e0
      have := (hX k' σ _ _).1 e0
      rwa [Meta.dshift_dinst]
    · simp only [ISub.tail_cons, ISub.comp_id] at e1
      rw [Meta.dshift_dinst, isub_id_of_closed (closed_of_ty hW hE.1)] at e1
      have := (hX k' σ _ _).1 e1
      rwa [Meta.dshift_dinst]
  · intro h
    refine ⟨RE2.typed h, fun k3 σ3 => ⟨(X0.isub σ).dshift.isub σ3.up, (a.isub σ).isub σ3, (b.isub σ).isub σ3,
      ⟨redW_self rfl, TyEq.refl _⟩, fun r r' hr hr' hE' => ?_, ?_, ?_⟩⟩
    · have hσ3 := RE2.isub hW h σ3
      rw [show (Tm.pathC (X0.isub σ) (a.isub σ) (b.isub σ)).isub σ3 =
        Tm.path ((X0.isub σ).dshift.isub σ3.up) _ _ from rfl] at hσ3
      have := (RE2_path_elim hW hσ3).1 r r' hr hr' hE'
      simp only [ISub.id_comp, ISub.tail_cons]
      rw [dshift_up_dinst, Tm.isub_isub] at this ⊢
      exact (hX k3 (σ.comp σ3) _ _).2 this
    · have hσ3 := RE2.isub hW h σ3
      rw [show (Tm.pathC (X0.isub σ) (a.isub σ) (b.isub σ)).isub σ3 =
        Tm.path ((X0.isub σ).dshift.isub σ3.up) _ _ from rfl] at hσ3
      have := (RE2_path_elim hW hσ3).2.1
      simp only [ISub.id_comp, ISub.tail_cons]
      rw [dshift_up_dinst, Tm.isub_isub] at this ⊢
      exact (hX k3 (σ.comp σ3) _ _).2 this
    · have hσ3 := RE2.isub hW h σ3
      rw [show (Tm.pathC (X0.isub σ) (a.isub σ) (b.isub σ)).isub σ3 =
        Tm.path ((X0.isub σ).dshift.isub σ3.up) _ _ from rfl] at hσ3
      have := (RE2_path_elim hW hσ3).2.2
      simp only [ISub.id_comp, ISub.tail_cons]
      rw [dshift_up_dinst, Tm.isub_isub] at this ⊢
      exact (hX k3 (σ.comp σ3) _ _).2 this

/-- A good family at the identity of its base. -/
theorem goodP_id {P : (k' : ℕ) → ISub k' n → Pack2} {X0 : Tm} (h : GoodP S n P X0)
    (hcl : X0.closedB 0 n = true) (t t' : Tm) : (P n (ISub.id n)).el X0 t t' ↔ RE2 S n X0 t t' := by
  have := h n (ISub.id n) t t'
  rwa [isub_id_of_closed hcl] at this

theorem goodP_fiberF {T A f y : Tm} {l : ℕ} (hF : HasTy S n .one [] (Tm.fiber T A f y) (.univ l))
    {TP AP : (k' : ℕ) → ISub k' n → Pack2} (hT : GoodP S n TP T) (hA : GoodP S n AP A) :
    GoodP S n (fiberF S TP AP) (Tm.fiber T A f y) := by
  refine goodP_sigF hW hF hT fun k' σ a ha t t' => ?_
  rw [fiberB_inst, pathF_rebase]
  have hFσ := HasTy.isubS hW hF σ
  simp only [Tm.fiber] at hFσ
  rw [isub_sigma] at hFσ
  have hP := fam_inst_ty hW hFσ ha
  rw [fiberB_inst] at hP
  exact goodP_id hW (goodP_pathF hW hP (hA.restr σ)) (closed_of_ty hW hP) t t'

theorem goodP_isContrF {X0 : Tm} {l : ℕ} (hC : HasTy S n .one [] (Tm.isContr X0) (.univ l))
    {XP : (k' : ℕ) → ISub k' n → Pack2} (hX : GoodP S n XP X0) :
    GoodP S n (isContrF S XP) (Tm.isContr X0) := by
  refine goodP_sigF hW hC hX fun k' σ c hc t t' => ?_
  rw [isContrB_inst, piF_rebase]
  have hCσ := HasTy.isubS hW hC σ
  simp only [Tm.isContr] at hCσ
  rw [isub_sigma] at hCσ
  have hP := fam_inst_ty hW hCσ hc
  rw [isContrB_inst] at hP
  refine goodP_id hW (goodP_piF hW hP (hX.restr σ) fun k'' σ' x hx t2 t2' => ?_) (closed_of_ty hW hP) t t'
  rw [pathCB_inst, pathF_rebase]
  have hPσ := HasTy.isubS hW hP σ'
  rw [isub_pi] at hPσ
  have hQ := fam_inst_ty_pi hW hPσ hx
  rw [pathCB_inst] at hQ
  have := goodP_id hW (goodP_pathF hW hQ ((hX.restr σ).restr σ')) (closed_of_ty hW hQ) t2 t2'
  simpa only [ISub.comp_assoc] using this

/-- The pack `equivF` of good families relates the elements of `equiv T A` as `RE2` does. -/
theorem goodP_equivF {T A : Tm} {l : ℕ} (hE : HasTy S n .one [] (Tm.equiv T A) (.univ l))
    {TP AP : (k' : ℕ) → ISub k' n → Pack2} (hT : GoodP S n TP T) (hA : GoodP S n AP A) :
    GoodP S n (equivF S TP AP) (Tm.equiv T A) := by
  have hE' : HasTy S n .one [] (.sigma (Tm.arrow T A) (Tm.isEquiv T.shift A.shift (.var 0))) (.univ l) := hE
  have hArr := HasTy.sigmaDom hE'
  refine goodP_sigF hW hE' (goodP_piF hW hArr hT fun k' σ a ha t t' => ?_) fun k' σ f hf t t' => ?_
  · rw [arrowB_inst]; exact hA k' σ t t'
  · rw [isEquivB_inst, isEquivF_rebase]
    have hEσ := HasTy.isubS hW hE' σ
    rw [isub_sigma] at hEσ
    have hI := fam_inst_ty hW hEσ hf
    rw [isEquivB_inst] at hI
    refine goodP_id hW (goodP_piF hW hI (hA.restr σ) fun k'' σ' y hy t2 t2' => ?_) (closed_of_ty hW hI) t t'
    rw [isContrFiberB_inst, isContrF_rebase]
    have hfam : (fun k3 (σ3 : ISub k3 k'') => fiberF S (fun k4 σ4 => TP k4 (σ.comp σ4))
        (fun k4 σ4 => AP k4 (σ.comp σ4)) k3 (σ'.comp σ3)) =
        fiberF S (fun k3 σ3 => TP k3 (σ.comp (σ'.comp σ3))) (fun k3 σ3 => AP k3 (σ.comp (σ'.comp σ3))) := by
      funext k3 σ3; simp only [fiberF, sigF, pathF, ISub.comp_assoc]
    rw [hfam]
    have hIσ := HasTy.isubS hW hI σ'
    simp only [Tm.isEquiv] at hIσ
    rw [isub_pi] at hIσ
    have hC := fam_inst_ty_pi hW hIσ hy
    rw [isContrFiberB_inst] at hC
    have hF := HasTy.sigmaDom (show HasTy S k'' .one [] (.sigma _ _) _ from hC)
    have hT' : GoodP S k'' (fun k3 σ3 => TP k3 (σ.comp (σ'.comp σ3))) ((T.isub σ).isub σ') := by
      have := (hT.restr σ).restr σ'; exact this
    have hA' : GoodP S k'' (fun k3 σ3 => AP k3 (σ.comp (σ'.comp σ3))) ((A.isub σ).isub σ') := by
      have := (hA.restr σ).restr σ'; exact this
    exact goodP_id hW (goodP_isContrF hW hC (goodP_fiberF hW hF hT' hA')) (closed_of_ty hW hC) t2 t2'

end

end Model.Whnf
