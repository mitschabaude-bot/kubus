import Model.Canon.KanPath

/-!
# Canonicity: computable equivalences

The computability of Glue types records the equivalence through the relation `equivE` built from
the relations of the two types. For closed types this is computability at the type `equiv T A`.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

/-- The computability relation of a closed type, at its restrictions. -/
def CR (S : Sig) (k : ℕ) (X : Tm) : ElR k := fun k' σ => (Comp S (semK S k X) k k' σ.hom).el

theorem fiberB_inst (A f y x : Tm) (σ : ISub k' k) :
    ((Tm.pathC A.shift (.app f.shift (.var 0)) y.shift).isub σ).inst x =
      Tm.pathC (A.isub σ) (.app (f.isub σ) x) (y.isub σ) := by
  simp only [Tm.pathC, Tm.isub]; scalc

theorem isContrB_inst (X c : Tm) (σ : ISub k' k) :
    ((Tm.pi X.shift (Tm.pathC X.shift.shift (.var 1) (.var 0))).isub σ).inst c =
      Tm.pi (X.isub σ) (Tm.pathC (X.isub σ).shift c.shift (.var 0)) := by
  simp only [Tm.pathC, Tm.isub]; scalc

theorem pathCB_inst (X c x : Tm) (σ : ISub k' k) :
    ((Tm.pathC X.shift c.shift (.var 0)).isub σ).inst x = Tm.pathC (X.isub σ) (c.isub σ) x := by
  simp only [Tm.pathC, Tm.isub]; scalc

theorem isEquivB_inst (T A f : Tm) (σ : ISub k' k) :
    ((Tm.isEquiv T.shift A.shift (.var 0)).isub σ).inst f = Tm.isEquiv (T.isub σ) (A.isub σ) f := by
  simp only [Tm.isEquiv, Tm.isContr, Tm.fiber, Tm.pathC, Tm.isub]; scalc

theorem isContrFiberB_inst (T A f y : Tm) (σ : ISub k' k) :
    ((Tm.isContr (Tm.fiber T.shift A.shift f.shift (.var 0))).isub σ).inst y =
      Tm.isContr (Tm.fiber (T.isub σ) (A.isub σ) (f.isub σ) y) := by
  simp only [Tm.isContr, Tm.fiber, Tm.pathC, Tm.isub]; scalc

theorem arrowB_inst (A a : Tm) (σ : ISub k' k) : ((A.shift).isub σ).inst a = A.isub σ := by
  rw [isub_shift, shift_inst]

variable (hW : WfSig S)
include hW

theorem CR_RE {X : Tm} {l : ℕ} (hX : HasTy S k .one [] X (.univ l)) (σ : ISub k' k) {Y t : Tm}
    (hY : TyEq S k' (X.isub σ) Y) : CR S k X k' σ Y t ↔ RE S k' Y t := by
  unfold CR RE
  rw [Comp_res_el hW hX, semK_tyEq hW hY]

theorem CR_comp {X : Tm} {l : ℕ} (hX : HasTy S k .one [] X (.univ l)) (ρ : ISub k' k) {k'' : ℕ}
    (ρ' : ISub k'' k') : CR S k X k'' (ρ.comp ρ') = CR S k' (X.isub ρ) k'' ρ' := by
  unfold CR
  rw [ISub.hom_comp, ← Comp_res (semK_ne hW hX), semK_isubS hW hX]

omit hW in
theorem dshift_up_dinst (X : Tm) (σ : ISub k' k) (r : I) : (X.dshift.isub σ.up).dinst r = X.isub σ := by
  rw [isub_dshift, dshift_dinst]

/-- A relation agrees with computability at all restrictions of the closed type `X0`. -/
def GoodR (S : Sig) (k : ℕ) (R : ElR k) (X0 : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) Z t, TyEq S k' (X0.isub σ) Z → (R k' σ Z t ↔ RE S k' Z t)

/-- The same for the codomain relations of `Σ` and `Π`. -/
def CodGood (S : Sig) (k : ℕ) (cod : (k' : ℕ) → ISub k' k → Tm → ElR k') (A0 B0 : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) a, RE S k' (A0.isub σ) a → ∀ Z t, TyEq S k' ((B0.isub σ).inst a) Z →
    (cod k' σ a k' (ISub.id k') Z t ↔ RE S k' Z t)

omit hW in
theorem GoodR.restr {R : ElR k} {X0 : Tm} (h : GoodR S k R X0) (σ : ISub k' k) :
    GoodR S k' (fun k'' σ'' => R k'' (σ.comp σ'')) (X0.isub σ) :=
  fun k'' σ'' Z t hZ => h k'' (σ.comp σ'') Z t (by rwa [← Tm.isub_isub])

theorem goodR_CR {X : Tm} {l : ℕ} (hX : HasTy S k .one [] X (.univ l)) : GoodR S k (CR S k X) X :=
  fun k' σ Z t hZ => CR_RE hW hX σ hZ

theorem tyEq_sigma_dom {A0 B0 A1 B1 : Tm} (h : TyEq S k (.sigma A0 B0) (.sigma A1 B1)) : TyEq S k A0 A1 := by
  rcases h with h | ⟨l, h⟩
  · injection h with h1 h2; subst h1; exact TyEq.refl _
  · exact .inr ⟨l, EqTm.sigmaInjDom h⟩

theorem tyEq_sigma_cod {A0 B0 A1 B1 a : Tm} (h : TyEq S k (.sigma A0 B0) (.sigma A1 B1))
    (ha : HasTy S k .one [] a A0) : TyEq S k (B0.inst a) (B1.inst a) := by
  rcases h with h | ⟨l, h⟩
  · injection h with h1 h2; subst h1 h2; exact TyEq.refl _
  · exact .inr ⟨l, EqTm.sigmaInjCod h ha⟩

theorem tyEq_pi_dom {A0 B0 A1 B1 : Tm} (h : TyEq S k (.pi A0 B0) (.pi A1 B1)) : TyEq S k A0 A1 := by
  rcases h with h | ⟨l, h⟩
  · injection h with h1 h2; subst h1; exact TyEq.refl _
  · exact .inr ⟨l, EqTm.piInjDom h⟩

theorem tyEq_pi_cod {A0 B0 A1 B1 a : Tm} (h : TyEq S k (.pi A0 B0) (.pi A1 B1))
    (ha : HasTy S k .one [] a A0) : TyEq S k (B0.inst a) (B1.inst a) := by
  rcases h with h | ⟨l, h⟩
  · injection h with h1 h2; subst h1 h2; exact TyEq.refl _
  · exact .inr ⟨l, EqTm.piInjCod h ha⟩

/-- Elements of path types over a constant line. -/
theorem goodR_pathE {X a b : Tm} {l : ℕ} (hP : HasTy S k .one [] (Tm.pathC X a b) (.univ l))
    {R : ElR k} (hR : GoodR S k R X) : GoodR S k (pathE S (constLine R)) (Tm.pathC X a b) := by
  intro k' σ Y p hY
  have hPσ : HasTy S k' .one [] (Tm.pathC (X.isub σ) (a.isub σ) (b.isub σ)) (.univ l) := by
    have := HasTy.isubS hW hP σ
    rwa [show (Tm.pathC X a b).isub σ = Tm.pathC (X.isub σ) (a.isub σ) (b.isub σ) by
      show Tm.path (X.dshift.isub σ.up) _ _ = _; rw [isub_dshift]; rfl] at this
  have hY' : TyEq S k' (Tm.pathC (X.isub σ) (a.isub σ) (b.isub σ)) Y := by
    rwa [show (Tm.pathC X a b).isub σ = Tm.pathC (X.isub σ) (a.isub σ) (b.isub σ) by
      show Tm.path (X.dshift.isub σ.up) _ _ = _; rw [isub_dshift]; rfl] at hY
  constructor
  · rintro ⟨hpt, L1, b0, b1, hE, hall⟩
    have hE' := hY'.trans hW hE
    have hpt' := hpt.tyConv (TyEq.symm hY')
    refine (RE_path_intro hW hPσ hpt' fun k'' σ' r hr => ?_).conv_ty hW hY'
    have h1 := hall k'' σ' r hr
    simp only [constLine] at h1
    rw [show (ISub.cons r hr (σ.comp σ')).tail = σ.comp σ' from rfl] at h1
    have hT : TyEq S k'' (X.isub (σ.comp σ')) ((L1.isub σ'.up).dinst r) := by
      rcases hE' with h | ⟨l', h⟩
      · simp only [Tm.pathC] at h
        injection h with h1 h2 h3
        subst h1
        rw [dshift_up_dinst, Tm.isub_isub]; exact TyEq.refl _
      · have h2 := EqTm.pathInjLine (A := (X.isub σ).dshift.isub σ'.up) (A' := L1.isub σ'.up)
          (a := (a.isub σ).isub σ') (a' := b0.isub σ') (b := (b.isub σ).isub σ') (b' := b1.isub σ')
          (EqTm.isubS hW h σ') hr
        rw [dshift_up_dinst, Tm.isub_isub] at h2
        exact .inr ⟨l', h2⟩
    have h3 := (hR k'' (σ.comp σ') _ _ hT).1 h1
    rw [dshift_up_dinst, Tm.isub_isub]
    exact h3.conv_ty hW (TyEq.symm hT)
  · intro hp
    have hp' := hp.conv_ty hW (TyEq.symm hY')
    refine ⟨(Comp_el_typed hp).1, (X.isub σ).dshift, a.isub σ, b.isub σ, TyEq.symm hY', fun k'' σ' r hr => ?_⟩
    simp only [constLine]
    rw [show (ISub.cons r hr (σ.comp σ')).tail = σ.comp σ' from rfl, dshift_up_dinst]
    refine (hR k'' (σ.comp σ') _ _ (by rw [Tm.isub_isub]; exact TyEq.refl _)).2 ?_
    have := RE_path_elim hW (L := (X.isub σ).dshift.isub σ'.up) (hp'.isub hW σ') r hr
    rwa [dshift_up_dinst] at this

/-- `sigmaE` with good relations is computability. -/
theorem goodR_sigmaE {A0 B0 : Tm} {l : ℕ} (hsig : HasTy S k .one [] (.sigma A0 B0) (.univ l))
    {dom : ElR k} {cod : (k' : ℕ) → ISub k' k → Tm → ElR k'}
    (hdom : GoodR S k dom A0) (hcod : CodGood S k cod A0 B0) : GoodR S k (sigmaE S dom cod) (.sigma A0 B0) := by
  intro k' σ Y x hY
  have hsigσ := HasTy.isubS hW hsig σ
  rw [isub_sigma] at hsigσ hY
  have hcl := closed_of_ty hW hsigσ
  simp only [Tm.closedB, Bool.and_eq_true] at hcl
  constructor
  · rintro ⟨hxt, A1, B1, hE, hall⟩
    have hE0 := hY.trans hW hE
    have hxt0 := hxt.tyConv (TyEq.symm hY)
    have hx0 : x.isub (ISub.id k') = x := isub_id_of_closed (closed_of_ty hW hxt)
    have hcl1 := closed_of_isTyK hW ((isTyK_of_ty hW hxt).of_tyEq hE)
    simp only [Tm.closedB, Bool.and_eq_true] at hcl1
    obtain ⟨h1, h2⟩ := hall k' (ISub.id k')
    rw [ISub.comp_id, hx0, isub_id_of_closed hcl1.1] at h1
    rw [ISub.comp_id, hx0, isub_id_of_closed hcl1.2] at h2
    have hd := tyEq_sigma_dom hW hE0
    have hfst := ((hdom k' σ A1 _ hd).1 h1).conv_ty hW (TyEq.symm hd)
    have hc := tyEq_sigma_cod hW hE0 (Comp_el_typed hfst).1
    have hsnd := ((hcod k' σ (.fst x) hfst _ _ hc).1 h2).conv_ty hW (TyEq.symm hc)
    exact (RE_sigma_intro hW hsigσ hxt0 hfst hsnd).conv_ty hW hY
  · intro hx
    have hx0 := hx.conv_ty hW (TyEq.symm hY)
    refine ⟨(Comp_el_typed hx).1, A0.isub σ, B0.isub σ, TyEq.symm hY, fun k'' σ' => ?_⟩
    have h := hx0.isub hW σ'
    rw [isub_sigma] at h
    obtain ⟨h1, h2⟩ := RE_sigma_elim hW h
    refine ⟨(hdom k'' (σ.comp σ') _ _ (by rw [← Tm.isub_isub]; exact TyEq.refl _)).2 h1,
      (hcod k'' (σ.comp σ') _ (by rw [← Tm.isub_isub]; exact h1) _ _ (by rw [← Tm.isub_isub]; exact TyEq.refl _)).2 h2⟩

/-- `piE` with good relations is computability. -/
theorem goodR_piE {A0 B0 : Tm} {l : ℕ} (hpi : HasTy S k .one [] (.pi A0 B0) (.univ l))
    {dom : ElR k} {cod : (k' : ℕ) → ISub k' k → Tm → ElR k'}
    (hdom : GoodR S k dom A0) (hcod : CodGood S k cod A0 B0) : GoodR S k (piE S dom cod) (.pi A0 B0) := by
  intro k' σ Y f hY
  have hpiσ := HasTy.isubS hW hpi σ
  rw [isub_pi] at hpiσ hY
  constructor
  · rintro ⟨hft, A1, B1, hE, hall⟩
    have hE0 := hY.trans hW hE
    have hft0 := hft.tyConv (TyEq.symm hY)
    refine (RE_pi_intro hW hpiσ hft0 fun k'' σ' a ha => ?_).conv_ty hW hY
    have hEσ := hE0.isub hW σ'
    rw [isub_pi, isub_pi] at hEσ
    have hd := tyEq_pi_dom hW hEσ
    have hc := tyEq_pi_cod hW hEσ (Comp_el_typed ha).1
    have h1 := hall k'' σ' a ((hdom k'' (σ.comp σ') _ a (by rw [← Tm.isub_isub]; exact hd)).2 (ha.conv_ty hW hd))
    exact ((hcod k'' (σ.comp σ') a (by rw [← Tm.isub_isub]; exact ha) _ _ (by rw [← Tm.isub_isub]; exact hc)).1
      h1).conv_ty hW (TyEq.symm hc)
  · intro hf
    have hf0 := hf.conv_ty hW (TyEq.symm hY)
    refine ⟨(Comp_el_typed hf).1, A0.isub σ, B0.isub σ, TyEq.symm hY, fun k'' σ' a ha => ?_⟩
    have ha' := (hdom k'' (σ.comp σ') _ a (by rw [← Tm.isub_isub]; exact TyEq.refl _)).1 ha
    have h := hf0.isub hW σ'
    rw [isub_pi] at h
    have := RE_pi_elim hW h ha'
    exact (hcod k'' (σ.comp σ') a (by rw [← Tm.isub_isub]; exact ha') _ _
      (by rw [← Tm.isub_isub]; exact TyEq.refl _)).2 this

theorem fam_inst_ty {X B a : Tm} {l : ℕ} (h : HasTy S k .one [] (.sigma X B) (.univ l)) (ha : HasTy S k .one [] a X) :
    HasTy S k .one [] (B.inst a) (.univ l) := HasTy.subst (HasTy.sigmaCod h) ha

theorem fam_inst_ty_pi {X B a : Tm} {l : ℕ} (h : HasTy S k .one [] (.pi X B) (.univ l)) (ha : HasTy S k .one [] a X) :
    HasTy S k .one [] (B.inst a) (.univ l) := HasTy.subst (HasTy.piCod h) ha

theorem goodR_id {R : ElR k} {X0 : Tm} (h : GoodR S k R X0) {Z t : Tm} (hcl : X0.closedB 0 k = true)
    (hZ : TyEq S k X0 Z) : R k (ISub.id k) Z t ↔ RE S k Z t :=
  h k (ISub.id k) Z t (by rw [isub_id_of_closed hcl]; exact hZ)

theorem goodR_fiberE {T A f y : Tm} {l : ℕ} (hF : HasTy S k .one [] (Tm.fiber T A f y) (.univ l))
    {RT RA : ElR k} (hT : GoodR S k RT T) (hA : GoodR S k RA A) :
    GoodR S k (fiberE S RT RA) (Tm.fiber T A f y) := by
  refine goodR_sigmaE hW hF hT fun k' σ a ha Z t hZ => ?_
  rw [fiberB_inst] at hZ
  have hFσ := HasTy.isubS hW hF σ
  simp only [Tm.fiber] at hFσ
  rw [isub_sigma] at hFσ
  have hP := fam_inst_ty hW hFσ (Comp_el_typed ha).1
  rw [fiberB_inst] at hP
  exact goodR_id hW (goodR_pathE hW hP (hA.restr σ)) (closed_of_ty hW hP) hZ

theorem goodR_isContrE {X0 : Tm} {l : ℕ} (hC : HasTy S k .one [] (Tm.isContr X0) (.univ l))
    {R : ElR k} (hR : GoodR S k R X0) : GoodR S k (isContrE S R) (Tm.isContr X0) := by
  refine goodR_sigmaE hW hC hR fun k' σ c hc Z t hZ => ?_
  rw [isContrB_inst] at hZ
  have hCσ := HasTy.isubS hW hC σ
  simp only [Tm.isContr] at hCσ
  rw [isub_sigma] at hCσ
  have hP := fam_inst_ty hW hCσ (Comp_el_typed hc).1
  rw [isContrB_inst] at hP
  refine goodR_id hW (goodR_piE hW hP (hR.restr σ) fun k'' σ' x hx Z' t' hZ' => ?_) (closed_of_ty hW hP) hZ
  rw [pathCB_inst] at hZ'
  have hPσ := HasTy.isubS hW hP σ'
  rw [isub_pi] at hPσ
  have hQ := fam_inst_ty_pi hW hPσ (Comp_el_typed hx).1
  rw [pathCB_inst] at hQ
  exact goodR_id hW (goodR_pathE hW hQ ((hR.restr σ).restr σ')) (closed_of_ty hW hQ) hZ'

/-- The relation `equivE` built from good relations is computability at `equiv T A`. -/
theorem goodR_equivE {T A : Tm} {l : ℕ} (hE : HasTy S k .one [] (Tm.equiv T A) (.univ l))
    {RT RA : ElR k} (hT : GoodR S k RT T) (hA : GoodR S k RA A) :
    GoodR S k (equivE S RT RA) (Tm.equiv T A) := by
  have hE' : HasTy S k .one [] (.sigma (Tm.arrow T A) (Tm.isEquiv T.shift A.shift (.var 0))) (.univ l) := hE
  have hArr := HasTy.sigmaDom hE'
  refine goodR_sigmaE hW hE' (goodR_piE hW hArr hT fun k' σ a ha Z t hZ => ?_) fun k' σ f hf Z t hZ => ?_
  · rw [arrowB_inst] at hZ
    rw [ISub.comp_id]
    exact hA k' σ Z t hZ
  · rw [isEquivB_inst] at hZ
    have hEσ := HasTy.isubS hW hE' σ
    rw [isub_sigma] at hEσ
    have hI := fam_inst_ty hW hEσ (Comp_el_typed hf).1
    rw [isEquivB_inst] at hI
    refine goodR_id hW (goodR_piE hW hI (hA.restr σ) fun k'' σ' y hy Z' t' hZ' => ?_) (closed_of_ty hW hI) hZ
    rw [isContrFiberB_inst] at hZ'
    have hIσ := HasTy.isubS hW hI σ'
    simp only [Tm.isEquiv] at hIσ
    rw [isub_pi] at hIσ
    have hC := fam_inst_ty_pi hW hIσ (Comp_el_typed hy).1
    rw [isContrFiberB_inst] at hC
    have hF := HasTy.sigmaDom (show HasTy S k'' .one [] (.sigma _ _) _ from hC)
    have hT' : GoodR S k'' (fun k3 σ3 => RT k3 ((σ.comp σ').comp σ3)) ((T.isub σ).isub σ') := by
      have := hT.restr (σ.comp σ'); rwa [← Tm.isub_isub] at this
    have hA' : GoodR S k'' (fun k3 σ3 => RA k3 ((σ.comp σ').comp σ3)) ((A.isub σ).isub σ') := by
      have := hA.restr (σ.comp σ'); rwa [← Tm.isub_isub] at this
    exact goodR_id hW (goodR_isContrE hW hC (goodR_fiberE hW hF hT' hA')) (closed_of_ty hW hC) hZ'

end

end Model.Canon
