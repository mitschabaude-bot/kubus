import Model.Whnf.Pack2
import Model.Canon.GlueEquiv
import Model.Whnf.EquivCongr

/-!
# The binary relation of equivalences

`equivF T A` is the relation of `equiv T A` built from the relations of `T` and `A` (as in Glue
types). It is a partial equivalence, transferable along related `T` and `A`, given the PER
properties of `T` and `A` and their Kripke property.
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

variable {S : Sig} {k k' : ℕ}

theorem piE2_rebase (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') (σ : ISub k' k) :
    piE2 S dom cod k' σ = piE2 S (fun k'' σ'' => dom k'' (σ.comp σ'')) (fun k'' σ'' => cod k'' (σ.comp σ''))
      k' (ISub.id k') := by
  funext A t t'; simp only [piE2, ISub.id_comp]

theorem sigmaE2_rebase (dom : ElR2 k) (cod : (k' : ℕ) → ISub k' k → Tm → ElR2 k') (σ : ISub k' k) :
    sigmaE2 S dom cod k' σ = sigmaE2 S (fun k'' σ'' => dom k'' (σ.comp σ'')) (fun k'' σ'' => cod k'' (σ.comp σ''))
      k' (ISub.id k') := by
  funext A t t'; simp only [sigmaE2, ISub.id_comp]

theorem pathE2_rebase (line : ElR2 (k + 1)) (σ : ISub k' k) :
    pathE2 S line k' σ = pathE2 S (fun k'' σ'' => line k'' (σ.up.comp σ'')) k' (ISub.id k') := by
  funext A t t'
  simp only [pathE2, ISub.id_comp, ISub.up_comp_cons]

/-- A Kripke family of related types and elements over a base stage. -/
structure FamOK (S : Sig) (n : ℕ) (P : (k' : ℕ) → ISub k' n → Pack2) : Prop where
  per : ∀ k' (σ : ISub k' n), PERP (P k' σ)
  kr : ∀ k' (σ : ISub k' n) k'' (σ' : ISub k'' k') X X', (P k' σ).ty X X' →
    (P k'' (σ.comp σ')).ty (X.isub σ') (X'.isub σ')
  krEl : ∀ k' (σ : ISub k' n) k'' (σ' : ISub k'' k') X t t', (P k' σ).el X t t' →
    (P k'' (σ.comp σ')).el (X.isub σ') (t.isub σ') (t'.isub σ')
  tyEq : ∀ k' (σ : ISub k' n) X X', (P k' σ).ty X X' → TyEq S k' X X'
  isTy : ∀ k' (σ : ISub k' n) X X', (P k' σ).ty X X' → IsTyK S k' X ∧ IsTyK S k' X'
  elEB : ∀ k' (σ : ISub k' n) X t t', (P k' σ).el X t t' → EB S k' X t t'

theorem FamOK.rebase {n n' : ℕ} {P : (k' : ℕ) → ISub k' n → Pack2} (h : FamOK S n P) (ρ : ISub n' n) :
    FamOK S n' (fun k' σ => P k' (ρ.comp σ)) where
  per k' σ := h.per k' _
  kr k' σ k'' σ' X X' hX := by have := h.kr k' (ρ.comp σ) k'' σ' X X' hX; rwa [ISub.comp_assoc] at this
  krEl k' σ k'' σ' X t t' hX := by have := h.krEl k' (ρ.comp σ) k'' σ' X t t' hX; rwa [ISub.comp_assoc] at this
  tyEq k' σ X X' hX := h.tyEq k' _ X X' hX
  isTy k' σ X X' hX := h.isTy k' _ X X' hX
  elEB k' σ X t t' hX := h.elEB k' _ X t t' hX

theorem ISub.up_tail_comp_cons_id {n : ℕ} (σ : ISub k' n) (r : I) (hr : r.Scoped k') :
    σ.up.tail.comp (ISub.cons r hr (ISub.id k')) = σ := by
  ext i
  show ((σ.τ i).shift).subst (ISub.cons r hr (ISub.id k')).τ = σ.τ i
  rw [I_shift_cons]
  by_cases h : i < n
  · exact ISub.I.subst_scoped_id (σ.sc i h) fun j hj => by simp [ISub.id, hj]
  · rw [σ.hi i (by omega)]; rfl

variable (hW : WfSig S)
include hW

/-- The lines of path types over a constant family satisfy the line condition. -/
theorem constLine_ty {n : ℕ} {AP : (k' : ℕ) → ISub k' n → Pack2} (hA : FamOK S n AP) :
    ∀ k' (σ : ISub k' n) (L1 L1' : Tm), (AP (k' + 1) σ.up.tail).ty L1 L1' → ∀ (r : I) (hr : r.Scoped k'),
      (AP k' (ISub.cons r hr σ).tail).ty (L1.dinst r) (L1'.dinst r) := by
  intro k' σ L1 L1' h r hr
  obtain ⟨h1, h2⟩ := hA.isTy _ _ _ _ h
  have := hA.kr _ _ k' (ISub.cons r hr (ISub.id k')) _ _ h
  rw [ISub.up_tail_comp_cons_id, isub_cons_id_of_closed (closed_of_isTyK hW h1),
    isub_cons_id_of_closed (closed_of_isTyK hW h2)] at this
  exact this

omit hW in
theorem ISub.up_comp_tail {n k'' : ℕ} (σ : ISub k' n) (σ' : ISub k'' (k' + 1)) :
    (σ.up.comp σ').tail = σ.comp σ'.tail := by
  ext i
  show ((σ.τ i).shift).subst σ'.τ = (σ.τ i).subst σ'.tail.τ
  exact I_shift_tail _ _

section fam
variable {n : ℕ}

theorem pathF_ok {AP : (k' : ℕ) → ISub k' n → Pack2} (hA : FamOK S n AP) : FamOK S n (pathF S AP) where
  per k' σ := pathPack_per hW _ (fun k3 σ3 => hA.per _ _) (constLine_ty hW (hA.rebase σ))
  kr k' σ k'' σ' X X' h := by
    refine ⟨⟨h.1.1.isub hW σ', h.1.2.1.isub hW σ', h.1.2.2.isub hW σ'⟩, ?_⟩
    have := pathT_isub _ σ' h.2
    simp only [ISub.up_comp_tail, ISub.comp_assoc] at this ⊢
    exact this
  krEl k' σ k'' σ' X t t' h := by
    have := pathEl_isub (S := S) (fun k3 (σ3 : ISub k3 (k' + 1)) => AP k3 (σ.comp σ3.tail)) hW σ' h
    simp only [pathF, pathPack, ISub.up_comp_tail, ISub.comp_assoc] at this ⊢
    exact this
  tyEq k' σ X X' h := h.1.2.2
  isTy k' σ X X' h := ⟨h.1.1, h.1.2.1⟩
  elEB k' σ X t t' h := h.1

theorem sigF_ok {D Cf : (k' : ℕ) → ISub k' n → Pack2} (hD : FamOK S n D) (hC : FamOK S n Cf) :
    FamOK S n (sigF S D Cf) where
  per k' σ := sigPack_per hW _ _ (fun k3 σ3 => hD.per _ _) (fun k3 σ3 _ _ _ _ => hC.per _ _) (fun _ _ _ _ _ _ => rfl)
  kr k' σ k'' σ' X X' h := by
    refine ⟨⟨h.1.1.isub hW σ', h.1.2.1.isub hW σ', h.1.2.2.isub hW σ'⟩, ?_⟩
    have := sigT_isub _ _ σ' h.2
    simp only [ISub.comp_assoc] at this ⊢
    exact this
  krEl k' σ k'' σ' X t t' h := by
    have := sigEl_isub (S := S) (fun k3 σ3 => D k3 (σ.comp σ3)) (fun k3 σ3 _ k4 σ4 => Cf k4 ((σ.comp σ3).comp σ4)) hW σ' h
    simp only [sigF, sigPack, ISub.comp_assoc] at this ⊢
    exact this
  tyEq k' σ X X' h := h.1.2.2
  isTy k' σ X X' h := ⟨h.1.1, h.1.2.1⟩
  elEB k' σ X t t' h := h.1

theorem piF_ok {D Cf : (k' : ℕ) → ISub k' n → Pack2} (hD : FamOK S n D) (hC : FamOK S n Cf) :
    FamOK S n (piF S D Cf) where
  per k' σ := piPack_per hW _ _ (fun k3 σ3 => hD.per _ _) (fun k3 σ3 _ _ _ _ => hC.per _ _) (fun _ _ _ _ _ _ => rfl)
  kr k' σ k'' σ' X X' h := by
    refine ⟨⟨h.1.1.isub hW σ', h.1.2.1.isub hW σ', h.1.2.2.isub hW σ'⟩, ?_⟩
    have := piT_isub _ _ σ' h.2
    simp only [ISub.comp_assoc] at this ⊢
    exact this
  krEl k' σ k'' σ' X t t' h := by
    have := piEl_isub (S := S) (fun k3 σ3 => D k3 (σ.comp σ3)) (fun k3 σ3 _ k4 σ4 => Cf k4 ((σ.comp σ3).comp σ4)) hW σ' h
    simp only [piF, piPack, ISub.comp_assoc] at this ⊢
    exact this
  tyEq k' σ X X' h := h.1.2.2
  isTy k' σ X X' h := ⟨h.1.1, h.1.2.1⟩
  elEB k' σ X t t' h := h.1

end fam

section eqv
variable {n : ℕ} (TP AP : (k' : ℕ) → ISub k' n → Pack2)

theorem equivF_ok (hT : FamOK S n TP) (hA : FamOK S n AP) : FamOK S n (equivF S TP AP) :=
  sigF_ok hW (piF_ok hW hT hA) (piF_ok hW hA (sigF_ok hW (sigF_ok hW hT (pathF_ok hW hA))
    (piF_ok hW (sigF_ok hW hT (pathF_ok hW hA)) (pathF_ok hW (sigF_ok hW hT (pathF_ok hW hA))))))

end eqv

omit hW in
theorem redW_self {t : Tm} (h : step S t = none) : RedW S t t := ⟨.refl _, h⟩

section ty
variable {n : ℕ}

omit hW in
theorem sigF_ty {D Cf : (k' : ℕ) → ISub k' n → Pack2} {X Y X' Y' : Tm}
    (hb : IsTyK S n (.sigma X Y) ∧ IsTyK S n (.sigma X' Y') ∧ TyEq S n (.sigma X Y) (.sigma X' Y'))
    (h : ∀ k3 (σ3 : ISub k3 n), (D k3 σ3).ty (X.isub σ3) (X'.isub σ3) ∧
      ∀ a a', (D k3 σ3).el (X.isub σ3) a a' → (Cf k3 σ3).ty ((Y.isub σ3).inst a) ((Y'.isub σ3).inst a')) :
    (sigF S D Cf n (ISub.id n)).ty (.sigma X Y) (.sigma X' Y') := by
  refine ⟨hb, fun k3 σ3 => ⟨X.isub σ3, Y.isub σ3, X'.isub σ3, Y'.isub σ3, ?_, ?_, ?_, fun a a' ha => ?_⟩⟩
  · rw [isub_sigma]; exact ⟨redW_self (by simp [step]), TyEq.refl _⟩
  · rw [isub_sigma]; exact ⟨redW_self (by simp [step]), TyEq.refl _⟩
  · simpa only [ISub.id_comp] using (h k3 σ3).1
  · simp only [ISub.id_comp, ISub.comp_id] at ha ⊢; exact (h k3 σ3).2 a a' ha

omit hW in
theorem piF_ty {D Cf : (k' : ℕ) → ISub k' n → Pack2} {X Y X' Y' : Tm}
    (hb : IsTyK S n (.pi X Y) ∧ IsTyK S n (.pi X' Y') ∧ TyEq S n (.pi X Y) (.pi X' Y'))
    (h : ∀ k3 (σ3 : ISub k3 n), (D k3 σ3).ty (X.isub σ3) (X'.isub σ3) ∧
      ∀ a a', (D k3 σ3).el (X.isub σ3) a a' → (Cf k3 σ3).ty ((Y.isub σ3).inst a) ((Y'.isub σ3).inst a')) :
    (piF S D Cf n (ISub.id n)).ty (.pi X Y) (.pi X' Y') := by
  refine ⟨hb, fun k3 σ3 => ⟨X.isub σ3, Y.isub σ3, X'.isub σ3, Y'.isub σ3, ?_, ?_, ?_, fun a a' ha => ?_⟩⟩
  · rw [isub_pi]; exact ⟨redW_self (by simp [step]), TyEq.refl _⟩
  · rw [isub_pi]; exact ⟨redW_self (by simp [step]), TyEq.refl _⟩
  · simpa only [ISub.id_comp] using (h k3 σ3).1
  · simp only [ISub.id_comp, ISub.comp_id] at ha ⊢; exact (h k3 σ3).2 a a' ha

omit hW in
theorem pathF_ty {AP : (k' : ℕ) → ISub k' n → Pack2} (hA : FamOK S n AP) {X X' b0 b0' b1 b1' : Tm}
    (hb : IsTyK S n (Tm.pathC X b0 b1) ∧ IsTyK S n (Tm.pathC X' b0' b1') ∧
      TyEq S n (Tm.pathC X b0 b1) (Tm.pathC X' b0' b1'))
    (hX : (AP n (ISub.id n)).ty X X') (h0 : (AP n (ISub.id n)).el X b0 b0') (h1 : (AP n (ISub.id n)).el X b1 b1') :
    (pathF S AP n (ISub.id n)).ty (Tm.pathC X b0 b1) (Tm.pathC X' b0' b1') := by
  refine ⟨hb, fun k3 σ3 => ⟨(X.isub σ3).dshift, b0.isub σ3, b1.isub σ3, (X'.isub σ3).dshift, b0'.isub σ3,
    b1'.isub σ3, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show RedT S k3 (Tm.path (X.dshift.isub σ3.up) _ _) _
    rw [isub_dshift]; exact ⟨redW_self (by simp [step]), TyEq.refl _⟩
  · show RedT S k3 (Tm.path (X'.dshift.isub σ3.up) _ _) _
    rw [isub_dshift]; exact ⟨redW_self (by simp [step]), TyEq.refl _⟩
  · have := hA.kr n (ISub.id n) (k3 + 1) σ3.up.tail X X' hX
    rw [← dshift_isub_tail, ← dshift_isub_tail, isub_dshift, isub_dshift] at this
    simpa only [ISub.id_comp] using this
  · have := hA.krEl n (ISub.id n) k3 σ3 X b0 b0' h0
    rw [Meta.dshift_dinst]
    simpa only [ISub.id_comp] using this
  · have := hA.krEl n (ISub.id n) k3 σ3 X b1 b1' h1
    rw [Meta.dshift_dinst]
    simpa only [ISub.id_comp] using this

end ty

section rebase
variable {n : ℕ}

omit hW in
theorem pathF_rebase (AP : (k' : ℕ) → ISub k' n → Pack2) (σ : ISub k' n) :
    pathF S AP k' σ = pathF S (fun k3 σ3 => AP k3 (σ.comp σ3)) k' (ISub.id k') := by
  simp only [pathF, ISub.id_comp]

omit hW in
theorem sigF_rebase (D Cf : (k' : ℕ) → ISub k' n → Pack2) (σ : ISub k' n) :
    sigF S D Cf k' σ = sigF S (fun k3 σ3 => D k3 (σ.comp σ3)) (fun k3 σ3 => Cf k3 (σ.comp σ3)) k' (ISub.id k') := by
  simp only [sigF, ISub.id_comp, ISub.comp_assoc]

omit hW in
theorem piF_rebase (D Cf : (k' : ℕ) → ISub k' n → Pack2) (σ : ISub k' n) :
    piF S D Cf k' σ = piF S (fun k3 σ3 => D k3 (σ.comp σ3)) (fun k3 σ3 => Cf k3 (σ.comp σ3)) k' (ISub.id k') := by
  simp only [piF, ISub.id_comp, ISub.comp_assoc]

end rebase

omit hW in
theorem isub_arrow (T A : Tm) (σ : ISub k' k) : (Tm.arrow T A).isub σ = Tm.arrow (T.isub σ) (A.isub σ) := by
  simp only [Tm.arrow, isub_pi, isub_shift]

omit hW in
theorem tyk {n l : ℕ} {X : Tm} (h : HasTy S n .one [] X (.univ l)) : IsTyK S n X := ⟨l, .inl h⟩

omit hW in
/-- Related functions, at a restriction, applied to related arguments. -/
theorem app_rel {n : ℕ} {TP AP : (k' : ℕ) → ISub k' n → Pack2} {T A f f' : Tm} (hf : (piF S TP AP n (ISub.id n)).el (Tm.arrow T A) f f') {k3 : ℕ} (σ3 : ISub k3 n)
    {x x' : Tm} (hx : (TP k3 σ3).el (T.isub σ3) x x') :
    (AP k3 σ3).el (A.isub σ3) (.app (f.isub σ3) x) (.app (f'.isub σ3) x') := by
  obtain ⟨-, hall⟩ := hf
  obtain ⟨A1, B1, hr, hel⟩ := hall k3 σ3
  rw [isub_arrow] at hr
  have := RedW.unique hr.1 (redW_self (by simp [Tm.arrow, step]))
  simp only [Tm.arrow, Tm.pi.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  have := hel x x' (by simpa only [ISub.id_comp] using hx)
  simpa only [ISub.id_comp, ISub.comp_id, Meta.shift_inst] using this



omit hW in
theorem pairOf {n l : ℕ} {X X' : Tm} (e : EqTm S n .one [] X X' (.univ l)) :
    IsTyK S n X ∧ IsTyK S n X' ∧ TyEq S n X X' :=
  ⟨tyk (HasTy.eqL e), tyk (HasTy.eqR e), .inr ⟨l, e⟩⟩

theorem pathC_congrS {n l : ℕ} {X X' b0 b0' b1 b1' : Tm} (eX : EqTm S n .one [] X X' (.univ l))
    (e0 : EqTm S n .one [] b0 b0' X) (e1 : EqTm S n .one [] b1 b1' X) :
    EqTm S n .one [] (Tm.pathC X b0 b1) (Tm.pathC X' b0' b1') (.univ l) :=
  minimal_to_spec_eq (pathC_congr (sigClosed_of_wfSig hW) (spec_to_minimal_eq hW eX) (spec_to_minimal_eq hW e0)
    (spec_to_minimal_eq hW e1))

theorem fiber_congrS {n l : ℕ} {T T' A A' f f' y y' : Tm} (eT : EqTm S n .one [] T T' (.univ l))
    (eA : EqTm S n .one [] A A' (.univ l)) (ef : EqTm S n .one [] f f' (Tm.arrow T A)) (ey : EqTm S n .one [] y y' A) :
    EqTm S n .one [] (Tm.fiber T A f y) (Tm.fiber T' A' f' y') (.univ l) :=
  minimal_to_spec_eq (fiber_congr (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2
    (spec_to_minimal_eq hW eT) (spec_to_minimal_eq hW eA) (spec_to_minimal_eq hW ef) (spec_to_minimal_eq hW ey))

theorem isEquiv_congrS {n l : ℕ} {T T' A A' f f' : Tm} (eT : EqTm S n .one [] T T' (.univ l))
    (eA : EqTm S n .one [] A A' (.univ l)) (ef : EqTm S n .one [] f f' (Tm.arrow T A)) :
    EqTm S n .one [] (Tm.isEquiv T A f) (Tm.isEquiv T' A' f') (.univ l) :=
  minimal_to_spec_eq (isEquiv_congr (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2
    (spec_to_minimal_eq hW eT) (spec_to_minimal_eq hW eA) (spec_to_minimal_eq hW ef))

theorem arrow_congrS {n l : ℕ} {T T' A A' : Tm} (eT : EqTm S n .one [] T T' (.univ l))
    (eA : EqTm S n .one [] A A' (.univ l)) : EqTm S n .one [] (Tm.arrow T A) (Tm.arrow T' A') (.univ l) :=
  minimal_to_spec_eq (arrow_congr (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2
    (spec_to_minimal_eq hW eT) (spec_to_minimal_eq hW eA))

theorem equiv_congrS {n l : ℕ} {T T' A A' : Tm} (eT : EqTm S n .one [] T T' (.univ l))
    (eA : EqTm S n .one [] A A' (.univ l)) : EqTm S n .one [] (Tm.equiv T A) (Tm.equiv T' A') (.univ l) :=
  minimal_to_spec_eq (equiv_congr (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2
    (spec_to_minimal_eq hW eT) (spec_to_minimal_eq hW eA))


theorem piPath_congrS {n l : ℕ} {X X' c c' : Tm} (eX : EqTm S n .one [] X X' (.univ l)) (ec : EqTm S n .one [] c c' X) :
    EqTm S n .one [] (.pi X (Tm.pathC X.shift c.shift (.var 0))) (.pi X' (Tm.pathC X'.shift c'.shift (.var 0))) (.univ l) :=
  minimal_to_spec_eq (piPath_congr (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2
    (spec_to_minimal_eq hW eX) (spec_to_minimal_eq hW ec))

theorem isContr_congrS {n l : ℕ} {X X' : Tm} (eX : EqTm S n .one [] X X' (.univ l)) :
    EqTm S n .one [] (Tm.isContr X) (Tm.isContr X') (.univ l) :=
  minimal_to_spec_eq (isContr_congr (sigClosed_of_wfSig hW) (wf_typed _ S rfl hW).1 (wf_typed _ S rfl hW).2
    (spec_to_minimal_eq hW eX))

theorem isContrF_ty {n : ℕ} {XP : (k' : ℕ) → ISub k' n → Pack2} (hX : FamOK S n XP) {l : ℕ} {X X' : Tm}
    (eX : EqTm S n .one [] X X' (.univ l)) (hXX : (XP n (ISub.id n)).ty X X') :
    (isContrF S XP n (ISub.id n)).ty (Tm.isContr X) (Tm.isContr X') := by
  show (sigF S XP (piF S XP (pathF S XP)) n (ISub.id n)).ty
    (.sigma X (.pi X.shift (Tm.pathC X.shift.shift (.var 1) (.var 0))))
    (.sigma X' (.pi X'.shift (Tm.pathC X'.shift.shift (.var 1) (.var 0))))
  refine sigF_ty (pairOf (isContr_congrS hW eX)) fun k3 σ3 => ⟨?_, fun c c' hc => ?_⟩
  · simpa only [ISub.id_comp] using hX.kr n (ISub.id n) k3 σ3 X X' hXX
  · rw [isContrB_inst, isContrB_inst, piF_rebase]
    have hXσ := hX.kr n (ISub.id n) k3 σ3 X X' hXX
    simp only [ISub.id_comp] at hXσ
    have ec := (hX.elEB _ _ _ _ _ hc).2.2
    have eXσ := EqTm.isubS hW eX σ3
    refine piF_ty (pairOf (piPath_congrS hW eXσ ec)) fun k4 σ4 => ⟨?_, fun x x' hx => ?_⟩
    · have := hX.kr k3 σ3 k4 σ4 _ _ hXσ
      simpa only [ISub.comp_id] using this
    · rw [pathCB_inst, pathCB_inst, pathF_rebase]
      have hXσ4 := hX.kr k3 σ3 k4 σ4 _ _ hXσ
      have hc4 := hX.krEl k3 σ3 k4 σ4 _ _ _ hc
      have ex := (hX.elEB _ _ _ _ _ hx).2.2
      refine pathF_ty (hX.rebase (σ3.comp σ4))
        (pairOf (pathC_congrS hW (EqTm.isubS hW eXσ σ4) ((hX.elEB _ _ _ _ _ hc4).2.2) ex)) ?_ ?_ ?_ <;>
        simp only [ISub.comp_id, Tm.isub_isub]
      · rw [← Tm.isub_isub, ← Tm.isub_isub]; exact hXσ4
      · rw [← Tm.isub_isub]; exact hc4
      · rw [← Tm.isub_isub]; exact hx

omit hW in
theorem fiberF_rebase {n : ℕ} (TP AP : (k' : ℕ) → ISub k' n → Pack2) (σ : ISub k' n) :
    fiberF S TP AP k' σ = fiberF S (fun k3 σ3 => TP k3 (σ.comp σ3)) (fun k3 σ3 => AP k3 (σ.comp σ3)) k' (ISub.id k') := by
  simp only [fiberF, sigF, pathF, ISub.id_comp, ISub.comp_assoc]

omit hW in
theorem isContrF_rebase {n : ℕ} (XP : (k' : ℕ) → ISub k' n → Pack2) (σ : ISub k' n) :
    isContrF S XP k' σ = isContrF S (fun k3 σ3 => XP k3 (σ.comp σ3)) k' (ISub.id k') := by
  simp only [isContrF, sigF, piF, pathF, ISub.id_comp, ISub.comp_assoc]

omit hW in
theorem isEquivF_rebase {n : ℕ} (TP AP : (k' : ℕ) → ISub k' n → Pack2) (σ : ISub k' n) :
    isEquivF S TP AP k' σ =
      isEquivF S (fun k3 σ3 => TP k3 (σ.comp σ3)) (fun k3 σ3 => AP k3 (σ.comp σ3)) k' (ISub.id k') := by
  simp only [isEquivF, isContrF, fiberF, sigF, piF, pathF, ISub.id_comp, ISub.comp_assoc]

section tys
variable {n : ℕ} {TP AP : (k' : ℕ) → ISub k' n → Pack2} (hT : FamOK S n TP) (hA : FamOK S n AP)
  {l : ℕ} {T T' A A' : Tm}
  (eT : EqTm S n .one [] T T' (.univ l)) (eA : EqTm S n .one [] A A' (.univ l))
  (hTT : (TP n (ISub.id n)).ty T T') (hAA : (AP n (ISub.id n)).ty A A')
include hT hA eT eA hTT hAA


theorem fiberF_ty {f f' y y' : Tm} (hf : (piF S TP AP n (ISub.id n)).el (Tm.arrow T A) f f')
    (hy : (AP n (ISub.id n)).el A y y') :
    (fiberF S TP AP n (ISub.id n)).ty (Tm.fiber T A f y) (Tm.fiber T' A' f' y') := by
  have ef : EqTm S n .one [] f f' (Tm.arrow T A) := hf.1.2.2
  have ey : EqTm S n .one [] y y' A := (hA.elEB _ _ _ _ _ hy).2.2
  show (sigF S TP (pathF S AP) n (ISub.id n)).ty (.sigma T (Tm.pathC A.shift (.app f.shift (.var 0)) y.shift))
    (.sigma T' (Tm.pathC A'.shift (.app f'.shift (.var 0)) y'.shift))
  refine sigF_ty (pairOf (fiber_congrS hW eT eA ef ey)) fun k3 σ3 => ⟨?_, fun x x' hx => ?_⟩
  · simpa only [ISub.id_comp] using hT.kr n (ISub.id n) k3 σ3 T T' hTT
  · rw [fiberB_inst, fiberB_inst, pathF_rebase]
    have hAσ := hA.kr n (ISub.id n) k3 σ3 A A' hAA
    have h0 := app_rel hf σ3 hx
    have h1 := hA.krEl n (ISub.id n) k3 σ3 A y y' hy
    simp only [ISub.id_comp] at hAσ h1
    have e0 := (hA.elEB _ _ _ _ _ h0).2.2
    refine pathF_ty (hA.rebase σ3) (pairOf (pathC_congrS hW (EqTm.isubS hW eA σ3) e0 (EqTm.isubS hW ey σ3)))
      ?_ ?_ ?_ <;> simp only [ISub.comp_id]
    · exact hAσ
    · exact h0
    · exact h1


theorem isEquivF_ty {f f' : Tm} (hf : (piF S TP AP n (ISub.id n)).el (Tm.arrow T A) f f') :
    (isEquivF S TP AP n (ISub.id n)).ty (Tm.isEquiv T A f) (Tm.isEquiv T' A' f') := by
  have ef : EqTm S n .one [] f f' (Tm.arrow T A) := hf.1.2.2
  show (piF S AP (isContrF S (fiberF S TP AP)) n (ISub.id n)).ty
    (.pi A (Tm.isContr (Tm.fiber T.shift A.shift f.shift (.var 0))))
    (.pi A' (Tm.isContr (Tm.fiber T'.shift A'.shift f'.shift (.var 0))))
  refine piF_ty (pairOf (isEquiv_congrS hW eT eA ef)) fun k3 σ3 => ⟨?_, fun y y' hy => ?_⟩
  · simpa only [ISub.id_comp] using hA.kr n (ISub.id n) k3 σ3 A A' hAA
  · rw [isContrFiberB_inst, isContrFiberB_inst, isContrF_rebase]
    have hTσ := hT.kr n (ISub.id n) k3 σ3 T T' hTT
    have hAσ := hA.kr n (ISub.id n) k3 σ3 A A' hAA
    have hfσ := (piF_ok hW hT hA).krEl n (ISub.id n) k3 σ3 _ f f' hf
    simp only [ISub.id_comp] at hTσ hAσ hfσ
    rw [isub_arrow, piF_rebase] at hfσ
    have eTσ := EqTm.isubS hW eT σ3
    have eAσ := EqTm.isubS hW eA σ3
    have efσ := EqTm.isubS hW ef σ3
    rw [isub_arrow] at efσ
    have ey := (hA.elEB _ _ _ _ _ hy).2.2
    refine isContrF_ty hW ((sigF_ok hW hT (pathF_ok hW hA)).rebase σ3) (fiber_congrS hW eTσ eAσ efσ ey) ?_
    simp only [ISub.comp_id]
    rw [show sigF S TP (pathF S AP) k3 σ3 = fiberF S TP AP k3 σ3 from rfl, fiberF_rebase]
    exact fiberF_ty hW (hT.rebase σ3) (hA.rebase σ3) eTσ eAσ (by simpa only [ISub.comp_id] using hTσ)
      (by simpa only [ISub.comp_id] using hAσ) hfσ (by simpa only [ISub.comp_id] using hy)


theorem arrowF_ty : (piF S TP AP n (ISub.id n)).ty (Tm.arrow T A) (Tm.arrow T' A') := by
  show (piF S TP AP n (ISub.id n)).ty (.pi T A.shift) (.pi T' A'.shift)
  refine piF_ty (pairOf (arrow_congrS hW eT eA)) fun k3 σ3 => ⟨?_, fun x x' _ => ?_⟩
  · simpa only [ISub.id_comp] using hT.kr n (ISub.id n) k3 σ3 T T' hTT
  · rw [arrowB_inst, arrowB_inst]
    simpa only [ISub.id_comp] using hA.kr n (ISub.id n) k3 σ3 A A' hAA

theorem equivF_ty : (equivF S TP AP n (ISub.id n)).ty (Tm.equiv T A) (Tm.equiv T' A') := by
  show (sigF S (piF S TP AP) (isEquivF S TP AP) n (ISub.id n)).ty
    (.sigma (Tm.arrow T A) (Tm.isEquiv T.shift A.shift (.var 0)))
    (.sigma (Tm.arrow T' A') (Tm.isEquiv T'.shift A'.shift (.var 0)))
  have eTσ : ∀ k3 (σ3 : ISub k3 n), EqTm S k3 .one [] (T.isub σ3) (T'.isub σ3) (.univ l) := fun _ σ3 =>
    EqTm.isubS hW eT σ3
  have eAσ : ∀ k3 (σ3 : ISub k3 n), EqTm S k3 .one [] (A.isub σ3) (A'.isub σ3) (.univ l) := fun _ σ3 =>
    EqTm.isubS hW eA σ3
  have hTσ : ∀ k3 (σ3 : ISub k3 n), (TP k3 σ3).ty (T.isub σ3) (T'.isub σ3) := fun k3 σ3 => by
    simpa only [ISub.id_comp] using hT.kr n (ISub.id n) k3 σ3 T T' hTT
  have hAσ : ∀ k3 (σ3 : ISub k3 n), (AP k3 σ3).ty (A.isub σ3) (A'.isub σ3) := fun k3 σ3 => by
    simpa only [ISub.id_comp] using hA.kr n (ISub.id n) k3 σ3 A A' hAA
  refine sigF_ty (pairOf (equiv_congrS hW eT eA)) fun k3 σ3 => ⟨?_, fun f f' hf => ?_⟩
  · rw [isub_arrow, isub_arrow, piF_rebase]
    exact arrowF_ty hW (hT.rebase σ3) (hA.rebase σ3) (eTσ k3 σ3) (eAσ k3 σ3)
      (by simpa only [ISub.comp_id] using hTσ k3 σ3) (by simpa only [ISub.comp_id] using hAσ k3 σ3)
  · rw [isEquivB_inst, isEquivB_inst, isEquivF_rebase]
    rw [piF_rebase] at hf
    exact isEquivF_ty hW (hT.rebase σ3) (hA.rebase σ3) (eTσ k3 σ3) (eAσ k3 σ3)
      (by simpa only [ISub.comp_id] using hTσ k3 σ3) (by simpa only [ISub.comp_id] using hAσ k3 σ3)
      (by rw [← isub_arrow]; exact hf)

end tys

end

end Model.Whnf
