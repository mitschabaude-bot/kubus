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

theorem FamOK.rebase {n n' : ℕ} {P : (k' : ℕ) → ISub k' n → Pack2} (h : FamOK S n P) (ρ : ISub n' n) :
    FamOK S n' (fun k' σ => P k' (ρ.comp σ)) where
  per k' σ := h.per k' _
  kr k' σ k'' σ' X X' hX := by have := h.kr k' (ρ.comp σ) k'' σ' X X' hX; rwa [ISub.comp_assoc] at this
  krEl k' σ k'' σ' X t t' hX := by have := h.krEl k' (ρ.comp σ) k'' σ' X t t' hX; rwa [ISub.comp_assoc] at this
  tyEq k' σ X X' hX := h.tyEq k' _ X X' hX
  isTy k' σ X X' hX := h.isTy k' _ X X' hX

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
  · rw [isub_sigma]; exact redW_self (by simp [step])
  · rw [isub_sigma]; exact redW_self (by simp [step])
  · simpa only [ISub.id_comp] using (h k3 σ3).1
  · simp only [ISub.id_comp, ISub.comp_id] at ha ⊢; exact (h k3 σ3).2 a a' ha

omit hW in
theorem piF_ty {D Cf : (k' : ℕ) → ISub k' n → Pack2} {X Y X' Y' : Tm}
    (hb : IsTyK S n (.pi X Y) ∧ IsTyK S n (.pi X' Y') ∧ TyEq S n (.pi X Y) (.pi X' Y'))
    (h : ∀ k3 (σ3 : ISub k3 n), (D k3 σ3).ty (X.isub σ3) (X'.isub σ3) ∧
      ∀ a a', (D k3 σ3).el (X.isub σ3) a a' → (Cf k3 σ3).ty ((Y.isub σ3).inst a) ((Y'.isub σ3).inst a')) :
    (piF S D Cf n (ISub.id n)).ty (.pi X Y) (.pi X' Y') := by
  refine ⟨hb, fun k3 σ3 => ⟨X.isub σ3, Y.isub σ3, X'.isub σ3, Y'.isub σ3, ?_, ?_, ?_, fun a a' ha => ?_⟩⟩
  · rw [isub_pi]; exact redW_self (by simp [step])
  · rw [isub_pi]; exact redW_self (by simp [step])
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
  · show RedW S (Tm.path (X.dshift.isub σ3.up) _ _) _
    rw [isub_dshift]; exact redW_self (by simp [step])
  · show RedW S (Tm.path (X'.dshift.isub σ3.up) _ _) _
    rw [isub_dshift]; exact redW_self (by simp [step])
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

end

end Model.Whnf
