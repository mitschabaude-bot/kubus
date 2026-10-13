import Model.Canon.FormersData

/-!
# Canonicity: the Kan properties of a closed type

`KanH S k A`: composition in `A` of a computable tube and base is computable; `KanT S k A`:
transport along the line `A` (at stage `k + 1`) of a computable element is computable. Both are
invariant under judgmental equality of types, and hold trivially where the face holds.
-/

set_option autoImplicit false

namespace Model.Canon

open KubusCore KubusCore.Meta

noncomputable section

variable {S : Sig} {k k' m : ℕ}

theorem forall0_scoped {φ : I} (h : φ.Scoped (k + 1)) : φ.forall0.Scoped k := by
  apply scoped_ofFaces
  intro c hc l hl
  simp only [List.mem_map, List.mem_filter] at hc
  obtain ⟨α, ⟨hα, hall⟩, rfl⟩ := hc
  obtain ⟨⟨i, d⟩, hil, rfl⟩ := List.mem_map.1 hl
  have h1 := faces_scoped h α hα _ hil
  have h2 := List.all_eq_true.1 hall _ hil
  simp only [bne_iff_ne, ne_eq] at h2
  simp only at h1 ⊢
  omega

/-- Computable tubes for `hcomp` at `A` with face `φ`. -/
def TubeC (S : Sig) (k : ℕ) (A : Tm) (φ : I) (u : Tm) : Prop :=
  ∀ k' (σ : ISub k' k) (r : I), r.Scoped k' → (ival (idEnv k') (φ.subst σ.τ)).holds →
    RE S k' (A.isub σ) ((u.isub σ.up).dinst r)

/-- Composition in `A` preserves computability. -/
def KanH (S : Sig) (k : ℕ) (A : Tm) : Prop :=
  ∀ (φ : I) (u a : Tm), HasTy S k .one [] (.hcomp A φ u a) A → TubeC S k A φ u → RE S k A a →
    RE S k A (.hcomp A φ u a)

/-- Transport along the line `A` (at stage `k + 1`) preserves computability. -/
def KanT (S : Sig) (k : ℕ) (A : Tm) : Prop :=
  ∀ (φ : I) (a : Tm), HasTy S k .one [] (.transp A φ a) (A.dinst .one) → RE S k (A.dinst .zero) a →
    RE S k (A.dinst .one) (.transp A φ a)

/-- The Kan properties of all restrictions of `A` (a closed type at stage `n`). -/
def KanAll (S : Sig) (n : ℕ) (A : Tm) : Prop :=
  (∀ k' (ρ : ISub k' n), KanH S k' (A.isub ρ)) ∧ (∀ k' (ρ : ISub (k' + 1) n), KanT S k' (A.isub ρ))

theorem I_subst_congr_scoped {σ τ : ℕ → I} {n : ℕ} (h : ∀ i < n, σ i = τ i) :
    ∀ {r : I}, r.Scoped n → r.subst σ = r.subst τ
  | .zero, _ => rfl
  | .one, _ => rfl
  | .var i, hr => h i hr
  | .neg r, hr => congrArg I.neg (I_subst_congr_scoped h hr)
  | .and r s, ⟨h1, h2⟩ => congrArg₂ I.and (I_subst_congr_scoped h h1) (I_subst_congr_scoped h h2)
  | .or r s, ⟨h1, h2⟩ => congrArg₂ I.or (I_subst_congr_scoped h h1) (I_subst_congr_scoped h h2)

theorem I_subst_id {r : I} (hr : r.Scoped k) : r.subst (ISub.id k).τ = r := by
  rw [I_subst_congr_scoped (τ := I.var) (fun i hi => by simp [ISub.id, hi]) hr, I_subst_var]

/-- Every computable type has the base clause: it is a type whose value is the code. -/
theorem Comp_ty_base {X : V} {f : Hom k m} {T : Tm} (h : (Comp S X m k f).ty T) :
    X ≠ ∅ ∧ IsTyK S k T ∧ semK S k T = res f X := by
  rw [Comp_eq] at h; unfold compF at h
  split at h
  · rename_i hX
    refine ⟨hX, ?_⟩
    simp only [body, core] at h
    split_ifs at h <;> first | exact h.1 | exact h | exact h.elim
  · exact h.elim

theorem Comp_eq_semK {X : V} {f : Hom k m} {T : Tm} (h : (Comp S X m k f).ty T) :
    Comp S X m k f = Comp S (semK S k T) k k (Hom.id k) := by
  obtain ⟨hX, -, hs⟩ := Comp_ty_base h
  rw [Comp_eq_res hX, hs]

/-- The interval substitution `τ` out of stage `n`, made an `ISub` (zero beyond `n`). -/
def ISub.ofFun (n : ℕ) (τ : ℕ → I) (hsc : ∀ i < n, (τ i).Scoped k) : ISub k n :=
  ⟨fun i => if i < n then τ i else .zero, fun i hi => by simp only [if_pos hi]; exact hsc i hi,
    fun i hi => by simp only [if_neg (show ¬ i < n by omega)]⟩

theorem isub_ofFun {n m : ℕ} {t : Tm} (h : t.closedB m n = true) (τ : ℕ → I) (hsc : ∀ i < n, (τ i).Scoped k) :
    t.isub (ISub.ofFun n τ hsc) = t.subst .var τ :=
  closed_subst_eq t m n _ _ _ _ h (fun _ _ => rfl) (fun i hi => by simp [ISub.ofFun, hi])

variable (hW : WfSig S)
include hW

/-- Interval substitutions equal in the De Morgan algebra give judgmentally equal instances. -/
theorem ieq0 {n : ℕ} {t T : Tm} (h : HasTy0 S n .one [] t T) {τ1 τ2 : ℕ → I}
    (hb1 : ∀ i < n, (τ1 i).Scoped k) (hb2 : ∀ i < n, (τ2 i).Scoped k) (heq : ∀ i < n, I.Eq (τ1 i) (τ2 i)) :
    EqTm S k .one [] (t.subst .var τ1) (t.subst .var τ2) (T.subst .var τ1) :=
  minimal_to_spec_eq (HasTy0.ieq (Γ := []) (Φ' := .one) (sigClosed_of_wfSig hW) h hb1 hb2 (ent_refl _) (ent_refl _)
    heq rfl (Wf0.nil trivial))

theorem tyEq_eq {A B : Tm} (h : TyEq S k A B) (hB : ∃ l, HasTy S k .one [] B (.univ l)) :
    ∃ l, EqTm S k .one [] A B (.univ l) := by
  rcases h with rfl | h
  · obtain ⟨l, hB⟩ := hB; exact ⟨l, EqTm.refl hB⟩
  · exact h

theorem ent_cof_one {φ : I} (h : I.Entails .one φ) : I.Entails .one (cof .one φ) :=
  entails_iff.2 fun ρ hρ hs => by
    have := (entails_iff.1 h) ρ hρ hs
    simp only [cof, I.eval] at this ⊢
    rw [this]; rfl

/-- Composition at judgmentally equal types. -/
theorem hcomp_retype {A A' u a : Tm} {φ : I} {l : ℕ} (hty : HasTy S k .one [] (.hcomp A φ u a) A)
    (e : EqTm S k .one [] A A' (.univ l)) :
    HasTy S k .one [] (.hcomp A' φ u a) A' ∧
      EqTm S k .one [] (.hcomp A φ u a) (.hcomp A' φ u a) A := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hA, hφ, hu, ha, hside⟩, -⟩ := gen_hcomp h0 rfl
  have e0 := spec_to_minimal_eq hW e
  have hA' := spec_to_minimal hW (HasTy.eqR e)
  have hXs : (cof .one φ).Scoped k := ⟨trivial, hφ⟩
  have hent : I.Entails (cof .one φ) .one := ent_and_left _ _
  have hu' := HasTy0.conv hu (EqTm0.restrict (scoped_shift hXs) (ent_shift hent) (EqTm0.dwk hS e0))
  have ha' := HasTy0.conv ha e0
  have hside' := EqTm0.conv hside (EqTm0.restrict hXs hent e0)
  have hh' := HasTy0.hcomp hA' hφ hu' ha' hside'
  exact ⟨minimal_to_spec hh', minimal_to_spec_eq (EqTm0.hcomp h0 (HasTy0.conv hh' (EqTm0.symm e0)) e0
    (ent_refl _) (ent_refl _) (EqTm0.refl hu) (EqTm0.refl ha))⟩

omit hW in
theorem HasTy0.cumulTo {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A : Tm} {l l' : ℕ} (h : HasTy0 S Ψ Φ Γ A (.univ l))
    (hl : l ≤ l') (hl' : l' ≤ maxLevel) : HasTy0 S Ψ Φ Γ A (.univ l') := by
  induction l', hl using Nat.le_induction with
  | base => exact h
  | succ n hn ih => exact HasTy0.cumul hl' (ih (by omega))

omit hW in
theorem EqTm0.cumulTo {Ψ : ℕ} {Φ : I} {Γ : Ctx} {A B : Tm} {l l' : ℕ} (h : EqTm0 S Ψ Φ Γ A B (.univ l))
    (hl : l ≤ l') (hl' : l' ≤ maxLevel) : EqTm0 S Ψ Φ Γ A B (.univ l') := by
  induction l', hl using Nat.le_induction with
  | base => exact h
  | succ n hn ih => exact EqTm0.cumul hl' (ih (by omega))

/-- Transport along judgmentally equal lines. -/
theorem transp_retype {A A' a : Tm} {φ : I} {l : ℕ} (hty : HasTy S k .one [] (.transp A φ a) (A.dinst .one))
    (e : EqTm S (k + 1) .one [] A A' (.univ l)) :
    HasTy S k .one [] (.transp A' φ a) (A'.dinst .one) ∧
      EqTm S k .one [] (.transp A φ a) (.transp A' φ a) (A.dinst .one) ∧
      EqTm S k .one [] (A.dinst .zero) (A'.dinst .zero) (.univ l) ∧
      EqTm S k .one [] (A.dinst .one) (A'.dinst .one) (.univ l) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hA, hφ, hc, ha⟩, -⟩ := gen_transpF h0 rfl
  have e0 := spec_to_minimal_eq hW e
  have hA' := spec_to_minimal hW (HasTy.eqR e)
  have hl := lvl_of_eq hW e
  have hl0 := lvl_of_ty hW (minimal_to_spec hA)
  have hXs : (cof .one φ).Scoped k := ⟨trivial, hφ⟩
  have hent : I.Entails (cof .one φ) .one := ent_and_left _ _
  have ez := EqTm0.dsubst hS (Γ := []) (Φ := .one) e0 (r := .zero) trivial
  have eo := EqTm0.dsubst hS (Γ := []) (Φ := .one) e0 (r := .one) trivial
  have eL := EqTm0.cumulTo (l' := max l l0) e0 (le_max_left _ _) (max_le hl hl0)
  have hcL := EqTm0.cumulTo (l' := max l l0) hc (le_max_right _ _) (max_le hl hl0)
  have ezL := EqTm0.cumulTo (l' := max l l0) ez (le_max_left _ _) (max_le hl hl0)
  have hc' : EqTm0 S (k + 1) (cof .one φ).shift [] A' (A'.dinst .zero).dshift (.univ (max l l0)) :=
    EqTm0.trans (EqTm0.trans (EqTm0.symm (EqTm0.restrict (scoped_shift hXs) (ent_shift hent) eL)) hcL)
      (EqTm0.restrict (scoped_shift hXs) (ent_shift hent) (EqTm0.dwk hS ezL))
  have ha' := HasTy0.conv ha ez
  have hh' := HasTy0.transp (HasTy0.cumulTo hA' (le_max_left _ _) (max_le hl hl0)) hφ hc' ha'
  exact ⟨minimal_to_spec hh', minimal_to_spec_eq (EqTm0.transp h0 (HasTy0.conv hh' (EqTm0.symm eo)) e0
    (ent_refl _) (ent_refl _) (EqTm0.refl ha)), minimal_to_spec_eq ez, minimal_to_spec_eq eo⟩

theorem kanH_retype {A A' : Tm} (e : TyEq S k A A') (h : KanH S k A') : KanH S k A := by
  rcases e with rfl | ⟨l, e⟩
  · exact h
  intro φ u a hty hu ha
  obtain ⟨hty', eqv⟩ := hcomp_retype hW hty e
  have r := h φ u a hty' (fun k' σ r hr hh => (hu k' σ r hr hh).conv_ty hW ((TyEq.isub hW σ (.inr ⟨l, e⟩))))
    (ha.conv_ty hW (.inr ⟨l, e⟩))
  exact r.conv hW (.inr ⟨l, EqTm.symm e⟩) (EqTm.symm eqv)

theorem kanT_retype {A A' : Tm} {l : ℕ} (e : EqTm S (k + 1) .one [] A A' (.univ l)) (h : KanT S k A') :
    KanT S k A := by
  intro φ a hty ha
  obtain ⟨hty', eqv, e0, e1⟩ := transp_retype hW hty e
  have r := h φ a hty' (ha.conv_ty hW (.inr ⟨l, e0⟩))
  exact r.conv hW (.inr ⟨l, EqTm.symm e1⟩) (EqTm.symm eqv)

/-- Composition where the face holds. -/
theorem RE_hcomp_face {A u a : Tm} {φ : I} (hty : HasTy S k .one [] (.hcomp A φ u a) A)
    (hu : TubeC S k A φ u) (hh : (ival (idEnv k) φ).holds) : RE S k A (.hcomp A φ u a) := by
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hA, hφ, hu0, -, -⟩, -⟩ := gen_hcomp h0 rfl
  have hu1 := hu k (ISub.id k) .one trivial (by rw [I_subst_id hφ]; exact hh)
  rw [isub_id_of_closed (closed_ty hA), isub_up_id_of_closed (closed_ty hu0)] at hu1
  exact hu1.conv hW (TyEq.refl _) (EqTm.symm (EqTm.hcompFace (entails_of_holds hφ hh) hty))

/-- Transport where the face holds. -/
theorem RE_transp_face {A a : Tm} {φ : I} (hty : HasTy S k .one [] (.transp A φ a) (A.dinst .one))
    (hh : (ival (idEnv k) φ).holds) (ha : RE S k (A.dinst .zero) a) : RE S k (A.dinst .one) (.transp A φ a) := by
  have hS := sigClosed_of_wfSig hW
  have h0 := spec_to_minimal hW hty
  obtain ⟨l0, ⟨hA, hφ, hc, -⟩, -⟩ := gen_transpF h0 rfl
  have hent := entails_of_holds hφ hh
  have e1 := EqTm0.dsubst hS (Γ := []) (Φ := cof .one φ) hc (r := .one) trivial
  rw [dshift_dinst] at e1
  have e2 := EqTm0.restrict (Φ' := .one) trivial (ent_cof_one hW hent) e1
  exact ha.conv hW (.inr ⟨l0, EqTm.symm (minimal_to_spec_eq e2)⟩) (EqTm.symm (EqTm.transpFace hent hty))

theorem closed_of_isTyK {T : Tm} (h : IsTyK S k T) : T.closedB 0 k = true := by
  obtain ⟨l, h | rfl⟩ := h
  · exact closed_of_ty hW h
  · rfl

/-- The endpoints of a computable line are computable types, at the restricted code. -/
theorem ty_dinst {X : V} (hX : KR S m X) {f : Hom (k + 1) m} {T : Tm} (h : (Comp S X m (k + 1) f).ty T)
    (r : I) (hr : r.Scoped k) : (Comp S X m k (f.comp (ISub.cons r hr (ISub.id k)).hom)).ty (T.dinst r) := by
  have := (hX (k + 1) f k (ISub.cons r hr (ISub.id k)) T T).1 h
  rwa [isub_cons_id_of_closed (closed_of_isTyK hW (Comp_ty_base h).2.1)] at this

end

end Model.Canon
