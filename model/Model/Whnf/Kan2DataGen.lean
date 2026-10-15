import Model.Whnf.Kan2DataH2
import Model.Whnf.Kan2Glue

/-!
# The binary composition at inductive types without path constructors: general types

A type related to itself whose normal form is an inductive type is related to that normal form
(`RT2_data_whnf`); composition at such types (`kanH2_data`), from that at the literal types
(`kanH2_lit`).
-/

set_option autoImplicit false

namespace Model.Whnf

open KubusCore KubusCore.Meta Model.Canon

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Sig} {k k' k'' m : ℕ}

section
variable (hW : WfSig S) {d : ℕ} {D : DataDecl} (hD : S[d]? = some (.data D))
include hW hD

/-- A type whose normal form is an inductive type: that normal form is typed at the level of the
declaration. -/
theorem data_whnf_ty {T ps : Tm} (hTK : IsTyK S k T) (hR : RedT S k T (.data d ps)) :
    HasTy S k .one [] (.data d ps) (.univ D.level) := by
  obtain ⟨l, hd | hd⟩ := hTK.of_tyEq hR.2
  · obtain ⟨D', hD', hPt⟩ := gen_data_tele (spec_to_minimal hW hd) rfl
    rw [hD] at hD'; cases hD'
    exact minimal_to_spec (HasTy0.data hD (hW.2 d D hD).1 hPt)
  · cases hd

/-- A type related to itself whose normal form is an inductive type is related to that normal form. -/
theorem RT2_data_whnf {T ps : Tm} (hTT : RT2 S k T T) (hR : RedT S k T (.data d ps)) :
    RT2 S k T (.data d ps) := by
  obtain ⟨-, hTK, -, -, -, -⟩ := Comp2_ty_base hTT
  have hd := data_whnf_ty hW hD hTK hR
  have hsem : semK S k T = dataC (ΘK S D d k ps) := (semK_tyEq hW hR.2).trans (semK_dataT hW hD hd)
  have ihp : ∀ n (g : Hom n k) j t X, vnth ((ΘK S D d k ps).pt n g) j = ZFSet.pair t X → PER2 S n X :=
    fun n g j t X e => per2_wf hW _ (level_le hW hD (K := k)) n _ (ΘK_pt_wf hW hD hd n g j t X e)
  have hTc := closed_of_isTyK hW hTK
  have hT := hTT
  unfold RT2 at hT ⊢
  rw [hsem, Comp2_dataC] at hT ⊢
  obtain ⟨hb, hall, hc, -⟩ := hT
  -- the parameters at the identity
  obtain ⟨ps0, -, h0, -, hpl, -, -, -, d0, -, -⟩ := hall k (ISub.id k)
  rw [isub_id_of_closed hTc] at h0
  obtain rfl : ps0 = ps := by have := RedW.unique h0.1 hR.1; injection this
  -- the parameters' clauses at a restriction
  have hσ : ∀ k' (σ : ISub k' k) ps1, RedT S k' (T.isub σ) (.data d ps1) →
      argRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) ps1 ∧
      argRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ ps1 (ps0.isub σ) ∧
      parRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) ps1 := by
    intro k' σ ps1 h1
    have := hc k (ISub.id k) k' σ ps0 ps1 (by rw [isub_id_of_closed hTc]; exact hR)
      (by rw [ISub.id_comp]; exact h1)
    rw [ISub.id_comp] at this
    exact this
  have hpc : ps0.closedB 0 k = true := by have := closed_of_ty hW hd; simpa [Tm.closedB] using this
  have hdK : IsTyK S k (.data d ps0) := ⟨_, .inl hd⟩
  -- the self-relation of the restricted parameters
  have hself : ∀ k' (σ : ISub k' k),
      argRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) (ps0.isub σ) ∧
      parRel2 S (ΘK S D d k ps0) (Hom.id k) k' σ (ps0.isub σ) (ps0.isub σ) := by
    intro k' σ
    obtain ⟨ps1, -, h1, -, -, -, -, -, -, -, -⟩ := hall k' σ
    obtain ⟨-, -, p⟩ := hσ k' σ ps1 h1
    have hT1 : IsTyK S k' (.data d ps1) := (hTK.isub hW σ).of_tyEq h1.2
    refine ⟨?_, parRel2_trans ihp (Hom.id k) σ ?_ p (parRel2_symm ihp (Hom.id k) σ p)⟩
    · have := argRelH_isub _ _ ((argRel2_iff _ (ISub.id k)).1 d0) σ
      rw [ISub.hom_id, Hom.id_comp] at this
      exact (argRel2_iff _ σ).2 this
    · rw [data_len_of hW hT1, data_len_of hW (show IsTyK S k' (.data d (ps0.isub σ)) from hdK.isub hW σ)]
  have hred : ∀ k' (σ : ISub k' k), RedT S k' ((Tm.data d ps0).isub σ) (.data d (ps0.isub σ)) :=
    fun k' σ => ⟨redW_self (step_data d _), TyEq.refl _⟩
  refine ⟨⟨hTK, hdK, hb.2.2.1, ?_, hR.2⟩, fun k' σ => ?_, hc, ?_⟩
  · exact (semK_tyEq hW hR.2).symm.trans hb.2.2.1
  · obtain ⟨ps1, -, h1, -, hl1, -, -, -, d1, -, pr1⟩ := hall k' σ
    obtain ⟨a, b, p⟩ := hσ k' σ ps1 h1
    exact ⟨ps1, ps0.isub σ, h1, hred k' σ, hl1, isList_subst hpl _ _, b, a, d1, (hself k' σ).1,
      parRel2_symm ihp (Hom.id k) σ p⟩
  · intro k' σ k3 σ' p1 p2 h1 h2
    obtain rfl := redT_data_eq (Θ := ΘK S D d k ps0) (show RedT S k' (.data d (ps0.isub σ)) (.data d p1) from h1)
    obtain rfl := redT_data_eq (Θ := ΘK S D d k ps0)
      (show RedT S k3 (.data d (ps0.isub (σ.comp σ'))) (.data d p2) from h2)
    rw [Tm.isub_isub]
    exact ⟨(hself k3 _).1, (hself k3 _).1, (hself k3 _).2⟩

/-- The normal forms of the restrictions of related types whose normal form is an inductive type. -/
theorem data_whnf_pair {T T' ps : Tm} (hTT : RT2 S k T T') (hR : RedT S k T (.data d ps)) (σ : ISub k' k) :
    ∃ P1 P1', RedT S k' (T.isub σ) (.data d P1) ∧ RedT S k' (T'.isub σ) (.data d P1') := by
  obtain ⟨-, hTK, -, -, -, -⟩ := Comp2_ty_base hTT
  have hd := data_whnf_ty hW hD hTK hR
  have hsem : semK S k T = dataC (ΘK S D d k ps) := (semK_tyEq hW hR.2).trans (semK_dataT hW hD hd)
  have hT := hTT
  unfold RT2 at hT
  rw [hsem, Comp2_dataC] at hT
  obtain ⟨P1, P1', h1, h2, -⟩ := hT.2.1 k' σ
  exact ⟨P1, P1', h1, h2⟩

omit hD in
/-- Compositions with heads equal to given types, from those with the given heads. -/
theorem HC2.retype {A L L' M M' a a' : Tm} (h : HC2 S k A L L' a a') (eL : TyEq S k M L) (eL' : TyEq S k M' L')
    (eA : TyEq S k M A) (eA' : TyEq S k M' A) {φ φ' : I} {u u' : Tm}
    (hty : HasTy S k .one [] (.hcomp M φ u a) A) (hty' : HasTy S k .one [] (.hcomp M' φ' u' a') A)
    (heq : EqTm S k .one [] (.hcomp M φ u a) (.hcomp M' φ' u' a') A)
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' A.dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k A φ u u') (haa : RE2 S k A a a')
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ))
    (hbd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (A.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) :
    RE2 S k A (.hcomp L φ u a) (.hcomp L' φ' u' a') := by
  have r := hcomp_retype hW hty eL
  have r' := hcomp_retype hW hty' eL'
  exact h φ φ' u u' (r.1.tyConv eA) (r'.1.tyConv eA') ((r.2.tyConv eA).symm.trans (heq.trans (r'.2.tyConv eA')))
    hteq h12 h21 htube haa hbd hbd'

/-- Composition at a type related to itself and equal to a literal inductive type, against a related
type: compositions at the literal types. -/
theorem kanH2_data_at {X X' P Q' : Tm} (hP : HasTy S k .one [] (.data d P) (.univ D.level))
    (hPX : RT2 S k (.data d P) X) (hXX' : RT2 S k X X') (hX'Q : RT2 S k X' (.data d Q'))
    (hlit : RT2 S k (.data d P) (.data d P) → RT2 S k (.data d P) (.data d Q') →
      ∀ a a', HC2 S k (.data d P) (.data d P) (.data d Q') a a')
    {φ φ' : I} {u u' a a' : Tm}
    (hty : HasTy S k .one [] (.hcomp X φ u a) X) (hty' : HasTy S k .one [] (.hcomp X' φ' u' a') X)
    (heq : EqTm S k .one [] (.hcomp X φ u a) (.hcomp X' φ' u' a') X)
    (hteq : EqTm S (k + 1) (cof .one φ).shift [] u u' X.dshift)
    (h12 : I.Entails φ φ') (h21 : I.Entails φ' φ) (htube : Tube2 S k X φ u u') (haa : RE2 S k X a a')
    (hbd : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (X.isub σ) ((u.isub σ.up).dinst .zero) (a'.isub σ))
    (hbd' : ∀ k' (σ : ISub k' k), (ival (idEnv k') (φ.subst σ.τ)).holds →
      RE2 S k' (X.isub σ) (a.isub σ) ((u'.isub σ.up).dinst .zero)) :
    RE2 S k X (.hcomp (.data d P) φ u a) (.hcomp (.data d Q') φ' u' a') := by
  have hPc : TyCode k (semK S k (.data d P)) := tyCode_of_univ hW hP
  have hXc : TyCode k (semK S k X) := RT2.tyCode_r hW hPX hPc
  have hPP : RT2 S k (.data d P) (.data d P) := RT2.trans hW hPc hPX (RT2.symm hW hPc hPX)
  have hPQ : RT2 S k (.data d P) (.data d Q') := RT2.trans hW hPc hPX (RT2.trans hW hXc hXX' hX'Q)
  have h := (hlit hPP hPQ a a').conv hW hPX hPc
  have eXP : TyEq S k X (.data d P) := TyEq.symm (Comp2_ty_base hPX).2.2.2.2.2
  have eXX' : TyEq S k X X' := (Comp2_ty_base hXX').2.2.2.2.2
  have eX'Q : TyEq S k X' (.data d Q') := (Comp2_ty_base hX'Q).2.2.2.2.2
  exact h.retype hW eXP eX'Q (TyEq.refl _) (TyEq.symm eXX') hty hty' heq hteq h12 h21 htube haa hbd hbd'

/-- Composition at a pair of related types whose normal forms are an inductive type, from composition at
the literal types related to the restrictions of `T`. -/
theorem kanH2_data_gen {T T' ps : Tm} (hTT : RT2 S k T T') (hR : RedT S k T (.data d ps))
    (hL : ∀ k1 (ρ1 : ISub k1 k) P1 Q1, HasTy S k1 .one [] (.data d P1) (.univ D.level) →
      RT2 S k1 (.data d P1) (T.isub ρ1) → RT2 S k1 (.data d P1) (.data d P1) → RT2 S k1 (.data d P1) (.data d Q1) →
      ∀ a a', HC2 S k1 (.data d P1) (.data d P1) (.data d Q1) a a') :
    KanH2 S k T T' := by
  intro ψ ψ' u u' a0 a0' hty hty' heq hteq p12 p21 htube ha0 hbd hbd'
  obtain ⟨-, ⟨-, hψs, -, -, -⟩, -⟩ := gen_hcomp (spec_to_minimal hW hty) rfl
  have hXT : TyCode k (semK S k T) := tyCode_of_ty hW hty
  have hTTd : RT2 S k T T := RT2.refl hW hXT hTT
  have hTK : IsTyK S k T := (Comp2_ty_base hTT).2.1
  have hTT'e : TyEq S k T T' := (Comp2_ty_base hTT).2.2.2.2.2
  have hTτ : ∀ {k'} (τ : ISub k' k), RT2 S k' (T.isub τ) (T.isub τ) := fun τ => RT2.isub hW hXT hTTd τ
  have hTτ' : ∀ {k'} (τ : ISub k' k), RT2 S k' (T.isub τ) (T'.isub τ) := fun τ => RT2.isub hW hXT hTT τ
  have hT'τ : ∀ {k'} (τ : ISub k' k), RT2 S k' (T'.isub τ) (T'.isub τ) := fun τ =>
    RT2.refl' hW (tyCode_of_ty hW (HasTy.isubS hW hty τ)) (hTτ' τ)
  have hholdψ : ∀ {k'} (τ : ISub k' k), I.Entails .one (ψ.subst τ.τ) → (ival (idEnv k') (ψ.subst τ.τ)).holds :=
    fun τ h => (holds_iff_entails (I.scoped_subst hψs τ.sc)).2 h
  have hw := fun k' (σ : ISub k' k) => data_whnf_pair hW hD hTT hR σ
  choose P1 P1' hw using hw
  refine RE2.expandBoth hW hXT hTTd hty hty'
    (fun k' σ => if I.Entails .one (ψ.subst σ.τ) then (u.isub σ.up).dinst .one
      else .hcomp (.data d (P1 k' σ)) (ψ.subst σ.τ) (u.isub σ.up) (a0.isub σ))
    (fun k' σ => if I.Entails .one (ψ'.subst σ.τ) then (u'.isub σ.up).dinst .one
      else .hcomp (.data d (P1' k' σ)) (ψ'.subst σ.τ) (u'.isub σ.up) (a0'.isub σ))
    (fun k' σ => ?_) (fun k' σ => ?_) (fun k' σ k'' ρ => ?_)
  · -- the left reducts
    have htyσ : HasTy S k' .one [] (.hcomp (T.isub σ) (ψ.subst σ.τ) (u.isub σ.up) (a0.isub σ)) (T.isub σ) :=
      HasTy.isubS hW hty σ
    rw [isub_hcomp]
    dsimp only
    split_ifs with hψ
    · exact ⟨.step (step_hcomp_face hψ) (.refl _), EqTm.hcompFace hψ htyσ⟩
    · exact ⟨red_hcomp_ty hψ (hw k' σ).1.1.1, (hcomp_retype hW htyσ (hw k' σ).1.2).2⟩
  · -- the right reducts
    have htyσ : HasTy S k' .one [] (.hcomp (T'.isub σ) (ψ'.subst σ.τ) (u'.isub σ.up) (a0'.isub σ)) (T.isub σ) :=
      HasTy.isubS hW hty' σ
    have eσ : TyEq S k' (T.isub σ) (T'.isub σ) := TyEq.isub hW σ hTT'e
    rw [isub_hcomp]
    dsimp only
    split_ifs with hψ
    · exact ⟨.step (step_hcomp_face hψ) (.refl _), EqTm.hcompFace hψ htyσ⟩
    · exact ⟨red_hcomp_ty hψ (hw k' σ).2.1.1, ((hcomp_retype hW htyσ (hw k' σ).2.2).2.tyConv (TyEq.symm eσ))⟩
  · -- the reducts across restrictions
    dsimp only
    have hτ0 : ∀ {x : I}, x.subst (σ.comp ρ).τ = (x.subst σ.τ).subst ρ.τ := fun {x} => I_subst_comp x σ ρ
    by_cases hψ : I.Entails .one (ψ.subst σ.τ)
    · have hψ2 : I.Entails .one (ψ.subst (σ.comp ρ).τ) := by rw [hτ0]; exact ent_one_subst hψ ρ.τ
      have hψ2' : I.Entails .one (ψ'.subst (σ.comp ρ).τ) := ent_trans hψ2 (ent_subst p12 _)
      rw [if_pos hψ, if_pos hψ2', isub_dinst, Tm.isub_isub, ← ISub.up_comp]
      exact htube k'' (σ.comp ρ) _ _ trivial trivial (I_eq_refl _) (hholdψ _ hψ2)
    rw [if_neg hψ, isub_hcomp, Tm.isub_isub u, ← ISub.up_comp, Tm.isub_isub a0, ← hτ0]
    have hd1 := data_whnf_ty hW hD (hTK.isub hW σ) (hw k' σ).1
    have hP : HasTy S k'' .one [] (.data d ((P1 k' σ).isub ρ)) (.univ D.level) := HasTy.isubS hW hd1 ρ
    have hPX : RT2 S k'' (.data d ((P1 k' σ).isub ρ)) (T.isub (σ.comp ρ)) := by
      have h1 := RT2.isub hW (tyCode_of_ty hW (HasTy.isubS hW hty σ)) (RT2_data_whnf hW hD (hTτ σ) (hw k' σ).1) ρ
      rw [Tm.isub_isub] at h1
      exact RT2.symm hW (tyCode_of_ty hW (HasTy.isubS hW hty (σ.comp ρ))) h1
    have hX'Q := RT2_data_whnf hW hD (hT'τ (σ.comp ρ)) (hw k'' (σ.comp ρ)).2
    have hteqτ := EqTm.cofIsub hW hψs hteq (σ.comp ρ)
    rw [isub_dshift] at hteqτ
    have M := kanH2_data_at hW hD hP hPX (hTτ' (σ.comp ρ)) hX'Q (hL k'' (σ.comp ρ) _ _ hP hPX)
      (HasTy.isubS hW hty (σ.comp ρ)) (HasTy.isubS hW hty' (σ.comp ρ)) (EqTm.isubS hW heq (σ.comp ρ)) hteqτ
      (ent_subst p12 _) (ent_subst p21 _) (htube.isub (σ.comp ρ)) (RE2.isub hW ha0 (σ.comp ρ))
      (bdry_isub hbd (σ.comp ρ)) (bdry_isub' hbd' (σ.comp ρ))
    by_cases hψ2' : I.Entails .one (ψ'.subst (σ.comp ρ).τ)
    · rw [if_pos hψ2']
      have hψ2 : I.Entails .one (ψ.subst (σ.comp ρ).τ) := ent_trans hψ2' (ent_subst p21 _)
      have tb := htube k'' (σ.comp ρ) .one .one trivial trivial (I_eq_refl _) (hholdψ _ hψ2)
      have eτ : TyEq S k'' (T'.isub (σ.comp ρ)) (T.isub (σ.comp ρ)) := TyEq.symm (TyEq.isub hW (σ.comp ρ) hTT'e)
      have hq := ((hcomp_retype hW (HasTy.isubS hW hty' (σ.comp ρ)) (hw k'' (σ.comp ρ)).2.2).1).tyConv eτ
      exact el_reduceSR hW (RE2.tyCode hW M) (hTτ (σ.comp ρ)) M (stable_hcompFace hW hψ2' hq) (RE2.typed tb).2.1
    · rw [if_neg hψ2']
      exact M
variable (hH : D.isHIT = false)
include hH

/-- Composition at a literal inductive type without path constructors, against a related literal type. -/
theorem kanH2_litId {K : ℕ} {P Q' : Tm} (hP : HasTy S K .one [] (.data d P) (.univ D.level))
    (hPP : RT2 S K (.data d P) (.data d P))

    (hQ' : RT2 S K (.data d P) (.data d Q')) (a a' : Tm) :
    HC2 S K (.data d P) (.data d P) (.data d Q') a a' := by
  have h := kanH2_lit hW hD hH hP hPP  (ISub.id K) hPP hQ' a a'
  have hPc : P.closedB 0 K = true := by have := closed_of_ty hW hP; simpa [Tm.closedB] using this
  have hQc : Q'.closedB 0 K = true := by
    have := closed_of_isTyK hW (Comp2_ty_base hQ').2.2.1; simpa [Tm.closedB] using this
  rwa [isub_id_of_closed hPc, isub_id_of_closed hQc] at h


/-- Composition at a pair of related types whose normal forms are an inductive type without path
constructors. The Kan properties of the argument types are required at the literal types related to
the restrictions of `T`. -/
theorem kanH2_data {T T' ps : Tm} (hTT : RT2 S k T T') (hR : RedT S k T (.data d ps))
 :
    KanH2 S k T T' :=
  kanH2_data_gen hW hD hTT hR fun k1 ρ1 P1 _ hP1 hPX hPP hPQ a a' =>
    kanH2_litId hW hD hH hP1 hPP hPQ a a'

end

end

end Model.Whnf
